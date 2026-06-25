"""
Polish Architecture Tender Scraper
====================================
Scrapes public procurement notices (przetargi) related to architecture,
executive designs (projekty wykonawcze), and construction documentation
from Polish and EU procurement portals.

Sources
-------
1. DuckDuckGo full-text search  – no API key required, broad coverage
2. TED (Tenders Electronic Daily) – EU procurement portal RSS feeds (feedparser)
3. ezamowienia.gov.pl (BZP)       – Polish national procurement platform API
4. platformazakupowa.pl           – popular Polish e-procurement platform (scraper)

Persistence
-----------
- data/history.json       : set of already-seen tender IDs (deduplication)
- data/reports/YYYY-MM-DD.json  : raw daily report (source of truth)
- docs/reports/YYYY-MM-DD.json  : copy served by GitHub Pages
- docs/index.html               : regenerated SPA dashboard after every run
- docs/manifest.json            : ordered list of available reports for the JS frontend

Configuration (environment variables)
--------------------------------------
  LOOKBACK_DAYS  –  how many days back to consider (default: 30)
"""

from __future__ import annotations

import hashlib
import json
import logging
import os
import random
import re
import time
from datetime import date, datetime, timedelta, timezone
from pathlib import Path
from typing import Optional
from urllib.parse import urljoin

import feedparser
import requests
from bs4 import BeautifulSoup
from dateutil import parser as dateutil_parser
from duckduckgo_search import DDGS
from jinja2 import Environment, FileSystemLoader, select_autoescape
from markupsafe import Markup

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

LOOKBACK_DAYS: int = int(os.getenv("LOOKBACK_DAYS", "30"))
TODAY: date = datetime.now(tz=timezone.utc).date()
CUTOFF_DATE: date = TODAY - timedelta(days=LOOKBACK_DAYS)

BASE_DIR: Path = Path(__file__).parent
DATA_DIR: Path = BASE_DIR / "data"
REPORTS_DIR: Path = DATA_DIR / "reports"
HISTORY_FILE: Path = DATA_DIR / "history.json"
DOCS_DIR: Path = BASE_DIR / "docs"
DOCS_REPORTS_DIR: Path = DOCS_DIR / "reports"
TEMPLATES_DIR: Path = BASE_DIR / "templates"

for _d in (DATA_DIR, REPORTS_DIR, DOCS_DIR, DOCS_REPORTS_DIR):
    _d.mkdir(parents=True, exist_ok=True)

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(name)s – %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
log = logging.getLogger("tender_scraper")

_REQUEST_TIMEOUT: int = 20
_DELAY_RANGE: tuple[float, float] = (1.5, 3.5)
# Set DDG_SSL_VERIFY=0 in corporate environments where the proxy intercepts TLS.
# On GitHub Actions this should always stay True.
_DDG_VERIFY_SSL: bool = os.getenv("DDG_SSL_VERIFY", "1") != "0"
_USER_AGENTS: list[str] = [
    (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36"
    ),
    (
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 "
        "(KHTML, like Gecko) Version/17.5 Safari/605.1.15"
    ),
    "Mozilla/5.0 (X11; Linux x86_64; rv:126.0) Gecko/20100101 Firefox/126.0",
]

# ---------------------------------------------------------------------------
# Keywords, queries, and sector taxonomy
# ---------------------------------------------------------------------------

# CPV codes covering architectural and related design services
_ARCH_CPV_CODES: list[str] = [
    "71200000",  # Architectural and related services
    "71220000",  # Architectural design services
    "71221000",  # Architectural services for buildings
    "71222000",  # Architectural services for outdoor areas
    "71240000",  # Architectural, engineering and planning services
    "71250000",  # Architectural, engineering and surveying services
    "71320000",  # Engineering design services
]

# DuckDuckGo search queries – extend freely to add new coverage
DDG_QUERIES: list[str] = [
    '"projekt wykonawczy" architektura przetarg',
    '"projekt architektoniczny" przetarg',
    '"dokumentacja projektowa" architektura przetarg',
    '"projekt budowlano-wykonawczy" przetarg Polska',
    '"hala przemysłowa" projekt przetarg',
    '"budynek użyteczności publicznej" projekt przetarg',
    'KGHM "projekt architektoniczny" OR "projekt wykonawczy" przetarg',
    'Orlen "projekt architektoniczny" przetarg',
    'PGE "projekt budowlany" przetarg',
    'PKP "projekt architektoniczny" przetarg',
    'Tauron "projekt wykonawczy" przetarg',
    '"projekt wykonawczy" architektura site:platformazakupowa.pl',
    '"projekt architektoniczny" site:ezamowienia.gov.pl',
    '"dokumentacja projektowa" site:logintrade.net architektura',
]

# Polish State-Owned Enterprises (Spółki Skarbu Państwa)
_SOE_NAMES: list[str] = [
    "KGHM", "Orlen", "PKN Orlen", "PGE", "PKP", "Tauron", "PPL",
    "PSE", "Enea", "Energa", "PGNiG", "Lotos", "JSW", "KPEC",
    "Poczta Polska", "PKO BP", "PLL LOT", "Azoty", "Ciech", "PESA",
]

_SECTOR_PATTERNS: dict[str, re.Pattern] = {
    # SOE checked first so it wins over generic "public"
    "soe": re.compile(
        "|".join(re.escape(n) for n in _SOE_NAMES),
        re.IGNORECASE,
    ),
    "industrial": re.compile(
        r"hala\b|magazyn|logistyk|przemysł|fabryk|zakład|centrum dystrybucji"
        r"|warehouse|produkcj|przemysłow|sortowni",
        re.IGNORECASE,
    ),
    "public": re.compile(
        r"gmina|miasto|urząd|starostwo|szpital|szkoła|uczelnia|ministerstwo"
        r"|agencja|powiat|biblioteka|muzeum|komunaln|publiczn",
        re.IGNORECASE,
    ),
}

# ---------------------------------------------------------------------------
# Utility helpers
# ---------------------------------------------------------------------------


def _random_headers() -> dict[str, str]:
    return {
        "User-Agent": random.choice(_USER_AGENTS),
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "pl-PL,pl;q=0.9,en-US;q=0.8,en;q=0.7",
    }


def _get(url: str, **kwargs) -> requests.Response:
    """Polite HTTP GET with random delay to avoid triggering rate-limits."""
    time.sleep(random.uniform(*_DELAY_RANGE))
    kwargs.setdefault("headers", _random_headers())
    kwargs.setdefault("timeout", _REQUEST_TIMEOUT)
    kwargs.setdefault("allow_redirects", True)
    return requests.get(url, **kwargs)


def _make_id(url: str) -> str:
    """Stable 16-char hex ID derived from the normalised URL."""
    return hashlib.sha256(url.strip().lower().encode()).hexdigest()[:16]


def _parse_date(raw: Optional[str]) -> Optional[str]:
    """Return ISO-8601 date string or None if unparseable."""
    if not raw:
        return None
    raw = str(raw).strip()
    # TED API returns dates as YYYYMMDD
    if re.fullmatch(r"\d{8}", raw):
        try:
            return date(int(raw[:4]), int(raw[4:6]), int(raw[6:])).isoformat()
        except ValueError:
            pass
    try:
        return dateutil_parser.parse(raw, fuzzy=True).date().isoformat()
    except Exception:
        return None


def _within_window(date_str: Optional[str]) -> bool:
    """True if date_str is on or after CUTOFF_DATE (or unknown)."""
    if not date_str:
        return True  # keep if we cannot determine publication date
    try:
        return date.fromisoformat(date_str) >= CUTOFF_DATE
    except ValueError:
        return True


def _classify_sector(title: str, entity: str) -> str:
    """Classify a tender into one of: soe | industrial | public | other."""
    text = f"{title} {entity}"
    for sector, pattern in _SECTOR_PATTERNS.items():
        if pattern.search(text):
            return sector
    return "other"


def _format_value(raw) -> Optional[str]:
    """Format a raw numeric value into a readable PLN string."""
    if raw is None:
        return None
    try:
        v = float(str(raw).replace("\xa0", "").replace(" ", "").replace(",", "."))
        formatted = f"{v:,.2f}"  # "1,234,567.89"
        # Convert to Polish locale: space thousands, comma decimal
        formatted = formatted.replace(".", "\x00").replace(",", " ").replace("\x00", ",")
        return formatted + " PLN"
    except (ValueError, TypeError):
        s = str(raw).strip()
        return s if s else None


def _parse_ted_summary(summary: str) -> dict:
    """Extract structured fields (cpv, value, procedure_type, deadline, description)
    from a TED RSS entry summary HTML string."""
    result: dict = {"description": None, "value": None, "cpv": None,
                    "procedure_type": None, "deadline": None}
    if not summary:
        return result
    try:
        soup = BeautifulSoup(summary, "lxml")
        # Build a flat label→value map from table rows
        for tr in soup.find_all("tr"):
            cells = [td.get_text(" ", strip=True) for td in tr.find_all(["td", "th"])]
            if len(cells) >= 2:
                label, value = cells[0].lower(), cells[1].strip()
                if any(k in label for k in ("cpv", "common procurement")):
                    m = re.search(r"(7[0-9]\d{6})", value)
                    if m:
                        result["cpv"] = m.group(1)
                elif any(k in label for k in ("value", "wartość", "estimated")):
                    result["value"] = re.sub(r"\s+", " ", value)[:60]
                elif any(k in label for k in ("type of contract", "rodzaj zamówienia", "type")):
                    result["procedure_type"] = value[:80]
                elif any(k in label for k in ("deadline", "time limit", "termin")):
                    result["deadline"] = _parse_date(value)
                elif any(k in label for k in ("short description", "opis", "subject", "przedmiot")):
                    result["description"] = value[:300]
        # Fallback: CPV from raw text
        if not result["cpv"]:
            m = re.search(r"\b(7[0-9]\d{6})\b", summary)
            if m:
                result["cpv"] = m.group(1)
    except Exception as exc:
        log.debug("[TED summary parse] %s", exc)
    return result


def _enrich_bzp_detail(proc_id: str) -> dict:
    """Fetch extra fields for a BZP notice via the detail API endpoint.
    Returns an empty dict on any failure."""
    if not proc_id:
        return {}
    try:
        safe_id = requests.utils.quote(str(proc_id), safe="")
        url = f"{_BZP_API_BASE}/opi/og/notice/{safe_id}"
        resp = _get(url, headers=_BZP_HEADERS, timeout=15)
        ct = resp.headers.get("Content-Type", "")
        if resp.status_code != 200 or "html" in ct or not resp.content:
            return {}
        data = resp.json()
        raw_val = (
            data.get("estimatedValueBrutto") or data.get("estimatedValue")
            or data.get("contractValueBrutto") or data.get("tenderValue")
        )
        return {
            "description": str(
                data.get("orderSubject") or data.get("description")
                or data.get("shortDescription") or ""
            )[:300] or None,
            "value": _format_value(raw_val),
            "cpv": str(data.get("mainCpvCode") or data.get("cpvCode") or "").strip() or None,
            "procedure_type": str(
                data.get("procedureType") or data.get("orderType")
                or data.get("procurementMode") or ""
            ).strip() or None,
        }
    except Exception as exc:
        log.debug("[BZP detail] proc_id=%r: %s", proc_id, exc)
        return {}


# ---------------------------------------------------------------------------
# Persistence – history tracking
# ---------------------------------------------------------------------------


def load_history() -> set[str]:
    """Load the set of previously seen tender IDs from disk."""
    if HISTORY_FILE.exists():
        try:
            data = json.loads(HISTORY_FILE.read_text(encoding="utf-8"))
            return set(data.get("seen_ids", []))
        except Exception as exc:
            log.warning("Could not load history.json: %s", exc)
    return set()


def save_history(seen_ids: set[str]) -> None:
    """Persist the full set of seen IDs back to disk."""
    HISTORY_FILE.write_text(
        json.dumps({"seen_ids": sorted(seen_ids)}, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )
    log.info("History saved: %d known tender IDs", len(seen_ids))


# ---------------------------------------------------------------------------
# Source 1: DuckDuckGo Search
# ---------------------------------------------------------------------------


def fetch_ddg(queries: list[str]) -> list[dict]:
    """Run a list of DDG text queries and return raw tender dicts."""
    results: list[dict] = []
    # proxies=None lets primp pick up system proxy; verify controls TLS cert check
    ddgs_kwargs: dict = {"verify": _DDG_VERIFY_SSL}
    with DDGS(**ddgs_kwargs) as ddgs:
        for query in queries:
            try:
                log.info("[DDG] Querying: %s", query)
                hits = ddgs.text(query, max_results=15, region="pl-pl") or []
                for h in hits:
                    url = h.get("href", "").strip()
                    if not url:
                        continue
                    title = h.get("title", "").strip()
                    pub_date = _parse_date(h.get("published"))
                    results.append(
                        {
                            "id": _make_id(url),
                            "proc_id": None,
                            "title": title,
                            "entity": "",
                            "publication_date": pub_date,
                            "deadline": None,
                            "description": None,
                            "value": None,
                            "cpv": None,
                            "procedure_type": None,
                            "url": url,
                            "source": "DuckDuckGo",
                            "sector": _classify_sector(title, ""),
                        }
                    )
            except Exception as exc:
                log.warning("[DDG] Query failed (%r): %s", query, exc)
            # Extra pause between queries to be polite
            time.sleep(random.uniform(2.0, 5.0))
    log.info("[DDG] Collected %d raw results", len(results))
    return results


# ---------------------------------------------------------------------------
# Source 2: TED (Tenders Electronic Daily) – RSS feeds
# ---------------------------------------------------------------------------

_TED_RSS_BASE = "https://ted.europa.eu/TED/search/result.do"


def fetch_ted() -> list[dict]:
    """Fetch architecture-related tenders in Poland via TED CPV RSS feeds."""
    results: list[dict] = []
    for cpv in _ARCH_CPV_CODES[:4]:  # limit to 4 CPV codes to avoid overloading
        try:
            _fetch_ted_rss(cpv, results)
        except Exception as exc:
            log.warning("[TED] RSS CPV %s failed: %s", cpv, exc)
    log.info("[TED] Collected %d results", len(results))
    return results


def _fetch_ted_rss(cpv: str, results: list[dict]) -> None:
    url = (
        f"{_TED_RSS_BASE}?sortColumn=0&countryCode=POL"
        f"&cpvCodes={cpv}&orderType=YEAR_DESC&format=RSS"
    )
    time.sleep(random.uniform(*_DELAY_RANGE))
    feed = feedparser.parse(url, request_headers=_random_headers())
    log.debug("[TED] RSS CPV %s: %d entries", cpv, len(feed.entries))
    for entry in feed.entries:
        link = entry.get("link", "").strip()
        if not link:
            continue
        pub_date = _parse_date(entry.get("published") or entry.get("updated"))
        if not _within_window(pub_date):
            continue
        title = entry.get("title", "").strip()
        summary = entry.get("summary", "")
        # Try to extract buyer name from RSS summary
        entity = ""
        for pattern in [
            r"Authority[:\s]+([^\n|<]+)",
            r"Contracting authority[:\s]+([^\n|<]+)",
            r"Organisation[:\s]+([^\n|<]+)",
            r"Zamawiający[:\s]+([^\n|<]+)",
        ]:
            m = re.search(pattern, summary, re.IGNORECASE)
            if m:
                entity = m.group(1).strip()[:200]
                break
        ted_pub_num = None
        m_ted = re.search(r'/notice/([^/?#]+)', link)
        if m_ted:
            ted_pub_num = m_ted.group(1)
        ted_details = _parse_ted_summary(summary)
        results.append(
            {
                "id": _make_id(link),
                "proc_id": ted_pub_num,
                "title": title,
                "entity": entity,
                "publication_date": pub_date,
                "deadline": ted_details.get("deadline"),
                "description": ted_details.get("description"),
                "value": ted_details.get("value"),
                "cpv": ted_details.get("cpv"),
                "procedure_type": ted_details.get("procedure_type"),
                "url": link,
                "source": "TED (EU)",
                "sector": _classify_sector(title, entity),
            }
        )


# ---------------------------------------------------------------------------
# Source 3: ezamowienia.gov.pl – BZP API
# ---------------------------------------------------------------------------

_BZP_API_BASE = "https://ezamowienia.gov.pl/mo-client-board/api"
# Headers required to receive JSON instead of HTML from the BZP SPA backend
_BZP_HEADERS = {
    "Accept": "application/json",
    "X-Requested-With": "XMLHttpRequest",
    "Referer": "https://ezamowienia.gov.pl/",
    "Origin": "https://ezamowienia.gov.pl",
}


def fetch_bzp() -> list[dict]:
    """Query the BZP public API on ezamowienia.gov.pl using CPV codes and keywords."""
    results: list[dict] = []

    # Attempt A – CPV-code filter
    for cpv in _ARCH_CPV_CODES[:4]:
        try:
            _bzp_search({"cpvCodes": cpv}, results, tag=f"CPV {cpv}")
        except Exception as exc:
            log.warning("[BZP] CPV %s failed: %s", cpv, exc)

    # Attempt B – keyword search
    for keyword in ["projekt architektoniczny", "projekt wykonawczy", "hala przemysłowa"]:
        try:
            _bzp_search({"searchText": keyword}, results, tag=f"kw={keyword!r}")
        except Exception as exc:
            log.warning("[BZP] Keyword %r failed: %s", keyword, exc)

    log.info("[BZP] Collected %d results", len(results))
    return results


def _bzp_search(extra_params: dict, results: list[dict], tag: str) -> None:
    params = {
        "pageNumber": 1,
        "pageSize": 30,
        "sortBy": "publicationDate",
        "sortOrder": "DESC",
        **extra_params,
    }
    headers = {**_random_headers(), **_BZP_HEADERS}
    resp = _get(
        f"{_BZP_API_BASE}/opi/og/searchNotice",
        params=params,
        headers=headers,
    )
    if resp.status_code in (404, 403):
        log.debug("[BZP] Endpoint returned %d for %s – skipping", resp.status_code, tag)
        return
    resp.raise_for_status()
    # Guard: endpoint may return HTML redirect instead of JSON
    ct = resp.headers.get("Content-Type", "")
    if "html" in ct or not resp.content:
        log.debug("[BZP] Non-JSON response (%s) for %s – skipping", ct, tag)
        return

    data = resp.json()
    # Normalise – the API may return a list directly or nest under a key
    if isinstance(data, list):
        items = data
    else:
        items = (
            data.get("notices")
            or data.get("items")
            or data.get("data")
            or []
        )
    for item in items:
        _extract_bzp_item(item, results)


def _extract_bzp_item(item: dict, results: list[dict]) -> None:
    notice_id = (
        item.get("id")
        or item.get("noticeId")
        or item.get("publicationNumber")
        or ""
    )
    url = item.get("url") or item.get("href") or (
        f"https://ezamowienia.gov.pl/mo-client-board/bzp/notice/{notice_id}"
        if notice_id
        else ""
    )
    if not url:
        return

    pub_date = _parse_date(
        item.get("publicationDate")
        or item.get("publication_date")
        or item.get("publicationDateBzp")
    )
    if not _within_window(pub_date):
        return

    title = str(
        item.get("title")
        or item.get("name")
        or item.get("subject")
        or item.get("orderSubject")
        or ""
    )
    entity = str(
        item.get("organizationName")
        or item.get("entity")
        or item.get("orderingParty")
        or item.get("buyerName")
        or ""
    )
    deadline = _parse_date(
        item.get("submissionDeadline")
        or item.get("deadline")
        or item.get("offerDeadline")
    )
    # Extract detail fields directly from the API response if present
    raw_val = (
        item.get("estimatedValueBrutto") or item.get("estimatedValue")
        or item.get("contractValueBrutto") or item.get("tenderValue")
    )
    results.append(
        {
            "id": _make_id(url),
            "proc_id": notice_id or None,
            "title": title,
            "entity": entity,
            "publication_date": pub_date,
            "deadline": deadline,
            "description": str(
                item.get("orderSubject") or item.get("description")
                or item.get("shortDescription") or ""
            )[:300] or None,
            "value": _format_value(raw_val),
            "cpv": str(item.get("mainCpvCode") or item.get("cpvCode") or "").strip() or None,
            "procedure_type": str(
                item.get("procedureType") or item.get("orderType")
                or item.get("procurementMode") or ""
            ).strip() or None,
            "url": url,
            "source": "BZP (ezamowienia.gov.pl)",
            "sector": _classify_sector(title, entity),
        }
    )


# ---------------------------------------------------------------------------
# Source 4: platformazakupowa.pl – HTML scraper
# ---------------------------------------------------------------------------

_PZP_BASE = "https://platformazakupowa.pl"
# Try multiple URL patterns — the platform has changed its search URL over time
_PZP_SEARCH_URLS = [
    "{base}/transakcje",
    "{base}/pn/szukaj",
    "{base}/transakcje/poczta",
]


def fetch_platformazakupowa() -> list[dict]:
    """Scrape search results from platformazakupowa.pl."""
    results: list[dict] = []
    search_terms = [
        "projekt architektoniczny",
        "projekt wykonawczy",
        "dokumentacja projektowa",
    ]
    for term in search_terms:
        for url_tpl in _PZP_SEARCH_URLS:
            try:
                _pzp_search(term, results, url_tpl.format(base=_PZP_BASE))
                break  # stop trying URLs once one succeeds
            except Exception as exc:
                log.debug("[PZP] %s with %r: %s", url_tpl, term, exc)
        else:
            log.warning("[PZP] All URL patterns failed for %r", term)
    log.info("[PZP] Collected %d results", len(results))
    return results


def _pzp_search(term: str, results: list[dict], search_url: str) -> None:
    resp = _get(search_url, params={"search": term, "q": term})
    resp.raise_for_status()
    soup = BeautifulSoup(resp.text, "lxml")

    for link in soup.select("a[href*='/transakcje/']"):
        href = link["href"]
        if not re.search(r"/transakcje/\d+", href):
            continue
        full_url = urljoin(_PZP_BASE, href)
        title = link.get_text(strip=True)
        if len(title) < 10:
            parent = link.find_parent()
            title = parent.get_text(" ", strip=True)[:200] if parent else title

        row_text = ""
        parent_row = (
            link.find_parent("tr")
            or link.find_parent("li")
            or link.find_parent("div")
        )
        if parent_row:
            row_text = parent_row.get_text(" ", strip=True)

        m = re.search(r"\b(\d{4}-\d{2}-\d{2})\b", row_text)
        pub_date = _parse_date(m.group(1)) if m else None
        if pub_date and not _within_window(pub_date):
            continue

        m_pzp = re.search(r'/transakcje/(\d+)', full_url)
        pzp_id = m_pzp.group(1) if m_pzp else None
        # Try to extract estimated value from the row text
        m_val = re.search(r'([\d\s]+[,.]\d{2})\s*(?:PLN|zł)', row_text, re.IGNORECASE)
        pzp_value = _format_value(m_val.group(1)) if m_val else None
        results.append(
            {
                "id": _make_id(full_url),
                "proc_id": pzp_id,
                "title": title,
                "entity": "",
                "publication_date": pub_date,
                "deadline": None,
                "description": None,
                "value": pzp_value,
                "cpv": None,
                "procedure_type": None,
                "url": full_url,
                "source": "platformazakupowa.pl",
                "sector": _classify_sector(title, ""),
            }
        )


# ---------------------------------------------------------------------------
# Deduplication
# ---------------------------------------------------------------------------


def deduplicate(
    tenders: list[dict],
    seen_ids: set[str],
) -> tuple[list[dict], set[str]]:
    """Remove any tender whose ID was seen in previous runs or this batch."""
    new_tenders: list[dict] = []
    batch_ids: set[str] = set()
    for t in tenders:
        tid = t["id"]
        if tid not in seen_ids and tid not in batch_ids:
            batch_ids.add(tid)
            new_tenders.append(t)
    seen_ids.update(batch_ids)
    log.info(
        "Deduplication: %d new / %d total (batch discarded %d duplicates)",
        len(new_tenders),
        len(tenders),
        len(tenders) - len(new_tenders),
    )
    return new_tenders, seen_ids


# ---------------------------------------------------------------------------
# Report persistence
# ---------------------------------------------------------------------------


def save_daily_report(tenders: list[dict]) -> None:
    today_str = TODAY.isoformat()

    # Merge with any existing report for today – never discard previously found data
    existing: list[dict] = []
    for candidate in (REPORTS_DIR / f"{today_str}.json", DOCS_REPORTS_DIR / f"{today_str}.json"):
        if candidate.exists():
            try:
                existing = json.loads(candidate.read_text(encoding="utf-8")).get("tenders", [])
                break
            except Exception:
                pass

    # New tenders take priority; re-append existing ones not in the fresh batch
    new_ids = {t["id"] for t in tenders}
    retained = [t for t in existing if t["id"] not in new_ids]
    merged = tenders + retained

    report = {
        "date": today_str,
        "count": len(merged),
        "generated_at": datetime.now(tz=timezone.utc).isoformat(),
        "tenders": merged,
    }
    payload = json.dumps(report, indent=2, ensure_ascii=False)
    (REPORTS_DIR / f"{today_str}.json").write_text(payload, encoding="utf-8")
    (DOCS_REPORTS_DIR / f"{today_str}.json").write_text(payload, encoding="utf-8")
    log.info(
        "Daily report saved: %s.json (%d new + %d retained = %d total)",
        today_str, len(tenders), len(retained), len(merged),
    )


def _build_manifest() -> list[dict]:
    """Return all available report dates sorted newest-first."""
    manifest: list[dict] = []
    for p in sorted(DOCS_REPORTS_DIR.glob("*.json"), reverse=True):
        try:
            date.fromisoformat(p.stem)  # validate it looks like a date
            manifest.append({"date": p.stem, "file": f"reports/{p.name}"})
        except ValueError:
            pass
    return manifest


# ---------------------------------------------------------------------------
# Dashboard generation (Jinja2 → docs/index.html)
# ---------------------------------------------------------------------------


def generate_dashboard() -> None:
    manifest = _build_manifest()
    if not manifest:
        log.warning("No report files found – skipping dashboard generation")
        return

    # Load most recent report for server-side initial render
    latest_name = Path(manifest[0]["file"]).name
    latest_report = json.loads(
        (DOCS_REPORTS_DIR / latest_name).read_text(encoding="utf-8")
    )

    env = Environment(
        loader=FileSystemLoader(str(TEMPLATES_DIR)),
        autoescape=select_autoescape(["html"]),
    )
    # Register tojson so the template can embed Python objects as JSON literals
    # Markup() marks the output safe so Jinja2 autoescape won't HTML-encode the quotes
    env.filters["tojson"] = lambda v: Markup(json.dumps(v, ensure_ascii=False))

    html = env.get_template("dashboard_template.html").render(
        manifest=manifest,
        latest_report=latest_report,
        generated_at=datetime.now(tz=timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
    )
    (DOCS_DIR / "index.html").write_text(html, encoding="utf-8")
    (DOCS_DIR / "manifest.json").write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False), encoding="utf-8"
    )
    log.info(
        "Dashboard written to docs/index.html (%d reports in manifest)", len(manifest)
    )


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def main() -> None:
    log.info(
        "=== Polish Tender Scraper | TODAY=%s | CUTOFF=%s ===",
        TODAY,
        CUTOFF_DATE,
    )
    seen_ids = load_history()
    log.info("Loaded %d previously seen tender IDs from history", len(seen_ids))

    all_tenders: list[dict] = []

    sources: list[tuple] = [
        (lambda: fetch_ddg(DDG_QUERIES), "DDG"),
        (fetch_ted, "TED"),
        (fetch_bzp, "BZP"),
        (fetch_platformazakupowa, "platformazakupowa"),
    ]

    for source_fn, label in sources:
        try:
            batch = source_fn()
            all_tenders.extend(batch)
        except Exception as exc:
            # One source failing must never abort the whole run
            log.error("[%s] Source failed entirely: %s", label, exc)

    # Enrich BZP tenders with per-notice detail API (fills description/value/cpv/procedure_type)
    bzp_to_enrich = [
        t for t in all_tenders
        if t.get("source") == "BZP (ezamowienia.gov.pl)" and t.get("proc_id")
        and not any(t.get(k) for k in ("description", "value", "cpv", "procedure_type"))
    ]
    if bzp_to_enrich:
        log.info("Enriching %d BZP tenders with detail API data…", len(bzp_to_enrich))
        for t in bzp_to_enrich:
            extra = _enrich_bzp_detail(t["proc_id"])
            for k, v in extra.items():
                if v and not t.get(k):
                    t[k] = v

    # Filter to the configurable time window
    before = len(all_tenders)
    all_tenders = [t for t in all_tenders if _within_window(t.get("publication_date"))]
    log.info(
        "Date filter: %d → %d tenders (cutoff: %s)", before, len(all_tenders), CUTOFF_DATE
    )

    new_tenders, seen_ids = deduplicate(all_tenders, seen_ids)

    save_history(seen_ids)
    save_daily_report(new_tenders)
    generate_dashboard()

    log.info(
        "=== Done. %d new tenders found and saved for %s ===",
        len(new_tenders),
        TODAY,
    )


if __name__ == "__main__":
    main()
