"""회계·세무 채용공고 대시보드 - 백엔드 (FastAPI)

수집 사이트: 잡코리아 · 사람인 · 인크루트 · 알바몬 · 고용24 · 한공회(수습CPA 구인게시판)

실행:
    pip install -r requirements.txt
    python -m playwright install chromium      # 한공회 수집용 (최초 1회)
    uvicorn app:app --reload
    → http://127.0.0.1:8000

환경변수 (선택):
    KICPA_URL           한공회 메인 주소 (기본 https://www.kicpa.or.kr/)
    KICPA_BOARD_PATH    구인 게시판 메뉴 경로 (기본: 알림마당 > 구인정보 > 수습CPA)
    KICPA_ROW_SELECTOR  목록 행 CSS 선택자 (기본 table tbody tr)
    KICPA_DEBUG         1이면 성공 시에도 debug/에 스크린샷 저장
    CACHE_TTL           캐시 유지 시간(초), 기본 600
    DB_PATH             데이터 파일 경로 (기본 ./data.db)

데이터(data.db):
    jobs      한 번이라도 수집된 공고 (처음/마지막 발견일 기록 → 목록에서 사라진 공고도 지원 현황에 남음)
    marks     내 지원 상태 + 메모
    settings  숨긴 회사, 제외 키워드
"""
import csv
import hashlib
import io
import json
import os
import re
import sqlite3
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from datetime import date, datetime, timedelta
from pathlib import Path
from urllib.parse import parse_qs, urljoin, urlparse

import requests
from bs4 import BeautifulSoup
from fastapi import Body, FastAPI, HTTPException, Query
from fastapi.responses import FileResponse, Response
from fastapi.staticfiles import StaticFiles

BASE_DIR = Path(__file__).parent
KICPA_URL = os.getenv("KICPA_URL", "https://www.kicpa.or.kr/")
KICPA_BOARD_PATH = os.getenv("KICPA_BOARD_PATH", "/portal/default/kicpa/gnb/kr_pc/menu05/menu09/menu07.page")
KICPA_DEBUG = os.getenv("KICPA_DEBUG") == "1"
KICPA_ROW_SELECTOR = os.getenv("KICPA_ROW_SELECTOR", "table tbody tr")
CACHE_TTL = int(os.getenv("CACHE_TTL", "600"))
DB_PATH = Path(os.getenv("DB_PATH", BASE_DIR / "data.db"))

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
    ),
    "Accept-Language": "ko-KR,ko;q=0.9",
}
TIMEOUT = 12
PART_TIME_RE = re.compile(r"파트\s?타임|part[\s\-]?time|시간제|(?<![가-힣])파트(?![가-힣])", re.I)
INTERN_RE = re.compile(r"인턴|intern|체험형|채용연계형", re.I)
SHORT_RE = re.compile(r"알바|아르바이트|단기|일용|시급|일당|일급|한시|(?<![0-9])[1-6]\s?개월\s?(근무|계약|단기)", re.I)
# 알바몬의 근무기간 중 '단기'로 볼 것
ALBAMON_SHORT_PERIODS = ("하루", "1주일이하", "1주일~1개월", "1개월~3개월", "3개월~6개월")

# 지원 상태 (화면의 순서와 같음)
STATUSES = ["관심", "지원예정", "지원완료", "서류합격", "면접", "최종합격", "불합격"]
DEFAULT_SETTINGS = {
    "hidden_companies": [],
    # 잡코리아에서 'CPA'(광고 단가) 마케팅 공고가, 알바몬에서 수강생 모집 광고가 섞여 나와서 기본으로 제외
    "exclude_words": ["마케터", "마케팅", "퍼포먼스", "광고대행", "취업교육", "기초교육", "교육생"],
}


# ───────────────────────── 공통 유틸 ─────────────────────────
def parse_deadline(text: str):
    """'~ 11/20(목)', '2026.11.20', 'D-5', '오늘마감' 등에서 날짜를 뽑는다. 못 찾으면 None(상시/미정)."""
    if not text:
        return None
    t = text.strip()
    today = date.today()
    if ("오늘" in t and "마감" in t) or re.search(r"(?<![\d/.~])\d{1,2}\s?시\s?마감", t):  # '23시 마감' = 오늘
        return today
    if "내일" in t and "마감" in t:
        return today + timedelta(days=1)
    m = re.search(r"D-(\d+)", t, re.I)
    if m:
        return today + timedelta(days=int(m.group(1)))
    m = re.search(r"(20\d{2})\s?[.\-/]\s?(\d{1,2})\s?[.\-/]\s?(\d{1,2})", t)
    if m:
        try:
            return date(int(m.group(1)), int(m.group(2)), int(m.group(3)))
        except ValueError:
            return None
    m = re.search(r"~\s?(\d{1,2})\s?[/.]\s?(\d{1,2})", t)
    if m:
        try:
            d = date(today.year, int(m.group(1)), int(m.group(2)))
        except ValueError:
            return None
        if d < today - timedelta(days=180):  # 연말에 내년 1월 공고를 볼 때
            d = d.replace(year=today.year + 1)
        return d
    return None


def parse_posted(text: str):
    """'등록일 26/09/17', '2026-11-03', '2026.11.03' → date"""
    if not text:
        return None
    m = re.search(r"(20\d{2})\s?[.\-/]\s?(\d{1,2})\s?[.\-/]\s?(\d{1,2})", text)
    if m:
        y, mo, d = map(int, m.groups())
    else:
        m = re.search(r"(?<!\d)(\d{2})/(\d{1,2})/(\d{1,2})(?!\d)", text)
        if not m:
            return None
        y, mo, d = 2000 + int(m.group(1)), int(m.group(2)), int(m.group(3))
    try:
        return date(y, mo, d)
    except ValueError:
        return None


def make_job(source, title, company, url, location="", career="", job_type="",
             deadline_text="", deadline_date=None, extra="", key=None, posted=None, closed=False,
             pay="", part_time=None, short_term=None, intern=None):
    """key: 공고를 구분하는 고유값 (없으면 url). 즐겨찾기/지원 현황이 이 값으로 연결된다.
    part_time/short_term/intern: 사이트가 알려 주면 그 값을, 아니면 제목·조건 글자로 추정."""
    deadline_date = deadline_date or parse_deadline(deadline_text)
    blob = " ".join([title or "", job_type or "", extra or ""])
    head = " ".join([title or "", job_type or ""])  # 본문 전체까지 보면 오탐이 많아 제목·고용형태만
    return {
        "id": hashlib.md5((key or url).encode()).hexdigest()[:12],
        "source": source,
        "title": re.sub(r"\s+", " ", title or "").strip(),
        "company": (company or "").strip(),
        "url": url,
        "location": re.sub(r"\s+", " ", location or "").strip(),
        "career": (career or "").strip(),
        "job_type": (job_type or "").strip(),
        "deadline_text": (deadline_text or "").strip()[:80],
        "deadline_date": deadline_date.isoformat() if deadline_date else None,
        "posted_date": posted.isoformat() if posted else None,
        "pay": re.sub(r"\s+", " ", pay or "").strip(),
        "part_time": bool(PART_TIME_RE.search(blob)) if part_time is None else bool(part_time),
        "short_term": bool(SHORT_RE.search(head)) if short_term is None else bool(short_term),
        "intern": bool(INTERN_RE.search(head)) if intern is None else bool(intern),
        "closed": bool(closed),
    }


def get_html(url, **kwargs):
    r = requests.get(url, headers=HEADERS, timeout=TIMEOUT, **kwargs)
    r.raise_for_status()
    if not r.encoding or r.encoding.lower() == "iso-8859-1":
        r.encoding = r.apparent_encoding
    return BeautifulSoup(r.text, "html.parser")


# ───────────────────────── 사람인 ─────────────────────────
def fetch_saramin(keyword):
    soup = get_html(
        "https://www.saramin.co.kr/zf_user/search/recruit",
        params={"searchword": keyword, "recruitPageCount": 40},
    )
    jobs = []
    for item in soup.select(".item_recruit"):
        a = item.select_one(".job_tit a")
        if not a:
            continue
        href = urljoin("https://www.saramin.co.kr", a.get("href", ""))
        # 검색어가 주소에 붙어 키워드마다 주소가 달라지므로, 공고번호로 깔끔한 주소를 만든다
        rec = item.get("value") or (parse_qs(urlparse(href).query).get("rec_idx") or [""])[0]
        url = f"https://www.saramin.co.kr/zf_user/jobs/relay/view?rec_idx={rec}" if rec else href
        corp = item.select_one(".corp_name a")
        cond = [s.get_text(strip=True) for s in item.select(".job_condition span")]
        date_el = item.select_one(".job_date .date")
        day_el = item.select_one(".job_day")
        jobs.append(make_job(
            "saramin",
            a.get("title") or a.get_text(strip=True),
            corp.get_text(strip=True) if corp else "",
            url,
            location=cond[0] if len(cond) > 0 else "",
            career=cond[1] if len(cond) > 1 else "",
            job_type=cond[3] if len(cond) > 3 else "",
            deadline_text=date_el.get_text(strip=True) if date_el else "",
            extra=item.get_text(" ", strip=True),
            key=f"saramin:{rec}" if rec else None,
            posted=parse_posted(day_el.get_text(strip=True)) if day_el else None,
        ))
    return jobs


# ───────────────────────── 잡코리아 ─────────────────────────
def fetch_jobkorea(keyword):
    """클래스명이 자주 바뀌므로 '공고 링크 패턴'을 기준으로 잡고, 같은 카드 안에서 나머지를 찾는다."""
    soup = get_html(
        "https://www.jobkorea.co.kr/Search/",
        params={"stext": keyword, "tabType": "recruit"},
    )
    jobs, seen = [], set()
    for a in soup.select('a[href*="/Recruit/GI_Read/"]'):
        url = urljoin("https://www.jobkorea.co.kr", a["href"]).split("?")[0]
        title = a.get_text(" ", strip=True)
        if url in seen or len(title) < 4:
            continue
        seen.add(url)
        box = a.find_parent(["li", "article"]) or a.parent.parent
        co = box.select_one('a[href*="/Recruit/Co_Read/"]')
        text = box.get_text(" ", strip=True)
        career = re.search(r"(신입|경력무관|경력\s?\d+년?[~\-\s\d년]*|경력)", text)
        loc = re.search(r"(서울|경기|인천|부산|대구|대전|광주|울산|세종|강원|충북|충남|전북|전남|경북|경남|제주)\S*(\s\S+구)?", text)
        dl = re.search(r"(오늘\s?마감|내일\s?마감|D-\d+|~\s?\d{1,2}[/.]\d{1,2}|20\d{2}[.\-/]\d{1,2}[.\-/]\d{1,2}\s?마감)", text, re.I)
        jobs.append(make_job(
            "jobkorea", title,
            co.get_text(strip=True) if co else "",
            url,
            location=loc.group(0) if loc else "",
            career=career.group(0).strip() if career else "",
            deadline_text=dl.group(0) if dl else "",
            extra=text,
        ))
    return jobs


# ───────────────────────── 인크루트 ─────────────────────────
def fetch_incruit(keyword):
    soup = get_html("https://search.incruit.com/list/search.asp", params={"col": "job", "kw": keyword})
    jobs = []
    for row in soup.select("li.c_col"):
        a = row.select_one('a[href*="jobdb_info/jobpost.asp"]')
        if not a:
            continue
        m = re.search(r"job=(\d+)", a["href"])
        url = f"https://job.incruit.com/jobdb_info/jobpost.asp?job={m.group(1)}" if m else a["href"]
        co = row.select_one("a.cpname")
        conds = [s.get_text(strip=True) for s in row.select(".cell_mid .cl_md span")]
        last = " ".join(s.get_text(strip=True) for s in row.select(".cell_last span"))
        # 조건 칸: 지역 · 경력 · 학력 · 고용형태 순
        jobs.append(make_job(
            "incruit", a.get_text(), co.get_text(strip=True) if co else "", url,  # 강조 표시 앞뒤에 공백이 끼지 않게
            location=conds[0] if conds else "",
            career=next((c for c in conds if "경력" in c or "신입" in c), ""),
            job_type=next((c for c in conds if re.search(r"정규|계약|인턴|아르바이트|파견|프리랜서|위촉", c)), ""),
            deadline_text=last, extra=row.get_text(" ", strip=True),
            key=f"incruit:{m.group(1)}" if m else None,
        ))
    return jobs


# ───────────────────────── 알바몬 ─────────────────────────
def _relative_posted(text):
    """알바몬 등록 시각: '23분전', '5시간전', '3일전', '2026.11.01' 등"""
    if not text:
        return None
    if re.search(r"(분|시간)\s?전|방금|오늘", text):
        return date.today()
    m = re.search(r"(\d+)\s?일\s?전", text)
    if m:
        return date.today() - timedelta(days=int(m.group(1)))
    return parse_posted(text)


ALBAMON_OFFICE_RE = re.compile(r"사무|경리|회계|세무|재무|총무|인사|금융|보험|비서|문서|데이터|자료|전산|ERP|행정|은행|증권", re.I)


def fetch_albamon(keyword, pages=2):
    """알바몬 통합검색 화면의 Next.js 데이터(__NEXT_DATA__)에서 공고 목록을 읽는다.
    알바몬은 전부 알바라서 '알바'를 붙이면 오히려 검색이 흐려지므로 빼고 찾고,
    업직종(parts)이 사무·회계 계열인 공고만 남긴다 ('남동세무서점' 같은 식당 공고 제외)."""
    keyword = re.sub(r"알바|아르바이트", "", keyword).strip() or keyword
    jobs = []
    for page in range(1, pages + 1):
        r = requests.get("https://www.albamon.com/total-search", params={"keyword": keyword, "page": page},
                         headers=HEADERS, timeout=TIMEOUT)
        r.raise_for_status()
        m = re.search(r'<script id="__NEXT_DATA__"[^>]*>(.*?)</script>', r.content.decode("utf-8", "replace"), re.S)
        if not m:
            raise RuntimeError("알바몬 화면 구조가 바뀌었어요 (__NEXT_DATA__ 없음)")
        items = []
        for q in json.loads(m.group(1))["props"]["pageProps"].get("dehydratedState", {}).get("queries", []):
            if q.get("queryKey", [None])[0] == "SEARCH_RECRUIT_LIST":
                items = (((q.get("state") or {}).get("data") or {}).get("base") or {}).get("normal", {}).get("collection", [])
                break
        for it in items:
            no = it.get("recruitNo")
            if not no or not it.get("recruitTitle"):
                continue
            period = it.get("workingPeriod") or ""
            pay_type = (it.get("payType") or {}).get("description", "")
            parts = it.get("parts") or []
            if parts and not any(ALBAMON_OFFICE_RE.search(p) for p in parts):
                continue
            closing = it.get("closingDate") or ""
            jobs.append(make_job(
                "albamon", it["recruitTitle"], it.get("companyName", ""),
                f"https://www.albamon.com/jobs/detail/{no}",
                location=it.get("workplaceArea", ""),
                job_type=" · ".join(x for x in [period, it.get("workingWeek") or "", it.get("workingTime") or ""] if x),
                deadline_date=parse_posted(closing),
                deadline_text=closing,
                extra=" ".join([*parts, period]),
                key=f"albamon:{no}",
                posted=_relative_posted(it.get("postedDate", "")),
                pay=f"{pay_type} {it.get('pay', '')}".strip(),
                short_term=period in ALBAMON_SHORT_PERIODS or bool(SHORT_RE.search(it["recruitTitle"])),
            ))
        if len(items) < 20:
            break
    return jobs


# ───────────────────────── 고용24 (워크넷) ─────────────────────────
def fetch_work24(keyword):
    """고용노동부 고용24 채용정보 상세검색. 제목에 키워드가 들어간 공고만 (본문까지 찾으면 무관한 공고가 많음)."""
    soup = get_html(
        "https://www.work24.go.kr/wk/a/b/1200/retriveDtlEmpSrchList.do",
        params={"srcKeyword": keyword, "keywordWantedTitle": "Y", "pageIndex": 1, "resultCnt": 50,
                "sortField": "DATE", "sortOrderBy": "DESC"},
    )
    jobs = []
    for tr in soup.select('tr[id^="list"]'):
        a = tr.select_one('a[href*="wantedAuthNo="]')
        if not a:
            continue
        no = re.search(r"wantedAuthNo=([A-Za-z0-9]+)", a["href"]).group(1)
        co = tr.select_one("a.cp_name")
        text = re.sub(r"\s+", " ", tr.get_text(" ", strip=True))
        info = lambda cls: re.sub(r"\s+", " ", (tr.select_one(f"li.{cls}") or BeautifulSoup("", "html.parser")).get_text(" ", strip=True))
        member, worktime = info("member"), info("time")
        hours = re.search(r"주\s?(\d+)\s?시간", worktime)
        dl = re.search(r"마감일\s?:\s?([\d\-]+)", text)
        reg = re.search(r"등록일\s?:\s?([\d\-]+)", text)
        jobs.append(make_job(
            "work24", a.get_text(" ", strip=True), co.get_text(strip=True) if co else "",
            urljoin("https://www.work24.go.kr", a["href"]),
            location=info("site"),
            career=next((w for w in member.split(" ") if "경력" in w or "신입" in w), ""),
            job_type=worktime,
            deadline_text=dl.group(1) if dl else "",
            extra=text, key=f"work24:{no}",
            posted=parse_posted(reg.group(1)) if reg else None,
            pay=info("dollar"),
            part_time=(hours and int(hours.group(1)) < 35) or None,
        ))
    return jobs


# ───────────────────────── 한공회 구인게시판 (알림마당 > 구인정보 > 수습CPA) ─────────────────────────
# 한공회는 주소가 안 바뀌는 iframe 구조라서 헤드리스 크롬(Playwright)으로 사이트의 메뉴 이동 함수
# fn_pageFilter(...)를 그대로 호출해 목록 화면(iframe)을 연 뒤, 모든 프레임에서 목록 행을 읽는다.
# 표 머리글: 번호 | 제목 | 회사명 | 지역 | 구직완료 구분 | 고용형태 | 등록일자 | 조회수
_KICPA_ROW_JS = """rs => rs.map(r => {
    const a = r.querySelector('a');
    const t = r.closest('table');
    return {
        cells: [...r.querySelectorAll('td,th')].map(c => c.innerText.replace(/\\s+/g, ' ').trim()),
        heads: t ? [...t.querySelectorAll('thead th')].map(c => c.innerText.trim()) : [],
        title: a ? a.innerText.trim() : '',
        href: a ? a.href : '',
        onclick: a ? (a.getAttribute('onclick') || '') : ''
    };
})"""


def _kicpa_debug(page, tag):
    d = BASE_DIR / "debug"
    d.mkdir(exist_ok=True)
    try:
        page.screenshot(path=str(d / f"kicpa_{tag}.png"), full_page=True)
        for i, f in enumerate(page.frames):
            try:
                (d / f"kicpa_{tag}_frame{i}.html").write_text(f.content(), encoding="utf-8")
            except Exception:
                pass
    except Exception:
        pass


def _kicpa_rows(page):
    """모든 프레임에서 행을 찾아, 가장 많이 찾은 프레임의 행을 쓴다."""
    best = []
    for f in page.frames:
        try:
            rows = f.eval_on_selector_all(KICPA_ROW_SELECTOR, _KICPA_ROW_JS)
        except Exception:  # 이동 중 사라진 프레임 등
            continue
        rows = [r for r in rows if r["title"]]
        if len(rows) > len(best):
            best = rows
    return best


def _kicpa_open_board(page):
    page.goto(KICPA_URL, wait_until="networkidle", timeout=30000)
    for f in page.frames:  # 사이트 자체의 메뉴 이동 함수를 호출 (메뉴 클릭과 동일한 동작)
        try:
            if f.evaluate("typeof fn_pageFilter === 'function'"):
                f.evaluate("p => fn_pageFilter(p, '_self', 'false')", KICPA_BOARD_PATH)
                return "fn_pageFilter"
        except Exception:
            continue
    page.goto(urljoin(KICPA_URL, KICPA_BOARD_PATH), wait_until="networkidle", timeout=30000)
    return "goto"


def fetch_kicpa(keyword):
    from playwright.sync_api import sync_playwright

    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True)
        page = None
        try:
            page = browser.new_context(user_agent=HEADERS["User-Agent"], locale="ko-KR").new_page()
            _kicpa_open_board(page)
            rows = []
            for _ in range(15):  # 목록이 뜰 때까지 최대 15초
                rows = _kicpa_rows(page)
                if rows:
                    break
                page.wait_for_timeout(1000)
            if not rows:
                raise RuntimeError("수습CPA 목록에서 공고 행을 찾지 못했어요 (debug 폴더 확인)")
            if KICPA_DEBUG:
                _kicpa_debug(page, "ok")
        except Exception:
            if page is not None:
                _kicpa_debug(page, "error")
            raise
        finally:
            browser.close()
    return parse_kicpa_rows(rows)


def parse_kicpa_rows(rows):
    board_url = urljoin(KICPA_URL, KICPA_BOARD_PATH)  # 상세는 POST 방식이라 목록 화면으로 연결
    jobs = []
    for r in rows:
        title = r["title"]
        if len(title) < 2:
            continue
        cells, heads = r["cells"], r.get("heads") or []

        def col(name, fallback_idx):
            for i, h in enumerate(heads):
                if name in h and i < len(cells):
                    return cells[i]
            return cells[fallback_idx] if len(cells) > fallback_idx else ""

        company = col("회사", 2)
        if not company:
            m = re.match(r"\s*[\[<(（]([^\]>)）]{2,30})[\]>)）]", title)  # 제목 앞의 [회사명]
            company = m.group(1).strip() if m else ""
        location = col("지역", 3).replace("전체", "").strip()
        state = col("구직", 4)
        job_type = col("고용", 5)
        posted = parse_posted(col("등록", 6))
        m = re.search(r"fn_detail\('?(\d+)", r.get("onclick", ""))
        key = f"kicpa:{m.group(1)}" if m else f"kicpa:{company}:{title}"
        # 마감일은 제목에 적힌 경우만 인식 (게시판의 날짜 칸은 '등록일'이라 마감일이 아님)
        jobs.append(make_job("kicpa", title, company, board_url, location=location, job_type=job_type,
                             deadline_text=title, extra=" ".join(c for c in cells if c),
                             key=key, posted=posted, closed="완료" in state))
    return jobs  # 이 게시판은 이미 수습CPA 전용이라 키워드로 거르지 않음


SOURCES = {
    "jobkorea": ("잡코리아", fetch_jobkorea),
    "saramin": ("사람인", fetch_saramin),
    "incruit": ("인크루트", fetch_incruit),
    "albamon": ("알바몬", fetch_albamon),
    "work24": ("고용24", fetch_work24),
    "kicpa": ("한공회", fetch_kicpa),
}
DEFAULT_KEYWORD = "공인회계사, 회계, 세무"
KEYWORDLESS = {"kicpa"}  # 키워드와 상관없이 한 번만 수집


# ───────────────────────── 저장소 (SQLite) ─────────────────────────
_db_lock = threading.Lock()


def db():
    con = sqlite3.connect(DB_PATH, check_same_thread=False)
    con.row_factory = sqlite3.Row
    return con


def init_db():
    with _db_lock, db() as con:
        con.executescript("""
            CREATE TABLE IF NOT EXISTS jobs (
                id TEXT PRIMARY KEY, source TEXT, data TEXT,
                first_seen TEXT, last_seen TEXT);
            CREATE TABLE IF NOT EXISTS marks (
                id TEXT PRIMARY KEY, status TEXT, memo TEXT, updated_at TEXT);
            CREATE TABLE IF NOT EXISTS settings (key TEXT PRIMARY KEY, value TEXT);
        """)


def save_jobs(jobs):
    """수집한 공고를 기록하고 각 공고에 first_seen(처음 발견 시각)을 붙인다."""
    now = datetime.now().isoformat(timespec="seconds")
    with _db_lock, db() as con:
        for j in jobs:
            row = con.execute("SELECT first_seen FROM jobs WHERE id=?", (j["id"],)).fetchone()
            first = row["first_seen"] if row else now
            con.execute(
                "INSERT INTO jobs(id, source, data, first_seen, last_seen) VALUES(?,?,?,?,?) "
                "ON CONFLICT(id) DO UPDATE SET data=excluded.data, last_seen=excluded.last_seen",
                (j["id"], j["source"], json.dumps(j, ensure_ascii=False), first, now),
            )
            j["first_seen"] = first


def get_settings():
    with _db_lock, db() as con:
        rows = con.execute("SELECT key, value FROM settings").fetchall()
    s = {k: list(v) for k, v in DEFAULT_SETTINGS.items()}
    s.update({r["key"]: json.loads(r["value"]) for r in rows if r["key"] in DEFAULT_SETTINGS})
    return s


def get_marks():
    with _db_lock, db() as con:
        rows = con.execute(
            "SELECT m.id, m.status, m.memo, m.updated_at, j.data, j.first_seen, j.last_seen "
            "FROM marks m LEFT JOIN jobs j ON j.id = m.id"
        ).fetchall()
    out = {}
    for r in rows:
        job = json.loads(r["data"]) if r["data"] else None
        if job:
            job["first_seen"], job["last_seen"] = r["first_seen"], r["last_seen"]
        out[r["id"]] = {"status": r["status"], "memo": r["memo"], "updated_at": r["updated_at"], "job": job}
    return out


# ───────────────────────── 수집 ─────────────────────────
_cache = {}


def split_keywords(keyword):
    kws = [k.strip() for k in re.split(r"[,，]", keyword or "") if k.strip()]
    return list(dict.fromkeys(kws)) or split_keywords(DEFAULT_KEYWORD)


def collect(keyword):
    """키워드는 쉼표로 여러 개 가능. (사이트, 키워드) 조합을 동시에 수집한다."""
    keywords = split_keywords(keyword)
    tasks = [(src, kw) for src in SOURCES for kw in (keywords[:1] if src in KEYWORDLESS else keywords)]
    status = {k: {"label": SOURCES[k][0], "count": 0, "error": None} for k in SOURCES}

    def run(task):
        src, kw = task
        try:
            return src, kw, SOURCES[src][1](kw), None
        except Exception as e:  # 한 사이트가 실패해도 나머지는 보여준다
            return src, kw, [], f"{type(e).__name__}: {e}"

    results = []
    with ThreadPoolExecutor(max_workers=min(10, len(tasks))) as pool:
        for src, kw, jobs, err in pool.map(run, tasks):
            for j in jobs:
                j.setdefault("keywords", []).append(kw)
            status[src]["count"] += len(jobs)
            if err:
                status[src]["error"] = (status[src]["error"] + " / " if status[src]["error"] else "") + (
                    f"[{kw}] {err}" if len(keywords) > 1 and src not in KEYWORDLESS else err)
            results.extend(jobs)

    # 같은 공고(ID) 합치기 + 사이트 간 중복 제거 (회사명 + 제목 기준)
    by_id, seen, unique = {}, set(), []
    for j in results:
        if j["id"] in by_id:
            by_id[j["id"]]["keywords"] = list(dict.fromkeys(by_id[j["id"]]["keywords"] + j["keywords"]))
            continue
        k = re.sub(r"\s|\(주\)|㈜|주식회사", "", j["company"] + j["title"]).lower()
        if k in seen:
            continue
        seen.add(k)
        by_id[j["id"]] = j
        unique.append(j)
    for src in status:
        status[src]["count"] = sum(1 for j in unique if j["source"] == src)
    save_jobs(unique)
    return unique, status


# ───────────────────────── API ─────────────────────────
app = FastAPI(title="회계·세무 채용공고 대시보드")
init_db()


@app.get("/api/jobs")
def api_jobs(keyword: str = Query(DEFAULT_KEYWORD), refresh: bool = False):
    now = time.time()
    ck = ",".join(split_keywords(keyword))
    hit = _cache.get(ck)
    if hit and not refresh and now - hit["ts"] < CACHE_TTL:
        return hit["payload"]
    jobs, status = collect(keyword)
    payload = {
        "keyword": ck,
        "fetched_at": datetime.now().isoformat(timespec="seconds"),
        "jobs": jobs,
        "sources": status,
    }
    _cache[ck] = {"ts": now, "payload": payload}
    return payload


@app.get("/api/marks")
def api_marks():
    return {"statuses": STATUSES, "marks": get_marks()}


@app.put("/api/marks/{job_id}")
def api_set_mark(job_id: str, body: dict = Body(...)):
    status = (body.get("status") or "").strip()
    memo = (body.get("memo") or "").strip()[:2000]
    if status and status not in STATUSES:
        raise HTTPException(400, f"알 수 없는 상태: {status}")
    with _db_lock, db() as con:
        if not status and not memo:
            con.execute("DELETE FROM marks WHERE id=?", (job_id,))
        else:
            con.execute(
                "INSERT INTO marks(id, status, memo, updated_at) VALUES(?,?,?,?) "
                "ON CONFLICT(id) DO UPDATE SET status=excluded.status, memo=excluded.memo, updated_at=excluded.updated_at",
                (job_id, status, memo, datetime.now().isoformat(timespec="seconds")),
            )
    return {"ok": True}


@app.get("/api/settings")
def api_settings():
    return get_settings()


@app.put("/api/settings")
def api_set_settings(body: dict = Body(...)):
    with _db_lock, db() as con:
        for k in DEFAULT_SETTINGS:
            if k in body:
                vals = [str(v).strip() for v in body[k] if str(v).strip()]
                con.execute("INSERT OR REPLACE INTO settings(key, value) VALUES(?,?)",
                            (k, json.dumps(list(dict.fromkeys(vals)), ensure_ascii=False)))
    return get_settings()


def _ics_escape(s):
    return re.sub(r"([,;\\])", r"\\\1", s or "").replace("\n", "\\n")


@app.get("/api/calendar.ics")
def api_calendar():
    """지원 현황에 넣은 공고의 마감일을 캘린더 파일로 (구글/아웃룩 캘린더에 가져오기)."""
    lines = ["BEGIN:VCALENDAR", "VERSION:2.0", "PRODID:-//cpa-dashboard//KO", "CALSCALE:GREGORIAN",
             "X-WR-CALNAME:회계사 채용 마감일"]
    stamp = datetime.now().strftime("%Y%m%dT%H%M%S")
    for jid, m in get_marks().items():
        j = m["job"]
        if not j or not j.get("deadline_date") or m["status"] in ("최종합격", "불합격"):
            continue
        d = date.fromisoformat(j["deadline_date"])
        name = f"{j['company']} - {j['title']}" if j.get("company") else j["title"]
        lines += [
            "BEGIN:VEVENT", f"UID:{jid}@cpa-dashboard", f"DTSTAMP:{stamp}",
            f"DTSTART;VALUE=DATE:{d:%Y%m%d}", f"DTEND;VALUE=DATE:{d + timedelta(days=1):%Y%m%d}",
            f"SUMMARY:{_ics_escape(f'[마감] {name}')}",
            f"DESCRIPTION:{_ics_escape(f'상태: {m['status'] or '-'}\n{m['memo'] or ''}\n{j['url']}')}",
            f"URL:{j['url']}",
            "BEGIN:VALARM", "TRIGGER:-P1D", "ACTION:DISPLAY", "DESCRIPTION:내일 마감", "END:VALARM",
            "END:VEVENT",
        ]
    lines.append("END:VCALENDAR")
    return Response("\r\n".join(lines) + "\r\n", media_type="text/calendar; charset=utf-8",
                    headers={"Content-Disposition": "attachment; filename=cpa-deadlines.ics"})


@app.get("/api/marks.csv")
def api_marks_csv():
    """지원 현황을 엑셀에서 열 수 있는 CSV로."""
    buf = io.StringIO()
    w = csv.writer(buf)
    w.writerow(["상태", "회사", "제목", "마감일", "지역", "경력", "출처", "메모", "수정일", "링크"])
    order = {s: i for i, s in enumerate(STATUSES)}
    marks = sorted(get_marks().values(), key=lambda m: (order.get(m["status"], 99), m["updated_at"] or ""))
    for m in marks:
        j = m["job"] or {}
        w.writerow([m["status"], j.get("company", ""), j.get("title", ""), j.get("deadline_date") or "",
                    j.get("location", ""), j.get("career", ""), SOURCES.get(j.get("source"), ("",))[0],
                    m["memo"], (m["updated_at"] or "").replace("T", " "), j.get("url", "")])
    return Response("﻿" + buf.getvalue(), media_type="text/csv; charset=utf-8",
                    headers={"Content-Disposition": "attachment; filename=cpa-applications.csv"})


app.mount("/static", StaticFiles(directory=BASE_DIR / "static"), name="static")


@app.get("/")
def index():
    return FileResponse(BASE_DIR / "static" / "index.html")
