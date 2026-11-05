"""한공회 접속 진단 도구.  실행: python kicpa_debug.py
크롬 창이 직접 뜨고, 한공회 수습CPA 목록을 여는 과정과 읽은 공고를 출력해요."""
import traceback

from playwright.sync_api import sync_playwright

import app

with sync_playwright() as p:
    browser = p.chromium.launch(headless=False, slow_mo=300)
    try:
        page = browser.new_context(locale="ko-KR", viewport={"width": 1400, "height": 900}).new_page()
        how = app._kicpa_open_board(page)
        print("목록 여는 방식:", how)
        rows = []
        for _ in range(15):
            rows = app._kicpa_rows(page)
            if rows:
                break
            page.wait_for_timeout(1000)
        print("읽은 공고 수:", len(rows))
        for r in rows[:5]:
            print("  -", r["title"], "|", r["cells"])
        for i, f in enumerate(page.frames):
            print(f"  프레임{i}: {f.url[:100]}")
        app._kicpa_debug(page, "diag")
    except Exception:
        print("\n!!! 오류가 발생했어요. 아래 내용을 복사해서 보내 주세요 !!!")
        traceback.print_exc()
    finally:
        input("\n확인이 끝나면 엔터를 누르세요...")
        browser.close()
