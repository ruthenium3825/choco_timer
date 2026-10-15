"""Puretomo access through an isolated, user-authenticated WebView2 browser.

Endpoints and payloads follow the closet site's own client (2026-10-15).
Authentication stays in the browser profile; no cookies or passwords cross IPC.
"""

import json
import os
import queue
import threading
import time
from urllib.parse import urlparse


CLOSET_URL = "https://puretomo.hange.jp/closet/"
API_ORIGIN = "https://puretomo-ap.hange.jp"


class ClosetError(Exception):
    pass


class LoginRequired(ClosetError):
    pass


class ClosetClient:
    def __init__(self, window):
        self.window = window
        self.mannequins = {}

    def request(self, method, path, body=None):
        page_url = urlparse(self.window.get_current_url() or "")
        if page_url.scheme != "https" or page_url.hostname != "puretomo.hange.jp":
            raise LoginRequired("専用クローゼット画面でログインしてください。")
        if method not in {"GET", "PUT"} or not path.startswith("/api/"):
            raise ClosetError("クローゼットへの要求が不正です。")
        arguments = json.dumps({"url": API_ORIGIN + path, "method": method, "body": body})
        script = r"""(async function(a) {
            const controller = new AbortController();
            const timer = setTimeout(() => controller.abort(), 15000);
            try {
                // Match the website's Axios XSRF handling without exporting the token.
                const headers = {'Content-Type':'application/json', 'Accept':'application/json, text/plain, */*'};
                const xsrf = document.cookie.match(/(?:^|;\s*)XSRF-TOKEN=([^;]*)/);
                if (xsrf) headers['X-XSRF-TOKEN'] = decodeURIComponent(xsrf[1]);
                const r = await fetch(a.url, {
                    method: a.method, credentials: 'include', cache: 'no-store',
                    headers: headers,
                    body: a.body == null ? undefined : JSON.stringify(a.body),
                    signal: controller.signal
                });
                if (!r.ok) return {status:r.status, ok:false, data:{}};
                const text = await r.text();
                const data = text ? JSON.parse(text) : {};
                return {status:r.status, ok:r.ok, data:data};
            } catch(e) { return {failed:true}; }
            finally { clearTimeout(timer); }
        })(""" + arguments + ")"
        done = threading.Event()
        result = []

        def receive(value):
            result.append(value)
            done.set()

        self.window.evaluate_js(script, callback=receive)
        if not done.wait(18) or not result or not isinstance(result[0], dict):
            raise ClosetError("通信結果を確認できません。クローゼット画面で状態を確認してください。")
        response = result[0]
        if response.get("status") in {401, 403}:
            raise LoginRequired("ログインの有効期限が切れました。再度ログインしてください。")
        if response.get("failed") or not response.get("ok"):
            raise ClosetError("通信に失敗しました。クローゼット画面で状態を確認してください。")
        data = response.get("data")
        if not isinstance(data, dict):
            raise ClosetError("クローゼットの応答を読み取れません。")
        return data.get("result")

    def refresh(self):
        mannequins = {}
        page = 1
        while True:
            result = self.request("GET", f"/api/closet/mannequin.json?page={page}")
            if not isinstance(result, dict) or not isinstance(result.get("mannequinList"), list):
                raise LoginRequired("専用クローゼット画面でログインしてください。")
            for position, entry in enumerate(result["mannequinList"]):
                if not isinstance(entry, dict) or not isinstance(entry.get("avatarLayer"), dict):
                    continue  # Empty slots are not selectable outfits.
                seq = entry.get("seq")
                if not isinstance(seq, (int, str)) or isinstance(seq, bool) or str(seq).strip() == "":
                    raise ClosetError("マネキンの情報を読み取れません。")
                name = str(entry.get("mqTitle") or "").strip() or f"マネキン {(page - 1) * 15 + position + 1}"
                mannequins[seq] = {"seq": seq, "name": name, "skin": entry["avatarLayer"].get("skin")}
            max_page = result.get("maxPage", 1)
            if not isinstance(max_page, int) or not 0 <= max_page <= 100:
                raise ClosetError("マネキンのページ数を読み取れません。")
            if page >= max_page:
                break
            page += 1
        self.mannequins = mannequins
        return [{"seq": entry["seq"], "name": entry["name"]} for entry in mannequins.values()]

    @staticmethod
    def _wear_signature(wear):
        if not isinstance(wear, dict) or not isinstance(wear.get("wearList"), list):
            raise ClosetError("着替え情報を読み取れません。")
        try:
            return str(wear["skin"]), sorted(str(item["seq"]) for item in wear["wearList"])
        except (KeyError, TypeError):
            raise ClosetError("着替え情報を読み取れません。") from None

    def save(self, seq):
        self.refresh()  # Detect logout/account changes and edits made on the website.
        mannequin = self.mannequins.get(seq)
        if mannequin is None:
            raise ClosetError("マネキン一覧を更新してから選択してください。")
        current = self.request("GET", "/api/user/wearlist.json")
        self._wear_signature(current)
        if not all(key in current for key in ("avatarId", "sex")) or mannequin["skin"] is None:
            raise ClosetError("着替え情報を読み取れません。")
        wear = self.request("PUT", "/api/closet/mannequin/wear.json", {"seq": seq})
        if not isinstance(wear, dict) or not isinstance(wear.get("ngList"), list) or not isinstance(wear.get("wearList"), list):
            raise ClosetError("着用できるアイテムを確認できません。保存は行っていません。")
        if wear["ngList"]:
            raise ClosetError("着用できないアイテムがあります。クローゼット画面で確認してください。保存は行っていません。")
        desired = {key: current[key] for key in ("avatarId", "sex")}
        desired.update(skin=mannequin["skin"], wearList=wear["wearList"])
        signature = self._wear_signature(desired)
        if signature == self._wear_signature(current):
            return "選択した着替えは保存済みです。"
        # Never retry this mutation automatically: a timeout may still mean it was applied.
        self.request("PUT", "/api/user/avatar.json", desired)
        verified = self.request("GET", "/api/user/wearlist.json")
        if self._wear_signature(verified) != signature:
            raise ClosetError("保存結果が一致しません。クローゼット画面で状態を確認してください。")
        return "着替えを保存しました。左の「アバター更新」でゲームへ反映できます。"


def run_closet_browser(commands, responses, profile_path):
    """Separate process: WebView2 and Tk both require their own main GUI thread."""
    try:
        import webview
    except ImportError:
        responses.put({"type": "error", "message": "クローゼット連携用の追加ライブラリがありません。READMEの導入手順を確認してください。"})
        return

    window = None
    stopped = threading.Event()
    try:
        window = webview.create_window("クローゼット連携 — ハンゲにログイン", CLOSET_URL,
                                       width=1100, height=780, hidden=True)
        window.events.closed += lambda: stopped.set()
        def keep_session():
            if not stopped.is_set():
                window.hide()
                return False
        # Closing the login screen must not discard its session cookies.
        window.events.closing += keep_session
        client = ClosetClient(window)

        def worker():
            pending_refresh = True
            next_probe = 0
            last_login_message = False
            hide_after_refresh = True
            allow_login = True
            window.events.loaded.wait(30)
            while not stopped.is_set():
                try:
                    command = commands.get(timeout=0.2)
                except queue.Empty:
                    command = None
                try:
                    if command:
                        action = command.get("action")
                        if action == "close":
                            stopped.set()
                            window.destroy()
                            return
                        if action == "show":
                            window.show()
                            pending_refresh = True
                            last_login_message = False
                            hide_after_refresh = False
                            allow_login = True
                        elif action == "refresh":
                            pending_refresh = True
                            last_login_message = False
                            hide_after_refresh = True
                            allow_login = True
                        elif action == "save":
                            message = client.save(command.get("seq"))
                            responses.put({"type": "saved", "message": message})
                    if pending_refresh and time.monotonic() >= next_probe:
                        next_probe = time.monotonic() + 3
                        items = client.refresh()
                        responses.put({"type": "items", "items": items})
                        pending_refresh = False
                        last_login_message = False
                        allow_login = False
                        if hide_after_refresh:
                            window.hide()
                except LoginRequired as error:
                    pending_refresh = allow_login
                    if not last_login_message:
                        responses.put({"type": "login", "message": str(error)})
                        if pending_refresh:
                            window.show()
                        last_login_message = True
                    if not allow_login:
                        responses.put({"type": "error", "message": "ログインの有効期限が切れました。トレイの「ログイン／一覧を更新...」から再ログインしてください。"})
                except Exception as error:
                    pending_refresh = False
                    message = str(error) if isinstance(error, ClosetError) else "クローゼットと連携できませんでした。専用画面で状態を確認してください。"
                    responses.put({"type": "error", "message": message})

        os.makedirs(profile_path, exist_ok=True)
        webview.start(worker, gui="edgechromium", private_mode=False, storage_path=profile_path)
    except Exception:
        responses.put({"type": "error", "message": "クローゼット画面を起動できません。WebView2 Runtimeと追加ライブラリを確認してください。"})
    finally:
        stopped.set()
        responses.put({"type": "closed"})
