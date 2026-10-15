"""Avatar-title anchored controls, clipped to the game and safe in fullscreen."""

import multiprocessing
import os
import queue
import time
import tkinter as tk

import numpy as np
from PIL import Image
import win32con
import win32gui

from closet_browser import run_closet_browser


def intersect_rect(rect, bounds):
    left, top = max(rect[0], bounds[0]), max(rect[1], bounds[1])
    right, bottom = min(rect[2], bounds[2]), min(rect[3], bounds[3])
    return (left, top, right, bottom) if left < right and top < bottom else None


class TitleDetector:
    def __init__(self, image):
        rgba = np.array(image.convert("RGBA"))
        self.rgb = rgba[:, :, :3]
        self.mask = rgba[:, :, 3] > 0
        colors, counts = np.unique(self.rgb[self.mask], axis=0, return_counts=True)
        self.anchors = []
        for color in colors[np.argsort(counts)]:
            y, x = np.argwhere(np.all(self.rgb == color, axis=2) & self.mask)[0]
            if all(abs(int(y) - ay) + abs(int(x) - ax) >= 5 for ay, ax in self.anchors):
                self.anchors.append((int(y), int(x)))
            if len(self.anchors) == 8:
                break

    def find(self, frame_bgr):
        height, width = self.rgb.shape[:2]
        rows, cols = frame_bgr.shape[0] - height + 1, frame_bgr.shape[1] - width + 1
        if rows <= 0 or cols <= 0 or not self.anchors:
            return None
        frame = frame_bgr[:, :, ::-1]
        y0, x0 = self.anchors[0]
        delta = np.abs(frame[y0:y0 + rows, x0:x0 + cols, 0].astype(np.int16) - int(self.rgb[y0, x0, 0]))
        ys, xs = np.where(delta <= 10)
        for ay, ax in self.anchors:
            if not len(xs):
                return None
            delta = np.abs(frame[ys + ay, xs + ax].astype(np.int16) - self.rgb[ay, ax])
            keep = np.all(delta <= 10, axis=1)
            ys, xs = ys[keep], xs[keep]
        for y, x in zip(ys, xs):
            patch = frame[y:y + height, x:x + width]
            delta = np.abs(patch[self.mask].astype(np.int16) - self.rgb[self.mask])
            if np.mean(delta) <= 3 and np.mean(np.all(delta <= 16, axis=1)) >= 0.98:
                return int(x), int(y), width, height
        return None


class AvatarCloset:
    # Offsets from images/avatar_title.dat to the existing bottom-row controls.
    CONTROLS_OFFSET = (84, 305)

    def __init__(self, app, template_path):
        self.app = app
        with Image.open(template_path) as image:
            self.reference = image.convert("RGBA")
        self.detectors = {}
        self.match = None
        self.match_scale = 1.0
        self.items = []
        self.selected = None
        self.busy = False
        self.process = None
        self.commands = self.responses = None
        self.popup = None
        self.visible = False
        self.maximized = False
        self.game_bounds = None
        self.full_rect = None
        self._geometry = None
        self.feedback = ""
        self.feedback_until = 0

        self.panel = tk.Toplevel(app.root)
        self.panel.withdraw()
        self.panel.overrideredirect(True)
        self.panel.attributes("-topmost", True)
        self.panel.attributes("-toolwindow", True)
        self.panel.configure(bg="black")
        self.panel.wm_attributes("-transparentcolor", "black")
        self.selector, self.save_button = self._create_controls(self.panel)
        self.selector.bind("<Button-1>", lambda _e: self.open_dropdown())
        self.save_button.bind("<Button-1>", lambda _e: self.save(from_click=True))
        # Avoid activating the normal toolbar even during a fullscreen transition.
        self._set_panel_noactivate()

        # In fullscreen there is no separate top-level window to take focus.
        self.embedded = tk.Frame(app.canvas, bg="black", borderwidth=0)
        self.embedded_selector, self.embedded_save = self._create_controls(self.embedded)
        self.app.root.after(100, self.poll)

    @staticmethod
    def _create_controls(parent):
        return tuple(tk.Canvas(parent, highlightthickness=0, bg="black", cursor="hand2") for _ in range(2))

    def _set_panel_noactivate(self):
        # Tk can recreate the native wrapper when it maps an overrideredirect window.
        hwnd = win32gui.GetAncestor(self.panel.winfo_id(), win32con.GA_ROOT)
        style = win32gui.GetWindowLong(hwnd, win32con.GWL_EXSTYLE)
        if not style & win32con.WS_EX_NOACTIVATE:
            win32gui.SetWindowLong(hwnd, win32con.GWL_EXSTYLE, style | win32con.WS_EX_NOACTIVATE)

    def contains_foreground(self):
        foreground = win32gui.GetForegroundWindow()
        for window in (self.panel, self.popup):
            if window is not None and window.winfo_exists():
                if win32gui.GetAncestor(window.winfo_id(), 2) == win32gui.GetAncestor(foreground, 2):
                    return True
        return False

    def hide(self):
        self.visible = False
        self.close_dropdown()
        self.panel.withdraw()
        self.embedded.place_forget()

    def close_dropdown(self):
        if self.popup is not None:
            popup, self.popup = self.popup, None
            popup.destroy()

    def detect(self, frame_bgr):
        for scale in dict.fromkeys((1.0, round(self.app.dpi_scale, 2))):
            if scale not in self.detectors:
                size = tuple(max(1, round(value * scale)) for value in self.reference.size)
                self.detectors[scale] = TitleDetector(self.reference.resize(size, Image.Resampling.NEAREST))
            match = self.detectors[scale].find(frame_bgr)
            if match is not None:
                self.match, self.match_scale = match, scale
                return
        self.match = None
        self.hide()

    def place(self, left, top, right, bottom, maximized=False):
        self.game_bounds = (left, top, right, bottom)
        if self.match is None:
            self.hide()
            return
        x, y, _, _ = self.match
        scale = self.match_scale
        selector_width, button_width, gap, height = (round(n * scale) for n in (116, 70, 4, 37))
        screen_x = left + x + round(self.CONTROLS_OFFSET[0] * scale)
        screen_y = top + y + round(self.CONTROLS_OFFSET[1] * scale)
        self.full_rect = (screen_x, screen_y, screen_x + selector_width + button_width + gap, screen_y + height)
        clipped = intersect_rect(self.full_rect, self.game_bounds)
        if clipped is None:
            self.hide()
            return
        clip_left, clip_top, clip_right, clip_bottom = clipped
        offset_x, offset_y = screen_x - clip_left, screen_y - clip_top
        if self.maximized != maximized:
            self.close_dropdown()
        self.maximized = maximized
        for selector, save in ((self.selector, self.save_button), (self.embedded_selector, self.embedded_save)):
            selector.configure(width=selector_width, height=height)
            save.configure(width=button_width, height=height)
            selector.place(x=offset_x, y=offset_y, width=selector_width, height=height)
            save.place(x=offset_x + selector_width + gap, y=offset_y, width=button_width, height=height)
        geometry = f"{clip_right - clip_left}x{clip_bottom - clip_top}+{clip_left}+{clip_top}"
        if geometry != self._geometry:
            self.close_dropdown()
            self.panel.geometry(geometry)
            self._geometry = geometry
        self.redraw()
        if maximized:
            self.panel.withdraw()
            self.embedded.place(x=clip_left - left, y=clip_top - top,
                                width=clip_right - clip_left, height=clip_bottom - clip_top)
            self.embedded.lift()
        else:
            self.embedded.place_forget()
            if not self.visible or self.panel.state() == "withdrawn":
                self.panel.deiconify()
                self.panel.update_idletasks()
            self._set_panel_noactivate()
        self.visible = True

    def _paint(self, canvas, text, enabled=True):
        width, height = int(canvas.cget("width")), int(canvas.cget("height"))
        canvas.delete("all")
        radius = max(3, round(height * 0.16))
        def outline(inset, fill):
            x, y, w, h = inset, inset, width - inset - 1, height - inset - 1
            canvas.create_polygon(x + radius, y, w - radius, y, w, y + radius,
                                  w, h - radius, w - radius, h, x + radius, h,
                                  x, h - radius, x, y + radius, fill=fill, outline="")
        outline(0, "#192889")
        outline(1, "#ffffff")
        outline(3, "#42518d")
        outline(4, "#19234e" if enabled else "#42465b")
        canvas.create_text(width / 2, height / 2, text=text, fill="white" if enabled else "#c0c3d0",
                           font=("Yu Gothic UI", -max(9, round(height * 0.32)), "bold"), width=width - 12, justify="center")

    def redraw(self):
        entry = next((item for item in self.items if item["seq"] == self.selected), None)
        label = (entry["name"] if entry else "マネキン一覧を取得") + "  ▼"
        feedback = self.feedback if time.monotonic() < self.feedback_until else ""
        for selector, save in ((self.selector, self.save_button), (self.embedded_selector, self.embedded_save)):
            self._paint(selector, "処理中…" if self.busy else label)
            self._paint(save, "保存中…" if self.busy else feedback or "着替え\n保存", bool(entry) and not self.busy)

    def cycle(self, direction):
        if not self.visible or self.busy or not self.items:
            return
        seqs = [item["seq"] for item in self.items]
        index = seqs.index(self.selected) if self.selected in seqs else 0
        self.selected = seqs[(index + direction) % len(seqs)]
        self.feedback = ""
        self.redraw()

    def ensure_browser(self):
        if self.process is not None and self.process.is_alive():
            return
        context = multiprocessing.get_context("spawn")
        self.commands, self.responses = context.Queue(), context.Queue()
        profile = os.path.join(os.environ.get("LOCALAPPDATA", os.path.expanduser("~")), "ChocoTimer", "ClosetProfile")
        self.process = context.Process(target=run_closet_browser, args=(self.commands, self.responses, profile), daemon=True)
        self.process.start()

    def refresh(self):
        if self.busy:
            return
        self.ensure_browser()
        self.busy = True
        self.commands.put({"action": "refresh"})
        self.redraw()

    def show_browser(self):
        self.ensure_browser()
        self.commands.put({"action": "show"})

    def open_dropdown(self):
        if not self.visible or self.busy or self.app.is_target_maximized():
            return
        if not self.items:
            self.refresh()
            return
        self.close_dropdown()
        popup = self.popup = tk.Toplevel(self.panel)
        popup.withdraw()
        popup.overrideredirect(True)
        popup.attributes("-topmost", True)
        popup.configure(bg="#ffffff", padx=2, pady=2)
        listbox = tk.Listbox(popup, width=28, height=min(10, len(self.items) + 2),
                             bg="#19234e", fg="white", selectbackground="#4056a1",
                             selectforeground="white", font=("Yu Gothic UI", 10),
                             activestyle="none", borderwidth=0, highlightthickness=0)
        scrollbar = tk.Scrollbar(popup, command=listbox.yview)
        listbox.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side="right", fill="y")
        listbox.pack(side="left", fill="both", expand=True)
        for item in self.items:
            listbox.insert("end", item["name"])
        listbox.insert("end", "一覧を更新…", "クローゼットを開く…")
        def choose(_event=None):
            selection = listbox.curselection()
            if not selection:
                return
            index = selection[0]
            self.close_dropdown()
            if index < len(self.items):
                self.selected = self.items[index]["seq"]
                self.redraw()
            elif index == len(self.items):
                self.refresh()
            else:
                self.show_browser()
        listbox.bind("<ButtonRelease-1>", choose)
        listbox.bind("<Return>", choose)
        popup.bind("<Escape>", lambda _e: self.close_dropdown())
        popup.update_idletasks()
        if self.popup is not popup or not popup.winfo_exists():
            return
        left, top, right, bottom = self.game_bounds
        width, height = min(popup.winfo_reqwidth(), right - left), min(popup.winfo_reqheight(), bottom - top)
        x = max(left, min(self.full_rect[0], right - width))
        y = self.full_rect[3]
        if y + height > bottom:
            y = max(top, self.full_rect[1] - height)
        popup.geometry(f"{width}x{height}+{x}+{y}")
        def close_if_unfocused():
            if self.popup is popup and popup.winfo_exists():
                focus = popup.focus_get()
                if focus is None or focus.winfo_toplevel() is not popup:
                    self.close_dropdown()
        popup.bind("<FocusOut>", lambda _e: self.app.root.after(100, close_if_unfocused))
        popup.deiconify()
        listbox.focus_set()

    def save(self, from_click=False):
        if not self.visible or self.busy or self.selected is None:
            return
        if from_click and self.app.is_target_maximized():
            return
        self.ensure_browser()
        self.feedback = ""
        self.busy = True
        self.redraw()
        self.commands.put({"action": "save", "seq": self.selected})

    def poll(self):
        if self.responses is not None:
            try:
                while True:
                    response = self.responses.get_nowait()
                    kind = response["type"]
                    if kind == "items":
                        self.items = response["items"]
                        self.busy = False
                        if self.selected not in {item["seq"] for item in self.items}:
                            self.selected = self.items[0]["seq"] if self.items else None
                        if not self.items:
                            self.feedback, self.feedback_until = "マネキン\nなし", time.monotonic() + 4
                    elif kind in {"saved", "error"}:
                        self.busy = False
                        self.feedback = "保存\n完了" if kind == "saved" else "処理\n失敗"
                        self.feedback_until = time.monotonic() + 4
                        self.app.root.after(4000, self.redraw)
                    elif kind in {"login", "closed"}:
                        self.busy = False
                    self.redraw()
            except queue.Empty:
                pass
        self.app.root.after(100, self.poll)

    def close(self):
        self.hide()
        if self.process is not None and self.process.is_alive():
            self.commands.put({"action": "close"})
            self.process.join(timeout=1)
            if self.process.is_alive():
                self.process.terminate()
                self.process.join(timeout=1)
