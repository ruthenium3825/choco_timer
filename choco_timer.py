import ctypes
from ctypes import wintypes
import json
import math
import os
import queue
import sys
import threading
import time

import cv2
import keyboard
import mouse
import numpy as np
import pygame
import pystray
import win32api
import win32con
import win32event
import win32gui
import win32ui
import winerror
from PIL import Image, ImageDraw, ImageFilter, ImageTk
from pystray import MenuItem as item
from tkinter import messagebox, ttk
import tkinter as tk


CONFIG_FILE = "config.json"

AUTO_QUIT_AFTER_SECONDS = 300
PROCESS_QUEUE_INTERVAL_MS = 100
OVERLAY_UPDATE_INTERVAL_MS = 100
ICON_CHECK_INTERVAL_MS = 500
TIMER_TICK_INTERVAL_MS = 100
PREVIEW_DURATION_MS = 2000

DEFAULT_UI_ASSETS = [
    "clock",
    "colon",
    "counter",
    "slash",
    "keyboard",
    "left",
    "right",
    "feather",
    "cursor",
]

DEFAULT_SOUND_NAMES = [
    "timer_start",
    "reset",
    "cursor",
    "timer_select",
    "counter",
    "enter",
    "cancel",
]

HOTKEY_ACTION_LABELS = [
    ("add_timer", "タイマースタート"),
    ("reset_timer", "タイマーリセット"),
    ("reset_all_timers", "全タイマーリセット"),
    ("move_cursor", "リセットカーソル移動"),
    None,
    ("prev_preset", "時間設定（戻る）"),
    ("next_preset", "時間設定（進む）"),
    None,
    ("inc_counter1", "カウンター1 +1"),
    ("dec_counter1", "カウンター1 -1"),
    ("reset_counter1", "カウンター1 リセット"),
    None,
    ("inc_counter2", "カウンター2 +1"),
    ("dec_counter2", "カウンター2 -1"),
    ("reset_counter2", "カウンター2 リセット"),
]

HOTKEY_LABEL_MAP = {
    key_id: label
    for key_id, label in (entry for entry in HOTKEY_ACTION_LABELS if entry is not None)
}

DIALOG_BG = "#15171c"
DIALOG_PANEL_BG = "#1f2229"
DIALOG_INPUT_BG = "#101217"
DIALOG_FG = "#f3f4f6"
DIALOG_MUTED_FG = "#a6adbb"
DIALOG_ACCENT = "#4f8cff"
DIALOG_ACCENT_HOVER = "#6aa0ff"
DIALOG_DANGER = "#ff6b6b"
DIALOG_BORDER = "#303440"
DIALOG_SLIDER_TRACK = "#353b48"
DIALOG_SLIDER_TRACK_INNER = "#242934"
DIALOG_SLIDER_FILL = DIALOG_ACCENT
DIALOG_SLIDER_FILL_HIGHLIGHT = "#83b4ff"
DIALOG_SLIDER_KNOB = "#f4f8ff"
DIALOG_SLIDER_KNOB_OUTLINE = "#a9c9ff"
DIALOG_SLIDER_KNOB_SHADOW = "#0a0c10"
DIALOG_FONT = ("Yu Gothic UI", 10)
DIALOG_TITLE_FONT = ("Yu Gothic UI", 14, "bold")
DIALOG_SMALL_FONT = ("Yu Gothic UI", 9)
DIALOG_BUTTON_FONT = ("Yu Gothic UI", 10, "bold")
DIALOG_BUTTON_WIDTH = 124
DIALOG_BUTTON_HEIGHT = 38
DIALOG_BUTTON_GAP = 8


def resource_path(relative_path, folder="images"):
    """Resolve resource path for source execution and PyInstaller builds."""
    try:
        base_path = sys._MEIPASS
    except Exception:
        base_path = os.path.abspath(".")

    path = os.path.join(base_path, folder, relative_path)
    if not os.path.exists(path):
        path = os.path.join(base_path, relative_path)
    return path


def enable_dpi_awareness():
    """Make Win32/Tk coordinates use the same physical-pixel basis."""
    if sys.platform != "win32":
        return

    try:
        # Windows 10 or newer: Per-monitor DPI aware v2.
        pointer_bits = ctypes.sizeof(ctypes.c_void_p) * 8
        awareness_context = ctypes.c_void_p(-4 & ((1 << pointer_bits) - 1))
        if ctypes.windll.user32.SetProcessDpiAwarenessContext(awareness_context):
            return
    except Exception:
        pass

    try:
        # Windows 8.1 or newer: PROCESS_PER_MONITOR_DPI_AWARE.
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
        return
    except Exception:
        pass

    try:
        # Windows 7 compatible fallback.
        ctypes.windll.user32.SetProcessDPIAware()
    except Exception:
        pass


class OverlayApp:
    def __init__(self, target_class, target_title, icon_config, default_hotkeys):
        enable_dpi_awareness()

        self._prevent_multiple_instances()
        self._init_audio()

        self.target_class = target_class
        self.target_title = target_title
        self.icon_config = icon_config
        self.icon_filenames = list(icon_config.keys())
        self.icon_paths = [resource_path(filename, "images") for filename in self.icon_filenames]
        self.valid_hotkey_ids = set(default_hotkeys.keys())

        self.load_config(default_hotkeys)
        self.dpi_scale = 1.0
        self.request_queue = queue.Queue()

        self._init_static_config()
        self._init_state()
        self._load_sounds()
        self.apply_volume_to_mixer()

        self._create_root_and_overlay()
        self._load_assets_and_templates()
        self.setup_hooks()

        self.tray_icon = None
        self.setup_tray()

        self.update_overlay()
        self.check_icon_loop()
        self.process_queue()

    # ------------------------------------------------------------------
    # Initialization
    # ------------------------------------------------------------------

    def _prevent_multiple_instances(self):
        self.mutex_name = "Global\\ChocottoTimer_Mutex"
        self.mutex = win32event.CreateMutex(None, False, self.mutex_name)
        if win32api.GetLastError() != winerror.ERROR_ALREADY_EXISTS:
            return

        root_temp = tk.Tk()
        root_temp.withdraw()
        messagebox.showwarning("多重起動", "アプリは既に起動しています。")
        root_temp.destroy()
        sys.exit(0)

    def _init_audio(self):
        pygame.mixer.pre_init(44100, -16, 2, 512)
        pygame.mixer.init()
        pygame.mixer.set_num_channels(16)
        self.sound_objects = {}

    def _init_static_config(self):
        self.max_timers = 8
        self.base_timer_spacing = 12
        self.origin_x = 8
        self.counter_offset_x = 12
        self.timer_offset_x = 13
        self.cursor_offset_x = 0

        # BitBlt で取得できる画像は、テスト結果に合わせて100%基準座標で扱う。
        self.icon_search_x = 20
        self.icon_search_y = 101
        self.icon_search_w = 200
        self.icon_search_h = 10
        self.icon_search_margin_x = 0
        self.icon_search_margin_y = 0
        self.icon_check_interval_ms = ICON_CHECK_INTERVAL_MS
        self.threshold = 0.90

    def _init_state(self):
        self.target_time = 0
        self.feather_timer = 0
        self.is_counting = False
        self.timers = []
        self.counter1 = 0
        self.counter2 = 0
        self.target_hwnd = None
        self.tick_id = None
        self.current_icon_index = -1
        self.is_typing_mode = False
        self.not_found_start_time = None
        self.selected_cursor_index = 0
        self.selected_preset_index = 0
        self.preview_timer_id = None

    def _load_sounds(self):
        for name in DEFAULT_SOUND_NAMES:
            path = resource_path(f"{name}.dat", "sounds")
            if not os.path.exists(path):
                continue
            try:
                self.sound_objects[name] = pygame.mixer.Sound(path)
            except Exception as e:
                print(f"Failed to load {name}: {e}")

    def _create_root_and_overlay(self):
        self.root = tk.Tk()
        self.root.withdraw()

        self.overlay = tk.Toplevel(self.root)
        self.overlay.attributes("-topmost", True)
        self.overlay.overrideredirect(True)
        self.overlay.config(bg="black")
        self.overlay.wm_attributes("-transparentcolor", "black")
        self.overlay.update()

        hwnd = win32gui.GetParent(self.overlay.winfo_id())
        ex_style = win32gui.GetWindowLong(hwnd, win32con.GWL_EXSTYLE)
        win32gui.SetWindowLong(
            hwnd,
            win32con.GWL_EXSTYLE,
            ex_style | win32con.WS_EX_LAYERED | win32con.WS_EX_TRANSPARENT,
        )

        self.canvas = tk.Canvas(
            self.overlay,
            width=600,
            height=1000,
            bg="black",
            highlightthickness=0,
        )
        self.canvas.pack()

    def _load_assets_and_templates(self):
        self.raw_images = {}
        self.images = {}
        self.load_assets()

        self.templates = []
        self.reload_templates()

    # ------------------------------------------------------------------
    # Config
    # ------------------------------------------------------------------

    def load_config(self, default_hotkeys):
        self.scale = 1.0
        self.origin_y = 114
        self.presets = [300, 600, 1800, 3600]
        self.counter_enabled = False
        self.sound_enabled = True
        self.volume_level = 35

        self.hotkey_config = default_hotkeys
        self.auto_start_enabled = True
        self.hotkey_enabled = True

        if not os.path.exists(CONFIG_FILE):
            return

        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                saved_data = json.load(f)
        except Exception:
            return

        loaded_hotkeys = saved_data.get("hotkeys", {})
        loaded_hotkeys = self._sanitize_hotkey_config(loaded_hotkeys)
        self.hotkey_config = {**default_hotkeys, **loaded_hotkeys}
        self.auto_start_enabled = saved_data.get("auto_start", True)
        self.hotkey_enabled = saved_data.get("hotkey_enabled", True)
        self.scale = saved_data.get("scale", 1.0)
        self.origin_y = saved_data.get("origin_y", 114)
        self.presets = saved_data.get("presets", [300, 600, 1800, 3600])
        self.counter_enabled = saved_data.get("counter_enabled", False)
        self.sound_enabled = saved_data.get("sound_enabled", True)
        self.volume_level = saved_data.get("volume_level", 35)

    def _sanitize_hotkey_config(self, hotkey_config):
        if not isinstance(hotkey_config, dict):
            return {}

        sanitized = {}
        for key_id, hotkey in hotkey_config.items():
            if not isinstance(key_id, str):
                continue
            if key_id not in getattr(self, "valid_hotkey_ids", set()):
                continue
            if hotkey is None:
                sanitized[key_id] = ""
            else:
                sanitized[key_id] = str(hotkey)
        return sanitized

    def save_config(self):
        self.hotkey_config = self._sanitize_hotkey_config(self.hotkey_config)
        data = {
            "hotkeys": self.hotkey_config,
            "auto_start": self.auto_start_enabled,
            "hotkey_enabled": self.hotkey_enabled,
            "scale": self.scale,
            "origin_y": self.origin_y,
            "presets": self.presets,
            "counter_enabled": self.counter_enabled,
            "sound_enabled": self.sound_enabled,
            "volume_level": self.volume_level,
        }

        try:
            with open(CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=4, ensure_ascii=False)
        except Exception as e:
            print(f"Save Error: {e}")

    # ------------------------------------------------------------------
    # DPI and scaling
    # ------------------------------------------------------------------

    def get_effective_scale(self):
        return self.scale * getattr(self, "dpi_scale", 1.0)

    def _valid_dpi_scale(self, value):
        try:
            value = float(value)
            if 0.5 <= value <= 4.0:
                return value
        except Exception:
            pass
        return None

    def _round_half_up(self, value):
        return int(math.floor(float(value) + 0.5))

    def get_window_dpi_scale(self):
        if sys.platform != "win32" or not self.target_hwnd:
            return 1.0

        try:
            dpi = ctypes.windll.user32.GetDpiForWindow(self.target_hwnd)
            scale = self._valid_dpi_scale(dpi / 96.0)
            if scale:
                return scale
        except Exception:
            pass
        return 1.0

    def get_monitor_dpi_scale(self):
        if sys.platform != "win32":
            return 1.0

        try:
            hwnd = self.target_hwnd or self.overlay.winfo_id()
            monitor = ctypes.windll.user32.MonitorFromWindow(hwnd, 2)
            dpi_x = ctypes.c_uint(0)
            dpi_y = ctypes.c_uint(0)
            result = ctypes.windll.shcore.GetDpiForMonitor(
                monitor,
                0,
                ctypes.byref(dpi_x),
                ctypes.byref(dpi_y),
            )
            if result == 0 and dpi_x.value:
                scale = self._valid_dpi_scale(dpi_x.value / 96.0)
                if scale:
                    return scale
        except Exception:
            pass

        try:
            hdc = ctypes.windll.user32.GetDC(0)
            dpi = ctypes.windll.gdi32.GetDeviceCaps(hdc, 88)
            ctypes.windll.user32.ReleaseDC(0, hdc)
            scale = self._valid_dpi_scale(dpi / 96.0)
            if scale:
                return scale
        except Exception:
            pass
        return 1.0

    def get_tk_dpi_scale(self):
        try:
            scale = self._valid_dpi_scale(self.root.winfo_fpixels("1i") / 96.0)
            if scale:
                return scale
        except Exception:
            pass
        return 1.0

    def get_dialog_dpi_scale(self):
        """設定ウィンドウ用の現在DPI倍率を返す。

        アプリ起動後にWindowsの拡大率を変更した場合、Tk側のDPI値は
        古い値を返すことがあるため、操作中のモニターDPIを優先する。
        self.scale はオーバーレイ表示サイズ用なので使わない。
        """
        if sys.platform == "win32":
            try:
                x, y = win32gui.GetCursorPos()
                monitor = ctypes.windll.user32.MonitorFromPoint(wintypes.POINT(x, y), 2)
                dpi_x = ctypes.c_uint(0)
                dpi_y = ctypes.c_uint(0)
                result = ctypes.windll.shcore.GetDpiForMonitor(
                    monitor,
                    0,
                    ctypes.byref(dpi_x),
                    ctypes.byref(dpi_y),
                )
                if result == 0 and dpi_x.value:
                    scale = self._valid_dpi_scale(dpi_x.value / 96.0)
                    if scale:
                        return round(float(scale), 2)
            except Exception:
                pass

            try:
                hwnd = self.target_hwnd or self.root.winfo_id()
                dpi = ctypes.windll.user32.GetDpiForWindow(hwnd)
                scale = self._valid_dpi_scale(dpi / 96.0)
                if scale:
                    return round(float(scale), 2)
            except Exception:
                pass

        scale = self.get_tk_dpi_scale()
        if self._valid_dpi_scale(scale):
            return round(float(scale), 2)
        return 1.0


    def dialog_px(self, value):
        """設定ウィンドウ用のpx値を、ダイアログ生成時のDPI倍率で変換する。"""
        scale = getattr(self, "_dialog_dpi_scale", None)
        if not scale:
            scale = self.get_dialog_dpi_scale()
        return self._round_half_up(float(value) * float(scale))

    def get_target_dpi_scale(self):
        monitor_scale = self.get_monitor_dpi_scale()
        if self._valid_dpi_scale(monitor_scale):
            return round(monitor_scale, 2)

        window_scale = self.get_window_dpi_scale()
        if self._valid_dpi_scale(window_scale):
            return round(window_scale, 2)

        tk_scale = self.get_tk_dpi_scale()
        if self._valid_dpi_scale(tk_scale):
            return round(tk_scale, 2)

        return 1.0

    def update_dpi_scale_for_target(self):
        new_scale = round(self.get_target_dpi_scale(), 2)
        if abs(new_scale - getattr(self, "dpi_scale", 1.0)) <= 0.01:
            return

        self.dpi_scale = new_scale
        self.apply_scale()

    def _resize_ui_image_clean(self, pil_img, new_size):
        effective_scale = self.get_effective_scale()
        is_integer_scale = abs(effective_scale - round(effective_scale)) < 0.01
        if is_integer_scale:
            return pil_img.resize(new_size, Image.Resampling.NEAREST)

        resized = pil_img.convert("RGB").resize(new_size, Image.Resampling.BICUBIC)

        # Tk の transparentcolor は完全な黒だけ透明扱いするため、補間でにじんだ
        # 黒背景をもう一度黒に戻す。
        arr = np.array(resized)
        near_black = (
            (arr[:, :, 0] <= 24)
            & (arr[:, :, 1] <= 24)
            & (arr[:, :, 2] <= 24)
        )
        arr[near_black] = [0, 0, 0]
        return Image.fromarray(arr, "RGB")

    def apply_scale(self):
        effective_scale = self.get_effective_scale()
        for name, pil_img in self.raw_images.items():
            w, h = pil_img.size
            new_size = (
                max(1, self._round_half_up(w * effective_scale)),
                max(1, self._round_half_up(h * effective_scale)),
            )
            resized = self._resize_ui_image_clean(pil_img, new_size)
            self.images[name] = ImageTk.PhotoImage(resized)
        self.draw_timer()

    # ------------------------------------------------------------------
    # Assets and sound
    # ------------------------------------------------------------------

    def load_assets(self):
        try:
            for name in DEFAULT_UI_ASSETS:
                self.raw_images[name] = Image.open(resource_path(f"{name}.dat", "images"))
            for digit in range(10):
                self.raw_images[str(digit)] = Image.open(resource_path(f"{digit}.dat", "images"))
            self.apply_scale()
        except Exception:
            pass

    def reload_templates(self):
        self.templates = []
        for path in self.icon_paths:
            if not os.path.exists(path):
                continue
            try:
                with Image.open(path) as img:
                    rgb = np.array(img.convert("RGB"))
                    self.templates.append(cv2.cvtColor(rgb, cv2.COLOR_RGB2BGR))
            except Exception as e:
                print(f"Template load error: {path}: {e}")

    def apply_volume_to_mixer(self):
        actual_vol = max(0.0, min(1.0, self.volume_level / 100.0))
        for sound in self.sound_objects.values():
            sound.set_volume(actual_vol)

    def play_sound(self, sound_type="timer_start"):
        if not self.sound_enabled:
            return

        sound = self.sound_objects.get(sound_type)
        if not sound:
            return

        try:
            channel = pygame.mixer.find_channel(True)
            if channel:
                channel.play(sound)
        except Exception as e:
            print(f"Sound play error: {e}")

    # ------------------------------------------------------------------
    # Queue and dialogs
    # ------------------------------------------------------------------

    def _enqueue(self, task_type, **kwargs):
        task = {"type": task_type}
        task.update(kwargs)
        self.request_queue.put(task)

    def process_queue(self):
        try:
            while True:
                task = self.request_queue.get_nowait()
                try:
                    self._dispatch_queue_task(task)
                finally:
                    self.request_queue.task_done()
        except queue.Empty:
            pass
        self.root.after(PROCESS_QUEUE_INTERVAL_MS, self.process_queue)

    def _dispatch_queue_task(self, task):
        task_type = task.get("type")
        if task_type == "change_hotkey":
            self._execute_change_hotkey(task["key_id"])
        elif task_type == "edit_preset":
            self._execute_edit_preset(task["index"])
        elif task_type == "add_preset":
            self._execute_add_preset()
        elif task_type == "show_volume_dialog":
            self._execute_show_volume_dialog()

    def _hotkey_action_label(self, key_id):
        return HOTKEY_LABEL_MAP.get(key_id, key_id)

    def _prepare_dialog_owner(self):
        """
        自作ダイアログを確実に前面表示するため、非表示の root を
        一時的に透明な1pxウィンドウとして復帰させる。

        Windows/Tk では、withdraw中のrootを親にした transient な
        Toplevel が表に出てこないことがあるため、ダイアログ表示前に
        親だけ復帰させる。
        """
        # ダイアログを開く瞬間のDPIを固定して使う。
        # 起動後にWindowsの拡大率を変更した直後に tk scaling を変更すると、
        # Tk/Windows側の再計算と競合してウィンドウサイズがガクガク変化する
        # ことがあるため、tk scaling は触らず、dialog_px() で明示的に拡大する。
        self._dialog_dpi_scale = self.get_dialog_dpi_scale()

        try:
            self.root.geometry("1x1+0+0")
            self.root.deiconify()
            try:
                self.root.attributes("-alpha", 0.0)
            except Exception:
                pass
            self.root.update_idletasks()
        except Exception as e:
            print(f"Dialog owner prepare error: {e}")

    def _restore_dialog_owner(self):
        try:
            try:
                self.root.attributes("-alpha", 1.0)
            except Exception:
                pass
            self.root.withdraw()
        except Exception as e:
            print(f"Dialog owner restore error: {e}")

    def _bring_dialog_to_front(self, dialog):
        try:
            dialog.attributes("-topmost", True)
            dialog.lift()
            dialog.focus_force()
            # 生成直後に一度だけでは前面に来ない環境があるため、
            # Tkの描画後にも再度持ち上げる。
            dialog.after(50, lambda: (dialog.lift(), dialog.focus_force()))
        except Exception:
            pass

    def _center_dialog(self, dialog, width, height):
        dialog.update_idletasks()
        sw = dialog.winfo_screenwidth()
        sh = dialog.winfo_screenheight()
        x = int((sw - width) / 2)
        y = int((sh - height) / 2)
        dialog.geometry(f"{width}x{height}+{x}+{y}")

    def _lock_dialog_size(self, dialog, width, height):
        """移動後にだけサイズを戻す、DPI変更後向けの軽いサイズロック。

        <Configure> のたびに即 geometry() をかけると、Windows/Tk のDPI再計算と
        競合してガクガクする。逆に何もしないと、125%以上で移動した時に少しずつ
        縮むことがある。そこで Configure が落ち着いてから1回だけサイズを戻す。
        """
        lock_state = {
            "busy": False,
            "after_id": None,
        }

        def restore_size():
            lock_state["after_id"] = None
            if lock_state["busy"]:
                return
            try:
                if not dialog.winfo_exists():
                    return
            except Exception:
                return

            try:
                current_width = dialog.winfo_width()
                current_height = dialog.winfo_height()
                if abs(current_width - width) <= 1 and abs(current_height - height) <= 1:
                    return

                x = dialog.winfo_x()
                y = dialog.winfo_y()
                lock_state["busy"] = True
                dialog.geometry(f"{width}x{height}+{x}+{y}")
            finally:
                try:
                    dialog.after_idle(lambda: lock_state.update({"busy": False}))
                except Exception:
                    lock_state["busy"] = False

        def on_configure(event):
            if event.widget is not dialog:
                return
            if lock_state["busy"]:
                return

            if abs(event.width - width) <= 1 and abs(event.height - height) <= 1:
                return

            # 移動中・DPI再計算中はConfigureが連続するので、最後のイベントから
            # 少し待って1回だけ補正する。これでガクガクを避けつつ縮みを戻す。
            if lock_state["after_id"] is not None:
                try:
                    dialog.after_cancel(lock_state["after_id"])
                except Exception:
                    pass
            lock_state["after_id"] = dialog.after(180, restore_size)

        dialog.bind("<Configure>", on_configure, add="+")
        
    def _configure_dialog_base(self, dialog, title, width, height):
        dialog.title(title)
        dialog.configure(bg=DIALOG_BG)
        dialog.resizable(False, False)
        dialog.attributes("-topmost", True)

        fixed_width = self.dialog_px(width)
        fixed_height = self.dialog_px(height)

        dialog._fixed_width = fixed_width
        dialog._fixed_height = fixed_height

        # minsize/maxsize はDPI変更後にTk/Windowsと競合しやすいため使わない。
        # 代わりに、移動やDPI再計算が落ち着いた後だけサイズを戻す。
        self._center_dialog(dialog, fixed_width, fixed_height)
        dialog.update_idletasks()
        self._lock_dialog_size(dialog, fixed_width, fixed_height)
        self._bring_dialog_to_front(dialog)
        return dialog

    def _make_dialog_panel(self, dialog):
        outer = tk.Frame(
            dialog,
            bg=DIALOG_BG,
            padx=self.dialog_px(16),
            pady=self.dialog_px(16),
        )
        outer.pack(fill="both", expand=True)

        panel = tk.Frame(
            outer,
            bg=DIALOG_PANEL_BG,
            highlightbackground=DIALOG_BORDER,
            highlightthickness=1,
            padx=self.dialog_px(18),
            pady=self.dialog_px(16),
        )
        panel.pack(fill="both", expand=True)
        return panel

    def _dialog_label(
        self,
        parent,
        text,
        *,
        font=None,
        fg=None,
        pady=(0, 0),
        anchor="w",
        wraplength=360,
    ):
        label = tk.Label(
            parent,
            text=text,
            bg=DIALOG_PANEL_BG,
            fg=fg or DIALOG_FG,
            font=font or DIALOG_FONT,
            anchor=anchor,
            justify="left",
            wraplength=wraplength,
        )
        label.pack(fill="x", pady=pady)
        return label

    def _dialog_button(self, parent, text, command, *, primary=False, danger=False):
        """Create a fixed-pixel-size dialog button.

        The command is intentionally fired on mouse release, not on press.
        This mimics a normal HTML/button widget:
        press on the button -> show pressed state -> release on the button -> run.
        Dragging out of the button before release cancels the action.
        """
        if primary:
            bg = DIALOG_ACCENT
            active_bg = DIALOG_ACCENT_HOVER
            pressed_bg = "#486ee8"
            fg = "white"
        elif danger:
            bg = "#2a1d22"
            active_bg = "#3a242b"
            pressed_bg = "#462731"
            fg = DIALOG_DANGER
        else:
            bg = "#2a2e38"
            active_bg = "#363b48"
            pressed_bg = "#20242d"
            fg = DIALOG_FG

        button = tk.Frame(
            parent,
            width=self.dialog_px(DIALOG_BUTTON_WIDTH),
            height=self.dialog_px(DIALOG_BUTTON_HEIGHT),
            bg=bg,
            cursor="hand2",
            highlightthickness=0,
            bd=0,
        )
        button.pack_propagate(False)

        label = tk.Label(
            button,
            text=text,
            bg=bg,
            fg=fg,
            activebackground=active_bg,
            activeforeground=fg,
            font=DIALOG_BUTTON_FONT,
            anchor="center",
            cursor="hand2",
        )
        label.pack(fill="both", expand=True)

        state = {"pressed": False, "inside": False}

        def set_bg(color):
            button.config(bg=color)
            label.config(bg=color, activebackground=color)

        def is_pointer_inside_button():
            widget = button.winfo_containing(button.winfo_pointerx(), button.winfo_pointery())
            while widget is not None:
                if widget is button:
                    return True
                widget = getattr(widget, "master", None)
            return False

        def refresh_visual():
            inside = is_pointer_inside_button()
            state["inside"] = inside
            if state["pressed"] and inside:
                set_bg(pressed_bg)
            elif inside:
                set_bg(active_bg)
            else:
                set_bg(bg)

        def on_enter(_event):
            state["inside"] = True
            refresh_visual()

        def on_leave(_event):
            state["inside"] = False
            refresh_visual()

        def on_press(_event):
            state["pressed"] = True
            button.focus_set()
            refresh_visual()
            return "break"

        def on_release(_event):
            if not state["pressed"]:
                return "break"

            should_fire = is_pointer_inside_button()
            state["pressed"] = False
            refresh_visual()

            if should_fire:
                command()
            return "break"

        for widget in (button, label):
            widget.bind("<Enter>", on_enter)
            widget.bind("<Leave>", on_leave)
            widget.bind("<ButtonPress-1>", on_press)
            widget.bind("<ButtonRelease-1>", on_release)

        return button

    def _pack_dialog_button(self, parent, button, *, side="right", padx=None):
        if padx is None:
            gap = self.dialog_px(DIALOG_BUTTON_GAP)
            padx = (gap, 0) if side == "right" else (0, gap)
        else:
            padx = tuple(self.dialog_px(v) for v in padx)

        button.pack(side=side, padx=padx)
        return button

    def _show_notice_dialog(self, title, heading, message, *, danger=False):
        self._prepare_dialog_owner()
        dialog = tk.Toplevel(self.root)
        width, height = 390, 210
        self._configure_dialog_base(dialog, title, width, height)
        panel = self._make_dialog_panel(dialog)

        self._dialog_label(panel, heading, font=DIALOG_TITLE_FONT, fg=DIALOG_DANGER if danger else DIALOG_FG, pady=(0, 10), wraplength=330)
        self._dialog_label(panel, message, fg=DIALOG_MUTED_FG, pady=(0, 18), wraplength=330)

        buttons = tk.Frame(panel, bg=DIALOG_PANEL_BG)
        buttons.pack(fill="x", side="bottom")
        self._pack_dialog_button(
            buttons,
            self._dialog_button(buttons, "OK", dialog.destroy, primary=not danger, danger=danger),
            side="right",
            padx=(0, 0),
        )

        dialog.bind("<Return>", lambda _event: dialog.destroy())
        dialog.bind("<Escape>", lambda _event: dialog.destroy())
        dialog.grab_set()
        dialog.focus_force()
        self.root.wait_window(dialog)
        self._restore_dialog_owner()

    def _show_text_input_dialog(
        self,
        *,
        title,
        heading,
        description,
        initial_value="",
        confirm_text="保存",
        allow_blank=True,
        width=460,
        height=260,
    ):
        result = {"value": None}
        self._prepare_dialog_owner()
        dialog = tk.Toplevel(self.root)
        self._configure_dialog_base(dialog, title, width, height)
        panel = self._make_dialog_panel(dialog)

        self._dialog_label(panel, heading, font=DIALOG_TITLE_FONT, pady=(0, 8), wraplength=400)
        self._dialog_label(panel, description, fg=DIALOG_MUTED_FG, pady=(0, 14), wraplength=400)

        entry_var = tk.StringVar(value=initial_value)
        entry = tk.Entry(
            panel,
            textvariable=entry_var,
            bg=DIALOG_INPUT_BG,
            fg=DIALOG_FG,
            insertbackground=DIALOG_FG,
            relief="flat",
            highlightthickness=1,
            highlightbackground=DIALOG_BORDER,
            highlightcolor=DIALOG_ACCENT,
            font=("Consolas", 12),
        )
        entry.pack(fill="x", ipady=8, pady=(0, 8))

        error_label = tk.Label(
            panel,
            text="",
            bg=DIALOG_PANEL_BG,
            fg=DIALOG_DANGER,
            font=DIALOG_SMALL_FONT,
            anchor="w",
        )
        error_label.pack(fill="x", pady=(0, 8))

        def confirm():
            value = entry_var.get()
            if not allow_blank and value.strip() == "":
                error_label.config(text="値を入力してください。")
                return
            result["value"] = value
            dialog.destroy()

        def cancel():
            dialog.destroy()

        buttons = tk.Frame(panel, bg=DIALOG_PANEL_BG)
        buttons.pack(fill="x", side="bottom", pady=(8, 0))
        self._pack_dialog_button(
            buttons,
            self._dialog_button(buttons, "キャンセル", cancel),
            side="right",
            padx=(DIALOG_BUTTON_GAP, 0),
        )
        self._pack_dialog_button(
            buttons,
            self._dialog_button(buttons, confirm_text, confirm, primary=True),
            side="right",
            padx=(0, 0),
        )

        dialog.protocol("WM_DELETE_WINDOW", cancel)
        dialog.bind("<Return>", lambda _event: confirm())
        dialog.bind("<Escape>", lambda _event: cancel())
        dialog.grab_set()
        entry.focus_set()
        entry.selection_range(0, tk.END)
        self.root.wait_window(dialog)
        self._restore_dialog_owner()
        return result["value"]

    def _canvas_display_size(self, canvas):
        """Return a stable canvas size even before Tk has completed layout."""
        try:
            configured_width = int(float(canvas.cget("width")))
            configured_height = int(float(canvas.cget("height")))
        except Exception:
            configured_width, configured_height = 360, 52

        actual_width = int(canvas.winfo_width())
        actual_height = int(canvas.winfo_height())

        # Just after creation Tk often reports 1x1.  Use the configured size in that case.
        width = configured_width if actual_width <= 2 else actual_width
        height = configured_height if actual_height <= 2 else actual_height
        return max(80, width), max(32, height)

    def _draw_rounded_slider_image(self, width, height, value):
        """Draw a high-quality antialiased volume slider image."""
        value = max(0.0, min(100.0, float(value)))
        scale = 6
        w = max(80, int(width))
        h = max(32, int(height))
        img = Image.new("RGB", (w * scale, h * scale), DIALOG_PANEL_BG)
        draw = ImageDraw.Draw(img)

        def sc_rect(rect):
            x0, y0, x1, y1 = rect
            if x1 < x0:
                x0, x1 = x1, x0
            if y1 < y0:
                y0, y1 = y1, y0
            return tuple(int(round(v * scale)) for v in (x0, y0, x1, y1))

        left = 22
        right = max(left + 20, w - 22)
        center_y = h / 2
        track_h = 12
        fill_end = left + (right - left) * (value / 100.0)
        radius = track_h / 2

        # Track shadow / outer track.
        shadow_rect = (left, center_y - track_h / 2 + 2, right, center_y + track_h / 2 + 2)
        draw.rounded_rectangle(sc_rect(shadow_rect), radius=int(radius * scale), fill="#11151d")

        track_rect = (left, center_y - track_h / 2, right, center_y + track_h / 2)
        draw.rounded_rectangle(sc_rect(track_rect), radius=int(radius * scale), fill=DIALOG_SLIDER_TRACK)

        inner_rect = (left + 1.5, center_y - track_h / 2 + 1.5, right - 1.5, center_y + track_h / 2 - 1.5)
        draw.rounded_rectangle(sc_rect(inner_rect), radius=int((radius - 1.5) * scale), fill=DIALOG_SLIDER_TRACK_INNER)

        # Fill, drawn only when it has visible width.
        if fill_end > left + 1:
            fill_rect = (left, center_y - track_h / 2, fill_end, center_y + track_h / 2)
            draw.rounded_rectangle(sc_rect(fill_rect), radius=int(radius * scale), fill=DIALOG_SLIDER_FILL)
            highlight_rect = (left + 2, center_y - track_h / 2 + 2, fill_end - 1, center_y - 1)
            if highlight_rect[2] > highlight_rect[0] + 1:
                draw.rounded_rectangle(
                    sc_rect(highlight_rect),
                    radius=int(max(1, (radius - 2) * scale)),
                    fill=DIALOG_SLIDER_FILL_HIGHLIGHT,
                )

        # Knob shadow and body.
        knob_r = 12
        knob_x = max(left, min(right, fill_end))
        shadow_offset = 2
        shadow_bbox = (
            knob_x - knob_r,
            center_y - knob_r + shadow_offset,
            knob_x + knob_r,
            center_y + knob_r + shadow_offset,
        )
        draw.ellipse(sc_rect(shadow_bbox), fill=DIALOG_SLIDER_KNOB_SHADOW)

        knob_bbox = (knob_x - knob_r, center_y - knob_r, knob_x + knob_r, center_y + knob_r)
        draw.ellipse(sc_rect(knob_bbox), fill=DIALOG_SLIDER_KNOB, outline=DIALOG_SLIDER_KNOB_OUTLINE, width=scale * 2)

        # Small shine on the knob.
        shine_bbox = (knob_x - 5, center_y - 7, knob_x + 2, center_y)
        draw.ellipse(sc_rect(shine_bbox), fill="#ffffff")

        return img.resize((w, h), Image.Resampling.LANCZOS)

    def _set_canvas_slider_value(self, canvas, value, on_change=None):
        value = max(0.0, min(100.0, float(value)))
        canvas._slider_value = value

        width, height = self._canvas_display_size(canvas)
        image = self._draw_rounded_slider_image(width, height, value)
        photo = ImageTk.PhotoImage(image)

        canvas.delete("all")
        canvas.create_image(0, 0, image=photo, anchor="nw")
        canvas._slider_photo = photo

        if on_change:
            on_change(value)

    def _create_canvas_slider(self, parent, initial_value, on_change):
        canvas = tk.Canvas(
            parent,
            width=360,
            height=52,
            bg=DIALOG_PANEL_BG,
            highlightthickness=0,
            bd=0,
            cursor="hand2",
        )

        def value_from_event(event):
            width, _height = self._canvas_display_size(canvas)
            left = 22
            right = max(left + 20, width - 22)
            ratio = (event.x - left) / max(1, (right - left))
            return max(0.0, min(100.0, ratio * 100.0))

        def update_from_event(event):
            self._set_canvas_slider_value(canvas, value_from_event(event), on_change)

        def redraw(_event=None):
            self._set_canvas_slider_value(canvas, getattr(canvas, "_slider_value", initial_value), on_change=None)

        canvas.bind("<Button-1>", update_from_event)
        canvas.bind("<B1-Motion>", update_from_event)
        canvas.bind("<Configure>", redraw)
        self._set_canvas_slider_value(canvas, initial_value, on_change=None)
        return canvas

    def _execute_show_volume_dialog(self):
        self._prepare_dialog_owner()
        dialog = tk.Toplevel(self.root)
        width, height = 460, 300
        self._configure_dialog_base(dialog, "音量設定", width, height)
        panel = self._make_dialog_panel(dialog)

        self._dialog_label(panel, "効果音の音量", font=DIALOG_TITLE_FONT, pady=(0, 8))
        self._dialog_label(
            panel,
            "タイマー開始音やリセット音の大きさを調整します。",
            fg=DIALOG_MUTED_FG,
            pady=(0, 14),
            wraplength=380,
        )

        value_label = tk.Label(
            panel,
            text=f"{int(self.volume_level)}%",
            bg=DIALOG_PANEL_BG,
            fg=DIALOG_FG,
            font=("Yu Gothic UI", 24, "bold"),
            anchor="center",
        )
        value_label.pack(fill="x", pady=(0, 8))

        def on_slider_change(value):
            self.volume_level = float(value)
            value_label.config(text=f"{int(round(float(value)))}%")
            self.apply_volume_to_mixer()

        volume_slider = self._create_canvas_slider(panel, self.volume_level, on_slider_change)
        volume_slider.pack(fill="x", pady=(0, 18))

        def close_dialog():
            self.save_config()
            dialog.destroy()
            self.root.withdraw()

        buttons = tk.Frame(panel, bg=DIALOG_PANEL_BG)
        buttons.pack(fill="x", side="bottom", pady=(8, 0))
        self._pack_dialog_button(
            buttons,
            self._dialog_button(buttons, "閉じる", close_dialog, primary=True),
            side="right",
            padx=(0, 0),
        )

        dialog.protocol("WM_DELETE_WINDOW", close_dialog)
        dialog.bind("<Escape>", lambda _event: close_dialog())
        dialog.grab_set()
        dialog.focus_force()
        self.root.wait_window(dialog)
        self._restore_dialog_owner()

    def _is_physical_key_pressed(self, *names):
        """Return True if any of the given physical keys are currently pressed."""
        for name in names:
            try:
                if keyboard.is_pressed(name):
                    return True
            except Exception:
                pass
        return False

    def _hotkey_from_tk_event(self, event):
        modifier_keysyms = {
            "Shift_L",
            "Shift_R",
            "Control_L",
            "Control_R",
            "Alt_L",
            "Alt_R",
            "Meta_L",
            "Meta_R",
            "Win_L",
            "Win_R",
        }
        if event.keysym in modifier_keysyms:
            return None

        key_map = {
            "Return": "enter",
            "Escape": "esc",
            "BackSpace": "backspace",
            "Delete": "delete",
            "Insert": "insert",
            "Home": "home",
            "End": "end",
            "Prior": "page up",
            "Next": "page down",
            "Left": "left",
            "Right": "right",
            "Up": "up",
            "Down": "down",
            "Tab": "tab",
            "space": "space",
            "comma": ",",
            "period": ".",
            "slash": "/",
            "backslash": "\\",
            "minus": "-",
            "equal": "=",
            "semicolon": ";",
            "apostrophe": "'",
            "bracketleft": "[",
            "bracketright": "]",
            "grave": "`",
        }

        key = key_map.get(event.keysym, event.keysym.lower())
        if len(key) == 1:
            key = key.lower()

        # Tkのevent.stateは環境によってAlt相当のビットが常時立つことがあるため、
        # 修飾キーはkeyboardライブラリで「実際に押されているキー」を見る。
        modifiers = []
        if self._is_physical_key_pressed("ctrl", "left ctrl", "right ctrl"):
            modifiers.append("ctrl")
        if self._is_physical_key_pressed("shift", "left shift", "right shift"):
            modifiers.append("shift")
        if self._is_physical_key_pressed("alt", "left alt", "right alt"):
            modifiers.append("alt")

        return "+".join(modifiers + [key]) if modifiers else key

    def _show_hotkey_capture_dialog(self, *, title, heading, current_value=""):
        result = {"value": None}
        self._prepare_dialog_owner()
        dialog = tk.Toplevel(self.root)
        width, height = 460, 285
        self._configure_dialog_base(dialog, title, width, height)
        panel = self._make_dialog_panel(dialog)

        self._dialog_label(panel, heading, font=DIALOG_TITLE_FONT, pady=(0, 8), wraplength=400)
        self._dialog_label(
            panel,
            "下の欄をクリックして、設定したいキーを押してください。Ctrl / Shift / Alt との組み合わせも設定できます。",
            fg=DIALOG_MUTED_FG,
            pady=(0, 14),
            wraplength=400,
        )

        hotkey_var = tk.StringVar(value=current_value or "")
        capture_entry = tk.Entry(
            panel,
            textvariable=hotkey_var,
            bg=DIALOG_INPUT_BG,
            fg=DIALOG_FG,
            insertbackground=DIALOG_FG,
            relief="flat",
            highlightthickness=1,
            highlightbackground=DIALOG_BORDER,
            highlightcolor=DIALOG_ACCENT,
            font=("Consolas", 13, "bold"),
            justify="center",
            readonlybackground=DIALOG_INPUT_BG,
        )
        capture_entry.pack(fill="x", ipady=10, pady=(0, 8))

        hint_label = tk.Label(
            panel,
            text="未設定にする場合は「空欄にする」を押してください。",
            bg=DIALOG_PANEL_BG,
            fg=DIALOG_MUTED_FG,
            font=DIALOG_SMALL_FONT,
            anchor="w",
        )
        hint_label.pack(fill="x", pady=(0, 8))

        def capture_key(event):
            if event.keysym in {"Return", "KP_Enter"}:
                confirm()
                return "break"
            if event.keysym == "Escape":
                cancel()
                return "break"

            hotkey_text = self._hotkey_from_tk_event(event)
            if hotkey_text:
                hotkey_var.set(hotkey_text)
                capture_entry.selection_range(0, tk.END)
            return "break"

        def clear_hotkey():
            hotkey_var.set("")
            capture_entry.focus_set()

        def confirm():
            result["value"] = hotkey_var.get().strip().lower().replace(" ", "")
            dialog.destroy()

        def cancel():
            dialog.destroy()

        capture_entry.bind("<KeyPress>", capture_key)
        capture_entry.bind("<Button-1>", lambda _event: capture_entry.focus_set())

        buttons = tk.Frame(panel, bg=DIALOG_PANEL_BG)
        buttons.pack(fill="x", side="bottom", pady=(10, 0))
        self._pack_dialog_button(
            buttons,
            self._dialog_button(buttons, "キャンセル", cancel),
            side="right",
            padx=(DIALOG_BUTTON_GAP, 0),
        )
        self._pack_dialog_button(
            buttons,
            self._dialog_button(buttons, "保存", confirm, primary=True),
            side="right",
            padx=(0, 0),
        )
        self._pack_dialog_button(
            buttons,
            self._dialog_button(buttons, "空欄にする", clear_hotkey),
            side="left",
            padx=(0, 0),
        )

        dialog.protocol("WM_DELETE_WINDOW", cancel)
        dialog.bind("<Escape>", lambda _event: cancel())
        dialog.grab_set()
        capture_entry.focus_set()
        capture_entry.selection_range(0, tk.END)
        self.root.wait_window(dialog)
        self._restore_dialog_owner()
        return result["value"]

    def _execute_change_hotkey(self, key_id):
        if not isinstance(key_id, str) or key_id not in getattr(self, "valid_hotkey_ids", set()):
            print(f"Invalid hotkey id ignored: {key_id!r}")
            return

        label = self._hotkey_action_label(key_id)
        current = self.hotkey_config.get(key_id, "")
        new_key = self._show_hotkey_capture_dialog(
            title="ショートカットキー設定",
            heading=label,
            current_value=current,
        )

        if new_key is None:
            return

        self.hotkey_config[key_id] = new_key
        self.setup_hooks()
        self.save_config()
        self.refresh_tray_menu()
        self.root.withdraw()

    def _show_preset_edit_dialog(self, current):
        result = {"action": None, "value": None}
        self._prepare_dialog_owner()
        dialog = tk.Toplevel(self.root)
        width, height = 460, 285
        self._configure_dialog_base(dialog, "プリセット編集", width, height)
        panel = self._make_dialog_panel(dialog)

        self._dialog_label(
            panel,
            f"{self._format_preset_label(current)} を編集",
            font=DIALOG_TITLE_FONT,
            pady=(0, 8),
            wraplength=400,
        )
        self._dialog_label(
            panel,
            "秒数で入力してください。プリセットの削除をする場合は左下の「削除」ボタンを押してください。",
            fg=DIALOG_MUTED_FG,
            pady=(0, 14),
            wraplength=390,
        )

        entry_var = tk.StringVar(value=str(current))
        entry = tk.Entry(
            panel,
            textvariable=entry_var,
            bg=DIALOG_INPUT_BG,
            fg=DIALOG_FG,
            insertbackground=DIALOG_FG,
            relief="flat",
            highlightthickness=1,
            highlightbackground=DIALOG_BORDER,
            highlightcolor=DIALOG_ACCENT,
            font=("Consolas", 12),
            justify="center",
        )
        entry.pack(fill="x", ipady=8, pady=(0, 8))

        error_label = tk.Label(
            panel,
            text="",
            bg=DIALOG_PANEL_BG,
            fg=DIALOG_DANGER,
            font=DIALOG_SMALL_FONT,
            anchor="w",
        )
        error_label.pack(fill="x", pady=(0, 8))

        def save_value():
            value_text = entry_var.get().strip()
            if value_text == "":
                error_label.config(text="秒数を入力してください。")
                return
            result["action"] = "save"
            result["value"] = value_text
            dialog.destroy()

        def delete_value():
            result["action"] = "delete"
            dialog.destroy()

        def cancel():
            dialog.destroy()

        buttons = tk.Frame(panel, bg=DIALOG_PANEL_BG)
        buttons.pack(fill="x", side="bottom", pady=(10, 0))
        self._pack_dialog_button(
            buttons,
            self._dialog_button(buttons, "キャンセル", cancel),
            side="right",
            padx=(DIALOG_BUTTON_GAP, 0),
        )
        self._pack_dialog_button(
            buttons,
            self._dialog_button(buttons, "保存", save_value, primary=True),
            side="right",
            padx=(0, 0),
        )
        self._pack_dialog_button(
            buttons,
            self._dialog_button(buttons, "削除", delete_value, danger=True),
            side="left",
            padx=(0, 0),
        )

        dialog.protocol("WM_DELETE_WINDOW", cancel)
        dialog.bind("<Return>", lambda _event: save_value())
        dialog.bind("<Escape>", lambda _event: cancel())
        dialog.grab_set()
        entry.focus_set()
        entry.selection_range(0, tk.END)
        self.root.wait_window(dialog)
        self._restore_dialog_owner()

        if result["action"] is None:
            return None
        return result

    def _execute_edit_preset(self, index):
        if index >= len(self.presets):
            return

        current = self.presets[index]
        result = self._show_preset_edit_dialog(current)

        if result is None:
            return

        if result.get("action") == "delete":
            self.presets.pop(index)
            self.selected_preset_index = 0
            self.save_config()
            self.refresh_tray_menu()
            self.root.withdraw()
            return

        new_val = result.get("value", "")
        try:
            val = int(new_val)
        except ValueError:
            self._show_notice_dialog("入力エラー", "数字で入力してください", "1〜5999の範囲で秒数を入力してください。", danger=True)
            return

        if val < 1 or val > 5999:
            self._show_notice_dialog("入力エラー", "範囲外です", "1〜5999の範囲で入力してください。削除する場合は削除ボタンを押してください。", danger=True)
            return

        self.presets[index] = val
        self.presets.sort()
        self.save_config()
        self.refresh_tray_menu()
        self.root.withdraw()

    def _execute_add_preset(self):
        new_val = self._show_text_input_dialog(
            title="プリセット追加",
            heading="新しいタイマー時間",
            description="追加する時間を秒数で入力してください。1〜5999秒まで指定できます。",
            initial_value="300",
            confirm_text="追加",
            allow_blank=False,
        )

        if new_val is None:
            return

        try:
            val = int(new_val)
        except ValueError:
            self._show_notice_dialog("入力エラー", "数字で入力してください", "1〜5999の範囲で秒数を入力してください。", danger=True)
            return

        if val < 1 or val > 5999:
            self._show_notice_dialog("入力エラー", "範囲外です", "1〜5999の範囲で入力してください。", danger=True)
            return

        self.presets.append(val)
        self.presets.sort()
        self.save_config()
        self.refresh_tray_menu()
        self.root.withdraw()

    # ------------------------------------------------------------------
    # Hooks and actions
    # ------------------------------------------------------------------

    def setup_hooks(self):
        keyboard.unhook_all()
        mouse.unhook_all()
        keyboard.hook(self._on_key_event)
        mouse.hook(self._on_mouse_event)

    def _on_key_event(self, e):
        if not self.hotkey_enabled or e.event_type != "down":
            return

        key_name = e.name.lower()
        if key_name == "enter" or e.scan_code == 28:
            self._handle_enter_key()
            return

        if self.is_typing_mode or not self.is_target_foreground_exact():
            return

        current_combination = self._current_hotkey_combination(key_name)
        action = self._hotkey_action_map().get(self._find_action_id(current_combination))
        if action:
            self.overlay.after(0, action)

    def _handle_enter_key(self):
        if self.target_hwnd and win32gui.GetForegroundWindow() == self.target_hwnd:
            if not self.is_typing_mode:
                self.is_typing_mode = True
                self.play_sound("enter")
                self.overlay.after(0, self.draw_timer)

    def _current_hotkey_combination(self, key_name):
        mods = []
        if keyboard.is_pressed("ctrl"):
            mods.append("ctrl")
        if keyboard.is_pressed("shift"):
            mods.append("shift")
        if keyboard.is_pressed("alt"):
            mods.append("alt")
        return "+".join(mods + [key_name]) if mods else key_name

    def _find_action_id(self, current_combination):
        for action_id, cfg_hotkey in self.hotkey_config.items():
            if cfg_hotkey == current_combination:
                return action_id
        return None

    def _hotkey_action_map(self):
        return {
            "reset_timer": self.reset_selected_timer,
            "reset_all_timers": self.reset_timer,
            "add_timer": lambda: self.add_timer(self.presets[self.selected_preset_index]),
            "inc_counter1": lambda: self.increment_counter(1),
            "dec_counter1": lambda: self.decrement_counter(1),
            "reset_counter1": lambda: self.reset_specific_counter(1),
            "inc_counter2": lambda: self.increment_counter(2),
            "dec_counter2": lambda: self.decrement_counter(2),
            "reset_counter2": lambda: self.reset_specific_counter(2),
            "prev_preset": self.cycle_preset_prev,
            "next_preset": self.cycle_preset_next,
            "move_cursor": self.move_cursor,
        }

    def _on_mouse_event(self, e):
        if not isinstance(e, mouse.ButtonEvent):
            return
        if e.event_type != "down" or e.button != "left":
            return
        if not self.is_typing_mode:
            return
        if self.target_hwnd and win32gui.GetForegroundWindow() == self.target_hwnd:
            self.is_typing_mode = False
            self.overlay.after(0, self.draw_timer)

    def move_cursor(self):
        valid_indices = [0] if self.is_counting else []
        valid_indices += [i + 1 for i in range(len(self.timers))]

        if not valid_indices:
            self.selected_cursor_index = 0
            self.draw_timer()
            return

        try:
            cur = valid_indices.index(self.selected_cursor_index)
            new_idx = valid_indices[(cur + 1) % len(valid_indices)]
            if new_idx != self.selected_cursor_index:
                self.play_sound("cursor")
            self.selected_cursor_index = new_idx
        except ValueError:
            self.selected_cursor_index = valid_indices[0]
        self.draw_timer()

    def validate_cursor_position(self):
        valid_indices = [0] if self.is_counting else []
        valid_indices += [i + 1 for i in range(len(self.timers))]

        if not valid_indices:
            self.selected_cursor_index = 0
            return

        if self.selected_cursor_index not in valid_indices:
            self.selected_cursor_index = (
                max(valid_indices) if self.selected_cursor_index > max(valid_indices) else valid_indices[0]
            )

    # ------------------------------------------------------------------
    # Tray menu
    # ------------------------------------------------------------------

    def _tray_action(self, func, *bound_args):
        # pystray can pass the tray icon and the clicked menu item to callbacks.
        # Bound values such as key_id/index must therefore be captured after
        # those callback arguments, otherwise the icon object may be mistaken
        # for a hotkey id.
        def callback(icon=None, menu_item=None):
            return func(*bound_args)

        return callback

    def refresh_tray_menu(self):
        if self.tray_icon:
            self.tray_icon.menu = self.create_tray_menu()

    def create_tray_menu(self):
        hotkey_settings_items = []
        for entry in HOTKEY_ACTION_LABELS:
            if entry is None:
                hotkey_settings_items.append(pystray.Menu.SEPARATOR)
                continue
            key_id, label = entry
            hotkey_settings_items.append(
                item(
                    lambda _, key_id=key_id, label=label: self._hotkey_menu_label(key_id, label),
                    self._tray_action(self.request_change_hotkey, key_id),
                )
            )

        preset_items = [
            item(
                self._format_preset_label(preset),
                self._tray_action(self.request_edit_preset, index),
            )
            for index, preset in enumerate(self.presets)
        ]
        preset_items += [
            pystray.Menu.SEPARATOR,
            item("新規追加...", self._tray_action(self.request_add_preset)),
        ]

        return pystray.Menu(
            item("ショートカットキー設定", pystray.Menu(*hotkey_settings_items)),
            item("タイマープリセット編集", pystray.Menu(*preset_items)),
            pystray.Menu.SEPARATOR,
            item(
                "表示サイズ",
                pystray.Menu(
                    item(
                        "標準 (1.0x)",
                        self._tray_action(self.set_scale, 1.0),
                        checked=lambda _: self.scale == 1.0,
                        radio=True,
                    ),
                    item(
                        "大 (2.0x)",
                        self._tray_action(self.set_scale, 2.0),
                        checked=lambda _: self.scale == 2.0,
                        radio=True,
                    ),
                ),
            ),
            item(
                "表示位置",
                pystray.Menu(
                    item(
                        "標準 (上)",
                        self._tray_action(self.set_origin_y, 114),
                        checked=lambda _: self.origin_y == 114,
                        radio=True,
                    ),
                    item(
                        "やや下",
                        self._tray_action(self.set_origin_y, 150),
                        checked=lambda _: self.origin_y == 150,
                        radio=True,
                    ),
                ),
            ),
            pystray.Menu.SEPARATOR,
            item("ショートカットキー有効", self.toggle_hotkeys, checked=lambda _: self.hotkey_enabled),
            item("タイマー自動スタート有効", self.toggle_auto_start, checked=lambda _: self.auto_start_enabled),
            item("カウンターを表示", self.toggle_counter, checked=lambda _: self.counter_enabled),
            pystray.Menu.SEPARATOR,
            item("効果音を再生", self.toggle_sound, checked=lambda _: self.sound_enabled),
            item("音量設定...", self._tray_action(self.request_show_volume_dialog)),
            pystray.Menu.SEPARATOR,
            item("終了", self.quit_app),
        )

    def _hotkey_menu_label(self, key_id, base_text):
        hotkey = self.hotkey_config.get(key_id, "").upper()
        return f"{base_text} [{hotkey if hotkey else '未設定'}]"

    def _format_preset_label(self, seconds):
        return f"{seconds // 60}分{seconds % 60}秒" if seconds % 60 else f"{seconds // 60}分"

    def setup_tray(self):
        try:
            icon_img = Image.open(resource_path("choco_timer.ico", "images"))
            self.tray_icon = pystray.Icon(
                "choco_timer",
                icon_img,
                "チョコットタイマー",
                menu=self.create_tray_menu(),
            )
            threading.Thread(target=self.tray_icon.run, daemon=True).start()
        except Exception:
            pass

    def toggle_sound(self, icon=None, menu_item=None):
        self.sound_enabled = not self.sound_enabled
        self.save_config()
        self.refresh_tray_menu()

    def toggle_counter(self, icon=None, menu_item=None):
        self.counter_enabled = not self.counter_enabled
        self.save_config()
        self.draw_timer()
        self.refresh_tray_menu()

    def toggle_hotkeys(self, icon=None, menu_item=None):
        self.hotkey_enabled = not self.hotkey_enabled
        self.setup_hooks()
        self.save_config()
        self.refresh_tray_menu()

    def toggle_auto_start(self, icon=None, menu_item=None):
        self.auto_start_enabled = not self.auto_start_enabled
        self.save_config()
        self.refresh_tray_menu()

    # ------------------------------------------------------------------
    # Drawing
    # ------------------------------------------------------------------

    def set_scale(self, new_scale):
        self.scale = new_scale
        self.apply_scale()
        self.save_config()
        self.refresh_tray_menu()

    def set_origin_y(self, new_y):
        self.origin_y = new_y
        self.save_config()
        self.draw_timer()
        self.refresh_tray_menu()

    def _draw_image(self, x, y, image_name):
        if image_name in self.images:
            self.canvas.create_image(
                self._round_half_up(x),
                self._round_half_up(y),
                image=self.images[image_name],
                anchor="nw",
            )

    def draw_timer(self):
        self.canvas.delete("all")
        s = self.get_effective_scale()
        bx, by = self._overlay_base_position()

        if self.is_typing_mode:
            self._draw_image(bx, by, "keyboard")

        draw_y = by + 1 * s
        if self.preview_timer_id and self.presets:
            self._render_select_time_images(
                self.presets[self.selected_preset_index],
                bx + (13 * s),
                draw_y,
            )

        draw_y += self.base_timer_spacing * s
        if self.counter_enabled:
            self._render_counter_images(
                self.counter1,
                self.counter2,
                bx + (self.counter_offset_x * s),
                draw_y,
            )
            draw_y += self.base_timer_spacing * s

        if self.is_counting:
            if self.selected_cursor_index == 0:
                self._draw_image(bx + (self.cursor_offset_x * s), draw_y - 1 * s, "cursor")
            self._render_feather_time_images(
                self.feather_timer,
                bx + (self.timer_offset_x * s),
                draw_y,
            )
            draw_y += self.base_timer_spacing * s

        for index, timer in enumerate(self.timers):
            if self.selected_cursor_index == (index + 1):
                self._draw_image(bx + (self.cursor_offset_x * s), draw_y - 1 * s, "cursor")
            self._render_time_images(timer["seconds"], bx + (self.timer_offset_x * s), draw_y)
            draw_y += self.base_timer_spacing * s

    def _overlay_base_position(self):
        # 位置はWindowsの表示倍率に追従し、アプリ内表示サイズ self.scale では動かさない。
        dpi_scale = getattr(self, "dpi_scale", 1.0)
        return (
            self._round_half_up(self.origin_x * dpi_scale),
            self._round_half_up(self.origin_y * dpi_scale),
        )

    def _time_digits(self, total_seconds):
        mins, secs = divmod(total_seconds, 60)
        m1, m2 = divmod(mins, 10)
        s1, s2 = divmod(secs, 10)
        return [str(m1), str(m2), "colon", str(s1), str(s2)]

    def _draw_digit_row(self, x, y, image_names, offsets):
        s = self.get_effective_scale()
        for offset, image_name in zip(offsets, image_names):
            self._draw_image(x + offset * s, y - 1 * s, image_name)

    def _render_feather_time_images(self, total_seconds, x, y):
        s = self.get_effective_scale()
        self._draw_image(x - 1 * s, y - 1 * s, "feather")
        self._draw_digit_row(x, y, self._time_digits(total_seconds), [11, 18, 25, 32, 39])

    def _render_select_time_images(self, total_seconds, x, y):
        s = self.get_effective_scale()
        self._draw_image(x + 2 * s, y - 1 * s, "left")
        self._draw_digit_row(
            x,
            y,
            self._time_digits(total_seconds) + ["right"],
            [11, 18, 25, 32, 39, 48],
        )

    def _render_time_images(self, total_seconds, x, y):
        self._draw_image(x, y, "clock")
        self._draw_digit_row(x, y, self._time_digits(total_seconds), [11, 18, 25, 32, 39])

    def _render_counter_images(self, c1, c2, x, y):
        s = self.get_effective_scale()
        self._draw_image(x, y, "counter")
        for index, digit in enumerate(f"{c1:04d}"):
            self._draw_image(x + (12 + index * 7) * s, y - 1 * s, digit)
        self._draw_image(x + 42 * s, y - 1 * s, "slash")
        for index, digit in enumerate(f"{c2:04d}"):
            self._draw_image(x + (51 + index * 7) * s, y - 1 * s, digit)

    # ------------------------------------------------------------------
    # Window tracking and icon detection
    # ------------------------------------------------------------------

    def find_target_window(self):
        hwnd = win32gui.FindWindow(self.target_class, None)
        return hwnd if hwnd else win32gui.FindWindow(None, self.target_title)

    def get_window_rect(self, hwnd):
        return win32gui.GetWindowRect(hwnd)

    def update_overlay(self):
        try:
            self.target_hwnd = self.find_target_window()
            if self.target_hwnd and win32gui.IsWindow(self.target_hwnd):
                self._update_overlay_for_existing_target()
            else:
                self._handle_target_not_found()
        except Exception:
            pass
        self.root.after(OVERLAY_UPDATE_INTERVAL_MS, self.update_overlay)

    def _update_overlay_for_existing_target(self):
        self.not_found_start_time = None
        self.update_dpi_scale_for_target()

        if self.is_target_minimized() or not self.is_target_foreground_exact():
            self.overlay.withdraw()
            if self.is_typing_mode:
                self.is_typing_mode = False
            return

        left, top, right, bottom = self.get_window_rect(self.target_hwnd)
        width = right - left
        height = bottom - top
        self.canvas.config(width=width, height=height)
        self.overlay.geometry(f"{width}x{height}+{left}+{top}")
        self.draw_timer()
        self.overlay.deiconify()

    def _handle_target_not_found(self):
        if self.not_found_start_time is None:
            self.not_found_start_time = time.time()
        if time.time() - self.not_found_start_time > AUTO_QUIT_AFTER_SECONDS:
            self.quit_app()
            return
        self.overlay.withdraw()


    def is_target_foreground_exact(self):
        try:
            return bool(self.target_hwnd and win32gui.GetForegroundWindow() == self.target_hwnd)
        except Exception:
            return False

    def is_target_foreground(self):
        try:
            if not self.target_hwnd or not win32gui.IsWindow(self.target_hwnd):
                return False

            foreground_hwnd = win32gui.GetForegroundWindow()
            if foreground_hwnd == self.target_hwnd:
                return True

            try:
                return win32gui.GetAncestor(foreground_hwnd, 2) == self.target_hwnd
            except Exception:
                return False
        except Exception:
            return False

    def is_target_minimized(self):
        try:
            placement = win32gui.GetWindowPlacement(self.target_hwnd)
            return placement[1] == win32con.SW_SHOWMINIMIZED
        except Exception:
            return True

    def _get_icon_search_regions(self):
        margin_x = int(self.icon_search_margin_x)
        margin_y = int(self.icon_search_margin_y)
        src_x = max(0, int(self.icon_search_x) - margin_x)
        src_y = max(0, int(self.icon_search_y) - margin_y)
        width = int(self.icon_search_w) + margin_x * 2
        height = int(self.icon_search_h) + margin_y * 2
        return [{"src_rect": (src_x, src_y, width, height)}]

    def _capture_windowdc_region_bgr(self, src_x, src_y, width, height):
        hwnd_dc = None
        src_dc = None
        mem_dc = None
        bmp = None
        try:
            hwnd_dc = win32gui.GetWindowDC(self.target_hwnd)
            if not hwnd_dc:
                return None

            src_dc = win32ui.CreateDCFromHandle(hwnd_dc)
            mem_dc = src_dc.CreateCompatibleDC()

            bmp = win32ui.CreateBitmap()
            bmp.CreateCompatibleBitmap(src_dc, width, height)
            mem_dc.SelectObject(bmp)

            mem_dc.BitBlt(
                (0, 0),
                (width, height),
                src_dc,
                (src_x, src_y),
                win32con.SRCCOPY,
            )

            bmp_info = bmp.GetInfo()
            bmp_bits = bmp.GetBitmapBits(True)
            bmp_w = bmp_info["bmWidth"]
            bmp_h = bmp_info["bmHeight"]

            arr = np.frombuffer(bmp_bits, dtype=np.uint8).reshape((bmp_h, bmp_w, 4))
            return arr[:, :, :3].copy()
        except Exception as e:
            print(f"BitBlt capture error: {e}")
            return None
        finally:
            self._release_bitblt_objects(hwnd_dc, src_dc, mem_dc, bmp)

    def _release_bitblt_objects(self, hwnd_dc, src_dc, mem_dc, bmp):
        try:
            if bmp:
                win32gui.DeleteObject(bmp.GetHandle())
        except Exception:
            pass
        try:
            if mem_dc:
                mem_dc.DeleteDC()
        except Exception:
            pass
        try:
            if src_dc:
                src_dc.DeleteDC()
        except Exception:
            pass
        try:
            if hwnd_dc:
                win32gui.ReleaseDC(self.target_hwnd, hwnd_dc)
        except Exception:
            pass

    def _find_matching_icon_index(self, frame_bgr):
        frame_h, frame_w = frame_bgr.shape[:2]
        for idx, template in enumerate(self.templates):
            th, tw = template.shape[:2]
            if tw > frame_w or th > frame_h:
                continue

            res = cv2.matchTemplate(frame_bgr, template, cv2.TM_CCOEFF_NORMED)
            if cv2.minMaxLoc(res)[1] >= self.threshold:
                return idx
        return None

    def _start_detected_icon_timer(self, idx):
        if self.current_icon_index != idx:
            self.current_icon_index = idx
            self.start_countdown(self.icon_config.get(self.icon_filenames[idx], 300))

    def _schedule_icon_check(self):
        self.root.after(self.icon_check_interval_ms, self.check_icon_loop)

    def check_icon_loop(self):
        try:
            if not (self.auto_start_enabled and self.target_hwnd and self.templates):
                return

            self.update_dpi_scale_for_target()
            if self.is_target_minimized() or not self.is_target_foreground():
                return

            regions = self._get_icon_search_regions()
            if not regions:
                return

            src_x, src_y, width, height = regions[0]["src_rect"]
            frame_bgr = self._capture_windowdc_region_bgr(src_x, src_y, width, height)
            if frame_bgr is None:
                return

            idx = self._find_matching_icon_index(frame_bgr)
            if idx is not None:
                self._start_detected_icon_timer(idx)
        except Exception as e:
            print(f"Icon check error: {e}")
        finally:
            self._schedule_icon_check()

    # ------------------------------------------------------------------
    # Timers and counters
    # ------------------------------------------------------------------

    def start_countdown(self, seconds):
        self.play_sound("timer_start")
        self.target_time = time.time() + seconds
        self.feather_timer = int(seconds)
        self.is_counting = True
        self.selected_cursor_index = 0
        if not self.tick_id:
            self.tick_timer()

    def add_timer(self, seconds):
        if len(self.timers) >= self.max_timers:
            self.play_sound("cancel")
            return
        self.play_sound("timer_start")
        self.timers.append({"target_time": time.time() + seconds, "seconds": int(seconds)})
        if not self.tick_id:
            self.tick_timer()

    def reset_selected_timer(self):
        if self.selected_cursor_index == 0 and self.is_counting:
            self.feather_timer = 0
            self.is_counting = False
            self.current_icon_index = -1
            self.play_sound("reset")
        else:
            idx = self.selected_cursor_index - 1
            if 0 <= idx < len(self.timers):
                self.timers.pop(idx)
                self.play_sound("reset")
        self.validate_cursor_position()
        self.draw_timer()

    def reset_timer(self):
        if not (self.is_counting or self.timers):
            return

        self.play_sound("reset")
        self.feather_timer = 0
        self.is_counting = False
        self.timers = []
        self.current_icon_index = -1
        self.selected_cursor_index = 0
        if self.tick_id:
            self.overlay.after_cancel(self.tick_id)
            self.tick_id = None
        self.draw_timer()

    def tick_timer(self):
        now = time.time()
        any_running = False

        if self.is_counting:
            rem = int(self.target_time - now)
            if rem >= 0:
                self.feather_timer = rem
                any_running = True
            else:
                self.feather_timer = 0
                self.is_counting = False
                self.current_icon_index = -1

        active = []
        for timer in self.timers:
            rem = int(timer["target_time"] - now)
            if rem >= 0:
                timer["seconds"] = rem
                active.append(timer)
                any_running = True
        self.timers = active
        self.validate_cursor_position()

        if any_running:
            self.tick_id = self.overlay.after(TIMER_TICK_INTERVAL_MS, self.tick_timer)
        else:
            self.tick_id = None
        self.draw_timer()

    def increment_counter(self, num):
        if not self.counter_enabled:
            return
        self.play_sound("counter")
        if num == 1:
            self.counter1 = (self.counter1 + 1) % 10000
        elif num == 2:
            self.counter2 = (self.counter2 + 1) % 10000
        self.draw_timer()

    def decrement_counter(self, num):
        if not self.counter_enabled:
            return
        self.play_sound("counter")
        if num == 1:
            self.counter1 = max(0, self.counter1 - 1)
        elif num == 2:
            self.counter2 = max(0, self.counter2 - 1)
        self.draw_timer()

    def reset_specific_counter(self, num):
        if not self.counter_enabled:
            return
        self.play_sound("reset")
        if num == 1:
            self.counter1 = 0
        elif num == 2:
            self.counter2 = 0
        self.draw_timer()

    def cycle_preset_next(self):
        if not self.presets:
            return
        self.play_sound("timer_select")
        self.selected_preset_index = (self.selected_preset_index + 1) % len(self.presets)
        self.show_preset_preview()

    def cycle_preset_prev(self):
        if not self.presets:
            return
        self.play_sound("timer_select")
        self.selected_preset_index = (self.selected_preset_index - 1) % len(self.presets)
        self.show_preset_preview()

    def show_preset_preview(self):
        self.draw_timer()
        if self.preview_timer_id:
            self.overlay.after_cancel(self.preview_timer_id)
        self.preview_timer_id = self.overlay.after(PREVIEW_DURATION_MS, self._hide_preview)

    def _hide_preview(self):
        self.preview_timer_id = None
        self.draw_timer()

    # ------------------------------------------------------------------
    # Public request helpers and shutdown
    # ------------------------------------------------------------------

    def request_change_hotkey(self, key_id):
        if not isinstance(key_id, str) or key_id not in getattr(self, "valid_hotkey_ids", set()):
            print(f"Invalid hotkey id ignored: {key_id!r}")
            return
        self._enqueue("change_hotkey", key_id=key_id)

    def request_edit_preset(self, index):
        self._enqueue("edit_preset", index=index)

    def request_add_preset(self):
        self._enqueue("add_preset")

    def request_show_volume_dialog(self):
        self._enqueue("show_volume_dialog")

    def quit_app(self, icon=None, menu_item=None):
        if self.tray_icon:
            self.tray_icon.stop()
        pygame.mixer.quit()
        self.root.after(0, self.root.destroy)

    def run(self):
        self.root.mainloop()


if __name__ == "__main__":
    enable_dpi_awareness()

    default_hotkeys = {
        "add_timer": "t",
        "reset_timer": "r",
        "reset_all_timers": "ctrl+r",
        "move_cursor": "tab",
        "prev_preset": ",",
        "next_preset": ".",
        "inc_counter1": "z",
        "dec_counter1": "shift+z",
        "reset_counter1": "ctrl+z",
        "inc_counter2": "x",
        "dec_counter2": "shift+x",
        "reset_counter2": "ctrl+x",
    }

    app = OverlayApp(
        "xtWin32WindowBase",
        "チョコットランド",
        {
            "bell.dat": 297,
            "juda.dat": 9,
            "eru.dat": 300,
            "retro.dat": 300,
            "shira.dat": 300,
            "fiss.dat": 300,
            "bene.dat": 300,
            "renamana.dat": 300,
            "riarie.dat": 300,
            "roya.dat": 300,
            "code.dat": 90,
        },
        default_hotkeys,
    )
    app.run()
