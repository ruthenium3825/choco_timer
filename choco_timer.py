import tkinter as tk
from tkinter import simpledialog, messagebox, ttk
from PIL import Image, ImageTk
import win32gui
import win32con
import win32api
import win32event
import winerror
import cv2
import numpy as np
import dxcam
import os
import sys
import keyboard
import mouse
import threading
import pystray
from pystray import MenuItem as item
import time
import queue
import json
import pygame

def resource_path(relative_path, folder="images"):
    """ Resolve resource path for compiled executable """
    try:
        base_path = sys._MEIPASS
    except Exception:
        base_path = os.path.abspath(".")
    
    path = os.path.join(base_path, folder, relative_path)
    if not os.path.exists(path):
        path = os.path.join(base_path, relative_path)
    return path

CONFIG_FILE = "config.json"

class OverlayApp:
    def __init__(self, target_class, target_title, icon_config, default_hotkeys):
        # --- Multi-instance prevention ---
        self.mutex_name = "Global\\ChocottoTimer_Mutex"
        self.mutex = win32event.CreateMutex(None, False, self.mutex_name)
        if win32api.GetLastError() == winerror.ERROR_ALREADY_EXISTS:
            root_temp = tk.Tk()
            root_temp.withdraw()
            messagebox.showwarning("多重起動", "アプリは既に起動しています。")
            root_temp.destroy()
            sys.exit(0)

        # Pygame mixer initialization
        pygame.mixer.pre_init(44100, -16, 2, 512)
        pygame.mixer.init()
        pygame.mixer.set_num_channels(16)

        self.target_class = target_class
        self.target_title = target_title
        self.icon_config = icon_config
        
        # DXcamの初期化
        self.camera = dxcam.create()
        
        # Load configuration (Includes volume and position)
        self.load_config(default_hotkeys)
        
        self.icon_filenames = list(icon_config.keys())
        self.icon_paths = [resource_path(f, "images") for f in self.icon_filenames]
        
        self.sound_objects = {}
        sound_names = ["timer_start", "reset", "cursor", "timer_select", "counter", "enter", "cancel"]
        for name in sound_names:
            path = resource_path(f"{name}.dat", "sounds")
            if os.path.exists(path):
                try:
                    self.sound_objects[name] = pygame.mixer.Sound(path)
                except Exception as e:
                    print(f"Failed to load {name}: {e}")
        
        # Apply loaded volume
        self.apply_volume_to_mixer()
        
        self.request_queue = queue.Queue()
        
        self.root = tk.Tk()
        self.root.withdraw() 
        
        # --- Static Config ---
        self.max_timers = 8
        self.base_timer_spacing = 12
        self.threshold = 0.9 
        self.origin_x = 8
        self.counter_offset_x = 12
        self.timer_offset_x = 13
        self.cursor_offset_x = 0 
        
        # --- State Variables ---
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

        # Overlay Window setup
        self.overlay = tk.Toplevel(self.root)
        self.overlay.attributes("-topmost", True)
        self.overlay.overrideredirect(True)
        self.overlay.config(bg='black')
        self.overlay.wm_attributes("-transparentcolor", "black")
        
        self.overlay.update() 
        hwnd = win32gui.GetParent(self.overlay.winfo_id())
        ex_style = win32gui.GetWindowLong(hwnd, win32con.GWL_EXSTYLE)
        win32gui.SetWindowLong(hwnd, win32con.GWL_EXSTYLE, 
                               ex_style | win32con.WS_EX_LAYERED | win32con.WS_EX_TRANSPARENT)

        self.canvas = tk.Canvas(self.overlay, width=600, height=1000, bg='black', highlightthickness=0)
        self.canvas.pack()

        self.raw_images = {} 
        self.images = {}     
        self.load_assets()
        
        self.templates = []
        self.reload_templates()

        self.setup_hooks()

        self.tray_icon = None
        self.setup_tray()

        self.update_overlay()
        self.check_icon_loop()
        self.process_queue()

    def load_config(self, default_hotkeys):
        # デフォルト設定
        self.scale = 1.0
        self.origin_y = 114
        self.presets = [300, 600, 1800, 3600]
        self.counter_enabled = False
        self.sound_enabled = True
        self.volume_level = 35
        
        if os.path.exists(CONFIG_FILE):
            try:
                with open(CONFIG_FILE, 'r', encoding='utf-8') as f:
                    saved_data = json.load(f)
                    loaded_hotkeys = saved_data.get("hotkeys", {})
                    self.hotkey_config = {**default_hotkeys, **loaded_hotkeys}
                    self.auto_start_enabled = saved_data.get("auto_start", True)
                    self.hotkey_enabled = saved_data.get("hotkey_enabled", True)
                    self.scale = saved_data.get("scale", 1.0)
                    self.origin_y = saved_data.get("origin_y", 114)
                    self.presets = saved_data.get("presets", [300, 600, 1800, 3600])
                    self.counter_enabled = saved_data.get("counter_enabled", False)
                    self.sound_enabled = saved_data.get("sound_enabled", True)
                    self.volume_level = saved_data.get("volume_level", 35)
                    return
            except:
                pass
        self.hotkey_config = default_hotkeys
        self.auto_start_enabled = True
        self.hotkey_enabled = True

    def save_config(self):
        try:
            data = {
                "hotkeys": self.hotkey_config,
                "auto_start": self.auto_start_enabled,
                "hotkey_enabled": self.hotkey_enabled,
                "scale": self.scale,
                "origin_y": self.origin_y,
                "presets": self.presets,
                "counter_enabled": self.counter_enabled,
                "sound_enabled": self.sound_enabled,
                "volume_level": self.volume_level
            }
            with open(CONFIG_FILE, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=4, ensure_ascii=False)
        except Exception as e:
            print(f"Save Error: {e}")

    def apply_volume_to_mixer(self):
        actual_vol = self.volume_level / 100.0
        actual_vol = max(0.0, min(1.0, actual_vol))
        for sound in self.sound_objects.values():
            sound.set_volume(actual_vol)

    def play_sound(self, sound_type="timer_start"):
        if not self.sound_enabled:
            return
        sound = self.sound_objects.get(sound_type)
        if sound:
            try:
                channel = pygame.mixer.find_channel(True)
                if channel:
                    channel.play(sound)
            except Exception as e:
                print(f"Sound play error: {e}")

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

    def apply_scale(self):
        for name, pil_img in self.raw_images.items():
            w, h = pil_img.size
            new_size = (int(w * self.scale), int(h * self.scale))
            resized = pil_img.resize(new_size, Image.Resampling.NEAREST)
            self.images[name] = ImageTk.PhotoImage(resized)
        self.draw_timer()

    def process_queue(self):
        try:
            while True:
                task = self.request_queue.get_nowait()
                if task.get('type') == 'change_hotkey':
                    self._execute_change_hotkey(task['key_id'])
                elif task.get('type') == 'edit_preset':
                    self._execute_edit_preset(task['index'])
                elif task.get('type') == 'add_preset':
                    self._execute_add_preset()
                elif task.get('type') == 'show_volume_dialog':
                    self._execute_show_volume_dialog()
                self.request_queue.task_done()
        except queue.Empty:
            pass
        self.root.after(100, self.process_queue)

    def _execute_show_volume_dialog(self):
        dialog = tk.Toplevel(self.root)
        dialog.title("音量設定")
        dialog.geometry("300x120")
        dialog.resizable(False, False)
        dialog.attributes("-topmost", True)
        
        sw = dialog.winfo_screenwidth()
        sh = dialog.winfo_screenheight()
        dialog.geometry(f"+{int(sw/2-150)}+{int(sh/2-60)}")

        label = tk.Label(dialog, text=f"音量: {int(self.volume_level)}")
        label.pack(pady=10)

        def on_scale_change(val):
            self.volume_level = float(val)
            label.config(text=f"音量: {int(self.volume_level)}")
            self.apply_volume_to_mixer()

        scale = ttk.Scale(dialog, from_=0, to=100, orient="horizontal", command=on_scale_change)
        scale.set(self.volume_level)
        scale.pack(fill="x", padx=20)

        def on_close():
            self.save_config()
            dialog.destroy()
            self.root.withdraw()

        dialog.protocol("WM_DELETE_WINDOW", on_close)
        btn = tk.Button(dialog, text="閉じる", command=on_close)
        btn.pack(pady=10)
        
        self.root.deiconify()
        self.root.withdraw()

    def reload_templates(self):
        self.templates = []
        for path in self.icon_paths:
            if os.path.exists(path):
                try:
                    with Image.open(path) as img:
                        img_cv = cv2.cvtColor(np.array(img.convert('RGB')), cv2.COLOR_RGB2BGR)
                        self.templates.append(img_cv)
                except:
                    pass

    def setup_hooks(self):
        keyboard.unhook_all()
        mouse.unhook_all()
        
        def on_key_event(e):
            if not self.hotkey_enabled: return
            if e.event_type != 'down': return
            key_name = e.name.lower()
            if key_name == 'enter' or e.scan_code == 28:
                foreground_hwnd = win32gui.GetForegroundWindow()
                if self.target_hwnd and foreground_hwnd == self.target_hwnd:
                    if not self.is_typing_mode:
                        self.is_typing_mode = True
                        self.play_sound("enter")
                        self.overlay.after(0, self.draw_timer)
                return
            if self.is_typing_mode: return
            foreground_hwnd = win32gui.GetForegroundWindow()
            if not (self.target_hwnd and foreground_hwnd == self.target_hwnd): return

            mods = []
            if keyboard.is_pressed('ctrl'): mods.append('ctrl')
            if keyboard.is_pressed('shift'): mods.append('shift')
            if keyboard.is_pressed('alt'): mods.append('alt')
            current_combination = "+".join(mods + [key_name]) if mods else key_name

            mapping = {
                'reset_timer': self.reset_selected_timer,
                'reset_all_timers': self.reset_timer,
                'add_timer': lambda: self.add_timer(self.presets[self.selected_preset_index]),
                'inc_counter1': lambda: self.increment_counter(1),
                'dec_counter1': lambda: self.decrement_counter(1),
                'reset_counter1': lambda: self.reset_specific_counter(1),
                'inc_counter2': lambda: self.increment_counter(2),
                'dec_counter2': lambda: self.decrement_counter(2),
                'reset_counter2': lambda: self.reset_specific_counter(2),
                'prev_preset': self.cycle_preset_prev,
                'next_preset': self.cycle_preset_next,
                'move_cursor': self.move_cursor,
            }
            for action_id, cfg_hotkey in self.hotkey_config.items():
                if cfg_hotkey == current_combination:
                    self.overlay.after(0, mapping[action_id]); break

        def on_mouse_event(e):
            if isinstance(e, mouse.ButtonEvent) and e.event_type == 'down' and e.button == 'left':
                if self.is_typing_mode:
                    foreground_hwnd = win32gui.GetForegroundWindow()
                    if self.target_hwnd and foreground_hwnd == self.target_hwnd:
                        self.is_typing_mode = False; self.overlay.after(0, self.draw_timer)

        keyboard.hook(on_key_event); mouse.hook(on_mouse_event)

    def move_cursor(self):
        valid_indices = [0] if self.is_counting else []
        valid_indices += [i + 1 for i in range(len(self.timers))]
        if not valid_indices: self.selected_cursor_index = 0; self.draw_timer(); return
        try:
            cur = valid_indices.index(self.selected_cursor_index)
            new_idx = valid_indices[(cur + 1) % len(valid_indices)]
            if new_idx != self.selected_cursor_index:
                self.play_sound("cursor")
            self.selected_cursor_index = new_idx
        except ValueError: self.selected_cursor_index = valid_indices[0]
        self.draw_timer()

    def reset_selected_timer(self):
        if self.selected_cursor_index == 0 and self.is_counting:
            self.feather_timer = 0; self.is_counting = False; self.current_icon_index = -1
            self.play_sound("reset")
        else:
            idx = self.selected_cursor_index - 1
            if 0 <= idx < len(self.timers): 
                self.timers.pop(idx)
                self.play_sound("reset")
        self.validate_cursor_position(); self.draw_timer()

    def validate_cursor_position(self):
        v = [0] if self.is_counting else []
        v += [i + 1 for i in range(len(self.timers))]
        if not v: self.selected_cursor_index = 0; return
        if self.selected_cursor_index not in v:
            self.selected_cursor_index = max(v) if self.selected_cursor_index > max(v) else v[0]

    def cycle_preset_next(self):
        if not self.presets: return
        self.play_sound("timer_select")
        self.selected_preset_index = (self.selected_preset_index + 1) % len(self.presets)
        self.show_preset_preview()

    def cycle_preset_prev(self):
        if not self.presets: return
        self.play_sound("timer_select")
        self.selected_preset_index = (self.selected_preset_index - 1) % len(self.presets)
        self.show_preset_preview()

    def show_preset_preview(self):
        self.draw_timer()
        if self.preview_timer_id: self.overlay.after_cancel(self.preview_timer_id)
        self.preview_timer_id = self.overlay.after(2000, self._hide_preview)

    def _hide_preview(self): self.preview_timer_id = None; self.draw_timer()

    def _execute_change_hotkey(self, key_id):
        self.root.deiconify()
        self.root.focus_force()
        new_key = simpledialog.askstring("ホットキー設定", f"'{key_id}' のキー設定を入力してください。\n(空欄でOKを押すと解除されます)\n現在: {self.hotkey_config.get(key_id, '')}", parent=self.root)
        self.root.withdraw()
        if new_key is not None:
            self.hotkey_config[key_id] = new_key.lower().replace(" ", "")
            self.setup_hooks(); self.save_config(); self.refresh_tray_menu()

    def _execute_edit_preset(self, index):
        if index >= len(self.presets): return
        self.root.deiconify()
        new_val = simpledialog.askstring("プリセット編集", f"秒数を入力してください (現在: {self.presets[index]}秒)\n※0を入力すると削除されます", parent=self.root)
        self.root.withdraw()
        if new_val is not None:
            try:
                val = int(new_val)
                if val < 0 or val > 5999:
                    self.root.deiconify()
                    messagebox.showwarning("入力エラー", "0～5999の範囲で入力してください。", parent=self.root)
                    self.root.withdraw()
                else:
                    if val == 0: self.presets.pop(index); self.selected_preset_index = 0
                    else: self.presets[index] = val
                    self.presets.sort(); self.save_config(); self.refresh_tray_menu()
            except ValueError: pass
            
    def _execute_add_preset(self):
        self.root.deiconify()
        new_val = simpledialog.askstring("プリセット追加", "追加する秒数を入力してください:", parent=self.root)
        self.root.withdraw()
        if new_val:
            try:
                val = int(new_val)
                if val < 0 or val > 5999:
                    self.root.deiconify()
                    messagebox.showwarning("入力エラー", "0～5999の範囲で入力してください。", parent=self.root)
                    self.root.withdraw()
                elif val > 0:
                    self.presets.append(val); self.presets.sort()
                    self.save_config(); self.refresh_tray_menu()
            except ValueError: pass

    def refresh_tray_menu(self):
        if self.tray_icon: self.tray_icon.menu = self.create_tray_menu()
              
    def create_tray_menu(self):
        def get_hk_label(key_id, base_text):
            k = self.hotkey_config.get(key_id, "").upper()
            return f"{base_text} [{k if k else '未設定'}]"

        hotkey_settings_items = [
            item(lambda _: get_hk_label('add_timer', 'タイマースタート'), lambda: self.request_change_hotkey('add_timer')),
            item(lambda _: get_hk_label('reset_timer', 'タイマーリセット'), lambda: self.request_change_hotkey('reset_timer')),
            item(lambda _: get_hk_label('reset_all_timers', '全タイマーリセット'), lambda: self.request_change_hotkey('reset_all_timers')),
            item(lambda _: get_hk_label('move_cursor', 'リセットカーソル移動'), lambda: self.request_change_hotkey('move_cursor')),
            pystray.Menu.SEPARATOR,
            item(lambda _: get_hk_label('prev_preset', '時間設定（戻る）'), lambda: self.request_change_hotkey('prev_preset')),
            item(lambda _: get_hk_label('next_preset', '時間設定（進む）'), lambda: self.request_change_hotkey('next_preset')),
            pystray.Menu.SEPARATOR,
            item(lambda _: get_hk_label('inc_counter1', 'カウンター1 +1'), lambda: self.request_change_hotkey('inc_counter1')),
            item(lambda _: get_hk_label('dec_counter1', 'カウンター1 -1'), lambda: self.request_change_hotkey('dec_counter1')),
            item(lambda _: get_hk_label('reset_counter1', 'カウンター1 リセット'), lambda: self.request_change_hotkey('reset_counter1')),
            pystray.Menu.SEPARATOR,
            item(lambda _: get_hk_label('inc_counter2', 'カウンター2 +1'), lambda: self.request_change_hotkey('inc_counter2')),
            item(lambda _: get_hk_label('dec_counter2', 'カウンター2 -1'), lambda: self.request_change_hotkey('dec_counter2')),
            item(lambda _: get_hk_label('reset_counter2', 'カウンター2 リセット'), lambda: self.request_change_hotkey('reset_counter2')),
        ]
        preset_items = [item(f"{p//60}分{p%60}秒" if p%60 else f"{p//60}分", (lambda idx: lambda: self.request_edit_preset(idx))(i)) for i, p in enumerate(self.presets)]
        preset_items += [pystray.Menu.SEPARATOR, item("新規追加...", self.request_add_preset)]

        return pystray.Menu(
            item('ショートカットキー設定', pystray.Menu(*hotkey_settings_items)),
            item('タイマープリセット編集', pystray.Menu(*preset_items)),
            pystray.Menu.SEPARATOR,
            item('表示サイズ', pystray.Menu(
                item('標準 (1.0x)', lambda: self.set_scale(1.0), checked=lambda _: self.scale == 1.0, radio=True),
                item('大 (2.0x)', lambda: self.set_scale(2.0), checked=lambda _: self.scale == 2.0, radio=True),
            )),
            item('表示位置', pystray.Menu(
                item('標準 (上)', lambda: self.set_origin_y(114), checked=lambda _: self.origin_y == 114, radio=True),
                item('やや下', lambda: self.set_origin_y(150), checked=lambda _: self.origin_y == 150, radio=True),
            )),
            pystray.Menu.SEPARATOR,
            item('ショートカットキー有効', self.toggle_hotkeys, checked=lambda _: self.hotkey_enabled),
            item('タイマー自動スタート有効', self.toggle_auto_start, checked=lambda _: self.auto_start_enabled),
            item('カウンターを表示', self.toggle_counter, checked=lambda _: self.counter_enabled),
            pystray.Menu.SEPARATOR,
            item('効果音を再生', self.toggle_sound, checked=lambda _: self.sound_enabled),
            item('音量設定...', lambda: self.request_queue.put({'type': 'show_volume_dialog'})),
            pystray.Menu.SEPARATOR,
            item('終了', self.quit_app)
        )

    def setup_tray(self):
        try:
            icon_img = Image.open(resource_path("choco_timer.ico", "images"))
            self.tray_icon = pystray.Icon("choco_timer", icon_img, "チョコットタイマー", menu=self.create_tray_menu())
            threading.Thread(target=self.tray_icon.run, daemon=True).start()
        except: pass

    def toggle_sound(self, icon, item):
        self.sound_enabled = not self.sound_enabled; self.save_config(); self.refresh_tray_menu()

    def toggle_counter(self, icon, item):
        self.counter_enabled = not self.counter_enabled; self.save_config(); self.draw_timer(); self.refresh_tray_menu()

    def toggle_hotkeys(self, icon, item):
        self.hotkey_enabled = not self.hotkey_enabled; self.setup_hooks(); self.save_config(); self.refresh_tray_menu()

    def toggle_auto_start(self, icon, item):
        self.auto_start_enabled = not self.auto_start_enabled; self.save_config(); self.refresh_tray_menu()

    def quit_app(self, icon=None, item=None):
        if self.tray_icon: self.tray_icon.stop()
        pygame.mixer.quit(); self.root.after(0, self.root.destroy)

    def load_assets(self):
        try:
            asset_names = ['clock','colon','counter','slash','keyboard','left','right','feather','cursor']
            for name in asset_names: self.raw_images[name] = Image.open(resource_path(f"{name}.dat", "images"))
            for i in range(10): self.raw_images[str(i)] = Image.open(resource_path(f"{i}.dat", "images"))
            self.apply_scale()
        except: pass

    def increment_counter(self, num):
        if not self.counter_enabled: return
        self.play_sound("counter")
        if num == 1: self.counter1 = (self.counter1 + 1) % 10000
        elif num == 2: self.counter2 = (self.counter2 + 1) % 10000
        self.draw_timer()

    def decrement_counter(self, num):
        if not self.counter_enabled: return
        self.play_sound("counter")
        if num == 1: self.counter1 = max(0, self.counter1 - 1)
        elif num == 2: self.counter2 = max(0, self.counter2 - 1)
        self.draw_timer()

    def reset_specific_counter(self, num):
        if not self.counter_enabled: return
        self.play_sound("reset")
        if num == 1: self.counter1 = 0
        elif num == 2: self.counter2 = 0
        self.draw_timer()

    def draw_timer(self):
        self.canvas.delete("all")
        s, bx, by = self.scale, self.origin_x, self.origin_y
        if self.is_typing_mode and 'keyboard' in self.images: self.canvas.create_image(bx, by, image=self.images['keyboard'], anchor="nw")
        draw_y = by + 1 
        if self.preview_timer_id and self.presets:
            self._render_select_time_images(self.presets[self.selected_preset_index], bx + (13 * s), draw_y)
        draw_y += self.base_timer_spacing * s
        if self.counter_enabled:
            self._render_counter_images(self.counter1, self.counter2, bx + (self.counter_offset_x * s), draw_y)
            draw_y += self.base_timer_spacing * s
        if self.is_counting:
            if self.selected_cursor_index == 0: self.canvas.create_image(bx + (self.cursor_offset_x * s), draw_y - 1 * s, image=self.images['cursor'], anchor="nw")
            self._render_feather_time_images(self.feather_timer, bx + (self.timer_offset_x * s), draw_y)
            draw_y += self.base_timer_spacing * s
        for i, t in enumerate(self.timers):
            if self.selected_cursor_index == (i + 1): self.canvas.create_image(bx + (self.cursor_offset_x * s), draw_y - 1 * s, image=self.images['cursor'], anchor="nw")
            self._render_time_images(t['seconds'], bx + (self.timer_offset_x * s), draw_y); draw_y += self.base_timer_spacing * s

    def _render_feather_time_images(self, total_seconds, x, y):
        s = self.scale; mins, secs = divmod(total_seconds, 60); m1, m2 = divmod(mins, 10); s1, s2 = divmod(secs, 10)
        self.canvas.create_image(x - 1*s, y - 1*s, image=self.images['feather'], anchor="nw")
        for off, img in zip([11, 18, 25, 32, 39], [str(m1), str(m2), 'colon', str(s1), str(s2)]):
            self.canvas.create_image(x + off*s, y - 1*s, image=self.images[img], anchor="nw")

    def _render_select_time_images(self, total_seconds, x, y):
        s = self.scale; mins, secs = divmod(total_seconds, 60); m1, m2 = divmod(mins, 10); s1, s2 = divmod(secs, 10)
        self.canvas.create_image(x + 2, y - 1*s, image=self.images['left'], anchor="nw")
        for off, img in zip([11, 18, 25, 32, 39, 48], [str(m1), str(m2), 'colon', str(s1), str(s2), 'right']):
            self.canvas.create_image(x + off*s, y - 1*s, image=self.images[img], anchor="nw")

    def _render_time_images(self, total_seconds, x, y):
        s = self.scale; mins, secs = divmod(total_seconds, 60); m1, m2 = divmod(mins, 10); s1, s2 = divmod(secs, 10)
        self.canvas.create_image(x, y, image=self.images['clock'], anchor="nw")
        for off, img in zip([11, 18, 25, 32, 39], [str(m1), str(m2), 'colon', str(s1), str(s2)]):
            self.canvas.create_image(x + off*s, y - 1*s, image=self.images[img], anchor="nw")

    def _render_counter_images(self, c1, c2, x, y):
        s = self.scale; self.canvas.create_image(x, y, image=self.images['counter'], anchor="nw")
        for i, digit in enumerate(f"{c1:04d}"): self.canvas.create_image(x + (12 + i*7)*s, y - 1*s, image=self.images[digit], anchor="nw")
        self.canvas.create_image(x + 42*s, y - 1*s, image=self.images['slash'], anchor="nw")
        for i, digit in enumerate(f"{c2:04d}"): self.canvas.create_image(x + (51 + i*7)*s, y - 1*s, image=self.images[digit], anchor="nw")

    def find_target_window(self):
        hwnd = win32gui.FindWindow(self.target_class, None)
        return hwnd if hwnd else win32gui.FindWindow(None, self.target_title)

    def update_overlay(self):
        try:
            self.target_hwnd = self.find_target_window()
            if self.target_hwnd and win32gui.IsWindow(self.target_hwnd):
                self.not_found_start_time = None
                p = win32gui.GetWindowPlacement(self.target_hwnd)
                if p[1] != win32con.SW_SHOWMINIMIZED and win32gui.GetForegroundWindow() == self.target_hwnd:
                    r = win32gui.GetWindowRect(self.target_hwnd); w, h = r[2]-r[0], r[3]-r[1]
                    self.canvas.config(width=w, height=h); self.overlay.geometry(f"{w}x{h}+{r[0]}+{r[1]}")
                    self.draw_timer(); self.overlay.deiconify()
                else: 
                    self.overlay.withdraw()
                    if self.is_typing_mode: self.is_typing_mode = False
            else:
                if self.not_found_start_time is None: self.not_found_start_time = time.time()
                if time.time() - self.not_found_start_time > 300: self.quit_app(); return
                self.overlay.withdraw()
        except: pass
        self.root.after(100, self.update_overlay)

    def check_icon_loop(self):
        if self.auto_start_enabled and self.target_hwnd and self.templates:
            try:
                r = win32gui.GetWindowRect(self.target_hwnd)
                left, top, right, bottom = r[0]+20, r[1]+101, r[0]+220, r[1]+111
                
                # DXcamを使用して指定領域をキャプチャ
                frame = self.camera.grab(region=(left, top, right, bottom))
                
                if frame is not None:
                    # dxcamはデフォルトでRGB numpy arrayを返すため、そのままBGRに変換
                    frame_bgr = cv2.cvtColor(frame, cv2.COLOR_RGB2BGR)
                    for idx, template in enumerate(self.templates):
                        res = cv2.matchTemplate(frame_bgr, template, cv2.TM_CCOEFF_NORMED)
                        if cv2.minMaxLoc(res)[1] >= self.threshold:
                            if self.current_icon_index != idx:
                                self.current_icon_index = idx
                                self.start_countdown(self.icon_config.get(self.icon_filenames[idx], 300))
                            break 
            except: pass
        self.root.after(500, self.check_icon_loop)

    def start_countdown(self, seconds):
        self.play_sound("timer_start"); self.target_time = time.time() + seconds
        self.feather_timer = int(seconds); self.is_counting = True; self.selected_cursor_index = 0
        if not self.tick_id: self.tick_timer()

    def add_timer(self, seconds):
        if len(self.timers) >= self.max_timers: self.play_sound("cancel"); return
        self.play_sound("timer_start"); self.timers.append({'target_time': time.time() + seconds, 'seconds': int(seconds)})
        if not self.tick_id: self.tick_timer()

    def reset_timer(self):
        if self.is_counting or self.timers:
            self.play_sound("reset"); self.feather_timer = 0; self.is_counting = False; self.timers = []; self.current_icon_index = -1
            self.selected_cursor_index = 0
            if self.tick_id: self.overlay.after_cancel(self.tick_id); self.tick_id = None
            self.draw_timer()

    def tick_timer(self):
        now, any_running = time.time(), False
        if self.is_counting:
            rem = int(self.target_time - now)
            if rem >= 0: self.feather_timer = rem; any_running = True
            else: self.feather_timer = 0; self.is_counting = False; self.current_icon_index = -1
        active = []
        for t in self.timers:
            rem = int(t['target_time'] - now)
            if rem >= 0: t['seconds'] = rem; active.append(t); any_running = True
        self.timers = active; self.validate_cursor_position()
        if any_running: self.tick_id = self.overlay.after(100, self.tick_timer)
        else: self.tick_id = None
        self.draw_timer()

    def request_change_hotkey(self, key_id): self.request_queue.put({'type': 'change_hotkey', 'key_id': key_id})
    def request_edit_preset(self, index): self.request_queue.put({'type': 'edit_preset', 'index': index})
    def request_add_preset(self): self.request_queue.put({'type': 'add_preset'})
    def run(self): self.root.mainloop()

if __name__ == "__main__":
    default_hotkeys = {
        'add_timer': 't', 'reset_timer': 'r', 'reset_all_timers': 'ctrl+r',
        'move_cursor': 'tab', 'prev_preset': ',', 'next_preset': '.',
        'inc_counter1': 'z', 'dec_counter1': 'shift+z', 'reset_counter1': 'ctrl+z',
        'inc_counter2': 'x', 'dec_counter2': 'shift+x', 'reset_counter2': 'ctrl+x'
    }
    app = OverlayApp("xtWin32WindowBase", "チョコットランド", 
        {"bell.dat": 297, "juda.dat": 9, "eru.dat": 300, "retro.dat": 300, "shira.dat": 300, "fiss.dat": 300, "bene.dat": 300, "renamana.dat": 300, "riarie.dat": 300, "roya.dat": 300, "code.dat": 90},
        default_hotkeys
    )
    app.run()