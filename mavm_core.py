# -*- coding: utf-8 -*-
"""
MAVM  -  MAV Mobil  (MAVS altyapısı)  |  Android / Kivy sürümü
==============================================================
Masaüstü MAV uygulamasının Android karşılığı. Aynı MAVS algılama motoru
(imza + sezgisel analiz), kalkan, karantina ve giriş sistemi; arayüz Kivy ile.

Dosyalar:
    mavm_core.py   -> uygulamanın tamamı (bu dosya)
    main.py        -> Android'in aradığı giriş noktası (mavm_core'u çalıştırır)
    buildozer.spec -> APK yapılandırması

PC'de denemek için (isteğe bağlı):
    pip install kivy
    python main.py

APK oluşturma (Linux / WSL2 Ubuntu / Google Colab):
    sudo apt install -y git zip unzip openjdk-17-jdk python3-pip autoconf libtool \
         pkg-config zlib1g-dev libncurses-dev cmake libffi-dev libssl-dev
    pip install buildozer "cython<3"
    buildozer android debug
    # Çıktı: bin/ klasöründeki *.apk  (adını mavm_core.apk yapabilirsiniz)

Bilgisayarınız Windows ise en kolayı: dosyaları bir GitHub deposuna yükleyin;
.github/workflows/build-apk.yml APK'yı sizin için derler (Actions > Artifacts).

Önemli notlar:
  * Android 11+ üzerinde tüm dosyaları taramak için "Tüm dosyalara erişim" izni gerekir;
    uygulama ilk girişte sizi ilgili ayar ekranına yönlendirir.
  * Gerçek zamanlı kalkan uygulama çalıştığı sürece (arka plana alınsa bile Android
    izin verdiği ölçüde) izleme yapar. Uygulama tamamen kapatılırsa durur.
  * Motor bir prototiptir: EICAR/MAV test imzası, bilinen-kötü SHA-256 ve sezgisel
    kurallarla çalışır; ticari mobil güvenlik ürünlerinin yerini tutmaz.
"""
from __future__ import annotations

import os

os.environ.setdefault("KIVY_NO_ARGS", "1")

import ctypes  # noqa: F401
import datetime
import hashlib
import hmac
import json
import platform as _platform
import queue
import random
import re
import secrets
import shutil
import tempfile
import threading
import time
import uuid
from collections import deque
from pathlib import Path

try:
    import psutil

    HAS_PSUTIL = True
except Exception:  # pragma: no cover
    psutil = None
    HAS_PSUTIL = False

# --------------------------------------------------------------------------
# SABİTLER
# --------------------------------------------------------------------------
APP_NAME = "MAV"
APP_VERSION = "1.0.0"
ENGINE_NAME = "MAVS Engine 1.0 (mobil)"
IS_NT = os.name == "nt"
IS_ANDROID = "ANDROID_ARGUMENT" in os.environ or "ANDROID_BOOTLOGO" in os.environ


def _home() -> Path:
    try:
        return Path.home()
    except Exception:
        return Path(tempfile.gettempdir())


DATA_DIR = _home() / ".mavm"
USERS_FILE = DATA_DIR / "users.json"
QUAR_DIR = DATA_DIR / "quarantine"
QUAR_INDEX = DATA_DIR / "quarantine.json"
TEST_DIR = DATA_DIR / "test_zone"


def init_paths(base) -> None:
    """Uygulama veri klasörünü (Android'de uygulamaya özel dizin) ayarlar."""
    global DATA_DIR, USERS_FILE, QUAR_DIR, QUAR_INDEX, TEST_DIR
    DATA_DIR = Path(base)
    USERS_FILE = DATA_DIR / "users.json"
    QUAR_DIR = DATA_DIR / "quarantine"
    QUAR_INDEX = DATA_DIR / "quarantine.json"
    TEST_DIR = DATA_DIR / "test_zone"
    DATA_DIR.mkdir(parents=True, exist_ok=True)


C = dict(
    bg="#0A0A0A",
    navy="#0A1128",
    card="#0D1428",
    card2="#1E1E2F",
    header="#05080F",
    border="#1B2A4A",
    cyan="#00D2FF",
    cyan_dim="#0A6E8F",
    text="#E6F1FF",
    muted="#7A8BA8",
    danger="#FF3B4E",
    warn="#FF9F1A",
    ok="#2ED573",
    logo_blue="#0A3D62",
    violet="#7B8CFF",
)


def fmt_size(n: float) -> str:
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or unit == "TB":
            return f"{n:.0f} {unit}" if unit == "B" else f"{n:.1f} {unit}"
        n /= 1024.0
    return f"{n:.1f} TB"


def fmt_dur(sec: float) -> str:
    sec = int(sec)
    return f"{sec // 60:02d}:{sec % 60:02d}"


def short_path(p: str, n: int = 56) -> str:
    return p if len(p) <= n else "…" + p[-(n - 1):]


# --------------------------------------------------------------------------
# KULLANICI YÖNETİMİ  (PBKDF2-HMAC-SHA256 + tuz; düz metin şifre saklanmaz)
# --------------------------------------------------------------------------
class AuthManager:
    ITER = 200_000

    def __init__(self):
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        self.db = self._load()

    def _load(self) -> dict:
        try:
            with open(USERS_FILE, "r", encoding="utf-8") as f:
                d = json.load(f)
            if isinstance(d, dict) and isinstance(d.get("users"), dict):
                return d
        except (OSError, ValueError):
            pass
        return {"version": 1, "users": {}}

    def _save(self) -> None:
        tmp = USERS_FILE.with_suffix(".tmp")
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(self.db, f, indent=2, ensure_ascii=False)
        os.replace(tmp, USERS_FILE)
        if not IS_NT:
            try:
                os.chmod(USERS_FILE, 0o600)
            except OSError:
                pass

    @staticmethod
    def _hash(pw: str, salt: bytes, it: int) -> bytes:
        return hashlib.pbkdf2_hmac("sha256", pw.encode("utf-8"), salt, it)

    def register(self, user: str, pw: str):
        if not re.fullmatch(r"[\w.\-]{3,24}", user or ""):
            return False, "Kullanıcı adı 3-24 karakter olmalı (harf, rakam, _ . -)."
        if len(pw or "") < 6:
            return False, "Şifre en az 6 karakter olmalı."
        key = user.lower()
        if key in self.db["users"]:
            return False, "Bu kullanıcı adı zaten kayıtlı."
        salt = secrets.token_bytes(16)
        self.db["users"][key] = {
            "display": user,
            "salt": salt.hex(),
            "iter": self.ITER,
            "hash": self._hash(pw, salt, self.ITER).hex(),
            "created": datetime.datetime.now().isoformat(timespec="seconds"),
        }
        try:
            self._save()
        except OSError as e:
            self.db["users"].pop(key, None)
            return False, f"Kayıt dosyasına yazılamadı: {e}"
        return True, "Kayıt başarılı."

    def login(self, user: str, pw: str):
        rec = self.db["users"].get((user or "").lower())
        if not rec:
            return False, "Kullanıcı adı veya şifre hatalı.", None
        try:
            calc = self._hash(pw, bytes.fromhex(rec["salt"]), int(rec["iter"]))
            ok = hmac.compare_digest(calc.hex(), rec["hash"])
        except (ValueError, KeyError):
            ok = False
        if not ok:
            return False, "Kullanıcı adı veya şifre hatalı.", None
        return True, "Giriş başarılı.", rec.get("display", user)


# --------------------------------------------------------------------------
# ALGILAMA MOTORU
# --------------------------------------------------------------------------
# Test imzaları parçalı yazılır; böylece bu dosya kendi kendini veya başka bir
# antivirüsü tetiklemez.
EICAR = ("X5O!P%@AP[4\\PZX54(P^)7CC)7}$" "EICAR-STANDARD-ANTIVIRUS-TEST-FILE!" "$H+H*").encode()
MAV_TEST = (b"MAV-TEST-" b"THREAT-SIGNATURE-" b"7F3A-HARMLESS")

KNOWN_BAD_HASHES = {
    "275a021bbfb6489e54d471899f7db9d1663fc695ec2fe2a2c4538aabf651fd0f": "EICAR-Test-File",
}

# (kalıp, açıklama, ağırlık) - kalıplar parçalı yazıldı, küçük harfle eşleşir
HEUR = [
    (b"-encodedcom" b"mand", "Kodlanmış PowerShell komutu", 2),
    (b"frombase64" b"string(", "Base64 çözümleme", 1),
    (b"invoke-exp" b"ression", "Dinamik kod çalıştırma", 2),
    (b"downloadstr" b"ing(", "Uzaktan içerik indirme", 2),
    (b"downloadfi" b"le(", "Uzaktan dosya indirme", 2),
    (b"vssadmin" b" delete" b" shadows", "Gölge kopya silme (fidye davranışı)", 5),
    (b"wscript.sh" b"ell", "WScript.Shell kullanımı", 1),
    (b"-windowstyle hid" b"den", "Gizli pencere çalıştırma", 2),
    (b"-executionpolicy by" b"pass", "Yürütme ilkesi atlatma", 2),
    (b"mimi" b"katz", "Kimlik bilgisi hırsızlığı aracı", 5),
    (b"certutil -url" b"cache", "LOLBin ile dosya indirme", 3),
    (b"regsvr32 /s /n /u /i:", "Regsvr32 uzaktan betik çağırma", 4),
    (b"schtasks /cre" b"ate", "Zamanlanmış görev ile kalıcılık", 1),
]

SCRIPT_EXT = {".ps1", ".psm1", ".vbs", ".vbe", ".js", ".jse", ".bat", ".cmd",
              ".hta", ".wsf", ".sh"}
DISGUISE_EXT = {".jpg", ".jpeg", ".png", ".gif", ".bmp", ".pdf", ".doc", ".docx",
                ".xls", ".xlsx", ".ppt", ".pptx", ".txt", ".mp3", ".mp4", ".rtf"}
DOUBLE_EXT = re.compile(
    r"\.(pdf|docx?|xlsx?|pptx?|jpe?g|png|gif|txt|mp3|mp4|zip|rar)"
    r"\.(exe|scr|bat|cmd|com|pif|vbs|js|jar|msi|lnk)$")

MAX_FULL_READ = 2 * 1024 * 1024
HEAD_READ = 64 * 1024
SKIP_NAMES_NT = {"$recycle.bin", "system volume information", "winsxs",
                 "$windows.~bt", "$windows.~ws"}
SKIP_PATHS_POSIX = {"/proc", "/sys", "/dev", "/run", "/snap"}


class Detection:
    __slots__ = ("name", "kind", "severity", "detail")

    def __init__(self, name, kind, severity, detail=""):
        self.name, self.kind, self.severity, self.detail = name, kind, severity, detail


def analyze_file(path: str):
    """Dönüş: (Detection | None, dosya_boyutu, okunabildi_mi, sha256)"""
    try:
        st = os.stat(path)
    except OSError:
        return None, 0, False, ""
    size = st.st_size
    name = os.path.basename(path)
    low = name.lower()
    ext = os.path.splitext(low)[1]

    if "\u202e" in name:
        return Detection("Heur.RLO.FilenameSpoof", "heuristic", "Şüpheli",
                         "Dosya adında sağdan-sola geçersiz kılma karakteri"), size, True, ""
    if DOUBLE_EXT.search(low):
        return Detection("Heur.DoubleExtension", "heuristic", "Şüpheli",
                         "Çift uzantı hilesi"), size, True, ""
    if size == 0:
        return None, 0, True, ""

    try:
        with open(path, "rb") as f:
            data = f.read() if size <= MAX_FULL_READ else f.read(HEAD_READ)
    except (OSError, PermissionError):
        return None, size, False, ""

    full = size <= MAX_FULL_READ
    sha = hashlib.sha256(data).hexdigest() if full else ""

    if full:
        if EICAR in data:
            return Detection("EICAR-Test-File", "signature", "Tehdit",
                             "EICAR standart test imzası"), size, True, sha
        if MAV_TEST in data:
            return Detection("MAV.Test.Threat", "signature", "Tehdit",
                             "MAV test imzası (zararsız)"), size, True, sha
        if sha in KNOWN_BAD_HASHES:
            return Detection(KNOWN_BAD_HASHES[sha], "signature", "Tehdit",
                             "Bilinen kötü SHA-256"), size, True, sha

    if data[:2] == b"MZ" and ext in DISGUISE_EXT:
        return Detection("Heur.Disguised.Executable", "heuristic", "Şüpheli",
                         f"{ext} uzantılı dosya yürütülebilir (MZ) başlığı taşıyor"), size, True, sha

    if full and ext in SCRIPT_EXT:
        lowdata = data.lower()
        hits = [(n, w) for p, n, w in HEUR if p in lowdata]
        score = sum(w for _, w in hits)
        if score >= 3:
            hits.sort(key=lambda x: -x[1])
            why = ", ".join(n for n, _ in hits[:3])
            sev = "Tehdit" if score >= 5 else "Şüpheli"
            return Detection("Heur.Script.Malicious", "heuristic", sev,
                             f"Skor {score}: {why}"), size, True, sha
    return None, size, True, sha


def make_record(path: str, det: Detection, size: int, sha: str, source: str) -> dict:
    return {
        "path": path, "name": os.path.basename(path), "threat": det.name,
        "kind": det.kind, "severity": det.severity, "detail": det.detail,
        "sha256": sha, "size": size, "source": source,
        "time": datetime.datetime.now().strftime("%d.%m.%Y %H:%M:%S"),
    }


def _skip_dir(full: str, full_scan: bool = True) -> bool:
    ap = os.path.abspath(full)
    if ap.startswith(str(QUAR_DIR)):
        return True
    if IS_NT:
        return os.path.basename(ap).lower() in SKIP_NAMES_NT
    return ap in SKIP_PATHS_POSIX


class ScanJob(threading.Thread):
    """Arka plan tarama iş parçacığı. Olaylar emit(tuple) ile kuyruğa gider."""

    def __init__(self, mode: str, roots: list, emit, stop_evt: threading.Event):
        super().__init__(daemon=True)
        self.mode, self.roots, self.emit, self.stop = mode, roots, emit, stop_evt
        self.st = dict(scanned=0, threats=0, skipped=0, bytes=0)
        self.t0 = 0.0
        self._last_emit = 0.0
        self._last_log = 0.0
        self.delay = 0.0

    # --- yardımcılar
    def _progress(self, frac, current, force=False):
        now = time.time()
        if not force and now - self._last_emit < 0.1:
            return
        self._last_emit = now
        d = dict(self.st)
        d.update(frac=frac, current=current, elapsed=now - self.t0)
        self.emit(("progress", d))

    def _scan_one(self, path):
        det, size, ok, sha = analyze_file(path)
        self.st["scanned"] += 1
        self.st["bytes"] += size
        if not ok:
            self.st["skipped"] += 1
        now = time.time()
        if now - self._last_log > 0.12 or self.delay:
            self._last_log = now
            self.emit(("log", "scan", f"[TARA] {short_path(path, 90)}"))
        if det:
            self.st["threats"] += 1
            rec = make_record(path, det, size, sha, self.mode)
            tag = "TEHDİT" if det.severity == "Tehdit" else "ŞÜPHELİ"
            self.emit(("log", "threat" if det.severity == "Tehdit" else "warn",
                       f"[{tag}] {det.name} -> {short_path(path, 80)}  ({det.detail})"))
            self.emit(("scan_threat", rec))
        if self.delay:
            time.sleep(self.delay)
        return size

    def _walk(self, root):
        if os.path.isfile(root):
            yield root
            return
        for dpath, dn, fn in os.walk(root, onerror=lambda e: None):
            dn[:] = [d for d in dn if not _skip_dir(os.path.join(dpath, d))]
            for f in fn:
                yield os.path.join(dpath, f)

    # --- ana akış
    def run(self):
        self.t0 = time.time()
        try:
            if self.mode == "full":
                self._run_stream()
            else:
                self._run_listed()
        except Exception as ex:  # pragma: no cover
            self.emit(("log", "warn", f"[HATA] Tarama hatası: {ex}"))
        finally:
            d = dict(self.st)
            d.update(stopped=self.stop.is_set(), elapsed=time.time() - self.t0)
            self.emit(("scan_done", d))

    def _run_listed(self):
        self.emit(("phase", "listing"))
        self.emit(("log", "sys", "[SİSTEM] Dosyalar listeleniyor..."))
        files = []
        for root in self.roots:
            for p in self._walk(root):
                if self.stop.is_set():
                    return
                files.append(p)
                if len(files) % 500 == 0:
                    self._progress(0.0, f"Listeleniyor... {len(files)} dosya", force=False)
        total = len(files)
        self.emit(("phase", "scanning"))
        self.emit(("log", "sys", f"[SİSTEM] {total} dosya bulundu. Analiz başlıyor."))
        if total == 0:
            return
        self.delay = 0.012 if total <= 400 else 0.0
        for i, p in enumerate(files, 1):
            if self.stop.is_set():
                return
            self._scan_one(p)
            self._progress(i / total, p)
        self._progress(1.0, "Tamamlandı", force=True)

    def _run_stream(self):
        total_est = 0
        for r in self.roots:
            try:
                total_est += shutil.disk_usage(r).used
            except OSError:
                pass
        total_est = max(total_est, 1)
        self.emit(("phase", "scanning"))
        self.emit(("log", "sys",
                   f"[SİSTEM] Tam tarama: {', '.join(self.roots)}  (tahmini ilerleme disk kullanımına göre)"))
        for root in self.roots:
            for p in self._walk(root):
                if self.stop.is_set():
                    return
                self._scan_one(p)
                self._progress(min(0.99, self.st["bytes"] / total_est), p)
        self._progress(1.0, "Tamamlandı", force=True)


class Shield(threading.Thread):
    """Gerçek zamanlı koruma: klasörü yoklayarak yeni/değişen dosyaları tarar."""
    IGNORE_EXT = {".crdownload", ".part", ".tmp", ".download", ".partial"}
    MAX_DEPTH = 3
    MAX_ENTRIES = 50_000

    def __init__(self, folder: str, emit, interval: float = 2.0):
        super().__init__(daemon=True)
        self.folder, self.emit, self.interval = folder, emit, interval
        self.stop_evt = threading.Event()

    def _snapshot(self) -> dict:
        snap = {}
        base = self.folder.rstrip("\\/").count(os.sep)
        for dpath, dn, fn in os.walk(self.folder, onerror=lambda e: None):
            if dpath.count(os.sep) - base >= self.MAX_DEPTH:
                dn[:] = []
            dn[:] = [d for d in dn if not _skip_dir(os.path.join(dpath, d))]
            for f in fn:
                p = os.path.join(dpath, f)
                try:
                    st = os.stat(p)
                except OSError:
                    continue
                snap[p] = (st.st_mtime, st.st_size)
                if len(snap) > self.MAX_ENTRIES:
                    return snap
        return snap

    def _check(self, path: str):
        self.emit(("log", "shield", f"[KALKAN] Yeni/değişen dosya: {short_path(path, 80)}"))
        det, size, ok, sha = analyze_file(path)
        self.emit(("shield_scanned",))
        if det:
            tag = "TEHDİT" if det.severity == "Tehdit" else "ŞÜPHELİ"
            self.emit(("log", "threat" if det.severity == "Tehdit" else "warn",
                       f"[{tag}] {det.name} -> {os.path.basename(path)}  ({det.detail})"))
            self.emit(("shield_threat", make_record(path, det, size, sha, "Gerçek Zamanlı")))
        else:
            self.emit(("log", "ok", f"[KALKAN] Temiz: {os.path.basename(path)}"))

    def run(self):
        try:
            prev = self._snapshot()
        except Exception:
            prev = {}
        self.emit(("log", "shield",
                   f"[KALKAN] Gerçek zamanlı koruma aktif -> {short_path(self.folder, 70)}"))
        while not self.stop_evt.wait(self.interval):
            try:
                cur = self._snapshot()
            except Exception:
                continue
            now = time.time()
            for p, sig in cur.items():
                if prev.get(p) == sig:
                    continue
                if os.path.splitext(p)[1].lower() in self.IGNORE_EXT:
                    continue
                if now - sig[0] < 1.5:  # hâlâ yazılıyor olabilir
                    continue
                prev[p] = sig
                self._check(p)
            for p in [k for k in prev if k not in cur]:
                del prev[p]
        self.emit(("log", "warn", "[KALKAN] Gerçek zamanlı koruma durduruldu."))


# --------------------------------------------------------------------------
# KARANTİNA
# --------------------------------------------------------------------------
class Quarantine:
    def __init__(self):
        QUAR_DIR.mkdir(parents=True, exist_ok=True)
        self.lock = threading.Lock()
        self.items = self._load()

    def _load(self) -> list:
        try:
            with open(QUAR_INDEX, "r", encoding="utf-8") as f:
                d = json.load(f)
            return d if isinstance(d, list) else []
        except (OSError, ValueError):
            return []

    def _save(self):
        tmp = QUAR_INDEX.with_suffix(".tmp")
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(self.items, f, indent=2, ensure_ascii=False)
        os.replace(tmp, QUAR_INDEX)

    def add(self, rec: dict):
        src, name = rec["path"], rec["name"]
        if not os.path.isfile(src):
            return False, f"Dosya bulunamadı: {name}"
        qid = uuid.uuid4().hex
        dst = QUAR_DIR / f"{qid}.mavq"
        try:
            shutil.move(src, str(dst))
        except (OSError, shutil.Error) as e:
            return False, f"Karantinaya alınamadı ({name}): {e}"
        with self.lock:
            self.items.append({
                "id": qid, "path": src, "name": name, "threat": rec["threat"],
                "severity": rec["severity"], "size": rec["size"],
                "sha256": rec.get("sha256", ""), "time": rec["time"],
            })
            self._save()
        return True, f"Karantinaya alındı: {name} -> {rec['threat']}"

    def _find(self, qid):
        for it in self.items:
            if it["id"] == qid:
                return it
        return None

    def restore(self, qid: str):
        with self.lock:
            it = self._find(qid)
            if not it:
                return False, "Kayıt bulunamadı."
            src = QUAR_DIR / f"{qid}.mavq"
            dest = Path(it["path"])
            try:
                dest.parent.mkdir(parents=True, exist_ok=True)
                if dest.exists():
                    dest = dest.with_name(f"{dest.stem} (geri yüklendi){dest.suffix}")
                shutil.move(str(src), str(dest))
            except (OSError, shutil.Error) as e:
                return False, f"Geri yüklenemedi: {e}"
            self.items.remove(it)
            self._save()
            return True, f"Geri yüklendi: {dest}"

    def delete(self, qid: str):
        with self.lock:
            it = self._find(qid)
            if not it:
                return False, "Kayıt bulunamadı."
            try:
                p = QUAR_DIR / f"{qid}.mavq"
                if p.exists():
                    os.remove(p)
            except OSError as e:
                return False, f"Silinemedi: {e}"
            self.items.remove(it)
            self._save()
            return True, f"Kalıcı olarak silindi: {it['name']}"


# --------------------------------------------------------------------------
# ANDROID / MASAÜSTÜ KONUM YARDIMCILARI  (motor bölümündeki varsayılanları geçersiz kılar)
# --------------------------------------------------------------------------
def ext_storage() -> str:
    if IS_ANDROID:
        return os.environ.get("EXTERNAL_STORAGE") or "/storage/emulated/0"
    return str(_home())


def local_roots() -> list:
    roots = [ext_storage()]
    if IS_ANDROID:
        try:
            for n in sorted(os.listdir("/storage")):
                p = os.path.join("/storage", n)
                if n not in ("self", "emulated") and os.path.isdir(p) and os.access(p, os.R_OK):
                    roots.append(p)
        except OSError:
            pass
    return roots


def quick_roots() -> list:
    base = ext_storage()
    names = (("Download", "DCIM", "Documents", "Pictures", "Movies", "Music") if IS_ANDROID
             else ("Downloads", "Desktop", "Documents"))
    out = [os.path.join(base, n) for n in names if os.path.isdir(os.path.join(base, n))]
    return out or [base]


def default_watch_dir() -> str:
    d = os.path.join(ext_storage(), "Download" if IS_ANDROID else "Downloads")
    return d if os.path.isdir(d) else ext_storage()


# --------------------------------------------------------------------------
# SİSTEM MONİTÖRÜ  (psutil -> /proc -> MAV işlem CPU'su / simülasyon)
# --------------------------------------------------------------------------
class SysMon:
    def __init__(self):
        self.prev_stat = None
        self.prev_proc = (time.time(), time.process_time())
        self.sim_ram = 46.0
        self.cores = os.cpu_count() or 1
        if HAS_PSUTIL:
            try:
                psutil.cpu_percent(None)
            except Exception:
                pass

    def _cpu_stat(self):
        try:
            with open("/proc/stat", "r") as f:
                vals = [int(x) for x in f.readline().split()[1:8]]
            idle, total = vals[3] + vals[4], sum(vals)
            res = None
            if self.prev_stat:
                dt, di = total - self.prev_stat[0], idle - self.prev_stat[1]
                if dt > 0:
                    res = max(0.0, min(100.0, 100.0 * (1 - di / dt)))
            self.prev_stat = (total, idle)
            return res
        except Exception:
            return None

    def _cpu_proc(self):
        now, cpu = time.time(), time.process_time()
        pt, pc = self.prev_proc
        self.prev_proc = (now, cpu)
        dt = max(now - pt, 0.001)
        return max(0.0, min(100.0, 100.0 * (cpu - pc) / dt / self.cores))

    def _ram(self):
        if HAS_PSUTIL:
            try:
                vm = psutil.virtual_memory()
                return float(vm.percent), f"{vm.used / 2**30:.1f} / {vm.total / 2**30:.1f} GB"
            except Exception:
                pass
        try:
            info = {}
            with open("/proc/meminfo", "r") as f:
                for line in f:
                    k, v = line.split(":", 1)
                    info[k] = int(v.split()[0])
            total, avail = info["MemTotal"], info["MemAvailable"]
            used = total - avail
            return 100.0 * used / total, f"{used / 2**20:.1f} / {total / 2**20:.1f} GB"
        except Exception:
            self.sim_ram = min(88, max(30, self.sim_ram + random.uniform(-2.5, 2.5)))
            return self.sim_ram, "simüle edilmiş veri"

    def sample(self):
        """Dönüş: (cpu %, ram %, ram bilgisi, cpu kaynağı)"""
        cpu, src = None, ""
        if HAS_PSUTIL:
            try:
                cpu, src = float(psutil.cpu_percent(None)), "Sistem"
            except Exception:
                cpu = None
        if cpu is None:
            cpu = self._cpu_stat()
            src = "Sistem"
        if cpu is None:
            cpu, src = self._cpu_proc(), "MAV işlemi"
        ram, info = self._ram()
        return cpu, ram, info, src


# =====================================================================
#  KIVY ARAYÜZ
# =====================================================================
from kivy import kivy_data_dir  # noqa: E402
from kivy.animation import Animation  # noqa: E402
from kivy.app import App  # noqa: E402
from kivy.clock import Clock  # noqa: E402
from kivy.core.window import Window  # noqa: E402
from kivy.graphics import Color, Ellipse, Line, RoundedRectangle, Triangle  # noqa: E402
from kivy.metrics import dp, sp  # noqa: E402
from kivy.properties import NumericProperty  # noqa: E402
from kivy.uix.boxlayout import BoxLayout  # noqa: E402
from kivy.uix.button import Button  # noqa: E402
from kivy.uix.filechooser import FileChooserListView  # noqa: E402
from kivy.uix.floatlayout import FloatLayout  # noqa: E402
from kivy.uix.label import Label  # noqa: E402
from kivy.uix.popup import Popup  # noqa: E402
from kivy.uix.screenmanager import FadeTransition, Screen, ScreenManager  # noqa: E402
from kivy.uix.scrollview import ScrollView  # noqa: E402
from kivy.uix.textinput import TextInput  # noqa: E402
from kivy.uix.widget import Widget  # noqa: E402
from kivy.utils import escape_markup  # noqa: E402

_mono = os.path.join(kivy_data_dir, "fonts", "RobotoMono-Regular.ttf")
MONO = _mono if os.path.exists(_mono) else "Roboto"

if not IS_ANDROID:  # PC'de telefon boyutunda aç
    try:
        Window.size = (400, 780)
    except Exception:
        pass


def rgba(h: str, a: float = 1.0):
    h = h.lstrip("#")
    return (int(h[0:2], 16) / 255.0, int(h[2:4], 16) / 255.0, int(h[4:6], 16) / 255.0, a)


def mixc(a, b, t):
    return tuple(a[i] + (b[i] - a[i]) * t for i in range(4))


# ---------------------------------------------------------------- Android izinleri
def _sdk_int() -> int:
    from jnius import autoclass
    return int(autoclass("android.os.Build$VERSION").SDK_INT)


def storage_granted() -> bool:
    if not IS_ANDROID:
        return True
    try:
        from jnius import autoclass
        if _sdk_int() >= 30:
            return bool(autoclass("android.os.Environment").isExternalStorageManager())
        from android.permissions import Permission, check_permission
        return bool(check_permission(Permission.READ_EXTERNAL_STORAGE))
    except Exception:
        return False


def request_storage() -> None:
    if not IS_ANDROID:
        return
    try:
        from jnius import autoclass
        if _sdk_int() >= 30:
            Intent = autoclass("android.content.Intent")
            Settings = autoclass("android.provider.Settings")
            Uri = autoclass("android.net.Uri")
            act = autoclass("org.kivy.android.PythonActivity").mActivity
            intent = Intent(Settings.ACTION_MANAGE_APP_ALL_FILES_ACCESS_PERMISSION)
            intent.setData(Uri.parse("package:" + act.getPackageName()))
            act.startActivity(intent)
        else:
            from android.permissions import Permission, request_permissions
            request_permissions([Permission.READ_EXTERNAL_STORAGE, Permission.WRITE_EXTERNAL_STORAGE])
    except Exception as ex:
        print("storage permission error:", ex)


def minimize_app() -> bool:
    if not IS_ANDROID:
        return False
    try:
        from jnius import autoclass
        autoclass("org.kivy.android.PythonActivity").mActivity.moveTaskToBack(True)
        return True
    except Exception:
        return False


# ---------------------------------------------------------------- temel widget'lar
class Card(BoxLayout):
    def __init__(self, bg=None, border=None, radius=14, **kw):
        kw.setdefault("orientation", "vertical")
        super().__init__(**kw)
        self._r = dp(radius)
        with self.canvas.before:
            self._cbg = Color(*rgba(bg or C["card"]))
            self._rbg = RoundedRectangle(pos=self.pos, size=self.size, radius=[self._r])
            self._cbd = Color(*rgba(border or C["border"]))
            self._lbd = Line(rounded_rectangle=(self.x, self.y, max(self.width, 1), max(self.height, 1), self._r),
                             width=1.0)
        self.bind(pos=self._upd, size=self._upd)

    def _upd(self, *a):
        self._rbg.pos, self._rbg.size = self.pos, self.size
        if self.width > 2 and self.height > 2:
            self._lbd.rounded_rectangle = (self.x, self.y, self.width, self.height, self._r)

    def set_border(self, col: str):
        self._cbd.rgba = rgba(col)


class Btn(Button):
    def __init__(self, text="", base=None, down=None, fg=None, radius=12, size=14, bold=True, **kw):
        self._base = rgba(base or C["cyan"])
        self._down = rgba(down) if down else mixc(self._base, (1, 1, 1, 1), 0.25)
        kw.setdefault("size_hint_y", None)
        kw.setdefault("height", dp(48))
        super().__init__(text=text, background_normal="", background_down="", background_color=(0, 0, 0, 0),
                         color=rgba(fg or "#00131A"), font_size=sp(size), bold=bold, **kw)
        with self.canvas.before:
            self._col = Color(*self._base)
            self._rr = RoundedRectangle(pos=self.pos, size=self.size, radius=[dp(radius)])
        self.bind(pos=self._upd, size=self._upd, state=self._state, disabled=self._state)
        self._state()

    def _upd(self, *a):
        self._rr.pos, self._rr.size = self.pos, self.size

    def _target(self):
        if self.disabled:
            return mixc(self._base, rgba(C["bg"]), 0.65)
        return self._down if self.state == "down" else self._base

    def _state(self, *a):
        t = self._target()
        try:
            Animation.cancel_all(self._col)
            Animation(r=t[0], g=t[1], b=t[2], a=t[3], d=0.12).start(self._col)
        except Exception:
            self._col.rgba = t

    def set_colors(self, base, down=None, fg=None):
        self._base = rgba(base)
        self._down = rgba(down) if down else mixc(self._base, (1, 1, 1, 1), 0.25)
        if fg:
            self.color = rgba(fg)
        self._col.rgba = self._target()


class Lbl(Label):
    def __init__(self, text="", size=14, color=None, bold=False, mono=False, wrap=False, align="left", **kw):
        kw.setdefault("font_size", sp(size))
        if mono:
            kw["font_name"] = MONO
        super().__init__(text=text, color=rgba(color or C["text"]), bold=bold and not mono,
                         halign=align, valign="top" if wrap else "middle", **kw)
        if wrap:
            self.size_hint_y = None
            self.bind(width=self._wrap_w, texture_size=self._wrap_h)
            self._wrap_w()
        else:
            self.bind(size=self._fit)
            self._fit()

    def _fit(self, *a):
        self.text_size = self.size

    def _wrap_w(self, *a):
        self.text_size = (self.width, None)

    def _wrap_h(self, *a):
        self.height = self.texture_size[1]


class Field(Card):
    def __init__(self, hint="", password=False, **kw):
        super().__init__(bg="#080D1C", radius=10, size_hint_y=None, height=dp(48), **kw)
        self.input = TextInput(hint_text=hint, password=password, multiline=False, write_tab=False,
                               background_normal="", background_active="", background_color=(0, 0, 0, 0),
                               foreground_color=rgba(C["text"]), hint_text_color=rgba(C["muted"]),
                               cursor_color=rgba(C["cyan"]), font_size=sp(16),
                               padding=[dp(14), dp(13), dp(14), dp(13)])
        self.add_widget(self.input)
        self.input.bind(focus=self._focus)

    def _focus(self, inst, f):
        self.set_border(C["cyan"] if f else C["border"])

    @property
    def text(self):
        return self.input.text

    @text.setter
    def text(self, v):
        self.input.text = v


class Dot(Widget):
    def __init__(self, color=None, **kw):
        kw.setdefault("size_hint", (None, None))
        kw.setdefault("size", (dp(14), dp(14)))
        super().__init__(**kw)
        self._color = color or C["ok"]
        self.bind(pos=self._d, size=self._d)
        self._d()

    def set_color(self, c):
        self._color = c
        self._d()

    def _d(self, *a):
        self.canvas.clear()
        with self.canvas:
            Color(*rgba(self._color, 0.25))
            Ellipse(pos=(self.x - dp(3), self.y - dp(3)), size=(self.width + dp(6), self.height + dp(6)))
            Color(*rgba(self._color))
            Ellipse(pos=self.pos, size=self.size)


class Bar(Widget):
    value = NumericProperty(0.0)
    phase = NumericProperty(0.0)

    def __init__(self, **kw):
        kw.setdefault("size_hint_y", None)
        kw.setdefault("height", dp(14))
        super().__init__(**kw)
        self.color = C["cyan"]
        self.ind = False
        self._ev = None
        self._t0 = 0.0
        self.bind(pos=self._d, size=self._d, value=self._d, phase=self._d)

    def set(self, v, instant=False):
        v = max(0.0, min(1.0, v))
        Animation.cancel_all(self, "value")
        if instant:
            self.value = v
        else:
            Animation(value=v, d=0.25).start(self)

    def set_color(self, c):
        self.color = c
        self._d()

    def set_indeterminate(self, on):
        if on == self.ind:
            return
        self.ind = on
        if on:
            self._t0 = time.time()
            self._ev = Clock.schedule_interval(self._tick, 1 / 30.0)
        else:
            if self._ev:
                self._ev.cancel()
                self._ev = None
            self.phase = 0.0
        self._d()

    def _tick(self, dt):
        p = (time.time() - self._t0) % 2.0
        self.phase = p if p < 1 else 2 - p

    def _d(self, *a):
        self.canvas.clear()
        h = self.height
        with self.canvas:
            Color(*rgba("#131B36"))
            RoundedRectangle(pos=self.pos, size=self.size, radius=[h / 2])
            Color(*rgba(self.color))
            if self.ind:
                sw = max(h, self.width * 0.3)
                RoundedRectangle(pos=(self.x + (self.width - sw) * self.phase, self.y), size=(sw, h), radius=[h / 2])
            elif self.value > 0:
                RoundedRectangle(pos=self.pos, size=(max(h, self.width * self.value), h), radius=[h / 2])


class Gauge(FloatLayout):
    shown = NumericProperty(0.0)

    def __init__(self, title="", **kw):
        super().__init__(**kw)
        self.val = Lbl("0%", size=24, bold=True, align="center", size_hint=(1, 0.3), pos_hint={"center_x": .5, "center_y": .56})
        self.ttl = Lbl(title, size=11, color=C["muted"], align="center", size_hint=(1, 0.2), pos_hint={"center_x": .5, "center_y": .34})
        self.add_widget(self.val)
        self.add_widget(self.ttl)
        self.bind(pos=self._d, size=self._d, shown=self._d)
        self._d()

    def set(self, v):
        v = max(0.0, min(100.0, v))
        Animation.cancel_all(self, "shown")
        Animation(shown=v, d=0.6, t="out_cubic").start(self)

    @staticmethod
    def _col(v):
        return C["cyan"] if v < 60 else (C["warn"] if v < 85 else C["danger"])

    def _d(self, *a):
        self.val.text = f"{self.shown:.0f}%"
        cv = self.canvas.before
        cv.clear()
        r = min(self.width, self.height) / 2 - dp(14)
        if r <= 4:
            return
        cx, cy = self.center
        with cv:
            Color(*rgba("#17213F"))
            Line(circle=(cx, cy, r, -135, 135), width=dp(8), cap="round")
            Color(*rgba(self._col(self.shown)))
            Line(circle=(cx, cy, r, -135, -135 + max(3.0, 270.0 * self.shown / 100.0)), width=dp(8), cap="round")


class LineChart(Widget):
    def __init__(self, series, maxlen=60, **kw):
        super().__init__(**kw)
        self.series = series
        self.data = {n: deque([0.0] * maxlen, maxlen=maxlen) for n, _ in series}
        self.bind(pos=self._d, size=self._d)

    def push(self, **vals):
        for k, v in vals.items():
            self.data[k].append(v)
        self._d()

    def _d(self, *a):
        self.canvas.clear()
        if self.width < 20 or self.height < 20:
            return
        l, r = self.x + dp(4), self.right - dp(4)
        b, t = self.y + dp(6), self.top - dp(6)
        with self.canvas:
            Color(*rgba("#16213F"))
            for v in (0, 25, 50, 75, 100):
                y = b + (t - b) * v / 100.0
                Line(points=[l, y, r, y], width=1)
            for name, color in self.series:
                d = self.data[name]
                n = len(d)
                pts = []
                for i, v in enumerate(d):
                    pts += [l + (r - l) * i / (n - 1), b + (t - b) * min(100.0, max(0.0, v)) / 100.0]
                Color(*rgba(color))
                Line(points=pts, width=dp(1.6))


class Terminal(Card):
    COLORS = {"info": "#9FB3D1", "sys": C["cyan"], "scan": "#4F6F8F", "ok": C["ok"],
              "warn": C["warn"], "threat": C["danger"], "shield": "#8E9CFF"}

    def __init__(self, maxlines=70, **kw):
        super().__init__(bg="#000000", radius=10, **kw)
        self.lines = deque(maxlen=maxlines)
        self._pending = False
        self.sv = ScrollView(do_scroll_x=False, bar_width=dp(3), scroll_type=["bars", "content"])
        self.lab = Label(text="", markup=True, font_name=MONO, font_size=sp(10.5), size_hint_y=None,
                         halign="left", valign="top", color=rgba(C["text"]))
        self.lab.bind(width=self._w, texture_size=self._h)
        self.sv.add_widget(self.lab)
        self.add_widget(self.sv)

    def _w(self, *a):
        self.lab.text_size = (self.lab.width, None)

    def _h(self, *a):
        self.lab.height = self.lab.texture_size[1] + dp(8)

    def append(self, text, level="info"):
        col = self.COLORS.get(level, self.COLORS["info"])
        self.lines.append(f"[color={col}]{escape_markup(text)}[/color]")
        if not self._pending:
            self._pending = True
            Clock.schedule_once(self._flush, 0.12)

    def _flush(self, dt):
        self._pending = False
        stick = self.sv.scroll_y <= 0.05
        self.lab.text = "\n".join(self.lines)
        if stick:
            Clock.schedule_once(lambda d: setattr(self.sv, "scroll_y", 0), 0.05)


def smooth(pts, n=3, closed=False):
    """Chaikin köşe yumuşatma."""
    for _ in range(n):
        if len(pts) < 3:
            break
        new = [] if closed else [pts[0]]
        rng = range(len(pts)) if closed else range(len(pts) - 1)
        for i in rng:
            a, b = pts[i], pts[(i + 1) % len(pts)]
            new.append((.75 * a[0] + .25 * b[0], .75 * a[1] + .25 * b[1]))
            new.append((.25 * a[0] + .75 * b[0], .25 * a[1] + .75 * b[1]))
        if not closed:
            new.append(pts[-1])
        pts = new
    return pts


class Logo(Widget):
    """Yandan görünüşlü minimalist muhabbet kuşu kafası (çizgi sanatı)."""

    def __init__(self, **kw):
        super().__init__(**kw)
        self.bind(pos=self._d, size=self._d)
        self._d()

    def _d(self, *a):
        self.canvas.clear()
        side = min(self.width, self.height)
        if side < 8:
            return
        s = side / 200.0
        ox = self.x + (self.width - side) / 2.0
        oy = self.y + (self.height - side) / 2.0 + side

        def X(x):
            return ox + x * s

        def Y(y):
            return oy - y * s

        def flat(pts):
            return [c for x, y in pts for c in (X(x), Y(y))]

        lw = max(1.6, side * 0.021)
        thin = max(1.0, side * 0.011)
        cy_, blk, fill = rgba(C["cyan"]), rgba("#000000"), rgba("#0B1A3C")

        def oval(x1, y1, x2, y2, fcol, ocol, w):
            pos, size = (X(x1), Y(y2)), ((x2 - x1) * s, (y2 - y1) * s)
            if fcol:
                Color(*fcol)
                Ellipse(pos=pos, size=size)
            if ocol:
                Color(*ocol)
                Line(ellipse=(pos[0], pos[1], size[0], size[1]), width=w)

        with self.canvas:
            # boyun
            Color(*cy_)
            Line(points=flat(smooth([(48, 128), (38, 152), (46, 176), (72, 194)])), width=lw, cap="round")
            Line(points=flat(smooth([(142, 126), (152, 150), (144, 176), (118, 194)])), width=lw, cap="round")
            # kafa
            oval(40, 38, 150, 148, fill, cy_, lw)
            # tüy çizgileri
            for pts in ([(66, 52), (73, 46), (80, 52), (87, 46), (94, 52)],
                        [(54, 66), (61, 60), (68, 66), (75, 60), (82, 66)],
                        [(48, 80), (55, 74), (62, 80), (69, 74), (76, 80)],
                        [(48, 94), (55, 88), (62, 94), (69, 88)]):
                fl = flat(smooth(pts))
                Color(*blk)
                Line(points=fl, width=thin * 2.4, cap="round")
                Color(*cy_)
                Line(points=fl, width=thin, cap="round")
            # gaga
            beak = smooth([(142, 78), (160, 80), (174, 94), (172, 112), (162, 118), (160, 106), (150, 108), (143, 104)],
                          n=2, closed=True)
            mx = sum(p[0] for p in beak) / len(beak)
            my = sum(p[1] for p in beak) / len(beak)
            Color(*fill)
            for i in range(len(beak)):
                a, b = beak[i], beak[(i + 1) % len(beak)]
                Triangle(points=[X(mx), Y(my), X(a[0]), Y(a[1]), X(b[0]), Y(b[1])])
            Color(*cy_)
            Line(points=flat(beak), width=lw, close=True, joint="round")
            # cere + burun deliği
            oval(138, 68, 156, 84, fill, cy_, thin)
            oval(146, 74, 151, 79, blk, None, 1)
            # göz
            oval(99, 67, 125, 93, blk, cy_, lw * 0.75)
            oval(116, 72, 121, 77, cy_, None, 1)
            # yanak
            oval(94, 102, 122, 120, rgba("#0A1330"), cy_, thin)
            # boğaz benekleri
            for x, y in ((132, 126), (118, 131), (104, 131)):
                oval(x - 4.5, y - 4.5, x + 4.5, y + 4.5, blk, cy_, thin)


def make_brand(size_dp: float, text_size: float = 34) -> BoxLayout:
    """Logo + altında 'MAVS' yazısı."""
    box = BoxLayout(orientation="vertical", size_hint_y=None, height=dp(size_dp) + dp(text_size * 1.5))
    lg = Logo(size_hint=(None, None), size=(dp(size_dp), dp(size_dp)), pos_hint={"center_x": .5})
    box.add_widget(lg)
    box.add_widget(Lbl("MAVS", size=text_size, bold=True, color=C["logo_blue"], align="center",
                       size_hint_y=None, height=dp(text_size * 1.5),
                       outline_width=2, outline_color=rgba(C["cyan"])))
    return box


# ---------------------------------------------------------------- GİRİŞ / KAYIT
class AuthView(ScrollView):
    def __init__(self, app, **kw):
        super().__init__(do_scroll_x=False, bar_width=0, **kw)
        self.app = app
        self.mode, self.fails, self.locked = "login", 0, False
        box = BoxLayout(orientation="vertical", size_hint_y=None, padding=[dp(24), dp(26), dp(24), dp(24)],
                        spacing=dp(10))
        box.bind(minimum_height=box.setter("height"))
        self.add_widget(box)

        box.add_widget(make_brand(120, 38))
        box.add_widget(Lbl("Gelişmiş Mobil Koruma Altyapısı", size=12, color=C["muted"], align="center",
                           size_hint_y=None, height=dp(22)))

        tabs = BoxLayout(size_hint_y=None, height=dp(42), spacing=dp(6))
        self.t_login = Btn("Giriş Yap", size=13, height=dp(42), on_release=lambda *a: self._switch("login"))
        self.t_reg = Btn("Kayıt Ol", size=13, height=dp(42), base="#141A2E", fg=C["muted"],
                         on_release=lambda *a: self._switch("register"))
        tabs.add_widget(self.t_login)
        tabs.add_widget(self.t_reg)
        box.add_widget(tabs)

        self.e_user = Field("Kullanıcı adı")
        self.e_pass = Field("Şifre", password=True)
        self.e_pass2 = Field("Şifre (tekrar)", password=True)
        for f in (self.e_user, self.e_pass, self.e_pass2):
            box.add_widget(f)
            f.input.bind(on_text_validate=lambda *a: self._submit())
        self._hide(self.e_pass2, True)

        self.b_show = Btn("Şifreyi göster", base=C["bg"], down="#16213F", fg=C["muted"], size=12, height=dp(32),
                          bold=False, on_release=lambda *a: self._toggle_pw())
        box.add_widget(self.b_show)

        self.msg = Lbl("", size=12, color=C["danger"], align="center", wrap=True)
        box.add_widget(self.msg)
        self.btn = Btn("GİRİŞ YAP", size=15, height=dp(50), on_release=lambda *a: self._submit())
        box.add_widget(self.btn)
        box.add_widget(Lbl("Hesap bilgileri yalnızca bu cihazda, PBKDF2 özeti olarak saklanır.", size=10,
                           color=C["muted"], align="center", wrap=True))

    @staticmethod
    def _hide(w, hide):
        w.opacity = 0 if hide else 1
        w.disabled = hide
        w.height = 0 if hide else dp(48)

    def reset(self):
        self.e_user.text = self.e_pass.text = self.e_pass2.text = ""
        self.fails = 0
        self._switch("login")
        self._msg("")

    def _toggle_pw(self):
        show = self.e_pass.input.password
        self.e_pass.input.password = not show
        self.e_pass2.input.password = not show
        self.b_show.text = "Şifreyi gizle" if show else "Şifreyi göster"

    def _switch(self, mode):
        self.mode = mode
        reg = mode == "register"
        self.t_login.set_colors("#141A2E" if reg else C["cyan"], fg=C["muted"] if reg else "#00131A")
        self.t_reg.set_colors(C["cyan"] if reg else "#141A2E", fg="#00131A" if reg else C["muted"])
        self._hide(self.e_pass2, not reg)
        self.btn.text = "HESAP OLUŞTUR" if reg else "GİRİŞ YAP"
        self._msg("")

    def _msg(self, text, ok=False):
        self.msg.text = text
        self.msg.color = rgba(C["ok"] if ok else C["danger"])

    def _submit(self):
        if self.locked:
            return
        user, pw = self.e_user.text.strip(), self.e_pass.text
        if self.mode == "register":
            if pw != self.e_pass2.text:
                self._msg("Şifreler eşleşmiyor.")
                return
            ok, msg = self.app.auth.register(user, pw)
            if not ok:
                self._msg(msg)
                return
        ok, msg, disp = self.app.auth.login(user, pw)
        if ok:
            self.app.login_success(disp)
            return
        self.fails += 1
        self._msg(msg)
        if self.fails >= 5:
            self.locked = True
            self.btn.disabled = True
            self._msg("Çok fazla hatalı deneme. 10 saniye bekleyin.")
            Clock.schedule_once(self._unlock, 10)

    def _unlock(self, dt):
        self.locked, self.fails = False, 0
        self.btn.disabled = False
        self._msg("")


# ---------------------------------------------------------------- SAYFALAR
class Page(Screen):
    def __init__(self, app, name, **kw):
        super().__init__(name=name, **kw)
        self.app = app

    def scroll_body(self):
        sv = ScrollView(do_scroll_x=False, bar_width=dp(3), scroll_type=["bars", "content"],
                        bar_color=rgba(C["cyan"], .5))
        body = BoxLayout(orientation="vertical", size_hint_y=None, padding=[dp(12), dp(12), dp(12), dp(16)],
                         spacing=dp(10))
        body.bind(minimum_height=body.setter("height"))
        sv.add_widget(body)
        self.add_widget(sv)
        return body


class DashboardPage(Page):
    def __init__(self, app):
        super().__init__(app, "dash")
        body = self.scroll_body()

        hero = Card(size_hint_y=None, height=dp(240), padding=dp(14), spacing=dp(8))
        top = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(12))
        self.dot = Dot(C["ok"], pos_hint={"center_y": .5})
        top.add_widget(self.dot)
        tx = BoxLayout(orientation="vertical")
        self.h_title = Lbl("Sisteminiz Korunuyor", size=18, bold=True)
        self.h_sub = Lbl("", size=11, color=C["muted"])
        tx.add_widget(self.h_title)
        tx.add_widget(self.h_sub)
        top.add_widget(tx)
        hero.add_widget(top)

        r1 = BoxLayout(size_hint_y=None, height=dp(44), spacing=dp(8))
        self.b_shield = Btn("", size=12, height=dp(44), on_release=lambda *a: app.toggle_shield())
        self.b_auto = Btn("", size=12, height=dp(44), on_release=lambda *a: app.toggle_auto_q())
        r1.add_widget(self.b_shield)
        r1.add_widget(self.b_auto)
        hero.add_widget(r1)
        r2 = BoxLayout(size_hint_y=None, height=dp(44), spacing=dp(8))
        r2.add_widget(Btn("Hızlı Tarama", size=12, height=dp(44), on_release=lambda *a: app.goto_scan("quick")))
        r2.add_widget(Btn("Kalkanı Test Et", size=12, height=dp(44), base="#16213F", fg=C["text"],
                          on_release=lambda *a: app.test_shield()))
        hero.add_widget(r2)
        hero.add_widget(Btn("İzlenen klasörü değiştir", size=12, height=dp(44), base="#16213F", fg=C["text"],
                            on_release=lambda *a: app.choose_watch_dir()))
        body.add_widget(hero)

        gc = Card(orientation="horizontal", size_hint_y=None, height=dp(176), padding=dp(10), spacing=dp(8))
        for attr, title in (("g_cpu", "CPU"), ("g_ram", "RAM")):
            col = BoxLayout(orientation="vertical")
            col.add_widget(Lbl(f"{title} Kullanımı", size=12, bold=True, align="center", size_hint_y=None, height=dp(22)))
            g = Gauge(title)
            setattr(self, attr, g)
            col.add_widget(g)
            info = Lbl("", size=10, color=C["muted"], align="center", size_hint_y=None, height=dp(18))
            setattr(self, attr + "_info", info)
            col.add_widget(info)
            gc.add_widget(col)
        body.add_widget(gc)

        cc = Card(size_hint_y=None, height=dp(190), padding=dp(12), spacing=dp(4))
        hdr = BoxLayout(size_hint_y=None, height=dp(22))
        hdr.add_widget(Lbl("Canlı Performans (60 sn)", size=12, bold=True))
        hdr.add_widget(Lbl("CPU", size=11, bold=True, color=C["cyan"], size_hint_x=None, width=dp(40), align="right"))
        hdr.add_widget(Lbl("RAM", size=11, bold=True, color=C["violet"], size_hint_x=None, width=dp(40), align="right"))
        cc.add_widget(hdr)
        self.chart = LineChart([("CPU", C["cyan"]), ("RAM", C["violet"])])
        cc.add_widget(self.chart)
        body.add_widget(cc)

        sc = Card(size_hint_y=None, padding=dp(14), spacing=dp(4))
        sc.bind(minimum_height=sc.setter("height"))
        sc.add_widget(Lbl("İstatistikler", size=13, bold=True, color=C["cyan"], size_hint_y=None, height=dp(24)))
        self.stat = {}
        for key, label in (("scanned", "Taranan dosya"), ("threats", "Tespit edilen"),
                           ("quar", "Karantinada"), ("last", "Son tarama")):
            r = BoxLayout(size_hint_y=None, height=dp(24))
            r.add_widget(Lbl(label, size=12, color=C["muted"]))
            v = Lbl("-", size=12, bold=True, align="right")
            self.stat[key] = v
            r.add_widget(v)
            sc.add_widget(r)
        body.add_widget(sc)

        tc = Card(size_hint_y=None, height=dp(260), padding=dp(10), spacing=dp(6))
        tc.add_widget(Lbl("Canlı Olay Akışı", size=12, bold=True, color=C["cyan"], size_hint_y=None, height=dp(22)))
        self.term = Terminal()
        tc.add_widget(self.term)
        body.add_widget(tc)
        app.register_terminal(self.term)
        self.update_status()

    def on_sample(self, cpu, ram, info, src):
        self.g_cpu.set(cpu)
        self.g_ram.set(ram)
        self.g_cpu_info.text = f"{os.cpu_count() or '?'} çekirdek · {src}"
        self.g_ram_info.text = info
        self.chart.push(CPU=cpu, RAM=ram)
        self.refresh_stats()

    def refresh_stats(self):
        a = self.app
        self.stat["scanned"].text = f"{a.total_scanned:,}".replace(",", ".")
        self.stat["threats"].text = str(a.total_threats)
        self.stat["threats"].color = rgba(C["danger"] if a.total_threats else C["text"])
        self.stat["quar"].text = str(len(a.quarantine.items))
        self.stat["last"].text = a.last_scan

    def update_status(self):
        a = self.app
        on = a.shield is not None and a.shield.is_alive()
        if a.pending:
            self.dot.set_color(C["danger"])
            self.h_title.text = f"Dikkat: {len(a.pending)} tehdit bekliyor"
            self.h_sub.text = "Tarama sekmesinden karantinaya alabilirsiniz."
        elif on:
            self.dot.set_color(C["ok"])
            self.h_title.text = "Sisteminiz Korunuyor"
            self.h_sub.text = f"Kalkan aktif · {short_path(a.watch_dir, 34)}"
        else:
            self.dot.set_color(C["warn"])
            self.h_title.text = "Gerçek Zamanlı Koruma Kapalı"
            self.h_sub.text = "Kalkanı açarak yeni dosyaları otomatik taratın."
        self.b_shield.text = "Kalkan: AÇIK" if on else "Kalkan: KAPALI"
        self.b_shield.set_colors(C["cyan"] if on else "#3A2A10", fg="#00131A" if on else C["warn"])
        self.b_auto.text = "Oto. karantina: AÇIK" if a.auto_q else "Oto. karantina: KAPALI"
        self.b_auto.set_colors(C["cyan"] if a.auto_q else "#16213F", fg="#00131A" if a.auto_q else C["muted"])


class ScanPage(Page):
    def __init__(self, app):
        super().__init__(app, "scan")
        self.scanning = False
        self._dots = 0
        self._title = "Hazır"
        root = BoxLayout(orientation="vertical", padding=dp(12), spacing=dp(10))
        self.add_widget(root)

        modes = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(8))
        self.mode_btns = []
        for text, key in (("Hızlı Tarama", "quick"), ("Tam Tarama", "full"), ("Özel Klasör", "custom")):
            b = Btn(text, size=12, height=dp(46), on_release=lambda *a, k=key: app.scan_action(k))
            self.mode_btns.append(b)
            modes.add_widget(b)
        root.add_widget(modes)

        pc = Card(size_hint_y=None, height=dp(218), padding=dp(12), spacing=dp(8))
        top = BoxLayout(size_hint_y=None, height=dp(24))
        self.status = Lbl("Hazır", size=14, bold=True)
        self.pct = Lbl("0%", size=14, bold=True, color=C["cyan"], align="right", size_hint_x=None, width=dp(56))
        top.add_widget(self.status)
        top.add_widget(self.pct)
        pc.add_widget(top)
        self.current = Lbl("", size=10, mono=True, color=C["muted"], size_hint_y=None, height=dp(16),
                           shorten=True, shorten_from="left")
        pc.add_widget(self.current)
        self.bar = Bar()
        pc.add_widget(self.bar)

        tiles = BoxLayout(size_hint_y=None, height=dp(54), spacing=dp(6))
        self.tile = {}
        for key, label in (("scanned", "Taranan"), ("threats", "Tehdit"), ("skipped", "Atlanan"), ("time", "Süre")):
            t = Card(bg="#0A1124", border="#0A1124", radius=10, padding=[dp(4), dp(4)], spacing=0)
            t.add_widget(Lbl(label, size=10, color=C["muted"], align="center"))
            v = Lbl("0", size=15, bold=True, align="center")
            self.tile[key] = v
            t.add_widget(v)
            tiles.add_widget(t)
        pc.add_widget(tiles)

        act = BoxLayout(size_hint_y=None, height=dp(42), spacing=dp(6))
        self.stop_btn = Btn("Durdur", size=12, height=dp(42), base="#3A1620", fg=C["text"], disabled=True,
                            on_release=lambda *a: app.stop_scan())
        self.q_btn = Btn("Karantinaya Al", size=12, height=dp(42), base="#16213F", fg=C["text"], disabled=True,
                         on_release=lambda *a: app.quarantine_pending())
        self.test_btn = Btn("Test Dosyası", size=12, height=dp(42), base="#16213F", fg=C["text"],
                            on_release=lambda *a: app.test_scan())
        for b in (self.stop_btn, self.q_btn, self.test_btn):
            act.add_widget(b)
        pc.add_widget(act)
        root.add_widget(pc)

        tc = Card(padding=dp(10), spacing=dp(6))
        tc.add_widget(Lbl("Terminal", size=12, bold=True, color=C["cyan"], size_hint_y=None, height=dp(22)))
        self.term = Terminal()
        tc.add_widget(self.term)
        root.add_widget(tc)
        app.register_terminal(self.term)
        Clock.schedule_interval(self._anim, 0.4)

    def _anim(self, dt):
        if self.scanning:
            self._dots = (self._dots + 1) % 4
            self.status.text = self._title + "." * self._dots

    def _set_buttons(self, scanning):
        for b in self.mode_btns:
            b.disabled = scanning
        self.stop_btn.disabled = not scanning
        self.test_btn.disabled = scanning

    def begin(self, title):
        self.scanning = True
        self._title = title
        self._set_buttons(True)
        self.status.text = title
        self.bar.set_color(C["cyan"])
        self.bar.set(0, instant=True)
        self.pct.text = "0%"
        for k, v in self.tile.items():
            v.text = "00:00" if k == "time" else "0"
        self.tile["threats"].color = rgba(C["text"])

    def set_phase(self, phase):
        self.bar.set_indeterminate(phase == "listing")

    def update_progress(self, d):
        self.bar.set_indeterminate(False)
        self.bar.set(d["frac"])
        self.pct.text = f"{d['frac'] * 100:.0f}%"
        self.current.text = str(d["current"])
        self.tile["scanned"].text = str(d["scanned"])
        self.tile["threats"].text = str(d["threats"])
        self.tile["threats"].color = rgba(C["danger"] if d["threats"] else C["text"])
        self.tile["skipped"].text = str(d["skipped"])
        self.tile["time"].text = fmt_dur(d["elapsed"])

    def finish(self, d):
        self.scanning = False
        self.bar.set_indeterminate(False)
        self._set_buttons(False)
        if d.get("stopped"):
            self.status.text = "Tarama durduruldu"
            self.bar.set_color(C["warn"])
        else:
            self.status.text = "Tarama tamamlandı"
            self.bar.set(1.0)
            self.pct.text = "100%"
            self.bar.set_color(C["danger"] if d["threats"] else C["ok"])
        self.current.text = ""
        self.tile["scanned"].text = str(d["scanned"])
        self.tile["threats"].text = str(d["threats"])
        self.tile["threats"].color = rgba(C["danger"] if d["threats"] else C["text"])
        self.tile["skipped"].text = str(d["skipped"])
        self.tile["time"].text = fmt_dur(d["elapsed"])

    def set_pending(self, n):
        self.q_btn.disabled = n == 0
        self.q_btn.text = f"Karantinaya Al ({n})" if n else "Karantinaya Al"


class QuarantinePage(Page):
    def __init__(self, app):
        super().__init__(app, "quar")
        root = BoxLayout(orientation="vertical")
        self.add_widget(root)
        bar = BoxLayout(size_hint_y=None, height=dp(56), padding=[dp(14), dp(8), dp(12), dp(8)], spacing=dp(8))
        self.count = Lbl("", size=14, bold=True)
        bar.add_widget(self.count)
        bar.add_widget(Btn("Tümünü Sil", size=12, height=dp(40), base="#3A1620", fg=C["text"], size_hint_x=None,
                           width=dp(110), on_release=lambda *a: self._delete_all()))
        root.add_widget(bar)
        sv = ScrollView(do_scroll_x=False, bar_width=dp(3), scroll_type=["bars", "content"])
        self.listf = BoxLayout(orientation="vertical", size_hint_y=None, padding=[dp(12), 0, dp(12), dp(16)],
                               spacing=dp(8))
        self.listf.bind(minimum_height=self.listf.setter("height"))
        sv.add_widget(self.listf)
        root.add_widget(sv)

    def refresh(self):
        self.listf.clear_widgets()
        items = list(reversed(self.app.quarantine.items))
        self.count.text = f"{len(items)} öğe karantinada"
        if not items:
            self.listf.add_widget(Lbl("Karantina boş. Sisteminiz temiz görünüyor.", size=14, color=C["muted"],
                                      align="center", wrap=True))
            return
        for it in items:
            card = Card(size_hint_y=None, padding=dp(12), spacing=dp(6))
            card.bind(minimum_height=card.setter("height"))
            card.add_widget(Lbl(it["name"], size=14, bold=True, wrap=True))
            sev = C["danger"] if it["severity"] == "Tehdit" else C["warn"]
            card.add_widget(Lbl(f"{it['threat']}  ·  {it['severity']}", size=12, bold=True, color=sev, wrap=True))
            card.add_widget(Lbl(f"{short_path(it['path'], 60)}\n{fmt_size(it['size'])}  ·  {it['time']}", size=10,
                                color=C["muted"], wrap=True))
            row = BoxLayout(size_hint_y=None, height=dp(40), spacing=dp(8))
            row.add_widget(Btn("Geri Yükle", size=12, height=dp(40), base="#16213F", fg=C["cyan"],
                               on_release=lambda *a, i=it: self._restore(i)))
            row.add_widget(Btn("Kalıcı Olarak Sil", size=12, height=dp(40), base="#3A1620", fg=C["text"],
                               on_release=lambda *a, i=it: self._delete(i)))
            card.add_widget(row)
            self.listf.add_widget(card)

    def _restore(self, it):
        def go():
            ok, msg = self.app.quarantine.restore(it["id"])
            self.app.log("ok" if ok else "warn", f"[KARANTİNA] {msg}")
            self.refresh()
            self.app.refresh_status()
            if not ok:
                self.app.show_dialog("Geri Yükleme Başarısız", msg)
        self.app.show_dialog("Dosyayı geri yükle?",
                             f"'{it['name']}' tehdit içerebilir. Orijinal konumuna geri yüklemek istediğinize emin misiniz?",
                             [("Vazgeç", None, "ghost"), ("Geri Yükle", go, "primary")])

    def _delete(self, it):
        def go():
            ok, msg = self.app.quarantine.delete(it["id"])
            self.app.log("ok" if ok else "warn", f"[KARANTİNA] {msg}")
            self.refresh()
            self.app.refresh_status()
        self.app.show_dialog("Kalıcı olarak sil?", f"'{it['name']}' geri döndürülemez şekilde silinecek.",
                             [("Vazgeç", None, "ghost"), ("Sil", go, "danger")], danger=True)

    def _delete_all(self):
        if not self.app.quarantine.items:
            return

        def go():
            n = sum(1 for it in list(self.app.quarantine.items) if self.app.quarantine.delete(it["id"])[0])
            self.app.log("ok", f"[KARANTİNA] {n} öğe kalıcı olarak silindi.")
            self.refresh()
            self.app.refresh_status()
        self.app.show_dialog("Tümünü sil?", "Karantinadaki tüm dosyalar kalıcı olarak silinecek.",
                             [("Vazgeç", None, "ghost"), ("Tümünü Sil", go, "danger")], danger=True)


class LicensePage(Page):
    def __init__(self, app, user):
        super().__init__(app, "lic")
        body = self.scroll_body()
        card = Card(size_hint_y=None, padding=dp(16), spacing=dp(6))
        card.bind(minimum_height=card.setter("height"))
        head = BoxLayout(size_hint_y=None, height=dp(40))
        head.add_widget(Lbl("MAVM Pro", size=24, bold=True, color=C["cyan"]))
        head.add_widget(Lbl("AKTİF", size=13, bold=True, color=C["ok"], align="right", size_hint_x=None, width=dp(70)))
        card.add_widget(head)
        key = hashlib.sha256((user + "|MAVM").encode()).hexdigest().upper()
        lic = "MAVM-" + "-".join(key[i:i + 4] for i in (0, 4, 8, 12))
        info = (
            ("Ürün", "MAV Mobil — MAVS Güvenlik Altyapısı"),
            ("Sürüm", APP_VERSION),
            ("Lisans türü", "MAVM Pro (yerel etkinleştirme)"),
            ("Lisans sahibi", user),
            ("Lisans anahtarı", lic),
            ("Geçerlilik", "Süresiz (yerel lisans)"),
            ("Motor", ENGINE_NAME),
            ("İmza veritabanı", f"{datetime.date.today():%Y.%m.%d} (gömülü)"),
            ("Platform", ("Android" if IS_ANDROID else f"{_platform.system()} (test)") + f" · Python {_platform.python_version()}"),
            ("Sistem monitörü", "psutil" if HAS_PSUTIL else "/proc + MAV işlemi"),
        )
        for k, v in info:
            r = BoxLayout(orientation="vertical", size_hint_y=None, height=dp(40))
            r.add_widget(Lbl(k, size=10, color=C["muted"], size_hint_y=None, height=dp(14)))
            r.add_widget(Lbl(v, size=12, bold=True, size_hint_y=None, height=dp(22)))
            card.add_widget(r)
        card.add_widget(Lbl("Dahil özellikler", size=13, bold=True, color=C["cyan"], size_hint_y=None, height=dp(30)))
        for ft in ("Hızlı / Tam / Özel klasör tarama", "Gerçek zamanlı kalkan", "Karantina yöneticisi",
                   "Canlı CPU / RAM monitörü", "İmza + sezgisel analiz motoru"):
            card.add_widget(Lbl("+  " + ft, size=12, wrap=True))
        card.add_widget(Lbl("Not: MAVS, imza ve sezgisel analiz yapan yerel bir prototip motordur; ticari mobil "
                            "güvenlik ürünlerinin yerini tutmaz. Lisans doğrulaması çevrimdışı ve yereldir.",
                            size=10, color=C["muted"], wrap=True))
        body.add_widget(card)
        body.add_widget(Btn("Güncellemeleri Kontrol Et", size=13, on_release=lambda *a: app.show_dialog(
            "Güncelleme", "Çevrimiçi güncelleme sunucusu yapılandırılmamış. Yerel sürüm ve gömülü imzalar güncel.")))
        body.add_widget(Btn("Oturumu Kapat", size=13, base="#16213F", fg=C["text"],
                            on_release=lambda *a: app.logout()))


class MainView(BoxLayout):
    NAV = (("dash", "Panel"), ("scan", "Tarama"), ("quar", "Karantina"), ("lic", "Lisans"))

    def __init__(self, app, user, **kw):
        super().__init__(orientation="vertical", **kw)
        self.app = app
        self.current = "dash"

        hdr = Card(bg=C["header"], border=C["header"], radius=0, orientation="horizontal", size_hint_y=None,
                   height=dp(54), padding=[dp(10), dp(6)], spacing=dp(8))
        hdr.add_widget(Logo(size_hint=(None, 1), width=dp(40)))
        hdr.add_widget(Lbl("MAV", size=17, bold=True, color=C["cyan"], size_hint_x=None, width=dp(48)))
        hdr.add_widget(Widget())
        badge = Card(bg="#0C1E3D", border="#0C1E3D", radius=14, size_hint=(None, None), height=dp(28),
                     width=dp(min(230, 80 + 7 * len(user))), pos_hint={"center_y": .5})
        badge.add_widget(Lbl(f"Kullanıcı: {user} | MAVM Pro", size=11, bold=True, color=C["cyan"], align="center"))
        hdr.add_widget(badge)
        self.add_widget(hdr)

        self.sm = ScreenManager(transition=FadeTransition(duration=0.12))
        self.pages = {
            "dash": DashboardPage(app), "scan": ScanPage(app),
            "quar": QuarantinePage(app), "lic": LicensePage(app, user),
        }
        for p in self.pages.values():
            self.sm.add_widget(p)
        self.add_widget(self.sm)

        nav = Card(bg=C["header"], border=C["border"], radius=0, orientation="horizontal", size_hint_y=None,
                   height=dp(58), padding=[dp(4), dp(4)], spacing=dp(4))
        self.nav_btns = {}
        for key, label in self.NAV:
            b = Btn(label, size=13, height=dp(50), base=C["header"], down="#0F2447", fg=C["muted"], radius=10,
                    on_release=lambda *a, k=key: self.show(k))
            b.size_hint_y = 1
            self.nav_btns[key] = b
            nav.add_widget(b)
        self.add_widget(nav)
        self.show("dash")

    def show(self, key):
        self.current = key
        self.sm.current = key
        for k, b in self.nav_btns.items():
            if k == key:
                b.set_colors("#0F2447", "#14305E", C["cyan"])
            else:
                b.set_colors(C["header"], "#0F2447", C["muted"])
        if key == "quar":
            self.pages["quar"].refresh()

    def set_quar_count(self, n):
        self.nav_btns["quar"].text = f"Karantina ({n})" if n else "Karantina"


# ---------------------------------------------------------------- UYGULAMA
class MavApp(App):
    title = "MAV"

    def build(self):
        Window.clearcolor = rgba(C["bg"])
        try:
            Window.softinput_mode = "below_target"
        except Exception:
            pass
        init_paths(self.user_data_dir)
        self.auth = AuthManager()
        self.quarantine = Quarantine()
        self.sysmon = SysMon()
        self.events = queue.Queue()
        self.terminals = []
        self.log_hist = deque(maxlen=200)
        self.scan_job = None
        self.scan_stop = threading.Event()
        self.shield = None
        self.watch_dir = default_watch_dir()
        self.auto_q = True
        self.pending = []
        self.total_scanned = 0
        self.total_threats = 0
        self.last_scan = "-"
        self.user = None
        self.main = None
        self._dialog = None
        self._storage_ok = storage_granted()

        self.sm = ScreenManager(transition=FadeTransition(duration=0.2))
        self.auth_view = AuthView(self)
        s1 = Screen(name="auth")
        s1.add_widget(self.auth_view)
        self.main_screen = Screen(name="main")
        self.sm.add_widget(s1)
        self.sm.add_widget(self.main_screen)
        Window.bind(on_keyboard=self._on_key)
        Clock.schedule_interval(self._pump, 0.1)
        Clock.schedule_interval(self._tick, 1.0)
        return self.sm

    # --- yaşam döngüsü
    def on_pause(self):
        return True

    def on_resume(self):
        ok = storage_granted()
        if ok and not self._storage_ok:
            self.log("ok", "[SİSTEM] Dosya erişimi verildi.")
            if self.shield is not None:
                self.set_shield(False, quiet=True)
                self.set_shield(True)
        self._storage_ok = ok

    def on_stop(self):
        self.scan_stop.set()
        if self.shield:
            self.shield.stop_evt.set()

    def _on_key(self, window, key, *args):
        if key != 27:
            return False
        if self._dialog is not None:
            self.close_dialog()
            return True
        if self.main and self.main.current != "dash":
            self.main.show("dash")
            return True
        if self.main and minimize_app():
            return True
        return False

    # --- günlük & olay kuyruğu
    def register_terminal(self, term):
        self.terminals.append(term)
        for lvl, line in self.log_hist:
            term.append(line, lvl)

    def log(self, level, msg):
        self.events.put(("log", level, msg))

    def _write_log(self, level, msg):
        line = f"[{time.strftime('%H:%M:%S')}] {msg}"
        if level != "scan":
            self.log_hist.append((level, line))
        for t in list(self.terminals):
            t.append(line, level)

    def _pump(self, dt):
        try:
            for _ in range(300):
                self._handle(self.events.get_nowait())
        except queue.Empty:
            pass
        except Exception as ex:  # arayüz çökmesin
            import traceback
            traceback.print_exc()
            print("event error:", ex)

    def _tick(self, dt):
        if not self.main:
            return
        try:
            cpu, ram, info, src = self.sysmon.sample()
            self.main.pages["dash"].on_sample(cpu, ram, info, src)
        except Exception as ex:
            print("sample error:", ex)

    def _handle(self, ev):
        k = ev[0]
        if k == "log":
            self._write_log(ev[1], ev[2])
            return
        m = self.main
        if k == "progress" and m:
            m.pages["scan"].update_progress(ev[1])
        elif k == "phase" and m:
            m.pages["scan"].set_phase(ev[1])
        elif k == "scan_threat":
            self._add_pending(ev[1])
        elif k == "scan_done":
            self._on_scan_done(ev[1])
        elif k == "shield_scanned":
            self.total_scanned += 1
        elif k == "shield_threat":
            self.total_threats += 1
            if self.auto_q:
                self.quarantine_records([ev[1]])
            else:
                self._add_pending(ev[1])
                self.log("warn", "[KALKAN] Tehdit karantina bekliyor (otomatik karantina kapalı).")

    # --- oturum
    def login_success(self, display):
        self.user = display
        self.main = MainView(self, display)
        self.main_screen.clear_widgets()
        self.main_screen.add_widget(self.main)
        self.sm.current = "main"
        self.log("sys", f"[SİSTEM] MAV Mobil {APP_VERSION} başlatıldı · Hoş geldiniz, {display}.")
        self.log("info", f"[SİSTEM] Motor: {ENGINE_NAME}")
        self.set_shield(True)
        self.refresh_status()
        if IS_ANDROID and not storage_granted():
            Clock.schedule_once(lambda dt: self.ask_storage(), 0.6)

    def logout(self):
        self.stop_scan()
        self.set_shield(False, quiet=True)
        self.user = None
        self.pending.clear()
        self.terminals.clear()
        self.main = None
        self.main_screen.clear_widgets()
        self.auth_view.reset()
        self.sm.current = "auth"

    def ask_storage(self):
        self.show_dialog(
            "Dosya erişimi gerekli",
            "MAV'ın telefonunuzdaki dosyaları tarayabilmesi için 'Tüm dosyalara erişim' izni gerekir. "
            "İzin Ver'e dokunun ve açılan ayarlarda MAV için izni açın.",
            [("Sonra", None, "ghost"), ("İzin Ver", request_storage, "primary")])

    # --- durum
    def refresh_status(self):
        m = self.main
        if not m:
            return
        m.pages["dash"].update_status()
        m.pages["dash"].refresh_stats()
        m.pages["scan"].set_pending(len(self.pending))
        m.set_quar_count(len(self.quarantine.items))

    def _add_pending(self, rec):
        if any(p["path"] == rec["path"] for p in self.pending):
            return
        self.pending.append(rec)
        self.refresh_status()

    def quarantine_pending(self):
        self.quarantine_records(list(self.pending))

    def quarantine_records(self, recs):
        done = set()
        for rec in recs:
            ok, msg = self.quarantine.add(rec)
            self.log("ok" if ok else "warn", f"[KARANTİNA] {msg}")
            if ok or not os.path.exists(rec["path"]):
                done.add(rec["path"])
        self.pending = [p for p in self.pending if p["path"] not in done]
        self.refresh_status()
        if self.main and self.main.current == "quar":
            self.main.pages["quar"].refresh()

    # --- tarama
    def goto_scan(self, mode):
        if self.main:
            self.main.show("scan")
        self.scan_action(mode)

    def scan_action(self, mode):
        if self.scan_job and self.scan_job.is_alive():
            self.show_dialog("Tarama sürüyor", "Zaten çalışan bir tarama var. Bitmesini bekleyin veya durdurun.")
            return
        if IS_ANDROID and not storage_granted():
            self.ask_storage()
            return
        if mode == "quick":
            self.start_scan("quick", quick_roots(), "Hızlı Tarama")
        elif mode == "full":
            self.show_dialog(
                "Tam taramayı başlat?",
                "Telefondaki tüm dosyalar taranacak. Bu işlem uzun sürebilir ve pil tüketir; istediğiniz an durdurabilirsiniz.",
                [("Vazgeç", None, "ghost"),
                 ("Başlat", lambda: self.start_scan("full", local_roots(), "Tam Tarama"), "primary")])
        else:
            self.pick_folder("Taranacak klasörü seçin", ext_storage(),
                             lambda p: self.start_scan("custom", [p], "Özel Klasör Taraması"))

    def start_scan(self, mode, roots, title):
        if not roots or not self.main:
            return
        self.main.show("scan")
        self.scan_stop = threading.Event()
        self.scan_job = ScanJob(mode, roots, self.events.put, self.scan_stop)
        self.main.pages["scan"].begin(title)
        self.log("sys", f"[SİSTEM] {title} başlatıldı: {', '.join(short_path(r, 30) for r in roots)}")
        self.scan_job.start()

    def stop_scan(self):
        if self.scan_job and self.scan_job.is_alive():
            self.scan_stop.set()
            self.log("warn", "[SİSTEM] Tarama durduruluyor...")

    def _on_scan_done(self, d):
        self.scan_job = None
        self.total_scanned += d["scanned"]
        self.total_threats += d["threats"]
        self.last_scan = time.strftime("%d.%m %H:%M")
        state = "durduruldu" if d["stopped"] else "tamamlandı"
        self.log("threat" if d["threats"] else "ok",
                 f"[SİSTEM] Tarama {state}: {d['scanned']} dosya, {d['threats']} tehdit, "
                 f"{d['skipped']} atlanan, süre {fmt_dur(d['elapsed'])}")
        if self.main:
            self.main.pages["scan"].finish(d)
        if d["threats"] and self.auto_q:
            self.quarantine_pending()
        self.refresh_status()
        if not d["stopped"]:
            msg = (f"{d['scanned']} dosya tarandı.\n{d['threats']} tehdit/şüpheli öğe bulundu."
                   + ("\nOtomatik karantina uygulandı." if d["threats"] and self.auto_q else ""))
            self.show_dialog("Tarama Tamamlandı", msg, danger=bool(d["threats"]))

    def create_test_file(self, folder):
        folder = Path(folder)
        folder.mkdir(parents=True, exist_ok=True)
        p = folder / "MAV_Test_Tehdit.txt"
        p.write_bytes(MAV_TEST + b"\r\nBu dosya MAV algilama motorunu test etmek icin olusturuldu. Zararsizdir.\r\n")
        return p

    def test_scan(self):
        if self.scan_job and self.scan_job.is_alive():
            return
        try:
            p = self.create_test_file(TEST_DIR)
        except OSError as e:
            self.show_dialog("Hata", f"Test dosyası oluşturulamadı: {e}")
            return
        self.log("sys", f"[SİSTEM] Test dosyası oluşturuldu: {p}")
        self.start_scan("custom", [str(TEST_DIR)], "Test Taraması")

    # --- kalkan
    def toggle_shield(self):
        self.set_shield(not (self.shield is not None and self.shield.is_alive()))

    def toggle_auto_q(self):
        self.auto_q = not self.auto_q
        self.log("info", f"[SİSTEM] Otomatik karantina {'açık' if self.auto_q else 'kapalı'}.")
        self.refresh_status()

    def set_shield(self, on, quiet=False):
        if on:
            if self.shield and self.shield.is_alive():
                return
            if not os.path.isdir(self.watch_dir):
                self.watch_dir = str(DATA_DIR)
            self.shield = Shield(self.watch_dir, self.events.put)
            self.shield.start()
        else:
            if self.shield:
                self.shield.stop_evt.set()
            self.shield = None
        if not quiet:
            Clock.schedule_once(lambda dt: self.refresh_status(), 0.15)

    def choose_watch_dir(self):
        self.pick_folder("İzlenecek klasörü seçin", self.watch_dir if os.path.isdir(self.watch_dir) else ext_storage(),
                         self._set_watch_dir)

    def _set_watch_dir(self, folder):
        self.watch_dir = os.path.normpath(folder)
        was_on = self.shield is not None and self.shield.is_alive()
        self.set_shield(False, quiet=True)
        if was_on:
            self.set_shield(True)
        self.log("sys", f"[SİSTEM] İzlenen klasör değiştirildi: {self.watch_dir}")
        self.refresh_status()

    def test_shield(self):
        if not (self.shield and self.shield.is_alive()):
            self.show_dialog("Kalkan kapalı", "Test için önce Gerçek Zamanlı Korumayı açın.")
            return
        try:
            p = self.create_test_file(self.watch_dir)
            self.log("sys", f"[SİSTEM] Test dosyası izlenen klasöre bırakıldı: {p.name} (birkaç saniye içinde algılanır)")
        except OSError as e:
            self.show_dialog("Hata", f"Test dosyası yazılamadı: {e}")

    # --- diyaloglar
    def close_dialog(self):
        d, self._dialog = self._dialog, None
        if d is not None:
            try:
                d.dismiss()
            except Exception:
                pass

    def _popup(self, content, size_hint, height=None, title=""):
        pop = Popup(title=title, content=content, size_hint=size_hint, auto_dismiss=False,
                    background="", background_color=rgba("#0E1430"), separator_color=rgba(C["cyan"]),
                    title_color=rgba(C["cyan"]), title_size=sp(15))
        if height is not None:
            pop.size_hint_y = None
            pop.height = height
        self._dialog = pop
        pop.open()
        return pop

    def show_dialog(self, title, message, buttons=None, danger=False):
        self.close_dialog()
        col = C["danger"] if danger else C["cyan"]
        content = BoxLayout(orientation="vertical", padding=dp(16), spacing=dp(12), size_hint_y=None)
        content.bind(minimum_height=content.setter("height"))
        content.add_widget(Lbl(title, size=18, bold=True, color=col, wrap=True))
        content.add_widget(Lbl(message, size=13, wrap=True))
        row = BoxLayout(size_hint_y=None, height=dp(44), spacing=dp(8))
        styles = {"primary": (C["cyan"], "#00131A"), "danger": ("#8A1F2D", C["text"]), "ghost": ("#16213F", C["text"])}
        for label, cb, style in (buttons or [("Tamam", None, "primary")]):
            base, fg = styles[style]

            def _click(*a, cb=cb):
                self.close_dialog()
                if cb:
                    cb()
            row.add_widget(Btn(label, size=13, height=dp(44), base=base, fg=fg, on_release=_click))
        content.add_widget(row)
        pop = self._popup(content, (.92, None), height=dp(220))
        content.bind(height=lambda inst, h: setattr(pop, "height", h + dp(34)))

    def pick_folder(self, title, start, callback):
        self.close_dialog()
        if not os.path.isdir(start):
            start = ext_storage() if os.path.isdir(ext_storage()) else "/"
        content = BoxLayout(orientation="vertical", spacing=dp(8), padding=dp(8))
        path_lbl = Lbl(start, size=10, mono=True, color=C["muted"], size_hint_y=None, height=dp(30),
                       shorten=True, shorten_from="left")
        content.add_widget(path_lbl)
        fc = FileChooserListView(path=start, dirselection=True,
                                 filters=[lambda folder, name: os.path.isdir(os.path.join(folder, name))])
        fc.bind(path=lambda inst, p: setattr(path_lbl, "text", p))
        content.add_widget(fc)
        row = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(8))

        def _pick(*a):
            p = fc.path
            self.close_dialog()
            callback(p)
        row.add_widget(Btn("İptal", size=13, height=dp(46), base="#16213F", fg=C["text"],
                           on_release=lambda *a: self.close_dialog()))
        row.add_widget(Btn("Bu klasörü seç", size=13, height=dp(46), on_release=_pick))
        content.add_widget(row)
        self._popup(content, (.96, .92), title=title)


def main():
    MavApp().run()


if __name__ == "__main__":
    main()
