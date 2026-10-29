[app]
title = MAV
package.name = mavm
package.domain = org.mavs
source.dir = .
source.include_exts = py
source.exclude_dirs = bin, .buildozer, .github, __pycache__
version = 1.0.0

# psutil gerekmez: sistem monitörü /proc üzerinden okunur, olmazsa MAV işlemi ölçülür.
requirements = python3,kivy==2.3.0

orientation = portrait
fullscreen = 0

# Dosya tarama için depolama izinleri (Android 11+ için MANAGE_EXTERNAL_STORAGE ayrıca kullanıcıdan istenir)
android.permissions = READ_EXTERNAL_STORAGE,WRITE_EXTERNAL_STORAGE,MANAGE_EXTERNAL_STORAGE
android.api = 33
android.minapi = 24
android.ndk = 25b
android.archs = arm64-v8a, armeabi-v7a
android.accept_sdk_license = True
android.allow_backup = False

[buildozer]
log_level = 2
warn_on_root = 1
