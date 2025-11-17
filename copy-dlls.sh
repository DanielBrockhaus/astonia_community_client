#!/bin/bash
# Copy all required Windows DLLs from Docker container to bin/

set -e

echo "Copying Windows DLLs from Docker container..."

docker run --rm -v "$(pwd):/workspace" -u "$(id -u):$(id -g)" astonia-windows-builder bash -c '
# Core SDL2 libraries
cp /usr/x86_64-w64-mingw32/sys-root/mingw/bin/SDL2.dll bin/
cp /usr/x86_64-w64-mingw32/sys-root/mingw/bin/SDL2_mixer.dll bin/
cp /usr/x86_64-w64-mingw32/sys-root/mingw/bin/SDL2_ttf.dll bin/

# Image libraries
cp /usr/x86_64-w64-mingw32/sys-root/mingw/bin/libpng16-16.dll bin/

# Compression libraries
cp /usr/x86_64-w64-mingw32/sys-root/mingw/bin/zlib1.dll bin/
cp /usr/x86_64-w64-mingw32/sys-root/mingw/bin/libzip-5.dll bin/
cp /usr/x86_64-w64-mingw32/sys-root/mingw/bin/libbz2-1.dll bin/

# Font rendering
cp /usr/x86_64-w64-mingw32/sys-root/mingw/bin/libfreetype-6.dll bin/
cp /usr/x86_64-w64-mingw32/sys-root/mingw/bin/libharfbuzz-0.dll bin/

# Runtime dependencies
cp /usr/x86_64-w64-mingw32/sys-root/mingw/bin/libgcc_s_seh-1.dll bin/
cp /usr/x86_64-w64-mingw32/sys-root/mingw/bin/libwinpthread-1.dll bin/
cp /usr/x86_64-w64-mingw32/sys-root/mingw/bin/libglib-2.0-0.dll bin/
cp /usr/x86_64-w64-mingw32/sys-root/mingw/bin/libintl-8.dll bin/
cp /usr/x86_64-w64-mingw32/sys-root/mingw/bin/libpcre2-8-0.dll bin/
cp /usr/x86_64-w64-mingw32/sys-root/mingw/bin/libiconv-2.dll bin/

# Optional: graphite2 for advanced font shaping
cp /usr/x86_64-w64-mingw32/sys-root/mingw/bin/libgraphite2.dll bin/ 2>/dev/null || true
'

echo ""
echo "✓ DLL copy complete!"
echo ""
echo "DLLs in bin/:"
ls -lh bin/*.dll | awk '{print "  " $9 " (" $5 ")"}'
echo ""
echo "Total DLLs: $(ls -1 bin/*.dll | wc -l)"
