# Root Makefile - Platform dispatcher
#
# Usage:
#   make                - Build for current platform (auto-detect)
#   make windows        - Build for Windows
#   make linux          - Build for Linux  
#   make macos          - Build for macOS
#   make zig-build      - Build with zig for current platform
#   make docker-linux   - Build Linux in Docker container
#   make linux-appimage - Build Linux AppImage (portable, all distros)
#   make clean          - Clean all platforms
#   make distrib        - Create distribution package

# Detect platform (defaults to Windows if unknown)
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Linux)
    PLATFORM := linux
else ifeq ($(UNAME_S),Darwin)
    PLATFORM := macos
else
    PLATFORM := windows
endif

# Default target - build for detected platform
all:
	@echo "Building for $(PLATFORM)..."
	@$(MAKE) -f build/make/Makefile.$(PLATFORM)

# Platform-specific targets
windows:
	@echo "Building for Windows..."
	@$(MAKE) -f build/make/Makefile.windows

linux:
	@echo "Building for Linux..."
	@$(MAKE) -f build/make/Makefile.linux

macos:
	@echo "Building for macOS..."
	@$(MAKE) -f build/make/Makefile.macos

# Clean for all platforms
clean:
	@echo "Cleaning all platforms..."
	@$(MAKE) -f build/make/Makefile.windows clean 2>/dev/null || true
	@$(MAKE) -f build/make/Makefile.linux clean 2>/dev/null || true
	@$(MAKE) -f build/make/Makefile.macos clean 2>/dev/null || true

# Distribution target (delegates to platform-specific Makefile)
distrib:
	@echo "Creating distribution for $(PLATFORM)..."
	@$(MAKE) -f build/make/Makefile.$(PLATFORM) distrib

# Helper targets (delegates to platform-specific Makefile)
amod:
	@$(MAKE) -f build/make/Makefile.$(PLATFORM) amod

convert:
	@$(MAKE) -f build/make/Makefile.$(PLATFORM) convert

anicopy:
	@$(MAKE) -f build/make/Makefile.$(PLATFORM) anicopy

# Code quality targets
sanitizer:
	@echo "Building with AddressSanitizer/UBSan for $(PLATFORM)..."
	@$(MAKE) -f build/make/Makefile.$(PLATFORM) sanitizer

coverage:
	@echo "Building with coverage instrumentation for $(PLATFORM)..."
	@$(MAKE) -f build/make/Makefile.$(PLATFORM) coverage

# Zig build target
zig-build:
	cp build/build.zig .
	zig build --release=fast install --prefix .
	rm -f build.zig

# Docker build for Linux
docker-linux:
	cp build/containers/Dockerfile.linux .
	docker build -f Dockerfile.linux -t astonia-linux-build .
	docker run --rm -i -e HOST_UID=$(shell id -u) -e HOST_GID=$(shell id -g) -v "$(PWD):/app" -w /app astonia-linux-build
	rm -f Dockerfile.linux

docker-windows:
	docker build -f Dockerfile.windows-build -t astonia-windows-build .
	docker run --rm -i -e HOST_UID=$(shell id -u) -e HOST_GID=$(shell id -g) -v "$(PWD):/app" -w /app astonia-windows-build

docker-windows-dev:
	docker build -f Dockerfile.windows-dev -t astonia-windows-dev .
	docker run --rm -it -e HOST_UID=$(shell id -u) -e HOST_GID=$(shell id -g) -v "$(PWD):/app" -w /app astonia-windows-dev

docker-linux-dev:
	docker build -f Dockerfile.linux-dev -t astonia-linux-dev .
	docker run --rm -it -e HOST_UID=$(shell id -u) -e HOST_GID=$(shell id -g) -v "$(PWD):/app" -w /app astonia-linux-dev

# Build Linux AppImage (portable, works on all distributions)
appimage:
	@echo "Building Linux AppImage..."
	cp build/containers/Dockerfile.appimage .
	docker build -f Dockerfile.appimage -t astonia-appimage-build .
	rm -f Dockerfile.appimage
	docker run --rm -e HOST_UID=$(shell id -u) -e HOST_GID=$(shell id -g) -v "$(PWD):/output" astonia-appimage-build
	mv astonia-client-*.AppImage astonia-client.AppImage
	@echo ""
	@echo "============================================"
	@echo "AppImage created successfully!"
	@echo "============================================"
	@echo ""
	@echo "To run: chmod +x astonia-client.AppImage && ./astonia-client.AppImage"

zen4-appimage:
	@echo "Building Linux AppImage..."
	cp build/containers/Dockerfile.appimage .
	docker build -f Dockerfile.appimage -t astonia-appimage-build --build-arg ZEN4=1 .
	rm -f Dockerfile.appimage
	docker run --rm -e HOST_UID=$(shell id -u) -e HOST_GID=$(shell id -g) -v "$(PWD):/output" astonia-appimage-build
	mv astonia-client-*.AppImage astonia-client-zen4.AppImage
	@echo ""
	@echo "============================================"
	@echo "Zen4 AppImage created successfully!"
	@echo "============================================"
	@echo ""
	@echo "To run: chmod +x astonia-client-zen4.AppImage && ./astonia-client.AppImage"

# Include quality checks makefile (see build/make/Makefile.quality)
include build/make/Makefile.quality

.PHONY: all windows linux macos clean distrib amod convert anicopy zig-build docker-linux docker-windows docker-windows-dev docker-linux-dev appimage zen4-appimage sanitizer coverage
