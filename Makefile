# Root Makefile - Platform dispatcher
#
# Usage:
#   make              - Build for current platform (auto-detect)
#   make windows      - Build for Windows
#   make linux        - Build for Linux  
#   make macos        - Build for macOS
#   make zig-build    - Build with zig for current platform
#   make docker-linux - Build Linux in Docker container
#   make clean        - Clean all platforms
#   make distrib      - Create distribution package

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

# Zig build target
zig-build:
	cp build/build.zig .
	zig build --release=fast install --prefix .
	rm -f build.zig

# Docker build for Linux
docker-linux:
	docker build -f Dockerfile.linux -t astonia-linux-build .
	docker run --rm -i -e HOST_UID=$(shell id -u) -e HOST_GID=$(shell id -g) -v "$(PWD):/app" -w /app astonia-linux-build

docker-windows:
	docker build -f Dockerfile.windows-build -t astonia-windows-build .
	docker run --rm -i -e HOST_UID=$(shell id -u) -e HOST_GID=$(shell id -g) -v "$(PWD):/app" -w /app astonia-windows-build

docker-windows-dev:
	docker build -f Dockerfile.windows-dev -t astonia-windows-dev .
	docker run --rm -it -e HOST_UID=$(shell id -u) -e HOST_GID=$(shell id -g) -v "$(PWD):/app" -w /app astonia-windows-dev

docker-linux-dev:
	docker build -f Dockerfile.linux-dev -t astonia-linux-dev .
	docker run --rm -it -e HOST_UID=$(shell id -u) -e HOST_GID=$(shell id -g) -v "$(PWD):/app" -w /app astonia-linux-dev

.PHONY: all windows linux macos clean distrib amod convert anicopy zig-build docker-linux docker-windows docker-windows-dev
