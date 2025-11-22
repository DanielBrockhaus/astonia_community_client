# Astonia Community Client

This is the community client for Astonia 3. It is based on, and compatible
with, the [client maintained by Daniel Brockhaus](https://github.com/DanielBrockhaus/astonia_client).

The main goal is to allow community driven development.

Further goals:

- Maintain backwards compatibility with the original game server.
- Maintain compatibility with all servers currently using the client.
- Keep it simple. No additional libraries, frameworks or tools unless absolutely needed.
- Whenever possible, put bugfixes in single commits for easy cherry-picking.
- Always have a downloadable Windows release with sensible hardware requirements and no software requirements.
- Work towards supporting more / all of the servers.

## Build

### Windows

Install [MSYS2](https://www.msys2.org/). It comes with three shells, launch the clang 64 one (not aarch64).

Install dependencies:
```bash
pacman -Syu
pacman -Sy mingw-w64-clang-x86_64-clang mingw-w64-clang-x86_64-SDL2 mingw-w64-clang-x86_64-libpng mingw-w64-clang-x86_64-SDL2_mixer mingw-w64-clang-x86_64-libzip make zip mingw-w64-clang-x86_64-dwarfstack mingw-w64-clang-x86_64-zig mingw-w64-clang-x86_64-rustup
rustup toolchain install stable-x86_64-pc-windows-gnu
rustup default stable-x86_64-pc-windows-gnu
```

### Linux

Install dependencies:
```bash
sudo pacman -S base-devel sdl3 sdl2-compat sdl2_mixer libpng libzip zlib zig rust
```

Or use Docker (no dependencies needed):
```bash
make docker-linux
```

### macOS

Install Xcode Command Line Tools:
```bash
xcode-select --install
```

Install dependencies:
```bash
brew install zig sdl2 sdl2_mixer libpng zlib libzip rust
```

## Commands

```bash
make            # Build for current platform
make zig-build  # Build using Zig
make distrib    # Create distribution package
make amod       # Build mod (src/amod/)
make clean      # Clean up build assets
```
