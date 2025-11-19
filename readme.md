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

## Build from Source

### Windows Build
If you wish to build your own, install https://www.msys2.org/

Make sure that "c:\msys64\clang64\bin" and "C:\msys64\usr\bin" (if you installed
into the default directory) end up in your Windows PATH.

Open a shell (CMD.EXE or Powershell) and run

```
pacman -S mingw-w64-clang-x86_64-clang mingw-w64-clang-x86_64-SDL2 mingw-w64-clang-x86_64-libpng
pacman -S mingw-w64-clang-x86_64-SDL2_mixer mingw-w64-clang-x86_64-libzip make zip
pacman -S mingw-w64-clang-x86_64-dwarfstack mingw-w64-clang-x86_64-zig
```

to install the 64 bit Clang compiler toolchain, libraries, make, zip, and Zig.

#### Install Rust
In the MSYS2 shell, install Rust using:
```
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain stable --target x86_64-pc-windows-gnu
```

Also install git lfs (large file system) as described here: https://docs.github.com/en/repositories/working-with-files/managing-large-files/installing-git-large-file-storage

Clone or download the sources from Github to the current directory.

#### Build with Make
```
make           # Auto-detects platform and builds
make windows   # or make linux, make macos
make zig-build # Build with zig
```

Build files: `build/build.zig`, `build/make/` (Makefiles).

### Errors
If pacman, make, clang, or zig are not found something with your MSYS2 installation
went wrong. The same goes for missing headers during compile or missing
libraries during linking. And even missing DLLs when running the client point
to an incomplete MSYS2 installation.

### Make Distribution
```
make distrib
```
Will copy all neccessary DLLs to the build directory and create a zip archive
with the executables and graphics.

### Linux Build
```
make               # Native Linux build
make zig-build     # Native Linux build using zig
make docker-linux  # Build in Docker container
```

### macOS Build

#### Prerequisites
Install Xcode Command Line Tools:
```
xcode-select --install
```

#### Install Dependencies

**Option 1: SDL2**
```
brew install zig sdl2 sdl2_mixer libpng zlib libzip
```

**Option 2: SDL3 with SDL2-compat**
SDL2-compat provides SDL2 API compatibility while using SDL3 underneath:
```
brew install zig sdl2_mixer sdl3 libpng zlib libzip
```

# Build and install SDL2-compat

```
git clone https://github.com/libsdl-org/sdl2-compat
cd sdl2-compat
cmake -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build
sudo cmake --install build
cd ..
```

#### Install Rust

```
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source $HOME/.cargo/env
rustup target add aarch64-apple-darwin
```

#### Build
```
make           # Auto-detects macOS
make zig-build # Build with zig
```

### Make A Mod
```
make amod
```
To compile your mod (located in src/amod/). More information about modding the
client is on my website: https://brockhaus.org/modding.html
