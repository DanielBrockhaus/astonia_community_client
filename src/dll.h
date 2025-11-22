#ifdef _WIN32
// On Windows, always use __declspec for DLL exports (works with all compilers)
#define DLL_EXPORT __declspec(dllexport)
#define DLL_IMPORT __declspec(dllimport)
#else
// On Unix-like systems, use visibility attributes for GCC/Clang
#if __GNUC__ >= 4 || defined(__clang__)
#define DLL_EXPORT __attribute__((visibility("default")))
// Imports resolve via the dynamic linker, so no attribute is required
#define DLL_IMPORT
#else
#define DLL_EXPORT
#define DLL_IMPORT
#endif
#endif