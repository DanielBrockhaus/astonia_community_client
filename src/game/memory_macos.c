#include <sys/sysctl.h>
#include <sys/resource.h>
#include <unistd.h>
#include <stdint.h>

uint64_t get_total_system_memory(void)
{
	uint64_t mem = 0;
	size_t length = sizeof(mem);

	if (sysctlbyname("hw.memsize", &mem, &length, NULL, 0) == 0 && length == sizeof(mem)) {
		return mem;
	}

	// TODO: Probably should return some indication of an error somehow.
	return 0;
}

size_t get_memory_usage(void)
{
	struct rusage r_usage;
	getrusage(RUSAGE_SELF, &r_usage);
	// On macOS, ru_maxrss is in bytes (not kilobytes like Linux)
	return r_usage.ru_maxrss;
}
