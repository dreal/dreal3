#pragma once
#define RP_PACKAGE "realpaver"
#define RP_SOFTWARE_NAME "realpaver"
#define RP_VERSION "1.0"

#ifdef __linux__
#define RP_SYSTEM_LINUX_IX86 1
#elif __APPLE__
#define RP_SYSTEM_POWERPC 1
#endif

#define RP_DEBUGGING_MODE 0
#define RP_PROFILING_MODE 0
