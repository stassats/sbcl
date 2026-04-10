#include "interr.h"
#include <stdio.h>

int
#if !(defined LISP_FEATURE_WIN32 && !defined __clang__)
__attribute__((weak))
#endif
main(int argc, char *argv[], char *envp[])
{
    extern int initialize_lisp(int argc, char *argv[], char *envp[]);
#ifdef TRACE_MMAP_SYSCALLS
    extern FILE* mmgr_debug_logfile;
    mmgr_debug_logfile = fopen("mman.log", "w");
#endif
    initialize_lisp(argc, argv, envp);
    lose("unexpected return from initial thread in main()");
    return 0;
}
