#include <time.h>
#include <unistd.h>

/* Get configurable system variables.  */

long _sysconf(int name) {
    switch (name) {
    case _SC_CLK_TCK:
        return CLOCKS_PER_SEC;
    }

    return -1;
}

extern __typeof(_sysconf) sysconf
    __attribute__((__weak__, __alias__("_sysconf")));
