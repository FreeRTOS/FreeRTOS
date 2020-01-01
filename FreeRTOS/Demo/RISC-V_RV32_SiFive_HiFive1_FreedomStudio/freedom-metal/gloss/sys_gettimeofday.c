#include <errno.h>
#include <metal/timer.h>
#include <sys/time.h>

int
_gettimeofday(struct timeval *tp, void *tzp)
{
    int rv;
    unsigned long long mcc, timebase;
    rv = metal_timer_get_cyclecount(0, &mcc);
    if (rv != 0) {
        return -1;
    }
    rv = metal_timer_get_timebase_frequency(0, &timebase);
    if (rv != 0) {
        return -1;
    }
    tp->tv_sec = mcc / timebase;
    tp->tv_usec = mcc % timebase * 1000000 / timebase;
    return 0;
}
