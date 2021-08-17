#include <errno.h>

int _openat(int dirfd, const char *name, int flags, int mode) {
    errno = ENOSYS;
    return -1;
}
