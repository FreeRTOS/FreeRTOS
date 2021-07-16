#include <errno.h>

int _open(const char *name, int flags, int mode) {
    errno = ENOSYS;
    return -1;
}
