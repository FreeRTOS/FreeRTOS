#include <errno.h>

int _access(const char *file, int mode) {
    errno = ENOSYS;
    return -1;
}
