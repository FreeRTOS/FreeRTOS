#include <errno.h>

int _close(int file) {
    errno = ENOSYS;
    return -1;
}
