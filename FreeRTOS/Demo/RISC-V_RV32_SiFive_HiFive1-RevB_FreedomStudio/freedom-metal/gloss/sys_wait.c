#include <errno.h>

int _wait(int *status) {
    errno = ENOSYS;
    return -1;
}
