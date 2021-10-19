#include <errno.h>
#include <sys/types.h>

ssize_t _read(int file, void *ptr, size_t len) {
    errno = ENOSYS;
    return -1;
}
