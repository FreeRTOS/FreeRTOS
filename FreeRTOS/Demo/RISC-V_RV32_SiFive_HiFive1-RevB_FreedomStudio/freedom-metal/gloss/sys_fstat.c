#include <errno.h>
#include <sys/stat.h>

int _fstat(int file, struct stat *st) {
    errno = -ENOSYS;
    return -1;
}
