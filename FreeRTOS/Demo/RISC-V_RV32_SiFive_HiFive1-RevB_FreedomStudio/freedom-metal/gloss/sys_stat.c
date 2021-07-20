#include <errno.h>
#include <sys/stat.h>

int _stat(const char *file, struct stat *st) {
    errno = ENOSYS;
    return -1;
}
