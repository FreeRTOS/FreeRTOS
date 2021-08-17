#include <errno.h>
#include <sys/types.h>

off_t _lseek(int file, off_t ptr, int dir) {
    errno = ENOSYS;
    return -1;
}
