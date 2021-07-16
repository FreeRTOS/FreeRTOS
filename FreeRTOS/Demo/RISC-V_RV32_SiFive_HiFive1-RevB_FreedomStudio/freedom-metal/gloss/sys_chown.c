#include <errno.h>
#include <sys/types.h>

int _chown(const char *path, uid_t owner, gid_t group) {
    errno = ENOSYS;
    return -1;
}
