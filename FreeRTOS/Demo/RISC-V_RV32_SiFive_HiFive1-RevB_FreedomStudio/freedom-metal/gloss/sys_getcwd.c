#include <errno.h>
#include <stddef.h>

char *_getcwd(char *buf, size_t size) {
    errno = -ENOSYS;
    return NULL;
}
