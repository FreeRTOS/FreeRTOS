#include <errno.h>
#include <sys/stat.h>

int
_fstatat(int dirfd, const char *file, struct stat *st, int flags)
{
  errno = ENOSYS;
  return -1;
}
