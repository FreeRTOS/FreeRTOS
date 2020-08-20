#include <sys/types.h>
#include <errno.h>

int
_chown(const char *path, uid_t owner, gid_t group)
{
  errno = ENOSYS;
  return -1;
}
