#include <stdio.h>

/*
 * fcntl -- Manipulate a file descriptor.
 *          We don't have a filesystem, so we do nothing.
 */
int fcntl (int fd, int cmd, long arg)
{
  (void) fd;
  (void) cmd;
  (void) arg;
  return 0;
}
