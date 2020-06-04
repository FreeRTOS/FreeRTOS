#include <unistd.h>

int
_isatty(int file)
{
  return (file == STDOUT_FILENO);
}
