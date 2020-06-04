#include <unistd.h>
#include <time.h>

/* Get configurable system variables.  */

long
_sysconf(int name)
{
  switch (name)
    {
    case _SC_CLK_TCK:
      return CLOCKS_PER_SEC;
    }

  return -1;
}
