/* The errno variable is stored in the reentrancy structure.  This
   function returns its address for use by the macro errno defined in
   errno.h.  */

#include <errno.h>
#include <reent.h>
#include "xil_types.h"
sint32 * __errno (void);

sint32 *
__errno (void)
{
  return &_REENT->_errno;
}
