#include "cbmc.h"

/****************************************************************
 * Model a malloc that can fail (CBMC malloc does not fail) and
 * check that CBMC can model an object of the requested size.
 ****************************************************************/

void * safeMalloc( size_t size )
{
    __CPROVER_assert( size < CBMC_MAX_OBJECT_SIZE, "safeMalloc size too big" );
    return nondet_bool() ? NULL : malloc( size );
}
