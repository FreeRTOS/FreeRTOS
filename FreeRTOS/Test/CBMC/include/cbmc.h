/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

/*
 * CBMC models a pointer as an object id and an offset into that
 * object.  The top bits of a pointer encode the object id and the
 * remaining bits encode the offset.  This means there is a bound on
 * the maximum offset into an object in CBMC, and hence a bound on the
 * size of objects in CBMC.
 */
#define CBMC_BITS               7
#define CBMC_MAX_OBJECT_SIZE    ( 0xFFFFFFFF >> ( CBMC_BITS + 1 ) )

#define IMPLIES( a, b )    ( !( a ) || ( b ) )

BaseType_t nondet_basetype();
UBaseType_t nondet_ubasetype();
TickType_t nondet_ticktype();
int32_t nondet_int32();
uint32_t nondet_uint32();
size_t nondet_sizet();

#define nondet_BaseType()    nondet_basetype()

void * safeMalloc( size_t size );


enum CBMC_LOOP_CONDITION
{
    CBMC_LOOP_BREAK, CBMC_LOOP_CONTINUE, CBMC_LOOP_RETURN
};

/* CBMC specification: capture old value for precondition and */
/* postcondition checking */

#define OLDVAL( var )              _old_ ## var
#define SAVE_OLDVAL( var, typ )    const typ OLDVAL( var ) = var

/* CBMC specification: capture old value for values passed by */
/* reference in function abstractions */

#define OBJ( var )                 ( * var )
#define OLDOBJ( var )              _oldobj_ ## var
#define SAVE_OLDOBJ( var, typ )    const typ OLDOBJ( var ) = OBJ( var )

/* CBMC debugging: printfs for expressions */

#define __CPROVER_printf( var )          { uint32_t ValueOf_ ## var = ( uint32_t ) var; }
#define __CPROVER_printf2( str, exp )    { uint32_t ValueOf_ ## str = ( uint32_t ) ( exp ); }

/* CBMC debugging: printfs for pointer expressions */

#define __CPROVER_printf_ptr( var )          { uint8_t * ValueOf_ ## var = ( uint8_t * ) var; }
#define __CPROVER_printf2_ptr( str, exp )    { uint8_t * ValueOf_ ## str = ( uint8_t * ) ( exp ); }

/*
 * An assertion that pvPortMalloc returns NULL when asked to allocate 0 bytes.
 * This assertion is used in some of the TaskPool proofs.
 */
#define __CPROVER_assert_zero_allocation()       \
    __CPROVER_assert( pvPortMalloc( 0 ) == NULL, \
                      "pvPortMalloc allows zero-allocated memory." )

/*
 * A stub for pvPortMalloc that nondeterministically chooses to return
 * either NULL or an allocation of the requested space.  The stub is
 * guaranteed to return NULL when asked to allocate 0 bytes.
 * This stub is used in some of the TaskPool proofs.
 */
void * pvPortMalloc( size_t xWantedSize )
{
    if( xWantedSize == 0 )
    {
        return NULL;
    }

    return nondet_bool() ? malloc( xWantedSize ) : NULL;
}

void vPortFree( void * pv )
{
    ( void ) pv;
    free( pv );
}
