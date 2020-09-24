#include "platform.h"
#include <stdlib.h>

#if BSP_CFG_RTOS_USED != 0

/* Replacement to be thread-safe (in case of other than using heap_3.c). */
void *malloc( size_t xWantedSize )
{
#if BSP_CFG_RTOS_USED == 1
    /* FreeRTOS */

    return pvPortMalloc( xWantedSize );
#else
    /* SEGGER embOS */
    /* Micrium MicroC/OS */
    /* Renesas RI600V4 & RI600PX */

    #error "Unsupported RTOS is selected."
#endif
}

/* Replacement to be thread-safe (in case of other than using heap_3.c). */
void free( void *pv )
{
#if BSP_CFG_RTOS_USED == 1
    /* FreeRTOS */

    vPortFree( pv );
#else
    /* SEGGER embOS */
    /* Micrium MicroC/OS */
    /* Renesas RI600V4 & RI600PX */

    #error "Unsupported RTOS is selected."
#endif
}

#if defined(__GNUC__)

int8_t *sbrk( size_t size );

/* Maybe not called but necessary for linking without an undefined error. */
int8_t *sbrk( size_t size )
{
    ( void ) size;
    return (int8_t *)-1;
}

#endif /* defined(__GNUC__) */

#if defined(__ICCRX__)

void main( void );

/* Never called but necessary for linking without an undefined error. */
void main( void )
{
    /* Nothing to do. */
}

#endif /* defined(__ICCRX__) */

#endif /* BSP_CFG_RTOS_USED != 0 */
