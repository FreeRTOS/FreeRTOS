// Copyright 2019-2021 XMOS LIMITED.
// This Software is subject to the terms of the XMOS Public Licence: Version 1.

#include <xcore/triggerable.h>
#include "rtos_support.h"

/*
 * Source IDs 0-7 are reserved for RTOS cores
 * Source IDs 8-15 are allowed for other use
 *
 * (Assuming RTOS_MAX_CORE_COUNT == 8)
 */
#define RTOS_CORE_SOURCE_MASK ( ( 1 << RTOS_MAX_CORE_COUNT ) - 1)
#define MAX_ADDITIONAL_SOURCES 8
#define MAX_SOURCE_ID ( RTOS_MAX_CORE_COUNT + MAX_ADDITIONAL_SOURCES - 1 )

/*
 * The channel ends used by RTOS cores to send and receive IRQs.
 */
static chanend_t rtos_irq_chanend[ RTOS_MAX_CORE_COUNT ];

/*
 * The channel ends used by peripherals to send IRQs.
 */
static chanend_t peripheral_irq_chanend[ MAX_ADDITIONAL_SOURCES ];

/*
 * Flag set per core indicating which IRQ sources are pending
 */
static volatile uint32_t irq_pending[ RTOS_MAX_CORE_COUNT ];

static int peripheral_source_count;

/*
 * The IRQ enabled bitfield. Represents which cores have
 * their IRQ enabled.
 */
static uint32_t irq_enable_bf;

/*
 * Set to 1 when all cores have enabled their IRQ.
 */
static int irq_ready;

typedef struct {
    RTOS_IRQ_ISR_ATTR rtos_irq_isr_t isr;
    void *data;
} isr_info_t;

static isr_info_t isr_info[MAX_ADDITIONAL_SOURCES];

DEFINE_RTOS_INTERRUPT_CALLBACK( rtos_irq_handler, data )
{
    int core_id;
    uint32_t pending;

    core_id = rtos_core_id_get();

    xassert( irq_pending[ core_id ] );

    chanend_check_end_token( rtos_irq_chanend[ core_id ] );

    /* just ensure the channel read is done before clearing the pending flags. */
    RTOS_MEMORY_BARRIER();

    /* grab a snapshot of the pending flags before clearing them.
    After the clear, this core may be interrupted again. We will
    handle all the interrupts at the time the snapshot is taken now,
    and any more will be handled when this ISR is called again. */

    rtos_lock_acquire(0);
    {
        pending = irq_pending[ core_id ];
        irq_pending[ core_id ] = 0;
    }
    rtos_lock_release(0);

    if (pending & RTOS_CORE_SOURCE_MASK )
    {
        /* This core is being yielded by at least one other RTOS core.
        Clear the pending flags from all of them and enter the scheduler. */

        pending &= ~RTOS_CORE_SOURCE_MASK;

        RTOS_INTERCORE_INTERRUPT_ISR();
    }

    while ( pending != 0 )
    {
        int source_id = 31UL - ( uint32_t ) __builtin_clz( pending );

        xassert( source_id >= RTOS_MAX_CORE_COUNT && source_id <= MAX_SOURCE_ID );

        pending &= ~( 1 << source_id );

        source_id -= RTOS_MAX_CORE_COUNT;
        if ( isr_info[ source_id ].isr != NULL )
        {
            isr_info[ source_id ].isr( isr_info[ source_id ].data );
        }
    }
}

/*
 * May be called by a non-RTOS core provided
 * xSourceID >= RTOS_MAX_CORE_COUNT.
 */
void rtos_irq( int core_id, int source_id )
{
    chanend_t source_chanend;
    uint32_t pending;
    int num_cores = rtos_core_count();

    xassert( core_id >= 0 && core_id < num_cores );
    xassert( source_id >= 0 && source_id < RTOS_MAX_CORE_COUNT + peripheral_source_count );

    /*
     * Atomically set the pending flag and, if the core we are
     * sending an IRQ does not already have a pending IRQ, interrupt
     * it with a channel send. This guarantees that if two cores
     * simultaneously send a core an IRQ that only one will perform
     * the channel send. Another channel send will not be performed
     * until the core reads the token from the channel and clears the
     * pending flags.
     */
    rtos_lock_acquire(0);
    {
        pending = irq_pending[ core_id ];
        irq_pending[ core_id ] |= ( 1 << source_id );

        if( pending == 0 )
        {
            if( source_id >= 0 && source_id < num_cores )
            {
                source_chanend = rtos_irq_chanend[ source_id ];
            }
            else if ( source_id >= RTOS_MAX_CORE_COUNT && source_id < RTOS_MAX_CORE_COUNT + peripheral_source_count )
            {
                source_chanend = peripheral_irq_chanend[ source_id - RTOS_MAX_CORE_COUNT ];
            }
            else
            {
                xassert(0);
                /* If assertions are disabled, setting this to 0
                 * here should cause a resource exception below. */
                source_chanend = 0;
            }

            /* just ensure the pending flag is set before the channel send. */
            RTOS_MEMORY_BARRIER();

            chanend_set_dest( source_chanend, rtos_irq_chanend[ core_id ] );
            chanend_out_end_token( source_chanend );
        }
    }
    rtos_lock_release(0);
}


/*
 * Must be called by an RTOS core to interrupt a
 * non-RTOS core.
 */
void rtos_irq_peripheral( chanend_t dest_chanend )
{
    int core_id;

    uint32_t mask = rtos_interrupt_mask_all();
    core_id = rtos_core_id_get();
    chanend_set_dest( rtos_irq_chanend[ core_id ], dest_chanend );
    chanend_out_end_token( rtos_irq_chanend[ core_id ] );
    rtos_interrupt_mask_set(mask);
}

int rtos_irq_register(rtos_irq_isr_t isr, void *data, chanend_t source_chanend)
{
    int source_id;

    xassert( peripheral_source_count < MAX_ADDITIONAL_SOURCES );

    rtos_lock_acquire(0);
    source_id = peripheral_source_count++;
    rtos_lock_release(0);

    isr_info[ source_id ].isr = isr;
    isr_info[ source_id ].data = data;
    peripheral_irq_chanend[ source_id ] = source_chanend;

    return RTOS_MAX_CORE_COUNT + source_id;
}

void rtos_irq_enable( int total_rtos_cores )
{
    int core_id;

    core_id = rtos_core_id_get();
    rtos_irq_chanend[ core_id ] = chanend_alloc();
    triggerable_setup_interrupt_callback( rtos_irq_chanend[ core_id ], NULL, RTOS_INTERRUPT_CALLBACK( rtos_irq_handler ) );
    triggerable_enable_trigger( rtos_irq_chanend[ core_id ] );

    rtos_lock_acquire(0);
    {
        irq_enable_bf |= (1 << core_id);

        if (irq_enable_bf == (1 << total_rtos_cores) - 1) {
            irq_ready = 1;
        }
    }
    rtos_lock_release(0);
}

int rtos_irq_ready(void)
{
    return irq_ready;
}
