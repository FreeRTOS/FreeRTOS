/******************************************************************************
*
* alt_interrupt.c - API for the Altera SoC FPGA interrupts
*
******************************************************************************/

/******************************************************************************
*
* Copyright 2013 Altera Corporation. All Rights Reserved.
* 
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
* 
* 1. Redistributions of source code must retain the above copyright notice,
* this list of conditions and the following disclaimer.
* 
* 2. Redistributions in binary form must reproduce the above copyright notice,
* this list of conditions and the following disclaimer in the documentation
* and/or other materials provided with the distribution.
* 
* 3. The name of the author may not be used to endorse or promote products
* derived from this software without specific prior written permission.
* 
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER "AS IS" AND ANY EXPRESS OR
* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE DISCLAIMED. IN NO
* EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
* OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
* INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
* CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
* IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
* OF SUCH DAMAGE.
* 
******************************************************************************/

#include "alt_interrupt.h"
#include "socal/socal.h"
#include "hwlib.h"

/////

// NOTE: To enable debugging output, delete the next line and uncomment the
//   line after.
#define dprintf(...)
// #define dprintf(fmt, ...) printf(fmt, __VA_ARGS__)

/////

// Interrupt attribute(s) flags

typedef enum INT_FLAG_e
{
    INT_FLAG_IMPLEMENTED = 0x01
}
INT_FLAG_t;

static uint8_t alt_int_flag[ALT_INT_PROVISION_INT_COUNT];

/////

// IRQ Stack

#if ALT_INT_PROVISION_STACK_SUPPORT

static char __attribute__ ((aligned (16))) alt_int_stack_irq_block[ALT_INT_PROVISION_CPU_COUNT][ALT_INT_PROVISION_STACK_SIZE];

#ifdef __ARMCC_VERSION
// ARMCC specific helper function to fixup the IRQ stack.
// This is implemented in alt_interrupt_armcc.s.
extern void alt_int_fixup_irq_stack(uint32_t stack_irq);
#else
static void alt_int_fixup_irq_stack(uint32_t stack_irq)
{
    // 1. Save the current SP
    // 2. Switch to the IRQ context
    // 3. Point SP to the stack IRQ block provided
    // 4. Switch back to SYS context
    // 5. Restore the saved "current" SP

    // Mode_USR     0x10
    // Mode_FIQ     0x11
    // Mode_IRQ     0x12
    // Mode_SVC     0x13
    // Mode_MON     0x16
    // Mode_ABT     0x17
    // Mode_UNDEF   0x1B
    // Mode_SYS     0x1F

    // I_Bit        0x80  @ when I bit is set, IRQ is disabled
    // F_Bit        0x40  @ when F bit is set, FIQ is disabled
    // NS_BIT       0x1   @ when NS bit is set, core in non-secure

    // r4 being used for stack_sys.
    // Consider adding "lr" to the list of mangled registers. This way GCC will push/pop {lr} for us.
    __asm(
        "push {lr}\n"
        "mov r4, sp\n"
        "msr CPSR_c, #(0x12 | 0x80 | 0x40)\n"
        "mov sp, %0\n"
        "msr CPSR_c, #(0x1F | 0x80 | 0x40)\n"
        "mov sp, r4\n"
        "pop {lr}\n"

        : : "r" (stack_irq) : "sp", "r4"
        );
}
#endif

#endif // #if ALT_INT_PROVISION_STACK_SUPPORT

/////

// Interrupt dispatch information
// See Cortex-A9 MPCore TRM, section 1.3.
// SGI (16) + PPI (16) + SPI count (224) = total number of interrupts.
typedef struct INT_DISPATCH_s
{
    alt_int_callback_t callback;
    void *             context;
}
INT_DISPATCH_t;

static INT_DISPATCH_t alt_int_dispatch[ALT_INT_PROVISION_INT_COUNT];

/////

// Distributer interface base address
static uint32_t alt_int_base_dist;
// CPU interface base address
static uint32_t alt_int_base_cpu;

/////

// Number of CPU(s) in system
static uint32_t alt_int_count_cpu;
// Number of interrupts in system, rounded up to nearest 32
static uint32_t alt_int_count_int;

/////

inline static uint32_t get_periphbase(void)
{
    uint32_t periphbase;

    // Read the Peripheral Base Address.
    // See: Cortex-A9 TRM, section 4.3.24.

#ifdef __ARMCC_VERSION
    __asm("MRC p15, 4, periphbase, c15, c0, 0");
#else
    __asm("MRC p15, 4, %0, c15, c0, 0" : "=r" (periphbase));
#endif

    return periphbase;
}

#if ALT_INT_PROVISION_VECTOR_SUPPORT
inline static void set_sctlr_vbit(bool value)
{
    // See ARMv7, section B4.1.130.

    uint32_t sctlr;

#ifdef __ARMCC_VERSION
    __asm("MRC p15, 0, sctlr, c1, c0, 0");
#else
    __asm("MRC p15, 0, %0, c1, c0, 0" : "=r" (sctlr));
#endif

    if (value)
    {
        sctlr |= 1 << 13;
    }
    else
    {
        sctlr &= ~(1 << 13);
    }

#ifdef __ARMCC_VERSION
    __asm("MCR p15, 0, sctlr, c1, c0, 0");
#else
    __asm("MCR p15, 0, %0, c1, c0, 0" : : "r" (sctlr));
#endif

}
#endif

inline static uint32_t get_current_cpu_num(void)
{
    uint32_t affinity;

    // Use the MPIDR. This is only available at PL1 or higher.
    // See ARMv7, section B4.1.106.

#ifdef __ARMCC_VERSION
    __asm("MRC p15, 0, affinity, c0, c0, 5");
#else
    __asm ("MRC p15, 0, %0, c0, c0, 5" : "=r" (affinity));
#endif

    return affinity & 0xFF;
}

/////

ALT_STATUS_CODE alt_int_global_init()
{
    // Cache the distributor and CPU base addresses
    // See: Cortex-A9 MPCore TRM, section 1.5.
    {
        uint32_t periphbase = get_periphbase();
        alt_int_base_dist = periphbase + 0x1000;
        alt_int_base_cpu  = periphbase + 0x0100;
    }

    // Discover CPU and interrupt count
    // See GIC 1.0, section 4.3.2.
    {
        uint32_t icdictr = alt_read_word(alt_int_base_dist + 0x4);
        alt_int_count_cpu = ((icdictr >> 5) & 0x7) + 1;
        alt_int_count_int = ((icdictr & 0x1F) + 1) << 5;
    }

    // Initialize the callback and context array
    // Initialize interrupt flags array
    for (int i = 0; i < ALT_INT_PROVISION_INT_COUNT; ++i)
    {
        alt_int_dispatch[i].callback = 0;
        alt_int_dispatch[i].context  = 0;

        alt_int_flag[i] = 0;
    }

    // Discover all interrupts that are implemented in hardware.
    // See GIC 1.0, section 3.1.2.
    for (int i = 0; i < (ALT_INT_PROVISION_INT_COUNT / 32); ++i)
    {
        // Set the whole bank to be enabled.
        alt_write_word(alt_int_base_dist + 0x100 + i * sizeof(uint32_t), 0xffffffff); // icdisern

        // Read it back to see which bits stick.
        uint32_t value = alt_read_word(alt_int_base_dist + 0x100 + i * sizeof(uint32_t)); // icdisern
        for (int j = 0; j < 32; ++j)
        {
            if (((1 << j) & value) != 0)
            {
                alt_int_flag[i * 32 + j] |= INT_FLAG_IMPLEMENTED;
            }
        }

        // Clear the whole bank to be disabled.
        alt_write_word(alt_int_base_dist + 0x180 + i * sizeof(uint32_t), 0xffffffff); // icdicern
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_int_global_uninit()
{
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_int_global_enable()
{
    // See GIC 1.0, section 4.3.1.
    // See Cortex-A9 MPCore TRM, section 3.3.1.

    alt_setbits_word(alt_int_base_dist + 0x0, 0x1); // icddcr

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_int_global_disable()
{
    // See GIC 1.0, section 4.3.1.
    // See Cortex-A9 MPCore TRM, section 3.3.1.

    alt_clrbits_word(alt_int_base_dist + 0x0, 0x1); // icddcr

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_int_global_enable_ns()
{
    // See Cortex-A9 MPCore TRM, section 3.3.1.

    alt_setbits_word(alt_int_base_dist + 0x0, 0x2); // icddcr

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_int_global_disable_ns()
{
    // See Cortex-A9 MPCore TRM, section 3.3.1.

    alt_clrbits_word(alt_int_base_dist + 0x0, 0x2);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_int_global_enable_all()
{
    // See Cortex-A9 MPCore TRM, section 3.3.1.

    alt_setbits_word(alt_int_base_dist + 0x0, 0x3); // icddcr

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_int_global_disable_all()
{
    // See Cortex-A9 MPCore TRM, section 3.3.1.

    alt_clrbits_word(alt_int_base_dist + 0x0, 0x3); // icddcr

    return ALT_E_SUCCESS;
}

/////

ALT_STATUS_CODE alt_int_dist_secure_enable(ALT_INT_INTERRUPT_t int_id)
{
    // See GIC 1.0, section 4.3.4.

    if ((uint32_t)int_id >= ALT_INT_PROVISION_INT_COUNT)
    {
        return ALT_E_BAD_ARG;
    }
    else if ((alt_int_flag[int_id] & INT_FLAG_IMPLEMENTED) == 0)
    {
        return ALT_E_BAD_ARG;
    }
    else
    {
        uint32_t regoffset   = int_id >> 5;
        uint32_t regbitshift = int_id & 0x1F;

        alt_clrbits_word(alt_int_base_dist + 0x80 + regoffset * sizeof(uint32_t), 1 << regbitshift); // icdisrn

        return ALT_E_SUCCESS;
    }
}

ALT_STATUS_CODE alt_int_dist_secure_disable(ALT_INT_INTERRUPT_t int_id)
{
    // See GIC 1.0, section 4.3.4.

    if ((uint32_t)int_id >= ALT_INT_PROVISION_INT_COUNT)
    {
        return ALT_E_BAD_ARG;
    }
    else if ((alt_int_flag[int_id] & INT_FLAG_IMPLEMENTED) == 0)
    {
        return ALT_E_BAD_ARG;
    }
    else
    {
        uint32_t regoffset   = int_id >> 5;
        uint32_t regbitshift = int_id & 0x1F;

        alt_setbits_word(alt_int_base_dist + 0x80 + regoffset * sizeof(uint32_t), 1 << regbitshift); // icdisrn

        return ALT_E_SUCCESS;
    }
}

ALT_STATUS_CODE alt_int_dist_is_secure(ALT_INT_INTERRUPT_t int_id)
{
    // See GIC 1.0, section 4.3.4.

    if ((uint32_t)int_id >= ALT_INT_PROVISION_INT_COUNT)
    {
        // Because interrupts are by default after reset secure, return the
        // default security state.
        return ALT_E_BAD_ARG;
    }
    else if ((alt_int_flag[int_id] & INT_FLAG_IMPLEMENTED) == 0)
    {
        // Because interrupts are by default after reset secure, return the
        // default security state.
        return ALT_E_TRUE;
    }
    else
    {
        uint32_t regoffset   = int_id >> 5;
        uint32_t regbitshift = int_id & 0x1F;

        uint32_t icdisrn = alt_read_word(alt_int_base_dist + 0x80 + regoffset * sizeof(uint32_t));

        if ((icdisrn & (1 << regbitshift)) == 0)
        {
            return ALT_E_TRUE;
        }
        else
        {
            return ALT_E_FALSE;
        }
    }
}

ALT_STATUS_CODE alt_int_dist_enable(ALT_INT_INTERRUPT_t int_id)
{
    // See GIC 1.0, section 4.3.5.

    if ((uint32_t)int_id >= ALT_INT_PROVISION_INT_COUNT)
    {
        return ALT_E_BAD_ARG;
    }
    else if ((alt_int_flag[int_id] & INT_FLAG_IMPLEMENTED) == 0)
    {
        return ALT_E_BAD_ARG;
    }
    else
    {
        uint32_t regoffset   = int_id >> 5;
        uint32_t regbitshift = int_id & 0x1F;

        alt_write_word(alt_int_base_dist + 0x100 + regoffset * sizeof(uint32_t), 1 << regbitshift); // icdisern

        return ALT_E_SUCCESS;
    }
}

ALT_STATUS_CODE alt_int_dist_disable(ALT_INT_INTERRUPT_t int_id)
{
    // See GIC 1.0, section 4.3.6.

    if ((uint32_t)int_id >= ALT_INT_PROVISION_INT_COUNT)
    {
        return ALT_E_BAD_ARG;
    }
    else if ((alt_int_flag[int_id] & INT_FLAG_IMPLEMENTED) == 0)
    {
        return ALT_E_BAD_ARG;
    }
    else
    {
        uint32_t regoffset   = int_id >> 5;
        uint32_t regbitshift = int_id & 0x1F;

        alt_write_word(alt_int_base_dist + 0x180 + regoffset * sizeof(uint32_t), 1 << regbitshift); // icdicern

        return ALT_E_SUCCESS;
    }
}

ALT_STATUS_CODE alt_int_dist_is_enabled(ALT_INT_INTERRUPT_t int_id)
{
    // See GIC 1.0, section 4.3.5.

    if ((uint32_t)int_id >= ALT_INT_PROVISION_INT_COUNT)
    {
        // Interrupts on the GIC is disabled by default, so report disabled.
        return ALT_E_BAD_ARG;
    }
    else if ((alt_int_flag[int_id] & INT_FLAG_IMPLEMENTED) == 0)
    {
        // Interrupts on the GIC is disabled by default, so report disabled.
        return ALT_E_FALSE;
    }
    else
    {
        uint32_t regoffset   = int_id >> 5;
        uint32_t regbitshift = int_id & 0x1F;

        uint32_t icdisern = alt_read_word(alt_int_base_dist + 0x100 + regoffset * sizeof(uint32_t));

        if ((icdisern & (1 << regbitshift)) != 0)
        {
            return ALT_E_TRUE;
        }
        else
        {
            return ALT_E_FALSE;
        }
    }
}

ALT_STATUS_CODE alt_int_dist_pending_set(ALT_INT_INTERRUPT_t int_id)
{
    // See GIC 1.0, section 4.3.7.

    if ((uint32_t)int_id >= ALT_INT_PROVISION_INT_COUNT)
    {
        return ALT_E_BAD_ARG;
    }
    else if ((alt_int_flag[int_id] & INT_FLAG_IMPLEMENTED) == 0)
    {
        return ALT_E_BAD_ARG;
    }
    else if ((uint32_t)int_id < 16)
    {
        return ALT_E_BAD_ARG;
    }
    else
    {
        uint32_t regoffset   = int_id >> 5;
        uint32_t regbitshift = int_id & 0x1F;

        alt_write_word(alt_int_base_dist + 0x200 + regoffset * sizeof(uint32_t), 1 << regbitshift); // icdisprn

        return ALT_E_SUCCESS;
    }
}

ALT_STATUS_CODE alt_int_dist_pending_clear(ALT_INT_INTERRUPT_t int_id)
{
    // See GIC 1.0, section 4.3.8.

    if ((uint32_t)int_id >= ALT_INT_PROVISION_INT_COUNT)
    {
        return ALT_E_BAD_ARG;
    }
    else if ((alt_int_flag[int_id] & INT_FLAG_IMPLEMENTED) == 0)
    {
        return ALT_E_BAD_ARG;
    }
    else if ((uint32_t)int_id < 16)
    {
        return ALT_E_BAD_ARG;
    }
    else
    {
        uint32_t regoffset   = int_id >> 5;
        uint32_t regbitshift = int_id & 0x1F;

        alt_write_word(alt_int_base_dist + 0x280 + regoffset * sizeof(uint32_t), 1 << regbitshift); // icdicprn

        return ALT_E_SUCCESS;
    }
}

ALT_STATUS_CODE alt_int_dist_is_pending(ALT_INT_INTERRUPT_t int_id)
{
    // See GIC 1.0, section 4.3.7.

    if ((uint32_t)int_id >= ALT_INT_PROVISION_INT_COUNT)
    {
        // Interrupts on the GIC is not pending by default, so report false.
        return ALT_E_BAD_ARG;
    }
    else if ((alt_int_flag[int_id] & INT_FLAG_IMPLEMENTED) == 0)
    {
        // Interrupts on the GIC is not pending by default, so report false.
        return ALT_E_FALSE;
    }
    else
    {
        uint32_t regoffset   = int_id >> 5;
        uint32_t regbitshift = int_id & 0x1F;

        uint32_t icdisprn = alt_read_word(alt_int_base_dist + 0x200 + regoffset * sizeof(uint32_t));

        if ((icdisprn & (1 << regbitshift)) != 0)
        {
            return ALT_E_TRUE;
        }
        else
        {
            return ALT_E_FALSE;
        }
    }
}

ALT_STATUS_CODE alt_int_dist_is_active(ALT_INT_INTERRUPT_t int_id)
{
    // See GIC 1.0, section 4.3.9.

    if ((uint32_t)int_id >= ALT_INT_PROVISION_INT_COUNT)
    {
        // Interrupts on the GIC is not active by default, so report false.
        return ALT_E_BAD_ARG;
    }
    else if ((alt_int_flag[int_id] & INT_FLAG_IMPLEMENTED) == 0)
    {
        // Interrupts on the GIC is not active by default, so report false.
        return ALT_E_FALSE;
    }
    else
    {
        uint32_t regoffset   = int_id >> 5;
        uint32_t regbitshift = int_id & 0x1F;

        uint32_t icdabrn = alt_read_word(alt_int_base_dist + 0x300 + regoffset * sizeof(uint32_t));

        if ((icdabrn & (1 << regbitshift)) != 0)
        {
            return ALT_E_TRUE;
        }
        else
        {
            return ALT_E_FALSE;
        }
    }
}

ALT_STATUS_CODE alt_int_dist_priority_get(ALT_INT_INTERRUPT_t int_id,
                                          uint32_t * priority)
{
    // See GIC 1.0, section 4.3.10.

    if ((uint32_t)int_id >= ALT_INT_PROVISION_INT_COUNT)
    {
        // Interrupts on the GIC have a default priority of 0.
        return ALT_E_BAD_ARG;
    }
    else if ((alt_int_flag[int_id] & INT_FLAG_IMPLEMENTED) == 0)
    {
        // Interrupts on the GIC have a default priority of 0.
        *priority = 0;
        return ALT_E_SUCCESS;
    }
    else
    {
        uint32_t regoffset = int_id;

        uint8_t icdiprn = alt_read_byte(alt_int_base_dist + 0x400 + regoffset * sizeof(uint8_t));

        *priority = icdiprn;
        return ALT_E_SUCCESS;
    }
}

ALT_STATUS_CODE alt_int_dist_priority_set(ALT_INT_INTERRUPT_t int_id, 
                                          uint32_t priority)
{
    // See GIC 1.0, section 4.3.10.

    if ((uint32_t)int_id >= ALT_INT_PROVISION_INT_COUNT)
    {
        return ALT_E_BAD_ARG;
    }
    else if ((alt_int_flag[int_id] & INT_FLAG_IMPLEMENTED) == 0)
    {
        return ALT_E_BAD_ARG;
    }
    else if (priority < 256)
    {
        uint32_t regoffset = int_id;

        alt_write_byte(alt_int_base_dist + 0x400 + regoffset * sizeof(uint8_t), (uint8_t)priority); // icdiprn

        return ALT_E_SUCCESS;
    }
    else
    {
        return ALT_E_BAD_ARG;
    }
}

ALT_STATUS_CODE alt_int_dist_target_get(ALT_INT_INTERRUPT_t int_id,
                                        alt_int_cpu_target_t * target)
{
    // See GIC 1.0, section 4.3.11.

    if ((uint32_t)int_id >= ALT_INT_PROVISION_INT_COUNT)
    {
        return ALT_E_BAD_ARG;
    }
    if ((alt_int_flag[int_id] & INT_FLAG_IMPLEMENTED) == 0)
    {
        *target = 0;
        return ALT_E_SUCCESS;
    }
    else
    {
        uint32_t regoffset = int_id;

        uint8_t icdiptr = alt_read_byte(alt_int_base_dist + 0x800 + regoffset * sizeof(uint8_t));
        
        *target = icdiptr;
        return ALT_E_SUCCESS;
    }
}

ALT_STATUS_CODE alt_int_dist_target_set(ALT_INT_INTERRUPT_t int_id,
                                        alt_int_cpu_target_t target)
{
    // See GIC 1.0, section 4.3.11.

    if ((uint32_t)int_id >= ALT_INT_PROVISION_INT_COUNT)
    {
        return ALT_E_BAD_ARG;
    }
    else if ((alt_int_flag[int_id] & INT_FLAG_IMPLEMENTED) == 0)
    {
        return ALT_E_BAD_ARG;
    }
    else if (target >= (1 << alt_int_count_cpu))
    {
        if (target == (1 << get_current_cpu_num()))
        {
            return ALT_E_SUCCESS;
        }
        return ALT_E_BAD_ARG;
    }
    else if (int_id < 32)
    {
        return ALT_E_BAD_ARG;
    }
    else
    {
        uint32_t regoffset = int_id;

        alt_write_byte(alt_int_base_dist + 0x800 + regoffset * sizeof(uint8_t), target); // icdiptr

        return ALT_E_SUCCESS;
    }
}

ALT_STATUS_CODE alt_int_dist_trigger_get(ALT_INT_INTERRUPT_t int_id,
                                         ALT_INT_TRIGGER_t * trigger)
{
    // See GIC 1.0, section 4.3.12.

    if ((uint32_t)int_id >= ALT_INT_PROVISION_INT_COUNT)
    {
        return ALT_E_BAD_ARG;
    }
    else if ((alt_int_flag[int_id] & INT_FLAG_IMPLEMENTED) == 0)
    {
        *trigger = ALT_INT_TRIGGER_NA;
        return ALT_E_SUCCESS;
    }
    else if (int_id < 16)
    {
        *trigger = ALT_INT_TRIGGER_SOFTWARE;
        return ALT_E_SUCCESS;
    }
    else
    {
        uint32_t regoffset   = int_id >> 4;
        uint32_t regbitshift = ((int_id & 0x0F) * 2) + 1;

        uint32_t icdicfrn = alt_read_word(alt_int_base_dist + 0xC00 + regoffset * sizeof(uint32_t));

        if ((icdicfrn & (1 << regbitshift)) == 0)
        {
            *trigger = ALT_INT_TRIGGER_LEVEL;
        }
        else
        {
            *trigger = ALT_INT_TRIGGER_EDGE;
        }

        return ALT_E_SUCCESS;
    }
}

ALT_STATUS_CODE alt_int_dist_trigger_set(ALT_INT_INTERRUPT_t int_id,
                                         ALT_INT_TRIGGER_t trigger_type)
{
    // See GIC 1.0, section 4.3.12.

    if ((uint32_t)int_id >= ALT_INT_PROVISION_INT_COUNT)
    {
        return ALT_E_BAD_ARG;
    }
    else if ((alt_int_flag[int_id] & INT_FLAG_IMPLEMENTED) == 0)
    {
        return ALT_E_BAD_ARG;
    }
    else if (int_id < 16)
    {
        if (   (trigger_type == ALT_INT_TRIGGER_AUTODETECT)
            || (trigger_type == ALT_INT_TRIGGER_SOFTWARE))
        {
            return ALT_E_SUCCESS;
        }
        else
        {
            return ALT_E_BAD_ARG;
        }
    }
    else
    {
        uint32_t regoffset   = int_id >> 4;
        uint32_t regbitshift = ((int_id & 0x0F) * 2) + 1;

        if (trigger_type == ALT_INT_TRIGGER_AUTODETECT)
        {
            if      (int_id <=  32) { trigger_type = ALT_INT_TRIGGER_EDGE;  } // PPI
            else if (int_id <=  40) { trigger_type = ALT_INT_TRIGGER_EDGE;  } // CPU0_PARITYFAIL
            else if (int_id <=  47) { trigger_type = ALT_INT_TRIGGER_LEVEL; } // CPU0_DEFLAGS
            else if (int_id <=  56) { trigger_type = ALT_INT_TRIGGER_EDGE;  } // CPU1_PARITYFAIL
            else if (int_id <=  63) { trigger_type = ALT_INT_TRIGGER_LEVEL; } // CPU1_DEFLAGS
            else if (int_id <=  66) { trigger_type = ALT_INT_TRIGGER_EDGE;  } // SCU
            else if (int_id <=  69) { trigger_type = ALT_INT_TRIGGER_EDGE;  } // L2_ECC
            else if (int_id <=  70) { trigger_type = ALT_INT_TRIGGER_LEVEL; } // L2 (other)
            else if (int_id <=  71) { trigger_type = ALT_INT_TRIGGER_LEVEL; } // DDR
            else if (int_id <= 135) { /* do nothing */                      } // FPGA, !!!
            else                    { trigger_type = ALT_INT_TRIGGER_LEVEL; } // everything else
        }

        switch (trigger_type)
        {
        case ALT_INT_TRIGGER_LEVEL:
            alt_clrbits_word(alt_int_base_dist + 0xC00 + regoffset * sizeof(uint32_t), 1 << regbitshift); // icdicfrn
            break;
        case ALT_INT_TRIGGER_EDGE:
            alt_setbits_word(alt_int_base_dist + 0xC00 + regoffset * sizeof(uint32_t), 1 << regbitshift); // icdicfrn
            break;
        default:
            return ALT_E_BAD_ARG;
        }

        return ALT_E_SUCCESS;
    }
}

/////

ALT_STATUS_CODE alt_int_sgi_trigger(ALT_INT_INTERRUPT_t int_id,
                                    ALT_INT_SGI_TARGET_t target_filter,
                                    alt_int_cpu_target_t target_list,
                                    bool secure_only)
{
    // See GIC 1.0, section 4.3.13.

    if (target_list >= (1 << alt_int_count_cpu))
    {
        return ALT_E_BAD_ARG;
    }
    else if ((uint32_t)int_id < 16)
    {
        uint32_t filterbits;
        uint32_t sattmask = 0;

        switch (target_filter)
        {
        case ALT_INT_SGI_TARGET_LIST:
            filterbits = 0x0 << 24;
            break;
        case ALT_INT_SGI_TARGET_ALL_EXCL_SENDER:
            filterbits = 0x1 << 24;
            break;
        case ALT_INT_SGI_TARGET_SENDER_ONLY:
            filterbits = 0x2 << 24;
            break;
        default:
            return ALT_E_BAD_ARG;
        }

        if (!secure_only)
        {
            sattmask = 1 << 15;
        }

        alt_write_word(alt_int_base_dist + 0xF00, int_id | sattmask | (target_list << 16) | filterbits); // icdsgir

        return ALT_E_SUCCESS;
    }
    else
    {
        return ALT_E_BAD_ARG;
    }
}

/////

ALT_STATUS_CODE alt_int_cpu_init()
{
    uint32_t cpu_num = get_current_cpu_num();

    if (cpu_num >= ALT_INT_PROVISION_CPU_COUNT)
    {
        return ALT_E_ERROR;
    }

    // Setup the IRQ stack

#if ALT_INT_PROVISION_STACK_SUPPORT

    // The ARM stack lowers in address as it is being used. 16 is the alignment
    // of the block.
    uint32_t stack_irq = (uint32_t) &alt_int_stack_irq_block[cpu_num][sizeof(alt_int_stack_irq_block[0]) - 16];

    alt_int_fixup_irq_stack(stack_irq);

#endif // #if ALT_INT_PROVISION_STACK_SUPPORT

    // Setup the Vector Interrupt Table

#if ALT_INT_PROVISION_VECTOR_SUPPORT

    // Set the vector interrupt table (VBAR) to use __cs3_interrupt_vector and
    // set SCTLR.V to always be 0.

    // For SCTLR.V information, See ARMv7, section B4.1.130.
    // For VBAR information, See ARMv7, section B4.1.156.

    set_sctlr_vbit(false);

#ifdef __ARMCC_VERSION
    extern char alt_interrupt_vector;
    uint32_t vector_table = (uint32_t)&alt_interrupt_vector;
    __asm("MCR p15, 0, vector_table, c12, c0, 0");
#else
    extern char __cs3_interrupt_vector;
    uint32_t vector_table = (uint32_t)&__cs3_interrupt_vector;
    __asm("MCR p15, 0, %0,           c12, c0, 0" : : "r" (vector_table));
#endif

#endif // #if ALT_INT_PROVISION_VECTOR_SUPPORT
    
    // Setup the priority mask and binary point defaults.
    // This will allow all interrupts to have sufficient priority to be
    // forwarded to the CPUs.

    ALT_STATUS_CODE status;

    status = alt_int_cpu_priority_mask_set(0xff);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }
    status = alt_int_cpu_binary_point_set(0);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_int_cpu_uninit()
{
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_int_cpu_enable()
{
    // See GIC 1.0, section 4.4.1.

    alt_setbits_word(alt_int_base_cpu + 0x0, 0x1); // iccicr

    // Unmask IRQ interrupts from current processor.

#ifdef __ARMCC_VERSION
    __enable_irq();
#else
    __asm("CPSIE i");
#endif

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_int_cpu_disable()
{
    // See GIC 1.0, section 4.4.1.

    alt_clrbits_word(alt_int_base_cpu + 0x0, 0x1); // iccicr

    // Mask IRQ interrupts from current processor.

#ifdef __ARMCC_VERSION
    __disable_irq();
#else
    __asm("CPSID i");
#endif

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_int_cpu_enable_ns()
{
    // See GIC 1.0, section 4.4.1.

    alt_setbits_word(alt_int_base_cpu + 0x0, 0x2); // iccicr

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_int_cpu_disable_ns()
{
    // See GIC 1.0, section 4.4.1.

    alt_clrbits_word(alt_int_base_cpu + 0x0, 0x2); // iccicr

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_int_cpu_enable_all()
{
    // See GIC 1.0, section 4.4.1.

    alt_setbits_word(alt_int_base_cpu + 0x0, 0x3); // iccicr

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_int_cpu_disable_all()
{
    // See GIC 1.0, section 4.4.1.

    alt_clrbits_word(alt_int_base_cpu + 0x0, 0x3); // iccicr

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_int_cpu_config_get(bool* use_secure_binary_point,
                                       bool* use_FIQ_for_secure_interrupts,
                                       bool* allow_secure_ack_all_interrupts)
{
    // See GIC 1.0, section 4.4.1.

    uint32_t iccicr = alt_read_word(alt_int_base_cpu + 0x0);

    if (use_secure_binary_point)
    {
        *use_secure_binary_point = (iccicr & (1 << 4)) != 0;
    }
    if (use_FIQ_for_secure_interrupts)
    {
        *use_FIQ_for_secure_interrupts = (iccicr & (1 << 3)) != 0;
    }
    if (allow_secure_ack_all_interrupts)
    {
        *allow_secure_ack_all_interrupts = (iccicr & (1 << 2)) != 0;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_int_cpu_config_set(bool use_secure_binary_point,
                                       bool use_FIQ_for_secure_interrupts,
                                       bool allow_secure_ack_all_interrupts)
{
    // See GIC 1.0, section 4.4.1.

    uint32_t iccicr = alt_read_word(alt_int_base_cpu + 0x0);

    if (use_secure_binary_point)
    {
        iccicr |= 1 << 4;
    }
    else
    {
        iccicr &= ~(1 << 4);
    }

    if (use_FIQ_for_secure_interrupts)
    {
        iccicr |= 1 << 3;
    }
    else
    {
        iccicr &= ~(1 << 3);
    }

    if (allow_secure_ack_all_interrupts)
    {
        iccicr |= 1 << 2;
    }
    else
    {
        iccicr &= ~(1 << 2);
    }

    alt_write_word(alt_int_base_cpu + 0x0, iccicr);

    return ALT_E_SUCCESS;
}

uint32_t alt_int_cpu_priority_mask_get()
{
    // See GIC 1.0, section 4.4.2.

    uint32_t iccpmr = alt_read_word(alt_int_base_cpu + 0x4);

    return iccpmr;
}

ALT_STATUS_CODE alt_int_cpu_priority_mask_set(uint32_t priority_mask)
{
    // See GIC 1.0, section 4.4.2.

    if (priority_mask < 256)
    {
        alt_write_word(alt_int_base_cpu + 0x4, priority_mask); // iccpmr

        return ALT_E_SUCCESS;
    }
    else
    {
        return ALT_E_BAD_ARG;
    }
}

uint32_t alt_int_cpu_binary_point_get()
{
    // See GIC 1.0, section 4.4.3.

    uint32_t iccbpr = alt_read_word(alt_int_base_cpu + 0x8);

    return iccbpr;
}

ALT_STATUS_CODE alt_int_cpu_binary_point_set(uint32_t binary_point)
{
    // See GIC 1.0, section 4.4.3.

    if (binary_point < 8)
    {
        alt_write_word(alt_int_base_cpu + 0x8, binary_point); // iccbpr

        return ALT_E_SUCCESS;
    }
    else
    {
        return ALT_E_BAD_ARG;
    }
}

uint32_t alt_int_cpu_binary_point_get_ns()
{
    // See GIC 1.0, section 4.4.7.

    uint32_t iccabpr = alt_read_word(alt_int_base_cpu + 0x1C);

    return iccabpr;
}

ALT_STATUS_CODE alt_int_cpu_binary_point_set_ns(uint32_t binary_point)
{
    // See GIC 1.0, section 4.4.7.

    if (binary_point < 8)
    {
        alt_write_word(alt_int_base_cpu + 0x1C, binary_point); // iccabpr

        return ALT_E_SUCCESS;
    }
    else
    {
        return ALT_E_BAD_ARG;
    }
}

/////

ALT_STATUS_CODE alt_int_isr_register(ALT_INT_INTERRUPT_t int_id,
                                     alt_int_callback_t callback,
                                     void * context)
{
    if ((uint32_t)int_id < ALT_INT_PROVISION_INT_COUNT)
    {
        alt_int_dispatch[int_id].callback = callback;
        alt_int_dispatch[int_id].context  = context;

        return ALT_E_SUCCESS;
    }
    else
    {
        return ALT_E_BAD_ARG;
    }
}

ALT_STATUS_CODE alt_int_isr_unregister(ALT_INT_INTERRUPT_t int_id)
{
    if ((uint32_t)int_id < ALT_INT_PROVISION_INT_COUNT)
    {
        alt_int_dispatch[int_id].callback = 0;
        alt_int_dispatch[int_id].context  = 0;

        return ALT_E_SUCCESS;
    }
    else
    {
        return ALT_E_BAD_ARG;
    }
}

/////

uint32_t alt_int_util_cpu_count(void)
{
    return alt_int_count_cpu;
}

uint32_t alt_int_util_int_count(void)
{
    return alt_int_count_int;
}

alt_int_cpu_target_t alt_int_util_cpu_current(void)
{
    return 1 << get_current_cpu_num();
}

/////

#if ALT_INT_PROVISION_VECTOR_SUPPORT

#ifdef __ARMCC_VERSION
void __irq alt_int_handler_irq(void)
#else
void __attribute__ ((interrupt)) __cs3_isr_irq(void)
#endif

#else // #if ALT_INT_PROVISION_VECTOR_SUPPORT

void alt_int_handler_irq(void)

#endif // #if ALT_INT_PROVISION_VECTOR_SUPPORT
{
    // See GIC 1.0, sections 4.4.4, 4.4.5.

   uint32_t icciar = alt_read_word(alt_int_base_cpu + 0xC);

    uint32_t ackintid = ALT_INT_ICCIAR_ACKINTID_GET(icciar);

    if (ackintid < ALT_INT_PROVISION_INT_COUNT)
    {
        if (alt_int_dispatch[ackintid].callback)
        {
            alt_int_dispatch[ackintid].callback(icciar, alt_int_dispatch[ackintid].context);
        }
    }
    else
    {
        // Report error.
        dprintf("INT[ISR]: Unhandled interrupt ID = 0x%lx.\n", ackintid);
    }

    alt_write_word(alt_int_base_cpu + 0x10, icciar); // icceoir
}
