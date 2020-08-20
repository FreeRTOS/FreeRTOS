/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_SIFIVE_CLIC0

#include <stdint.h>
#include <metal/io.h>
#include <metal/shutdown.h>
#include <metal/drivers/sifive_clic0.h>
#include <metal/machine.h>

typedef enum metal_clic_vector_{
    METAL_CLIC_NONVECTOR = 0,
    METAL_CLIC_VECTORED  = 1
} metal_clic_vector;

struct __metal_clic_cfg {
    unsigned char : 1,
             nmbits : 2,
             nlbits : 4,
              nvbit : 1;
};

const struct __metal_clic_cfg __metal_clic_defaultcfg = {
                .nmbits = METAL_INTR_PRIV_M_MODE,
                .nlbits = 0,
                .nvbit = METAL_CLIC_NONVECTOR
            };

void __metal_clic0_handler(int id, void *priv) __attribute__((aligned(64)));

void __metal_clic0_default_vector_handler (void) __attribute__((interrupt, aligned(64)));

struct __metal_clic_cfg __metal_clic0_configuration (struct __metal_driver_sifive_clic0 *clic,
                                                 struct __metal_clic_cfg *cfg)
{
    volatile unsigned char val;
    struct __metal_clic_cfg cliccfg;
    unsigned long control_base = __metal_driver_sifive_clic0_control_base((struct metal_interrupt *)clic);

    if ( cfg ) {
        val = cfg->nmbits << 5 | cfg->nlbits << 1 | cfg->nvbit;
        __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                       METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                       METAL_SIFIVE_CLIC0_CLICCFG)) = val;
    }
    val = __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                       METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                       METAL_SIFIVE_CLIC0_CLICCFG));
    cliccfg.nmbits = (val & METAL_SIFIVE_CLIC0_CLICCFG_NMBITS_MASK) >> 5;
    cliccfg.nlbits = (val & METAL_SIFIVE_CLIC0_CLICCFG_NLBITS_MASK) >> 1;
    cliccfg.nvbit = val & METAL_SIFIVE_CLIC0_CLICCFG_NVBIT_MASK;
    return cliccfg;
}

int __metal_clic0_interrupt_set_mode (struct __metal_driver_sifive_clic0 *clic, int id, int mode)
{
    uint8_t mask, val;
    struct __metal_clic_cfg cfg = __metal_clic0_configuration(clic, NULL);
    unsigned long control_base = __metal_driver_sifive_clic0_control_base((struct metal_interrupt *)clic);
 
    if (mode >= (cfg.nmbits << 1)) {
        /* Do nothing, mode request same or exceed what configured in CLIC */
        return 0;
    }
 
    /* Mask out nmbits and retain other values */
    mask = ((uint8_t)(-1)) >> cfg.nmbits;
    val = __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                       METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                       METAL_SIFIVE_CLIC0_CLICINTCTL_BASE + id)) & mask;
    __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                 METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                 METAL_SIFIVE_CLIC0_CLICINTCTL_BASE + id)) = val | (mode << (8 - cfg.nmbits));
    return 0;
}

int __metal_clic0_interrupt_set_level (struct __metal_driver_sifive_clic0 *clic, int id, unsigned int level)
{
    uint8_t mask, nmmask, nlmask, val;
    struct __metal_clic_cfg cfg = __metal_clic0_configuration(clic, NULL);
    unsigned long control_base = __metal_driver_sifive_clic0_control_base((struct metal_interrupt *)clic);

    /* Drop the LSBs that don't fit in nlbits */
    level = level >> (METAL_CLIC_MAX_NLBITS - cfg.nlbits);

    nmmask = ~( ((uint8_t)(-1)) >> (cfg.nmbits) );
    nlmask = ((uint8_t)(-1)) >> (cfg.nmbits + cfg.nlbits);
    mask = ~(nlmask | nmmask);
  
    val = __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                       METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                       METAL_SIFIVE_CLIC0_CLICINTCTL_BASE + id));
    __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                 METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                 METAL_SIFIVE_CLIC0_CLICINTCTL_BASE + id)) = __METAL_SET_FIELD(val, mask, level);
    return 0;
}

unsigned int __metal_clic0_interrupt_get_level (struct __metal_driver_sifive_clic0 *clic, int id)
{
    int level;
    uint8_t mask, val, freebits, nlbits;
    struct __metal_clic_cfg cfg = __metal_clic0_configuration(clic, NULL);
    unsigned long control_base = __metal_driver_sifive_clic0_control_base((struct metal_interrupt *)clic);
    int num_intbits = __metal_driver_sifive_clic0_num_intbits((struct metal_interrupt *)clic);

    if ((cfg.nmbits + cfg.nlbits) >= num_intbits) {
        nlbits = num_intbits - cfg.nmbits;
    } else {
        nlbits = cfg.nlbits;
    }

    mask = ((1 << nlbits) - 1) << (8 - (cfg.nmbits + nlbits));
    freebits = ((1 << METAL_CLIC_MAX_NLBITS) - 1) >> nlbits;
  
    if (mask == 0) {
        level = (1 << METAL_CLIC_MAX_NLBITS) - 1;
    } else {
        val = __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                       METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                       METAL_SIFIVE_CLIC0_CLICINTCTL_BASE + id));
        val = __METAL_GET_FIELD(val, mask);
        level = (val << (METAL_CLIC_MAX_NLBITS - nlbits)) | freebits;
    }

    return level;
}

int __metal_clic0_interrupt_set_priority (struct __metal_driver_sifive_clic0 *clic, int id, int priority)
{
    uint8_t mask, npmask, val, npbits;
    struct __metal_clic_cfg cfg = __metal_clic0_configuration(clic, NULL);
    unsigned long control_base = __metal_driver_sifive_clic0_control_base((struct metal_interrupt *)clic);
    int num_intbits = __metal_driver_sifive_clic0_num_intbits((struct metal_interrupt *)clic);

    if ((cfg.nmbits + cfg.nlbits) < num_intbits) {
        npbits = num_intbits - (cfg.nmbits + cfg.nlbits);
        priority = priority >> (8 - npbits);

        mask = ((uint8_t)(-1)) >> (cfg.nmbits + cfg.nlbits + npbits);
        npmask = ~(((uint8_t)(-1)) >> (cfg.nmbits + cfg.nlbits));
        mask = ~(mask | npmask);

        val = __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                       METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                       METAL_SIFIVE_CLIC0_CLICINTCTL_BASE + id));
        __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                     METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                     METAL_SIFIVE_CLIC0_CLICINTCTL_BASE + id)) = __METAL_SET_FIELD(val, mask, priority);
    }
    return 0;
}

int __metal_clic0_interrupt_get_priority (struct __metal_driver_sifive_clic0 *clic, int id)
{
    int priority;
    uint8_t mask, val, freebits, nlbits;
    struct __metal_clic_cfg cfg = __metal_clic0_configuration(clic, NULL);
    unsigned long control_base = __metal_driver_sifive_clic0_control_base((struct metal_interrupt *)clic);
    int num_intbits = __metal_driver_sifive_clic0_num_intbits((struct metal_interrupt *)clic);

    if ((cfg.nmbits + cfg.nlbits) >= num_intbits) {
        nlbits = num_intbits - cfg.nmbits;
    } else {
        nlbits = cfg.nlbits;
    }

    mask = ((1 << nlbits) - 1) << (8 - (cfg.nmbits + nlbits));
    freebits = ((1 << METAL_CLIC_MAX_NLBITS) - 1) >> nlbits;
    
    if (mask == 0) {
        priority = (1 << METAL_CLIC_MAX_NLBITS) - 1;
    } else {                           
        val = __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                       METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                       METAL_SIFIVE_CLIC0_CLICINTCTL_BASE + id));
        priority = __METAL_GET_FIELD(val, freebits);
    }
    return priority;
}

int __metal_clic0_interrupt_set_vector_mode (struct __metal_driver_sifive_clic0 *clic, int id, int enable)
{   
    uint8_t mask, val;
    unsigned long control_base = __metal_driver_sifive_clic0_control_base((struct metal_interrupt *)clic);
    int num_intbits = __metal_driver_sifive_clic0_num_intbits((struct metal_interrupt *)clic);

    mask = 1 << (8 - num_intbits);
    val = __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                       METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                       METAL_SIFIVE_CLIC0_CLICINTCTL_BASE + id));
    /* Ensure its value is 1 bit wide */
    enable &= 0x1;
    __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                 METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                 METAL_SIFIVE_CLIC0_CLICINTCTL_BASE + id)) = __METAL_SET_FIELD(val, mask, enable);
    return 0;
}

int __metal_clic0_interrupt_is_vectored (struct __metal_driver_sifive_clic0 *clic, int id)
{
    uint8_t mask, val;
    unsigned long control_base = __metal_driver_sifive_clic0_control_base((struct metal_interrupt *)clic);
    int num_intbits = __metal_driver_sifive_clic0_num_intbits((struct metal_interrupt *)clic);

    mask = 1 << (8 - num_intbits);
    val = __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                       METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                       METAL_SIFIVE_CLIC0_CLICINTCTL_BASE + id));
    return __METAL_GET_FIELD(val, mask);
}

int __metal_clic0_interrupt_enable (struct __metal_driver_sifive_clic0 *clic, int id)
{
    unsigned long control_base = __metal_driver_sifive_clic0_control_base((struct metal_interrupt *)clic);
    int num_subinterrupts = __metal_driver_sifive_clic0_num_subinterrupts((struct metal_interrupt *)clic);

    if (id >= num_subinterrupts) {
        return -1;
    }
    __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                       METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                       METAL_SIFIVE_CLIC0_CLICINTIE_BASE + id)) = METAL_ENABLE;
    return 0;
}

int __metal_clic0_interrupt_disable (struct __metal_driver_sifive_clic0 *clic, int id)
{
    unsigned long control_base = __metal_driver_sifive_clic0_control_base((struct metal_interrupt *)clic);
    int num_subinterrupts = __metal_driver_sifive_clic0_num_subinterrupts((struct metal_interrupt *)clic);

    if (id >= num_subinterrupts) {
        return -1;
    }
    __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                       METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                       METAL_SIFIVE_CLIC0_CLICINTIE_BASE + id)) = METAL_DISABLE;
    return 0;
}

int __metal_clic0_interrupt_is_enabled (struct __metal_driver_sifive_clic0 *clic, int id)
{
    unsigned long control_base = __metal_driver_sifive_clic0_control_base((struct metal_interrupt *)clic);
    int num_subinterrupts = __metal_driver_sifive_clic0_num_subinterrupts((struct metal_interrupt *)clic);

    if (id >= num_subinterrupts) {
        return 0;
    }
    return __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                       METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                       METAL_SIFIVE_CLIC0_CLICINTIE_BASE + id));
}

int __metal_clic0_interrupt_is_pending (struct __metal_driver_sifive_clic0 *clic, int id)
{
    unsigned long control_base = __metal_driver_sifive_clic0_control_base((struct metal_interrupt *)clic);
    int num_subinterrupts = __metal_driver_sifive_clic0_num_subinterrupts((struct metal_interrupt *)clic);

    if (id >= num_subinterrupts) {
        return 0;
    }
    return __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                       METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                       METAL_SIFIVE_CLIC0_CLICINTIP_BASE + id));
}

int __metal_clic0_interrupt_set (struct __metal_driver_sifive_clic0 *clic, int id)
{       
    unsigned long control_base = __metal_driver_sifive_clic0_control_base((struct metal_interrupt *)clic);
    int num_subinterrupts = __metal_driver_sifive_clic0_num_subinterrupts((struct metal_interrupt *)clic);

    if (id < num_subinterrupts) {
        __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                       METAL_SIFIVE_CLIC0_MMODE_APERTURE + 
                                       METAL_SIFIVE_CLIC0_CLICINTIP_BASE + id)) = METAL_ENABLE;
        return 0;
    }
    return -1;
}

int __metal_clic0_interrupt_clear (struct __metal_driver_sifive_clic0 *clic, int id)
{
    unsigned long control_base = __metal_driver_sifive_clic0_control_base((struct metal_interrupt *)clic);
    int num_subinterrupts = __metal_driver_sifive_clic0_num_subinterrupts((struct metal_interrupt *)clic);

    if (id < num_subinterrupts) {
        __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                       METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                       METAL_SIFIVE_CLIC0_CLICINTIP_BASE + id)) = METAL_DISABLE;
        return 0;
    }
    return -1;
}

int __metal_clic0_configure_set_vector_mode (struct __metal_driver_sifive_clic0 *clic, metal_vector_mode mode)
{
    struct __metal_clic_cfg cfg = __metal_clic0_configuration(clic, NULL);

    switch (mode) {
    case METAL_SELECTIVE_NONVECTOR_MODE:
        cfg.nvbit = METAL_CLIC_NONVECTOR;
        __metal_controller_interrupt_vector(mode, &clic->metal_mtvt_table);
        break;
    case METAL_SELECTIVE_VECTOR_MODE:
        cfg.nvbit = METAL_CLIC_VECTORED;
        __metal_controller_interrupt_vector(mode, &clic->metal_mtvt_table);
        break;
    case METAL_HARDWARE_VECTOR_MODE:
        cfg.nvbit = METAL_CLIC_VECTORED;
        __metal_controller_interrupt_vector(mode, &clic->metal_mtvt_table);
        break;
    default:
        return -1;
    }
    __metal_clic0_configuration(clic, &cfg);
    return 0;
}

metal_vector_mode __metal_clic0_configure_get_vector_mode (struct __metal_driver_sifive_clic0 *clic)
{
    struct __metal_clic_cfg cfg = __metal_clic0_configuration(clic, NULL);
    metal_vector_mode mode = __metal_controller_interrupt_vector_mode();

    if (mode == METAL_SELECTIVE_VECTOR_MODE) { 
        if (cfg.nvbit) {
            return METAL_SELECTIVE_VECTOR_MODE;
        } else {
            return METAL_SELECTIVE_NONVECTOR_MODE;
        }
    } else {
        return mode;
    }
}

int __metal_clic0_configure_set_privilege (struct __metal_driver_sifive_clic0 *clic, metal_intr_priv_mode priv)
{
    struct __metal_clic_cfg cfg = __metal_clic0_configuration(clic, NULL);

    cfg.nmbits = priv;
    __metal_clic0_configuration(clic, &cfg);
    return 0;
}

metal_intr_priv_mode __metal_clic0_configure_get_privilege (struct __metal_driver_sifive_clic0 *clic)
{
    struct __metal_clic_cfg cfg = __metal_clic0_configuration(clic, NULL);

    return cfg.nmbits;
}

int __metal_clic0_configure_set_level (struct __metal_driver_sifive_clic0 *clic, int level)
{
    struct __metal_clic_cfg cfg = __metal_clic0_configuration(clic, NULL);

    cfg.nlbits = level & 0xF;
    __metal_clic0_configuration(clic, &cfg);
    return 0;
}

int __metal_clic0_configure_get_level (struct __metal_driver_sifive_clic0 *clic)
{
    struct __metal_clic_cfg cfg = __metal_clic0_configuration(clic, NULL);

    return cfg.nlbits;
}

unsigned long long __metal_clic0_mtime_get (struct __metal_driver_sifive_clic0 *clic)
{
    __metal_io_u32 lo, hi;
    unsigned long control_base = __metal_driver_sifive_clic0_control_base((struct metal_interrupt *)clic);

    /* Guard against rollover when reading */
    do {
	hi = __METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base + METAL_SIFIVE_CLIC0_MTIME + 4));
	lo = __METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base + METAL_SIFIVE_CLIC0_MTIME));
    } while (__METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base + METAL_SIFIVE_CLIC0_MTIME + 4)) != hi);

    return (((unsigned long long)hi) << 32) | lo;
}

int __metal_driver_sifive_clic0_mtimecmp_set(struct metal_interrupt *controller,
                                             int hartid,
                                             unsigned long long time)
{   
    struct __metal_driver_sifive_clic0 *clic =
                              (struct __metal_driver_sifive_clic0 *)(controller);

    unsigned long control_base = __metal_driver_sifive_clic0_control_base((struct metal_interrupt *)clic);
    /* Per spec, the RISC-V MTIME/MTIMECMP registers are 64 bit,
     * and are NOT internally latched for multiword transfers.
     * Need to be careful about sequencing to avoid triggering
     * spurious interrupts: For that set the high word to a max
     * value first.
     */
    __METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base + (8 * hartid) + METAL_SIFIVE_CLIC0_MTIMECMP_BASE + 4)) = 0xFFFFFFFF;
    __METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base + (8 * hartid) + METAL_SIFIVE_CLIC0_MTIMECMP_BASE)) = (__metal_io_u32)time;
    __METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base + (8 * hartid) + METAL_SIFIVE_CLIC0_MTIMECMP_BASE + 4)) = (__metal_io_u32)(time >> 32);
    return 0;
}

void __metal_clic0_handler (int id, void *priv)
{
    struct __metal_driver_sifive_clic0 *clic = priv;
    int num_subinterrupts = __metal_driver_sifive_clic0_num_subinterrupts((struct metal_interrupt *)clic);

    if ( (id < num_subinterrupts) && (clic->metal_exint_table[id].handler) ) {
        clic->metal_exint_table[id].handler(id, clic->metal_exint_table[id].exint_data);
    }
}

void __metal_clic0_default_handler (int id, void *priv) {
    metal_shutdown(300);
}

void __metal_clic0_default_vector_handler (void) {
    metal_shutdown(400);
}

void __metal_driver_sifive_clic0_init (struct metal_interrupt *controller)
{
    struct __metal_driver_sifive_clic0 *clic =
                              (struct __metal_driver_sifive_clic0 *)(controller);

    if ( !clic->init_done ) {
        int level, max_levels, line, num_interrupts, num_subinterrupts;
        struct __metal_clic_cfg cfg = __metal_clic_defaultcfg;
        struct metal_interrupt *intc =
	    __metal_driver_sifive_clic0_interrupt_parent(controller);

        /* Initialize ist parent controller, aka cpu_intc. */
        intc->vtable->interrupt_init(intc);
        __metal_controller_interrupt_vector(METAL_SELECTIVE_NONVECTOR_MODE,
                                            &clic->metal_mtvt_table);

        /*
         * Register its interrupts with with parent controller,
         * aka sw, timer and ext to its default isr
         */
	num_interrupts = __metal_driver_sifive_clic0_num_interrupts(controller);
        for (int i = 0; i < num_interrupts; i++) {
	    line = __metal_driver_sifive_clic0_interrupt_lines(controller, i);
            intc->vtable->interrupt_register(intc, line, NULL, clic);
        }

        /* Default CLIC mode to per dts */
	max_levels = __metal_driver_sifive_clic0_max_levels(controller);
        cfg.nlbits = (max_levels > METAL_CLIC_MAX_NLBITS) ?
                                METAL_CLIC_MAX_NLBITS : max_levels;
        __metal_clic0_configuration(clic, &cfg);

        level = (1 << cfg.nlbits) - 1;
	num_subinterrupts = __metal_driver_sifive_clic0_num_subinterrupts(controller);
        clic->metal_mtvt_table[0] = &__metal_clic0_handler;
        for (int i = 1; i < num_subinterrupts; i++) {
            clic->metal_mtvt_table[i] = NULL;
            clic->metal_exint_table[i].handler = NULL;
            clic->metal_exint_table[i].sub_int = NULL;
            clic->metal_exint_table[i].exint_data = NULL;
            __metal_clic0_interrupt_disable(clic, i);
            __metal_clic0_interrupt_set_level(clic, i, level);
        }
	clic->init_done = 1;
    }	
}

int __metal_driver_sifive_clic0_register (struct metal_interrupt *controller,
                                        int id, metal_interrupt_handler_t isr,
                                        void *priv)
{   
    int rc = -1;
    int num_subinterrupts;
    struct __metal_driver_sifive_clic0 *clic =
                              (struct __metal_driver_sifive_clic0 *)(controller);
    struct metal_interrupt *intc =
                       __metal_driver_sifive_clic0_interrupt_parent(controller);
    metal_vector_mode mode = __metal_clic0_configure_get_vector_mode(clic);
    
    if ( ( (mode == METAL_SELECTIVE_VECTOR_MODE) &&
           (__metal_clic0_interrupt_is_vectored(clic, id)) ) ||
         (mode == METAL_HARDWARE_VECTOR_MODE) ||
         (mode == METAL_VECTOR_MODE) ||
         (mode == METAL_DIRECT_MODE) ) {
        return rc;
    }

    /* Register its interrupts with parent controller */
    if (id < METAL_INTERRUPT_ID_CSW) {
        return intc->vtable->interrupt_register(intc, id, isr, priv);
    }
    
    /* 
     * CLIC (sub-interrupts) devices interrupts start at 16 but offset from 0
     * Reset the IDs to reflects this.
     */
    num_subinterrupts = __metal_driver_sifive_clic0_num_subinterrupts(controller);
    if (id < num_subinterrupts) {
        if ( isr) {
            clic->metal_exint_table[id].handler = isr;
            clic->metal_exint_table[id].exint_data = priv;
        } else {
            clic->metal_exint_table[id].handler = __metal_clic0_default_handler;
            clic->metal_exint_table[id].sub_int = priv;
        }
        rc = 0;
    }
    return rc;
}

int __metal_driver_sifive_clic0_vector_register (struct metal_interrupt *controller,
                                                 int id, metal_interrupt_vector_handler_t isr,
                                                 void *priv)
{
    int rc = -1;
    struct __metal_driver_sifive_clic0 *clic =
                              (struct __metal_driver_sifive_clic0 *)(controller);
    struct metal_interrupt *intc =
                       __metal_driver_sifive_clic0_interrupt_parent(controller);
    int num_subinterrupts = __metal_driver_sifive_clic0_num_subinterrupts(controller);
    metal_vector_mode mode = __metal_clic0_configure_get_vector_mode(clic);

    if ((mode != METAL_SELECTIVE_VECTOR_MODE) && (mode != METAL_HARDWARE_VECTOR_MODE)) {
        return rc;
    }
    if ((mode == METAL_SELECTIVE_VECTOR_MODE) &&
        (__metal_clic0_interrupt_is_vectored(clic, id) == 0) ) {
        return rc;
    }
    if (id < num_subinterrupts) {
        if ( isr) {
            clic->metal_mtvt_table[id] = isr;
            clic->metal_exint_table[id].exint_data = priv;        
        } else {
            clic->metal_mtvt_table[id] = __metal_clic0_default_vector_handler;
            clic->metal_exint_table[id].sub_int = priv;
        }
        rc = 0;
    }
    return rc;
}

int __metal_driver_sifive_clic0_enable (struct metal_interrupt *controller, int id)
{
    struct __metal_driver_sifive_clic0 *clic =
                              (struct __metal_driver_sifive_clic0 *)(controller);
    return __metal_clic0_interrupt_enable(clic, id);
}

int __metal_driver_sifive_clic0_disable (struct metal_interrupt *controller, int id)
{
    struct __metal_driver_sifive_clic0 *clic =
                              (struct __metal_driver_sifive_clic0 *)(controller);
    return __metal_clic0_interrupt_disable(clic, id);
}

int __metal_driver_sifive_clic0_enable_interrupt_vector(struct metal_interrupt *controller, int id)
{
    int rc = -1;
    int num_subinterrupts = __metal_driver_sifive_clic0_num_subinterrupts(controller);
    struct __metal_driver_sifive_clic0 *clic =
                              (struct __metal_driver_sifive_clic0 *)(controller);
    metal_vector_mode mode = __metal_clic0_configure_get_vector_mode(clic);

    if ((mode != METAL_SELECTIVE_VECTOR_MODE) && (mode != METAL_HARDWARE_VECTOR_MODE)) {
        return rc;
    }
    if (id < num_subinterrupts) {
        __metal_clic0_interrupt_set_vector_mode(clic, id, METAL_ENABLE);
        return 0;
    }
    return -1;
}

int __metal_driver_sifive_clic0_disable_interrupt_vector(struct metal_interrupt *controller, int id)
{
    int num_subinterrupts;
    struct __metal_driver_sifive_clic0 *clic =
                              (struct __metal_driver_sifive_clic0 *)(controller);

    num_subinterrupts = __metal_driver_sifive_clic0_num_subinterrupts(controller);
    if (id < num_subinterrupts) {
        __metal_clic0_interrupt_set_vector_mode(clic, id, METAL_DISABLE);
        return 0;
    }
    return -1;
}

metal_vector_mode __metal_driver_sifive_clic0_get_vector_mode (struct metal_interrupt *controller)
{
    struct __metal_driver_sifive_clic0 *clic =
                              (struct __metal_driver_sifive_clic0 *)(controller);
    return __metal_clic0_configure_get_vector_mode(clic);
}

int __metal_driver_sifive_clic0_set_vector_mode (struct metal_interrupt *controller, metal_vector_mode mode)
{
    struct __metal_driver_sifive_clic0 *clic =
                              (struct __metal_driver_sifive_clic0 *)(controller);
    return __metal_clic0_configure_set_vector_mode(clic, mode);
}

metal_intr_priv_mode  __metal_driver_sifive_clic0_get_privilege (struct metal_interrupt *controller)
{
    struct __metal_driver_sifive_clic0 *clic =
                              (struct __metal_driver_sifive_clic0 *)(controller);
    return __metal_clic0_configure_get_privilege(clic);
}

int __metal_driver_sifive_clic0_set_privilege (struct metal_interrupt *controller, metal_intr_priv_mode priv)
{
    struct __metal_driver_sifive_clic0 *clic =
                              (struct __metal_driver_sifive_clic0 *)(controller);
    return __metal_clic0_configure_set_privilege(clic, priv);
}

unsigned int __metal_driver_sifive_clic0_get_threshold (struct metal_interrupt *controller)
{
    struct __metal_driver_sifive_clic0 *clic =
                              (struct __metal_driver_sifive_clic0 *)(controller);
    return __metal_clic0_configure_get_level(clic);
}

int __metal_driver_sifive_clic0_set_threshold (struct metal_interrupt *controller, unsigned int level)
{
    struct __metal_driver_sifive_clic0 *clic =
                              (struct __metal_driver_sifive_clic0 *)(controller);
    return __metal_clic0_configure_set_level(clic, level);
}

unsigned int __metal_driver_sifive_clic0_get_priority (struct metal_interrupt *controller, int id)
{   
    struct __metal_driver_sifive_clic0 *clic =
                              (struct __metal_driver_sifive_clic0 *)(controller);
    return __metal_clic0_interrupt_get_priority(clic, id);
}

int __metal_driver_sifive_clic0_set_priority (struct metal_interrupt *controller, int id, unsigned int priority)
{   
    struct __metal_driver_sifive_clic0 *clic =
                              (struct __metal_driver_sifive_clic0 *)(controller);
    return __metal_clic0_interrupt_set_priority(clic, id, priority);
}

int __metal_driver_sifive_clic0_clear_interrupt (struct metal_interrupt *controller, int id)
{
    struct __metal_driver_sifive_clic0 *clic =
                              (struct __metal_driver_sifive_clic0 *)(controller);
    return __metal_clic0_interrupt_clear(clic, id);
}

int __metal_driver_sifive_clic0_set_interrupt (struct metal_interrupt *controller, int id)
{
    struct __metal_driver_sifive_clic0 *clic =
                              (struct __metal_driver_sifive_clic0 *)(controller);
    return __metal_clic0_interrupt_set(clic, id);
}

int __metal_driver_sifive_clic0_command_request (struct metal_interrupt *controller,
                                               int command, void *data)
{
    int hartid;
    int rc = -1;
    struct __metal_driver_sifive_clic0 *clic =
                              (struct __metal_driver_sifive_clic0 *)(controller);
    unsigned long control_base = __metal_driver_sifive_clic0_control_base(controller);

    switch (command) {
    case METAL_TIMER_MTIME_GET:
        if (data) {
	    *(unsigned long long *)data = __metal_clic0_mtime_get(clic);
            rc = 0;
        }
        break;
    case METAL_SOFTWARE_IPI_CLEAR:
	if (data) {
	    hartid = *(int *)data;
            __METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base +
					       (hartid * 4))) = METAL_DISABLE;
           __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                              METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                              METAL_SIFIVE_CLIC0_CLICINTIP_BASE)) = METAL_DISABLE;
            rc = 0;
        }
        break;
    case METAL_SOFTWARE_IPI_SET:
	if (data) {
	    hartid = *(int *)data;
            __METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base +
					       (hartid * 4))) = METAL_ENABLE;
            __METAL_ACCESS_ONCE((__metal_io_u8 *)(control_base +
                                               METAL_SIFIVE_CLIC0_MMODE_APERTURE +
                                               METAL_SIFIVE_CLIC0_CLICINTIP_BASE)) = METAL_ENABLE;
            rc = 0;
        }
        break;
    case METAL_SOFTWARE_MSIP_GET:
        rc = 0;
	if (data) {
	    hartid = *(int *)data;
            rc = __METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base +
						    (hartid * 4)));
        }
        break;
    default:
	break;
    }

    return rc;
}
__METAL_DEFINE_VTABLE(__metal_driver_vtable_sifive_clic0) = {
    .clic_vtable.interrupt_init     = __metal_driver_sifive_clic0_init,
    .clic_vtable.interrupt_register = __metal_driver_sifive_clic0_register,
    .clic_vtable.interrupt_vector_register = __metal_driver_sifive_clic0_vector_register,
    .clic_vtable.interrupt_enable   = __metal_driver_sifive_clic0_enable,
    .clic_vtable.interrupt_disable  = __metal_driver_sifive_clic0_disable,
    .clic_vtable.interrupt_vector_enable   = __metal_driver_sifive_clic0_enable_interrupt_vector,
    .clic_vtable.interrupt_vector_disable  = __metal_driver_sifive_clic0_disable_interrupt_vector,
    .clic_vtable.interrupt_get_vector_mode = __metal_driver_sifive_clic0_get_vector_mode,
    .clic_vtable.interrupt_set_vector_mode = __metal_driver_sifive_clic0_set_vector_mode,
    .clic_vtable.interrupt_get_privilege   = __metal_driver_sifive_clic0_get_privilege,
    .clic_vtable.interrupt_set_privilege   = __metal_driver_sifive_clic0_set_privilege,
    .clic_vtable.interrupt_get_threshold   = __metal_driver_sifive_clic0_get_threshold,
    .clic_vtable.interrupt_set_threshold   = __metal_driver_sifive_clic0_set_threshold,
    .clic_vtable.interrupt_get_priority    = __metal_driver_sifive_clic0_get_priority,
    .clic_vtable.interrupt_set_priority    = __metal_driver_sifive_clic0_set_priority,
    .clic_vtable.interrupt_clear    = __metal_driver_sifive_clic0_clear_interrupt,
    .clic_vtable.interrupt_set      = __metal_driver_sifive_clic0_set_interrupt,
    .clic_vtable.command_request    = __metal_driver_sifive_clic0_command_request,
    .clic_vtable.mtimecmp_set       = __metal_driver_sifive_clic0_mtimecmp_set,
};

#endif /* METAL_SIFIVE_CLIC0 */

typedef int no_empty_translation_units;
