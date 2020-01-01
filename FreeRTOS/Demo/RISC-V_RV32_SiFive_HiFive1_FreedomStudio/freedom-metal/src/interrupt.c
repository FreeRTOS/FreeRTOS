/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <string.h>
#include <metal/interrupt.h>
#include <metal/machine.h>

struct metal_interrupt* metal_interrupt_get_controller (metal_intr_cntrl_type cntrl,
                                                        int id)
{
    switch (cntrl) {
    case METAL_CPU_CONTROLLER:
        break;
    case METAL_CLINT_CONTROLLER:
#ifdef __METAL_DT_RISCV_CLINT0_HANDLE
        return __METAL_DT_RISCV_CLINT0_HANDLE;
#endif
        break;
    case METAL_CLIC_CONTROLLER:
#ifdef __METAL_DT_SIFIVE_CLIC0_HANDLE
        return __METAL_DT_SIFIVE_CLIC0_HANDLE;
#endif
        break;
    case METAL_PLIC_CONTROLLER:
#ifdef __METAL_DT_RISCV_PLIC0_HANDLE
        return __METAL_DT_RISCV_PLIC0_HANDLE;
#endif
        break;
    }
    return NULL;
}

extern __inline__ void metal_interrupt_init(struct metal_interrupt *controller);

extern __inline__ int metal_interrupt_set_vector_mode(struct metal_interrupt *controller,
                                                  metal_vector_mode mode);
extern __inline__ metal_vector_mode metal_interrupt_get_vector_mode(struct metal_interrupt *controller);

extern __inline__ int metal_interrupt_set_privilege(struct metal_interrupt *controller,
                                                 metal_intr_priv_mode mode);
extern __inline__ metal_intr_priv_mode metal_interrupt_get_privilege(struct metal_interrupt *controller);

extern __inline__ int metal_interrupt_set_threshold(struct metal_interrupt *controller,
                                                unsigned int level);
extern __inline__ unsigned int metal_interrupt_get_threshold(struct metal_interrupt *controller);

extern __inline__ unsigned int metal_interrupt_get_priority(struct metal_interrupt *controller, int id);

extern __inline__ int metal_interrupt_set_priority(struct metal_interrupt *controller, int id, unsigned int priority);

extern __inline__ int metal_interrupt_clear(struct metal_interrupt *controller, int id);

extern __inline__ int metal_interrupt_set(struct metal_interrupt *controller, int id);

extern __inline__ int metal_interrupt_register_handler(struct metal_interrupt *controller,
						 int id,
						 metal_interrupt_handler_t handler,
						 void *priv);

extern __inline__ int metal_interrupt_register_vector_handler(struct metal_interrupt *controller,
                                                int id,
                                                metal_interrupt_vector_handler_t handler,
                                                void *priv_data);

extern __inline__ int metal_interrupt_enable(struct metal_interrupt *controller, int id);

extern __inline__ int metal_interrupt_disable(struct metal_interrupt *controller, int id);

extern __inline__ unsigned int metal_interrupt_get_threshold(struct metal_interrupt *controller);

extern __inline__ int metal_interrupt_set_threshold(struct metal_interrupt *controller, unsigned int threshold);

extern __inline__ unsigned int metal_interrupt_get_priority(struct metal_interrupt *controller, int id);

extern __inline__ int metal_interrupt_set_priority(struct metal_interrupt *controller, int id, unsigned int priority);

extern __inline__ int metal_interrupt_vector_enable(struct metal_interrupt *controller, int id);

extern __inline__ int metal_interrupt_vector_disable(struct metal_interrupt *controller, int id);

extern __inline__ int _metal_interrupt_command_request(struct metal_interrupt *controller,
                                         	int cmd, void *data);
