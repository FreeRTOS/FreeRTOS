/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__INTERRUPT_H
#define METAL__INTERRUPT_H

/*! @file interrupt.h
 *  @brief API for registering and manipulating interrupts
 */

#include <stddef.h>

/*!
 * @brief Possible interrupt controllers
 */
typedef enum metal_interrupt_controller_ {
    METAL_CPU_CONTROLLER = 0,
    METAL_CLINT_CONTROLLER = 1,
    METAL_CLIC_CONTROLLER = 2,
    METAL_PLIC_CONTROLLER = 3
} metal_intr_cntrl_type;

/*!
 * @brief Possible mode of interrupts to operate
 */
typedef enum metal_vector_mode_ {
    METAL_DIRECT_MODE = 0,
    METAL_VECTOR_MODE = 1,
    METAL_SELECTIVE_NONVECTOR_MODE = 2,
    METAL_SELECTIVE_VECTOR_MODE = 3,
    METAL_HARDWARE_VECTOR_MODE = 4
} metal_vector_mode;

/*!
 * @brief Possible mode of privilege interrupts to operate
 */
typedef enum metal_intr_priv_mode_ {
    METAL_INTR_PRIV_M_MODE = 0,
    METAL_INTR_PRIV_MU_MODE = 1,
    METAL_INTR_PRIV_MSU_MODE = 2
} metal_intr_priv_mode;

/*!
 * @brief The bitmask of hart context
 */
typedef struct metal_affinity_ {
    unsigned long bitmask;
} metal_affinity;

#define for_each_metal_affinity(bit, metal_affinity)                           \
    for (bit = 0; metal_affinity.bitmask; bit++, metal_affinity.bitmask >>= 1)

#define metal_affinity_set_val(metal_affinity, val)                            \
    metal_affinity.bitmask = val;

#define metal_affinity_set_bit(metal_affinity, bit, val)                       \
    metal_affinity.bitmask |= ((val & 0x1) << bit);

/*!
 * @brief Function signature for interrupt callback handlers
 */
typedef void (*metal_interrupt_handler_t)(int, void *);
typedef void (*metal_interrupt_vector_handler_t)(void);

struct metal_interrupt;

struct metal_interrupt_vtable {
    void (*interrupt_init)(struct metal_interrupt *controller);
    int (*interrupt_set_vector_mode)(struct metal_interrupt *controller,
                                     metal_vector_mode mode);
    metal_vector_mode (*interrupt_get_vector_mode)(
        struct metal_interrupt *controller);
    int (*interrupt_set_privilege)(struct metal_interrupt *controller,
                                   metal_intr_priv_mode priv);
    metal_intr_priv_mode (*interrupt_get_privilege)(
        struct metal_interrupt *controller);
    int (*interrupt_clear)(struct metal_interrupt *controller, int id);
    int (*interrupt_set)(struct metal_interrupt *controller, int id);
    int (*interrupt_register)(struct metal_interrupt *controller, int id,
                              metal_interrupt_handler_t isr, void *priv_data);
    int (*interrupt_vector_register)(struct metal_interrupt *controller, int id,
                                     metal_interrupt_vector_handler_t isr,
                                     void *priv_data);
    int (*interrupt_enable)(struct metal_interrupt *controller, int id);
    int (*interrupt_disable)(struct metal_interrupt *controller, int id);
    int (*interrupt_vector_enable)(struct metal_interrupt *controller, int id);
    int (*interrupt_vector_disable)(struct metal_interrupt *controller, int id);
    unsigned int (*interrupt_get_threshold)(struct metal_interrupt *controller);
    int (*interrupt_set_threshold)(struct metal_interrupt *controller,
                                   unsigned int threshold);
    unsigned int (*interrupt_get_priority)(struct metal_interrupt *controller,
                                           int id);
    int (*interrupt_set_priority)(struct metal_interrupt *controller, int id,
                                  unsigned int priority);
    unsigned int (*interrupt_get_preemptive_level)(
        struct metal_interrupt *controller, int id);
    int (*interrupt_set_preemptive_level)(struct metal_interrupt *controller,
                                          int id, unsigned int level);
    int (*command_request)(struct metal_interrupt *controller, int cmd,
                           void *data);
    int (*mtimecmp_set)(struct metal_interrupt *controller, int hartid,
                        unsigned long long time);
    metal_affinity (*interrupt_affinity_enable)(
        struct metal_interrupt *controller, metal_affinity bitmask, int id);
    metal_affinity (*interrupt_affinity_disable)(
        struct metal_interrupt *controller, metal_affinity bitmask, int id);
    metal_affinity (*interrupt_affinity_set_threshold)(
        struct metal_interrupt *controller, metal_affinity bitmask,
        unsigned int threshold);
    unsigned int (*interrupt_affinity_get_threshold)(
        struct metal_interrupt *controller, int context_id);
};

/*!
 * @brief A handle for an interrupt
 */
struct metal_interrupt {
    const struct metal_interrupt_vtable *vtable;
};

/*!
 * @brief Initialize a given interrupt controller
 *
 * Initialize a given interrupt controller. This function must be called
 * before any interrupts are registered or enabled with the handler. It
 * is invalid to initialize an interrupt controller more than once.
 *
 * @param controller The handle for the interrupt controller
 */
__inline__ void metal_interrupt_init(struct metal_interrupt *controller) {
    controller->vtable->interrupt_init(controller);
}

/*!
 * @brief Get the handle for an given interrupt controller type
 * @param cntrl The type ofinterrupt controller
 * @param id The instance of the interrupt controller
 * @return A handle to the interrupt controller (CLINT, CLIC, PLIC), or
 * NULL if none is found for the requested label
 */
struct metal_interrupt *
metal_interrupt_get_controller(metal_intr_cntrl_type cntrl, int id);

/*!
 * @brief Configure vector mode for an interrupt controller
 *
 * Configure vector mode for an interrupt controller.
 * This function must be called after initialization and before
 * configuring individual interrupts, registering ISR.
 *
 * @param controller The handle for the interrupt controller
 * @param mode The vector mode of the interrupt controller.
 * @return 0 upon success
 */
__inline__ int
metal_interrupt_set_vector_mode(struct metal_interrupt *controller,
                                metal_vector_mode mode) {
    return controller->vtable->interrupt_set_vector_mode(controller, mode);
}

/*!
 * @brief Get vector mode of a given an interrupt controller
 *
 * Configure vector mode for an interrupt controller.
 * This function must be called after initialization and before
 * configuring individual interrupts, registering ISR.
 *
 * @param controller The handle for the interrupt controller
 * @param mode The vector mode of the interrupt controller.
 * @return The interrupt vector mode
 */
__inline__ metal_vector_mode
metal_interrupt_get_vector_mode(struct metal_interrupt *controller) {
    return controller->vtable->interrupt_get_vector_mode(controller);
}

/*!
 * @brief Configure privilege mode a of given interrupt controller
 *
 * Configure privilege mode for a given interrupt controller.
 * This function must be called after initialization and before
 * configuring individual interrupts, registering ISR.
 *
 * @param controller The handle for the interrupt controller
 * @param privilege The privilege mode of the interrupt controller.
 * @return 0 upon success
 */
__inline__ int metal_interrupt_set_privilege(struct metal_interrupt *controller,
                                             metal_intr_priv_mode privilege) {
    return controller->vtable->interrupt_set_privilege(controller, privilege);
}

/*!
 * @brief Get privilege mode a of given interrupt controller
 *
 * Get privilege mode for a given interrupt controller.
 * This function must be called after initialization and before
 * configuring individual interrupts, registering ISR.
 *
 * @param controller The handle for the interrupt controller
 * @return The interrupt privilege mode
 */
__inline__ metal_intr_priv_mode
metal_interrupt_get_privilege(struct metal_interrupt *controller) {
    return controller->vtable->interrupt_get_privilege(controller);
}

/*!
 * @brief clear an interrupt
 * @param controller The handle for the interrupt controller
 * @param id The interrupt ID to trigger
 * @return 0 upon success
 */
__inline__ int metal_interrupt_clear(struct metal_interrupt *controller,
                                     int id) {
    return controller->vtable->interrupt_clear(controller, id);
}

/*!
 * @brief Set an interrupt
 * @param controller The handle for the interrupt controller
 * @param id The interrupt ID to trigger
 * @return 0 upon success
 */
__inline__ int metal_interrupt_set(struct metal_interrupt *controller, int id) {
    return controller->vtable->interrupt_set(controller, id);
}

/*!
 * @brief Register an interrupt handler
 * @param controller The handle for the interrupt controller
 * @param id The interrupt ID to register
 * @param handler The interrupt handler callback
 * @param priv_data Private data for the interrupt handler
 * @return 0 upon success
 */
__inline__ int
metal_interrupt_register_handler(struct metal_interrupt *controller, int id,
                                 metal_interrupt_handler_t handler,
                                 void *priv_data) {
    return controller->vtable->interrupt_register(controller, id, handler,
                                                  priv_data);
}

/*!
 * @brief Register an interrupt vector handler
 * @param controller The handle for the interrupt controller
 * @param id The interrupt ID to register
 * @param handler The interrupt vector handler callback
 * @param priv_data Private data for the interrupt handler
 * @return 0 upon success
 */
__inline__ int metal_interrupt_register_vector_handler(
    struct metal_interrupt *controller, int id,
    metal_interrupt_vector_handler_t handler, void *priv_data) {
    return controller->vtable->interrupt_vector_register(controller, id,
                                                         handler, priv_data);
}

/*!
 * @brief Enable an interrupt
 * @param controller The handle for the interrupt controller
 * @param id The interrupt ID to enable
 * @return 0 upon success
 */
__inline__ int metal_interrupt_enable(struct metal_interrupt *controller,
                                      int id) {
    return controller->vtable->interrupt_enable(controller, id);
}

/*!
 * @brief Disable an interrupt
 * @param controller The handle for the interrupt controller
 * @param id The interrupt ID to disable
 * @return 0 upon success
 */
__inline__ int metal_interrupt_disable(struct metal_interrupt *controller,
                                       int id) {
    return controller->vtable->interrupt_disable(controller, id);
}

/*!
 * @brief Set interrupt threshold level
 * @param controller The handle for the interrupt controller
 * @param threshold The interrupt threshold level
 * @return 0 upon success
 */
__inline__ int metal_interrupt_set_threshold(struct metal_interrupt *controller,
                                             unsigned int level) {
    return controller->vtable->interrupt_set_threshold(controller, level);
}

/*!
 * @brief Get an interrupt threshold level
 * @param controller The handle for the interrupt controller
 * @return The interrupt threshold level
 */
__inline__ unsigned int
metal_interrupt_get_threshold(struct metal_interrupt *controller) {
    return controller->vtable->interrupt_get_threshold(controller);
}

/*!
 * @brief Set an interrupt priority level
 * @param controller The handle for the interrupt controller
 * @param id The interrupt ID to enable
 * @param priority The interrupt priority level
 * @return 0 upon success
 */
__inline__ int metal_interrupt_set_priority(struct metal_interrupt *controller,
                                            int id, unsigned int priority) {
    return controller->vtable->interrupt_set_priority(controller, id, priority);
}

/*!
 * @brief Get an interrupt priority level
 * @param controller The handle for the interrupt controller
 * @param id The interrupt ID to enable
 * @return The interrupt priority level
 */
__inline__ unsigned int
metal_interrupt_get_priority(struct metal_interrupt *controller, int id) {
    return controller->vtable->interrupt_get_priority(controller, id);
}

/*!
 * @brief Set preemptive level and priority for a given interrupt ID
 *
 * Set the preemptive level and priority for a given interrupt ID.
 *
 * @param controller The handle for the interrupt controller
 * @param id The interrupt ID to enable
 * @param level The interrupt level and priority are encoded together
 * @return 0 upon success
 */
__inline__ int
metal_interrupt_set_preemptive_level(struct metal_interrupt *controller, int id,
                                     unsigned int level) {
    if (controller->vtable->interrupt_set_preemptive_level)
        return controller->vtable->interrupt_set_preemptive_level(controller,
                                                                  id, level);
    else
        return 0;
}

/*!
 * @brief Get an interrupt preemptive level
 * @param controller The handle for the interrupt controller
 * @param id The interrupt ID to enable
 * @return The interrupt level
 */
__inline__ unsigned int
metal_interrupt_get_preemptive_level(struct metal_interrupt *controller,
                                     int id) {
    if (controller->vtable->interrupt_get_preemptive_level)
        return controller->vtable->interrupt_get_preemptive_level(controller,
                                                                  id);
    else
        return 0;
}

/*!
 * @brief Enable an interrupt vector
 * @param controller The handle for the interrupt controller
 * @param id The interrupt ID to enable
 * @return 0 upon success
 */
__inline__ int metal_interrupt_vector_enable(struct metal_interrupt *controller,
                                             int id) {
    return controller->vtable->interrupt_vector_enable(controller, id);
}

/*!
 * @brief Disable an interrupt vector
 * @param controller The handle for the interrupt controller
 * @param id The interrupt ID to disable
 * @return 0 upon success
 */
__inline__ int
metal_interrupt_vector_disable(struct metal_interrupt *controller, int id) {
    return controller->vtable->interrupt_vector_disable(controller, id);
}

/*!
 * @brief Default interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt)) metal_interrupt_vector_handler(void);

/*!
 * @brief Metal Software interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt))
metal_software_interrupt_vector_handler(void);

/*!
 * @brief Metal Timer interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt))
metal_timer_interrupt_vector_handler(void);

/*!
 * @brief Metal External interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt))
metal_external_interrupt_vector_handler(void);

/*!
 * @brief Metal Local 0 interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt)) metal_lc0_interrupt_vector_handler(void);

/*!
 * @brief Metal Local 1 interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt)) metal_lc1_interrupt_vector_handler(void);

/*!
 * @brief Metal Local 2 interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt)) metal_lc2_interrupt_vector_handler(void);

/*!
 * @brief Metal Local 3 interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt)) metal_lc3_interrupt_vector_handler(void);

/*!
 * @brief Metal Local 4 interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt)) metal_lc4_interrupt_vector_handler(void);

/*!
 * @brief Metal Local 5 interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt)) metal_lc5_interrupt_vector_handler(void);

/*!
 * @brief Metal Local 6 interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt)) metal_lc6_interrupt_vector_handler(void);

/*!
 * @brief Metal Local 7 interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt)) metal_lc7_interrupt_vector_handler(void);

/*!
 * @brief Metal Local 8 interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt)) metal_lc8_interrupt_vector_handler(void);

/*!
 * @brief Metal Local 9 interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt)) metal_lc9_interrupt_vector_handler(void);

/*!
 * @brief Metal Local 10 interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt)) metal_lc10_interrupt_vector_handler(void);

/*!
 * @brief Metal Local 11 interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt)) metal_lc11_interrupt_vector_handler(void);

/*!
 * @brief Metal Local 12 interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt)) metal_lc12_interrupt_vector_handler(void);

/*!
 * @brief Metal Local 13 interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt)) metal_lc13_interrupt_vector_handler(void);

/*!
 * @brief Metal Local 14 interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt)) metal_lc14_interrupt_vector_handler(void);

/*!
 * @brief Metal Local 15 interrupt vector handler, that can be overriden by user
 * @param None
 * @return None
 */
void __attribute__((weak, interrupt)) metal_lc15_interrupt_vector_handler(void);

/* Utilities function to controll, manages devices via a given interrupt
 * controller */
__inline__ int
_metal_interrupt_command_request(struct metal_interrupt *controller, int cmd,
                                 void *data) {
    return controller->vtable->command_request(controller, cmd, data);
}

/*!
 * @brief Enable an interrupt for the hart contexts
 * @param controller The handle for the interrupt controller
 * @param bitmask The bit mask of hart contexts to enable
 * @param id The interrupt ID to enable
 * @return The result of each hart context. 0 upon success at relevant bit.
 */
__inline__ metal_affinity
metal_interrupt_affinity_enable(struct metal_interrupt *controller,
                                metal_affinity bitmask, int id) {
    return controller->vtable->interrupt_affinity_enable(controller, bitmask,
                                                         id);
}

/*!
 * @brief Disable an interrupt for the hart contexts
 * @param controller The handle for the interrupt controller
 * @param bitmask The bit mask of hart contexts to disable
 * @param id The interrupt ID to disable
 * @return The result of each hart context. 0 upon success at relevant bit.
 */
__inline__ metal_affinity
metal_interrupt_affinity_disable(struct metal_interrupt *controller,
                                 metal_affinity bitmask, int id) {
    return controller->vtable->interrupt_affinity_disable(controller, bitmask,
                                                          id);
}

/*!
 * @brief Set interrupt threshold level for the hart contexts
 * @param controller The handle for the interrupt controller
 * @param bitmask The bit mask of hart contexts to set threshold
 * @param threshold The interrupt threshold level
 * @return The result of each hart context. 0 upon success at relevant bit.
 */
__inline__ metal_affinity
metal_interrupt_affinity_set_threshold(struct metal_interrupt *controller,
                                       metal_affinity bitmask,
                                       unsigned int level) {
    return controller->vtable->interrupt_affinity_set_threshold(controller,
                                                                bitmask, level);
}

/*!
 * @brief Get an interrupt threshold level from the hart context
 * @param controller The handle for the interrupt controller
 * @param context_id The hart context ID to get threshold
 * @return The interrupt threshold level
 */
__inline__ unsigned int
metal_interrupt_affinity_get_threshold(struct metal_interrupt *controller,
                                       int context_id) {
    return controller->vtable->interrupt_affinity_get_threshold(controller,
                                                                context_id);
}
#endif
