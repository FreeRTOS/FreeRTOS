/* Copyright 2018 SiFive, Inc */

/* SPDX-License-Identifier: Apache-2.0 */

/*! @file cpu.h
 *  @brief API for accessing CPU capabilities.
 */

#ifndef METAL__CPU_H
#define METAL__CPU_H

#include <metal/interrupt.h>
#include <stdint.h>

struct metal_cpu;

/*!
 * @brief Function signature for exception handlers
 */
typedef void (*metal_exception_handler_t)(struct metal_cpu *cpu, int ecode);

struct metal_cpu_vtable {
    unsigned long long (*mcycle_get)(struct metal_cpu *cpu);
    unsigned long long (*timebase_get)(struct metal_cpu *cpu);
    unsigned long long (*mtime_get)(struct metal_cpu *cpu);
    int (*mtimecmp_set)(struct metal_cpu *cpu, unsigned long long time);
    struct metal_interrupt *(*tmr_controller_interrupt)(struct metal_cpu *cpu);
    int (*get_tmr_interrupt_id)(struct metal_cpu *cpu);
    struct metal_interrupt *(*sw_controller_interrupt)(struct metal_cpu *cpu);
    int (*get_sw_interrupt_id)(struct metal_cpu *cpu);
    int (*set_sw_ipi)(struct metal_cpu *cpu, int hartid);
    int (*clear_sw_ipi)(struct metal_cpu *cpu, int hartid);
    int (*get_msip)(struct metal_cpu *cpu, int hartid);
    struct metal_interrupt *(*controller_interrupt)(struct metal_cpu *cpu);
    int (*exception_register)(struct metal_cpu *cpu, int ecode,
                              metal_exception_handler_t handler);
    int (*get_ilen)(struct metal_cpu *cpu, uintptr_t epc);
    uintptr_t (*get_epc)(struct metal_cpu *cpu);
    int (*set_epc)(struct metal_cpu *cpu, uintptr_t epc);
    struct metal_buserror *(*get_buserror)(struct metal_cpu *cpu);
};

/*! @brief A device handle for a CPU hart
 */
struct metal_cpu {
    const struct metal_cpu_vtable *vtable;
};

/*! @brief Get a reference to a CPU hart
 *
 * @param hartid The ID of the desired CPU hart
 * @return A pointer to the CPU device handle
 */
struct metal_cpu *metal_cpu_get(unsigned int hartid);

/*! @brief Get the hartid of the CPU hart executing this function
 *
 * @return The hartid of the current CPU hart */
int metal_cpu_get_current_hartid(void);

/*! @brief Get the number of CPU harts
 *
 * @return The number of CPU harts */
int metal_cpu_get_num_harts(void);

/*! @brief Get the CPU cycle count timer value
 *
 * Get the value of the cycle count timer for a given CPU
 *
 * @param cpu The CPU device handle
 * @return The value of the CPU cycle count timer
 */
__inline__ unsigned long long metal_cpu_get_timer(struct metal_cpu *cpu) {
    return cpu->vtable->mcycle_get(cpu);
}

/*! @brief Get the timebase of the CPU
 *
 * Get the value of the timebase of the cycle count timer
 *
 * @param cpu The CPU device handle
 * @return The value of the cycle count timer timebase
 */
__inline__ unsigned long long metal_cpu_get_timebase(struct metal_cpu *cpu) {
    return cpu->vtable->timebase_get(cpu);
}

/*! @brief Get the value of the mtime RTC
 *
 * Get the value of the mtime real-time clock. The CPU interrupt controller
 * must be initialized before this function is called or the return value
 * will be 0.
 *
 * @param cpu The CPU device handle
 * @return The value of mtime, or 0 if failure
 */
__inline__ unsigned long long metal_cpu_get_mtime(struct metal_cpu *cpu) {
    return cpu->vtable->mtime_get(cpu);
}

/*! @brief Set the value of the RTC mtimecmp RTC
 *
 * Set the value of the mtime real-time clock compare register. The CPU
 * interrupt controller must be initialized before this function is called
 * or the return value will be -1;
 *
 * @param cpu The CPU device handle
 * @param time The value to set the compare register to
 * @return The value of mtimecmp or -1 if error
 */
__inline__ int metal_cpu_set_mtimecmp(struct metal_cpu *cpu,
                                      unsigned long long time) {
    return cpu->vtable->mtimecmp_set(cpu, time);
}

/*! @brief Get a reference to RTC timer interrupt controller
 *
 * Get a reference to the interrupt controller for the real-time clock
 * interrupt. The controller returned by this function must be initialized
 * before any interrupts are registered or enabled with it.
 *
 * @param cpu The CPU device handle
 * @return A pointer to the timer interrupt handle
 */
__inline__ struct metal_interrupt *
metal_cpu_timer_interrupt_controller(struct metal_cpu *cpu) {
    return cpu->vtable->tmr_controller_interrupt(cpu);
}

/*! @brief Get the RTC timer interrupt id
 *
 * Get the interrupt ID of the real-time clock interrupt
 *
 * @param cpu The CPU device handle
 * @return The timer interrupt ID
 */
__inline__ int metal_cpu_timer_get_interrupt_id(struct metal_cpu *cpu) {
    return cpu->vtable->get_tmr_interrupt_id(cpu);
}

/*! @brief Get a reference to the software interrupt controller
 *
 * Get a reference to the interrupt controller for the software/inter-process
 * interrupt. The controller returned by this function must be initialized
 * before any interrupts are registered or enabled with it.
 *
 * @param cpu The CPU device handle
 * @return A pointer to the software interrupt handle
 */
__inline__ struct metal_interrupt *
metal_cpu_software_interrupt_controller(struct metal_cpu *cpu) {
    return cpu->vtable->sw_controller_interrupt(cpu);
}

/*! @brief Get the software interrupt id
 *
 * Get the interrupt ID for the software/inter-process interrupt
 *
 * @param cpu The CPU device handle
 * @return the software interrupt ID
 */
__inline__ int metal_cpu_software_get_interrupt_id(struct metal_cpu *cpu) {
    return cpu->vtable->get_sw_interrupt_id(cpu);
}

/*!
 * @brief Set the inter-process interrupt for a hart
 *
 * Trigger a software/inter-process interrupt for a hart. The CPU interrupt
 * controller for the CPU handle passed to this function must be initialized
 * before this function is called.
 *
 * @param cpu The CPU device handle
 * @param hartid The CPU hart ID to be interrupted
 * @return 0 upon success
 */
__inline__ int metal_cpu_software_set_ipi(struct metal_cpu *cpu, int hartid) {
    return cpu->vtable->set_sw_ipi(cpu, hartid);
}

/*!
 * @brief Clear the inter-process interrupt for a hart
 *
 * Clear the software/inter-process interrupt for a hart. The CPU interrupt
 * controller for the CPU handle passed to this function must be initialized
 * before this function is called.
 *
 * @param cpu The CPU device handle
 * @param hartid The CPU hart ID to clear
 * @return 0 upon success
 */
__inline__ int metal_cpu_software_clear_ipi(struct metal_cpu *cpu, int hartid) {
    return cpu->vtable->clear_sw_ipi(cpu, hartid);
}

/*!
 * @brief Get the value of MSIP for the given hart
 *
 * Get the value of the machine software interrupt pending bit for
 * the given hart. The CPU interrupt controller for the CPU handle passed
 * as argument to this function must be initialized before this function
 * is called.
 *
 * @param cpu the CPU device handle
 * @param hartid The CPU hart to read
 * @return 0 upon success
 */
__inline__ int metal_cpu_get_msip(struct metal_cpu *cpu, int hartid) {
    return cpu->vtable->get_msip(cpu, hartid);
}

/*!
 * @brief Get the interrupt controller for the CPU
 *
 * Get the CPU interrupt controller. The controller returned by this
 * function must be initialized before any interrupts are registered
 * or enabled and before any exception handlers are registered with
 * this CPU.
 *
 * @param cpu The CPU device handle
 * @return The handle for the CPU interrupt controller
 */
__inline__ struct metal_interrupt *
metal_cpu_interrupt_controller(struct metal_cpu *cpu) {
    return cpu->vtable->controller_interrupt(cpu);
}

/*!
 * @brief Register an exception handler
 *
 * Register an exception handler for the CPU. The CPU interrupt controller must
 * be initialized before this function is called.
 *
 * @param cpu The CPU device handle
 * @param ecode The exception code to register a handler for
 * @param handler Callback function for the exception handler
 * @return 0 upon success
 */
__inline__ int metal_cpu_exception_register(struct metal_cpu *cpu, int ecode,
                                            metal_exception_handler_t handler) {
    return cpu->vtable->exception_register(cpu, ecode, handler);
}

/*!
 * @brief Get the length of an instruction in bytes
 *
 * Get the length of an instruction in bytes.
 *
 * On RISC-V platforms, this is useful for detecting whether an instruction is
 * compressed (2 bytes long) or uncompressed (4 bytes long).
 *
 * This function is useful in conjuction with `metal_cpu_get_exception_pc()`
 * and `metal_cpu_set_exception_pc()` in order to cause the exception handler to
 * return execution after the faulting instruction.
 *
 * @param cpu The CPU device handle
 * @param epc The address of the instruction to measure
 * @return the length of the instruction in bytes
 */
__inline__ int metal_cpu_get_instruction_length(struct metal_cpu *cpu,
                                                uintptr_t epc) {
    return cpu->vtable->get_ilen(cpu, epc);
}

/*!
 * @brief Get the program counter of the current exception.
 *
 * This function must be called within an exception handler. The behavior is
 * undefined outside of an exception handler.
 *
 * @param cpu The CPU device handle
 * @return The value of the program counter at the time of the exception
 */
__inline__ uintptr_t metal_cpu_get_exception_pc(struct metal_cpu *cpu) {
    return cpu->vtable->get_epc(cpu);
}

/*!
 * @brief Set the exception program counter
 *
 * This function must be called within an exception handler. The behavior
 * is undefined outside of an exception handler.
 *
 * This function can be used to cause an exception handler to return execution
 * to an address other than the one that caused the exception.
 *
 * @param cpu the CPU device handle
 * @param epc The address to set the exception program counter to
 * @return 0 upon success
 */
__inline__ int metal_cpu_set_exception_pc(struct metal_cpu *cpu,
                                          uintptr_t epc) {
    return cpu->vtable->set_epc(cpu, epc);
}

/*!
 * @brief Get the handle for the hart's bus error unit
 *
 * @param cpu The CPU device handle
 * @return A pointer to the bus error unit handle
 */
__inline__ struct metal_buserror *
metal_cpu_get_buserror(struct metal_cpu *cpu) {
    return cpu->vtable->get_buserror(cpu);
}

#endif
