// Copyright 2019-2021 XMOS LIMITED.
// This Software is subject to the terms of the XMOS Public Licence: Version 1.

#ifndef RTOS_INTERRUPT_H_
#define RTOS_INTERRUPT_H_

#include <stdint.h>
#include <xs1.h>

#include "rtos_interrupt_impl.h"
#include "rtos_macros.h"

/** Define the function that enters the RTOS kernel and begins the scheduler.
 *  This should only be used by the RTOS entry function that starts the scheduler.
 *
 *  This macro will define two functions for you:
 *    - An ordinary function that may be called directly
 *      Its signature will be '*ret* *root_function* ( *...* )'
 *    - A function that will also reserve space for and set up a stack
 *      for handling RTOS interrupts.
 *      The function name is accessed using the RTOS_KERNEL_ENTRY() macro
 *
 *  You would normally use this macro only on the definition of the RTOS entry
 *  function that starts the scheduler.
 *
 *  The interrupt stack (kernel stack) is created on the core's stack with the
 *  ksp and sp being modified as necessary. When the function exits, neither the
 *  kernel stack nor ksp is valid.
 *
 *  The kernel stack allocated has enough space for the interrupt_callback_t
 *  function (+callees) in the rtos_isr 'group'. The use of the 'group' identifier
 *  allows a kernel stack to be no larger than that required by its greediest member.
 *
 *  **The kernel stack is not re-entrant so kernel mode must not be masked
 *  from within an interrupt_callback_t**
 *
 *  Example usage: \code
 *    DEFINE_RTOS_KERNEL_ENTRY(void, vPortStartSchedulerOnCore, void)
 *    {
 *      // This is the body of 'void vPortStartSchedulerOnCore(void)'
 *    }
 *  \endcode
 *
 *  \param ret              the return type of the ordinary function
 *  \param root_function    the name of the ordinary function
 *  \param ...              the arguments of the ordinary function
 */
#define DEFINE_RTOS_KERNEL_ENTRY(ret, root_function, ...) \
        _DEFINE_RTOS_KERNEL_ENTRY(ret, root_function, __VA_ARGS__)

/** Declare an RTOS interrupt permitting function
 *
 *  Use this macro when you require a declaration of your RTOS kernel entry function.
 *  This should only be used by the RTOS entry function that starts the scheduler.
 *
 *  Example usage: \code
 *    // In another file:
 *    //   DEFINE_RTOS_KERNEL_ENTRY(void, vPortStartSchedulerOnCore, void) { ... }
 *    DECLARE_RTOS_KERNEL_ENTRY(void, vPortStartSchedulerOnCore, void);
 *    ...
 *      par {
 *          RTOS_KERNEL_ENTRY(vPortStartSchedulerOnCore)();
 *      }
 *  \endcode
 *
 *  \param ret              the return type of the ordinary function
 *  \param root_function    the name of the ordinary function
 *  \param ...              the arguments of the ordinary function
 */
#define DECLARE_RTOS_KERNEL_ENTRY(ret, root_function, ...) \
        _XCORE_DECLARE_INTERRUPT_PERMITTED(ret, root_function, __VA_ARGS__)

/** The name of the defined RTOS kernel entry function
 *
 *  Use this macro for retriving the name of the declared RTOS kernel entry function.
 *  This is the name used to invoke the function.
 *
 *  \return     the name of the defined kernel entry function
 */
#define RTOS_KERNEL_ENTRY(root_function) _XCORE_INTERRUPT_PERMITTED(root_function)


/** Define an RTOS interrupt handling function
 *
 *  This macro will define two functions for you:
 *    - An ordinary function that may be called directly
 *      Its signature will be 'void *intrpt* ( void\* *data* )'
 *    - An interrupt_callback_t function for passing to a res_setup_interrupt_callback function.
 *      The interrupt_callback_t function name is accessed using the RTOS_INTERRUPT_CALLBACK() macro
 *
 *  **The kernel stack is not re-entrant so kernel mode must not be masked
 *  from within an interrupt_callback_t**
 *
 *  Example usage: \code
 *    DEFINE_RTOS_INTERRUPT_CALLBACK(myfunc, arg)
 *    {
 *      // This is the body of 'void myfunc(void* arg)'
 *    }
 *  \endcode
 *
 *  \param intrpt   this is the name of the ordinary function
 *  \param data     the name to use for the void* argument
 */
#define DEFINE_RTOS_INTERRUPT_CALLBACK(intrpt, data) \
        _DEFINE_RTOS_INTERRUPT_CALLBACK(intrpt, data)

/** Declare an RTOS interrupt handling function
 *
 *  Use this macro when you require a declaration of your interrupt function types
 *
 *  Example usage: \code
 *    DECLARE_RTOS_INTERRUPT_CALLBACK(myfunc, arg);
 *    chanend_setup_interrupt_callback(c, 0 , RTOS_INTERRUPT_CALLBACK(myfunc));
 *  \endcode
 *
 *  \param intrpt   this is the name of the ordinary function
 *  \param data     the name to use for the void* argument
 */
#define DECLARE_RTOS_INTERRUPT_CALLBACK(intrpt, data) \
        _DECLARE_RTOS_INTERRUPT_CALLBACK(intrpt, data)

/** The name of the defined 'interrupt_callback_t' function
 *
 *  Use this macro for retriving the name of the declared RTOS interrupt callback function.
 *  This is the name that is passed to *res*_setup_interrupt_callback() for registration.
 *
 *  \return     the name of the defined interrupt_callback_t function
 */
#define RTOS_INTERRUPT_CALLBACK(intrpt) _XCORE_INTERRUPT_CALLBACK(intrpt)


/**
 * This function gets the current interrupt mask.
 * A non-zero mask value means that interrupts are enabled.
 *
 * \returns the current interrupt mask.
 */
inline uint32_t rtos_interrupt_mask_get(void)
{
    uint32_t mask;

    asm volatile(
        "getsr r11," RTOS_STRINGIFY(XS1_SR_IEBLE_MASK) "\n"
        "mov %0, r11"
        : "=r"(mask)
        : /* no inputs */
        : /* clobbers */ "r11"
    );

    return mask;
}

 /**
  * This function masks (disables) all interrupts on the
  * calling core.
  *
  * \returns the previous value of the interrupt mask.
  * This value can be passed to rtos_interrupt_mask_set()
  * to restore the interrupt mask to its previous state.
  */
inline uint32_t rtos_interrupt_mask_all(void)
{
    uint32_t mask;

    asm volatile(
        "getsr r11," RTOS_STRINGIFY(XS1_SR_IEBLE_MASK) "\n"
        "mov %0, r11\n"
        "clrsr " RTOS_STRINGIFY(XS1_SR_IEBLE_MASK)
        : "=r"(mask)
        : /* no inputs */
        : /* clobbers */ "r11", "memory"
    );

    return mask;
}

/**
 * This function unmasks (enables) all interrupts on the
 * calling core.
 */
inline void rtos_interrupt_unmask_all(void)
{
    asm volatile(
        "setsr" RTOS_STRINGIFY(XS1_SR_IEBLE_MASK)
        : /* no outputs */
        : /* no inputs */
        : /* clobbers */ "memory"
    );
}

/**
 * This function sets the interrupt mask.
 * A non-zero mask value unmasks (enables) interrupts.
 *
 * \param mask The value to set the interrupt mask to.
 */
inline void rtos_interrupt_mask_set(uint32_t mask)
{
   if (mask != 0) {
       rtos_interrupt_unmask_all();
   }
}

/*
 * This function checks to see if it is called from
 * within an ISR.
 *
 * \returns non-zero when called from within an ISR or kcall.
 */
inline uint32_t rtos_isr_running(void)
{
    uint32_t kernel_mode;

    asm volatile(
        "getsr r11," RTOS_STRINGIFY(XS1_SR_INK_MASK) "\n"
        "mov %0, r11"
        : "=r"(kernel_mode)
        : /* no inputs */
        : /* clobbers */ "r11"
    );

    return kernel_mode;
}

#endif /* RTOS_INTERRUPT_H_ */
