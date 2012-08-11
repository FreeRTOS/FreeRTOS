/*******************************************************************************
 * (c) Copyright 2009 Actel Corporation.  All rights reserved.
 * 
 * SmartFusion microcontroller subsystem (MSS) timer driver API.
 *
 * SVN $Revision: 2661 $
 * SVN $Date: 2010-04-19 17:14:26 +0100 (Mon, 19 Apr 2010) $
 */
/*=========================================================================*//**
  @mainpage SmartFusion MSS Timer Bare Metal Driver.

  @section intro_sec Introduction
  The SmartFusion Microcontroller Subsystem (MSS) includes a timer hardware
  block which can be used as two independent 32-bits timers or as a single
  64-bits timer in periodic or one-shot mode. 

  This driver provides a set of functions for controlling the MSS timer as part
  of a bare metal system where no operating system is available. These drivers
  can be adapted for use as part of an operating system but the implementation
  of the adaptation layer between this driver and the operating system's driver
  model is outside the scope of this driver.
  
  @section theory_op Theory of Operation
  The MSS Timer driver uses the SmartFusion "Cortex Microcontroler Software
  Interface Standard - Peripheral Access Layer" (CMSIS-PAL) to access hadware
  registers. You must ensure that the SmartFusion CMSIS-PAL is either included
  in the software toolchain used to build your project or is included in your
  project. The most up-to-date SmartFusion CMSIS-PAL files can be obtained using
  the Actel Firmware Catalog.
  The SmartFusion MSS Timer can be used in one of two mutually exclusive modes;
  either as a single 64-bits timer or as two independent 32-bits timers. The MSS
  Timer can be used in either periodic mode or one-shot mode. A timer configured
  for periodic mode operations will generate an interrupt and reload its
  down-counter when it reaches 0. The timer will then continue decrementing from
  its reload value without waiting for the interrupt to be cleared. A timer
  configured for one-shot mode will only generate an interrupt once when its
  down-counter reaches 0. It must be explitcitly reloaded to start decrementing
  again.
  
  The MSS Timer driver functions are grouped into the following categories:
    - Initialization and Configuration
    - Timer control
    - Interrupt control
  
  The MSS Timer driver provides three initialization functions:
    - MSS_TIM1_init()
    - MSS_TIM2_init()
    - MSS_TIM64_init()
  The MSS Timer driver is initialized through calls to these functions and at
  least one of them must be called before any other MSS Timer driver functions
  can be called.
  You should only use the MSS_TIM1_init() and MSS_TIM2_init() functions if you
  intend to use the timer in 32-bits mode. Use the MSS_TIM64_init() function is
  you intend to use the MSS Timer as a single 64-bits timer. The initialization
  functions take a single parameter specifying the operating mode of the timer
  being initialized.
  
  Once initialized a timer can be controlled using the following functions:
    - MSS_TIM1_load_immediate()
    - MSS_TIM1_load_background()
    - MSS_TIM1_get_current_value()
    - MSS_TIM1_start()
    - MSS_TIM1_stop()
    - MSS_TIM2_load_immediate()
    - MSS_TIM2_load_background()
    - MSS_TIM2_get_current_value()
    - MSS_TIM2_start()
    - MSS_TIM2_stop()
    - MSS_TIM64_load_immediate()
    - MSS_TIM64_load_background()
    - MSS_TIM64_get_current_value()
    - MSS_TIM64_start()
    - MSS_TIM64_stop()
  
  Timer interrupts are controlled using the following functions:
    - MSS_TIM1_enable_irq()
    - MSS_TIM1_disable_irq()
    - MSS_TIM1_clear_irq()
    - MSS_TIM2_enable_irq()
    - MSS_TIM2_disable_irq()
    - MSS_TIM2_clear_irq()
    - MSS_TIM64_enable_irq()
    - MSS_TIM64_disable_irq()
    - MSS_TIM64_clear_irq()
  
  The function prototypes for the timer interrupt handlers are:
    - void Timer1_IRQHandler( void )
    - void Timer2_IRQHandler( void )
  Entries for these interrupt handlers are provided in the SmartFusion CMSIS-PAL
  vector table. To add a Timer 1 interrupt handler, you must implement a
  Timer1_IRQHandler( ) function as part of your application code. To add a
  Timer 2 interrupt handler, you must implement a Timer2_IRQHandler( ) function
  as part of your application code. When using the MSS Timer as a 64-bit timer,
  you must implement a Timer1_IRQHandler( ) function as part of your
  application code. The Timer 2 interrupt is not used when the MSS Timer is
  configured as a 64-bit timer.
  
 *//*=========================================================================*/
#ifndef MSS_TIMER_H_
#define MSS_TIMER_H_


#include "../../CMSIS/a2fxxxm3.h"

#ifdef __cplusplus
extern "C" {
#endif 

/*-------------------------------------------------------------------------*//**
 * Timer mode selection. This enumeration is used to select between the two
 * possible timer modes of operation: periodic and one-shot mode. It is used as
 * an argument to the MSS_TIM1_init(), MSS_TIM2_init() and MSS_TIM64_init()
 * functions.
 * MSS_TIMER_PERIODIC_MODE:
 *  In periodic mode the timer generates interrupts at constant intervals. On 
 *  reaching zero, the timer's counter is reloaded with a value held in a
 *  register and begins counting down again.
 * MSS_TIMER_ONE_SHOT_MODE:
 *  The timer generates a single interrupt in this mode. On reaching zero, the
 *  timer's counter halts until reprogrammed by the user.
 */
typedef enum __mss_timer_mode_t
{
    MSS_TIMER_PERIODIC_MODE = 0,
    MSS_TIMER_ONE_SHOT_MODE = 1
} mss_timer_mode_t;

/*-------------------------------------------------------------------------*//**
  The MSS_TIM1_init() function initializes the SmartFusion MSS Timer block for
  use as a 32-bit timer and selects the operating mode for Timer 1. This function
  takes the MSS Timer block out of reset in case this hasn’t been done already,
  stops Timer 1, disables its interrupt and sets the Timer 1 operating mode.
  Please note that the SmartFusion MSS Timer block cannot be used both as a
  64-bit and 32-bit timer. Calling MSS_TIM1_init() will overwrite any previous
  configuration of the MSS Timer as a 64-bit timer.

 
  @param mode
    The mode parameter specifies whether the timer will operate in periodic or
    one-shot mode. Allowed values for this parameter are:
        - MSS_TIMER_PERIODIC_MODE
        - MSS_TIMER_ONE_SHOT_MODE
 */
static __INLINE void MSS_TIM1_init( mss_timer_mode_t mode )
{
    NVIC_DisableIRQ( Timer1_IRQn );             /* Disable timer 1 irq in the Cortex-M3 NVIC */  
    
    SYSREG->SOFT_RST_CR &= ~SYSREG_TIMER_SOFTRESET_MASK; /* Take timer block out of reset */
    
    TIMER->TIM64_MODE = 0U;                     /* switch to 32 bits mode */
    
    TIMER_BITBAND->TIM1ENABLE = 0U;             /* disable timer */
    TIMER_BITBAND->TIM1INTEN = 0U;              /* disable interrupt */
    TIMER_BITBAND->TIM1MODE = (uint32_t)mode;   /* set mode (continuous/one-shot) */
    
    TIMER->TIM1_RIS = 1U;                       /* clear timer 1 interrupt */
    NVIC_ClearPendingIRQ( Timer1_IRQn );        /* clear timer 1 interrupt within NVIC */
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM1_start() function enables Timer 1 and starts its down-counter
  decrementing from the load_value specified in previous calls to the
  MSS_TIM1_load_immediate() or MSS_TIM1_load_background() functions.
 */
static __INLINE void MSS_TIM1_start( void )
{
    TIMER_BITBAND->TIM1ENABLE = 1U;    /* enable timer */
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM1_stop() function disables Timer 1 and stops its down-counter
  decrementing.
 */
static __INLINE void MSS_TIM1_stop( void )
{
    TIMER_BITBAND->TIM1ENABLE = 0U;    /* disable timer */
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM1_get_current_value() returns the current value of the Timer 1
  down-counter.
  
  @return
    This function returns the 32-bits current value of the Timer 1 down-counter.
 */
static __INLINE uint32_t MSS_TIM1_get_current_value( void )
{
    return TIMER->TIM1_VAL;
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM1_load_immediate() function loads the value passed by the
  load_value parameter into the Timer 1 down-counter. The counter will decrement
  immediately from this value once Timer 1 is enabled. The MSS Timer will
  generate an interrupt when the counter reaches zero if Timer 1 interrupts are
  enabled. This function is intended to be used when Timer 1 is configured for
  one-shot mode to time a single delay.
 
  @param load_value
    The load_value parameter specifies the value from which the Timer 1 down-counter
    will start decrementing from.
 */
static __INLINE void MSS_TIM1_load_immediate( uint32_t load_value )
{
    TIMER->TIM1_LOADVAL = load_value;
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM1_load_background() function is used to specify the value that will
  be reloaded into the Timer 1 down-counter the next time the counter reaches
  zero. This function is typically used when Timer 1 is configured for periodic
  mode operation to select or change the delay period between the interrupts
  generated by Timer 1.
 
  @param load_value
    The load_value parameter specifies the value that will be loaded into the
    Timer 1 down-counter the next time the down-counter reaches zero. The Timer
    1 down-counter will start decrementing from this value after the current
    count expires.
 */
static __INLINE void MSS_TIM1_load_background( uint32_t load_value )
{
    TIMER->TIM1_BGLOADVAL = load_value;
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM1_enable_irq() function is used to enable interrupt generation for
  Timer 1. This function also enables the interrupt in the Cortex-M3 interrupt
  controller. The Timer1_IRQHandler() function will be called when a Timer 1
  interrupt occurs.
  Note: Note: 	A Timer1_IRQHandler() default implementation is defined, with
  weak linkage, in the SmartFusion CMSIS-PAL. You must provide your own
  implementation of the Timer1_IRQHandler() function, that will override the
  default implementation, to suit your application.

 */
static __INLINE void MSS_TIM1_enable_irq( void )
{
    TIMER_BITBAND->TIM1INTEN = 1U;
    NVIC_EnableIRQ( Timer1_IRQn );
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM1_disable_irq() function is used to disable interrupt generation
  for Timer 1. This function also disables the interrupt in the Cortex-M3
  interrupt controller.
 */
static __INLINE void MSS_TIM1_disable_irq( void )
{
    TIMER_BITBAND->TIM1INTEN = 0U;
    NVIC_DisableIRQ( Timer1_IRQn );
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM1_clear_irq() function is used to clear a pending interrupt from
  Timer 1. This function also clears the interrupt in the Cortex-M3 interrupt
  controller.
  Note: You must call the MSS_TIM1_clear_irq() function as part of your
  implementation of the Timer1_IRQHandler() Timer 1 interrupt service routine
  (ISR) in order to prevent the same interrupt event retriggering a call to the
  ISR.

 */
static __INLINE void MSS_TIM1_clear_irq( void )
{
    TIMER->TIM1_RIS = 1U;
    NVIC_ClearPendingIRQ( Timer1_IRQn );
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM2_init() function initializes the SmartFusion MSS Timer block for
  use as a 32-bit timer and selects the operating mode for Timer 2. This function
  takes the MSS Timer block out of reset in case this hasn’t been done already,
  stops Timer 2, disables its interrupt and sets the Timer 2 operating mode.
  Note: Please note that the SmartFusion MSS Timer block cannot be used both as
  a 64-bit and 32-bit timer. Calling MSS_TIM2_init() will overwrite any previous
  configuration of the MSS Timer as a 64-bit timer.
  
  @param mode
    The mode parameter specifies whether the timer will operate in periodic or
    one-shot mode. Allowed values for this parameter are:
        - MSS_TIMER_PERIODIC_MODE
        - MSS_TIMER_ONE_SHOT_MODE 
 */
static __INLINE void MSS_TIM2_init( mss_timer_mode_t mode )
{
    NVIC_DisableIRQ( Timer2_IRQn );             /* Disable timer 2 irq in the Cortex-M3 NVIC */  
    
    SYSREG->SOFT_RST_CR &= ~SYSREG_TIMER_SOFTRESET_MASK; /* Take timer block out of reset */
    
    TIMER->TIM64_MODE = 0U;                     /* switch to 32 bits mode */
    
    TIMER_BITBAND->TIM2ENABLE = 0U;             /* disable timer */
    TIMER_BITBAND->TIM2INTEN = 0U;              /* disable interrupt */
    TIMER_BITBAND->TIM2MODE = (uint32_t)mode;   /* set mode (continuous/one-shot) */
    
    TIMER->TIM2_RIS = 1U;                       /* clear timer 2 interrupt */
    NVIC_ClearPendingIRQ( Timer2_IRQn );        /* clear timer 2 interrupt within NVIC */
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM2_start() function enables Timer 2 and  starts its down-counter
  decrementing from the load_value specified in previous calls to the
  MSS_TIM2_load_immediate() or MSS_TIM2_load_background() functions.
 */
static __INLINE void MSS_TIM2_start( void )
{
    TIMER_BITBAND->TIM2ENABLE = 1U;    /* enable timer */
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM2_stop() function disables Timer 2 and stops its down-counter
  decrementing.
 */
static __INLINE void MSS_TIM2_stop( void )
{
    TIMER_BITBAND->TIM2ENABLE = 0U;    /* disable timer */
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM2_get_current_value() returns the current value of the Timer 2
  down-counter.
 */
static __INLINE uint32_t MSS_TIM2_get_current_value( void )
{
    return TIMER->TIM2_VAL;
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM2_load_immediate() function loads the value passed by the
  load_value parameter into the Timer 2 down-counter. The counter will decrement
  immediately from this value once Timer 2 is enabled. The MSS Timer will
  generate an interrupt when the counter reaches zero if Timer 2 interrupts are
  enabled. This function is intended to be used when Timer 2 is configured for
  one-shot mode to time a single delay.
  
  @param load_value
    The load_value parameter specifies the value from which the Timer 2
    down-counter will start decrementing. 
 */
static __INLINE void MSS_TIM2_load_immediate( uint32_t load_value )
{
    TIMER->TIM2_LOADVAL = load_value;
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM2_load_background() function is used to specify the value that will
  be reloaded into the Timer 2 down-counter the next time the counter reaches
  zero. This function is typically used when Timer 2 is configured for periodic
  mode operation to select or change the delay period between the interrupts
  generated by Timer 2.
  
  @param load_value
    The load_value parameter specifies the value that will be loaded into the
    Timer 2 down-counter the next time the down-counter reaches zero. The Timer
    2 down-counter will start decrementing from this value after the current
    count expires.
 */
static __INLINE void MSS_TIM2_load_background( uint32_t load_value )
{
    TIMER->TIM2_BGLOADVAL = load_value;
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM2_enable_irq() function is used to enable interrupt generation for
  Timer 2. This function also enables the interrupt in the Cortex-M3 interrupt
  controller. The Timer2_IRQHandler() function will be called when a Timer 2
  interrupt occurs.
  Note: A Timer2_IRQHandler() default implementation is defined, with weak
  linkage, in the SmartFusion CMSIS-PAL. You must provide your own implementation
  of the Timer2_IRQHandler() function, that will override the default
  implementation, to suit your application.
 */
static __INLINE void MSS_TIM2_enable_irq( void )
{
    TIMER_BITBAND->TIM2INTEN = 1U;
    NVIC_EnableIRQ( Timer2_IRQn );
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM2_disable_irq() function is used to disable interrupt generation
  for Timer 2. This function also disables the interrupt in the Cortex-M3
  interrupt controller.
 */
static __INLINE void MSS_TIM2_disable_irq( void )
{
    TIMER_BITBAND->TIM2INTEN = 0U;
    NVIC_DisableIRQ( Timer2_IRQn );
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM2_clear_irq() function is used to clear a pending interrupt from
  Timer 2. This function also clears the interrupt in the Cortex-M3 interrupt
  controller.
  Note: You must call the MSS_TIM2_clear_irq() function as part of your
  implementation of the Timer2_IRQHandler() Timer 2 interrupt service routine
  (ISR) in order to prevent the same interrupt event retriggering a call to the
  ISR.
 */
static __INLINE void MSS_TIM2_clear_irq( void )
{
    TIMER->TIM2_RIS = 1U;
    NVIC_ClearPendingIRQ( Timer2_IRQn );
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM64_init() function initializes the SmartFusion MSS Timer block for
  use as a single 64-bit timer and selects the operating mode of the timer. This
  function takes the MSS Timer block out of reset in case this hasn’t been done
  already, stops the timer, disables its interrupts and sets the timer's
  operating mode.
  Note: Please note that the SmartFusion MSS Timer block cannot be used both as
  a 64-bit and 32-bit timer. Calling MSS_TIM64_init() will overwrite any previous
  configuration of the MSS Timer as a 32-bit timer.

  @param mode
    The mode parameter specifies whether the timer will operate in periodic or
    one-shot mode. Allowed values for this parameter are:
        - MSS_TIMER_PERIODIC_MODE
        - MSS_TIMER_ONE_SHOT_MODE 
 */
static __INLINE void MSS_TIM64_init( mss_timer_mode_t mode )
{
    NVIC_DisableIRQ( Timer1_IRQn );         /* disable timer 1 interrupt within NVIC */
    NVIC_DisableIRQ( Timer2_IRQn );         /* disable timer 2 interrupt within NVIC */
    
    SYSREG->SOFT_RST_CR &= ~SYSREG_TIMER_SOFTRESET_MASK; /* Take timer block out of reset */
    
    TIMER->TIM64_MODE = 1U;                     /* switch to 64 bits mode */
    
    TIMER_BITBAND->TIM64ENABLE = 0U;            /* disable timer */
    TIMER_BITBAND->TIM64INTEN = 0U;             /* disable interrupt */
    TIMER_BITBAND->TIM64MODE = (uint32_t)mode;  /* set mode (continuous/one-shot) */
    
    TIMER->TIM1_RIS = 1U;                   /* clear timer 1 interrupt */
    TIMER->TIM2_RIS = 1U;                   /* clear timer 2 interrupt */
    NVIC_ClearPendingIRQ( Timer1_IRQn );    /* clear timer 1 interrupt within NVIC */
    NVIC_ClearPendingIRQ( Timer2_IRQn );    /* clear timer 2 interrupt within NVIC */
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM64_start() function enables the 64-bit timer and starts its
  down-counter decrementing from the load_value specified in previous calls to
  the MSS_TIM64_load_immediate() or MSS_TIM64_load_background() functions.
 */
static __INLINE void MSS_TIM64_start( void )
{
    TIMER_BITBAND->TIM64ENABLE = 1U;    /* enable timer */
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM64_stop() function disables the 64-bit timer and stops its
  down-counter decrementing.
 */
static __INLINE void MSS_TIM64_stop( void )
{
    TIMER_BITBAND->TIM64ENABLE = 0U;    /* disable timer */
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM64_get_current_value() is used to read the current value of the
  64-bit timer down-counter. 
 
  @param load_value_u
    The load_value_u parameter is a pointer to a 32-bit variable where the upper
    32 bits of the current value of the 64-bit timer down-counter will be copied.
    
  @param load_value_l
    The load_value_l parameter is a pointer to a 32-bit variable where the lower
    32 bits of the current value of the 64-bit timer down-counter will be copied.
    
  Example:
  @code
    uint32_t current_value_u = 0;
    uint32_t current_value_l = 0;
    MSS_TIM64_get_current_value( &current_value_u, &current_value_l );
  @endcode
 */
static __INLINE void MSS_TIM64_get_current_value
(
    uint32_t * load_value_u,
    uint32_t * load_value_l
)
{
    *load_value_l = TIMER->TIM64_VAL_L;
    *load_value_u = TIMER->TIM64_VAL_U;
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM64_load_immediate() function loads the values passed by the
  load_value_u and load_value_l parameters into the 64-bit timer down-counter.
  The counter will decrement immediately from the concatenated 64-bit value once
  the 64-bit timer is enabled. The MSS Timer will generate an interrupt when the
  counter reaches zero if 64-bit timer interrupts are enabled. This function is
  intended to be used when the 64-bit timer is configured for one-shot mode to
  time a single delay.
 
  @param load_value_u
    The load_value_u parameter specifies the upper 32 bits of the 64-bit timer
    load value from which the 64-bit timer down-counter will start decrementing.
    
  @param load_value_l
    The load_value_l parameter specifies the lower 32 bits of the 64-bit timer
    load value from which the 64-bit timer down-counter will start decrementing.
 */
static __INLINE void MSS_TIM64_load_immediate
(
    uint32_t load_value_u,
    uint32_t load_value_l
)
{
    TIMER->TIM64_LOADVAL_U = load_value_u;
    TIMER->TIM64_LOADVAL_L = load_value_l;
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM64_load_background() function is used to specify the 64-bit value
  that will be reloaded into the 64-bit timer down-counter the next time the
  counter reaches zero. This function is typically used when the 64-bit timer is
  configured for periodic mode operation to select or change the delay period
  between the interrupts generated by the 64-bit timer.
 
  @param load_value_u
    The load_value_u parameter specifies the upper 32 bits of the 64-bit timer
    load value. The concatenated 64-bit value formed from load_value_u and
    load_value_l will be loaded into the 64-bit timer down-counter the next
    time the down-counter reaches zero. The 64-bit timer down-counter will start
    decrementing from the concatenated 64-bit value after the current count
    expires.
    
  @param load_value_l
    The load_value_l parameter specifies the lower 32 bits of the 64-bit timer
    load value. The concatenated 64-bit value formed from load_value_u and
    load_value_l will be loaded into the 64-bit timer down-counter the next time
    the down-counter reaches zero. The 64-bit timer down-counter will start
    decrementing from the concatenated 64-bit value after the current count
    expires.
 
 */
static __INLINE void MSS_TIM64_load_background
(
    uint32_t load_value_u,
    uint32_t load_value_l
)
{
    TIMER->TIM64_BGLOADVAL_U = load_value_u;
    TIMER->TIM64_BGLOADVAL_L = load_value_l;
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM64_enable_irq() function is used to enable interrupt generation for
  the 64-bit timer. This function also enables the interrupt in the Cortex-M3
  interrupt controller. The Timer1_IRQHandler() function will be called when a
  64-bit timer interrupt occurs.
  Note: A Timer1_IRQHandler() default implementation is defined, with weak
  linkage, in the SmartFusion CMSIS-PAL. You must provide your own
  implementation of the Timer1_IRQHandler() function, that will override the
  default implementation, to suit your application.
  Note: The MSS_TIM64_enable_irq() function enables and uses Timer 1 interrupts
  for the 64-bit timer. Timer 2 interrupts remain disabled.
 */
static __INLINE void MSS_TIM64_enable_irq( void )
{
    TIMER_BITBAND->TIM64INTEN = 1U;
    NVIC_EnableIRQ( Timer1_IRQn );
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM64_disable_irq() function is used to disable interrupt generation
  for the 64-bit timer. This function also disables the interrupt in the
  Cortex-M3 interrupt controller.
 */
static __INLINE void MSS_TIM64_disable_irq( void )
{
    TIMER_BITBAND->TIM64INTEN = 0U;
    NVIC_DisableIRQ( Timer1_IRQn );
}

/*-------------------------------------------------------------------------*//**
  The MSS_TIM64_clear_irq() function is used to clear a pending interrupt from
  the 64-bit timer. This function also clears the interrupt in the Cortex-M3
  interrupt controller.
  Note: You must call the MSS_TIM64_clear_irq() function as part of your
  implementation of the Timer1_IRQHandler() 64-bit timer interrupt service
  routine (ISR) in order to prevent the same interrupt event retriggering a
  call to the ISR.
 */
static __INLINE void MSS_TIM64_clear_irq( void )
{
    TIMER->TIM64_RIS = 1U;
    NVIC_ClearPendingIRQ( Timer1_IRQn );
}

#ifdef __cplusplus
}
#endif

#endif /*MSS_TIMER_H_*/
