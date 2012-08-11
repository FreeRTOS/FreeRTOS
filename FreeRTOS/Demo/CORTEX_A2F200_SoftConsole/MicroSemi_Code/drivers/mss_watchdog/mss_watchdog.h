/*******************************************************************************
 * (c) Copyright 2009 Actel Corporation.  All rights reserved.
 * 
 * SmartFusion Microcontroller Subsystem (MSS) Watchdog bare metal software
 * driver.
 *
 * SVN $Revision: 1888 $
 * SVN $Date: 2009-12-18 10:58:42 +0000 (Fri, 18 Dec 2009) $
 */
/*=========================================================================*//**
  @section intro_sec Introduction
  The SmartFusion microcontroller subsystem (MSS) includes a watchdog timer used
  to detect system lockups.
  This driver provides a set of functions for controlling the MSS watchdog as
  part of a bare metal system where no operating system is available. These
  drivers can be adapted for use as part of an operating system but the
  implementation of the adaptation layer between this driver and the operating
  system's driver model is outside the scope of this driver.
    
  @section hw_dependencies Hardware Flow Dependencies
  The configuration of all features of the MSS watchdog is covered by this
  driver. There are no dependencies on the hardware flow for configuring the
  SmartFusion MSS watchdog timer.
    
  @section theory_op Theory of Operation
  The watchdog driver uses the SmartFusion "Cortex Microcontroler Software
  Interface Standard - Peripheral Access Layer" (CMSIS-PAL) to access hadware
  registers. You must ensure that the SmartFusion CMSIS-PAL is either included
  in the software toolchain used to build your project or is included in your
  project. The most up-to-date SmartFusion CMSIS-PAL files can be obtained using
  the Actel Firmware Catalog.
  
  The watchdog driver functions are grouped into the following categories:
    - Initialization and cnfiguration
    - Reading the watchdog timer current value and status
    - Refreshing the watchdog timer value
    - Time-out and wake-up interrupts control
  
  The watchdog driver is initialized and configured through a call to the
  MSS_WD_init() function. The parameters passed to MSS_WD_init() function
  specify the watchdog timer configuration. The configuration parameters include
  the value that will be reloaded into the watchdog timer down counter every
  time the watchdog is refreshed. Also included as part of the configuration
  parameters is the optional allowed refresh window. The allowed refresh window
  specifies the maximum allowed current value of the watchdog timer at the time
  of the watchdog is relaoded. Attempting to reload the watchdog timer when its
  value is larger than the allowed refresh window will cause a reset or
  interrupt depending on the watchdog configuration. The allowed refresh window
  can be disabled by specifying an allowed refesh window equal or higher than
  the watchdog reload value.
  The MSS_WD_init() function must be called before any other watchdog driver
  functions can be called with the exception of the MSS_WD_disable() function.
  
  The watchdog timer can be disabled using the MSS_WD_disable() function. Once
  disabled, the watchdog timer can only be reenabled by a power-on reset.
  
  The watchdog timer current value can be read using the MSS_WD_current_value()
  function. The watchdog status can be read using the MSS_WD_status() function.
  These functions are typically required when using the watchdog configured with
  an allowed refresh window to check if a watchdog reload is currently allowed.
  
  The watchdog timer value is reloaded using the MSS_WD_reload() function. The
  value reloaded into the watchdog timer down counter is the value specified as
  parameter to the MSS_WD_init() function.
  
  The watchdog timer can generate interrupts instead of resetting the system
  when its down-counter timer expires. These time-out interrupts are controlled
  using the following functions:
    - MSS_WD_enable_timeout_irq
    - MSS_WD_disable_timeout_irq
    - MSS_WD_clear_timeout_irq
  
  The watchdog timer is external to the Cortex-M3 processor core and operates
  even when the Cortex-M3 is in sleep mode. A wakeup interrupt can be generated
  by the watchdog timer to wakeup the Cortext-M3 when the watchdog timer value
  reaches the allowed refresh window while the Cortex-M3 is in sleep mode. The
  watchdog driver provides the following functions to control wakeup interrupts:
    - MSS_WD_enable_wakeup_irq
    - MSS_WD_disable_wakeup_irq
    - MSS_WD_clear_wakeup_irq
    
 *//*=========================================================================*/

#ifndef MSS_WATCHDOG_H_
#define MSS_WATCHDOG_H_

#ifdef __cplusplus
extern "C" {
#endif 

#include "../../CMSIS/a2fxxxm3.h"

/***************************************************************************//**
 * The MSS_WDOG_RESET_ON_TIMEOUT_MODE macro is one of the possible values for the
 * mode parameter of the WD_init() function. It is used to specify that a reset
 * should occur when the watchdog down counter times out.
 */
#define MSS_WDOG_RESET_ON_TIMEOUT_MODE       (uint32_t)0x00000000U

/***************************************************************************//**
 * The MSS_WDOG_INTERRUPT_ON_TIMEOUT_MODE macro is one of the possible values for
 * the  mode parameter of function the WD_init() function. It is used to specify
 * that a time out interrupt should occur when the watchdog down counter expires.
 */
#define MSS_WDOG_INTERRUPT_ON_TIMEOUT_MODE   (uint32_t)0x00000004U

/***************************************************************************//**
 * The MSS_WDOG_NO_WINDOW macro can be used as the value for the reload_window
 * parameter of the WD_init() function. It is used to specify that no forbidden
 * window will exist for the reload of the watchdog down counter.
 */
#define MSS_WDOG_NO_WINDOW    (uint32_t)0xFFFFFFFFU

/***************************************************************************//**
 * The MSS_WDOG_CTRL_MODE_BIT_MASK macro is a bit mask specifying the bit used to
 * set the watchdog's operating mode within the wathcdog's WDOGCONTROL register.
 */
#define MSS_WDOG_CTRL_MODE_BIT_MASK           (uint32_t)0x00000004U

/***************************************************************************//**
 * The MSS_WDOG_TIMEOUT_IRQ_ENABLE_BIT_MASK macro is a bit mask specifying the bit
 * used to enable the time out interrupt within the watchdog's WDOGCONTROL
 * register.
 */
#define MSS_WDOG_TIMEOUT_IRQ_ENABLE_BIT_MASK  (uint32_t)0x00000001U

/***************************************************************************//**
  The MSS_WDOG_WAKEUP_IRQ_ENABLE_BIT_MASK macro is a bit mask specifying the bit
  used to enable the wake up interrupt within the watchdog's WDOGCONTROL
  register.
 */
#define MSS_WDOG_WAKEUP_IRQ_ENABLE_BIT_MASK   (uint32_t)0x00000002U

/***************************************************************************//**
  The MSS_WDOG_TIMEOUT_IRQ_CLEAR_BIT_MASK macro is a bit mask specifying the bit
  used to clear the time out interrupt within the watchdog's WDOGRIS register.
 */
#define MSS_WDOG_TIMEOUT_IRQ_CLEAR_BIT_MASK   (uint32_t)0x00000001U

/***************************************************************************//**
  The MSS_WDOG_WAKEUP_IRQ_CLEAR_BIT_MASK macro is a bit mask specifying the bit
  used to clear the wake up interrupt within the watchdog's WDOGRIS register.
 */
#define MSS_WDOG_WAKEUP_IRQ_CLEAR_BIT_MASK    (uint32_t)0x00000002U

/***************************************************************************//**
  The MSS_WDOG_REFRESH_KEY macro holds the magic value which will cause a reload
  of the watchdog's down counter when written to the watchdog's WDOGREFRESH
  register.
 */
#define MSS_WDOG_REFRESH_KEY    (uint32_t)0xAC15DE42U

/***************************************************************************//**
  The MSS_WDOG_DISABLE_KEY macro holds the magic value which will disable the
  watchdog if written to the watchdog's WDOGENABLE register.
 */
#define MSS_WDOG_DISABLE_KEY    (uint32_t)0x4C6E55FAU

/***************************************************************************//**
  The MSS_WD_init() function initializes and configures the watchdog timer.
 
  @param load_value
    The load_value parameter specifies the value that will be loaded into the
    watchdog's down counter when the reload command is issued through a call to
    MSS_WD_reload().
                   
  @param reload_window
    The reload_window parameter specifies the time window during which a reload
    of the watchdog counter is allowed. A reload of the watchdog counter should
    only be performed when the watchdog counter value is below the value of the
    reload_window. Reloading the watchdog down counter value before it has
    reached the reload_window will result in an interrupt or reset depending on
    the watchdog's mode.
    The reload window can be disabled by using WDOG_NO_WINDOW for this parameter.
 
  @param mode
    The mode parameter specifies the watchdog's operating mode. It can be either
    MSS_WDOG_RESET_ON_TIMEOUT_MODE or MSS_WDOG_INTERRUPT_ON_TIMEOUT_MODE.
    MSS_WDOG_RESET_ON_TIMEOUT_MODE: a reset will occur if the watchdog timer
    expires.
    MSS_WDOG_INTERRUPT_ON_TIMEOUT_MODE: an NMI interrupt will occur if the
    watchdog timer expires.
 
  @return
    This function does not return a value.
 */
static __INLINE void MSS_WD_init
(
    uint32_t load_value,
    uint32_t reload_window,
    uint32_t mode
)
{
    /* Disable interrupts. */
    WATCHDOG->WDOGCONTROL &= ~(MSS_WDOG_TIMEOUT_IRQ_ENABLE_BIT_MASK | MSS_WDOG_WAKEUP_IRQ_CLEAR_BIT_MASK);
    
    /* Clear any existing interrupts. */
    WATCHDOG->WDOGRIS = MSS_WDOG_TIMEOUT_IRQ_CLEAR_BIT_MASK | MSS_WDOG_WAKEUP_IRQ_CLEAR_BIT_MASK;
    
    /* Configure watchdog with new configuration passed as parameter. */
    WATCHDOG->WDOGMVRP = MSS_WDOG_NO_WINDOW;
    WATCHDOG->WDOGLOAD = load_value;
    WATCHDOG->WDOGCONTROL = (WATCHDOG->WDOGCONTROL & ~MSS_WDOG_CTRL_MODE_BIT_MASK) | (mode & MSS_WDOG_CTRL_MODE_BIT_MASK);
    
    /* Reload watchdog with new load value. */
    WATCHDOG->WDOGREFRESH = MSS_WDOG_REFRESH_KEY;
    
    /* Set allowed window. */
    WATCHDOG->WDOGMVRP = reload_window;
}

/***************************************************************************//**
  The MSS_WD_reload() function causes the watchdog to reload its down counter timer
  with the load value configured through the call to WD_init(). This function 
  must be called regularly to avoid a system reset.
 
  @return
    This function does not return a value.
 */
static __INLINE void MSS_WD_reload( void )
{
    WATCHDOG->WDOGREFRESH = MSS_WDOG_REFRESH_KEY;
}

/***************************************************************************//**
  The MSS_WD_disable() function disables the watchdog.
  Please note that the watchdog can only be reenabled as a result of a power-on
  reset.
 
  @return
    This function does not return a value.
 */
static __INLINE void MSS_WD_disable( void )
{
    WATCHDOG->WDOGENABLE = MSS_WDOG_DISABLE_KEY;
}

/***************************************************************************//**
  The MSS_WD_current_value() function returns the current value of the watchdog's
  down counter.
 
  @return
    This function returns the current value of the watchdog down counter.
 */
static __INLINE uint32_t MSS_WD_current_value( void )
{
    return WATCHDOG->WDOGVALUE;
}

/***************************************************************************//**
  The MSS_WD_status() function returns the status of the watchdog.
 
  @return 
    The MSS_WD_status() function returns the status of the watchdog. A value of
    0 indicates that watchdog counter has reached the forbidden window and that
    a reload should not be done. A value of 1 indicates that the watchdog counter
    is within the permitted window and that a reload is allowed.
 */
static __INLINE uint32_t MSS_WD_status( void )
{
    return WATCHDOG->WDOGSTATUS;
}

/***************************************************************************//**
  The MSS_WD_enable_timeout_irq() function enables the watchdog’s time out
  interrupt which is connected to the Cortex-M3 NMI interrupt.
  The NMI_Handler() function will be called when a watchdog time out occurs. You
  must provide the implementation of the NMI_Handler() function to suit your
  application.
 
  @return
    This function does not return a value.
 
  Example:
  @code
  #include "mss_watchdog.h"
  int main( void )
  {
      MSS_WD_init( 0x10000000, MSS_WDOG_NO_WINDOW, MSS_WDOG_INTERRUPT_ON_TIMEOUT_MODE );
      MSS_WD_enable_timeout_irq();
      for (;;)
      {
          main_task();
      }
  }
 
  void NMI_Handler( void )
  {
      process_timeout();
      MSS_WD_clear_timeout_irq();
  }
  @endcode
 */
static __INLINE void MSS_WD_enable_timeout_irq( void )
{
    WATCHDOG->WDOGCONTROL |= MSS_WDOG_TIMEOUT_IRQ_ENABLE_BIT_MASK;
}

/***************************************************************************//**
  The WD_disable_timeout_irq() function disables the generation of the NMI
  interrupt when the watchdog times out.
 
  @return
    This function does not return a value.
 */
static __INLINE void MSS_WD_disable_timeout_irq( void )
{
    WATCHDOG->WDOGCONTROL &= ~MSS_WDOG_TIMEOUT_IRQ_ENABLE_BIT_MASK;
}

/***************************************************************************//**
  The MSS_WD_enable_wakeup_irq() function enables the SmartFusion wakeup
  interrupt. The WdogWakeup_IRQHandler() function will be called when a wake up
  interrupt occurs. You must provide the implementation of the WdogWakeup_IRQHandler()
  function to suit your application.
 
  @return
    This function does not return a value.
 
  Example:
  @code
  #include "mss_watchdog.h"
  int main( void )
  {
      MSS_WD_init( 0x10000000, MSS_WDOG_NO_WINDOW, MSS_WDOG_INTERRUPT_ON_TIMEOUT_MODE );
      MSS_WD_enable_wakeup_irq();
      for (;;)
      {
          main_task();
          cortex_sleep();
      }
  }
 
  void WdogWakeup_IRQHandler( void )
  {
      process_wakeup();
      MSS_WD_clear_wakeup_irq();
  }
  @endcode
 */
static __INLINE void MSS_WD_enable_wakeup_irq( void )
{
    WATCHDOG->WDOGCONTROL |= MSS_WDOG_WAKEUP_IRQ_ENABLE_BIT_MASK;
    NVIC_EnableIRQ( WdogWakeup_IRQn );
}

/***************************************************************************//**
  The MSS_WD_disable_wakeup_irq() function disables the SmartFusion wakeup
  interrupt. 
 
  @return
    This function does not return a value.
 */
static __INLINE void MSS_WD_disable_wakeup_irq( void )
{
    WATCHDOG->WDOGCONTROL &= ~MSS_WDOG_WAKEUP_IRQ_ENABLE_BIT_MASK;
}

/***************************************************************************//**
  The MSS_WD_clear_timeout_irq() function clears the watchdog’s time out
  interrupt which is connected to the Cortex-M3 NMI interrupt.
  Calling MSS_WD_clear_timeout_irq() results in clearing the Cortex-M3 NMI interrupt.
  Note: The MSS_WD_clear_timeout_irq() function must be called as part of the
  timeout interrupt service routine (ISR) in order to prevent the same interrupt
  event retriggering a call to the wakeup ISR.
 
  @return
    The example below demonstrates the use of the MSS_WD_clear_timeout_irq()
    function as part of the NMI interrupt service routine.

    Example:
  @code
  void NMI_Handler( void )
  {
      process_timeout();
      MSS_WD_clear_timeout_irq();
  }
  @endcode
 */
static __INLINE void MSS_WD_clear_timeout_irq( void )
{
    WATCHDOG->WDOGRIS = MSS_WDOG_TIMEOUT_IRQ_CLEAR_BIT_MASK;
    /*
     * Perform a second write to ensure that the first write completed before 
     * returning from this function. This is to account for posted writes across
     * the AHB matrix. The second write ensures that the first write has
     * completed and that the interrupt line has been de-asserted by the time
     * the function returns. Omitting the second write may result in a delay
     * in the de-assertion of the interrupt line going to the Cortex-M3 and a
     * retriggering of the interrupt.
     */
    WATCHDOG->WDOGRIS = MSS_WDOG_TIMEOUT_IRQ_CLEAR_BIT_MASK;
}

/***************************************************************************//**
  The MSS_WD_clear_wakeup_irq() function clears the wakeup interrupt.
  Note: The MSS_WD_clear_wakeup_irq() function must be called as part of the
  wakeup interrupt service routine (ISR) in order to prevent the same interrupt
  event retriggering a call to the wakeup ISR. This function also clears the
  interrupt in the Cortex-M3 interrupt controller through a call to
  NVIC_ClearPendingIRQ().
 
  @return
    This function does not return a value.

    Example:
    The example below demonstrates the use of the MSS_WD_clear_wakeup_irq() function
    as part of the wakeup interrupt service routine.  
    @code
    void WdogWakeup_IRQHandler( void )
    {
        do_interrupt_processing();
        
        MSS_WD_clear_wakeup_irq();
    }
    @endcode
*/
static __INLINE void MSS_WD_clear_wakeup_irq( void )
{
    WATCHDOG->WDOGRIS = MSS_WDOG_WAKEUP_IRQ_CLEAR_BIT_MASK;
    NVIC_ClearPendingIRQ( WdogWakeup_IRQn );
}
#ifdef __cplusplus
}
#endif

#endif /* MSS_WATCHDOG_H_ */
