/*******************************************************************************
 * (c) Copyright 2008-2013 Microsemi SoC Products Group.  All rights reserved.
 * 
 *  SmartFusion2 MSS RTC bare metal software driver public API.
 *
 * SVN $Revision: 5396 $
 * SVN $Date: 2013-03-27 21:57:50 +0000 (Wed, 27 Mar 2013) $
 */

/*=========================================================================*//**
  @mainpage SmartFusion2 MSS RTC Bare Metal Driver.

  @section intro_sec Introduction
  The SmartFusion2 microcontroller subsystem (MSS) includes a real time counter
  (RTC) that can generate alarms and wakeup interrupts in real time. This
  software driver provides a set of functions for controlling the MSS RTC as
  part of a bare metal system where no operating system is available. The driver
  can be adapted for use as part of an operating system, but the implementation
  of the adaptation layer between the driver and the operating system's driver
  model is outside the scope of the driver.
  
  The MSS RTC driver provides support for the following features:
    - Initialization of the RTC
    - Configuration of the RTC timebase
    - Configuration as a calendar or binary mode counter
    - Set the current calendar or binary mode count
    - Get the current calendar or binary mode count
    - Start and stop the RTC counting
    - Set alarm conditions
    - Enable, disable and clear the wakeup interrupt
    
  @section hw_dependencies Hardware Flow Dependencies
  The configuration of all features of the MSS RTC is covered by this driver
  with the exception of the clock source driving the MSS RTC clock (RTCCLK)
  input. The SmartFusion2 MSS clock controller can supply one of three clock
  sources to the MSS RTC clock input:
    - Crystal Oscillator 32.768 kHz
    - 1MHz Oscillator
    - 50MHz Oscillator.  (25 MHz in a 1.0v part).
  The SmartFusion2 MSS configurator tool in the hardware flow configures one
  of these clocks as the RTCCLK input source.
  The base address and register addresses and interrupt number assignment for
  the MSS RTC block are defined as constants in the SmartFusion2 CMSIS HAL. You
  must ensure that the SmartFusion2 CMSIS HAL is either included in the software
  tool chain used to build your project or is included in your project.
  
  @section theory_op Theory of Operation
  The MSS RTC driver functions are grouped into the following categories:
    - Initialization of the RTC driver and hardware
    - Setting and reading the RTC counter current value
    - Setting RTC alarm values
    - Starting and stopping the RTC
    - Interrupt Control
    
  Initialization
  The MSS RTC driver is initialized through a call to the MSS_RTC_init()
  function. The MSS_RTC_init() function must be called before any other MSS RTC
  driver functions are called.
  The MSS_RTC_init() function:
    - Stops the RTC counters and disables the RTC alarm
    - Disables the RTC wakeup interrupt in the RTC and in the Cortex-M3
      interrupt controller (NVIC).
    - Clears any pending RTC wakeup interrupt in the RTC and in the Cortex-M3
      interrupt controller (NVIC).
    - Enables the RTC_WAKEUP_CR[0] mask bit in the MSS System Register to
      connect the RTC wakeup interrupt to the Cortex-M3 interrupt controller.
    - Resets the RTC counters and the alarm and compare registers
    - Sets the RTC's operating mode to binary counter mode or calendar counter
      mode, as specified by the mode parameter
    - Sets the RTC's prescaler register to the value specified by the prescaler
      parameter. The frequency of the clock source driving the MSS RTC clock
      (RTCCLK) input is required to calculate the prescaler value.
    
  Setting and Reading the RTC Counter Value
  The MSS RTC supports two mode of operation – binary mode and calendar mode.
  The following functions are used to set and read the current value of the
  counter when the MSS RTC is configured to operate in binary mode:
    - MSS_RTC_set_binary_count() – This function is used to set the current
      value of the RTC binary counter.
    - MSS_RTC_get_binary_count() – This function is used to read the current
      value of the RTC binary counter.
  The following functions are used to set and read the current value of the
  counter the MSS RTC is configured to operate in calendar mode:
    - MSS_RTC_set_calendar_count() – This function is used to set the current
      value of the RTC calendar counter.
    - MSS_RTC_get_calendar_count() – This function is used to read the current
      value of the RTC calendar counter.
 
  The following functions resets the RTC counter in either binary and calendar
  operating mode:
    - MSS_RTC_reset_counter() – This function resets the RTC counter.
    
  Setting RTC Alarms
  The MSS RTC can generate alarms when the counter matches a specified count
  value in binary mode or a date and time in calendar mode.
  The following functions are used to set up alarms:
    - MSS_RTC_set_binary_count_alarm() – This function sets up one-shot or
      periodic alarms when the MSS RTC is configured to operate in binary mode.
    - MSS_RTC_set_calendar_count_alarm() – This function sets up one-shot or
      periodic alarms when the MSS RTC is configured to operate in calendar
      mode.
  Note: The alarm asserts a wakeup interrupt to the Cortex-M3. This function
        enables the RTC’s wakeup interrupt output, however the RTC wakeup
        interrupt input to the Cortex-M3 NVIC must be enabled separately by
        calling the MSS_RTC_enable_irq() function. The alarm can be disabled at
        any time by calling the MSS_RTC_disable_irq() function. activate
  
  Starting and Stopping the RTC Counter
  The following functions start and stop the RTC counter:
    - MSS_RTC_start() – This function starts the RTC counter.
    - MSS_RTC_stop() – This function stops the RTC counter.
    
  Interrupt Control
  The MSS_RTC_init() function enables the RTC_WAKEUP_CR[0] mask bit in the MSS
  System Register to connect the RTC wakeup interrupt to the Cortex-M3 interrupt
  controller.
  An RTC_Wakeup_IRQHandler() default implementation is defined, with weak
  linkage, in the SmartFusion2 CMSIS HAL. You must provide your own
  implementation of the RTC_Wakeup_IRQHandler() function, which will override
  the default implementation, to suit your application.
  The function prototype for the RTC wakeup interrupt handler is as follows:
    void RTC_Wakeup_IRQHandler ( void )
  The RTC wakeup interrupt is controlled using the following functions:
    - MSS_RTC_enable_irq() – The MSS_RTC_enable_irq() function enables the RTC
      to interrupt the Cortex-M3 when a wakeup alarm occurs.
    - MSS_RTC_disable_irq() – The MSS_RTC_disable_irq() function disables the
      RTC from interrupting the Cortex-M3 when a wakeup alarm occurs.
    - MSS_RTC_clear_irq() – The MSS_RTC_clear_irq() function clears a pending
      RTC wakeup interrupt at the RTC wakeup output. You must call the
      MSS_RTC_clear_irq() function as part of your implementation of the
      RTC_Wakeup_IRQHandler() interrupt service routine (ISR) in order to
      prevent the same interrupt event retriggering a call to the ISR.

 *//*=========================================================================*/
#ifndef MSS_RTC_H_
#define MSS_RTC_H_

#ifdef __cplusplus
extern "C" {
#endif 

#include "../../CMSIS/m2sxxx.h"

/*-------------------------------------------------------------------------*//**
  The MSS_RTC_BINARY_MODE constant is used to specify the mode parameter to the
  MSS_RTC_init() function. The RTC will run in binary mode if this constant is
  used. In binary mode, the calendar counter counts consecutively from 0 all the
  way to 2^43.
 */
#define MSS_RTC_BINARY_MODE               0u

/*-------------------------------------------------------------------------*//**
  The MSS_RTC_CALENDAR_MODE constant is used to specify the mode parameter to
  the MSS_RTC_init() function. The RTC will run in calendar mode if this
  constant is used. In calendar mode, the calendar counter counts seconds,
  minutes, hours, days, months, years, weekdays and weeks.
 */
#define MSS_RTC_CALENDAR_MODE             1u

/*-------------------------------------------------------------------------*//**
  The alarm_value parameter of the MSS_RTC_set_calendar_count_alarm() function
  is a pointer to an mss_rtc_calendar_t data structure specifying the date and
  time at which the alarm is to occur. You must assign the required date and
  time values to the mss_rtc_calendar_t structure before calling the function.
  Any of the fields of the mss_rtc_calendar_t structure can be set to
  MSS_RTC_CALENDAR_DONT_CARE, to indicate that they are not to be considered in
  deciding when the alarm will occur; this is necessary when setting periodic
  alarms. 
 */
#define MSS_RTC_CALENDAR_DONT_CARE      0xFFu

/*-------------------------------------------------------------------------*//**
  Days of the week.
 */
#define MSS_RTC_SUNDAY      1u
#define MSS_RTC_MONDAY      2u
#define MSS_RTC_TUESDAY     3u
#define MSS_RTC_WEDNESDAY   4u
#define MSS_RTC_THRUSDAY    5u
#define MSS_RTC_FRIDAY      6u
#define MSS_RTC_SATURDAY    7u

/*-------------------------------------------------------------------------*//**
  The mss_rtc_alarm_type_t enumeration is used as the alarm_type parameter for
  the MSS_RTC_set_calendar_count_alarm() and MSS_RTC_set_binary_count_alarm()
  functions to specify whether the requested alarm should occur only one time or
  periodically.
 */
typedef enum {
    MSS_RTC_SINGLE_SHOT_ALARM,
    MSS_RTC_PERIODIC_ALARM
} mss_rtc_alarm_type_t;

/*-------------------------------------------------------------------------*//**
  A pointer to an instance of the mss_rtc_calender_t data structure is used to
  write new date and time values to the RTC using the
  MSS_RTC_set_rtc_calendar_count() and MSS_RTC_set_calendar_count_alarm()
  functions. The MSS_RTC_get_calendar_count() function also uses a pointer to an
  instance of the mss_rtc_calender_t data structure to read the current date and
  time value from the RTC.
 */
typedef struct mss_rtc_calendar
{
     uint8_t second;
     uint8_t minute;
     uint8_t hour;
     uint8_t day;
     uint8_t month;
     uint8_t year;
     uint8_t weekday;
     uint8_t week;
} mss_rtc_calendar_t ;

/*-------------------------------------------------------------------------*//**
  The MSS_RTC_init() function initializes the RTC driver and hardware to a known
  state. 
  To initialize the RTC hardware, this function:
    - Stops the RTC counters and disables the RTC alarm
    - Disables the RTC wakeup interrupt in the RTC and in the Cortex-M3
      interrupt controller (NVIC).
    - Clears any pending RTC wakeup interrupt in the RTC and in the Cortex-M3
      interrupt controller (NVIC).
    - Resets the RTC counters and the alarm and compare registers
    - Sets the RTC's operating mode to binary counter mode or calendar counter
      mode, as specified by the mode parameter
    - Sets the RTC's prescaler register to the value specified by the prescaler
      parameter
  The MSS clock controller can supply one of three clock sources to the RTC
  clock input (RTCCLK):
    - Crystal Oscillator 32.768 kHz
    - 1MHz Oscillator
    - 50MHz Oscillator.  (25 MHz in a 1.0v part).
  For calendar mode, program the prescaler register to generate a 1Hz signal
  from the active RTCCLK according to the following equation:
    prescaler = RTCCLK – 1 (where RTCCLK unit is Hz)
  For a 32.768 kHz clock, set the prescaler to 32768 - 1 = 32767. The prescaler
  register is 26 bits wide, allowing clock sources of up to 67 MHz to generate
  the 1Hz time base.
  For binary mode, the prescaler register can be programmed to generate a 1Hz
  time base or a different time base, as required.
  
  @param mode
    The mode parameter is used to specify the operating mode of the RTC. The
    allowed values for mode are:
      - MSS_RTC_BINARY_MODE
      - MSS_RTC_CALENDAR_MODE
    
  @param prescaler
    The prescaler parameter specifies the value to divide the incoming RTC clock
    by, to generate the RTC time base signal. For calendar mode, set the
    prescaler value to generate a 1Hz time base from the incoming RTC clock
    according to the following equation:
        prescaler = RTCCLK – 1    (where the RTCCLK unit is Hz)
    For binary mode, set the prescaler value to generate a 1Hz time base or a
    different time base, as required.
    The prescaler parameter can be any integer value in the range 2 to 2^26.
    
  @return
    This function does not return a value.
    
  The example code below shows how the RTC can be initialized only after a power-on
  reset.
  @code
    #define PO_RESET_DETECT_MASK    0x00000001u
    
    void init_application(void)
    {
        uint32_t power_on_reset;
        power_on_reset = SYSREG->RESET_SOURCE_CR & PO_RESET_DETECT_MASK;
        if(power_on_reset)
        {
            MSS_RTC_init(MSS_RTC_CALENDAR_MODE, 32767);
            SYSREG->RESET_SOURCE_CR = PO_RESET_DETECT_MASK;
        }
    }
  @endcode
 */
void
MSS_RTC_init
(
    uint8_t mode,
    uint32_t prescaler
);

/*-------------------------------------------------------------------------*//**
  The MSS_RTC_set_rtc_calendar_count() function sets the current value of the
  RTC calendar counter.
  Note: This function must only be used when the RTC is configured to operate in
        calendar counter mode.
        
  @param new_rtc_value
    The new_rtc_value parameter is a pointer to an mss_rtc_calendar_t data
    structure specifying the new date and time value from which the RTC will
    increment. You must populate the mss_rtc_calendar_t structure with the
    required date and time values before calling this function.
    
  @return
    This function does not return a value.
 */

void
MSS_RTC_set_calendar_count
(
    const mss_rtc_calendar_t *new_rtc_value
);

/*-------------------------------------------------------------------------*//**
  The MSS_RTC_set_binary_count() function sets the current value of the RTC
  binary counter.
  Note: This function must only be used when the RTC is configured to operate in
        binary counter mode.
        
  @param new_rtc_value
    The new_rtc_value parameter specifies the new count value from which the RTC
    will increment. The binary counter is 43 bits wide, so the maximum allowed
    binary value is 2^43.

  @return
    This function does not return a value.
 */

void
MSS_RTC_set_binary_count
(
    uint64_t new_rtc_value
);

/*-------------------------------------------------------------------------*//**
  The MSS_RTC_get_calendar_count() function returns the current value of the RTC
  calendar counter via the data structure pointed to by the p_rtc_calendar
  parameter.
  Note: This function must only be used when the RTC is configured to operate in
        calendar counter mode.
        
  @param p_rtc_calendar
    The p_rtc_calendar parameter is a pointer to an mss_rtc_calendar_t data
    structure where the current value of the calendar counter will be written by
    the MSS_RTC_get_calendar_count() function
    
  @return
    This function does not return a value.
 */
void
MSS_RTC_get_calendar_count
(
    mss_rtc_calendar_t *p_rtc_calendar
);

/*-------------------------------------------------------------------------*//**
  The MSS_RTC_get_binary_count() function returns the current value of the RTC
  binary counter. 
  Note: This function must only be used when the RTC is configured to operate in
        binary counter mode.
        
  @param
    This function takes no parameters.

  @return
    This function returns the current value of the RTC binary counter as an
    unsigned 64-bit integer.
 */
uint64_t
MSS_RTC_get_binary_count(void);

/*-------------------------------------------------------------------------*//**
  The MSS_RTC_start() function starts the RTC incrementing.

  @param
    This function takes no parameters.

  @return
    This function does not return a value.
 */
void MSS_RTC_start(void);

/*-------------------------------------------------------------------------*//**
  The MSS_RTC_stop() function stops the RTC from incrementing.

  @param
    This function takes no parameters.

  @return
    This function does not return a value.
 */
void MSS_RTC_stop(void);

/*-------------------------------------------------------------------------*//**
  The MSS_RTC_reset_counter() function resets the RTC counters. If the counter
  was running before calling this function, then it continues incrementing from
  the counter’s reset value.
  
  @param
    This function takes no parameters.

  @return
    This function does not return a value.
 */
void MSS_RTC_reset_counter(void);

/*-------------------------------------------------------------------------*//**
  The MSS_RTC_enable_irq() function enables the RTC wakeup output to interrupt
  the Cortex-M3 when an alarm occurs. It enables the RTC wakeup interrupt
  (RTC_Wakeup_IRQn) in the Cortex-M3 interrupt controller (NVIC). The
  RTC_Wakeup_IRQHandler() function will be called when an RTC wakeup interrupt
  occurs.
  Note: An RTC_Wakeup_IRQHandler() default implementation is defined, with weak
        linkage, in the SmartFusion2 CMSIS HAL. You must provide your own
        implementation of the RTC_Wakeup_IRQHandler() function, which will
        override the default implementation, to suit your application.
  Note: This function only enables the RTC wakeup interrupt at the Cortex-M3
        NVIC level. The alarm setting functions enable the wakeup interrupt
        output from the RTC.
 */
void MSS_RTC_enable_irq(void);

/*-------------------------------------------------------------------------*//**
  The MSS_RTC_disable_irq() function disables the RTC wakeup interrupt
  (RTC_Wakeup_IRQn) in the Cortex-M3 interrupt controller (NVIC).
  Note: This function only disables the RTC wakeup interrupt at the Cortex-M3
        NVIC level. It does not disable the wakeup interrupt output from the
        RTC.
        
   @param
     This function takes no parameters.

   @return
     This function does not return a value.
 */
void MSS_RTC_disable_irq(void);

/*-------------------------------------------------------------------------*//**
  The MSS_RTC_clear_irq() function clears a pending wakeup interrupt from the
  RTC. This function does not clear the interrupt in the Cortex-M3 interrupt
  controller (NVIC); it only clears the wakeup output from the RTC.
  Note: You must call the MSS_RTC_clear_irq() function as part of your
        implementation of the RTC_Wakeup_IRQHandler() RTC wakeup interrupt
        service routine (ISR) in order to prevent the same interrupt event
        retriggering a call to the ISR.
        
  @param
    This function takes no parameters.

  @return
    This function does not return a value.
  
  Example:
  The example code below demoinstrates how the MSS_RTC_clear_irq() function is
  intended to be used as part of the RTC wakeup interrupt servicer routine used
  by an application to handle RTC alarms.
  @code
    #if defined(__GNUC__)
    __attribute__((__interrupt__)) void RTC_Wakeup_IRQHandler( void )
    #else
    void RTC_Wakeup_IRQHandler( void )
    #endif
    {
        process_alarm();
        MSS_RTC_clear_irq();
    }
  @endcode
*/
void MSS_RTC_clear_irq(void);

/*-------------------------------------------------------------------------*//**
  The MSS_RTC_set_calendar_count_alarm() function sets up the RTC to generate an
  alarm when the RTC count reaches the time/date specified by the alarm_value
  parameter. The alarm asserts a wakeup interrupt to the Cortex-M3. This
  function enables the RTC’s wakeup interrupt output, however the RTC wakeup
  interrupt input to the Cortex-M3 NVIC must be enabled separately by calling
  the MSS_RTC_enable_irq() function. The alarm can be disabled at any time by
  calling the MSS_RTC_disable_irq() function.
  
  Single-shot alarm
  The alarm can be a single-shot alarm, which will generate a single wakeup
  interrupt the first time the RTC count reaches the time/date specified by
  alarm_value. A single shot alarm is achieved by specifying a value for every
  field of the mss_rtc_calendar_t data structure pointed to by the alarm_value
  parameter. The RTC counter will keep incrementing after a single shot alarm
  occurs.
  
  Periodic alarm
  The alarm can also be a periodic alarm, which will generate a wakeup interrupt
  every time the RTC count reaches the time/date specified by alarm_value, with
  the counter running in a continuous loop. The periodic alarm can be set to
  occur every minute, hour, day, month, year, week, day of the week, or any
  valid combination of these. This is achieved by setting some of the fields of
  the mss_rtc_calendar_t data structure pointed to by the alarm_value parameter,
  to MSS_RTC_CALENDAR_DONT_CARE. For example, setting the weekday field to
  MSS_RTC_MONDAY and all other fields to MSS_RTC_CALENDAR_DONT_CARE will result
  in an alarm occurring every Monday. You can refine the time at which the alarm
  will occur by specifying values for the hour, minute and second fields.
  Note: This function must only be used when the RTC is configured to operate in
        calendar counter mode.
  
  @param alarm_value
    The alarm_value parameter is a pointer to an mss_rtc_calendar_t data
    structure specifying the date and time at which the alarm is to occur. You
    must assign the required date and time values to the mss_rtc_calendar_t
    structure before calling this function. Some of the fields within the
    mss_rtc_calendar_t structure can be set to MSS_RTC_CALENDAR_DONT_CARE, to
    indicate that they are not to be considered in deciding when the alarm will
    occur; this is necessary when setting periodic alarms.
  
  @return
    This function does not return a value.
     
  Examples:
  
  The following example code demonstrates how to configure the RTC to generate a
  single calendar alarm at a specific date and time. The alarm will only occur
  once and the RTC will keep incrementing regardless of the alarm taking place.
  
  @code
    const mss_rtc_calendar_t initial_calendar_count =
    {
        15u,     second
        30u,     minute
        6u,      hour
        6u,      day
        9u,      month
        12u,     year
        5u,      weekday
        37u      week
    };
    
    mss_rtc_calendar_t alarm_calendar_count =
    {
        17u,     second
        30u,     minute
        6u,      hour
        6u,      day
        9u,      month
        12u,     year
        5u,      weekday
        37u      week
    };
    
    MSS_RTC_init(MSS_RTC_CALENDAR_MODE, RTC_PRESCALER);
    MSS_RTC_clear_irq();
    MSS_RTC_set_calendar_count(&initial_calendar_count);
    MSS_RTC_enable_irq();
    MSS_RTC_start();
    
    MSS_RTC_set_calendar_count_alarm(&alarm_calendar_count);
  @endcode
  
  The following example code demonstrates how to configure the RTC to generate a
  periodic calendar alarm. The RTC is configured to generate an alarm every
  Tuesday at 16:45:00. The alarm will reoccur every week until the RTC wakeup
  interrupt is disabled using a call to MSS_RTC_disable_irq().
  
  @code
    mss_rtc_calendar_t initial_calendar_count =
    {
        58u,                            <--second
        59u,                            <--minute
        23u,                            <--hour
        10u,                            <--day
        9u,                             <--month
        12u,                            <--year
        MSS_RTC_MONDAY,                 <--weekday
        37u                             <--week
    };
    
    mss_rtc_calendar_t alarm_calendar_count =
    {
        MSS_RTC_CALENDAR_DONT_CARE,     <--second
        45u,                            <--minute
        16u,                            <--hour
        MSS_RTC_CALENDAR_DONT_CARE,     <--day
        MSS_RTC_CALENDAR_DONT_CARE,     <--month
        MSS_RTC_CALENDAR_DONT_CARE,     <--year
        MSS_RTC_TUESDAY,                <--weekday
        MSS_RTC_CALENDAR_DONT_CARE      <--week
    };
    
    MSS_RTC_init(MSS_RTC_CALENDAR_MODE, RTC_PRESCALER);
    MSS_RTC_set_calendar_count(&initial_calendar_count);
    MSS_RTC_enable_irq();
    MSS_RTC_start();
    
    MSS_RTC_set_calendar_count_alarm(&alarm_calendar_count);
  @endcode
  
  The following example code demonstrates the code that you need to include in
  your application to handle alarms. It is the interrupt service routine for the
  RTC wakeup interrupt input to the Cortex-M3 NVIC. You need to add your
  application code in this function in place of the process_alarm() function but
  you must retain the call to MSS_RTC_clear_irq() to ensure that the same alarm
  does not retrigger the interrupt.
  
  @code
    #if defined(__GNUC__)
    __attribute__((__interrupt__)) void RTC_Wakeup_IRQHandler( void )
    #else
    void RTC_Wakeup_IRQHandler( void )
    #endif
    {
        process_alarm();
        MSS_RTC_clear_irq();
    }
  @endcode
 */
void MSS_RTC_set_calendar_count_alarm
(
    const mss_rtc_calendar_t * alarm_value
);

/*-------------------------------------------------------------------------*//**
  The MSS_RTC_set_binary_count_alarm() function sets up the RTC to generate an
  alarm when the RTC count reaches the value specified by the alarm_value
  parameter. The alarm asserts a wakeup interrupt to the Cortex-M3. This
  function enables the RTC’s wakeup interrupt output, however the RTC wakeup
  interrupt input to the Cortex-M3 NVIC must be enabled separately by calling
  the MSS_RTC_enable_irq() function. The alarm can be disabled at any time by
  calling the MSS_RTC_disable_irq() function.

  Single-shot alarm
  The alarm can be a single-shot alarm, which will generate a single wakeup
  interrupt the first time the RTC count reaches the value specified by the
  alarm_value parameter. Setting the alarm_value parameter to
  MSS_RTC_PERIODIC_ALARM produces a single-shot alarm. The RTC counter continues
  incrementing when a single shot alarm occurs.

  Periodic alarm
  The alarm can also be a periodic alarm, which will generate a wakeup interrupt
  every time the RTC count reaches the value specified by the alarm_value
  parameter. Setting the alarm_value parameter to MSS_RTC_SINGLE_SHOT_ALARM
  produces a periodic alarm. The RTC counter automatically wraps around to zero
  and continues incrementing when a periodic alarm occurs.
  Note: This function must only be used when the RTC is configured to operate in
        binary counter mode
  
  @param alarm_value
    The alarm_value parameter is a 64-bit unsigned value specifying the RTC
    counter value that must be reached for the requested alarm to occur.
  
  @param alarm_type
    The alarm_type parameter specifies whether the requested alarm is a single
    shot or periodic alarm. It can only take one of these two values:
     - MSS_RTC_SINGLE_SHOT_ALARM,
     - MSS_RTC_PERIODIC_ALARM
  
  @return
    This function does not return a value.
 */
void MSS_RTC_set_binary_count_alarm
(
    uint64_t alarm_value,
    mss_rtc_alarm_type_t alarm_type
);

/*-------------------------------------------------------------------------*//**
  The MSS_RTC_get_update_flag() function indicates if the RTC counter has
  incremented since the last call to MSS_RTC_clear_update_flag(). It returns
  zero if no RTC counter increment has occurred. It returns a non-zero value if
  the RTC counter has incremented. This function can be used whether the RTC is
  configured to operate in calendar or binary counter mode.
  
  @return
   This function returns, 
   zero:     if the RTC has not incremented since the last call to
             MSS_RTC_clear_update_flag(), 
   non-zero: if the RTC has incremented since the last call to
             MSS_RTC_clear_update_flag().

   
  Example
  This example waits for the RTC timer to increment by one second.
  @code
    void wait_start_of_second(void)
    {
        uint32_t rtc_count_updated;
        MSS_RTC_clear_update_flag();
        do {
            rtc_count_updated = MSS_RTC_get_update_flag();
        } while(!rtc_count_updated)
    }
  @endcode
 */
uint32_t MSS_RTC_get_update_flag(void);

/*-------------------------------------------------------------------------*//**
  The MSS_RTC_clear_update_flag() function clears the CONTROL register flag that
  is set when the RTC counter increments. It is used alongside function
  MSS_RTC_get_update_flag() to detect RTC counter increments.
  
  @return
    This function does not return a value.
    
  Example
  The example below will wait for the RTC timer to increment by one second.
  @code
  void wait_start_of_second(void)
  {
      uint32_t rtc_count_updated;
      MSS_RTC_clear_update_flag();
      do {
          rtc_count_updated = MSS_RTC_get_update_flag();
      } while(!rtc_count_updated)
  }
  @endcode
 */
void MSS_RTC_clear_update_flag(void);

#ifdef __cplusplus
}
#endif

#endif /* MSS_RTC_H_ */
