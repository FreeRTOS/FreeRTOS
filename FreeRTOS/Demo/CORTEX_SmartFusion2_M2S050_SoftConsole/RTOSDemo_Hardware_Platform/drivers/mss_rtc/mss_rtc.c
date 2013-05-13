/*******************************************************************************
 * (c) Copyright 2008-2013 Microsemi SoC Products Group.  All rights reserved.
 * 
 * SmartFusion2 MSS RTC bare metal driver implementation.
 *
 * SVN $Revision: 5090 $
 * SVN $Date: 2013-02-18 12:13:31 +0000 (Mon, 18 Feb 2013) $
 */
#include "mss_rtc.h"
#include "../../CMSIS/mss_assert.h"
#include <string.h>

#ifdef __cplusplus
extern "C" {
#endif 

/*-------------------------------------------------------------------------*//**
 * CONTROL_REG register masks.
 */
#define CONTROL_RUNNING_MASK        0x00000001u

#define CONTROL_RTC_START_MASK      0x00000001u
#define CONTROL_RTC_STOP_MASK       0x00000002u
#define CONTROL_ALARM_ON_MASK       0x00000004u
#define CONTROL_ALARM_OFF_MASK      0x00000008u
#define CONTROL_RESET_MASK          0x00000010u
#define CONTROL_UPLOAD_MASK         0x00000020u
#define CONTROL_WAKEUP_CLR_MASK     0x00000100u
#define CONTROL_UPDATED_MASK        0x00000400u

/*-------------------------------------------------------------------------*//**
 * MODE_REG register masks.
 */
#define MODE_CLK_MODE_MASK          0x00000001u
#define MODE_WAKEUP_EN_MASK         0x00000002u
#define MODE_WAKEUP_RESET_MASK      0x00000004u
#define MODE_WAKEUP_CONTINUE_MASK   0x00000008u

/*-------------------------------------------------------------------------*//**
 * Other masks.
 */
#define MAX_BINARY_HIGHER_COUNT     0x7FFu
#define MASK_32_BIT                 0xFFFFFFFFu
#define MAX_PRESCALAR_COUNT         0x03FFFFFFu
#define CALENDAR_SHIFT              8u

#define COMPARE_ALL_BITS            0xFFFFFFFFu

#define SYSREG_RTC_WAKEUP_M3_EN_MASK    0x00000001u

/*-------------------------------------------------------------------------*//**
 * Index into look-up table.
 */
#define SECONDS     0
#define MINUTES     1
#define HOURS       2
#define DAYS        3
#define MONTHS      4
#define YEARS       5
#define WEEKDAYS    6
#define WEEKS       7

/*-------------------------------------------------------------------------*//**
  Local functions.
 */
static uint8_t
get_clock_mode
(
    void
);

static void set_rtc_mode(uint8_t requested_mode);

static void add_alarm_cfg_values
(
    uint8_t calendar_item,
    uint32_t * p_calendar_value,
    uint32_t * p_compare_mask
    
);

/*-------------------------------------------------------------------------*//**
 * See "mss_rtc.h" for details of how to use this function.
 */
void
MSS_RTC_init
(
    uint8_t mode,
    uint32_t prescaler
)
{
    ASSERT(prescaler <= MAX_PRESCALAR_COUNT);

    if(prescaler <= MAX_PRESCALAR_COUNT)
    {
        /* Stop the RTC. */
        MSS_RTC_stop();
        
        /* Disable alarm. */
        RTC->CONTROL_REG = CONTROL_ALARM_OFF_MASK;
        
        /* Disable Interrupt */
        MSS_RTC_disable_irq();
        NVIC_ClearPendingIRQ(RTC_Wakeup_IRQn);

        /* Clear RTC wake up interrupt signal */
        MSS_RTC_clear_irq();

        /* Enable the RTC to interrupt the Cortex-M3. */
        SYSREG->RTC_WAKEUP_CR |= SYSREG_RTC_WAKEUP_M3_EN_MASK;
        
        /* Select mode of operation, including the wake configuration. */
        if(MSS_RTC_CALENDAR_MODE == mode)
        {
            RTC->MODE_REG = MODE_CLK_MODE_MASK;
        }
        else
        {
            RTC->MODE_REG = 0u;
        }
        
        /* Reset the alarm and compare registers to a known value. */
        RTC->ALARM_LOWER_REG = 0u;
        RTC->ALARM_UPPER_REG = 0u;
        RTC->COMPARE_LOWER_REG = 0u;
        RTC->COMPARE_UPPER_REG = 0u;

        /* Reset the calendar counters */
        MSS_RTC_reset_counter();

        /* Set new Prescaler value */
        RTC->PRESCALER_REG = prescaler;
    }
}

/*-------------------------------------------------------------------------*//**
  See "mss_rtc.h" for details of how to use this function.
 */
void
MSS_RTC_set_calendar_count
(
    const mss_rtc_calendar_t *new_rtc_value
)
{
    uint8_t error = 0u;
    uint8_t clock_mode;
    
    const uint8_t g_rtc_max_count_lut[] =
    {
       /* Calendar mode */
        59u,    /* Seconds */
        59u,    /* Minutes */
        23u,    /* Hours   */
        31u,    /* Days    */
        12u,    /* Months  */
        254u,   /* Years   */
        7u,     /* Weekdays*/
        52u     /* Week    */
    };

    const uint8_t g_rtc_min_count_lut[] =
    {
       /* Calendar mode */
        0u, /* Seconds */
        0u, /* Minutes */
        0u, /* Hours   */
        1u, /* Days    */
        1u, /* Months  */
        0u, /* Years   */
        1u, /* Weekdays*/
        1u  /* Week    */
    };
    
    /* Assert if the values cross the limit */
    ASSERT(new_rtc_value->second >= g_rtc_min_count_lut[SECONDS]);
    ASSERT(new_rtc_value->second <= g_rtc_max_count_lut[SECONDS]);
    ASSERT(new_rtc_value->minute >= g_rtc_min_count_lut[MINUTES]);
    ASSERT(new_rtc_value->minute <= g_rtc_max_count_lut[MINUTES]);
    ASSERT(new_rtc_value->hour >= g_rtc_min_count_lut[HOURS]);
    ASSERT(new_rtc_value->hour <= g_rtc_max_count_lut[HOURS]);
    ASSERT(new_rtc_value->day >= g_rtc_min_count_lut[DAYS]);
    ASSERT(new_rtc_value->day <= g_rtc_max_count_lut[DAYS]);
    ASSERT(new_rtc_value->month >= g_rtc_min_count_lut[MONTHS]);
    ASSERT(new_rtc_value->month <= g_rtc_max_count_lut[MONTHS]);
    ASSERT(new_rtc_value->year >= g_rtc_min_count_lut[YEARS]);
    ASSERT(new_rtc_value->year <= g_rtc_max_count_lut[YEARS]);
    ASSERT(new_rtc_value->weekday >= g_rtc_min_count_lut[WEEKDAYS]);
    ASSERT(new_rtc_value->weekday <= g_rtc_max_count_lut[WEEKDAYS]);
    ASSERT(new_rtc_value->week >= g_rtc_min_count_lut[WEEKS]);
    ASSERT(new_rtc_value->week <= g_rtc_max_count_lut[WEEKS]);

    if(new_rtc_value->second < g_rtc_min_count_lut[SECONDS]) {error = 1u;}
    if(new_rtc_value->second > g_rtc_max_count_lut[SECONDS]) {error = 1u;}
    if(new_rtc_value->minute < g_rtc_min_count_lut[MINUTES]) {error = 1u;}
    if(new_rtc_value->minute > g_rtc_max_count_lut[MINUTES]) {error = 1u;}
    if(new_rtc_value->hour < g_rtc_min_count_lut[HOURS]) {error = 1u;}
    if(new_rtc_value->hour > g_rtc_max_count_lut[HOURS]) {error = 1u;}
    if(new_rtc_value->day < g_rtc_min_count_lut[DAYS]) {error = 1u;}
    if(new_rtc_value->day > g_rtc_max_count_lut[DAYS]) {error = 1u;}
    if(new_rtc_value->month < g_rtc_min_count_lut[MONTHS]) {error = 1u;}
    if(new_rtc_value->month > g_rtc_max_count_lut[MONTHS]) {error = 1u;}
    if(new_rtc_value->year < g_rtc_min_count_lut[YEARS]) {error = 1u;}
    if(new_rtc_value->year > g_rtc_max_count_lut[YEARS]) {error = 1u;}
    if(new_rtc_value->weekday < g_rtc_min_count_lut[WEEKDAYS]) {error = 1u;}
    if(new_rtc_value->weekday > g_rtc_max_count_lut[WEEKDAYS]) {error = 1u;}
    if(new_rtc_value->week < g_rtc_min_count_lut[WEEKS]) {error = 1u;}
    if(new_rtc_value->week > g_rtc_max_count_lut[WEEKS]) {error = 1u;}

    /* 
     * This function can only be used when the RTC is configured to operate in
     * calendar counter mode. 
     */
    clock_mode = get_clock_mode();
    ASSERT(MSS_RTC_CALENDAR_MODE == clock_mode);
    
    if((0u == error) && (MSS_RTC_CALENDAR_MODE == clock_mode))
    {
        uint32_t upload_in_progress;
        
        /*
         * Write the RTC new value. 
         */
        RTC->SECONDS_REG = new_rtc_value->second;
        RTC->MINUTES_REG = new_rtc_value->minute;
        RTC->HOURS_REG = new_rtc_value->hour;
        RTC->DAY_REG = new_rtc_value->day;
        RTC->MONTH_REG = new_rtc_value->month;
        RTC->YEAR_REG = new_rtc_value->year;
        RTC->WEEKDAY_REG = new_rtc_value->weekday;
        RTC->WEEK_REG = new_rtc_value->week;

        /* Data is copied, now issue upload command */
        RTC->CONTROL_REG = CONTROL_UPLOAD_MASK ;
        
        /* Wait for the upload to complete. */
        do {
            upload_in_progress = RTC->CONTROL_REG & CONTROL_UPLOAD_MASK;
        } while(upload_in_progress);
    }
}

/*-------------------------------------------------------------------------*//**
 * See "mss_rtc.h" for details of how to use this function.
 */
void
MSS_RTC_set_binary_count
(
    uint64_t new_rtc_value
)
{
    uint8_t clock_mode;

    /* 
     * This function can only be used when the RTC is configured to operate in
     * binary counter mode. 
     */
    clock_mode = get_clock_mode();
    ASSERT(MSS_RTC_BINARY_MODE == clock_mode);
    
    if(MSS_RTC_BINARY_MODE == clock_mode)
    {
        uint32_t rtc_upper_32_bit_value;
        
        rtc_upper_32_bit_value = (uint32_t)(new_rtc_value >> 32u) & MASK_32_BIT;

        /* Assert if the values cross the limit */
        ASSERT(rtc_upper_32_bit_value <= MAX_BINARY_HIGHER_COUNT);

        if(rtc_upper_32_bit_value <= MAX_BINARY_HIGHER_COUNT)
        {
            uint32_t upload_in_progress;
            
            /*
             * Write the RTC new value. 
             */
            RTC->DATE_TIME_LOWER_REG = (uint32_t)new_rtc_value;
            RTC->DATE_TIME_UPPER_REG =
                    (uint32_t)(( new_rtc_value >> 32u) & MAX_BINARY_HIGHER_COUNT);

            /* Data is copied, now issue upload command */
            RTC->CONTROL_REG = CONTROL_UPLOAD_MASK;
            
            /* Wait for the upload to complete. */
            do {
                upload_in_progress = RTC->CONTROL_REG & CONTROL_UPLOAD_MASK;
            } while(upload_in_progress);
        }
    }
}

/*-------------------------------------------------------------------------*//**
 * See "mss_rtc.h" for details of how to use this function.
 */
void
MSS_RTC_get_calendar_count
(
    mss_rtc_calendar_t *p_rtc_calendar
)
{
    uint8_t clock_mode;
    /* 
     * This function can only be used when the RTC is configured to operate in
     * calendar counter mode. 
     */
    clock_mode = get_clock_mode();
    ASSERT(MSS_RTC_CALENDAR_MODE == clock_mode);
    
    if(MSS_RTC_CALENDAR_MODE == clock_mode)
    {
        p_rtc_calendar->second = (uint8_t)RTC->SECONDS_REG;
        p_rtc_calendar->minute = (uint8_t)RTC->MINUTES_REG;
        p_rtc_calendar->hour = (uint8_t)RTC->HOURS_REG;
        p_rtc_calendar->day = (uint8_t)RTC->DAY_REG;
        p_rtc_calendar->month = (uint8_t)RTC->MONTH_REG;
        p_rtc_calendar->year = (uint8_t)RTC->YEAR_REG;
        p_rtc_calendar->weekday = (uint8_t)RTC->WEEKDAY_REG;
        p_rtc_calendar->week = (uint8_t)RTC->WEEK_REG;
    }
    else
    {
        /*
         * Set returned calendar count to zero if the RTC is not configured for
         * calendar counter mode. This should make incorrect release application
         * code behave consistently and help application debugging.
         */
        memset(p_rtc_calendar, 0, sizeof(mss_rtc_calendar_t));
    }
}

/*-------------------------------------------------------------------------*//**
 * See "mss_rtc.h" for details of how to use this function.
 */
uint64_t
MSS_RTC_get_binary_count
(
    void
)
{
    uint64_t rtc_count;
    uint8_t clock_mode;

    /* 
     * This function can only be used when the RTC is configured to operate in
     * binary counter mode. 
     */
    clock_mode = get_clock_mode();
    ASSERT(MSS_RTC_BINARY_MODE == clock_mode);
    
    if(MSS_RTC_BINARY_MODE == clock_mode)
    {
        rtc_count = RTC->DATE_TIME_LOWER_REG;
        rtc_count = rtc_count | ((uint64_t)RTC->DATE_TIME_UPPER_REG << 32u) ;
    }
    else
    {
        /*
         * Set returned binary count to zero if the RTC is not configured for
         * binary counter mode. This should make incorrect release application
         * code behave consistently and help application debugging.
         */
        rtc_count = 0u;
    }

    return rtc_count;
}

/*-------------------------------------------------------------------------*//**
 *
 */
static void add_alarm_cfg_values
(
    uint8_t calendar_item,
    uint32_t * p_calendar_value,
    uint32_t * p_compare_mask
    
)
{
    if(MSS_RTC_CALENDAR_DONT_CARE == calendar_item)
    {
        *p_calendar_value = (uint32_t)(*p_calendar_value << CALENDAR_SHIFT);
        *p_compare_mask = (uint32_t)(*p_compare_mask << CALENDAR_SHIFT);
    }
    else
    {
        *p_calendar_value = (uint32_t)((*p_calendar_value << CALENDAR_SHIFT) | (uint32_t)calendar_item);
        *p_compare_mask = (uint32_t)((*p_compare_mask << CALENDAR_SHIFT) | (uint32_t)0xFFu);
    }
}

/*-------------------------------------------------------------------------*//**
 * See "mss_rtc.h" for details of how to use this function.
 */
void MSS_RTC_set_calendar_count_alarm
(
    const mss_rtc_calendar_t * alarm_value
)
{
    uint32_t calendar_value;
    uint32_t compare_mask;
    uint8_t mode;
    
    mode = (uint8_t)(RTC->MODE_REG & MODE_CLK_MODE_MASK);
    /*
     * This function can only be used with the RTC set to operate in calendar
     * mode.
     */
    ASSERT(MSS_RTC_CALENDAR_MODE == mode);
    if(MSS_RTC_CALENDAR_MODE == mode)
    {
        uint8_t required_mode_reg;
        
        /* Disable the alarm before updating*/
        RTC->CONTROL_REG = CONTROL_ALARM_OFF_MASK;

        /* Set alarm and compare lower registers. */
        calendar_value = 0u;
        compare_mask = 0u;
        
        add_alarm_cfg_values(alarm_value->day, &calendar_value, &compare_mask);
        add_alarm_cfg_values(alarm_value->hour, &calendar_value, &compare_mask);
        add_alarm_cfg_values(alarm_value->minute, &calendar_value, &compare_mask);
        add_alarm_cfg_values(alarm_value->second, &calendar_value, &compare_mask);

        RTC->ALARM_LOWER_REG = calendar_value;
        RTC->COMPARE_LOWER_REG = compare_mask;

        /* Set alarm and compare upper registers. */
        calendar_value = 0u;
        compare_mask = 0u;
        
        add_alarm_cfg_values(alarm_value->week, &calendar_value, &compare_mask);
        add_alarm_cfg_values(alarm_value->weekday, &calendar_value, &compare_mask);
        add_alarm_cfg_values(alarm_value->year, &calendar_value, &compare_mask);
        add_alarm_cfg_values(alarm_value->month, &calendar_value, &compare_mask);

        RTC->ALARM_UPPER_REG = calendar_value;
        RTC->COMPARE_UPPER_REG = compare_mask;
        
        /* Configure the RTC to enable the alarm. */
        required_mode_reg = mode | MODE_WAKEUP_EN_MASK | MODE_WAKEUP_CONTINUE_MASK;
        set_rtc_mode(required_mode_reg);
        
        /* Enable the alarm */
        RTC->CONTROL_REG = CONTROL_ALARM_ON_MASK ;
    }
}

/*-------------------------------------------------------------------------*//**
  We only write the RTC mode register if really required because the RTC needs
  to be stopped for the mode register to be written. Stopping the RTC everytime
  the wakeup alarm configuration is set might induce drift on the RTC time.
  This function is intended to be used when setting alarms.
 */
static void set_rtc_mode(uint8_t requested_mode)
{
    if(RTC->MODE_REG != requested_mode)
    {
        uint32_t rtc_running;
        rtc_running = RTC->CONTROL_REG & CONTROL_RUNNING_MASK;
        if(rtc_running)
        {
            /* Stop the RTC in order to change the mode register content.*/
            MSS_RTC_stop();
            RTC->MODE_REG = requested_mode;
            MSS_RTC_start();
        }
        else
        {
            RTC->MODE_REG = requested_mode;
        }
    }
}

/*-------------------------------------------------------------------------*//**
 * See "mss_rtc.h" for details of how to use this function.
 */
void MSS_RTC_set_binary_count_alarm
(
    uint64_t alarm_value,
    mss_rtc_alarm_type_t alarm_type
)
{
    uint8_t mode;
    
    mode = (uint8_t)(RTC->MODE_REG & MODE_CLK_MODE_MASK);
    /*
     * This function can only be used with the RTC set to operate in binary
     * counter mode.
     */
    ASSERT(MSS_RTC_BINARY_MODE == mode);
    if(MSS_RTC_BINARY_MODE == mode)
    {
        uint8_t required_mode_reg;
        
        /* Disable the alarm before updating*/
        RTC->CONTROL_REG = CONTROL_ALARM_OFF_MASK;

        /* Set the alarm value. */
        RTC->COMPARE_LOWER_REG = COMPARE_ALL_BITS;
        RTC->COMPARE_UPPER_REG = COMPARE_ALL_BITS;
        RTC->ALARM_LOWER_REG = (uint32_t)alarm_value;
        RTC->ALARM_UPPER_REG = (uint32_t)(alarm_value >> 32u);

        /*
         * Configure the RTC to enable the alarm.
         */
        required_mode_reg = mode | MODE_WAKEUP_EN_MASK | MODE_WAKEUP_CONTINUE_MASK;
        if(MSS_RTC_PERIODIC_ALARM == alarm_type)
        {
            /*
             * The RTC binary counter will be fully reset when the alarm occurs.
             * The counter will continue counting while the wake-up interrupt is
             * active.
             */
            required_mode_reg |= MODE_WAKEUP_RESET_MASK;
        }
        set_rtc_mode(required_mode_reg);
        
        /* Enable the alarm */
        RTC->CONTROL_REG = CONTROL_ALARM_ON_MASK;
    }
}

/*-------------------------------------------------------------------------*//**
 * See "mss_rtc.h" for details of how to use this function.
 */
void
MSS_RTC_start
(
    void
)
{
    RTC->CONTROL_REG = CONTROL_RTC_START_MASK;
}

/*-------------------------------------------------------------------------*//**
 * See "mss_rtc.h" for details of how to use this function.
 */
void
MSS_RTC_stop
(
    void
)
{
    uint32_t rtc_running;
    
    /*
     * Send command to stop RTC.
     */
    RTC->CONTROL_REG = CONTROL_RTC_STOP_MASK;
    
    /* 
     * Wait for RTC internal synchronization to take place and RTC to actually
     * stop.
     */
    do {
        rtc_running =  RTC->CONTROL_REG & CONTROL_RUNNING_MASK;
    } while(rtc_running);
}

/*-------------------------------------------------------------------------*//**
  See "mss_rtc.h" for details of how to use this function.
 */
void
MSS_RTC_reset_counter
(
    void
)
{
    uint32_t upload_in_progress;
    
    RTC->CONTROL_REG = CONTROL_RESET_MASK;
    
    /* Wait for the upload to complete. */
    do {
        upload_in_progress = RTC->CONTROL_REG & CONTROL_UPLOAD_MASK;
    } while(upload_in_progress);
}

/*-------------------------------------------------------------------------*//**
  See "mss_rtc.h" for details of how to use this function.
 */
uint32_t MSS_RTC_get_update_flag(void)
{
    uint32_t updated;
    updated = RTC->CONTROL_REG & CONTROL_UPDATED_MASK;
    return updated;
}

/*-------------------------------------------------------------------------*//**
  See "mss_rtc.h" for details of how to use this function.
 */
void MSS_RTC_clear_update_flag(void)
{
    /* Clear the "updated" control bit. */
    RTC->CONTROL_REG = CONTROL_UPDATED_MASK;
}

/*-------------------------------------------------------------------------*//**
  See "mss_rtc.h" for details of how to use this function.
 */
void MSS_RTC_enable_irq(void)
{
    /*
     * Only the NVIC level interrupt enable is performed within this function.
     * The RTC level interrupt enable is performed within the alarm setting
     * functions.
     * This avoid the MODE register being modified whenever Cortex-M3 RTC
     * interrupts are enabled/disabled. 
     */
    NVIC_EnableIRQ(RTC_Wakeup_IRQn);
}

/*-------------------------------------------------------------------------*//**
  See "mss_rtc.h" for details of how to use this function.
 */
void
MSS_RTC_disable_irq
(
    void
)
{
    /*
     * Only the NVIC level interrupt disable is performed within this function.
     * This avoid the MODE register being modified whenever Cortex-M3 RTC
     * interrupts are enabled/disabled. 
     */
    NVIC_DisableIRQ(RTC_Wakeup_IRQn);
}

/*-------------------------------------------------------------------------*//**
 * See "mss_rtc.h" for details of how to use this function.
 */
void
MSS_RTC_clear_irq
(
    void
)
{
    /* Clear wake up interrupt signal */
    RTC->CONTROL_REG = CONTROL_WAKEUP_CLR_MASK;
}

/*-------------------------------------------------------------------------*//**
  The get_clock_mode() function gets the clock mode of RTC hardware.
  Possible clock modes are:
    MSS_RTC_CALENDAR_MODE
    MSS_RTC_BINARY_MODE
 */
static uint8_t
get_clock_mode
(
    void
)
{
    uint8_t clock_mode;

    clock_mode = (uint8_t)(RTC->MODE_REG & MODE_CLK_MODE_MASK);

    return(clock_mode);
}

#ifdef __cplusplus
}
#endif

