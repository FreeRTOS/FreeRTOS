/*******************************************************************************
 * (c) Copyright 2009-2013 Microsemi SoC Products Group.  All rights reserved.
 *
 * Simple SmartFusion2 microcontroller subsystem (MSS) GPIO example program.
 *
 * Please refer to the file README.txt for further details about this example.
 *
 * SVN $Revision: 5491 $
 * SVN $Date: 2013-03-29 16:00:31 +0000 (Fri, 29 Mar 2013) $
 */
#include "drivers/mss_gpio/mss_gpio.h"
#include "CMSIS/system_m2sxxx.h"

/*==============================================================================
  Private functions.
 */
static void delay(void);

/*==============================================================================
 * main() function.
 */
int main()
{
    /*
     * Initialize MSS GPIOs.
     */
    MSS_GPIO_init();
    
    /*
     * Configure MSS GPIOs.
     */
    MSS_GPIO_config( MSS_GPIO_0 , MSS_GPIO_OUTPUT_MODE );
    MSS_GPIO_config( MSS_GPIO_1 , MSS_GPIO_OUTPUT_MODE );
    MSS_GPIO_config( MSS_GPIO_2 , MSS_GPIO_OUTPUT_MODE );
    MSS_GPIO_config( MSS_GPIO_3 , MSS_GPIO_OUTPUT_MODE );
    
    /*
     * Infinite loop.
     */
    for(;;)
    {
        uint32_t gpio_pattern;
        /*
         * Decrement delay counter.
         */
        delay();
        
        /*
         * Toggle GPIO output pattern by doing an exclusive OR of all
         * pattern bits with ones.
         */
        gpio_pattern = MSS_GPIO_get_outputs();
        gpio_pattern ^= 0xFFFFFFFF;
        MSS_GPIO_set_outputs( gpio_pattern );
    }
    
    return 0;
}

/*==============================================================================
  Delay between displays of the watchdog counter value.
 */
static void delay(void)
{
    volatile uint32_t delay_count = SystemCoreClock / 512;
    
    while(delay_count > 0u)
    {
        --delay_count;
    }
}
