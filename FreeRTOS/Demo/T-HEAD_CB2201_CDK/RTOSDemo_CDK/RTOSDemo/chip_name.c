/*============================================================================
 * Name        : chip_name.c
 * Author      : $(UserName)
 * Copyright   : Your copyright notice
 * Description : System Initialization before main
 * 1 CPU initialization
 * 2 memory & IO base address initialization
 * 3 flash size & address initialization
 * 4 interrupt resource initialization for the soc
 *============================================================================
 */
#include "chip_name.h"
/**
 *  @brief initial CPU based on user config in chip_name.h
 */
static void CPUInit(void)
{
	/**
	 * Config CPU's Unit such as MGU, Cache...
	 */
	
	return;
}

/**
 * @brief entry of whole chip initialization
 * @Note anyone should not use any global variable in this function since this function is called 
 * at before data section's initialization.
 * Since here SystemInit is a weak symbol, any vendor can override this symbol on its own wishes.
 */
 
 #define CONFIG_SYSTICK_HZ 100
 #define CONFIG_SYSTEM_FREQ 24000000
 
__attribute__((weak)) void  SystemInit(void) 
{
	/**
	 * initial CPU based on the config in chip_name.h
	 */
	CPUInit();
	
	/**
	 * TODO: initial IO, memory, flash... 
	 */
	 
	drv_coret_config(CONFIG_SYSTEM_FREQ / CONFIG_SYSTICK_HZ, CORET_IRQn);    //10ms
    csi_vic_enable_sirq(CORET_IRQn);
	
    return;
}