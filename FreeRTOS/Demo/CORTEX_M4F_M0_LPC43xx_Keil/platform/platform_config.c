#include "LPC43xx.h"
#include "platform_config.h"

#include "scu.h"
#include "type.h"
#include "emc_LPC43xx.h"
#include "fpu_init.h"


/**********************************************************************
 ** Function prototypes
 **********************************************************************/
void vIOInit(void);
void clockInit(void);



/* this function initializes the platform with system level settings */
void platformInit(void) {

	SystemInit();
	
	fpuInit();	
	
	/* clockInit(); the clock is set in Hitex_CGU_Init */

	vIOInit();

	#if (USE_EXT_STATIC_MEM == YES) || (USE_EXT_DYNAMIC_MEM == YES)
	 
	EMC_Init();
	
	#endif

    #if (USE_EXT_FLASH == YES)
	
	// relocate vector table to internal ram
	// updates also VTOR
	relocIrqTable(); 
	
	#endif

}

/*----------------------------------------------------------------------------
  Initialize board specific IO
 *----------------------------------------------------------------------------*/
void vIOInit(void)
{	
	#if (PLATFORM == NXP_VALIDATION_BOARD)
		// P9.2 : GPIO4_14: LD11 (LED)
		scu_pinmux(0x9 ,2 , PDN_ENABLE, FUNC0); 	
		LPC_GPIO_PORT->DIR[4] |= (1UL << 14);
	#endif
	#if (PLATFORM == HITEX_A2_BOARD)
		// P9.3 : GPIO4_15
		scu_pinmux(0x9 , 3 , PDN_ENABLE, FUNC0); 	
		LPC_GPIO_PORT->DIR[4] |= (1UL << 15);
	#endif	
}
	
/*----------------------------------------------------------------------------
  Initialize clocks
 *----------------------------------------------------------------------------*/
void clockInit(void)
{
	/* Set PL160M @ 10*12=120 MHz */
	SetPL160M(SRC_XTAL, 10); 						
	/* Run base M4 clock from PL160M, no division */
	SetClock(BASE_M4_CLK, SRC_PL160M_0, DIV1);		
	/* Show base out clock on output */
	SetClock(BASE_OUT_CLK, SRC_XTAL, DIV1);	
	
	// clock to UART 1
	SetClock(BASE_UART1_CLK, SRC_PL160M_0, DIV1);

	// clock to CAN1 > 15 MHz
	// SetClock(BASE_VPB1_CLK, SRC_PL160M_0, DIV8);				
}


