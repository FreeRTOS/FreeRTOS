/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
 * \file
 *
 * Provides the low-level initialization function that called on chip startup.
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"


#if defined(ENABLE_TCM) && defined(__GNUC__)
	extern char _itcm_lma, _sitcm, _eitcm;
#endif


/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
/* Default memory map 
   Address range        Memory region      Memory type   Shareability  Cache policy
   0x00000000- 0x1FFFFFFF Code             Normal        Non-shareable  WT
   0x20000000- 0x3FFFFFFF SRAM             Normal        Non-shareable  WBWA
   0x40000000- 0x5FFFFFFF Peripheral       Device        Non-shareable  -
   0x60000000- 0x7FFFFFFF RAM              Normal        Non-shareable  WBWA
   0x80000000- 0x9FFFFFFF RAM              Normal        Non-shareable  WT
   0xA0000000- 0xBFFFFFFF Device           Device        Shareable
   0xC0000000- 0xDFFFFFFF Device           Device        Non Shareable
   0xE0000000- 0xFFFFFFFF System           -                  -
   */

/**
 * \brief Set up a memory region.
 */
void _SetupMemoryRegion( void )
{

	uint32_t dwRegionBaseAddr;
	uint32_t dwRegionAttr;
	
	memory_barrier();

/***************************************************
	ITCM memory region --- Normal 
	START_Addr:-  0x00000000UL
	END_Addr:-    0x00400000UL
****************************************************/
	dwRegionBaseAddr = 
		ITCM_START_ADDRESS |
		MPU_REGION_VALID |
		MPU_DEFAULT_ITCM_REGION;        // 1

	dwRegionAttr = 
		MPU_AP_PRIVILEGED_READ_WRITE | 
		MPU_CalMPURegionSize(ITCM_END_ADDRESS - ITCM_START_ADDRESS) |
		MPU_REGION_ENABLE;

	MPU_SetRegion( dwRegionBaseAddr, dwRegionAttr);

/****************************************************
	Internal flash memory region --- Normal read-only 
	(update to Strongly ordered in write accesses)
	START_Addr:-  0x00400000UL
	END_Addr:-    0x00600000UL
******************************************************/
	
	dwRegionBaseAddr = 
		IFLASH_START_ADDRESS |
		MPU_REGION_VALID |
		MPU_DEFAULT_IFLASH_REGION;      //2

	dwRegionAttr = 
		MPU_AP_READONLY |
		INNER_NORMAL_WB_NWA_TYPE( NON_SHAREABLE ) |
		MPU_CalMPURegionSize(IFLASH_END_ADDRESS - IFLASH_START_ADDRESS) |
		MPU_REGION_ENABLE;

	MPU_SetRegion( dwRegionBaseAddr, dwRegionAttr);

/****************************************************
	DTCM memory region --- Normal
	START_Addr:-  0x20000000L
	END_Addr:-    0x20400000UL
******************************************************/

	/* DTCM memory region */
	dwRegionBaseAddr = 
		DTCM_START_ADDRESS |
		MPU_REGION_VALID |
		MPU_DEFAULT_DTCM_REGION;         //3

	dwRegionAttr = 
		MPU_AP_PRIVILEGED_READ_WRITE | 
		MPU_CalMPURegionSize(DTCM_END_ADDRESS - DTCM_START_ADDRESS) |
		MPU_REGION_ENABLE;

	MPU_SetRegion( dwRegionBaseAddr, dwRegionAttr);

/****************************************************
	SRAM Cacheable memory region --- Normal
	START_Addr:-  0x20400000UL
	END_Addr:-    0x2043FFFFUL
******************************************************/
	/* SRAM memory  region */
	dwRegionBaseAddr = 
		SRAM_FIRST_START_ADDRESS |
		MPU_REGION_VALID |
		MPU_DEFAULT_SRAM_REGION_1;         //4

	dwRegionAttr = 
		MPU_AP_FULL_ACCESS    |
		INNER_NORMAL_WB_NWA_TYPE( NON_SHAREABLE ) |
		MPU_CalMPURegionSize(SRAM_FIRST_END_ADDRESS - SRAM_FIRST_START_ADDRESS) 
		| MPU_REGION_ENABLE;

	MPU_SetRegion( dwRegionBaseAddr, dwRegionAttr);

	
/****************************************************
	Internal SRAM second partition memory region --- Normal 
	START_Addr:-  0x20440000UL
	END_Addr:-    0x2045FFFFUL
******************************************************/
	/* SRAM memory region */
	dwRegionBaseAddr = 
		SRAM_SECOND_START_ADDRESS |
		MPU_REGION_VALID |
		MPU_DEFAULT_SRAM_REGION_2;         //5

	dwRegionAttr = 
		MPU_AP_FULL_ACCESS    |
		INNER_NORMAL_WB_NWA_TYPE( NON_SHAREABLE ) |
		MPU_CalMPURegionSize(SRAM_SECOND_END_ADDRESS - SRAM_SECOND_START_ADDRESS) |
		MPU_REGION_ENABLE;

	MPU_SetRegion( dwRegionBaseAddr, dwRegionAttr);

/****************************************************
	Peripheral memory region --- DEVICE Shareable
	START_Addr:-  0x40000000UL
	END_Addr:-    0x5FFFFFFFUL
******************************************************/
	dwRegionBaseAddr = 
		PERIPHERALS_START_ADDRESS |
		MPU_REGION_VALID |
		MPU_PERIPHERALS_REGION;          //6

	dwRegionAttr = MPU_AP_FULL_ACCESS |
		MPU_REGION_EXECUTE_NEVER |
		SHAREABLE_DEVICE_TYPE |
		MPU_CalMPURegionSize(PERIPHERALS_END_ADDRESS - PERIPHERALS_START_ADDRESS)
		|MPU_REGION_ENABLE;

	MPU_SetRegion( dwRegionBaseAddr, dwRegionAttr);


/****************************************************
	External EBI memory  memory region --- Strongly Ordered
	START_Addr:-  0x60000000UL
	END_Addr:-    0x6FFFFFFFUL
******************************************************/
	dwRegionBaseAddr =
		EXT_EBI_START_ADDRESS |
		MPU_REGION_VALID |
		MPU_EXT_EBI_REGION;

	dwRegionAttr =
		MPU_AP_FULL_ACCESS |
		/* External memory Must be defined with 'Device' or 'Strongly Ordered'
		attribute for write accesses (AXI) */
		STRONGLY_ORDERED_SHAREABLE_TYPE |
		MPU_CalMPURegionSize(EXT_EBI_END_ADDRESS - EXT_EBI_START_ADDRESS) |
		MPU_REGION_ENABLE;

	MPU_SetRegion( dwRegionBaseAddr, dwRegionAttr);

/****************************************************
	SDRAM Cacheable memory region --- Normal
	START_Addr:-  0x70000000UL
	END_Addr:-    0x7FFFFFFFUL
******************************************************/
	dwRegionBaseAddr = 
		SDRAM_START_ADDRESS |
		MPU_REGION_VALID |
		MPU_DEFAULT_SDRAM_REGION;        //7

	dwRegionAttr = 
		MPU_AP_FULL_ACCESS    |
		INNER_NORMAL_WB_RWA_TYPE( SHAREABLE ) |
		MPU_CalMPURegionSize(SDRAM_END_ADDRESS - SDRAM_START_ADDRESS) |
		MPU_REGION_ENABLE;

	MPU_SetRegion( dwRegionBaseAddr, dwRegionAttr);

/****************************************************
	QSPI memory region --- Strongly ordered
	START_Addr:-  0x80000000UL
	END_Addr:-    0x9FFFFFFFUL
******************************************************/
	dwRegionBaseAddr = 
		QSPI_START_ADDRESS |
		MPU_REGION_VALID |
		MPU_QSPIMEM_REGION;              //8

	dwRegionAttr = 
		MPU_AP_FULL_ACCESS |
		STRONGLY_ORDERED_SHAREABLE_TYPE |
		MPU_CalMPURegionSize(QSPI_END_ADDRESS - QSPI_START_ADDRESS) |
		MPU_REGION_ENABLE;

	MPU_SetRegion( dwRegionBaseAddr, dwRegionAttr);

  
/****************************************************
	USB RAM Memory region --- Device
	START_Addr:-  0xA0100000UL
	END_Addr:-    0xA01FFFFFUL
******************************************************/
	dwRegionBaseAddr = 
		USBHSRAM_START_ADDRESS |
		MPU_REGION_VALID |
		MPU_USBHSRAM_REGION;              //9

	dwRegionAttr = 
		MPU_AP_FULL_ACCESS |
		MPU_REGION_EXECUTE_NEVER |
		SHAREABLE_DEVICE_TYPE |
		MPU_CalMPURegionSize(USBHSRAM_END_ADDRESS - USBHSRAM_START_ADDRESS) |
		MPU_REGION_ENABLE;

	MPU_SetRegion( dwRegionBaseAddr, dwRegionAttr);


	/* Enable the memory management fault , Bus Fault, Usage Fault exception */
	SCB->SHCSR |= (SCB_SHCSR_MEMFAULTENA_Msk | SCB_SHCSR_BUSFAULTENA_Msk
					| SCB_SHCSR_USGFAULTENA_Msk);

	/* Enable the MPU region */
	MPU_Enable( MPU_ENABLE | MPU_PRIVDEFENA);
	
	memory_sync();
}

#ifdef ENABLE_TCM

#if defined ( __ICCARM__ ) /* IAR Ewarm */
#pragma section = "CSTACK"
#pragma section = "CSTACK_DTCM"
	#define SRAM_STACK_BASE     (__section_begin("CSTACK"))
	#define DTCM_STACK_BASE     (__section_begin("CSTACK_DTCM"))
	#define SRAM_STACK_LIMIT    (__section_end("CSTACK"))
	#define DTCM_STACK_LIMIT    (__section_end("CSTACK_DTCM"))
#elif defined (__CC_ARM)  /* MDK */
	extern uint32_t Image$$ARM_LIB_STACK$$Base;
	extern uint32_t Image$$ARM_LIB_STACK$$ZI$$Limit;
	extern uint32_t Image$$DTCM_STACK$$Base;
	extern uint32_t Image$$DTCM_STACK$$ZI$$Limit;
	#define SRAM_STACK_BASE     (&Image$$ARM_LIB_STACK$$Base)
	#define DTCM_STACK_BASE     (&Image$$DTCM_STACK$$Base)
	#define SRAM_STACK_LIMIT    (&Image$$ARM_LIB_STACK$$ZI$$Limit)
	#define DTCM_STACK_LIMIT    (&Image$$DTCM_STACK$$ZI$$Limit)
#elif defined (  __GNUC__  )  /* GCC */
	extern char _sdtcm_stack, _edtcm_stack, _sstack, _estack;
	#define SRAM_STACK_BASE     ((void *)(&_sstack))
	#define DTCM_STACK_BASE     ((void *)(&_sdtcm_stack))
	#define SRAM_STACK_LIMIT    ((void *)(&_estack))
	#define DTCM_STACK_LIMIT    ((void *)(&_edtcm_stack))
#endif

/** \brief  Change stack's location to DTCM

	The function changes the stack's location from SRAM to DTCM
 */
void TCM_StackInit(void);
void TCM_StackInit(void)
{
	uint32_t offset = (uint32_t)SRAM_STACK_LIMIT - (uint32_t)DTCM_STACK_LIMIT;
	volatile char *dst = (volatile char *)DTCM_STACK_LIMIT;
	volatile char *src = (volatile char *)SRAM_STACK_LIMIT;
	/* copy code_TCM from flash to ITCM */
	while(src > (volatile char *)SRAM_STACK_BASE){
		*--dst = *--src;
	}
	__set_MSP(__get_MSP() - offset);
}

#endif


/**
 * \brief Performs the low-level initialization of the chip.
 */
extern WEAK void LowLevelInit( void )
{
  
	SystemInit(); 
#ifndef MPU_EXAMPLE_FEATURE
	_SetupMemoryRegion();
#endif
	
	
#if defined(ENABLE_TCM) && defined(__GNUC__)
	volatile char *dst = &_sitcm;
	volatile char *src = &_itcm_lma;
	/* copy code_TCM from flash to ITCM */
	while(dst < &_eitcm){
		*dst++ = *src++;
	}
#endif
}
