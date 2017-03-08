/*****************************************************************************
* © 2015 Microchip Technology Inc. and its subsidiaries.
* You may use this software and any derivatives exclusively with
* Microchip products.
* THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS".
* NO WARRANTIES, WHETHER EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE,
* INCLUDING ANY IMPLIED WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY,
* AND FITNESS FOR A PARTICULAR PURPOSE, OR ITS INTERACTION WITH MICROCHIP
* PRODUCTS, COMBINATION WITH ANY OTHER PRODUCTS, OR USE IN ANY APPLICATION.
* IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
* INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
* WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
* BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE.
* TO THE FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL
* CLAIMS IN ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF
* FEES, IF ANY, THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
* MICROCHIP PROVIDES THIS SOFTWARE CONDITIONALLY UPON YOUR ACCEPTANCE
* OF THESE TERMS.
******************************************************************************

Version Control Information (Perforce)
******************************************************************************
$Revision: #1 $ 
$DateTime: 2016/09/22 08:03:49 $ 
$Author: pramans $
Last Change:	Updated for tabs
******************************************************************************/
/** @file pcr.h
* \brief Power, Clocks, and Resets Header file
* \author jvasanth
* 
* This file is the PCR header file  
******************************************************************************/

/** @defgroup PCR
 *  @{
 */

#ifndef _PCR_H
#define _PCR_H


/******************************************************************************/
/**  PCR Register IDS 
 *******************************************************************************/
enum _PCR_REGSET_ID_
{
	PCR_REG_SYSTEM_SLEEP_CTRL = 0,	
  PCR_REG_PROCESSOR_CLK_CTRL,	
	PCR_REG_SLOW_CLK_CTRL,
	PCR_REG_OSCILLATOR_ID,
	PCR_REG_PWR_RESET_STS,
	PCR_REG_PWR_RESET_CTRL,
	PCR_REG_SYSTEM_RESET,
	PCR_TEST0,
	PCR_TEST1,
	PCR_REG_EC_SLEEP_ENABLE_0 = 12,
	PCR_REG_EC_SLEEP_ENABLE_1,
	PCR_REG_EC_SLEEP_ENABLE_2,
	PCR_REG_EC_SLEEP_ENABLE_3,	
	PCR_REG_EC_SLEEP_ENABLE_4,	
	PCR_REG_EC_CLK_REQD_STS_0 = 20,
	PCR_REG_EC_CLK_REQD_STS_1,
	PCR_REG_EC_CLK_REQD_STS_2,
	PCR_REG_EC_CLK_REQD_STS_3,
	PCR_REG_EC_CLK_REQD_STS_4,
	PCR_REG_EC_RESET_ENABLE_0 = 28,
	PCR_REG_EC_RESET_ENABLE_1,
	PCR_REG_EC_RESET_ENABLE_2,
	PCR_REG_EC_RESET_ENABLE_3,
	PCR_REG_EC_RESET_ENABLE_4,
	
};
/* ---------------------------------------------------------------------- */

// Encode the Register ids for Sleep Enable, Clock Required, Reset Enable
//PCR register group 0 - EC 0
#define PCR0_REGS_EC		(((uint32_t)(PCR_REG_EC_SLEEP_ENABLE_0) & 0xFF) + \
							(((uint32_t)(PCR_REG_EC_CLK_REQD_STS_0) & 0xFF)<<8u) + \
							(((uint32_t)(PCR_REG_EC_RESET_ENABLE_0) & 0xFF)<<16u))

//PCR register group 1 - EC 1
#define PCR1_REGS_EC		(((uint32_t)(PCR_REG_EC_SLEEP_ENABLE_1) & 0xFF) + \
							(((uint32_t)(PCR_REG_EC_CLK_REQD_STS_1) & 0xFF)<<8u) + \
							(((uint32_t)(PCR_REG_EC_RESET_ENABLE_1) & 0xFF)<<16u))

//PCR register group 2 - EC 2
#define PCR2_REGS_EC		(((uint32_t)(PCR_REG_EC_SLEEP_ENABLE_2) & 0xFF) + \
							(((uint32_t)(PCR_REG_EC_CLK_REQD_STS_2) & 0xFF)<<8u) + \
							(((uint32_t)(PCR_REG_EC_RESET_ENABLE_2) & 0xFF)<<16u))

//PCR register group 3 - EC 3
#define PCR3_REGS_EC		(((uint32_t)(PCR_REG_EC_SLEEP_ENABLE_3) & 0xFF) + \
							(((uint32_t)(PCR_REG_EC_CLK_REQD_STS_3) & 0xFF)<<8u) + \
							(((uint32_t)(PCR_REG_EC_RESET_ENABLE_3) & 0xFF)<<16u))
							
//PCR register group 4 - EC 4
#define PCR4_REGS_EC		(((uint32_t)(PCR_REG_EC_SLEEP_ENABLE_4) & 0xFF) + \
							(((uint32_t)(PCR_REG_EC_CLK_REQD_STS_4) & 0xFF)<<8u) + \
							(((uint32_t)(PCR_REG_EC_RESET_ENABLE_4) & 0xFF)<<16u))
													
//PCR0_EC -> SLEEP_ENABLE, CLK REQD STS, RESET_ENABLE Bit Positions
#define PCR0_EC_JTAG_STAP_BITPOS     (0u)
#define PCR0_EC_EFUSE_BITPOS         (1u)
#define PCR0_EC_ISPI_BITPOS          (2u)

//PCR1_EC -> SLEEP_ENABLE, CLK REQD STS, RESET_ENABLE Bit Positions
#define PCR1_EC_INT_BITPOS           (0u)
#define PCR1_EC_PECI_BITPOS          (1u)
#define PCR1_EC_TACH0_BITPOS         (2u)
#define PCR1_EC_PWM0_BITPOS          (4u)
#define PCR1_EC_PMC_BITPOS           (5u)
#define PCR1_EC_DMA_BITPOS           (6u)
#define PCR1_EC_TFDP_BITPOS          (7u)
#define PCR1_EC_CPU_BITPOS           (8u)
#define PCR1_EC_WDT_BITPOS           (9u)
#define PCR1_EC_SMB0_BITPOS          (10u)
#define PCR1_EC_TACH1_BITPOS         (11u)
#define PCR1_EC_TACH2_BITPOS         (12u)
#define PCR1_EC_PWM1_BITPOS          (20u)
#define PCR1_EC_PWM2_BITPOS          (21u)
#define PCR1_EC_PWM3_BITPOS          (22u)
#define PCR1_EC_PWM4_BITPOS          (23u)
#define PCR1_EC_PWM5_BITPOS          (24u)
#define PCR1_EC_PWM6_BITPOS          (25u)
#define PCR1_EC_PWM7_BITPOS          (26u)
#define PCR1_EC_PWM8_BITPOS          (27u)
#define PCR1_EC_REG_BITPOS           (29u)
#define PCR1_EC_BTIMER0_BITPOS       (30u)
#define PCR1_EC_BTIMER1_BITPOS       (31u)

//PCR2_EC -> SLEEP_ENABLE, CLK REQD STS, RESET_ENABLE Bit Positions
#define PCR2_EC_LPC_BITPOS      		  (0u)
#define PCR2_EC_UART0_BITPOS    		  (1u)
#define PCR2_EC_UART1_BITPOS    		  (2u)
#define PCR2_EC_GLBL_CFG_BITPOS 		  (12u)
#define PCR2_EC_ACPI_EC0_BITPOS 		  (13u)
#define PCR2_EC_ACPI_EC1_BITPOS 		  (14u)
#define PCR2_EC_ACPI_PM1_BITPOS 		  (15u)
#define PCR2_EC_8042EM_BITPOS	  		  (16u)
#define PCR2_EC_MBOX_BITPOS 	  		  (17u)
#define PCR2_EC_RTC_BITPOS      		  (18u)
#define PCR2_EC_ESPI_BITPOS 	  		  (19u)
#define PCR2_EC_ACPI_EC_2_BITPOS 		  (21u)
#define PCR2_EC_ACPI_EC_3_BITPOS 		  (22u)
#define PCR2_EC_ACPI_EC_BITPOS 		    (23u)
#define PCR2_EC_PORT80_0_BITPOS 		  (25u)
#define PCR2_EC_PORT80_1_BITPOS 		  (26u)

//PCR3_EC -> SLEEP_ENABLE, CLK REQD STS, RESET_ENABLE Bit Positions
#define PCR3_EC_ADC_BITPOS      		   (3u)
#define PCR3_EC_PS2_0_BITPOS    		   (5u)
#define PCR3_EC_PS2_1_BITPOS    		   (6u)
#define PCR3_EC_PS2_2_BITPOS    		   (7u)
#define PCR3_EC_SPI0_BITPOS     		   (9u)
#define PCR3_EC_HTIMER_BITPOS   		   (10u)
#define PCR3_EC_KEYSCAN_BITPOS  		   (11u)
#define PCR3_EC_RPM_PWM_BITPOS  		   (12u)
#define PCR3_EC_SMB1_BITPOS     		   (13u)
#define PCR3_EC_SMB2_BITPOS     		   (14u)
#define PCR3_EC_SMB3_BITPOS     		   (15u)
#define PCR3_EC_LED0_BITPOS     		   (16u)
#define PCR3_EC_LED1_BITPOS     		   (17u)
#define PCR3_EC_LED2_BITPOS     		   (18u)
#define PCR3_EC_BCM_BITPOS      		   (19u)
#define PCR3_EC_SPI1_BITPOS     		   (20u)
#define PCR3_EC_BTIMER2_BITPOS  		   (21u)
#define PCR3_EC_BTIMER3_BITPOS  		   (22u)
#define PCR3_EC_BTIMER4_BITPOS  		   (23u)
#define PCR3_EC_BTIMER5_BITPOS  		   (24u)
#define PCR3_EC_LED3_BITPOS     		   (25u)
#define PCR3_EC_PKE_BITPOS     		     (26u)
#define PCR3_EC_RNG_BITPOS     		     (27u)
#define PCR3_EC_AES_BITPOS     		     (28u)
#define PCR3_EC_HTIMER_1_BITPOS 		   (29u)
#define PCR3_EC_C_C_TIMER_BITPOS		   (30u)
#define PCR3_EC_PWM9_BITPOS            (31u)


//PCR4_EC -> SLEEP_ENABLE, CLK REQD STS, RESET_ENABLE Bit Positions
#define PCR4_EC_PWM10_BITPOS      		 (0u)
#define PCR4_EC_PWM11_BITPOS      		 (1u)
#define PCR4_EC_CTIMER0_BITPOS   		   (2u)
#define PCR4_EC_CTIMER1_BITPOS   		   (3u)
#define PCR4_EC_CTIMER2_BITPOS   		   (4u)
#define PCR4_EC_CTIMER3_BITPOS   		   (5u)
#define PCR4_EC_RTOS_TIMER_BITPOS 		 (6u)
#define PCR4_EC_RPM2_PWM_BITPOS 		   (7u)
#define PCR4_EC_QMSPI_BITPOS  		     (8u)
#define PCR4_EC_BCM_1_BITPOS    		   (9u)
#define PCR4_EC_RC_ID0_BITPOS  		     (10u)
#define PCR4_EC_RC_ID1_BITPOS  		     (11u)
#define PCR4_EC_RC_ID2_BITPOS  		     (12u)
#define PCR4_EC_PROCHOT_BITPOS  		   (13u)
#define PCR4_EC_EEPROM_BITPOS  		     (14u)
#define PCR4_EC_CUST_LOG_BITPOS  		   (15u)


/*
 *  n = b[7:0]   = PCR Reg Bit Position
 *  m = b[31:8]  = PCRx Regs IDs
 */
//#define PCRx_REGS_BIT(m,n) ((((uint32_t)(m)&0xFFFFFFul)<<8u) + ((uint32_t)(n)&0xFFul)) 

//PCRx_REGS_BIT positions 													
#define	PCRx_REGS_POS_SLEEP_ENABLE				(8u)
#define	PCRx_REGS_POS_CLK_REQD_STS				(16u)
#define	PCRx_REGS_POS_RESET_ENABLE				(24u)													


/******************************************************************************/
/**  PCR Block IDS. 
 * These IDs are used to directly refer to a block 
 *******************************************************************************/
typedef enum {
	PCR_JTAG			= (((uint32_t)(PCR0_REGS_EC) << 8) + (uint32_t)(PCR0_EC_JTAG_STAP_BITPOS & 0xFFu)),
	PCR_EFUSE			= (((uint32_t)(PCR0_REGS_EC) << 8) + (uint32_t)(PCR0_EC_EFUSE_BITPOS & 0xFFu)),
  PCR_ISPI			= (((uint32_t)(PCR0_REGS_EC) << 8) + (uint32_t)(PCR0_EC_ISPI_BITPOS & 0xFFu)),
	
	PCR_INT				= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_INT_BITPOS & 0xFFu)),  	
	PCR_PECI			= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_PECI_BITPOS & 0xFFu)), 	
	PCR_TACH0			= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_TACH0_BITPOS & 0xFFu)), 	
	PCR_PWM0			= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_PWM0_BITPOS & 0xFFu)),  	
	PCR_PMC				= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_PMC_BITPOS & 0xFFu)),   	
	PCR_DMA				= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_DMA_BITPOS & 0xFFu)),  	
	PCR_TFDP			= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_TFDP_BITPOS & 0xFFu)),  	
	PCR_CPU				= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_CPU_BITPOS & 0xFFu)),   	
	PCR_WDT				= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_WDT_BITPOS & 0xFFu)),   	
	PCR_SMB0			= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_SMB0_BITPOS & 0xFFu)), 	
	PCR_TACH1			= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_TACH1_BITPOS & 0xFFu)),
	PCR_TACH2			= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_TACH2_BITPOS & 0xFFu)), 	
	PCR_PWM1			= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_PWM1_BITPOS & 0xFFu)),  	
	PCR_PWM2			= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_PWM2_BITPOS & 0xFFu)),  	
	PCR_PWM3			= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_PWM3_BITPOS & 0xFFu)),  	
	PCR_PWM4			= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_PWM4_BITPOS & 0xFFu)),  	
	PCR_PWM5			= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_PWM5_BITPOS & 0xFFu)),  	
	PCR_PWM6			= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_PWM6_BITPOS & 0xFFu)),  	
	PCR_PWM7			= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_PWM7_BITPOS & 0xFFu)),  	
	PCR_PWM8			= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_PWM8_BITPOS & 0xFFu)),  	
	PCR_REG				= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_REG_BITPOS & 0xFFu)),   	
	PCR_BTIMER0		= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_BTIMER0_BITPOS & 0xFFu)),	
	PCR_BTIMER1		= (((uint32_t)(PCR1_REGS_EC) << 8) + (uint32_t)(PCR1_EC_BTIMER1_BITPOS & 0xFFu)),	
	
	PCR_LPC				= (((uint32_t)(PCR2_REGS_EC) << 8) + (uint32_t)(PCR2_EC_LPC_BITPOS & 0xFFu)),
	PCR_UART0			= (((uint32_t)(PCR2_REGS_EC) << 8) + (uint32_t)(PCR2_EC_UART0_BITPOS & 0xFFu)),
	PCR_UART1			= (((uint32_t)(PCR2_REGS_EC) << 8) + (uint32_t)(PCR2_EC_UART1_BITPOS & 0xFFu)),
	PCR_GLBL_CFG	= (((uint32_t)(PCR2_REGS_EC) << 8) + (uint32_t)(PCR2_EC_GLBL_CFG_BITPOS & 0xFFu)),
	PCR_ACPI_EC0	= (((uint32_t)(PCR2_REGS_EC) << 8) + (uint32_t)(PCR2_EC_ACPI_EC0_BITPOS & 0xFFu)),
	PCR_ACPI_EC1	= (((uint32_t)(PCR2_REGS_EC) << 8) + (uint32_t)(PCR2_EC_ACPI_EC1_BITPOS & 0xFFu)),
	PCR_ACPI_PM1	= (((uint32_t)(PCR2_REGS_EC) << 8) + (uint32_t)(PCR2_EC_ACPI_PM1_BITPOS & 0xFFu)),
	PCR_8042EM		= (((uint32_t)(PCR2_REGS_EC) << 8) + (uint32_t)(PCR2_EC_8042EM_BITPOS & 0xFFu)),
	PCR_MBOX  		= (((uint32_t)(PCR2_REGS_EC) << 8) + (uint32_t)(PCR2_EC_MBOX_BITPOS & 0xFFu)),
	PCR_RTC				= (((uint32_t)(PCR2_REGS_EC) << 8) + (uint32_t)(PCR2_EC_RTC_BITPOS & 0xFFu)),
	PCR_ESPI			= (((uint32_t)(PCR2_REGS_EC) << 8) + (uint32_t)(PCR2_EC_ESPI_BITPOS & 0xFFu)),
	PCR_ACPI_EC2	= (((uint32_t)(PCR2_REGS_EC) << 8) + (uint32_t)(PCR2_EC_ACPI_EC_2_BITPOS & 0xFFu)),
	PCR_ACPI_EC3	= (((uint32_t)(PCR2_REGS_EC) << 8) + (uint32_t)(PCR2_EC_ACPI_EC_3_BITPOS & 0xFFu)),
	PCR_ACPI_EC	  = (((uint32_t)(PCR2_REGS_EC) << 8) + (uint32_t)(PCR2_EC_ACPI_EC_BITPOS & 0xFFu)),
	PCR_PORT80_0  = (((uint32_t)(PCR2_REGS_EC) << 8) + (uint32_t)(PCR2_EC_PORT80_0_BITPOS & 0xFFu)),
	PCR_PORT80_1  = (((uint32_t)(PCR2_REGS_EC) << 8) + (uint32_t)(PCR2_EC_PORT80_1_BITPOS & 0xFFu)),
		
	PCR_ADC				= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_ADC_BITPOS & 0xFFu)),
	PCR_PS2_0			= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_PS2_0_BITPOS & 0xFFu)),    	
	PCR_PS2_1			= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_PS2_1_BITPOS & 0xFFu)),    	
	PCR_PS2_2			= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_PS2_2_BITPOS & 0xFFu)),    		
	PCR_SPI0			= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_SPI0_BITPOS & 0xFFu)),     	
	PCR_HTIMER		= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_HTIMER_BITPOS & 0xFFu)),      	
	PCR_KEYSCAN		= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_KEYSCAN_BITPOS & 0xFFu)),      	
	PCR_RPM_PWM		= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_RPM_PWM_BITPOS & 0xFFu)),      	
	PCR_SMB1			= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_SMB1_BITPOS & 0xFFu)),     	
	PCR_SMB2			= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_SMB2_BITPOS & 0xFFu)),    	
	PCR_SMB3			= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_SMB3_BITPOS & 0xFFu)),     	
	PCR_LED0			= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_LED0_BITPOS & 0xFFu)),     	
	PCR_LED1			= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_LED1_BITPOS & 0xFFu)),     	
	PCR_LED2			= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_LED2_BITPOS & 0xFFu)),     	
	PCR_BCM				= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_BCM_BITPOS & 0xFFu)),   
	PCR_SPI1			= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_SPI1_BITPOS & 0xFFu)),     	
	PCR_BTIMER2		= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_BTIMER2_BITPOS & 0xFFu)),   	
	PCR_BTIMER3		= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_BTIMER3_BITPOS & 0xFFu)),   	
	PCR_BTIMER4		= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_BTIMER4_BITPOS & 0xFFu)),   	
	PCR_BTIMER5		= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_BTIMER5_BITPOS & 0xFFu)),   	
	PCR_LED3			= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_LED3_BITPOS & 0xFFu)),	
	PCR_PKE 			= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_PKE_BITPOS & 0xFFu)),	
	PCR_RNG 			= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_RNG_BITPOS & 0xFFu)),	
	PCR_AES 			= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_AES_BITPOS & 0xFFu)),	
	PCR_HTIMER_1	= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_HTIMER_1_BITPOS & 0xFFu)),      	
	PCR_C_C_TIMER	= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_C_C_TIMER_BITPOS & 0xFFu)),      	
	PCR_PWM9  		= (((uint32_t)(PCR3_REGS_EC) << 8) + (uint32_t)(PCR3_EC_PWM9_BITPOS & 0xFFu)),
	
  PCR_PWM10  		= (((uint32_t)(PCR4_REGS_EC) << 8) + (uint32_t)(PCR4_EC_PWM10_BITPOS & 0xFFu)),      		
	PCR_PWM11  		= (((uint32_t)(PCR4_REGS_EC) << 8) + (uint32_t)(PCR4_EC_PWM11_BITPOS & 0xFFu)),      		
	PCR_CTIMER0 	= (((uint32_t)(PCR4_REGS_EC) << 8) + (uint32_t)(PCR4_EC_CTIMER0_BITPOS & 0xFFu)),      		
	PCR_CTIMER1 	= (((uint32_t)(PCR4_REGS_EC) << 8) + (uint32_t)(PCR4_EC_CTIMER1_BITPOS & 0xFFu)), 
	PCR_CTIMER2 	= (((uint32_t)(PCR4_REGS_EC) << 8) + (uint32_t)(PCR4_EC_CTIMER2_BITPOS & 0xFFu)), 
	PCR_CTIMER3 	= (((uint32_t)(PCR4_REGS_EC) << 8) + (uint32_t)(PCR4_EC_CTIMER3_BITPOS & 0xFFu)), 
	PCR_RTOS_TIMER = (((uint32_t)(PCR4_REGS_EC) << 8) + (uint32_t)(PCR4_EC_RTOS_TIMER_BITPOS & 0xFFu)), 
	PCR_RPM2_PWM	= (((uint32_t)(PCR4_REGS_EC) << 8) + (uint32_t)(PCR4_EC_RPM2_PWM_BITPOS & 0xFFu)),      	
	PCR_QMSPI	    = (((uint32_t)(PCR4_REGS_EC) << 8) + (uint32_t)(PCR4_EC_QMSPI_BITPOS & 0xFFu)),      	
	PCR_BCM1    	= (((uint32_t)(PCR4_REGS_EC) << 8) + (uint32_t)(PCR4_EC_BCM_1_BITPOS & 0xFFu)),      	
	PCR_RCID0    	= (((uint32_t)(PCR4_REGS_EC) << 8) + (uint32_t)(PCR4_EC_RC_ID0_BITPOS & 0xFFu)),      	
	PCR_RCID1    	= (((uint32_t)(PCR4_REGS_EC) << 8) + (uint32_t)(PCR4_EC_RC_ID1_BITPOS & 0xFFu)),      	
	PCR_RCID2    	= (((uint32_t)(PCR4_REGS_EC) << 8) + (uint32_t)(PCR4_EC_RC_ID2_BITPOS & 0xFFu)),      	
	PCR_PROCHOT  	= (((uint32_t)(PCR4_REGS_EC) << 8) + (uint32_t)(PCR4_EC_PROCHOT_BITPOS & 0xFFu)),      	
	PCR_EEPROM   	= (((uint32_t)(PCR4_REGS_EC) << 8) + (uint32_t)(PCR4_EC_EEPROM_BITPOS & 0xFFu)),      	
	PCR_CUST_LOG 	= (((uint32_t)(PCR4_REGS_EC) << 8) + (uint32_t)(PCR4_EC_CUST_LOG_BITPOS & 0xFFu)),      	
} PCR_BLK_ID;


/******************************************************************************/
/**  PCR Processor ClK Divide Values 
 *******************************************************************************/
enum PROCESSOR_CLK_DIVIDE_VALUE
{
	PCR_CPU_CLK_DIVIDE_1 = 1,
	PCR_CPU_CLK_DIVIDE_2 = 2,
	PCR_CPU_CLK_DIVIDE_3 = 3,
	PCR_CPU_CLK_DIVIDE_4 = 4,
	PCR_CPU_CLK_DIVIDE_16 = 16,
	PCR_CPU_CLK_DIVIDE_48 = 48	
};

/******************************************************************************/
/**  System Sleep Modes 
 *******************************************************************************/
enum SYSTEM_SLEEP_MODES
{
	SYSTEM_LIGHT_SLEEP = 0,	
	SYSTEM_HEAVY_SLEEP = 1,
	SYSTEM_SLEEP_ALL = 4
};

/* Bitmask for Power Reset Status Register */
#define PCR_PWR_RESET_STS_VCC_PWRGD_RESET_STS_BITMASK	(1UL<<2)
#define PCR_PWR_RESET_STS_HOST_RESET_STS_BITMASK			(1UL<<3)
#define PCR_PWR_RESET_STS_VBAT_RESET_STS_BITMASK			(1UL<<5)
#define PCR_PWR_RESET_STS_VTR_RESET_STS_BITMASK			  (1UL<<6)
#define PCR_PWR_RESET_STS_JTAG_RESET_STS_BITMASK		  (1UL<<7)
#define PCR_PWR_RESET_STS_32K_ACTIVE_STS_BITMASK			(1UL<<10)
#define PCR_PWR_RESET_STS_PCICLK_ACTIVE_STS_BITMASK		(1UL<<11)
#define PCR_PWR_RESET_STS_ESPICLK_ACTIVE_STS_BITMASK		(1UL<<12)

/* Bitmask for Processor Clock Control Register */
#define PCR_OSCILLATOR_LOCK_STATUS_BITMASK					(1UL<<8)

/* Bitmask for Power Reset Control Register */
#define PCR_PWR_RESET_CTRL_PWR_INV_BITMASK               (1UL<<0)
#define PCR_PWR_RESET_CTRL_HOST_RST_SELECT_BITMASK       (1UL<<8)

/* Bitmask for OScillator ID register */
#define PCR_OSCILLATOR_ID_FOUNDARY_BITMASK          (3UL<<5)
#define PCR_OSCILLATOR_ID_REVISION_BITMASK          (0xFUL)

#define PCR_OSCILLATOR_ID_FOUNDARY_CHART_TSMC        (0UL)
#define PCR_OSCILLATOR_ID_FOUNDARY_TSMC              (0x10u)
#define PCR_OSCILLATOR_ID_FOUNDARY_CHART             (0x20u)
#define PCR_OSCILLATOR_ID_FOUNDARY_GRACE             (0x30u)

/* Bitmask for PKE Clock register */
#define PCR_PKE_CLOCK_REG_PKE_CLK_BITMASK         (1UL<<1)
#define PCR_PKE_CLOCK_REG_AUTO_SWITCH_BITMASK     (1UL<<0)

#define PCR_PKE_CLOCK_REG_PKE_CLK_48MHZ           (1UL<<1)
#define PCR_PKE_CLOCK_REG_PKE_CLK_96MHZ           (0UL<<0)
#define PCR_PKE_CLOCK_REG_AUTO_SWITCH_EN          (1UL<<0)
#define PCR_PKE_CLOCK_REG_AUTO_SWITCH_DIS         (0UL<<0)

/* ---------------------------------------------------------------------- */
/*  API - Functions to program Sleep Enable, CLK Reqd Status,             *
 *  Reset Enable for a block                                              *
 * ---------------------------------------------------------------------- */
 /** Sets or Clears block specific bit in PCR Sleep Enable Register
 * @param pcr_block_id - pcr block id encoded using PCRx_REGS_BIT 
 * @param set_clr_flag - Flag to set (1) or clear (0) bit in the PCR Sleep Enable Register
 */
void pcr_sleep_enable(uint32_t pcr_block_id, uint8_t set_clr_flag);

/** Get Clock Required Status for the block
 * @param pcr_block_id - pcr block id encoded using PCRx_REGS_BIT 
 * @return uint8_t - 1 if Clock Required Status set, else 0
 */
uint8_t pcr_clock_reqd_status_get(uint32_t pcr_block_id);

/** Sets or Clears Reset Enable register bit for the block
 * @param pcr_block_id - pcr block id encoded using PCRx_REGS_BIT 
 * @param set_clr_flag - Flag to set (1) or clear (0) bit in the PCR Reset Enable Register
 */
void pcr_reset_enable(uint32_t pcr_block_id, uint8_t set_clr_flag);

/* ---------------------------------------------------------------------- */
/*  API -   Functions for entering low power modes                        */
/* ---------------------------------------------------------------------- */
/** Instructs all blocks to sleep by setting the Sleep Enable bits */
void pcr_all_blocks_sleep(void);

/** Clears the Sleep Enable bits for all blocks */
void pcr_all_blocks_wake(void);

/** Programs required sleep mode in System Sleep Control Register
 * @param sleep_mode - see enum SYSTEM_SLEEP_MODES
 */
void pcr_system_sleep(uint8_t sleep_mode);

/** Reads the value of Power Reset status register
 * @param none
 * @return Power Status Reg value
 */
uint16_t pcr_power_reset_status_read(void);

/** Reads the value of Power Reset control register
 * @param none
 * @return Power reset control Reg value
 */
uint16_t pcr_power_reset_ctrl_read(void);

/** Sets the value of PWR_INV bit to 1 or 0
* @param set_clr: 1 or 0
 * @return none
 */
void pcr_pwr_reset_ctrl_pwr_inv_set_clr(uint8_t set_clr);

/** Sets the value of HOST_RESET bit to 1 or 0
* @param set_clr: 1 or 0
 * @return none
 */
void pcr_pwr_reset_ctrl_host_rst_set_clr(uint8_t set_clr);

/** Sets the SOFT SYS RESET bit to 1
* @param none
 * @return none
 */
void pcr_system_reset_set(void);

/** Writes to the PKE Clock register
* @param clock value
 * @return none
 */
void pcr_pke_clock_write(uint8_t pke_clk_val);

/** Reads the PKE clock register
* @param none
 * @return clock value
 */
uint8_t pcr_pke_clock_read(void);

/** Writes to the OSC cal register
* @param calibration value: 1 or 0
 * @return none
 */
void pcr_osc_cal_write(uint8_t pke_clk_val);

/** Reads the osc cal register
* @param none
 * @return cal value
 */
uint8_t pcr_osc_cal_read(void);


/* ---------------------------------------------------------------------- */
/* Peripheral Function - Functions to program and read 32-bit values      *
 * from PCR Registers                                                     *
 * ---------------------------------------------------------------------- */
 /** Write 32-bit value in the PCR Register
 * @param pcr_reg_id - pcr register id 
 * @param value - 32-bit value
 */
void p_pcr_reg_write(uint8_t pcr_reg_id, uint32_t value);

/** Reads 32-bit value from the PCR Register
 * @param pcr_reg_id - pcr register id 
 * @return value - 32-bit value
 */
uint32_t p_pcr_reg_read(uint8_t pcr_reg_id);

/* ---------------------------------------------------------------------- */
/* Peripheral Function - Functions to set, clr and get bits in            *
 * PCR Registers                                                          * 
 * ---------------------------------------------------------------------- */
 /** Sets bits in a PCR Register
 * @param pcr_reg_id - pcr register id 
 * @param bit_mask - Bit mask of bits to set 
 */
void p_pcr_reg_set(uint8_t pcr_reg_id, uint32_t bit_mask);

/** Clears bits in a PCR Register
 * @param pcr_reg_id - pcr register id 
 * @param bit_mask - Bit mask of bits to clear 
 */
void p_pcr_reg_clr(uint8_t pcr_reg_id, uint32_t bit_mask);

/** Read bits in a PCR Register
 * @param pcr_reg_id - pcr register id 
 * @param bit_mask - Bit mask of bits to read 
 * @return value - 32-bit value
 */
uint32_t p_pcr_reg_get(uint8_t pcr_reg_id, uint32_t bit_mask);

/** Sets or Clears bits in a PCR Register - Helper Function
 * @param pcr_reg_id - pcr register id 
 * @param bit_mask - Bit mask of bits to set or clear
 * @param set_clr_flag - Flag to set (1) or clear (0) bits in the PCR Register
 */
void p_pcr_reg_update(uint8_t pcr_reg_id, uint32_t bit_mask, uint8_t set_clr_flag);
	
//Functions to operate on System Sleep Control Register	

/* ---------------------------------------------------------------------- */
/* Peripheral Function - Functions to operate on System Sleep Control     *
 * Register                                                               * 
 * ---------------------------------------------------------------------- */
/** Writes required sleep mode in System Sleep Control Register
 * @param sleep_value - System Sleep control value - [D2, D1, D0]
 */
void p_pcr_system_sleep_ctrl_write(uint8_t sleep_value);

/** Reads the System Sleep Control PCR Register
 * @return value - byte 0 of the system sleep control PCR register
 */
uint8_t p_pcr_system_sleep_ctrl_read(void);

/* ---------------------------------------------------------------------- */
/* Peripheral Function - Function to program to CLK Divide Value          * 
 * ---------------------------------------------------------------------- */
 /** Writes the clock divide value in the Processor Clock Control Register
 * @param clk_divide_value - clk divide values, valid values in enum PROCESSOR_CLK_DIVIDE_VALUE
 */
void p_pcr_processor_clk_ctrl_write(uint8_t clk_divide_value);

/* ---------------------------------------------------------------------- */
/* Peripheral Function - Function to program the Slow Clock Control       *
 * Register                                                               *
 * ---------------------------------------------------------------------- */
 /** Write the slow clock divide value in the Slow Clock Control Register
 * @param slow_clk_divide_value - slow clk divide value
 */
void p_pcr_slow_clk_ctrl_write(uint16_t slow_clk_divide_value);

/* ---------------------------------------------------------------------- */
/* Peripheral Function - Function to read the Oscillator Lock Status      */ 
/* ---------------------------------------------------------------------- */
/** Reads the Oscillator Lock status bit in the Oscillator ID Register
 * @return 1 if Oscillator Lock Status bit is set, else 0
 */
uint8_t p_pcr_oscillator_lock_sts_get(void);

/** Reads the Oscillator ID Register
 * @return oscillator ID value
 */
uint16_t p_pcr_oscillator_id_reg_read(void);

/* ---------------------------------------------------------------------- */
/* Peripheral Function - Functions to read various power status in        *
 * Power Reset register                                               *
 * ---------------------------------------------------------------------- */
 /** Reads the VCC Reset Status bit 
 *        in the Power Reset Status Register
 * @return 1 if VCC Reset Status bit is set, else 0
 */
uint8_t p_pcr_pwr_reset_vcc_reset_sts_get(void);

/** Reads the Host Reset Status bit 
 *        in the Power Reset Status Register
 * @return 1 if Host Reset Status bit is set, else 0
 */
uint8_t p_pcr_pwr_reset_host_reset_sts_get(void);

/** Reads the VBAT Reset Status bit 
 *        in the Power Reset Status Register
 * @return 1 if VBAT Reset Status bit is set, else 0
 */
uint8_t p_pcr_pwr_reset_vbat_reset_sts_get(void);

/** Clears the VBAT Reset Status bit 
 *        in the Power Reset Status Register 
 */
void p_pcr_pwr_reset_vbat_reset_sts_clr(void);

/** Reads the VTR Reset Status bit 
 *        in the Power Reset Status Register
 * @return 1 if VCC1 Reset Status bit is set, else 0
 */
uint8_t p_pcr_pwr_reset_vtr_reset_sts_get(void);

/** Clears the VTR Reset Status bit 
 *        in the Power Reset Status Register 
 */
void p_pcr_chip_subsystem_vtr_reset_sts_clr(void);

/** Reads the 32K_ACTIVE status bit 
 *        in the Chip Subsystem Power Reset Status Register
 * @return 1 if 32_ACTIVE bit is set, else 0
 */
uint8_t p_pcr_pwr_reset_32K_active_sts_get(void);

/** Reads the PCICLK_ACTIVE status bit 
 *        in the Power Reset Status Register
 * @return 1 if CICLK_ACTIVE bit is set, else 0
 */
uint8_t p_pcr_pwr_reset_pciclk_active_sts_get(void);

/** Reads the ESPICLK_ACTIVE status bit 
 *        in the Power Reset Status Register
 * @return 1 if ESPICLK_ACTIVE bit is set, else 0
 */
uint8_t p_pcr_pwr_reset_espiclk_active_sts_get(void);

/** Reads the Power status reg
 * @return Power Status Reg value
 */
uint16_t p_pcr_pwr_reset_sts_get(void);

/* ---------------------------------------------------------------------- */
/* Peripheral Function - Functions for Power Reset Control Register       */ 
/* ---------------------------------------------------------------------- */

/** Reads the Power Reset Control Register
 * @return Power Reset Control Register value
 */
uint16_t p_pcr_pwr_reset_ctrl_read(void);

/** Set the PWR_INV bit in the Power Reset Control Register
 * @param set_clr value 1 or 0
 * @return none
 */
void p_pcr_pwr_reset_ctrl_pwr_inv_set_clr(uint8_t set_clr);

/** Set the HOST RESET SELECT bit in the Power Reset Control Register
 * @param set_clr value 1 or 0
 * @return none
 */
void p_pcr_pwr_reset_ctrl_host_rst_set_clr(uint8_t set_clr);

/* ---------------------------------------------------------------------- */
/* Peripheral Function - Functions for System Reset Register       */ 
/* ---------------------------------------------------------------------- */
/** Set the SOFT_SYS_RESET bit in the System Reset Register
 * @param none
 * @return none
 */
void p_pcr_system_reset_set(void);


/** Set the value in PKE CLOCK Register
 * @param PKE Clock value 
 * @return none
 */
void p_pcr_pke_clock_write(uint8_t pke_clk_val);

/** Read the value in PKE CLOCK Register
 * @none 
 * @return PKE Clock value 
 */
uint8_t p_pcr_pke_clock_read(void);

/** Set the value in Oscillator calibration Register
 * @param Oscillator calibration value 
 * @return none
 */
void p_pcr_osc_cal_write(uint8_t osc_cal_val);

/** Read the value in Osc cal Register
 * @none 
 * @return Osc cal value 
 */
uint8_t p_pcr_osc_cal_read(void);

#endif // #ifndef _PCR_H
/* end pcr.h */
/**   @}
 */



