/*****************************************************************************
* Copyright 2014 Microchip Technology Inc. and its subsidiaries.
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
*****************************************************************************/

/** @file appcfg.h
 *MEC14xx build configuration
 */
/** @defgroup common
 */

#ifndef _APPCFG_H
#define _APPCFG_H

#define ADISABLE     (0)
#define AENABLE      (1)

#define FALSE       (0)
#define TRUE        (1)

#define OFF         (0)
#define ON          (1)

/*
 * Choose MEC1404 or MEC1418 Device
 */
#define MEC1403_DEVID   (0x00011000) /* Code 96KB, 84-pin */
#define MEC1404_DEVID   (0x00021000) /* Code 96KB, 128-pin */
#define MEC1405_DEVID   (0x00031000) /* Code 128KB 84-pin */
#define MEC1406_DEVID   (0x00041000) /* Code 128KB 128-pin */
#define MEC1407_DEVID   (0x00051000) /* Code 160KB 84-pin */
#define MEC1408_DEVID   (0x00061000) /* Code 160KB 128-pin */
#define MEC1413_DEVID   (0x00071000) /* Code 96KB 84-pin */
#define MEC1414_DEVID   (0x00081000) /* Code 96KB 128-pin */
#define MEC1415_DEVID   (0x00091000) /* Code 128KB 84-pin */
#define MEC1416_DEVID   (0x000A1000) /* Code 128KB 128-pin */
#define MEC1417_DEVID   (0x000B1000) /* Code 160KB 84-pin */
#define MEC1418_DEVID   (0x000C1000) /* Code 160KB 128-pin */

#define MEC14XX_DEVID   (MEC1404_DEVID)

/*
 * MEC14xx Power-Control-Reset Processor clock divider value
 * MIPS M14K Processor clock = Chip_Input_Clock / PCR_PROC_CLK_DIV
 * MEC14xx POR PCR Processor Clock divider = 4
 *
 * Silicon Chip_Input_Clock = 48MHz
 *
 */
#define PCR_CLOCK_DIVIDER      (1)


// GPIO_0102/KSO9 0102(octal)=0x42. 
#define CR_STRAP_GPIO       (0x42ul)
#define CR_STRAP_GPIO_BANK  (2u)
#define CR_STRAP_BITPOS     (2u)

/* GPIO_0123 0:[0,37], 1:[40,77], 2:[100,137], 3:[140,177], 4[200,237] */
#define SPI0_CS0_REG_IDX     (0x53u)
#define SPI0_CS0_GPIO_BANK  (2ul)
#define SPI0_CS0_BITPOS     (19u)
/* GPIO_0015 0:[0,37], 1:[40,77], 2:[100,137], 3:[140,177], 4[200,237] */
#define SPI1_CS0_REG_IDX     (0x0Du)
#define SPI1_CS0_GPIO_BANK  (0ul)
#define SPI1_CS0_BITPOS     (13u)


/* 
 * ASIC at full speed (48MHz)
 * M14K CP0 Counter increments at 1/2 CPU core clock.
 */
#define M14K_TIMER_COMPARE_2SEC (0x00B71B00ul)
#define M14K_TIMER_COMPARE_1SEC (0x005B8D80ul)
#define M14K_TIMER_COMPARE_10MS (0x0000EA60ul)
#define M14K_TIMER_COMPARE (M14K_TIMER_COMPARE_2SEC)

/* 16-bit Timer 0 */
// Prescale value for 10KHz tick rate
#define BASIC_TIMER0_PRESCALE_10KHZ_ASIC    (4799ul)
#define BASIC_TIMER0_PRESCALE_1KHZ_ASIC     (47999ul)
// Preload/Count value for 1.733 seconds
#define BASIC_TIMER0_PRESCALE            (BASIC_TIMER0_PRESCALE_1KHZ_ASIC)
#define BASIC_TIMER0_PRELOAD             (2000ul)

/* RTOS Timer (32KHz) */
#define RTOS_TIMER_COUNT_10MS           (328ul)


/*
 * Enable check of GPIO access in mec14xx_gpio module
 */
#define ENABLE_GPIO_PIN_VALIDATION

/*
 * Enable check of Basic Timer ID in API calls
 */
#define MEC14XX_BTIMER_CHECK_ID

/*
 * Enable GPIO Pin Debug 
 */
//#define DEBUG_GPIO_PIN

/* 
 * Enable TFDP TRACE 
 */
#define ENABLE_TFDP_TRACE

/*
 * Use C-library printf for TFDP Trace
 *
#define ENABLE_TRACE_HOST_LINK
*/

/*
 * Delay between writes to TFDP data register
 */
#define TFDP_DELAY()

#endif // #ifndef _APPCFG_H
/**   @}
 */
