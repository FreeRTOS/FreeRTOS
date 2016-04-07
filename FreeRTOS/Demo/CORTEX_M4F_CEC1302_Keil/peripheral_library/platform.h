/****************************************************************************
* © 2013 Microchip Technology Inc. and its subsidiaries.
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
*/

/** @defgroup pwm pwm_c_wrapper
 *  @{
 */
/** @file pwm_c_wrapper.cpp
 \brief the pwm component C wrapper   
 This program is designed to allow the other C programs to be able to use this component

 There are entry points for all C wrapper API implementation

<b>Platform:</b> This is ARC-based component 

<b>Toolset:</b> Metaware IDE(8.5.1)
<b>Reference:</b> smsc_reusable_fw_requirement.doc */

/*******************************************************************************
 *  SMSC version control information (Perforce):
 *
 *  FILE:     $File: //depot_pcs/FWEng/Release/projects/CEC1302_CLIB/release2/Source/hw_blks/common/include/platform.h $
 *  REVISION: $Revision: #1 $
 *  DATETIME: $DateTime: 2015/12/23 15:37:58 $
 *  AUTHOR:   $Author: akrishnan $
 *
 *  Revision history (latest first):
 *      #xx
 ***********************************************************************************
 */

#ifndef _PLATFORM_H_
#define _PLATFORM_H_
#include <stdint.h>
/* Platform Configuration PreProcessor Conditions */
#define TOOLKEIL    1
#define TOOLPC      2
#define TOOLMW		3
#define TOOLMDK		4

#define PCLINT      9   //added to satisfy PC Lint's need for a value here

#ifdef __CC_ARM         // Keil ARM MDK
#define TOOLSET TOOLMDK
#endif

#if 0
#ifdef _WIN32           //always defined by visual c++
#define TOOLSET TOOLPC
#endif

#ifdef __WIN32__        //always defined by borland
#define TOOLSET TOOLPC
#endif
#endif


#ifdef _ARC
#define TOOLSET TOOLMW    // ARC Metaware
#endif

#ifndef TOOLSET
//#error "ERROR: cfg.h TOOLSET not defined!"
#endif

#if TOOLSET == TOOLMDK
#define _KEIL_ARM_  1   /* Make 1 for Keil MDK Compiler     */
#define _KEIL_  0       /* Make 1 for Keil Compiler     */
#define _PC_    0   
#define _ARC_CORE_	0
#endif

#if TOOLSET == TOOLKEIL
#define _KEIL_ARM_  0
#define _KEIL_  1   /* Make 1 for Keil Compiler     */
#define _PC_    0   
#define _ARC_CORE_	0
#endif

#if TOOLSET == TOOLPC
#define _KEIL_ARM_  0
#define _KEIL_  0   
#define _PC_    1 	/* Make 1 for PC Environment    */
#define _ARC_CORE_	0
#endif

#if TOOLSET == TOOLMW
#define _KEIL_ARM_  0
#define _KEIL_	0
#define _PC_	0
#define _ARC_CORE_	1
#endif

/* Short form for Standard Data Types */
typedef unsigned char           UINT8;
typedef unsigned short          UINT16;
typedef unsigned long           UINT32;

typedef volatile unsigned char  REG8;

typedef unsigned char           BYTE;
typedef unsigned short          WORD;
typedef unsigned long           DWORD;

typedef unsigned char           UCHAR;
typedef unsigned short          USHORT;
typedef unsigned long           ULONG;

typedef unsigned char           BOOL;
typedef unsigned int            UINT;

/* signed types */
typedef signed char             INT8;
typedef signed short            INT16;
typedef signed long             INT32;

typedef void                    VOID;

/* union types */
typedef union _BITS_8
{
    UINT8 byte;
    struct
    {
		UINT8 bit0: 1;
		UINT8 bit1: 1;
		UINT8 bit2: 1;
		UINT8 bit3: 1;
		UINT8 bit4: 1;
		UINT8 bit5: 1;
		UINT8 bit6: 1;
		UINT8 bit7: 1;
   }bit;
}BITS_8;


/* MACROS FOR Platform Portability */

/* macro for defining MMCR register */
/* add MMCRARRAY() & EXTERNMMCRARRAY() */
#if	_KEIL_
#define MMCR(name,address)      volatile unsigned char xdata name _at_ address
#define MMCRARRAY(name,length,address)  volatile unsigned char xdata name[length] _at_ address
#define MMCRTYPE(name,dtype,address) volatile dtype xdata name _at_ address
#define EXTERNMMCR(name)        extern volatile unsigned char xdata name
#define EXTERNMMCRARRAY(name)   extern volatile unsigned char xdata name[]
#define EXTERNMMCRTYPE(name,dtype) extern volatile dtype xdata name
#define SFR(name,address)       sfr name = address
#define SFRBIT(name,address)    sbit name = address
#define EXTERNSFR(name) 
#define BITADDRESSTYPE(name)    bit name
#define XDATA                   xdata
#define CODE                    code
#define DATA                    data
#define IDATA                   idata
#define INTERRUPT(x)            interrupt x
#define SET_GLOBAL_INTR_ENABLE()	(sfrIE_EAbit = TRUE;)
#define CLR_GLOBAL_INTR_ENABLE()	(sfrIE_EAbit = FALSE;)
#define NULLPTR						(char *)(0)
#define	PLATFORM_TRIM_OSC()			// TODO
#define PNOP() 
#define DISABLE_INTERRUPTS() sfrIE_EAbit=0
#define ENABLE_INTERRUPTS() sfrIE_EAbit=1
#define SAVE_DIS_INTERRUPTS(x) { x=sfrIE_EAbit; sfrIE_EAbit=0; }
#define RESTORE_INTERRUPTS(x) { sfrIE_EAbit=x; }
#define ATOMIC_CPU_SLEEP()
#define NUM_IRQ_VECTORS     12  // DW-8051
#define IRQ_VECTOR_SIZE     8 
#define USE_INLINE_PATCHER  1
#define IRQ_VECTABLE_IN_RAM 0
#define PLAT_ROM_IRQ_VECTOR_BASE 0x03  // ROM start
#define PLAT_IRQ_VECTOR_BASE 0x1003    // RAM start
#define FUNC_NEVER_RETURNS
#define BEGIN_SMALL_DATA_BLOCK(x)
#define END_SMALL_DATA_BLOCK()
UINT32 soft_norm(UINT32 val);
#define NORM(x) soft_norm(x)
//
#define USE_FUNC_REPLACEMENT    0
#endif

#if _PC_
#define MMCR(name,address)      volatile unsigned char name
#define MMCRARRAY(name,length,address)  volatile unsigned char name[length]
#define MMCRTYPE(name,dtype,address) volatile dtype name
#define EXTERNMMCR(name)        extern volatile unsigned char name
#define EXTERNMMCRARRAY(name)   extern volatile unsigned char name[]
#define EXTERNMMCRTYPE(name,dtype) extern volatile dtype name
#define SFR(name,address)       volatile unsigned char name
#define SFRBIT(name,address)    volatile unsigned char name
#define EXTERNSFR(name)         extern	volatile unsigned char name
#define BITADDRESSTYPE(name)    volatile unsigned char name
#define XDATA
#define CODE                
#define DATA
#define IDATA
#define INTERRUPT(x)
#define SET_GLOBAL_INTR_ENABLE()	(sfrIE_EAbit = TRUE;)
#define CLR_GLOBAL_INTR_ENABLE()	(sfrIE_EAbit = FALSE;)
#define NULLPTR						(char *)(0)
#define	PLATFORM_TRIM_OSC()			// TODO
#define PNOP() 
#define DISABLE_INTERRUPTS() 
#define ENABLE_INTERRUPTS()
#define SAVE_DIS_INTERRUPTS(x) 
#define RESTORE_INTERRUPTS(x) 
#define ATOMIC_CPU_SLEEP()
#define NUM_IRQ_VECTORS     24
#define IRQ_VECTOR_SIZE     8
#define USE_INLINE_PATCHER  1
#define IRQ_VECTABLE_IN_RAM 0
#define FUNC_NEVER_RETURNS
#define BEGIN_SMALL_DATA_BLOCK(x)
#define END_SMALL_DATA_BLOCK()
UINT32 soft_norm(UINT32 val);
#define NORM(x) soft_norm(x)
//
#define USE_FUNC_REPLACEMENT    0
#endif

#if _ARC_CORE_
// ARC C has no equivalent operator to specify address of a variable
// ARC MMCR's are 32-bit registers
#define MMCR(name,address)      volatile unsigned char name
#define MMCRARRAY(name,length,address)  volatile unsigned char name[length]
#define MMCRTYPE(name,dtype,address) volatile dtype name 
#define EXTERNMMCR(name)        extern volatile unsigned char name
#define EXTERNMMCRARRAY(name)   extern volatile unsigned char name[]
#define EXTERNMMCRTYPE(name,dtype) extern volatile dtype name
#define SFR(name,address)   volatile unsigned char name        
#define SFRBIT(name,address) volatile unsigned char name 
#define EXTERNSFR(name) extern volatile unsigned char name 
#define BITADDRESSTYPE(name) 
#define XDATA
#define CODE     
#define DATA
#define IDATA
#define INTERRUPT(x)
#define SET_GLOBAL_INTR_ENABLE()	(_enable())
#define CLR_GLOBAL_INTR_ENABLE()	(_disable())
#define NULLPTR						(char *)(0)
#define NULLVOIDPTR                 (void *)(0)
#define NULLFPTR					(void (*)(void))0
#define	PLATFORM_TRIM_OSC()			// TODO
#define PNOP() _nop()
#define DISABLE_INTERRUPTS() _disable()
#define ENABLE_INTERRUPTS() _enable()
#define SAVE_DIS_INTERRUPTS(x) { x=_lr(REG_STATUS32);_flag(x & ~(REG_STATUS32_E1_BIT | REG_STATUS32_E2_BIT));_nop(); }
#define RESTORE_INTERRUPTS(x) { _flag((_lr(REG_STATUS32) | (x & (REG_STATUS32_E1_BIT | REG_STATUS32_E2_BIT))));_nop(); }
#define ATOMIC_CPU_SLEEP() _flag(6);_sleep();_nop();_nop();
#define NUM_IRQ_VECTORS     24
#define IRQ_VECTOR_SIZE     8
#define USE_INLINE_PATCHER  0
#define DCCM_CODE_ALIAS_ADDR  0x00060000
#define PLAT_ROM_IRQ_VECTOR_BASE 0
#define PLAT_IRQ_VECTOR_BASE  (DCCM_CODE_ALIAS_ADDR)
/// y #define IRQ_VECTABLE_IN_RAM 1
#define IRQ_VECTABLE_IN_RAM 0
#define FUNC_NEVER_RETURNS  _CC(_NEVER_RETURNS)
#define BEGIN_SMALL_DATA_BLOCK(x)  #pragma Push_small_data(x)
#define END_SMALL_DATA_BLOCK()  #pragma Pop_small_data()
#define NORM(x) _norm(x)

#define INLINE_FUNCTION(x) #pragma On_inline(x)

//
#define USE_FUNC_REPLACEMENT    0
#endif

#if _KEIL_ARM_
// For ARM MDK compiler
// ARM MMCR's are 32-bit registers
#define MMCR(name,address)      volatile unsigned char name
#define MMCRARRAY(name,length,address)  volatile unsigned char name[length]
#define MMCRTYPE(name,dtype,address) volatile dtype name 
#define EXTERNMMCR(name)        extern volatile unsigned char name
#define EXTERNMMCRARRAY(name)   extern volatile unsigned char name[]
#define EXTERNMMCRTYPE(name,dtype) extern volatile dtype name
#define SFR(name,address)   volatile unsigned char name        
#define SFRBIT(name,address) volatile unsigned char name 
#define EXTERNSFR(name) extern volatile unsigned char name 
#define BITADDRESSTYPE(name) 
#define XDATA
#define CODE     
#define DATA
#define IDATA
#define INTERRUPT(x)
#define SET_GLOBAL_INTR_ENABLE()	(__enable_irq())
#define CLR_GLOBAL_INTR_ENABLE()	(__disable_irq())
#define NULLPTR						(char *)(0)
#define NULLVOIDPTR                 (void *)(0)
#define NULLFPTR					(void (*)(void))0
#define	PLATFORM_TRIM_OSC()			// TODO
#define PNOP() __NOP()
#define DISABLE_INTERRUPTS() __disable_irq()
#define ENABLE_INTERRUPTS() __enable_irq()
#define ATOMIC_CPU_SLEEP() __wfi();__nop();__nop();

#if 0 /* need further efforts if needed */
#define SAVE_DIS_INTERRUPTS(x) { x=_lr(REG_STATUS32);_flag(x & ~(REG_STATUS32_E1_BIT | REG_STATUS32_E2_BIT));_nop(); }
#define RESTORE_INTERRUPTS(x) { _flag((_lr(REG_STATUS32) | (x & (REG_STATUS32_E1_BIT | REG_STATUS32_E2_BIT))));_nop(); }
#define NUM_IRQ_VECTORS     24
#define IRQ_VECTOR_SIZE     8
#define USE_INLINE_PATCHER  0
#define DCCM_CODE_ALIAS_ADDR  0x00060000
#define PLAT_ROM_IRQ_VECTOR_BASE 0
#define PLAT_IRQ_VECTOR_BASE  (DCCM_CODE_ALIAS_ADDR)
/// y #define IRQ_VECTABLE_IN_RAM 1
#define IRQ_VECTABLE_IN_RAM 0
#define BEGIN_SMALL_DATA_BLOCK(x)  #pragma Push_small_data(x)
#define END_SMALL_DATA_BLOCK()  #pragma Pop_small_data()
#define INLINE_FUNCTION(x) #pragma On_inline(x)
#define USE_FUNC_REPLACEMENT    0
#endif

#if 0
#define FUNC_NEVER_RETURNS  _CC(_NEVER_RETURNS)
#define NORM(x) _norm(x)
#else
/* for ARM MDK */
#define FUNC_NEVER_RETURNS
UINT32 soft_norm(UINT32 val);
#define NORM(x) soft_norm(x)
#endif
#endif

/* General Constants */
#define FALSE   0x00
#define TRUE    !FALSE

#define BIT_n_MASK(n)	(1U << (n))
#define BIT_0_MASK    (1<<0)
#define BIT_1_MASK    (1<<1)
#define BIT_2_MASK    (1<<2)
#define BIT_3_MASK    (1<<3)
#define BIT_4_MASK    (1<<4)
#define BIT_5_MASK    (1<<5)
#define BIT_6_MASK    (1<<6)
#define BIT_7_MASK    (1<<7)
#define BIT_8_MASK    ((UINT16)1<<8)
#define BIT_9_MASK    ((UINT16)1<<9)
#define BIT_10_MASK   ((UINT16)1<<10)
#define BIT_11_MASK   ((UINT16)1<<11)
#define BIT_12_MASK   ((UINT16)1<<12)
#define BIT_13_MASK   ((UINT16)1<<13)
#define BIT_14_MASK   ((UINT16)1<<14)
#define BIT_15_MASK   ((UINT16)1<<15)
#define BIT_16_MASK     ((UINT32)1<<16)
#define BIT_17_MASK     ((UINT32)1<<17)
#define BIT_18_MASK     ((UINT32)1<<18)
#define BIT_19_MASK     ((UINT32)1<<19)
#define BIT_20_MASK     ((UINT32)1<<20)
#define BIT_21_MASK     ((UINT32)1<<21)
#define BIT_22_MASK     ((UINT32)1<<22)
#define BIT_23_MASK     ((UINT32)1<<23)
#define BIT_24_MASK     ((UINT32)1<<24)
#define BIT_25_MASK     ((UINT32)1<<25)
#define BIT_26_MASK     ((UINT32)1<<26)
#define BIT_27_MASK     ((UINT32)1<<27)
#define BIT_28_MASK     ((UINT32)1<<28)
#define BIT_29_MASK     ((UINT32)1<<29)
#define BIT_30_MASK     ((UINT32)1<<30)
#define BIT_31_MASK     ((UINT32)1<<31)


/* For CEC application  */
#define ON  1
#define OFF 0

#endif /*_PLATFORM_H_*/

/**   @}
 */

