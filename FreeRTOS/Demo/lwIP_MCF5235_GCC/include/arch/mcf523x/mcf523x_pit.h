/*
 * These files are taken from the MCF523X source code example package
 * which is available on the Freescale website. Freescale explicitly 
 * grants the redistribution and modification of these source files.
 * The complete licensing information is available in the file 
 * LICENSE_FREESCALE.TXT.
 *
 * File:	mcf523x_pit.h
 * Purpose:	Register and bit definitions for the MCF523X
 *
 * Notes:	
 *	
 */

#ifndef __MCF523X_PIT_H__
#define __MCF523X_PIT_H__

/*********************************************************************
*
* Programmable Interrupt Timer Modules (PIT)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_PIT_PCSR0       (*(vuint16*)(void*)(&__IPSBAR[0x150000]))
#define MCF_PIT_PMR0        (*(vuint16*)(void*)(&__IPSBAR[0x150002]))
#define MCF_PIT_PCNTR0      (*(vuint16*)(void*)(&__IPSBAR[0x150004]))
#define MCF_PIT_PCSR1       (*(vuint16*)(void*)(&__IPSBAR[0x160000]))
#define MCF_PIT_PMR1        (*(vuint16*)(void*)(&__IPSBAR[0x160002]))
#define MCF_PIT_PCNTR1      (*(vuint16*)(void*)(&__IPSBAR[0x160004]))
#define MCF_PIT_PCSR2       (*(vuint16*)(void*)(&__IPSBAR[0x170000]))
#define MCF_PIT_PMR2        (*(vuint16*)(void*)(&__IPSBAR[0x170002]))
#define MCF_PIT_PCNTR2      (*(vuint16*)(void*)(&__IPSBAR[0x170004]))
#define MCF_PIT_PCSR3       (*(vuint16*)(void*)(&__IPSBAR[0x180000]))
#define MCF_PIT_PMR3        (*(vuint16*)(void*)(&__IPSBAR[0x180002]))
#define MCF_PIT_PCNTR3      (*(vuint16*)(void*)(&__IPSBAR[0x180004]))
#define MCF_PIT_PCSR(x)     (*(vuint16*)(void*)(&__IPSBAR[0x150000+((x)*0x10000)]))
#define MCF_PIT_PMR(x)      (*(vuint16*)(void*)(&__IPSBAR[0x150002+((x)*0x10000)]))
#define MCF_PIT_PCNTR(x)    (*(vuint16*)(void*)(&__IPSBAR[0x150004+((x)*0x10000)]))

/* Bit definitions and macros for MCF_PIT_PCSR */
#define MCF_PIT_PCSR_EN        (0x0001)
#define MCF_PIT_PCSR_RLD       (0x0002)
#define MCF_PIT_PCSR_PIF       (0x0004)
#define MCF_PIT_PCSR_PIE       (0x0008)
#define MCF_PIT_PCSR_OVW       (0x0010)
#define MCF_PIT_PCSR_HALTED    (0x0020)
#define MCF_PIT_PCSR_DOZE      (0x0040)
#define MCF_PIT_PCSR_PRE(x)    (((x)&0x000F)<<8)

/* Bit definitions and macros for MCF_PIT_PMR */
#define MCF_PIT_PMR_PM0        (0x0001)
#define MCF_PIT_PMR_PM1        (0x0002)
#define MCF_PIT_PMR_PM2        (0x0004)
#define MCF_PIT_PMR_PM3        (0x0008)
#define MCF_PIT_PMR_PM4        (0x0010)
#define MCF_PIT_PMR_PM5        (0x0020)
#define MCF_PIT_PMR_PM6        (0x0040)
#define MCF_PIT_PMR_PM7        (0x0080)
#define MCF_PIT_PMR_PM8        (0x0100)
#define MCF_PIT_PMR_PM9        (0x0200)
#define MCF_PIT_PMR_PM10       (0x0400)
#define MCF_PIT_PMR_PM11       (0x0800)
#define MCF_PIT_PMR_PM12       (0x1000)
#define MCF_PIT_PMR_PM13       (0x2000)
#define MCF_PIT_PMR_PM14       (0x4000)
#define MCF_PIT_PMR_PM15       (0x8000)

/* Bit definitions and macros for MCF_PIT_PCNTR */
#define MCF_PIT_PCNTR_PC0      (0x0001)
#define MCF_PIT_PCNTR_PC1      (0x0002)
#define MCF_PIT_PCNTR_PC2      (0x0004)
#define MCF_PIT_PCNTR_PC3      (0x0008)
#define MCF_PIT_PCNTR_PC4      (0x0010)
#define MCF_PIT_PCNTR_PC5      (0x0020)
#define MCF_PIT_PCNTR_PC6      (0x0040)
#define MCF_PIT_PCNTR_PC7      (0x0080)
#define MCF_PIT_PCNTR_PC8      (0x0100)
#define MCF_PIT_PCNTR_PC9      (0x0200)
#define MCF_PIT_PCNTR_PC10     (0x0400)
#define MCF_PIT_PCNTR_PC11     (0x0800)
#define MCF_PIT_PCNTR_PC12     (0x1000)
#define MCF_PIT_PCNTR_PC13     (0x2000)
#define MCF_PIT_PCNTR_PC14     (0x4000)
#define MCF_PIT_PCNTR_PC15     (0x8000)

/********************************************************************/

#endif /* __MCF523X_PIT_H__ */
