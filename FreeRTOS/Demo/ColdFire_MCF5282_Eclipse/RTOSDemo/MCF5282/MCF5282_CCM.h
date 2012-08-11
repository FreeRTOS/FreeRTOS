/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.9
 */

#ifndef __MCF5282_CCM_H__
#define __MCF5282_CCM_H__


/*********************************************************************
*
* Chip Configuration Module (CCM)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_CCM_CCR                          (*(vuint16*)(&__IPSBAR[0x110004]))
#define MCF_CCM_RCON                         (*(vuint16*)(&__IPSBAR[0x110008]))
#define MCF_CCM_CIR                          (*(vuint16*)(&__IPSBAR[0x11000A]))


/* Bit definitions and macros for MCF_CCM_CCR */
#define MCF_CCM_CCR_BMT(x)                   (((x)&0x7)<<0)
#define MCF_CCM_CCR_BMT_65536                (0)
#define MCF_CCM_CCR_BMT_32768                (0x1)
#define MCF_CCM_CCR_BMT_16384                (0x2)
#define MCF_CCM_CCR_BMT_8192                 (0x3)
#define MCF_CCM_CCR_BMT_4096                 (0x4)
#define MCF_CCM_CCR_BMT_2048                 (0x5)
#define MCF_CCM_CCR_BMT_1024                 (0x6)
#define MCF_CCM_CCR_BMT_512                  (0x7)
#define MCF_CCM_CCR_BME                      (0x8)
#define MCF_CCM_CCR_PSTEN                    (0x20)
#define MCF_CCM_CCR_SZEN                     (0x40)
#define MCF_CCM_CCR_MODE(x)                  (((x)&0x7)<<0x8)
#define MCF_CCM_CCR_LOAD                     (0x8000)

/* Bit definitions and macros for MCF_CCM_RCON */
#define MCF_CCM_RCON_MODE                    (0x1)
#define MCF_CCM_RCON_BOOTSEL                 (0x4)
#define MCF_CCM_RCON_BOOTPS(x)               (((x)&0x3)<<0x3)
#define MCF_CCM_RCON_RLOAD                   (0x20)
#define MCF_CCM_RCON_RPLLREF                 (0x40)
#define MCF_CCM_RCON_RPLLSEL                 (0x80)
#define MCF_CCM_RCON_RCSC(x)                 (((x)&0x3)<<0x8)

/* Bit definitions and macros for MCF_CCM_CIR */
#define MCF_CCM_CIR_PRN(x)                   (((x)&0xFF)<<0)
#define MCF_CCM_CIR_PIN(x)                   (((x)&0xFF)<<0x8)


#endif /* __MCF5282_CCM_H__ */
