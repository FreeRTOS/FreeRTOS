/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.91
 */

#ifndef __MCF52235_I2C_H__
#define __MCF52235_I2C_H__


/*********************************************************************
*
* I2C Module (I2C)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_I2C_I2ADR                        (*(vuint8 *)(&__IPSBAR[0x300]))
#define MCF_I2C_I2FDR                        (*(vuint8 *)(&__IPSBAR[0x304]))
#define MCF_I2C_I2CR                         (*(vuint8 *)(&__IPSBAR[0x308]))
#define MCF_I2C_I2SR                         (*(vuint8 *)(&__IPSBAR[0x30C]))
#define MCF_I2C_I2DR                         (*(vuint8 *)(&__IPSBAR[0x310]))



/* Bit definitions and macros for MCF_I2C_I2ADR */
#define MCF_I2C_I2ADR_ADR(x)                 (((x)&0x7F)<<0x1)

/* Bit definitions and macros for MCF_I2C_I2FDR */
#define MCF_I2C_I2FDR_IC(x)                  (((x)&0x3F)<<0)

/* Bit definitions and macros for MCF_I2C_I2CR */
#define MCF_I2C_I2CR_RSTA                    (0x4)
#define MCF_I2C_I2CR_TXAK                    (0x8)
#define MCF_I2C_I2CR_MTX                     (0x10)
#define MCF_I2C_I2CR_MSTA                    (0x20)
#define MCF_I2C_I2CR_IIEN                    (0x40)
#define MCF_I2C_I2CR_IEN                     (0x80)

/* Bit definitions and macros for MCF_I2C_I2SR */
#define MCF_I2C_I2SR_RXAK                    (0x1)
#define MCF_I2C_I2SR_IIF                     (0x2)
#define MCF_I2C_I2SR_SRW                     (0x4)
#define MCF_I2C_I2SR_IAL                     (0x10)
#define MCF_I2C_I2SR_IBB                     (0x20)
#define MCF_I2C_I2SR_IAAS                    (0x40)
#define MCF_I2C_I2SR_ICF                     (0x80)

/* Bit definitions and macros for MCF_I2C_I2DR */
#define MCF_I2C_I2DR_DATA(x)                 (((x)&0xFF)<<0)


#endif /* __MCF52235_I2C_H__ */
