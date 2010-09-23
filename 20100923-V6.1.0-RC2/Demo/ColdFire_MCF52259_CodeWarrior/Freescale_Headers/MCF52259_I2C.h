/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2008/04/17 Revision: 0.2
 *
 * (c) Copyright UNIS, spol. s r.o. 1997-2008
 * UNIS, spol. s r.o.
 * Jundrovska 33
 * 624 00 Brno
 * Czech Republic
 * http      : www.processorexpert.com
 * mail      : info@processorexpert.com
 */

#ifndef __MCF52259_I2C_H__
#define __MCF52259_I2C_H__


/*********************************************************************
*
* I2C Module (I2C)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_I2C0_I2ADR                       (*(vuint8 *)(0x40000300))
#define MCF_I2C0_I2FDR                       (*(vuint8 *)(0x40000304))
#define MCF_I2C0_I2CR                        (*(vuint8 *)(0x40000308))
#define MCF_I2C0_I2SR                        (*(vuint8 *)(0x4000030C))
#define MCF_I2C0_I2DR                        (*(vuint8 *)(0x40000310))

#define MCF_I2C1_I2ADR                       (*(vuint8 *)(0x40000380))
#define MCF_I2C1_I2FDR                       (*(vuint8 *)(0x40000384))
#define MCF_I2C1_I2CR                        (*(vuint8 *)(0x40000388))
#define MCF_I2C1_I2SR                        (*(vuint8 *)(0x4000038C))
#define MCF_I2C1_I2DR                        (*(vuint8 *)(0x40000390))

#define MCF_I2C_I2ADR(x)                     (*(vuint8 *)(0x40000300 + ((x)*0x80)))
#define MCF_I2C_I2FDR(x)                     (*(vuint8 *)(0x40000304 + ((x)*0x80)))
#define MCF_I2C_I2CR(x)                      (*(vuint8 *)(0x40000308 + ((x)*0x80)))
#define MCF_I2C_I2SR(x)                      (*(vuint8 *)(0x4000030C + ((x)*0x80)))
#define MCF_I2C_I2DR(x)                      (*(vuint8 *)(0x40000310 + ((x)*0x80)))


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


#endif /* __MCF52259_I2C_H__ */
