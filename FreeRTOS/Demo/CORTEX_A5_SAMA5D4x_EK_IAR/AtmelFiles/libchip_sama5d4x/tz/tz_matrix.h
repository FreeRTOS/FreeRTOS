/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2013, Atmel Corporation

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
 */
#ifndef __TZ_MATRIX_H__
#define __TZ_MATRIX_H__

#define MATRIX_MCFG(n)	(0x0000 + (n) * 4)/* Master Configuration Register */
#define MATRIX_SCFG(n)	(0x0040 + (n) * 4)/* Slave Configuration Register */
#define MATRIX_PRAS(n)	(0x0080 + (n) * 8)/* Priority Register A for Slave */
#define MATRIX_PRBS(n)	(0x0084 + (n) * 8)/* Priority Register B for Slave */

#define MATRIX_MRCR	0x0100	/* Master Remap Control Register */
#define MATRIX_MEIER	0x0150	/* Master Error Interrupt Enable Register */
#define MATRIX_MEIDR	0x0154	/* Master Error Interrupt Disable Register */
#define MATRIX_MEIMR	0x0158	/* Master Error Interrupt Mask Register */
#define MATRIX_MESR	0x015c	/* Master Error Statue Register */

/* Master n Error Address Register */
#define MATRIX_MEAR(n)	(0x0160 + (n) * 4)

//#define MATRIX_WPMR	0x01E4		/* Write Protect Mode Register */
//#define MATRIX_WPSR	0x01E8		/* Write Protect Status Register */

/* Security Slave n Register */
#define MATRIX_SSR(n)	(0x0200 + (n) * 4)
/* Security Area Split Slave n Register */
#define MATRIX_SASSR(n)	(0x0240 + (n) * 4)
/* Security Region Top Slave n Register */
#define MATRIX_SRTSR(n)	(0x0280 + (n) * 4)

/* Security Peripheral Select n Register */
#define MATRIX_SPSELR(n)	(0x02c0	+ (n) * 4)

/**************************************************************************/
/* Write Protect Mode Register (MATRIX_WPMR) */

#define		MATRIX_WPMR_WPEN_DISABLE	(0 << 0)
#define		MATRIX_WPMR_WPEN_ENABLE		(1 << 0)
#define		MATRIX_WPMR_WPKEY_PASSWD	(0x4D4154 << 8)






#endif /* #ifndef __TZ_MATRIX_H__ */
