/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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
 *  \file
 *
 *  \section Purpose
 *
 *  Interface for configuring and using Timer Counter (TC) peripherals.
 *
 *  \section Usage
 *  -# Optionally, use TC_FindMckDivisor() to let the program find the best
 *     TCCLKS field value automatically.
 *  -# Configure a Timer Counter in the desired mode using TC_Configure().
 *  -# Start or stop the timer clock using TC_Start() and TC_Stop().
 */

#ifndef _MCAN_CONFIG_
#define _MCAN_CONFIG_

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/


/*------------------------------------------------------------------------------
 *         Global functions
 *------------------------------------------------------------------------------*/

#ifdef __cplusplus
 extern "C" {
#endif

/* Programmable Clock Source for Baud Rate is Common To Both MCAN Controllers */
#define MCAN_PROG_CLK_PRESCALER       1   /* /1 to /256 */  
// select one of the following for the programmable clock source
//#define MCAN_PROG_CLK_SELECT          PMC_PCK_CSS_SLOW_CLK
//#define MCAN_PROG_CLK_SELECT          PMC_PCK_CSS_MAIN_CLK 
//#define MCAN_PROG_CLK_SELECT          PMC_PCK_CSS_PLLA_CLK 
//#define MCAN_PROG_CLK_SELECT          PMC_PCK_CSS_UPLL_CLK 
#define MCAN_PROG_CLK_SELECT          PMC_PCK_CSS_MCK 
#define MCAN_PROG_CLK_FREQ_HZ \
		( (float) 150000000 / (float) MCAN_PROG_CLK_PRESCALER )

#define MCAN0_BIT_RATE_BPS            500000
#define MCAN0_PROP_SEG                2
#define MCAN0_PHASE_SEG1              11
#define MCAN0_PHASE_SEG2              11
#define MCAN0_SYNC_JUMP               4  

#define MCAN0_FAST_BIT_RATE_BPS       2000000
#define MCAN0_FAST_PROP_SEG           2
#define MCAN0_FAST_PHASE_SEG1         4
#define MCAN0_FAST_PHASE_SEG2         4
#define MCAN0_FAST_SYNC_JUMP          2  

#define MCAN0_NMBR_STD_FLTS           8  /* 128 max filters */
#define MCAN0_NMBR_EXT_FLTS           8  /* 64 max filters */
#define MCAN0_NMBR_RX_FIFO0_ELMTS     0  /* # of elements, 64 elements max */
#define MCAN0_NMBR_RX_FIFO1_ELMTS     0  /* # of elements, 64 elements max */
#define MCAN0_NMBR_RX_DED_BUF_ELMTS   16 /* # of elements, 64 elements max */
#define MCAN0_NMBR_TX_EVT_FIFO_ELMTS  0  /* # of elements, 32 elements max */
#define MCAN0_NMBR_TX_DED_BUF_ELMTS   4  /* # of elements, 32 elements max */
#define MCAN0_NMBR_TX_FIFO_Q_ELMTS    0  /* # of elements, 32 elements max */
#define MCAN0_RX_FIFO0_ELMT_SZ        8  /* 8, 12, 16, 20, 24, 32, 48, 64 bytes */
#define MCAN0_RX_FIFO1_ELMT_SZ        8  /* 8, 12, 16, 20, 24, 32, 48, 64 bytes */
#define MCAN0_RX_BUF_ELMT_SZ          8  /* 8, 12, 16, 20, 24, 32, 48, 64 bytes */
#define MCAN0_TX_BUF_ELMT_SZ          8  /* 8, 12, 16, 20, 24, 32, 48, 64 bytes */

#define MCAN1_BIT_RATE_BPS            500000
#define MCAN1_PROP_SEG                2
#define MCAN1_PHASE_SEG1              11
#define MCAN1_PHASE_SEG2              11
#define MCAN1_SYNC_JUMP               4  

#define MCAN1_FAST_BIT_RATE_BPS       2000000
#define MCAN1_FAST_PROP_SEG           2
#define MCAN1_FAST_PHASE_SEG1         4
#define MCAN1_FAST_PHASE_SEG2         4
#define MCAN1_FAST_SYNC_JUMP          2  

#define MCAN1_NMBR_STD_FLTS           8   /* 128 max filters */
#define MCAN1_NMBR_EXT_FLTS           8   /* 64 max filters */
#define MCAN1_NMBR_RX_FIFO0_ELMTS     12  /* # of elements, 64 elements max */
#define MCAN1_NMBR_RX_FIFO1_ELMTS     0   /* # of elements, 64 elements max */
#define MCAN1_NMBR_RX_DED_BUF_ELMTS   4   /* # of elements, 64 elements max */
#define MCAN1_NMBR_TX_EVT_FIFO_ELMTS  0   /* # of elements, 32 elements max */
#define MCAN1_NMBR_TX_DED_BUF_ELMTS   4   /* # of elements, 32 elements max */
#define MCAN1_NMBR_TX_FIFO_Q_ELMTS    4   /* # of elements, 32 elements max */
#define MCAN1_RX_FIFO0_ELMT_SZ        8   /* 8, 12, 16, 20, 24, 32, 48, 64 bytes */
#define MCAN1_RX_FIFO1_ELMT_SZ        8   /* 8, 12, 16, 20, 24, 32, 48, 64 bytes */
#define MCAN1_RX_BUF_ELMT_SZ          64  /* 8, 12, 16, 20, 24, 32, 48, 64 bytes */
#define MCAN1_TX_BUF_ELMT_SZ          32  /* 8, 12, 16, 20, 24, 32, 48, 64 bytes */
   
#ifdef __cplusplus
}
#endif

#endif /* #ifndef _MCAN_CONFIG_ */

