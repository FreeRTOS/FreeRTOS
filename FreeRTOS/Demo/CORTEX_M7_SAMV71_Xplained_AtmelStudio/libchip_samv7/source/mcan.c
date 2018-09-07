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

/** \file
 *  Implements functions for Controller Area Network (CAN)
 *  peripheral operations.
 */
/** \addtogroup can_module
 *@{*/


/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "board.h"
#include "chip.h"
#include "mcan_config.h"
#include <assert.h>
/*---------------------------------------------------------------------------
 *      Definitions
 *---------------------------------------------------------------------------*/
#define MAILBOX_ADDRESS(address) ( 0xFFFC & (address) )

#define CAN_CLK_FREQ_HZ               MCAN_PROG_CLK_FREQ_HZ

#define MCAN0_TSEG1                   ( MCAN0_PROP_SEG + MCAN0_PHASE_SEG1 )
#define MCAN0_TSEG2                   ( MCAN0_PHASE_SEG2 )
#define MCAN0_BRP                     ((uint32_t) (( (float) CAN_CLK_FREQ_HZ / \
									((float)( MCAN0_TSEG1 + MCAN0_TSEG2 + 3 ) *\
									(float) MCAN0_BIT_RATE_BPS )) - 1 ))
#define MCAN0_SJW                     ( MCAN0_SYNC_JUMP - 1 )
#define MCAN0_FTSEG1                  ( MCAN0_FAST_PROP_SEG + MCAN0_FAST_PHASE_SEG1 )
#define MCAN0_FTSEG2                  ( MCAN0_FAST_PHASE_SEG2 )
#define MCAN0_FBRP                    ((uint32_t) (( (float) CAN_CLK_FREQ_HZ / \
									((float)( MCAN0_FTSEG1 + MCAN0_FTSEG2 + 3 ) * \
									(float) MCAN0_FAST_BIT_RATE_BPS )) - 1 ))
#define MCAN0_FSJW                    ( MCAN0_FAST_SYNC_JUMP - 1 )

#define MCAN0_STD_FLTS_WRDS           (MCAN0_NMBR_STD_FLTS)  
									/* 128 max filters */
#define MCAN0_EXT_FLTS_WRDS           (MCAN0_NMBR_EXT_FLTS * 2)  
									/* 64 max filters */
#define MCAN0_RX_FIFO0_WRDS           (MCAN0_NMBR_RX_FIFO0_ELMTS * \
									((MCAN0_RX_FIFO0_ELMT_SZ/4) + 2)) 
									/* 64 elements max */
#define MCAN0_RX_FIFO1_WRDS           (MCAN0_NMBR_RX_FIFO1_ELMTS *\
									((MCAN0_RX_FIFO1_ELMT_SZ/4) + 2))  
									/* 64 elements max */
#define MCAN0_RX_DED_BUFS_WRDS            (MCAN0_NMBR_RX_DED_BUF_ELMTS * \
										((MCAN0_RX_BUF_ELMT_SZ/4) + 2)) 
									/* 64 elements max */
#define MCAN0_TX_EVT_FIFO_WRDS        (MCAN0_NMBR_TX_EVT_FIFO_ELMTS * 2)  
									/* 32 elements max */
#define MCAN0_TX_DED_BUF_WRDS         (MCAN0_NMBR_TX_DED_BUF_ELMTS * \
									((MCAN0_TX_BUF_ELMT_SZ/4) + 2))  
									/* 32 elements max */
#define MCAN0_TX_FIFO_Q_WRDS          (MCAN0_NMBR_TX_FIFO_Q_ELMTS *\
									((MCAN0_TX_BUF_ELMT_SZ/4) + 2))  
									/* 32 elements max */

#define MCAN1_TSEG1                   ( MCAN1_PROP_SEG + MCAN1_PHASE_SEG1 )
#define MCAN1_TSEG2                   ( MCAN1_PHASE_SEG2 )
#define MCAN1_BRP                     ((uint32_t) (( (float) CAN_CLK_FREQ_HZ / \
									((float)( MCAN1_TSEG1 + MCAN1_TSEG2 + 3 ) *\
									(float) MCAN1_BIT_RATE_BPS )) - 1 ))
#define MCAN1_SJW                     ( MCAN1_SYNC_JUMP - 1 )
#define MCAN1_FTSEG1                  ( MCAN1_FAST_PROP_SEG + MCAN1_FAST_PHASE_SEG1 )
#define MCAN1_FTSEG2                  ( MCAN1_FAST_PHASE_SEG2 )
#define MCAN1_FBRP                    ((uint32_t) (( (float) CAN_CLK_FREQ_HZ /\
									((float)( MCAN1_FTSEG1 + MCAN1_FTSEG2 + 3 ) *\
									(float) MCAN1_FAST_BIT_RATE_BPS )) - 1 ))
#define MCAN1_FSJW                    ( MCAN1_FAST_SYNC_JUMP - 1 )

#define MCAN1_STD_FLTS_WRDS           (MCAN1_NMBR_STD_FLTS)  
									/* 128 max filters */
#define MCAN1_EXT_FLTS_WRDS           (MCAN1_NMBR_EXT_FLTS * 2)  
									/* 64 max filters */
#define MCAN1_RX_FIFO0_WRDS           (MCAN1_NMBR_RX_FIFO0_ELMTS * \
									((MCAN1_RX_FIFO0_ELMT_SZ/4) + 2))  
									/* 64 elements max */
#define MCAN1_RX_FIFO1_WRDS           (MCAN1_NMBR_RX_FIFO1_ELMTS *\
									((MCAN1_RX_FIFO1_ELMT_SZ/4) + 2))  
									/* 64 elements max */
#define MCAN1_RX_DED_BUFS_WRDS            (MCAN1_NMBR_RX_DED_BUF_ELMTS * \
									((MCAN1_RX_BUF_ELMT_SZ/4) + 2))  
									/* 64 elements max */
#define MCAN1_TX_EVT_FIFO_WRDS        (MCAN1_NMBR_TX_EVT_FIFO_ELMTS * 2)  
/* 32 elements max */
#define MCAN1_TX_DED_BUF_WRDS         (MCAN1_NMBR_TX_DED_BUF_ELMTS * \
									((MCAN1_TX_BUF_ELMT_SZ/4) + 2))  
									/* 32 elements max */
#define MCAN1_TX_FIFO_Q_WRDS          (MCAN1_NMBR_TX_FIFO_Q_ELMTS * \
									((MCAN1_TX_BUF_ELMT_SZ/4) + 2))  
									/* 32 elements max */

/* validate CAN0 entries */
#if ( MCAN0_TSEG1 > 63 ) 
#error "Invalid CAN0 TSEG1"  
#endif
#if (  MCAN0_TSEG2 > 15 ) 
#error "Invalid CAN0 TSEG2"  
#endif
#if ( MCAN0_SJW > 15 ) 
#error "Invalid CAN0 SJW"  
#endif
#if ( MCAN0_FTSEG1 > 15 ) 
#error "Invalid CAN0 FTSEG1"  
#endif
#if (  MCAN0_FTSEG2 > 7 ) 
#error "Invalid CAN0 FTSEG2"  
#endif
#if ( MCAN0_FSJW > 3 ) 
#error "Invalid CAN0 FSJW"  
#endif

#if ( MCAN0_NMBR_STD_FLTS > 128 ) 
#error "Invalid CAN0 # of Standard Filters"  
#endif
#if ( MCAN0_NMBR_EXT_FLTS > 64 ) 
#error "Invalid CAN0 # of Extended Filters"  
#endif
#if ( MCAN0_NMBR_RX_FIFO0_ELMTS > 64 ) 
#error "Invalid CAN0 # RX FIFO 0 ELEMENTS"  
#endif
#if ( MCAN0_NMBR_RX_FIFO1_ELMTS > 64 ) 
#error "Invalid CAN0 # RX FIFO 0 ELEMENTS"  
#endif
#if ( MCAN0_NMBR_RX_DED_BUF_ELMTS > 64 ) 
#error "Invalid CAN0 # RX BUFFER ELEMENTS"  
#endif
#if ( MCAN0_NMBR_TX_EVT_FIFO_ELMTS > 32 ) 
#error "Invalid CAN0 # TX EVENT FIFO ELEMENTS"  
#endif
#if ( (MCAN0_NMBR_TX_DED_BUF_ELMTS + MCAN0_NMBR_TX_FIFO_Q_ELMTS)  > 32 ) 
#error "Invalid CAN0 # TX BUFFER ELEMENTS"  
#endif

#if   ( 8 == MCAN0_RX_FIFO0_ELMT_SZ )
#define MCAN0_RX_FIFO0_DATA_SIZE  (0u)
#elif ( 12 == MCAN0_RX_FIFO0_ELMT_SZ )
#define MCAN0_RX_FIFO0_DATA_SIZE  (1u)
#elif ( 16 == MCAN0_RX_FIFO0_ELMT_SZ )
#define MCAN0_RX_FIFO0_DATA_SIZE  (2u)
#elif ( 20 == MCAN0_RX_FIFO0_ELMT_SZ )
#define MCAN0_RX_FIFO0_DATA_SIZE  (3u)
#elif ( 24 == MCAN0_RX_FIFO0_ELMT_SZ )
#define MCAN0_RX_FIFO0_DATA_SIZE  (4u)
#elif ( 32 == MCAN0_RX_FIFO0_ELMT_SZ )
#define MCAN0_RX_FIFO0_DATA_SIZE  (5u)
#elif ( 48 == MCAN0_RX_FIFO0_ELMT_SZ )
#define MCAN0_RX_FIFO0_DATA_SIZE  (6u)
#elif ( 64 == MCAN0_RX_FIFO0_ELMT_SZ )
#define MCAN0_RX_FIFO0_DATA_SIZE  (7u)
#else
#error "Invalid CAN0 RX FIFO0 ELEMENT SIZE"
#endif

#if   ( 8 == MCAN0_RX_FIFO1_ELMT_SZ )
#define MCAN0_RX_FIFO1_DATA_SIZE  (0u)
#elif ( 12 == MCAN0_RX_FIFO1_ELMT_SZ )
#define MCAN0_RX_FIFO1_DATA_SIZE  (1u)
#elif ( 16 == MCAN0_RX_FIFO1_ELMT_SZ )
#define MCAN0_RX_FIFO1_DATA_SIZE  (2u)
#elif ( 20 == MCAN0_RX_FIFO1_ELMT_SZ )
#define MCAN0_RX_FIFO1_DATA_SIZE  (3u)
#elif ( 24 == MCAN0_RX_FIFO1_ELMT_SZ )
#define MCAN0_RX_FIFO1_DATA_SIZE  (4u)
#elif ( 32 == MCAN0_RX_FIFO1_ELMT_SZ )
#define MCAN0_RX_FIFO1_DATA_SIZE  (5u)
#elif ( 48 == MCAN0_RX_FIFO1_ELMT_SZ )
#define MCAN0_RX_FIFO1_DATA_SIZE  (6u)
#elif ( 64 == MCAN0_RX_FIFO1_ELMT_SZ )
#define MCAN0_RX_FIFO1_DATA_SIZE  (7u)
#else
#error "Invalid CAN0 RX FIFO1 ELEMENT SIZE"
#endif

#if   ( 8 == MCAN0_RX_BUF_ELMT_SZ )
#define MCAN0_RX_BUF_DATA_SIZE  (0u)
#elif ( 12 == MCAN0_RX_BUF_ELMT_SZ )
#define MCAN0_RX_BUF_DATA_SIZE  (1u)
#elif ( 16 == MCAN0_RX_BUF_ELMT_SZ )
#define MCAN0_RX_BUF_DATA_SIZE  (2u)
#elif ( 20 == MCAN0_RX_BUF_ELMT_SZ )
#define MCAN0_RX_BUF_DATA_SIZE  (3u)
#elif ( 24 == MCAN0_RX_BUF_ELMT_SZ )
#define MCAN0_RX_BUF_DATA_SIZE  (4u)
#elif ( 32 == MCAN0_RX_BUF_ELMT_SZ )
#define MCAN0_RX_BUF_DATA_SIZE  (5u)
#elif ( 48 == MCAN0_RX_BUF_ELMT_SZ )
#define MCAN0_RX_BUF_DATA_SIZE  (6u)
#elif ( 64 == MCAN0_RX_BUF_ELMT_SZ )
#define MCAN0_RX_BUF_DATA_SIZE  (7u)
#else
#error "Invalid CAN0 RX BUFFER ELEMENT SIZE"
#endif

#if   ( 8 == MCAN0_TX_BUF_ELMT_SZ )
#define MCAN0_TX_BUF_DATA_SIZE  (0u)
#elif ( 12 == MCAN0_TX_BUF_ELMT_SZ )
#define MCAN0_TX_BUF_DATA_SIZE  (1u)
#elif ( 16 == MCAN0_TX_BUF_ELMT_SZ )
#define MCAN0_TX_BUF_DATA_SIZE  (2u)
#elif ( 20 == MCAN0_TX_BUF_ELMT_SZ )
#define MCAN0_TX_BUF_DATA_SIZE  (3u)
#elif ( 24 == MCAN0_TX_BUF_ELMT_SZ )
#define MCAN0_TX_BUF_DATA_SIZE  (4u)
#elif ( 32 == MCAN0_TX_BUF_ELMT_SZ )
#define MCAN0_TX_BUF_DATA_SIZE  (5u)
#elif ( 48 == MCAN0_TX_BUF_ELMT_SZ )
#define MCAN0_TX_BUF_DATA_SIZE  (6u)
#elif ( 64 == MCAN0_TX_BUF_ELMT_SZ )
#define MCAN0_TX_BUF_DATA_SIZE  (7u)
#else
#error "Invalid CAN0 TX BUFFER ELEMENT SIZE"
#endif

/* validate CAN1 entries */
#if ( MCAN1_TSEG1 > 63 ) 
#error "Invalid CAN1 TSEG1"  
#endif
#if (  MCAN1_TSEG2 > 15 ) 
#error "Invalid CAN1 TSEG2"  
#endif
#if ( MCAN1_SJW > 15 ) 
#error "Invalid CAN1 SJW"  
#endif
#if ( MCAN1_FTSEG1 > 15 ) 
#error "Invalid CAN1 FTSEG1"  
#endif
#if (  MCAN1_FTSEG2 > 7 ) 
#error "Invalid CAN1 FTSEG2"  
#endif
#if ( MCAN1_FSJW > 3 ) 
#error "Invalid CAN1 FSJW"  
#endif

#if ( MCAN1_NMBR_STD_FLTS > 128 ) 
#error "Invalid CAN1 # of Standard Filters"  
#endif
#if ( MCAN1_NMBR_EXT_FLTS > 64 ) 
#error "Invalid CAN1 # of Extended Filters"  
#endif
#if ( MCAN1_NMBR_RX_FIFO0_ELMTS > 64 ) 
#error "Invalid CAN1 # RX FIFO 0 ELEMENTS"  
#endif
#if ( MCAN1_NMBR_RX_FIFO1_ELMTS > 64 ) 
#error "Invalid CAN1 # RX FIFO 0 ELEMENTS"  
#endif
#if ( MCAN1_NMBR_RX_DED_BUF_ELMTS > 64 ) 
#error "Invalid CAN1 # RX BUFFER ELEMENTS"  
#endif
#if ( MCAN1_NMBR_TX_EVT_FIFO_ELMTS > 32 ) 
#error "Invalid CAN1 # TX EVENT FIFO ELEMENTS"  
#endif
#if ( (MCAN1_NMBR_TX_DED_BUF_ELMTS + MCAN1_NMBR_TX_FIFO_Q_ELMTS)  > 32 ) 
#error "Invalid CAN1 # TX BUFFER ELEMENTS"  
#endif

#if   ( 8 == MCAN1_RX_FIFO0_ELMT_SZ )
#define MCAN1_RX_FIFO0_DATA_SIZE  (0u)
#elif ( 12 == MCAN1_RX_FIFO0_ELMT_SZ )
#define MCAN1_RX_FIFO0_DATA_SIZE  (1u)
#elif ( 16 == MCAN1_RX_FIFO0_ELMT_SZ )
#define MCAN1_RX_FIFO0_DATA_SIZE  (2u)
#elif ( 20 == MCAN1_RX_FIFO0_ELMT_SZ )
#define MCAN1_RX_FIFO0_DATA_SIZE  (3u)
#elif ( 24 == MCAN1_RX_FIFO0_ELMT_SZ )
#define MCAN1_RX_FIFO0_DATA_SIZE  (4u)
#elif ( 32 == MCAN1_RX_FIFO0_ELMT_SZ )
#define MCAN1_RX_FIFO0_DATA_SIZE  (5u)
#elif ( 48 == MCAN1_RX_FIFO0_ELMT_SZ )
#define MCAN1_RX_FIFO0_DATA_SIZE  (6u)
#elif ( 64 == MCAN1_RX_FIFO0_ELMT_SZ )
#define MCAN1_RX_FIFO0_DATA_SIZE  (7u)
#else
#error "Invalid CAN1 RX FIFO0 ELEMENT SIZE"
#endif

#if   ( 8 == MCAN1_RX_FIFO1_ELMT_SZ )
#define MCAN1_RX_FIFO1_DATA_SIZE  (0u)
#elif ( 12 == MCAN1_RX_FIFO1_ELMT_SZ )
#define MCAN1_RX_FIFO1_DATA_SIZE  (1u)
#elif ( 16 == MCAN1_RX_FIFO1_ELMT_SZ )
#define MCAN1_RX_FIFO1_DATA_SIZE  (2u)
#elif ( 20 == MCAN1_RX_FIFO1_ELMT_SZ )
#define MCAN1_RX_FIFO1_DATA_SIZE  (3u)
#elif ( 24 == MCAN1_RX_FIFO1_ELMT_SZ )
#define MCAN1_RX_FIFO1_DATA_SIZE  (4u)
#elif ( 32 == MCAN1_RX_FIFO1_ELMT_SZ )
#define MCAN1_RX_FIFO1_DATA_SIZE  (5u)
#elif ( 48 == MCAN1_RX_FIFO1_ELMT_SZ )
#define MCAN1_RX_FIFO1_DATA_SIZE  (6u)
#elif ( 64 == MCAN1_RX_FIFO1_ELMT_SZ )
#define MCAN1_RX_FIFO1_DATA_SIZE  (7u)
#else
#error "Invalid CAN1 RX FIFO1 ELEMENT SIZE"
#endif

#if   ( 8 == MCAN1_RX_BUF_ELMT_SZ )
#define MCAN1_RX_BUF_DATA_SIZE  (0u)
#elif ( 12 == MCAN1_RX_BUF_ELMT_SZ )
#define MCAN1_RX_BUF_DATA_SIZE  (1u)
#elif ( 16 == MCAN1_RX_BUF_ELMT_SZ )
#define MCAN1_RX_BUF_DATA_SIZE  (2u)
#elif ( 20 == MCAN1_RX_BUF_ELMT_SZ )
#define MCAN1_RX_BUF_DATA_SIZE  (3u)
#elif ( 24 == MCAN1_RX_BUF_ELMT_SZ )
#define MCAN1_RX_BUF_DATA_SIZE  (4u)
#elif ( 32 == MCAN1_RX_BUF_ELMT_SZ )
#define MCAN1_RX_BUF_DATA_SIZE  (5u)
#elif ( 48 == MCAN1_RX_BUF_ELMT_SZ )
#define MCAN1_RX_BUF_DATA_SIZE  (6u)
#elif ( 64 == MCAN1_RX_BUF_ELMT_SZ )
#define MCAN1_RX_BUF_DATA_SIZE  (7u)
#else
#error "Invalid CAN1 RX BUFFER ELEMENT SIZE"
#endif

#if   ( 8 == MCAN1_TX_BUF_ELMT_SZ )
#define MCAN1_TX_BUF_DATA_SIZE  (0u)
#elif ( 12 == MCAN1_TX_BUF_ELMT_SZ )
#define MCAN1_TX_BUF_DATA_SIZE  (1u)
#elif ( 16 == MCAN1_TX_BUF_ELMT_SZ )
#define MCAN1_TX_BUF_DATA_SIZE  (2u)
#elif ( 20 == MCAN1_TX_BUF_ELMT_SZ )
#define MCAN1_TX_BUF_DATA_SIZE  (3u)
#elif ( 24 == MCAN1_TX_BUF_ELMT_SZ )
#define MCAN1_TX_BUF_DATA_SIZE  (4u)
#elif ( 32 == MCAN1_TX_BUF_ELMT_SZ )
#define MCAN1_TX_BUF_DATA_SIZE  (5u)
#elif ( 48 == MCAN1_TX_BUF_ELMT_SZ )
#define MCAN1_TX_BUF_DATA_SIZE  (6u)
#elif ( 64 == MCAN1_TX_BUF_ELMT_SZ )
#define MCAN1_TX_BUF_DATA_SIZE  (7u)
#else
#error "Invalid CAN1 TX BUFFER ELEMENT SIZE"
#endif

#define CAN_11_BIT_ID_MASK                 (0x7FF)
#define CAN_29_BIT_ID_MASK                 (0x1FFFFFFF)
#define ELMT_SIZE_MASK                (0x1F) 
/* max element size is 18 words, fits in 5 bits */

#define BUFFER_XTD_MASK               (0x40000000)
#define BUFFER_EXT_ID_MASK            (0x1FFFFFFF)
#define BUFFER_STD_ID_MASK            (0x1FFC0000)
#define BUFFER_DLC_MASK               (0x000F0000)
#define BUFFER_RXTS_MASK              (0x0000FFFF)

#define STD_FILT_SFT_MASK             (3 << 30)
#define STD_FILT_SFT_RANGE            (0 << 30)
#define STD_FILT_SFT_DUAL             (1 << 30)
#define STD_FILT_SFT_CLASSIC          (2 << 30)
#define STD_FILT_SFEC_MASK            (7 << 27)
#define STD_FILT_SFEC_DISABLE         (0 << 27)
#define STD_FILT_SFEC_FIFO0           (1 << 27)
#define STD_FILT_SFEC_FIFO1           (2 << 27)
#define STD_FILT_SFEC_REJECT          (3 << 27)
#define STD_FILT_SFEC_PRIORITY        (4 << 27)
#define STD_FILT_SFEC_PRIORITY_FIFO0  (5 << 27)
#define STD_FILT_SFEC_PRIORITY_FIFO1  (6 << 27)
#define STD_FILT_SFEC_BUFFER          (7 << 27)
#define STD_FILT_SFID1_MASK           (0x03FF << 16)
#define STD_FILT_SFID2_MASK           (0x3FF << 0)
#define STD_FILT_SFID2_RX_BUFFER      (0 << 9)
#define STD_FILT_SFID2_DEBUG_A        (1 << 9)
#define STD_FILT_SFID2_DEBUG_B        (2 << 9)
#define STD_FILT_SFID2_DEBUG_C        (3 << 9)
#define STD_FILT_SFID2_BUFFER(nmbr)   (nmbr & 0x3F)

#define EXT_FILT_EFEC_MASK            (7 << 29)
#define EXT_FILT_EFEC_DISABLE         (0 << 29)
#define EXT_FILT_EFEC_FIFO0           (1 << 29)
#define EXT_FILT_EFEC_FIFO1           (2 << 29)
#define EXT_FILT_EFEC_REJECT          (3 << 29)
#define EXT_FILT_EFEC_PRIORITY        (4 << 29)
#define EXT_FILT_EFEC_PRIORITY_FIFO0  (5 << 29)
#define EXT_FILT_EFEC_PRIORITY_FIFO1  (6 << 29)
#define EXT_FILT_EFEC_BUFFER          (7 << 29)
#define EXT_FILT_EFID1_MASK           (0x1FFFFFFF)
#define EXT_FILT_EFT_MASK             (3 << 30)
#define EXT_FILT_EFT_RANGE            (0 << 30)
#define EXT_FILT_EFT_DUAL             (1 << 30)
#define EXT_FILT_EFT_CLASSIC          (2 << 30)
#define EXT_FILT_EFT_RANGE_NO_XIDAM   (3 << 30)
#define EXT_FILT_EFID2_MASK           (0x1FFFFFFF)
#define EXT_FILT_EFID2_RX_BUFFER      (0 << 9)
#define EXT_FILT_EFID2_DEBUG_A        (1 << 9)
#define EXT_FILT_EFID2_DEBUG_B        (2 << 9)
#define EXT_FILT_EFID2_DEBUG_C        (3 << 9)
#define EXT_FILT_EFID2_BUFFER(nmbr)   (nmbr & 0x3F)


/*---------------------------------------------------------------------------
 *      Internal variables
 *---------------------------------------------------------------------------*/

static const Pin pinsMcan0[] =  {PIN_MCAN0_TXD, PIN_MCAN0_RXD };
static const Pin pinsMcan1[] =  {PIN_MCAN1_TXD, PIN_MCAN1_RXD };

static uint32_t can0MsgRam[MCAN0_STD_FLTS_WRDS + 
						   MCAN0_EXT_FLTS_WRDS + 
						   MCAN0_RX_FIFO0_WRDS + 
						   MCAN0_RX_FIFO1_WRDS + 
						   MCAN0_RX_DED_BUFS_WRDS + 
						   MCAN0_TX_EVT_FIFO_WRDS + 
						   MCAN0_TX_DED_BUF_WRDS + 
						   MCAN0_TX_FIFO_Q_WRDS];

static uint32_t can1MsgRam[MCAN1_STD_FLTS_WRDS + 
						   MCAN1_EXT_FLTS_WRDS + 
						   MCAN1_RX_FIFO0_WRDS + 
						   MCAN1_RX_FIFO1_WRDS + 
						   MCAN1_RX_DED_BUFS_WRDS + 
						   MCAN1_TX_EVT_FIFO_WRDS + 
						   MCAN1_TX_DED_BUF_WRDS + 
						   MCAN1_TX_FIFO_Q_WRDS];

const MCan_ConfigType mcan0Config =
{
	MCAN0,
	MCAN_BTP_BRP(MCAN0_BRP) | MCAN_BTP_TSEG1(MCAN0_TSEG1) | 
	MCAN_BTP_TSEG2(MCAN0_TSEG2) | MCAN_BTP_SJW(MCAN0_SJW), 
	MCAN_FBTP_FBRP(MCAN0_FBRP) | MCAN_FBTP_FTSEG1(MCAN0_FTSEG1) | 
	MCAN_FBTP_FTSEG2(MCAN0_FTSEG2) | MCAN_FBTP_FSJW(MCAN0_FSJW), 
	MCAN0_NMBR_STD_FLTS,
	MCAN0_NMBR_EXT_FLTS,
	MCAN0_NMBR_RX_FIFO0_ELMTS,
	MCAN0_NMBR_RX_FIFO1_ELMTS,
	MCAN0_NMBR_RX_DED_BUF_ELMTS,
	MCAN0_NMBR_TX_EVT_FIFO_ELMTS,
	MCAN0_NMBR_TX_DED_BUF_ELMTS,
	MCAN0_NMBR_TX_FIFO_Q_ELMTS,
	(MCAN0_RX_FIFO0_DATA_SIZE << 29) | ((MCAN0_RX_FIFO0_ELMT_SZ/4)+2), 
	/* element size in WORDS */
	(MCAN0_RX_FIFO1_DATA_SIZE << 29) | ((MCAN0_RX_FIFO1_ELMT_SZ/4)+2), 
	/* element size in WORDS */
	(MCAN0_RX_BUF_DATA_SIZE << 29) | ((MCAN0_RX_BUF_ELMT_SZ/4)+2), 
	/* element size in WORDS */ 
	(MCAN0_TX_BUF_DATA_SIZE << 29) | ((MCAN0_TX_BUF_ELMT_SZ/4)+2), 
	/* element size in WORDS */
	{
		&can0MsgRam[0],
		&can0MsgRam[MCAN0_STD_FLTS_WRDS],
		&can0MsgRam[MCAN0_STD_FLTS_WRDS + MCAN0_EXT_FLTS_WRDS],
		&can0MsgRam[MCAN0_STD_FLTS_WRDS + MCAN0_EXT_FLTS_WRDS + MCAN0_RX_FIFO0_WRDS],
		&can0MsgRam[MCAN0_STD_FLTS_WRDS + MCAN0_EXT_FLTS_WRDS + MCAN0_RX_FIFO0_WRDS + 
		MCAN0_RX_FIFO1_WRDS],
		&can0MsgRam[MCAN0_STD_FLTS_WRDS + MCAN0_EXT_FLTS_WRDS + MCAN0_RX_FIFO0_WRDS + 
		MCAN0_RX_FIFO1_WRDS + MCAN0_RX_DED_BUFS_WRDS],
		&can0MsgRam[MCAN0_STD_FLTS_WRDS + MCAN0_EXT_FLTS_WRDS + MCAN0_RX_FIFO0_WRDS + 
		MCAN0_RX_FIFO1_WRDS + MCAN0_RX_DED_BUFS_WRDS + MCAN0_TX_EVT_FIFO_WRDS],
		&can0MsgRam[MCAN0_STD_FLTS_WRDS + MCAN0_EXT_FLTS_WRDS + MCAN0_RX_FIFO0_WRDS + 
		MCAN0_RX_FIFO1_WRDS + MCAN0_RX_DED_BUFS_WRDS + MCAN0_TX_EVT_FIFO_WRDS + 
		MCAN0_TX_DED_BUF_WRDS]    
  },
};

const MCan_ConfigType mcan1Config =
{
	MCAN1,
	MCAN_BTP_BRP(MCAN1_BRP) | MCAN_BTP_TSEG1(MCAN1_TSEG1) | 
	MCAN_BTP_TSEG2(MCAN1_TSEG2) | MCAN_BTP_SJW(MCAN1_SJW), 
	MCAN_FBTP_FBRP(MCAN1_FBRP) | MCAN_FBTP_FTSEG1(MCAN1_FTSEG1) | 
	MCAN_FBTP_FTSEG2(MCAN1_FTSEG2) | MCAN_FBTP_FSJW(MCAN1_FSJW), 
	MCAN1_NMBR_STD_FLTS,
	MCAN1_NMBR_EXT_FLTS,
	MCAN1_NMBR_RX_FIFO0_ELMTS,
	MCAN1_NMBR_RX_FIFO1_ELMTS,
	MCAN0_NMBR_RX_DED_BUF_ELMTS,
	MCAN1_NMBR_TX_EVT_FIFO_ELMTS,
	MCAN1_NMBR_TX_DED_BUF_ELMTS,
	MCAN1_NMBR_TX_FIFO_Q_ELMTS,
	(MCAN1_RX_FIFO0_DATA_SIZE << 29) | ((MCAN1_RX_FIFO0_ELMT_SZ/4)+2), 
	/* element size in WORDS */
	(MCAN1_RX_FIFO1_DATA_SIZE << 29) | ((MCAN1_RX_FIFO1_ELMT_SZ/4)+2), 
	/* element size in WORDS */
	(MCAN1_RX_BUF_DATA_SIZE << 29) | ((MCAN1_RX_BUF_ELMT_SZ/4)+2), 
	/* element size in WORDS */ 
	(MCAN1_TX_BUF_DATA_SIZE << 29) | ((MCAN1_TX_BUF_ELMT_SZ/4)+2), 
	/* element size in WORDS */
	{
		&can1MsgRam[0],
		&can1MsgRam[MCAN1_STD_FLTS_WRDS],
		&can1MsgRam[MCAN1_STD_FLTS_WRDS + MCAN1_EXT_FLTS_WRDS],
		&can1MsgRam[MCAN1_STD_FLTS_WRDS + MCAN1_EXT_FLTS_WRDS + MCAN1_RX_FIFO0_WRDS],
		&can1MsgRam[MCAN1_STD_FLTS_WRDS + MCAN1_EXT_FLTS_WRDS + MCAN1_RX_FIFO0_WRDS 
		+ MCAN1_RX_FIFO1_WRDS],
		&can1MsgRam[MCAN1_STD_FLTS_WRDS + MCAN1_EXT_FLTS_WRDS + MCAN1_RX_FIFO0_WRDS
		+ MCAN1_RX_FIFO1_WRDS + MCAN1_RX_DED_BUFS_WRDS],
		&can1MsgRam[MCAN1_STD_FLTS_WRDS + MCAN1_EXT_FLTS_WRDS + MCAN1_RX_FIFO0_WRDS
		+ MCAN1_RX_FIFO1_WRDS + MCAN1_RX_DED_BUFS_WRDS + MCAN1_TX_EVT_FIFO_WRDS],
		&can1MsgRam[MCAN1_STD_FLTS_WRDS + MCAN1_EXT_FLTS_WRDS + MCAN1_RX_FIFO0_WRDS
		+ MCAN1_RX_FIFO1_WRDS + MCAN1_RX_DED_BUFS_WRDS + MCAN1_TX_EVT_FIFO_WRDS
		+ MCAN1_TX_DED_BUF_WRDS]
	},
};


/*---------------------------------------------------------------------------
 *      Exported Functions
 *---------------------------------------------------------------------------*/
 /**
 * \brief Initializes the MCAN hardware for giving peripheral.
 * Default: Mixed mode TX Buffer + FIFO.
 *
 * \param mcanConfig  Pointer to a MCAN instance.
 */
void MCAN_Init( const MCan_ConfigType * mcanConfig )
{
	Mcan      * mcan = mcanConfig->pMCan;
	uint32_t    regVal32;
	uint32_t  * pMsgRam;
	uint32_t    cntr;
	IRQn_Type   mCanLine0Irq;
	
	/* Both MCAN controllers use programmable clock 5 to derive bit rate */
	// select MCK divided by 1 as programmable clock 5 output
	PMC->PMC_PCK[5] = PMC_PCK_PRES(MCAN_PROG_CLK_PRESCALER - 1) | MCAN_PROG_CLK_SELECT; 
	PMC->PMC_SCER = PMC_SCER_PCK5;
	
	if( MCAN0 ==  mcan ) {
		PIO_Configure(pinsMcan0, PIO_LISTSIZE(pinsMcan0));
		// Enable MCAN peripheral clock
		PMC_EnablePeripheral( ID_MCAN0 );
		// Configure Message RAM Base Address
		regVal32 = MATRIX->CCFG_CAN0 & 0x000001FF;
		MATRIX->CCFG_CAN0 = regVal32 | 
			( (uint32_t) mcanConfig->msgRam.pStdFilts & 0xFFFF0000 );
		mCanLine0Irq = MCAN0_IRQn;
	} else if ( MCAN1 ==  mcan ) {
		PIO_Configure(pinsMcan1, PIO_LISTSIZE(pinsMcan1));
		// Enable MCAN peripheral clock
		PMC_EnablePeripheral( ID_MCAN1 );
		// Configure Message RAM Base Address
		regVal32 = MATRIX->CCFG_SYSIO & 0x0000FFFF;
		MATRIX->CCFG_SYSIO = regVal32 | ( (uint32_t) mcanConfig->msgRam.pStdFilts & 0xFFFF0000 );
		mCanLine0Irq = MCAN1_IRQn;
	} else {
		return;
	}
	
	/* Indicates Initialization state */
	mcan->MCAN_CCCR = MCAN_CCCR_INIT_ENABLED;
	do { regVal32 = mcan->MCAN_CCCR; } 
		while(0u == (regVal32 & MCAN_CCCR_INIT_ENABLED));
	
	/* Enable writing to configuration registers */
	mcan->MCAN_CCCR = MCAN_CCCR_INIT_ENABLED | MCAN_CCCR_CCE_CONFIGURABLE;
	
	/* Global Filter Configuration: Reject remote frames, reject non-matching frames */
	mcan->MCAN_GFC = MCAN_GFC_RRFE_REJECT | MCAN_GFC_RRFS_REJECT 
		| MCAN_GFC_ANFE(2) | MCAN_GFC_ANFS(2);
	
	// Extended ID Filter AND mask  
	mcan->MCAN_XIDAM = 0x1FFFFFFF; 
	
	/* Interrupt configuration - leave initialization with all interrupts off */
	// Disable all interrupts  
	mcan->MCAN_IE =  0;
	mcan->MCAN_TXBTIE = 0x00000000;
	// All interrupts directed to Line 0
	mcan->MCAN_ILS =  0x00000000;
	// Disable both interrupt LINE 0 & LINE 1
	mcan->MCAN_ILE = 0x00;
	// Clear all interrupt flags
	mcan->MCAN_IR = 0xFFCFFFFF;
	/* Enable NVIC - but no interrupts will happen since all sources are 
		disabled in MCAN_IE */
	NVIC_ClearPendingIRQ(mCanLine0Irq);
	NVIC_EnableIRQ(mCanLine0Irq);
	NVIC_ClearPendingIRQ((IRQn_Type) (mCanLine0Irq+1));
	NVIC_EnableIRQ((IRQn_Type) (mCanLine0Irq+1));
	
	/* Configure CAN bit timing */
	mcan->MCAN_BTP = mcanConfig->bitTiming;
	mcan->MCAN_FBTP = mcanConfig->fastBitTiming;
	
	/* Configure message RAM starting addresses & sizes */
	mcan->MCAN_SIDFC = MAILBOX_ADDRESS( (uint32_t) mcanConfig->msgRam.pStdFilts ) 
			| MCAN_SIDFC_LSS(mcanConfig->nmbrStdFilts);
	mcan->MCAN_XIDFC = MAILBOX_ADDRESS( (uint32_t) mcanConfig->msgRam.pExtFilts ) 
			| MCAN_XIDFC_LSE(mcanConfig->nmbrExtFilts);
	mcan->MCAN_RXF0C = MAILBOX_ADDRESS( (uint32_t) mcanConfig->msgRam.pRxFifo0 )
			| MCAN_RXF0C_F0S(mcanConfig->nmbrFifo0Elmts);  
	// watermark interrupt off, blocking mode
	mcan->MCAN_RXF1C = MAILBOX_ADDRESS( (uint32_t) mcanConfig->msgRam.pRxFifo1 ) 
			| MCAN_RXF1C_F1S(mcanConfig->nmbrFifo1Elmts);  
	// watermark interrupt off, blocking mode 
	mcan->MCAN_RXBC = MAILBOX_ADDRESS( (uint32_t) mcanConfig->msgRam.pRxDedBuf ); 
	mcan->MCAN_TXEFC = MAILBOX_ADDRESS( (uint32_t) mcanConfig->msgRam.pTxEvtFifo )
			| MCAN_TXEFC_EFS(mcanConfig->nmbrTxEvtFifoElmts);  
	// watermark interrupt off
	mcan->MCAN_TXBC = MAILBOX_ADDRESS( (uint32_t) mcanConfig->msgRam.pTxDedBuf ) 
			| MCAN_TXBC_NDTB(mcanConfig->nmbrTxDedBufElmts) 
			| MCAN_TXBC_TFQS(mcanConfig->nmbrTxFifoQElmts);
	mcan->MCAN_RXESC = ((mcanConfig->rxBufElmtSize >> (29-MCAN_RXESC_RBDS_Pos)) & 
						MCAN_RXESC_RBDS_Msk) |
						((mcanConfig->rxFifo1ElmtSize >> (29-MCAN_RXESC_F1DS_Pos)) &
						MCAN_RXESC_F1DS_Msk) |
						((mcanConfig->rxFifo0ElmtSize >> (29-MCAN_RXESC_F0DS_Pos)) &
					   MCAN_RXESC_F0DS_Msk);
	mcan->MCAN_TXESC = ((mcanConfig->txBufElmtSize >> (29-MCAN_TXESC_TBDS_Pos)) &
				MCAN_TXESC_TBDS_Msk);  
	
	/* Configure Message Filters */
	// ...Disable all standard filters
	pMsgRam = mcanConfig->msgRam.pStdFilts;
	cntr = mcanConfig->nmbrStdFilts;
	while ( cntr > 0 ) {
	  *pMsgRam++ = STD_FILT_SFEC_DISABLE;
	  cntr--;
	}
	// ...Disable all extended filters
	pMsgRam = mcanConfig->msgRam.pExtFilts;
	cntr = mcanConfig->nmbrExtFilts;
	while ( cntr > 0 ) {
	  *pMsgRam = EXT_FILT_EFEC_DISABLE;
	  pMsgRam = pMsgRam + 2;
	  cntr--;
	}
	
	mcan->MCAN_NDAT1 = 0xFFFFFFFF;  // clear new (rx) data flags
	mcan->MCAN_NDAT2 = 0xFFFFFFFF;  // clear new (rx) data flags
	
	regVal32 =  mcan->MCAN_CCCR & ~(MCAN_CCCR_CME_Msk | MCAN_CCCR_CMR_Msk);
	mcan->MCAN_CCCR = regVal32 | MCAN_CCCR_CME_ISO11898_1;      
	mcan->MCAN_CCCR = regVal32 | (MCAN_CCCR_CMR_ISO11898_1 | MCAN_CCCR_CME_ISO11898_1);
	
	__DSB();
	__ISB();
}

/**
 * \brief Enables a FUTURE switch to FD mode (tx & rx payloads up to 64 bytes)  
 * but transmits WITHOUT bit rate switching 
 * INIT must be set - so this should be called between MCAN_Init() and 
 * MCAN_Enable()
 * \param mcanConfig  Pointer to a MCAN instance.
 */
void MCAN_InitFdEnable( const MCan_ConfigType * mcanConfig )
{
	Mcan     * mcan = mcanConfig->pMCan;
	uint32_t   regVal32;
	
	regVal32 =  mcan->MCAN_CCCR & ~MCAN_CCCR_CME_Msk;
	mcan->MCAN_CCCR = regVal32 | MCAN_CCCR_CME(1);
}

/**
 * \brief Enables a FUTURE switch to FD mode (tx & rx payloads up to 64 bytes) and transmits 
 * WITH bit rate switching 
 * INIT must be set - so this should be called between MCAN_Init() and MCAN_Enable()
 * \param mcanConfig  Pointer to a MCAN instance.
 */
void MCAN_InitFdBitRateSwitchEnable( const MCan_ConfigType * mcanConfig )
{
	Mcan     * mcan = mcanConfig->pMCan;
	uint32_t   regVal32;
	
	regVal32 =  mcan->MCAN_CCCR & ~MCAN_CCCR_CME_Msk;
	mcan->MCAN_CCCR = regVal32 | MCAN_CCCR_CME(2);
}

/**
 * \brief Initializes the MCAN in loop back mode.
 * INIT must be set - so this should be called between MCAN_Init() and 
 * MCAN_Enable()
 * \param mcanConfig  Pointer to a MCAN instance.
 */
void MCAN_InitLoopback( const MCan_ConfigType * mcanConfig )
{
	Mcan * mcan = mcanConfig->pMCan;
	
	mcan->MCAN_CCCR |= MCAN_CCCR_TEST_ENABLED;
	//mcan->MCAN_CCCR |= MCAN_CCCR_MON_ENABLED;  // for internal loop back
	mcan->MCAN_TEST |= MCAN_TEST_LBCK_ENABLED;
}

/**
 * \brief Initializes MCAN queue for TX
 * INIT must be set - so this should be called between MCAN_Init() and 
 * MCAN_Enable()
 * \param mcanConfig  Pointer to a MCAN instance.
 */
void MCAN_InitTxQueue( const MCan_ConfigType * mcanConfig )
{
	Mcan * mcan = mcanConfig->pMCan;
	mcan->MCAN_TXBC |= MCAN_TXBC_TFQM;
}

/**
 * \brief Enable MCAN peripheral.
 * INIT must be set - so this should be called between MCAN_Init()
 * \param mcanConfig  Pointer to a MCAN instance.
 */
void MCAN_Enable( const MCan_ConfigType * mcanConfig )
{
	Mcan * mcan = mcanConfig->pMCan;
	mcan->MCAN_CCCR &= ~MCAN_CCCR_INIT_ENABLED;
}

/**
 * \brief Requests switch to Iso11898-1 (standard / classic) mode (tx & rx 
 * payloads up to 8 bytes).
 * \param mcanConfig  Pointer to a MCAN instance.
 */
void MCAN_RequestIso11898_1( const MCan_ConfigType * mcanConfig )
{
	Mcan     * mcan = mcanConfig->pMCan;
	uint32_t   regVal32;
	
	regVal32 =  mcan->MCAN_CCCR & ~MCAN_CCCR_CMR_Msk;
	mcan->MCAN_CCCR = regVal32 | MCAN_CCCR_CMR_ISO11898_1;      
	while ( (mcan->MCAN_CCCR & ( MCAN_CCCR_FDBS | MCAN_CCCR_FDO )) != 0 ) 
		{ /* wait */ }
}

/**
 * \brief Requests switch to FD mode (tx & rx payloads up to 64 bytes) but 
 * transmits WITHOUT bit 
 * rate switching. requested mode should have been enabled at initialization
 * \param mcanConfig  Pointer to a MCAN instance.
 */
void MCAN_RequestFd( const MCan_ConfigType * mcanConfig )
{
	Mcan     * mcan = mcanConfig->pMCan;
	uint32_t   regVal32;
	
	if (( mcan->MCAN_CCCR & MCAN_CCCR_CME_Msk ) == MCAN_CCCR_CME(1) ) {
		regVal32 =  mcan->MCAN_CCCR & ~MCAN_CCCR_CMR_Msk;
		mcan->MCAN_CCCR = regVal32 | MCAN_CCCR_CMR_FD; 
		while ( (mcan->MCAN_CCCR & MCAN_CCCR_FDO) == 0 ) { /* wait */ }
	}
}

/**
 * \brief Request switch to FD mode (tx & rx payloads up to 64 bytes) and 
 * transmits WITH bit rate switching.
 * requested mode should have been enabled at initialization
 * \param mcanConfig  Pointer to a MCAN instance.
 */
void MCAN_RequestFdBitRateSwitch( const MCan_ConfigType * mcanConfig )
{
	Mcan     * mcan = mcanConfig->pMCan;
	uint32_t   regVal32;
	
	if (( mcan->MCAN_CCCR & MCAN_CCCR_CME_Msk ) == MCAN_CCCR_CME(2) ) {
	  regVal32 =  mcan->MCAN_CCCR & ~MCAN_CCCR_CMR_Msk;
	  mcan->MCAN_CCCR = regVal32 | MCAN_CCCR_CMR_FD_BITRATE_SWITCH;
	  while ( (mcan->MCAN_CCCR & ( MCAN_CCCR_FDBS | MCAN_CCCR_FDO )) != 
			( MCAN_CCCR_FDBS | MCAN_CCCR_FDO ) ) { /* wait */ }
	}
}

/**
 * \brief Switch on loop back mode.
 * TEST must be set in MCAN_CCCR - e.g. by a prior call to MCAN_InitLoopback()
 * \param mcanConfig  Pointer to a MCAN instance.
 */
void MCAN_LoopbackOn( const MCan_ConfigType * mcanConfig )
{  
	Mcan * mcan = mcanConfig->pMCan;
	mcan->MCAN_TEST |= MCAN_TEST_LBCK_ENABLED;
}

/**
 * \brief Switch off loop back mode.
 * \param mcanConfig  Pointer to a MCAN instance.
 */
void MCAN_LoopbackOff( const MCan_ConfigType * mcanConfig )
{  
	Mcan * mcan = mcanConfig->pMCan;
	mcan->MCAN_TEST &= ~MCAN_TEST_LBCK_ENABLED;
}

/**
 * \brief Enable message line and message stored to Dedicated Receive Buffer 
 * Interrupt Line.
 * \param mcanConfig  Pointer to a MCAN instance.
 * \param line  Message line.
 */
void MCAN_IEnableMessageStoredToRxDedBuffer( const MCan_ConfigType * mcanConfig, 
		MCan_IntrLineType line )
{
	Mcan * mcan = mcanConfig->pMCan;
	if ( line == CAN_INTR_LINE_0 ) {
		mcan->MCAN_ILS &= ~MCAN_ILS_DRXL;
		mcan->MCAN_ILE |= MCAN_ILE_EINT0;
	} else  {
	// Interrupt Line 1
		mcan->MCAN_ILS |= MCAN_ILS_DRXL;
		mcan->MCAN_ILE |= MCAN_ILE_EINT1;
	}
	mcan->MCAN_IR = MCAN_IR_DRX;  // clear previous flag
	mcan->MCAN_IE |= MCAN_IE_DRXE;  // enable it
}

/**
 * \brief Configures a Dedicated TX Buffer.
 * \param mcanConfig  Pointer to a MCAN instance.
 * \param buffer  Pointer to buffer.
 * \param id  Message ID.
 * \param idType  Type of ID
 * \param dlc  Type of dlc.
 */
uint8_t  * MCAN_ConfigTxDedBuffer( const MCan_ConfigType * mcanConfig, 
		uint8_t buffer, uint32_t id, MCan_IdType idType, MCan_DlcType dlc )
{
	 Mcan * mcan = mcanConfig->pMCan;
	 uint32_t * pThisTxBuf = 0;
	 
	 if ( buffer < mcanConfig->nmbrTxDedBufElmts ) {
		pThisTxBuf = mcanConfig->msgRam.pTxDedBuf + (buffer * 
			(mcanConfig->txBufElmtSize & ELMT_SIZE_MASK));
		if ( idType == CAN_STD_ID ) 
			*pThisTxBuf++ = (( id << 18 ) & ( CAN_11_BIT_ID_MASK << 18 ));
	   else 
			*pThisTxBuf++ = BUFFER_XTD_MASK | ( id & CAN_29_BIT_ID_MASK );
		*pThisTxBuf++ = (uint32_t) dlc << 16;
		/* enable transmit from buffer to set TC interrupt bit in IR, but 
		interrupt will not happen unless TC interrupt is enabled*/
		mcan->MCAN_TXBTIE = ( 1 << buffer) ;
	}
	SCB_CleanInvalidateDCache();
	return (uint8_t *) pThisTxBuf;  // now it points to the data field
}

/**
 * \brief Send Tx buffer.
 * \param mcanConfig  Pointer to a MCAN instance.
 * \param buffer  Pointer to buffer.
 */
void MCAN_SendTxDedBuffer( const MCan_ConfigType * mcanConfig, uint8_t buffer )
{ 
	Mcan * mcan = mcanConfig->pMCan;
	
	if ( buffer < mcanConfig->nmbrTxDedBufElmts ) {
	  mcan->MCAN_TXBAR = ( 1 << buffer );
	}
}

/**
 * \brief Adds Message to TX Fifo / Queue 
 * \param mcanConfig  Pointer to a MCAN instance.
 * \param id  Message ID.
 * \param idType  Type of ID
 * \param dlc  Type of dlc.
 * \param data  Pointer to data.
 */
uint32_t MCAN_AddToTxFifoQ( const MCan_ConfigType * mcanConfig, 
		uint32_t id, MCan_IdType idType, MCan_DlcType dlc, uint8_t * data )
{
	Mcan * mcan = mcanConfig->pMCan;
	uint32_t   putIdx = 255;
	uint32_t * pThisTxBuf = 0;
	uint8_t  * pTxData;
	uint8_t    cnt;
	
	// Configured for FifoQ and FifoQ not full?
	if (( mcanConfig->nmbrTxFifoQElmts > 0 ) && 
			(( mcan->MCAN_TXFQS & MCAN_TXFQS_TFQF ) == 0 )) {
		putIdx = ( mcan->MCAN_TXFQS & MCAN_TXFQS_TFQPI_Msk ) >> MCAN_TXFQS_TFQPI_Pos;
		pThisTxBuf = mcanConfig->msgRam.pTxDedBuf + (putIdx * 
			(mcanConfig->txBufElmtSize & ELMT_SIZE_MASK));
		if ( idType == CAN_STD_ID ) 
			*pThisTxBuf++ = (( id << 18 ) & ( CAN_11_BIT_ID_MASK << 18 ));
		else 
			*pThisTxBuf++ = BUFFER_XTD_MASK | ( id & CAN_29_BIT_ID_MASK );
		*pThisTxBuf++ = (uint32_t) dlc << 16;
		pTxData = (uint8_t *) pThisTxBuf;
		for ( cnt = 0; cnt < dlc ; cnt++ ) {
			*pTxData++ = *data++;
		}
		/* enable transmit from buffer to set TC interrupt bit in IR, but
		interrupt will not happen unless TC interrupt is enabled */
		mcan->MCAN_TXBTIE = ( 1 << putIdx);
		// request to send
		mcan->MCAN_TXBAR = ( 1 << putIdx );
	}
	SCB_CleanInvalidateDCache();
	return putIdx;  // now it points to the data field
}

/**
 * \brief Check if data transmitted from buffer/fifo/queue
 * \param mcanConfig  Pointer to a MCAN instance.
 * \param buffer  Pointer to data buffer.
 */
uint8_t MCAN_IsBufferTxd( const MCan_ConfigType * mcanConfig, uint8_t buffer )
{
	Mcan * mcan = mcanConfig->pMCan;
	
	return ( mcan->MCAN_TXBTO & ( 1 << buffer ) );
}

/**
 * \brief Configure RX Buffer Filter
 * ID must match exactly for a RX Buffer Filter
 * \param mcanConfig  Pointer to a MCAN instance.
 * \param buffer  Pointer to data buffer.
 * \param filter  data of filter.
 * \param idType  Type of ID
 */
void MCAN_ConfigRxBufferFilter( const MCan_ConfigType * mcanConfig, 
		uint32_t buffer, uint32_t filter, uint32_t id, MCan_IdType idType)
{ 
	uint32_t * pThisRxFilt = 0;
	
	if ( buffer < mcanConfig->nmbrRxDedBufElmts ) {
		if ( idType == CAN_STD_ID ) {
			if (( filter < mcanConfig->nmbrStdFilts ) 
					&& ( id <= CAN_11_BIT_ID_MASK )) {
				pThisRxFilt = mcanConfig->msgRam.pStdFilts + filter;
				// 1 word per filter
				*pThisRxFilt = STD_FILT_SFEC_BUFFER | (id << 16) |
						STD_FILT_SFID2_RX_BUFFER | buffer;
			}
		} else {
		// extended ID
			if (( filter < mcanConfig->nmbrExtFilts ) && 
					( id <= CAN_29_BIT_ID_MASK )) {
				pThisRxFilt = mcanConfig->msgRam.pExtFilts + (2 * filter);
				// 2 words per filter
				*pThisRxFilt++ = (uint32_t) EXT_FILT_EFEC_BUFFER | id;
				*pThisRxFilt = EXT_FILT_EFID2_RX_BUFFER | buffer;
			}
		}
	}
	SCB_CleanInvalidateDCache();
}

/**
 * \brief Configure Classic Filter
 * Classic Filters direct accepted messages to a FIFO & include both a ID and
 * a ID mask
 * \param mcanConfig  Pointer to a MCAN instance.
 * \param buffer  Pointer to data buffer.
 * \param fifo   fifo Number.
 * \param filter  data of filter.
 * \param idType  Type of ID
 * \param mask  Mask to be match
 */
void MCAN_ConfigRxClassicFilter( const MCan_ConfigType * mcanConfig, 
		MCan_FifoType fifo, uint8_t filter, uint32_t id, 
		MCan_IdType idType, uint32_t mask )
{ 
	uint32_t * pThisRxFilt = 0;
	uint32_t   filterTemp;
	
	if ( idType == CAN_STD_ID ) {
		if (( filter < mcanConfig->nmbrStdFilts ) && ( id <= CAN_11_BIT_ID_MASK ) 
				&& ( mask <= CAN_11_BIT_ID_MASK )) {
			pThisRxFilt = mcanConfig->msgRam.pStdFilts + filter;  
			// 1 word per filter
			filterTemp = (uint32_t) STD_FILT_SFT_CLASSIC | (id << 16) | mask;
			if ( fifo == CAN_FIFO_0 ) {
				*pThisRxFilt = STD_FILT_SFEC_FIFO0 | filterTemp;
			} else if ( fifo == CAN_FIFO_1 ) {
				*pThisRxFilt = STD_FILT_SFEC_FIFO1 | filterTemp;
			}
		} else { 
			// extended ID
			if (( filter < mcanConfig->nmbrExtFilts ) 
					&& ( id <= CAN_29_BIT_ID_MASK ) 
					&& ( mask <= CAN_29_BIT_ID_MASK )) {
				pThisRxFilt = mcanConfig->msgRam.pExtFilts + (2 * filter);
				// 2 words per filter
				if ( fifo == CAN_FIFO_0 ) {
					*pThisRxFilt++ = EXT_FILT_EFEC_FIFO0 | id;
				} else if ( fifo == CAN_FIFO_0 ) {
					*pThisRxFilt++ = EXT_FILT_EFEC_FIFO1 | id;
				}
				*pThisRxFilt = (uint32_t) EXT_FILT_EFT_CLASSIC | mask;
			}
		}
	}
	SCB_CleanInvalidateDCache();
}

/**
 * \brief check if data received into buffer
 * \param mcanConfig  Pointer to a MCAN instance.
 * \param buffer  Pointer to data buffer.
 */
uint8_t MCAN_IsNewDataInRxDedBuffer( const MCan_ConfigType * mcanConfig, 
								uint8_t buffer )
{
	Mcan * mcan = mcanConfig->pMCan;
	
	SCB_CleanInvalidateDCache();
	
	if ( buffer < 32 ) {
	  return ( mcan->MCAN_NDAT1 & ( 1 << buffer ));
	} else if ( buffer < 64 ) {
	  return ( mcan->MCAN_NDAT1 & ( 1 << (buffer - 32 )));
	}    
	else
	  return 0;
}

/**
 * \brief Get Rx buffer
 * \param mcanConfig  Pointer to a MCAN instance.
 * \param buffer  Pointer to data buffer.
 * \param pRxMailbox  Pointer to rx Mailbox.
 */
void MCAN_GetRxDedBuffer( const MCan_ConfigType * mcanConfig, 
					uint8_t buffer, Mailbox64Type * pRxMailbox )
{
	Mcan     * mcan = mcanConfig->pMCan;
	uint32_t * pThisRxBuf = 0;
	uint32_t   tempRy;  // temp copy of RX buffer word
	uint8_t  * pRxData;
	uint8_t    idx;
	
	SCB_CleanInvalidateDCache();
	
	if ( buffer < mcanConfig->nmbrRxDedBufElmts ) {
		pThisRxBuf = mcanConfig->msgRam.pRxDedBuf 
			+ (buffer * (mcanConfig->rxBufElmtSize & ELMT_SIZE_MASK));
		tempRy = *pThisRxBuf++;  // word R0 contains ID
		if ( tempRy & BUFFER_XTD_MASK ) {
			// extended ID?
			pRxMailbox->info.id = tempRy & BUFFER_EXT_ID_MASK;
		} else {
			// standard ID
			pRxMailbox->info.id = ( tempRy & BUFFER_STD_ID_MASK) >> 18;
		}
		tempRy = *pThisRxBuf++;  // word R1 contains DLC & time stamp
		pRxMailbox->info.length = (tempRy & BUFFER_DLC_MASK) >> 16;
		pRxMailbox->info.timestamp = tempRy & BUFFER_RXTS_MASK;
		// copy the data from the buffer to the mailbox
		pRxData = (uint8_t *) pThisRxBuf;
		for ( idx = 0; idx < pRxMailbox->info.length; idx++ )
			pRxMailbox->data[idx] = *pRxData++;
		/* clear the new data flag for the buffer */
		if ( buffer < 32 ) {
			mcan->MCAN_NDAT1 = ( 1 << buffer );
		} else {
			mcan->MCAN_NDAT1 = ( 1 << (buffer - 32 ));
		}
	}
}

/**
 * \brief Get from the receive FIFO and place in a application mailbox
 * \param mcanConfig  Pointer to a MCAN instance.
 * \param fifo  Fifo Number
 * \param pRxMailbox  Pointer to rx Mailbox.
 * \return: # of fifo entries at the start of the function
 *         0 -> FIFO was empty at start
 *         1 -> FIFO had 1 entry at start, but is empty at finish
 *         2 -> FIFO had 2 entries at start, has 1 entry at finish
 */
uint32_t MCAN_GetRxFifoBuffer( const MCan_ConfigType * mcanConfig, 
		MCan_FifoType fifo, Mailbox64Type * pRxMailbox )
{
	Mcan     * mcan = mcanConfig->pMCan;
	uint32_t * pThisRxBuf = 0;
	uint32_t   tempRy;  // temp copy of RX buffer word
	uint8_t  * pRxData;
	uint8_t    idx;
	uint32_t * fifo_ack_reg;
	uint32_t   get_index;
	uint32_t   fill_level;
	uint32_t   element_size;
	
	SCB_CleanInvalidateDCache();
	
	// default: fifo empty
	fill_level = 0; 
	
	if ( fifo == CAN_FIFO_0 ) {
		get_index = ( mcan->MCAN_RXF0S & MCAN_RXF0S_F0GI_Msk ) >> MCAN_RXF0S_F0GI_Pos;
		fill_level = ( mcan->MCAN_RXF0S & MCAN_RXF0S_F0FL_Msk ) >> MCAN_RXF0S_F0FL_Pos;
		pThisRxBuf = mcanConfig->msgRam.pRxFifo0;
		element_size = mcanConfig->rxFifo0ElmtSize & ELMT_SIZE_MASK;
		fifo_ack_reg = (uint32_t *) &mcan->MCAN_RXF0A;
	} else if ( fifo == CAN_FIFO_1 ) {
		get_index = ( mcan->MCAN_RXF1S & MCAN_RXF1S_F1GI_Msk ) >> MCAN_RXF1S_F1GI_Pos;
		fill_level = ( mcan->MCAN_RXF1S & MCAN_RXF1S_F1FL_Msk ) >> MCAN_RXF1S_F1FL_Pos;
		pThisRxBuf = mcanConfig->msgRam.pRxFifo1;
		element_size = mcanConfig->rxFifo1ElmtSize & ELMT_SIZE_MASK;
		fifo_ack_reg = (uint32_t *) &mcan->MCAN_RXF1A;
	}
	
	if ( fill_level > 0 ) {
		pThisRxBuf = pThisRxBuf + (get_index * element_size);
		tempRy = *pThisRxBuf++;  // word R0 contains ID
		if ( tempRy & BUFFER_XTD_MASK ) {
			// extended ID?
			pRxMailbox->info.id = tempRy & BUFFER_EXT_ID_MASK;
		} else {
			// standard ID
			pRxMailbox->info.id = ( tempRy & BUFFER_STD_ID_MASK) >> 18;
		}
		tempRy = *pThisRxBuf++;  // word R1 contains DLC & timestamps
		pRxMailbox->info.length = (tempRy & BUFFER_DLC_MASK) >> 16;
		pRxMailbox->info.timestamp = tempRy & BUFFER_RXTS_MASK;
		/* copy the data from the buffer to the mailbox */
		pRxData = (uint8_t *) pThisRxBuf;
		for ( idx = 0; idx < pRxMailbox->info.length; idx++ )
			pRxMailbox->data[idx] = *pRxData++;
		// acknowledge reading the fifo entry
		*fifo_ack_reg = get_index;
		/* return entries remaining in FIFO */
	}
	return ( fill_level );
}

/**@}*/

