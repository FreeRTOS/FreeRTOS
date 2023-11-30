/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
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
 *  Interface for configuration the Analog-to-Digital Converter (AFEC) peripheral.
 *
 *  \section Usage
 *
 *  -# Configurate the pins for AFEC.
 *  -# Initialize the AFEC with AFEC_Initialize().
 *  -# Set AFEC clock and timing with AFEC_SetClock() and AFEC_SetTiming().
 *  -# Select the active channel using AFEC_EnableChannel().
 *  -# Start the conversion with AFEC_StartConversion().
 *  -# Wait the end of the conversion by polling status with AFEC_GetStatus().
 *  -# Finally, get the converted data using AFEC_GetConvertedData() or 
 * AFEC_GetLastConvertedData().
 *
*/
#ifndef _AFEC_
#define _AFEC_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include <assert.h>
#include <stdint.h>

/*------------------------------------------------------------------------------
 *         Definitions
 *------------------------------------------------------------------------------*/

/* -------- AFEC_MR : (AFEC Offset: 0x04) AFEC Mode Register -------- */
#define AFEC_MR_SETTLING_Pos 20
#define AFEC_MR_SETTLING_Msk (0x3u << AFEC_MR_SETTLING_Pos) 
/**< \brief (AFEC_MR) Trigger Selection */
#define   AFEC_MR_SETTLING_AST3 (0x0u << 20) 
/**< \brief (AFEC_MR) ADC_SETTLING_AST3 3 periods of AFEClock */
#define   AFEC_MR_SETTLING_AST5 (0x1u << 20) 
/**< \brief (AFEC_MR) ADC_SETTLING_AST5 5 periods of AFEClock */
#define   AFEC_MR_SETTLING_AST9 (0x2u << 20) 
/**< \brief (AFEC_MR) ADC_SETTLING_AST9 9 periods of AFEClock*/
#define   AFEC_MR_SETTLING_AST17 (0x3u << 20) 
/**< \brief (AFEC_MR) ADC_SETTLING_AST17  17 periods of AFEClock*/

/***************************** Single Trigger Mode ****************************/
#define AFEC_EMR_STM_Pos 25
#define AFEC_EMR_STM_Msk (0x1u << AFEC_EMR_STM_Pos) 
/**< \brief (AFEC_EMR) Single Trigger Mode */
#define   AFEC_EMR_STM_MULTI_TRIG (0x0u << 25) 
/**< \brief (AFEC_EMR) Single Trigger Mode: Multiple triggers are required to 
	get an averaged result. */
#define   AFEC_EMR_STM_SINGLE_TRIG (0x1u << 25) 
/**< \brief (AFEC_EMR) Single Trigger Mode: Only a Single Trigger is required
	to get an averaged value. */

/***************************** TAG of the AFEC_LDCR Register ******************/
#define AFEC_EMR_TAG_Pos 24
#define AFEC_EMR_TAG_Msk (0x1u << AFEC_EMR_TAG_Pos) 
/**< \brief (AFEC_EMR) TAG of the AFEC_LDCR Register */
#define   AFEC_EMR_TAG_CHNB_ZERO (0x0u << 24) 
/**< \brief (AFEC_EMR) TAG of the AFEC_LDCR Register: Sets CHNB to zero 
in AFEC_LDCR. */
#define   AFEC_EMR_TAG_APPENDS (0x1u << 24) 
/**< \brief (AFEC_EMR) TAG of the AFEC_LDCR Register: Appends the channel 
number to the conversion result in AFEC_LDCR register. */

/***************************** Compare All Channels ******************/
#define AFEC_EMR_CMPALL_Pos 9
#define AFEC_EMR_CMPALL_Msk (0x1u << AFEC_EMR_TAG_Pos) 
/**< \brief (AFEC_EMR) Compare All Channels */
#define   AFEC_EMR_CMPALL_ONE_CHANNEL_COMP (0x0u << 9) 
/**< \brief (AFEC_EMR) Compare All Channels: Only channel indicated in 
CMPSEL field is compared. */
#define   AFEC_EMR_CMPALL_ALL_CHANNELS_COMP  (0x1u << 9) 
/**< \brief (AFEC_EMR) Compare All Channels: All channels are compared. */

#define AFEC_ACR_PGA0_ON     (0x1u << 2)
#define AFEC_ACR_PGA1_ON     (0x1u << 3)

#ifdef __cplusplus
 extern "C" {
#endif

/*------------------------------------------------------------------------------
 *         Macros function of register access
 *------------------------------------------------------------------------------*/

#define AFEC_GetModeReg( pAFEC )                ((pAFEC)->AFEC_MR)
#define AFEC_SetModeReg( pAFEC, mode )          ((pAFEC)->AFEC_MR = mode)

#define AFEC_GetExtModeReg( pAFEC )             ((pAFEC)->AFEC_EMR)
#define AFEC_SetExtModeReg( pAFEC, mode )       ((pAFEC)->AFEC_EMR = mode)

#define AFEC_StartConversion( pAFEC )           ((pAFEC)->AFEC_CR = AFEC_CR_START)

#define AFEC_EnableChannel( pAFEC, dwChannel )    {\
			(pAFEC)->AFEC_CHER = (1 << (dwChannel));\
		}

#define AFEC_DisableChannel(pAFEC, dwChannel)  {\
			(pAFEC)->AFEC_CHDR = (1 << (dwChannel));\
		}

#define AFEC_EnableIt(pAFEC, dwMode)            {\
			(pAFEC)->AFEC_IER = (dwMode);\
		}

#define AFEC_DisableIt(pAFEC, dwMode)           {\
			(pAFEC)->AFEC_IDR = (dwMode);\
		}

#define AFEC_SetChannelGain(pAFEC,dwMode)       {\
			(pAFEC)->AFEC_CGR = dwMode;\
		}

#define AFEC_EnableDataReadyIt(pAFEC)         ((pAFEC)->AFEC_IER = AFEC_IER_DRDY)

#define AFEC_GetStatus(pAFEC)                 ((pAFEC)->AFEC_ISR)

#define AFEC_GetCompareMode(pAFEC)            (((pAFEC)->AFEC_EMR)& (AFEC_EMR_CMPMODE_Msk))

#define AFEC_GetChannelStatus(pAFEC)          ((pAFEC)->AFEC_CHSR)

#define AFEC_GetInterruptMaskStatus(pAFEC)    ((pAFEC)->AFEC_IMR)

#define AFEC_GetLastConvertedData(pAFEC)      ((pAFEC)->AFEC_LCDR)

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/
extern void AFEC_Initialize( Afec* pAFEC, uint32_t dwId );
extern uint32_t AFEC_SetClock( Afec* pAFEC, uint32_t dwPres, uint32_t dwMck );
extern void AFEC_SetTiming( Afec* pAFEC, uint32_t dwStartup, uint32_t dwTracking, 
	uint32_t dwSettling );
extern void AFEC_SetTrigger( Afec* pAFEC, uint32_t dwTrgSel );
extern void AFEC_SetAnalogChange( Afec* pAFE, uint8_t bEnDis );
extern void AFEC_SetSleepMode( Afec* pAFEC, uint8_t bEnDis );
extern void AFEC_SetFastWakeup( Afec* pAFEC, uint8_t bEnDis );
extern void AFEC_SetSequenceMode( Afec* pAFEC, uint8_t bEnDis );
extern void AFEC_SetSequence( Afec* pAFEC, uint32_t dwSEQ1, uint32_t dwSEQ2 );
extern void AFEC_SetSequenceByList( Afec* pAFEC, uint8_t ucChList[], uint8_t ucNumCh );
extern void AFEC_SetTagEnable( Afec* pAFEC, uint8_t bEnDis );
extern void AFEC_SetCompareChannel( Afec* pAFEC, uint32_t dwChannel ) ;
extern void AFEC_SetCompareMode( Afec* pAFEC, uint32_t dwMode ) ;
extern void AFEC_SetComparisonWindow( Afec* pAFEC, uint32_t dwHi_Lo ) ;
extern uint8_t AFEC_CheckConfiguration( Afec* pAFEC, uint32_t dwMcK ) ;
extern uint32_t AFEC_GetConvertedData( Afec* pAFEC, uint32_t dwChannel ) ;
extern void AFEC_SetStartupTime( Afec* pAFEC, uint32_t dwUs );
extern void AFEC_SetTrackingTime( Afec* pAFEC, uint32_t dwNs );
extern void AFEC_SetAnalogOffset( Afec *pAFE, uint32_t dwChannel,uint32_t aoffset );
extern void AFEC_SetAnalogControl( Afec *pAFE, uint32_t control);
#ifdef __cplusplus
}
#endif

#endif /* #ifndef _AFEC_ */

