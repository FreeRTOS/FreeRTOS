//*******************************************************************************
//  Provides Functions to Initialize the UCS/FLL and clock sources
//    File: hal_ucs.c
//
//    Texas Instruments
//
//    Version 1.2
//    11/24/09
//
//    V1.0  Initial Version
//    V1.1  Added timeout function
//    V1.1  Added parameter for XTDrive
//*******************************************************************************


#ifndef __hal_UCS
#define __hal_UCS

#include <stdint.h>
#include "hal_macros.h"

/*************************************************************************
* MACROS
**************************************************************************/

/* Select source for FLLREF  e.g. SELECT_FLLREF(SELREF__XT1CLK) */
#define SELECT_FLLREF(source) st(UCSCTL3 = (UCSCTL3 & ~(SELREF_7)) | (source);) 
/* Select source for ACLK    e.g. SELECT_ACLK(SELA__XT1CLK) */
#define SELECT_ACLK(source)   st(UCSCTL4 = (UCSCTL4 & ~(SELA_7))   | (source);) 
/* Select source for MCLK    e.g. SELECT_MCLK(SELM__XT2CLK) */
#define SELECT_MCLK(source)   st(UCSCTL4 = (UCSCTL4 & ~(SELM_7))   | (source);) 
/* Select source for SMCLK   e.g. SELECT_SMCLK(SELS__XT2CLK) */
#define SELECT_SMCLK(source)  st(UCSCTL4 = (UCSCTL4 & ~(SELS_7))   | (source);) 
/* Select source for MCLK and SMCLK e.g. SELECT_MCLK_SMCLK(SELM__DCOCLK + SELS__DCOCLK) */
#define SELECT_MCLK_SMCLK(sources) st(UCSCTL4 = (UCSCTL4 & ~(SELM_7 + SELS_7)) | (sources);)

/* set ACLK/x */
#define ACLK_DIV(x)         st(UCSCTL5 = (UCSCTL5 & ~(DIVA_7)) | (DIVA__##x);)     
/* set MCLK/x */
#define MCLK_DIV(x)         st(UCSCTL5 = (UCSCTL5 & ~(DIVM_7)) | (DIVM__##x);)     
/* set SMCLK/x */
#define SMCLK_DIV(x)        st(UCSCTL5 = (UCSCTL5 & ~(DIVS_7)) | (DIVS__##x);)     
/* Select divider for FLLREF  e.g. SELECT_FLLREFDIV(2) */
#define SELECT_FLLREFDIV(x) st(UCSCTL3 = (UCSCTL3 & ~(FLLREFDIV_7))|(FLLREFDIV__##x);) 

//************************************************************************
// Defines
//************************************************************************

#define UCS_STATUS_OK     0
#define UCS_STATUS_ERROR  1

//====================================================================
/**
 * Startup routine for 32kHz Cristal on LFXT1
 *
 * \param xtdrive: Bits defining the LFXT drive mode after startup
 *
*/
extern void LFXT_Start(uint16_t xtdrive);

//====================================================================
/**
 * Startup routine for 32kHz Cristal on LFXT1 with timeout counter
 *
 * \param xtdrive: Bits defining the LFXT drive mode after startup
 * \param timeout: value for the timeout counter
 *
*/
extern uint16_t LFXT_Start_Timeout(uint16_t xtdrive, uint16_t timeout);

//====================================================================
/**
 * Startup routine for XT1
 *
 * \param xtdrive: Bits defining the XT drive mode
 *
*/
extern void XT1_Start(uint16_t xtdrive);

//====================================================================
/**
 * Startup routine for XT1 with timeout counter
 *
 * \param xtdrive: Bits defining the XT drive mode
 * \param timeout: value for the timeout counter
 *
*/
extern uint16_t XT1_Start_Timeout(uint16_t xtdrive, uint16_t timeout);

//====================================================================
/**
 * Use XT1 in Bypasss mode
 *
*/
extern void XT1_Bypass(void);

//====================================================================
/**
 * Startup routine for XT2
 *
 * \param xtdrive: Bits defining the XT drive mode
 *
*/
extern void XT2_Start(uint16_t xtdrive);

//====================================================================
/**
 * Startup routine for XT2 with timeout counter
 *
 * \param xtdrive: Bits defining the XT drive mode
 * \param timeout: value for the timeout counter
 *
*/
extern uint16_t XT2_Start_Timeout(uint16_t xtdrive, uint16_t timeout);

//====================================================================
/**
 * Use XT2 in Bypasss mode for MCLK
 *
*/
extern void XT2_Bypass(void);

//====================================================================
/**
  * Initializes FLL of the UCS and wait till settled
  *
  * \param fsystem  required system frequency (MCLK) in kHz
  * \param ratio    ratio between fsystem and FLLREFCLK
  */
extern void Init_FLL_Settle(uint16_t fsystem, uint16_t ratio);


//====================================================================
/**
  * Initializes FLL of the UCS
  *
  * \param fsystem  required system frequency (MCLK) in kHz
  * \param ratio    ratio between fsystem and FLLREFCLK
  */
static void Init_FLL(uint16_t fsystem, uint16_t ratio);

#endif /* __hal_UCS */
