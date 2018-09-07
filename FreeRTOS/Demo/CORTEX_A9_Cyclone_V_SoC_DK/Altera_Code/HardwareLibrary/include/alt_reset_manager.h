/*! \file
 *  Altera - SoC Reset Manager
 */

/******************************************************************************
*
* Copyright 2013 Altera Corporation. All Rights Reserved.
* 
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
* 
* 1. Redistributions of source code must retain the above copyright notice,
* this list of conditions and the following disclaimer.
* 
* 2. Redistributions in binary form must reproduce the above copyright notice,
* this list of conditions and the following disclaimer in the documentation
* and/or other materials provided with the distribution.
* 
* 3. The name of the author may not be used to endorse or promote products
* derived from this software without specific prior written permission.
* 
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER "AS IS" AND ANY EXPRESS OR
* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE DISCLAIMED. IN NO
* EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
* OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
* INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
* CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
* IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
* OF SUCH DAMAGE.
* 
******************************************************************************/

#ifndef __ALT_RESET_MGR_H__
#define __ALT_RESET_MGR_H__

#include "hwlib.h"
#include <stdbool.h>

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*! \addtogroup RST_MGR The Reset Manager
 *
 * The Reset Manager API defines functions for accessing, configuring, and
 * controlling the HPS reset behavior.
 * @{
 */

/******************************************************************************/
/*! \addtogroup RST_MGR_STATUS Reset Status
 *
 * This functional group provides information on various aspects of SoC reset
 * status and timeout events.
 *
 * @{
 */

/******************************************************************************/
/*!
 * This type definition enumerates the set of reset causes and timeout events as
 * register mask values.
 */
typedef enum ALT_RESET_EVENT_e
{
    /*! Power-On Voltage Detector Cold Reset */
    ALT_RESET_EVENT_PORVOLTRST          = 0x00000001,

    /*! nPOR Pin Cold Reset                  */
    ALT_RESET_EVENT_NPORPINRST          = 0x00000002,

    /*! FPGA Core Cold Reset                 */
    ALT_RESET_EVENT_FPGACOLDRST         = 0x00000004,

    /*! CONFIG_IO Cold Reset                 */
    ALT_RESET_EVENT_CONFIGIOCOLDRST     = 0x00000008,

    /*! Software Cold Reset                  */
    ALT_RESET_EVENT_SWCOLDRST           = 0x00000010,

    /*! nRST Pin Warm Reset                  */
    ALT_RESET_EVENT_NRSTPINRST          = 0x00000100,

    /*! FPGA Core Warm Reset                 */
    ALT_RESET_EVENT_FPGAWARMRST         = 0x00000200,

    /*! Software Warm Reset                  */
    ALT_RESET_EVENT_SWWARMRST           = 0x00000400,

    /*! MPU Watchdog 0 Warm Reset            */
    ALT_RESET_EVENT_MPUWD0RST           = 0x00001000,

    /*! MPU Watchdog 1 Warm Reset            */
    ALT_RESET_EVENT_MPUWD1RST           = 0x00002000,

    /*! L4 Watchdog 0 Warm Reset             */
    ALT_RESET_EVENT_L4WD0RST            = 0x00004000,

    /*! L4 Watchdog 1 Warm Reset             */
    ALT_RESET_EVENT_L4WD1RST            = 0x00008000,

    /*! FPGA Core Debug Reset                */
    ALT_RESET_EVENT_FPGADBGRST          = 0x00040000,

    /*! DAP Debug Reset                      */
    ALT_RESET_EVENT_CDBGREQRST          = 0x00080000,

    /*! SDRAM Self-Refresh Timeout           */
    ALT_RESET_EVENT_SDRSELFREFTIMEOUT   = 0x01000000,

    /*! FPGA manager handshake Timeout       */
    ALT_RESET_EVENT_FPGAMGRHSTIMEOUT    = 0x02000000,

    /*! SCAN manager handshake Timeout       */
    ALT_RESET_EVENT_SCANHSTIMEOUT       = 0x04000000,

    /*! FPGA handshake Timeout               */
    ALT_RESET_EVENT_FPGAHSTIMEOUT       = 0x08000000,

    /*! ETR Stall Timeout                    */
    ALT_RESET_EVENT_ETRSTALLTIMEOUT     = 0x10000000
} ALT_RESET_EVENT_t;

/******************************************************************************/
/*!
 * Gets the reset and timeout events that caused the last reset.
 *
 * The ALT_RESET_EVENT_t enumeration values should be used to selectively
 * examine the returned reset cause(s).
 *
 * \returns     A mask of the reset and/or timeout events that caused the last
 *              reset.
 */
uint32_t alt_reset_event_get(void);

/******************************************************************************/
/*!
 * Clears the reset and timeout events that caused the last reset.
 *
 * \param       event_mask
 *              A mask of the selected reset and timeout events to clear in the
 *              Reset Manager \e stat register. The mask selection can be formed
 *              using the ALT_RESET_EVENT_t enumeration values.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_reset_event_clear(uint32_t event_mask);

/*! @} */

/******************************************************************************/
/*! \addtogroup RST_MGR_CTRL Reset Control
 *
 * This functional group provides global and selective reset control for the SoC
 * and its constituent modules.
 *
 * @{
 */

/******************************************************************************/
/*!
 * Initiate a cold reset of the SoC.
 *
 * If this function is successful, then it should never return.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_reset_cold_reset(void);

/******************************************************************************/
/*!
 * Initiate a warm reset of the SoC.
 *
 * Perform a hardware sequenced warm reset of the SoC. A hardware sequenced
 * reset handshake with certain modules can optionally be requested in an
 * attempt to ensure an orderly reset transition.
 *
 * \param       warm_reset_delay
 *              Specifies the number of cycles after the Reset Manager releases
 *              the Clock Manager reset before releasing any other hardware
 *              controlled resets. Value must be greater than 16 and less than
 *              256.
 *
 * \param       nRST_pin_clk_assertion
 *              Specifies that number of clock cycles (osc1_clk?) to externally
 *              assert the warm reset pin (nRST). 0 <= \e nRST_pin_clk_assertion <=
 *              (2**20 - 1). A value of 0 prevents any assertion of nRST.
 *
 * \param       sdram_refresh
 *              Controls whether the contents of SDRAM survive a hardware
 *              sequenced warm reset. The reset manager requests the SDRAM
 *              controller to put SDRAM devices into self-refresh mode before
 *              asserting warm reset signals. An argument value of \b true
 *              enables the option, \b false disables the option.
 *
 * \param       fpga_mgr_handshake
 *              Controls whether a handshake between the reset manager and FPGA
 *              manager occurs before a warm reset. The handshake is used to
 *              warn the FPGA manager that a warm reset is imminent so it can
 *              prepare for it by driving its output clock to a quiescent state
 *              to avoid glitches. An argument value of \b true enables the
 *              option, \b false disables the option.
 *
 * \param       scan_mgr_handshake
 *              Controls whether a handshake between the reset manager and scan
 *              manager occurs before a warm reset. The handshake is used to
 *              warn the scan manager that a warm reset is imminent so it can
 *              prepare for it by driving its output clock to a quiescent state
 *              to avoid glitches. An argument value of \b true enables the
 *              option, \b false disables the option.
 *
 * \param       fpga_handshake
 *              Controls whether a handshake between the reset manager and the
 *              FPGA occurs before a warm reset. The handshake is used to warn
 *              the FPGA that a warm reset is imminent so that the FPGA prepare
 *              for the reset event in soft IP. An argument value of \b true
 *              enables the option, \b false disables the option.
 *
 * \param       etr_stall
 *              Controls whether the ETR is requested to idle its AXI master
 *              interface (i.e. finish outstanding transactions and not initiate
 *              any more) to the L3 Interconnect before a warm reset. An
 *              argument value of \b true enables the option, \b false disables
 *              the option.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_reset_warm_reset(uint32_t warm_reset_delay,
                                     uint32_t nRST_pin_clk_assertion,
                                     bool sdram_refresh,
                                     bool fpga_mgr_handshake,
                                     bool scan_mgr_handshake,
                                     bool fpga_handshake,
                                     bool etr_stall);

#if 0
/*! \addtogroup RST_MGR_MPU 
 *
 * This functional group provides reset control for the Cortex-A9 MPU module.
 *
 * @{
 */

/*! @} */

/*! \addtogroup RST_MGR_PERIPH
 *
 * This functional group provides inidividual reset control for the HPS
 * peripheral modules.
 *
 * @{
 */

/*! @} */

/*! \addtogroup RST_MGR_BRG
 *
 * This functional group provides inidividual reset control for the bridge
 * interfaces between the HPS and FPGA.
 *
 * @{
 */

/*! @} */

/*! \addtogroup RST_MGR_MISC
 *
 * This functional group provides inidividual reset control for miscellaneous
 * HPS modules.
 *
 * @{
 */

/*! @} */

#endif

/*! @} */

/*! @} */

#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALT_RESET_MGR_H__ */
