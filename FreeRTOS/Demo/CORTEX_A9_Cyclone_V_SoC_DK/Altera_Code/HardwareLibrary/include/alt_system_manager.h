/*! \file
 *  Altera - SoC FPGA System Manager
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

#ifndef __ALT_SYS_MGR_H__
#define __ALT_SYS_MGR_H__

#include "hwlib.h"

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/******************************************************************************/
/*! \addtogroup SYS_MGR The System Manager
 *
 * The System Manager API defines functions for control of system operation and
 * for other modules requiring external control as part of system integration.
 * 
 * The major functional APIs include:
 * * HPS I/O configuration and pin muxing
 * * External control of other modules
 * * Control and status of ECC
 * * Fault injection for ECC and parity errors.
 * @{
 */

/******************************************************************************/
/*! \addtogroup SYS_MGR_FPGA_INTERFACE FPGA Interface Group
 *
 * These functions provide enable/disable control and operational status of the
 * signal interfaces between the FPGA and HPS.  Selective enabling/disabling of
 * interfaces may be required under the following scenarios:
 * * Interfaces that are associated with an HPS module but that are not disabled
 *   when the HPS module associated with the interface is put into reset.
 * * An HPS module accepts signals from the FPGA and those signals might
 *   otherwise interfere with the normal operation of the HPS module.
 * @{
 */

/******************************************************************************/
/*!
 * This type definition enumerates the FPGA to HPS signal interfaces controlled
 * by the functions in this API group.
 */
typedef enum ALT_FPGA_INTERFACE_e
{
    ALT_FPGA_INTERFACE_GLOBAL,      /*!< All interfaces between the FPGA and
                                     *   HPS. If ALT_FPGA_INTERFACE_ALL is disabled
                                     *   then all of the individual and module
                                     *   interfaces between the FPGA and HPS are
                                     *   disabled regardless of their separate
                                     *   enable/disable settings. If
                                     *   ALT_FPGA_INTERFACE_ALL is enabled then each
                                     *   individual and module interface between
                                     *   the FPGA and HPS may be separately
                                     *   enabled/disabled.
                                     */
    ALT_FPGA_INTERFACE_RESET_REQ,   /*!< The reset request interface. This
                                     *   interface allows logic in the FPGA to
                                     *   request HPS resets. The following reset
                                     *   request signals from the FPGA fabric to
                                     *   HPS are part of this interface:
                                     *   * \b f2h_cold_rst_req_n - Triggers a HPS cold reset
                                     *   * \b f2h_warm_rst_req_n - Triggers a HPS warm reset
                                     *   * \b f2h_dbg_rst_req_n - Triggers a HPS debug reset
                                     */
    ALT_FPGA_INTERFACE_JTAG_ENABLE, /*!< The JTAG enable interface. This
                                     *   interface allows logic in the FPGA
                                     *   fabric to disable the HPS JTAG
                                     *   operation.
                                     */
    ALT_FPGA_INTERFACE_CONFIG_IO,   /*!< The CONFIG_IO interface. This interface
                                     *   allows the FPGA JTAG TAP controller to
                                     *   execute the CONFIG_IO instruction and
                                     *   configure all device I/O (FPGA and
                                     *   HPS).
                                     */
    ALT_FPGA_INTERFACE_BSCAN,       /*!< The boundary-scan interface. This
                                     *   interface allows the FPGA JTAG TAP
                                     *   controller to execute boundary-scan
                                     *   instructions.
                                     */
    ALT_FPGA_INTERFACE_TRACE,       /*!< The trace interface. This interface
                                     *   allows the HPS debug logic to send
                                     *   trace data to logic in the FPGA.
                                     */
    ALT_FPGA_INTERFACE_DBG_APB,     /*!< (Private) The debug APB interface. This
                                     *   interface allows the HPS debug logic to
                                     *   communicate with debug APB slaves in
                                     *   the FPGA fabric.
                                     */
    ALT_FPGA_INTERFACE_STM,         /*!< The STM event interface. This interface
                                     *   allows logic in the FPGA to trigger
                                     *   events to the HPS STM debug module.
                                     */
    ALT_FPGA_INTERFACE_CTI,         /*!< The Cross Trigger Interface (CTI). This
                                     *   interface allows logic in the FPGA to
                                     *   send triggers to HPS debug logic. Note
                                     *   that this does not prevent the HPS
                                     *   debug logic from sending triggers to
                                     *   the FPGA.
                                     */
    ALT_FPGA_INTERFACE_EMAC0,       /*!< Signal interface from the FPGA to the
                                     *   EMAC0 module.
                                     */
    ALT_FPGA_INTERFACE_EMAC1,       /*!< Signal interface from the FPGA to the
                                     *   EMAC1 module.
                                     */
    ALT_FPGA_INTERFACE_SPIM0,       /*!< (Private) Signal interface from the
                                     *   FPGA to the SPI Master 0 module.
                                     */
    ALT_FPGA_INTERFACE_SPIM1,       /*!< (Private) Signal interface from the
                                     *   FPGA to the SPI Master 0 module.
                                     */
    ALT_FPGA_INTERFACE_NAND,        /*!< (Private) Signal interface from the
                                     *   FPGA to the NAND Flash Controller
                                     *   module.
                                     */
    ALT_FPGA_INTERFACE_SDMMC        /*!< (Private) Signal interface from the
                                     *   FPGA to the SD/MMC Controller module.
                                     */
} ALT_FPGA_INTERFACE_t;

/******************************************************************************/
/*!
 * Disables the specified FPGA to HPS signal interface.
 *
 * Isolates and disables the designated FPGA/HPS signal interface. User is
 * responsible for determining that the interface is inactive before disabling
 * it.
 *
 * \param       intfc
 *              The interface to disable.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The \e intfc argument designates an invalid
 *                              FPGA/HPS signal interface.
 */
ALT_STATUS_CODE alt_fpga_interface_disable(ALT_FPGA_INTERFACE_t intfc);

/******************************************************************************/
/*!
 * Enables the specified FPGA to HPS signal interface.
 *
 * \param       intfc
 *              The interface to enable.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The \e intfc argument designates an invalid
 *                              FPGA/HPS signal interface.
 */
ALT_STATUS_CODE alt_fpga_interface_enable(ALT_FPGA_INTERFACE_t intfc);

/******************************************************************************/
/*!
 * Return whether the specified FPGA/HPS signal interface is enabled or not.
 *
 * \param       intfc
 *              The interface to enable.
 *
 * \retval      ALT_E_TRUE      The interface is enabled.
 * \retval      ALT_E_FALSE     The interface is not enabled.
 * \retval      ALT_E_BAD_ARG   The \e intfc argument designates an invalid
 *                              FPGA/HPS signal interface.
 */
ALT_STATUS_CODE alt_fpga_interface_is_enabled(ALT_FPGA_INTERFACE_t intfc);

/*! @} */

/*! @} */

#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALT_SYS_MGR_H__ */
