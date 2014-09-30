/*! \file
 *  Altera - SoC FPGA FPGA/HPS Bridge Management
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

#ifndef __ALT_BRG_MGR_H__
#define __ALT_BRG_MGR_H__

#include "hwlib.h"

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/******************************************************************************/
/*! \addtogroup ALT_BRIDGE The AXI Bridge Manager
 *
 * The functions in this group manage access, configuration, and control of the
 * AXI bridges between the FPGA and HPS.
 * 
 * @{
 */

/******************************************************************************/
/*!
 * This type definition enumerates the AXI bridge interfaces between the FPGA
 * and HPS.
 */
typedef enum ALT_BRIDGE_e
{
    ALT_BRIDGE_F2H,             /*!< FPGA-to-HPS AXI bridge providing a
                                 *   high-performance, statically configurable
                                 *   width interface that gives the FPGA the
                                 *   ability to:
                                 *   * master transactions to slaves in the HPS
                                 *   * have full visibility into the HPS address space
                                 *   * access the coherent memory interface (ACP)
                                 *
                                 *   The width (32/64/128 bits) of this bridge
                                 *   is statically configurable at design time
                                 *   using \e Quartus.
                                 */
    ALT_BRIDGE_H2F,             /*!< HPS-to-FPGA AXI bridge providing a
                                 *   statically configurable width,
                                 *   high-performance master interface to the
                                 *   FPGA fabric. The bridge provides a 1GB
                                 *   address space and gives any master in the
                                 *   HPS system access to logic, peripherals,
                                 *   and memory implemented in the FPGA.
                                 */
    ALT_BRIDGE_LWH2F            /*!< Lightweight HPS-to-FPGA AXI bridge
                                 *   providing a secondary, fixed-width, smaller
                                 *   address space, lower-performance master
                                 *   interface to the FPGA fabric. The bridge
                                 *   provides a 2MB address space and gives any
                                 *   master in the HPS access to logic,
                                 *   peripherals, and memory implemented in the
                                 *   FPGA fabric. The bridge master exposed to
                                 *   the FPGA fabric has a fixed data width of
                                 *   32 bits.
                                 *
                                 *   The bridge provides clock crossing logic to
                                 *   allow the logic in the FPGA to run
                                 *   asynchronous to the HPS. The bridge
                                 *   simplifies the process of connecting the
                                 *   HPS to soft logic. Soft logic can even be
                                 *   designed to support only a subset of the
                                 *   full AXI protocol that the bridge
                                 *   supports. Use the lightweight HPS-to-FPGA
                                 *   bridge for high-latency, low-bandwidth
                                 *   traffic, such as memory-mapped register
                                 *   accesses of FPGA peripherals. This approach
                                 *   diverts traffic from the high-performance
                                 *   HPS-to-FPGA bridge, which can improve
                                 *   overall performance.
                                 */
} ALT_BRIDGE_t;

/******************************************************************************/
/*!
 * Type definition for a callback function prototype used by the
 * alt_bridge_init() bridge initialization function to determine whether the
 * FPGA is ready to begin transactions across the bridge interface.
 *
 * The implementation of the callback function is user defined allowing the user
 * to define a flexible signaling protocol for the FPGA to indicate its
 * readiness to begin transactions across the initialized bridge interface.
 *
 * The range of values returned by the callback function may be extended per the
 * user defined FPGA readiness signaling protocol but any return value other
 * than ALT_E_SUCCESS will be interpreted by the alt_bridge_init() bridge
 * initialization function as an indication that the FPGA is not ready to
 * commence bridge interface transactions.
 *
 * \param       user_arg
 *              This is a user defined parameter available to pass additional
 *              data that might be needed to support the user defined FPGA
 *              readiness signaling protocol.
 *
 * \retval      ALT_E_SUCCESS   The FPGA is ready to commence bridge interface 
 *                              transactions.
 * \retval      ALT_E_ERROR     An error has occurred. The FPGA is not ready to
 *                              commence bridge interface transactions.
 * \retval      ALT_E_TMO       The FPGA failed to signal a ready to commence
 *                              bridge interface transactions indication before
 *                              the response timeout period expired.
 */
typedef ALT_STATUS_CODE (*alt_bridge_fpga_is_ready_t)(void* user_arg);

/******************************************************************************/
/*!
 * Initialize the bridge for bus transactions by bringing up the interface in a
 * safe, controlled sequence.
 *
 * The following actions are performed as part of the process of initializing
 * the bridge interface for transactions:
 *
 * * Sets and holds bridge interface in reset.
 * * Ensures that the bridge interface is ready by asserting that:
 *   - FPGA is powered and configured (i.e. in USER mode).
 *   - Bridge interface clock is ready and stable.
 *   - FPGA soft IP is ready for transactions across the bridge interface.
 * * Releases bridge interface from reset.
 *
 * The mechanism used by alt_bridge_init() to determine whether the FPGA soft IP
 * is ready to begin bus transactions across the interface is the user defined
 * callback \e fpga_is_ready.
 *
 * \internal
 * This process of software controlled bring-up of HPS/FPGA interfaces is
 * detailed in <em> Hammerhead-P HPS FPGA Interface NPP, Section 4 Software
 * Bring-up/Tear-down</em>.
 * \endinternal
 *
 * \param       bridge
 *              The bridge interface to initialize.
 *
 * \param       fpga_is_ready
 *              A pointer to a user defined callback function to determine
 *              whether the FPGA is ready to commence bridge interface
 *              transactions. If NULL is passed, then bridge interface
 *              initialization proceeds without making a determination of
 *              whether the FPGA is ready to commence bridge interface
 *              transactions or not.
 *
 * \param       user_arg
 *              A user defined argument value for passing support data to the \e
 *              fpga_is_ready callback function.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_bridge_init(ALT_BRIDGE_t bridge,
                                alt_bridge_fpga_is_ready_t fpga_is_ready,
                                void* user_arg);

/******************************************************************************/
/*!
 * Type definition for a callback function prototype used by the
 * alt_bridge_uninit() function to conduct a handshake protocol with the FPGA
 * notifying it that the bridge interface is being taken down.
 *
 * The callback function implementation is user defined and allows the user to
 * implement a flexible handshake notification protocol with the FPGA to allow
 * an orderly interface shutdown prior to the bridge being taken down.
 *
 * The handshake protocol is user defined but normally consists of two parts:
 * * The processor notifies the FPGA soft IP that the bridge interface is being
 *   taken down. The notification mechanism used to signal the FPGA is user
 *   defined.
 * * The process waits for an acknowledgement response from the FPGA.
 *
 * The range of return values for the callback function may be extended per the
 * user defined handshake notification protocol but any return value other than
 * ALT_E_SUCCESS will be interpreted by the alt_bridge_uninit() function as an
 * indication that the handshake protocol was unsuccessful.
 *
 * \param       user_arg
 *              This is a user defined parameter available to pass additional
 *              data that might be needed to support the user defined handshake
 *              notification protocol.
 *
 * \retval      ALT_E_SUCCESS   The handshake notification protocol was successful.
 * \retval      ALT_E_ERROR     An error has occurred. The handshake notification 
 *                              protocol was unsuccessful.
 * \retval      ALT_E_TMO       The handshake notification protocol failed
 *                              because a response timeout period expired.
 */
typedef ALT_STATUS_CODE (*alt_bridge_teardown_handshake_t)(void* user_arg);

/******************************************************************************/
/*!
 * Uninitialize the bridge by tearing down the interface in a safe and
 * controlled sequence.
 *
 * The process of taking down the bridge interface entails:
 * * Optional: Conduct teardown handshake notification protocol 
 *   - Bridge Manager informs FPGA that the bridge interface is being torn down.
 *   - Bridge Manager waits for FPGA response to notification.
 * * Processor waits for the completion of outstanding transactions on the AXI
 *   bridge. Note, that HPS has no mechanism to track outstanding AXI transactions;
 *   this needs to be provided by the customer design.
 * * Places and holds the bridge interface in reset.
 *
 * The mechanism used by alt_bridge_uninit() to initiate the handshake
 * notification to the FPGA soft IP that the bridge interface is being taken
 * down is the user defined \e handshake callback.
 *
 * \internal
 * This function implements the software controlled tear-down procedure detailed
 * in <em> Hammerhead-P HPS FPGA Interface NPP, Section 4 Software
 * Bring-up/Tear-down</em>.
 * \endinternal
 *
 * \param       bridge
 *              The bridge interface to uninitialize.
 *
 * \param       handshake
 *              A pointer to a user defined tear-down handshake protocol. If
 *              NULL is passed, then the bridge interface take down proceeds
 *              without conducting any handshake notification protocol.
 *
 * \param       user_arg
 *              A user defined argument value for passing support data to the
 *              \e teardown_hs callback function.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_bridge_uninit(ALT_BRIDGE_t bridge,
                                  alt_bridge_teardown_handshake_t handshake,
                                  void* user_arg);

/*! @} */

#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALT_BRG_MGR_H__ */
