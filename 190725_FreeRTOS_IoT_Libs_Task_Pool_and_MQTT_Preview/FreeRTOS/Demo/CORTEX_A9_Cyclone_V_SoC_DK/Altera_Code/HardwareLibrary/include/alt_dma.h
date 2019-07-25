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

#ifndef __ALT_DMA_H__
#define __ALT_DMA_H__

#include "hwlib.h"
#include "alt_dma_common.h"
#include "alt_dma_program.h"

#ifdef __cplusplus
extern "C"
{
#endif /* __cplusplus */

/*!
 * \addtogroup ALT_DMA DMA Controller API
 *
 * This module defines the API for configuration and use of the general purpose
 * DMA controller for the SoC. The DMA controller is an instance of the ARM
 * Corelink DMA Controller (DMA-330).
 *
 * References:
 *  * ARM DDI 0424C, CoreLink DMA Controller DMA-330 Technical Reference
 *    Manual.
 *  * ARM DAI 0239A, Application Note 239 Example Programs for the CoreLink
 *    DMA Controller DMA-330.
 *  * Altera, Cyclone V Device Handbook Volume 3: Hard Processor System
 *    Technical Reference Manual, DMA Controller.
 *
 * @{
 */

/*!
 * \addtogroup ALT_DMA_COMPILE DMA API Compile Options
 *
 * This API provides control over the compile time inclusion of selected
 * modules. This can allow for a smaller resulting binary.
 *
 * @{
 */

#ifndef ALT_DMA_PERIPH_PROVISION_16550_SUPPORT
#define ALT_DMA_PERIPH_PROVISION_16550_SUPPORT (1)
#endif

#ifndef ALT_DMA_PERIPH_PROVISION_QSPI_SUPPORT
#define ALT_DMA_PERIPH_PROVISION_QSPI_SUPPORT (1)
#endif

/*!
 * @}
 */

/*!
 * \addtogroup ALT_DMA_CSR DMA API for Configuration, Control, and Status
 *
 * This API provides functions for configuration, control, and status queries
 * of the DMA controller.
 *
 * @{
 */

/*!
 * This type definition enumerates the operational states that the DMA manager
 * may have.
 */
typedef enum ALT_DMA_MANAGER_STATE_e
{
    ALT_DMA_MANAGER_STATE_STOPPED     = 0, /*!< Stopped */
    ALT_DMA_MANAGER_STATE_EXECUTING   = 1, /*!< Executing */
    ALT_DMA_MANAGER_STATE_CACHE_MISS  = 2, /*!< Cache Miss */
    ALT_DMA_MANAGER_STATE_UPDATING_PC = 3, /*!< Updating PC */
    ALT_DMA_MANAGER_STATE_WFE         = 4, /*!< Waiting for Event */
    ALT_DMA_MANAGER_STATE_FAULTING    = 15 /*!< Faulting */
}
ALT_DMA_MANAGER_STATE_t;

/*!
 * This type definition enumerates the operational states that a DMA channel
 * may have.
 */
typedef enum ALT_DMA_CHANNEL_STATE_e
{
    ALT_DMA_CHANNEL_STATE_STOPPED             = 0,  /*!< Stopped */
    ALT_DMA_CHANNEL_STATE_EXECUTING           = 1,  /*!< Executing */
    ALT_DMA_CHANNEL_STATE_CACHE_MISS          = 2,  /*!< Cache Miss */
    ALT_DMA_CHANNEL_STATE_UPDATING_PC         = 3,  /*!< Updating PC */
    ALT_DMA_CHANNEL_STATE_WFE                 = 4,  /*!< Waiting for Event */
    ALT_DMA_CHANNEL_STATE_AT_BARRIER          = 5,  /*!< At Barrier */
    ALT_DMA_CHANNEL_STATE_WFP                 = 7,  /*!< Waiting for Peripheral */
    ALT_DMA_CHANNEL_STATE_KILLING             = 8,  /*!< Killing */
    ALT_DMA_CHANNEL_STATE_COMPLETING          = 9,  /*!< Completing */
    ALT_DMA_CHANNEL_STATE_FAULTING_COMPLETING = 14, /*!< Faulting Completing */
    ALT_DMA_CHANNEL_STATE_FAULTING            = 15  /*!< Faulting */
}
ALT_DMA_CHANNEL_STATE_t;

/*!
 * This type definition enumerates the possible fault status that the DMA
 * manager can have as a register mask.
 */
typedef enum ALT_DMA_MANAGER_FAULT_e
{
    /*!
     * The DMA manager abort occured because of an instruction issued through
     * the debug interface.
     */
    ALT_DMA_MANAGER_FAULT_DBG_INSTR       = (int32_t)(1UL << 30),

    /*!
     * The DMA manager instruction fetch AXI bus response was not OKAY.
     */
    ALT_DMA_MANAGER_FAULT_INSTR_FETCH_ERR = (int32_t)(1UL << 16),

    /*!
     * The DMA manager attempted to execute DMAWFE or DMASEV with
     * inappropriate security permissions.
     */
    ALT_DMA_MANAGER_FAULT_MGR_EVNT_ERR    = (int32_t)(1UL <<  5),

    /*!
     * The DMA manager attempted to execute DMAGO with inappropriate security
     * permissions.
     */
    ALT_DMA_MANAGER_FAULT_DMAGO_ERR       = (int32_t)(1UL <<  4),

    /*!
     * The DMA manager attempted to execute an instruction operand that was
     * not valid for the DMA configuration.
     */
    ALT_DMA_MANAGER_FAULT_OPERAND_INVALID = (int32_t)(1UL <<  1),

    /*!
     * The DMA manager attempted to execute an undefined instruction.
     */
    ALT_DMA_MANAGER_FAULT_UNDEF_INSTR     = (int32_t)(1UL <<  0)
}
ALT_DMA_MANAGER_FAULT_t;

/*!
 * This type definition enumerates the possible fault status that a channel
 * may have as a register mask.
 */
typedef enum ALT_DMA_CHANNEL_FAULT_e
{
    /*!
     * The DMA channel has locked up due to resource starvation.
     */
    ALT_DMA_CHANNEL_FAULT_LOCKUP_ERR          = (int32_t)(1UL << 31),

    /*!
     * The DMA channel abort occured because of an instruction issued through
     * the debug interface.
     */
    ALT_DMA_CHANNEL_FAULT_DBG_INSTR           = (int32_t)(1UL << 30),

    /*!
     * The DMA channel data read AXI bus reponse was not OKAY.
     */
    ALT_DMA_CHANNEL_FAULT_DATA_READ_ERR       = (int32_t)(1UL << 18),

    /*!
     * The DMA channel data write AXI bus response was not OKAY.
     */
    ALT_DMA_CHANNEL_FAULT_DATA_WRITE_ERR      = (int32_t)(1UL << 17),

    /*!
     * The DMA channel instruction fetch AXI bus response was not OKAY.
     */
    ALT_DMA_CHANNEL_FAULT_INSTR_FETCH_ERR     = (int32_t)(1UL << 16),

    /*!
     * The DMA channel MFIFO did not have the data for the DMAST instruction.
     */
    ALT_DMA_CHANNEL_FAULT_ST_DATA_UNAVAILABLE = (int32_t)(1UL << 13),

    /*!
     * The DMA channel MFIFO is too small to hold the DMALD instruction data,
     * or too small to servic the DMAST instruction request.
     */
    ALT_DMA_CHANNEL_FAULT_MFIFO_ERR           = (int32_t)(1UL << 12),

    /*!
     * The DMA channel in non-secure state attempted to perform a secure read
     * or write.
     */
    ALT_DMA_CHANNEL_FAULT_CH_RDWR_ERR         = (int32_t)(1UL <<  7),

    /*!
     * The DMA channel in non-secure state attempted to execute the DMAWFP,
     * DMALDP, DMASTP, or DMAFLUSHP instruction involving a secure peripheral.
     */
    ALT_DMA_CHANNEL_FAULT_CH_PERIPH_ERR       = (int32_t)(1UL <<  6),

    /*!
     * The DMA channel in non-secure state attempted to execute the DMAWFE or
     * DMASEV instruction for a secure event or secure interrupt (if
     * applicable).
     */
    ALT_DMA_CHANNEL_FAULT_CH_EVNT_ERR         = (int32_t)(1UL <<  5),

    /*!
     * The DMA channel attempted to execute an instruction operand that was
     * not valid for the DMA configuration.
     */
    ALT_DMA_CHANNEL_FAULT_OPERAND_INVALID     = (int32_t)(1UL <<  1),

    /*!
     * The DMA channel attempted to execute an undefined instruction.
     */
    ALT_DMA_CHANNEL_FAULT_UNDEF_INSTR         = (int32_t)(1UL <<  0)
}
ALT_DMA_CHANNEL_FAULT_t;

/*!
 * This type definition enumerates the possible DMA event-interrupt behavior
 * option selections when a DMASEV instruction is executed.
 */
typedef enum ALT_DMA_EVENT_SELECT_e
{
    /*!
     * If the DMA controller executes DMASEV for the event-interrupt resource
     * then the DMA sends the event to all of the channel threads.
     */
    ALT_DMA_EVENT_SELECT_SEND_EVT,

    /*!
     * If the DMA controller executes DMASEV for the event-interrupt resource
     * then the DMA sets the \b irq[N] HIGH.
     */
    ALT_DMA_EVENT_SELECT_SIG_IRQ
}
ALT_DMA_EVENT_SELECT_t;

/*!
 * This type enumerates the DMA peripheral interface MUX selection options
 * available.
 */
typedef enum ALT_DMA_PERIPH_MUX_e
{
    /*! 
     * Accept the reset default MUX selection
     */ 
    ALT_DMA_PERIPH_MUX_DEFAULT = 0,

    /*!
     * Select FPGA as the peripheral interface
     */
    ALT_DMA_PERIPH_MUX_FPGA    = 1,

    /*!
     * Select CAN as the peripheral interface
     */
    ALT_DMA_PERIPH_MUX_CAN     = 2
}
ALT_DMA_PERIPH_MUX_t;

/*!
 * This type defines the structure used to specify the configuration of the
 * security states and peripheral interface MUX selections for the DMA
 * controller.
 */
typedef struct ALT_DMA_CFG_s
{
    /*!
     * DMA Manager security state configuration.
     */
    ALT_DMA_SECURITY_t manager_sec;

    /*!
     * DMA interrupt output security state configurations. Security state
     * configurations are 0-based index-aligned with the enumeration values
     * ALT_DMA_EVENT_0 through ALT_DMA_EVENT_7 of the ALT_DMA_EVENT_t type.
     */
    ALT_DMA_SECURITY_t irq_sec[8];

    /*!
     * Peripheral request interface security state configurations. Security
     * state configurations are 0-based index-aligned with the enumeration
     * values of the ALT_DMA_PERIPH_t type.
     */
    ALT_DMA_SECURITY_t periph_sec[32];

    /*!
     * DMA Peripheral Register Interface MUX Selections. MUX selections are
     * 0-based index-aligned with the enumeration values
     * ALT_DMA_PERIPH_FPGA_4_OR_CAN0_IF1 through
     * ALT_DMA_PERIPH_FPGA_7_OR_CAN1_IF2 of the ALT_DMA_PERIPH_t type.
     */
    ALT_DMA_PERIPH_MUX_t periph_mux[4];
}
ALT_DMA_CFG_t;

/*!
 * Initialize the DMA controller.
 *
 * Initializes the DMA controller by setting the necessary control values to
 * establish the security state and MUXed peripheral request interface selection
 * configurations before taking the DMA controller out of reset.
 *
 * After the DMA is initialized, the following conditions hold true:
 *  * All DMA channel threads are in the Stopped state.
 *  * All DMA channel threads are available for allocation.
 *  * DMA Manager thread is waiting for an instruction from either APB
 *    interface.
 *  * The security state configurations of the DMA Manager, interrupt outputs,
 *    and peripheral request interfaces are established and immutable until the
 *    DMA is reset.
 *  * The MUXed peripheral request interface selection configurations are
 *    established and immutable until the DMA is reset.
 *
 * \param       dma_cfg
 *              A pointer to a ALT_DMA_CFG_t structure containing the desired
 *              DMA controller security state and peripheral request interface
 *              MUX selections.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_dma_init(const ALT_DMA_CFG_t * dma_cfg);

/*!
 * Uninitializes the DMA controller.
 *
 * Uninitializes the DMA controller by killing any running channel threads and
 * putting the DMA controller into reset.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_dma_uninit(void);

/*!
 * Allocate a DMA channel resource for use.
 *
 * \param       channel
 *              A DMA controller channel.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_dma_channel_alloc(ALT_DMA_CHANNEL_t channel);

/*!
 * Allocate a free DMA channel resource for use if there are any.
 *
 * \param       allocated
 *              [out] A pointer to an output parameter that will contain the
 *              channel allocated.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed. An unallocated channel
 *                              may not be available at the time of the API
 *                              call.
 */
ALT_STATUS_CODE alt_dma_channel_alloc_any(ALT_DMA_CHANNEL_t * allocated);

/*!
 * Free a DMA channel resource for reuse.
 *
 * \param       channel
 *              The DMA controller channel resource to free.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed. The channel may not be in
 *                              the STOPPED state.
 */
ALT_STATUS_CODE alt_dma_channel_free(ALT_DMA_CHANNEL_t channel);

/*!
 * Start execution of a DMA microcode program on the specified DMA channel
 * thread resource.
 *
 * \param       channel
 *              The DMA channel thread used to execute the microcode program.
 *
 * \param       pgm
 *              The DMA microcode program.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_dma_channel_exec(ALT_DMA_CHANNEL_t channel,
                                     ALT_DMA_PROGRAM_t * pgm);

/*!
 * Kill (abort) execution of any microcode program executing on the specified
 * DMA channel thread resource.
 *
 * Terminates the channel thread of execution by issuing a DMAKILL instruction
 * using the DMA APB slave interface.
 *
 * \param       channel
 *              The DMA channel thread to abort any executing microcode program
 *              on.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_TMO       Timeout waiting for the channel to change into
 *                              KILLING or STOPPED state.
 */
ALT_STATUS_CODE alt_dma_channel_kill(ALT_DMA_CHANNEL_t channel);

/*!
 * Returns the current register value for the given DMA channel.
 *
 * \param       channel
 *              The DMA channel thread to abort any executing microcode program
 *              on.
 *
 * \param       reg
 *              Register to get the value for.
 *
 * \param       val
 *              [out] The current value of the requested register.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The specified channel or register is invalid.
 */
ALT_STATUS_CODE alt_dma_channel_reg_get(ALT_DMA_CHANNEL_t channel,
                                        ALT_DMA_PROGRAM_REG_t reg, uint32_t * val);

/*!
 * Signals the occurrence of an event or interrupt, using the specified event
 * number.
 *
 * Causes the CPU to issue a DMASEV instruction using the DMA APB slave
 * interface.
 *
 * The Interrupt Enable Register (INTEN) register is used to control if each
 * event-interrupt resource is either an event or an interrupt. The INTEN
 * register sets the event-interrupt resource to function as an:
 *  * Event - The DMAC generates an event for the specified event-interrupt
 *            resource. When the DMAC executes a DMAWFE instruction for the
 *            same event-interrupt resource then it clears the event.
 *  * Interrupt - The DMAC sets the \b IRQ[N] signal high, where
 *                \e evt_num is the number of the specified event
 *                resource. The interrupt must be cleared after being handled.
 *
 * When the configured to generate an event, this function may be used to
 * restart one or more waiting DMA channels (i.e. having executed a DMAWFE
 * instruction).
 *
 * See the following sections from the \e ARM DDI 0424C, CoreLink DMA Controller
 * DMA-330 Technical Reference Manual for implementation details and use cases:
 *  * 2.5.1, Issuing Instructions to the DMAC using a Slave Interface
 *  * 2.7, Using Events and Interrupts
 *
 * \param       evt_num   
 *              A DMA event-interrupt resource. Allowable event values may be
 *              ALT_DMA_EVENT_0 .. ALT_DMA_EVENT_7 but ALT_DMA_EVENT_ABORT is
 *              not.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given event number is invalid.
 */
ALT_STATUS_CODE alt_dma_send_event(ALT_DMA_EVENT_t evt_num);

/*!
 * Returns the current operational state of the DMA manager thread.
 *
 * \param       state
 *              [out] Pointer to an output parameter to contain the DMA
 *              channel thread state.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_dma_manager_state_get(ALT_DMA_MANAGER_STATE_t * state);

/*!
 * Returns the current operational state of the specified DMA channel thread.
 *
 * \param       channel
 *              The DMA channel thread to return the operational state of.
 *
 * \param       state
 *              [out] Pointer to an output parameter to contain the DMA
 *              channel thread state.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given channel identifier is invalid.
 */
ALT_STATUS_CODE alt_dma_channel_state_get(ALT_DMA_CHANNEL_t channel,
                                          ALT_DMA_CHANNEL_STATE_t * state);

/*!
 * Return the current fault status of the DMA manager thread.
 *
 * \param       fault
 *              [out] Pointer to an output parameter to contain the DMA
 *              manager fault status.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_dma_manager_fault_status_get(ALT_DMA_MANAGER_FAULT_t * fault);

/*!
 * Return the current fault status of the specified DMA channel thread.
 *
 * \param       channel
 *              The DMA channel thread to return the fault status of.
 *
 * \param       fault
 *              [out] Pointer to an output parameter to contain the DMA
 *              channel fault status.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given channel identifier is invalid.
 */
ALT_STATUS_CODE alt_dma_channel_fault_status_get(ALT_DMA_CHANNEL_t channel,
                                                 ALT_DMA_CHANNEL_FAULT_t * fault);

/*!
 * Select whether the DMA controller sends the specific event to all channel
 * threads or signals an interrupt using the corressponding \b irq when a DMASEV
 * instruction is executed for the specified event-interrupt resource number.
 *
 * \param       evt_num
 *              The event-interrupt resource number. Valid values are
 *              ALT_DMA_EVENT_0 .. ALT_DMA_EVENT_7 and ALT_DMA_EVENT_ABORT.
 *
 * \param       opt
 *              The desired behavior selection for \e evt_num when a DMASEV is
 *              executed.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given selection identifier is invalid.
 */
ALT_STATUS_CODE alt_dma_event_int_select(ALT_DMA_EVENT_t evt_num,
                                         ALT_DMA_EVENT_SELECT_t opt);

/*!
 * Returns the status of the specified event-interrupt resource.
 *
 * Returns ALT_E_TRUE if event is active or \b irq[N] is HIGH and returns
 * ALT_E_FALSE if event is inactive or \b irq[N] is LOW.
 *
 * \param       evt_num
 *              The event-interrupt resource number. Valid values are
 *              ALT_DMA_EVENT_0 .. ALT_DMA_EVENT_7 and ALT_DMA_EVENT_ABORT.
 *
 * \retval      ALT_E_TRUE      Event is active or \b irq[N] is HIGH.
 * \retval      ALT_E_FALSE     Event is inactive or \b irq[N] is LOW.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given event identifier is invalid.
 */
ALT_STATUS_CODE alt_dma_event_int_status_get_raw(ALT_DMA_EVENT_t evt_num);

/*!
 * Returns the status of the specified interrupt resource.
 *
 * Returns ALT_E_TRUE if interrupt is active and therfore \b irq[N] is HIGH and
 * returns ALT_E_FALSE if interrupt is inactive and therfore \b irq[N] is LOW.
 *
 * \param       irq_num
 *              The interrupt resource number. Valid values are
 *              ALT_DMA_EVENT_0 .. ALT_DMA_EVENT_7 and ALT_DMA_EVENT_ABORT.
 *
 * \retval      ALT_E_TRUE      Event is active or \b irq[N] is HIGH.
 * \retval      ALT_E_FALSE     Event is inactive or \b irq[N] is LOW.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given event identifier is invalid.
 */
ALT_STATUS_CODE alt_dma_int_status_get(ALT_DMA_EVENT_t irq_num);

/*!
 * Clear the active (HIGH) status of the specified interrupt resource.
 *
 * If the specified interrupt is HIGH, then sets \b irq[N] to LOW if the
 * event-interrupt resource is configured (see: alt_dma_event_int_enable()) 
 * to signal an interrupt. Otherwise, the status of \b irq[N] does not change.
 *
 * \param       irq_num
 *              The interrupt resource number. Valid values are
 *              ALT_DMA_EVENT_0 .. ALT_DMA_EVENT_7 and ALT_DMA_EVENT_ABORT.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given event identifier is invalid.
 */
ALT_STATUS_CODE alt_dma_int_clear(ALT_DMA_EVENT_t irq_num);

/*!
 * @}
 */

/*!
 * \addtogroup ALT_DMA_STD_OPS DMA API for Standard Operations
 *
 * The functions in this group provide common DMA operations for common bulk
 * data transfers between:
 *  * Memory to Memory
 *  * Zero to Memory
 *  * Memory to Peripheral
 *  * Peripheral to Memory
 *
 * All DMA operations are asynchronous. The following are the ways to receive
 * notification of a DMA transfer complete operation:
 *  * Use alt_dma_channel_state_get() and poll for the 
 *    ALT_DMA_CHANNEL_STATE_STOPPED status.
 *  * In conjunction with the interrupt API, use DMA events to signal an
 *    interrupt. The event first must be configured to signal an interrupt
 *    using alt_dma_event_int_select(). Configure the DMA program to send an
 *    event.
 *  * Construct a custom program which waits for a particular event number by
 *    assemblying a DMAWFE using alt_dma_program_DMAWFE(). Then run the custom
 *    program on a different channel. The custom program will wait until the
 *    DMA program sends the event. Configure the DMA program to send an event.
 *
 * Cache related maintenance on the source and/or destinatino buffer are not
 * handled the DMA API and are the responsibility of the programmer. This is
 * because the DMA API does not have visibility into the current configuration
 * of the MMU or know about any special considerations regarding the source
 * and/or destination memory. The following are some example scenarios and
 * cache maintenance related precautions that may need to be taken:
 *  * alt_dma_memory_to_memory(): Source buffer should be cleaned or purged,
 *    destination buffer should be invalidated.
 *  * alt_dma_zero_to_memory(): Destination buffer should be invalidated.
 *  * alt_dma_memory_to_register(): Source buffer should be cleaned or purged.
 *  * alt_dma_register_to_memory(): Destination buffer should be invalidated.
 *  * alt_dma_memory_to_periph(): Source buffer should be cleaned or purged.
 *  * alt_dma_periph_to_memory(): Destination buffer should be invalidated.
 *
 * @{
 */

/*!
 * Uses the DMA engine to asynchronously copy the specified memory from the
 * given source address to the given destination address.
 *
 * Overlapping memory regions are not supported.
 *
 * \param       channel
 *              The DMA channel thread to use for the transfer.
 *
 * \param       program
 *              An allocated DMA program buffer to use for the life of the
 *              transfer.
 *
 * \param       dest
 *              The destination memory address to copy to.
 *
 * \param       src
 *              The source memory address to copy from.
 *
 * \param       size
 *              The size of the transfer in bytes.
 *
 * \param       send_evt
 *              If set to true, the DMA engine will be instructed to send an
 *              event upon completion or fault.
 *
 * \param       evt
 *              If send_evt is true, the event specified will be sent.
 *              Otherwise the parameter is ignored.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given channel or event identifier (if
 *                              used) is invalid, or the memory regions
 *                              specified are overlapping.
 */
ALT_STATUS_CODE alt_dma_memory_to_memory(ALT_DMA_CHANNEL_t channel,
                                         ALT_DMA_PROGRAM_t * program,
                                         void * dest,
                                         const void * src,
                                         size_t size,
                                         bool send_evt,
                                         ALT_DMA_EVENT_t evt);

/*!
 * Uses the DMA engine to asynchronously zero out the specified memory buffer.
 *
 * \param       channel
 *              The DMA channel thread to use for the transfer.
 *
 * \param       program
 *              An allocated DMA program buffer to use for the life of the
 *              transfer.
 *
 * \param       buf
 *              The buffer memory address to zero out.
 *
 * \param       size
 *              The size of the buffer in bytes.
 *
 * \param       send_evt
 *              If set to true, the DMA engine will be instructed to send an
 *              event upon completion or fault.
 *
 * \param       evt
 *              If send_evt is true, the event specified will be sent.
 *              Otherwise the parameter is ignored.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given channel or event identifier (if
 *                              used) is invalid.
 */
ALT_STATUS_CODE alt_dma_zero_to_memory(ALT_DMA_CHANNEL_t channel,
                                       ALT_DMA_PROGRAM_t * program,
                                       void * buf,
                                       size_t size,
                                       bool send_evt,
                                       ALT_DMA_EVENT_t evt);

/*!
 * Uses the DMA engine to asynchronously transfer the contents of a memory
 * buffer to a keyhole register.
 *
 * \param       channel
 *              The DMA channel thread to use for the transfer.
 *
 * \param       program
 *              An allocated DMA program buffer to use for the life of the
 *              transfer.
 *
 * \param       dst_reg
 *              The address of the register to write buffer to.
 *
 * \param       src_buf
 *              The address of the memory buffer for the data.
 *
 * \param       count
 *              The number of transfers to make.
 *
 * \param       register_width_bits
 *              The width of the register to transfer to in bits. Valid values
 *              are 8, 16, 32, and 64.
 *
 * \param       send_evt
 *              If set to true, the DMA engine will be instructed to send an
 *              event upon completion or fault.
 *
 * \param       evt
 *              If send_evt is true, the event specified will be sent.
 *              Otherwise the parameter is ignored.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given channel, event identifier (if used),
 *                              or register width are invalid, or if the
 *                              destination register or source buffer is
 *                              unaligned to the register width.
 */
ALT_STATUS_CODE alt_dma_memory_to_register(ALT_DMA_CHANNEL_t channel,
                                           ALT_DMA_PROGRAM_t * program,
                                           void * dst_reg,
                                           const void * src_buf,
                                           size_t count,
                                           uint32_t register_width_bits,
                                           bool send_evt,
                                           ALT_DMA_EVENT_t evt);

/*!
 * Uses the DMA engine to asynchronously transfer the contents of a keyhole
 * register to a memory buffer.
 *
 * \param       channel
 *              The DMA channel thread to use for the transfer.
 *
 * \param       program
 *              An allocated DMA program buffer to use for the life of the
 *              transfer.
 *
 * \param       dst_buf
 *              The address of the memory buffer to copy to.
 *
 * \param       src_reg
 *              The address of the keyhole register to read from.
 *
 * \param       count
 *              The number of transfers to make.
 *
 * \param       register_width_bits
 *              The width of the register to transfer to in bits. Valid values
 *              are 8, 16, 32, and 64.
 *
 * \param       send_evt
 *              If set to true, the DMA engine will be instructed to send an
 *              event upon completion or fault.
 *
 * \param       evt
 *              If send_evt is true, the event specified will be sent.
 *              Otherwise the parameter is ignored.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given channel, event identifier (if used),
 *                              or register width are invalid, or if the
 *                              destination buffer or source register is
 *                              unaligned to the register width.
 */
ALT_STATUS_CODE alt_dma_register_to_memory(ALT_DMA_CHANNEL_t channel,
                                           ALT_DMA_PROGRAM_t * program,
                                           void * dst_buf,
                                           const void * src_reg,
                                           size_t count,
                                           uint32_t register_width_bits,
                                           bool send_evt,
                                           ALT_DMA_EVENT_t evt);

/*!
 * Uses the DMA engine to asynchronously copy memory from the given source
 * address to the specified peripheral. Because different peripheral has
 * different characteristics, individual peripherals need to be explicitly
 * supported.
 *
 * The following lists the peripheral IDs supported by this API:
 *  * ALT_DMA_PERIPH_QSPI_FLASH_TX
 *  * ALT_DMA_PERIPH_UART0_TX
 *  * ALT_DMA_PERIPH_UART1_TX
 *
 * \param       channel
 *              The DMA channel thread to use for the transfer.
 *
 * \param       program
 *              An allocated DMA program buffer to use for the life of the
 *              transfer.
 *
 * \param       dest
 *              The destination peripheral to copy memory to.
 *
 * \param       src
 *              The source memory address to copy from.
 *
 * \param       size
 *              The size of the transfer in bytes.
 *
 * \param       periph_info
 *              A pointer to a peripheral specific data structure. The
 *              following list shows what data structure should be used for
 *              peripherals:
 *               * ALT_DMA_PERIPH_QSPI_FLASH_TX: This parameter is ignored.
 *               * ALT_DMA_PERIPH_UART0_TX: Use a pointer to the
 *                 ALT_16550_HANDLE_t used to interact with that UART.
 *               * ALT_DMA_PERIPH_UART1_TX: Use a pointer to the
 *                 ALT_16550_HANDLE_t used to interact with that UART.
 *
 * \param       send_evt
 *              If set to true, the DMA engine will be instructed to send an
 *              event upon completion or fault.
 *
 * \param       evt
 *              If send_evt is true, the event specified will be sent.
 *              Otherwise the parameter is ignored.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given channel, peripheral, or event
 *                              identifier (if used) is invalid.
 *
 * \internal
 * Priority peripheral IDs to be supported:
 *  * ALT_DMA_PERIPH_FPGA_0
 *  * ALT_DMA_PERIPH_FPGA_1
 *  * ALT_DMA_PERIPH_FPGA_2
 *  * ALT_DMA_PERIPH_FPGA_3
 *  * ALT_DMA_PERIPH_FPGA_4
 *  * ALT_DMA_PERIPH_FPGA_5
 *  * ALT_DMA_PERIPH_FPGA_6
 *  * ALT_DMA_PERIPH_FPGA_7
 *  * ALT_DMA_PERIPH_I2C0_TX
 *  * ALT_DMA_PERIPH_I2C1_TX
 *  * ALT_DMA_PERIPH_I2C2_TX
 *  * ALT_DMA_PERIPH_I2C3_TX
 *  * ALT_DMA_PERIPH_SPI0_MASTER_TX
 *  * ALT_DMA_PERIPH_SPI0_SLAVE_TX
 *  * ALT_DMA_PERIPH_SPI1_MASTER_TX
 *  * ALT_DMA_PERIPH_SPI1_SLAVE_TX
 * \endinternal
 */
ALT_STATUS_CODE alt_dma_memory_to_periph(ALT_DMA_CHANNEL_t channel,
                                         ALT_DMA_PROGRAM_t * program,
                                         ALT_DMA_PERIPH_t dest,
                                         const void * src,
                                         size_t size,
                                         void * periph_info,
                                         bool send_evt,
                                         ALT_DMA_EVENT_t evt);

/*!
 * Uses the DMA engine to copy memory from the specified peripheral to the
 * given destination address. Because different peripheral has different
 * characteristics, individual peripherals need to be explicitly supported.
 *
 * The following lists the peripheral IDs supported by this API:
 *  * ALT_DMA_PERIPH_QSPI_FLASH_RX
 *  * ALT_DMA_PERIPH_UART0_RX
 *  * ALT_DMA_PERIPH_UART1_RX
 *
 * \param       channel
 *              The DMA channel thread to use for the transfer.
 *
 * \param       program
 *              An allocated DMA program buffer to use for the life of the
 *              transfer.
 *
 * \param       dest
 *              The destination memory address to copy to.
 *
 * \param       src
 *              The source peripheral to copy memory from.
 *
 * \param       size
 *              The size of the transfer in bytes.
 *
 * \param       periph_info
 *              A pointer to a peripheral specific data structure. The
 *              following list shows what data structure should be used for
 *              peripherals:
 *               * ALT_DMA_PERIPH_QSPI_FLASH_RX: This parameter is ignored.
 *               * ALT_DMA_PERIPH_UART0_RX: Use a pointer to the
 *                 ALT_16550_HANDLE_t used to interact with that UART.
 *               * ALT_DMA_PERIPH_UART1_RX: Use a pointer to the
 *                 ALT_16550_HANDLE_t used to interact with that UART.
 *
 * \param       send_evt
 *              If set to true, the DMA engine will be instructed to send an
 *              event upon completion or fault.
 *
 * \param       evt
 *              If send_evt is true, the event specified will be sent.
 *              Otherwise the parameter is ignored.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The given channel, peripheral, or event
 *                              identifier (if used) is invalid.
*
 * \internal
 * Priority peripheral IDs to be supported:
 *  * ALT_DMA_PERIPH_FPGA_0
 *  * ALT_DMA_PERIPH_FPGA_1
 *  * ALT_DMA_PERIPH_FPGA_2
 *  * ALT_DMA_PERIPH_FPGA_3
 *  * ALT_DMA_PERIPH_FPGA_4
 *  * ALT_DMA_PERIPH_FPGA_5
 *  * ALT_DMA_PERIPH_FPGA_6
 *  * ALT_DMA_PERIPH_FPGA_7
 *  * ALT_DMA_PERIPH_I2C0_RX
 *  * ALT_DMA_PERIPH_I2C1_RX
 *  * ALT_DMA_PERIPH_I2C2_RX
 *  * ALT_DMA_PERIPH_I2C3_RX
 *  * ALT_DMA_PERIPH_SPI0_MASTER_RX
 *  * ALT_DMA_PERIPH_SPI0_SLAVE_RX
 *  * ALT_DMA_PERIPH_SPI1_MASTER_RX
 *  * ALT_DMA_PERIPH_SPI1_SLAVE_RX
 * \endinternal
 */
ALT_STATUS_CODE alt_dma_periph_to_memory(ALT_DMA_CHANNEL_t channel,
                                         ALT_DMA_PROGRAM_t * program,
                                         void * dest,
                                         ALT_DMA_PERIPH_t src,
                                         size_t size,
                                         void * periph_info,
                                         bool send_evt,
                                         ALT_DMA_EVENT_t evt);

/*!
 * @}
 */

/*!
 * @}
 */

#ifdef __cplusplus
}
#endif  /* __cplusplus */

#endif  /* __ALT_DMA_H__ */
