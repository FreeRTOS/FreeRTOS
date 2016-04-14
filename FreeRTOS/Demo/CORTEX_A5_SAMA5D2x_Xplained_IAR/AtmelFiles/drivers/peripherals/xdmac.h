/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
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

/** \file */

/** \addtogroup dmac_module Working with DMAC
 *
 * \section Usage
 * <ul>
 * <li> Enable or disable DMAC channel with XDMAC_EnableChannel() and XDMAC_EnableChannels() or XDMAC_DisableChannel() and XDMAC_DisableChannels().</li>
 * <li> Enable or disable %DMA interrupt using XDMAC_EnableGIt() and XDMAC_EnableChannelIt() or XDMAC_DisableGIt() and XDMAC_DisableChannelIt().</li>
 * <li> Get %DMA interrupt status by XDMAC_GetChannelIsr() and XDMAC_GetMaskChannelIsr().</li>
 * <li> Enable or disable specified %DMA channel with XDMAC_EnableChannel() or XDMAC_DisableChannel().</li>
 * <li> Suspend or resume specified %DMA channel with XDMAC_SuspendReadChannel(), XDMAC_SuspendWriteChannel() and XDMAC_SuspendReadWriteChannel() or XDMAC_ResumeReadWriteChannel().</li>
 * <li> Get %DMA channel status by XDMAC_GetGlobalChStatus().</li>
 * <li> Configure source and/or destination start address with XDMAC_SetSourceAddr() and/or XDMAC_SetDestinationAddr().</li>
 * <li> Set %DMA descriptor address using XDMAC_SetDescriptorAddr().</li>
 * <li> Set source transfer buffer size with XDMAC_SetMicroblockControl() or XDMAC_SetBlockControl().</li>
 * <li> Configure source and destination memory pattern with XDMAC_SetDataStride_MemPattern().</li>
 * <li> Configure source or destination Microblock stride with XDMAC_SetSourceMicroBlockStride() or XDMAC_SetDestinationMicroBlockStride().</li>
 * </ul>
 *
 * For more accurate information, please look at the DMAC section of the
 * Datasheet.
 *
 * \sa \ref dmad_module
 *
 * Related files :\n
 * \ref xdmac.c\n
 * \ref xdmac.h\n
 *
 */

#ifndef _XDMAC_H_
#define _XDMAC_H_

/**@{*/

/*------------------------------------------------------------------------------
 *         Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"
#include <stdint.h>

/*------------------------------------------------------------------------------
 *         Definitions
 *----------------------------------------------------------------------------*/

/** \addtogroup dmac_defines DMAC Definitions
 *      @{
 */

/** Number of DMA channels */
#define XDMAC_CONTROLLERS 2

/** Number of DMA channels */
#define XDMAC_CHANNELS (XDMACCHID_NUMBER)

/** Max DMA single transfer size */
#define XDMAC_MAX_BT_SIZE 0xFFFF

/**     @}*/

/*----------------------------------------------------------------------------
 *         Macro
 *----------------------------------------------------------------------------*/
#define XDMA_GET_DATASIZE(size) ((size==0)? XDMAC_CC_DWIDTH_BYTE : \
                                ((size==1)? XDMAC_CC_DWIDTH_HALFWORD : \
                                ((size==2)? XDMAC_CC_DWIDTH_WORD : XDMAC_CC_DWIDTH_DWORD )))
#define XDMA_GET_CC_SAM(s)      ((s==0)? XDMAC_CC_SAM_FIXED_AM : \
                                ((s==1)? XDMAC_CC_SAM_INCREMENTED_AM : \
                                ((s==2)? XDMAC_CC_SAM_UBS_AM : XDMAC_CC_SAM_UBS_DS_AM )))
#define XDMA_GET_CC_DAM(d)      ((d==0)? XDMAC_CC_DAM_FIXED_AM : \
                                ((d==1)? XDMAC_CC_DAM_INCREMENTED_AM : \
                                ((d==2)? XDMAC_CC_DAM_UBS_AM : XDMAC_CC_DAM_UBS_DS_AM )))
#define XDMA_GET_CC_MEMSET(m)   ((m==0)? XDMAC_CC_MEMSET_NORMAL_MODE : XDMAC_CC_MEMSET_HW_MODE)

/*------------------------------------------------------------------------------
 *         Global functions
 *------------------------------------------------------------------------------*/

/** \addtogroup dmac_functions XDMAC Functions
 *      @{
 */

#ifdef __cplusplus
extern "C" {
#endif

/**
 * \brief Enable the XDMAC peripheral clock
 *
 * \param xdmac Pointer to the XDMAC instance.
 */
extern Xdmac *xdmac_get_instance(uint32_t index);

/**
 * \brief Get the XDMAC peripheral ID for a given XDMAC instance
 *
 * \param xdmac Pointer to the XDMAC instance.
 */
extern uint32_t xdmac_get_periph_id(Xdmac *xdmac);

/**
 * \brief Get XDMAC global type.
 *
 * \param xdmac Pointer to the XDMAC instance.
 */
extern uint32_t xdmac_get_type(Xdmac *xdmac);

/**
 * \brief Get XDMAC global configuration.
 *
 * \param xdmac Pointer to the XDMAC instance.
 */
extern uint32_t xdmac_get_config(Xdmac *xdmac);

/**
 * \brief Get XDMAC global weighted arbiter configuration.
 *
 * \param xdmac Pointer to the XDMAC instance.
 */
extern uint32_t xdmac_get_arbiter(Xdmac *xdmac);

/**
 * \brief Enables XDMAC global interrupt.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param int_mask IT to be enabled.
 */
extern void xdmac_enable_global_it(Xdmac *xdmac, uint32_t int_mask);

/**
 * \brief Disables XDMAC global interrupt
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param int_mask IT to be enabled
 */
extern void xdmac_disable_global_it(Xdmac *xdmac, uint32_t int_mask);

/**
 * \brief Get XDMAC global interrupt mask.
 *
 * \param xdmac Pointer to the XDMAC instance.
 */
extern uint32_t xdmac_get_global_it_mask(Xdmac *xdmac);

/**
 * \brief Get XDMAC global interrupt status.
 *
 * \param xdmac Pointer to the XDMAC instance.
 */
extern uint32_t xdmac_get_global_isr(Xdmac *xdmac);

/**
 * \brief Get XDMAC masked global interrupt.
 *
 * \param xdmac Pointer to the XDMAC instance.
 */
extern uint32_t xdmac_get_masked_global_isr(Xdmac *xdmac);

/**
 * \brief enables the relevant channel of given XDMAC.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 */
extern void xdmac_enable_channel(Xdmac *xdmac, uint8_t channel);

/**
 * \brief enables the relevant channels of given XDMAC.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel_mask Channels bitmap.
 */
extern void xdmac_enable_channels(Xdmac *xdmac, uint8_t channel_mask);

/**
 * \brief Disables the relevant channel of given XDMAC.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 */
extern void xdmac_disable_channel(Xdmac *xdmac, uint8_t channel);

/**
 * \brief Disables the relevant channels of given XDMAC.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel_mask Channels bitmap.
 */
extern void xdmac_disable_channels(Xdmac *xdmac, uint8_t channel_mask);

/**
 * \brief Get Global channel status of given XDMAC.
 * \note: When set to 1, this bit indicates that the channel x is enabled. If a channel disable request is issued, this bit remains asserted
    until pending transaction is completed.
 * \param xdmac Pointer to the XDMAC instance.
 */
extern uint32_t xdmac_get_global_channel_status(Xdmac *xdmac);

/**
 * \brief Suspend the relevant channel's read.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 */
extern void xdmac_suspend_read_channel(Xdmac *xdmac, uint8_t channel);

/**
 * \brief Suspend the relevant channel's write.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 */
extern void xdmac_suspend_write_channel(Xdmac *xdmac, uint8_t channel);

/**
 * \brief Suspend the relevant channel's read & write.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 */
extern void xdmac_suspend_read_write_channel(Xdmac *xdmac, uint8_t channel);

/**
 * \brief Resume the relevant channel's read & write.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 */
extern void xdmac_resume_read_write_channel(Xdmac *xdmac, uint8_t channel);

/**
 * \brief Set software transfer request on the relevant channel.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 */
extern void xdmac_software_transfer_request(Xdmac *xdmac, uint8_t channel);

/**
 * \brief Get software transfer status of the relevant channel.
 *
 * \param xdmac Pointer to the XDMAC instance.
 */
extern uint32_t xdmac_get_software_transfer_status(Xdmac *xdmac);

/**
 * \brief Set software flush request on the relevant channel.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 */
extern void xdmac_software_flush_request(Xdmac *xdmac, uint8_t channel);

/**
 * \brief Disable interrupt with mask on the relevant channel of given XDMA.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 * \param int_mask Interrupt mask.
 */
extern void xdmac_enable_channel_it(Xdmac *xdmac, uint8_t channel, uint32_t int_mask);

/**
 * \brief Enable interrupt with mask on the relevant channel of given XDMA.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 * \param int_mask Interrupt mask.
 */
extern void xdmac_disable_channel_it(Xdmac *xdmac, uint8_t channel, uint32_t int_mask);

/**
 * \brief Get interrupt mask for the relevant channel of given XDMA.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 */
extern uint32_t xdmac_get_channel_it_mask(Xdmac *xdmac, uint8_t channel);

/**
 * \brief Get interrupt status for the relevant channel of given XDMA.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 */
extern uint32_t xdmac_get_channel_isr(Xdmac *xdmac, uint8_t channel);

/**
 * \brief Get masked interrupt status for the relevant channel of given XDMA.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 */
extern uint32_t xdmac_get_masked_channel_isr(Xdmac *xdmac, uint8_t channel);

/**
 * \brief Set source address for the relevant channel of given XDMA.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 * \param addr Source address.
 */
extern void xdmac_set_src_addr(Xdmac *xdmac, uint8_t channel, void *addr);

/**
 * \brief Set destination address for the relevant channel of given XDMA.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 * \param addr Destination address.
 */
extern void xdmac_set_dest_addr(Xdmac *xdmac, uint8_t channel, void *addr);

/**
 * \brief Set next descriptor's address & interface for the relevant channel of given XDMA.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 * \param addr Address of next descriptor.
 * \param nda Next Descriptor Interface.
 */
extern void xdmac_set_descriptor_addr(Xdmac *xdmac, uint8_t channel, void *addr, uint32_t ndaif);

/**
 * \brief Set next descriptor's configuration for the relevant channel of given XDMA.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 * \param config Configuration of next descriptor.
 */
extern void xdmac_set_descriptor_control(Xdmac *xdmac, uint8_t channel, uint32_t config);

/**
 * \brief Set microblock length for the relevant channel of given XDMA.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 * \param ublen Microblock length.
 */
extern void xdmac_set_microblock_control(Xdmac *xdmac, uint8_t channel, uint32_t ublen);

/**
 * \brief Set block length for the relevant channel of given XDMA.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 * \param blen Block length.
 */
extern void xdmac_set_block_control(Xdmac *xdmac, uint8_t channel, uint32_t blen);

/**
 * \brief Set configuration for the relevant channel of given XDMA.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 * \param config Channel configuration.
 */
extern void xdmac_set_channel_config(Xdmac *xdmac, uint8_t channel, uint32_t config);

/**
 * \brief Get the relevant channel's configuration of given XDMA.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 */
extern uint32_t xdmac_get_channel_config(Xdmac *xdmac, uint8_t channel);

/**
 * \brief Set the relevant channel's data stride memory pattern of given XDMA.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 * \param dds_msp Data stride memory pattern.
 */
extern void xdmac_set_data_stride_mem_pattern(Xdmac *xdmac, uint8_t channel,
			       uint32_t dds_msp);

/**
 * \brief Set the relevant channel's source microblock stride of given XDMA.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 * \param subs Source microblock stride.
 */
extern void xdmac_set_src_microblock_stride(Xdmac *xdmac, uint8_t channel, uint32_t subs);

/**
 * \brief Set the relevant channel's destination microblock stride of given XDMA.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 * \param dubs Destination microblock stride.
 */
extern void xdmac_set_dest_microblock_stride(Xdmac *xdmac, uint8_t channel, uint32_t dubs);

/**
 * \brief Get the relevant channel's destination address of given XDMA.
 *
 * \param xdmac Pointer to the XDMAC instance.
 * \param channel Particular channel number.
 */
extern uint32_t xdmac_get_channel_dest_addr(Xdmac *xdmac, uint8_t channel);

#ifdef __cplusplus
}
#endif

/**     @}*//**@}*/

#endif /* _XDMAC_H_ */
