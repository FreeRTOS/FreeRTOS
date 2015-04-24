/* --COPYRIGHT--,BSD
 * Copyright (c) 2014, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * --/COPYRIGHT--*/
//*****************************************************************************
//
// dma.h - Driver for the DMA Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_DMA_H__
#define __MSP430WARE_DMA_H__

#include "inc/hw_memmap.h"

#if defined(__MSP430_HAS_DMAX_3__) || defined(__MSP430_HAS_DMAX_6__)

//*****************************************************************************
//
// If building with a C++ compiler, make all of the definitions in this header
// have a C binding.
//
//*****************************************************************************
#ifdef __cplusplus
extern "C"
{
#endif

#include "inc/hw_regaccess.h"
//*****************************************************************************
//
//! \brief Used in the DMA_init() function as the param parameter.
//
//*****************************************************************************
typedef struct DMA_initParam
{
    //! Is the specified channel to initialize.
    //! \n Valid values are:
    //! - \b DMA_CHANNEL_0
    //! - \b DMA_CHANNEL_1
    //! - \b DMA_CHANNEL_2
    //! - \b DMA_CHANNEL_3
    //! - \b DMA_CHANNEL_4
    //! - \b DMA_CHANNEL_5
    //! - \b DMA_CHANNEL_6
    //! - \b DMA_CHANNEL_7
    uint8_t channelSelect;
    //! Is the transfer mode of the selected channel.
    //! \n Valid values are:
    //! - \b DMA_TRANSFER_SINGLE [Default]
    //! - \b DMA_TRANSFER_BLOCK
    //! - \b DMA_TRANSFER_BURSTBLOCK
    //! - \b DMA_TRANSFER_REPEATED_SINGLE
    //! - \b DMA_TRANSFER_REPEATED_BLOCK
    //! - \b DMA_TRANSFER_REPEATED_BURSTBLOCK
    uint16_t transferModeSelect;
    //! Is the amount of transfers to complete in a block transfer mode, as
    //! well as how many transfers to complete before the interrupt flag is
    //! set. Valid value is between 1-65535, if 0, no transfers will occur.
    uint16_t transferSize;
    //! Is the source that will trigger the start of each transfer, note that
    //! the sources are device specific.
    //! \n Valid values are:
    //! - \b DMA_TRIGGERSOURCE_0 [Default]
    //! - \b DMA_TRIGGERSOURCE_1
    //! - \b DMA_TRIGGERSOURCE_2
    //! - \b DMA_TRIGGERSOURCE_3
    //! - \b DMA_TRIGGERSOURCE_4
    //! - \b DMA_TRIGGERSOURCE_5
    //! - \b DMA_TRIGGERSOURCE_6
    //! - \b DMA_TRIGGERSOURCE_7
    //! - \b DMA_TRIGGERSOURCE_8
    //! - \b DMA_TRIGGERSOURCE_9
    //! - \b DMA_TRIGGERSOURCE_10
    //! - \b DMA_TRIGGERSOURCE_11
    //! - \b DMA_TRIGGERSOURCE_12
    //! - \b DMA_TRIGGERSOURCE_13
    //! - \b DMA_TRIGGERSOURCE_14
    //! - \b DMA_TRIGGERSOURCE_15
    //! - \b DMA_TRIGGERSOURCE_16
    //! - \b DMA_TRIGGERSOURCE_17
    //! - \b DMA_TRIGGERSOURCE_18
    //! - \b DMA_TRIGGERSOURCE_19
    //! - \b DMA_TRIGGERSOURCE_20
    //! - \b DMA_TRIGGERSOURCE_21
    //! - \b DMA_TRIGGERSOURCE_22
    //! - \b DMA_TRIGGERSOURCE_23
    //! - \b DMA_TRIGGERSOURCE_24
    //! - \b DMA_TRIGGERSOURCE_25
    //! - \b DMA_TRIGGERSOURCE_26
    //! - \b DMA_TRIGGERSOURCE_27
    //! - \b DMA_TRIGGERSOURCE_28
    //! - \b DMA_TRIGGERSOURCE_29
    //! - \b DMA_TRIGGERSOURCE_30
    //! - \b DMA_TRIGGERSOURCE_31
    uint8_t triggerSourceSelect;
    //! Is the specified size of transfers.
    //! \n Valid values are:
    //! - \b DMA_SIZE_SRCWORD_DSTWORD [Default]
    //! - \b DMA_SIZE_SRCBYTE_DSTWORD
    //! - \b DMA_SIZE_SRCWORD_DSTBYTE
    //! - \b DMA_SIZE_SRCBYTE_DSTBYTE
    uint8_t transferUnitSelect;
    //! Is the type of trigger that the trigger signal needs to be to start a
    //! transfer.
    //! \n Valid values are:
    //! - \b DMA_TRIGGER_RISINGEDGE [Default]
    //! - \b DMA_TRIGGER_HIGH
    uint8_t triggerTypeSelect;
} DMA_initParam;

//*****************************************************************************
//
// The following are values that can be passed to the triggerSourceSelect
// parameter for functions: DMA_init(); the param parameter for functions:
// DMA_init().
//
//*****************************************************************************
#define DMA_TRIGGERSOURCE_0                                              (0x00)
#define DMA_TRIGGERSOURCE_1                                              (0x01)
#define DMA_TRIGGERSOURCE_2                                              (0x02)
#define DMA_TRIGGERSOURCE_3                                              (0x03)
#define DMA_TRIGGERSOURCE_4                                              (0x04)
#define DMA_TRIGGERSOURCE_5                                              (0x05)
#define DMA_TRIGGERSOURCE_6                                              (0x06)
#define DMA_TRIGGERSOURCE_7                                              (0x07)
#define DMA_TRIGGERSOURCE_8                                              (0x08)
#define DMA_TRIGGERSOURCE_9                                              (0x09)
#define DMA_TRIGGERSOURCE_10                                             (0x0A)
#define DMA_TRIGGERSOURCE_11                                             (0x0B)
#define DMA_TRIGGERSOURCE_12                                             (0x0C)
#define DMA_TRIGGERSOURCE_13                                             (0x0D)
#define DMA_TRIGGERSOURCE_14                                             (0x0E)
#define DMA_TRIGGERSOURCE_15                                             (0x0F)
#define DMA_TRIGGERSOURCE_16                                             (0x10)
#define DMA_TRIGGERSOURCE_17                                             (0x11)
#define DMA_TRIGGERSOURCE_18                                             (0x12)
#define DMA_TRIGGERSOURCE_19                                             (0x13)
#define DMA_TRIGGERSOURCE_20                                             (0x14)
#define DMA_TRIGGERSOURCE_21                                             (0x15)
#define DMA_TRIGGERSOURCE_22                                             (0x16)
#define DMA_TRIGGERSOURCE_23                                             (0x17)
#define DMA_TRIGGERSOURCE_24                                             (0x18)
#define DMA_TRIGGERSOURCE_25                                             (0x19)
#define DMA_TRIGGERSOURCE_26                                             (0x1A)
#define DMA_TRIGGERSOURCE_27                                             (0x1B)
#define DMA_TRIGGERSOURCE_28                                             (0x1C)
#define DMA_TRIGGERSOURCE_29                                             (0x1D)
#define DMA_TRIGGERSOURCE_30                                             (0x1E)
#define DMA_TRIGGERSOURCE_31                                             (0x1F)

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: DMA_init(); the transferModeSelect parameter for functions:
// DMA_init().
//
//*****************************************************************************
#define DMA_TRANSFER_SINGLE                                           (DMADT_0)
#define DMA_TRANSFER_BLOCK                                            (DMADT_1)
#define DMA_TRANSFER_BURSTBLOCK                                       (DMADT_2)
#define DMA_TRANSFER_REPEATED_SINGLE                                  (DMADT_4)
#define DMA_TRANSFER_REPEATED_BLOCK                                   (DMADT_5)
#define DMA_TRANSFER_REPEATED_BURSTBLOCK                              (DMADT_6)

//*****************************************************************************
//
// The following are values that can be passed to the channelSelect parameter
// for functions: DMA_init(), DMA_setTransferSize(), DMA_getTransferSize(),
// DMA_setSrcAddress(), DMA_setDstAddress(), DMA_enableTransfers(),
// DMA_disableTransfers(), DMA_startTransfer(), DMA_enableInterrupt(),
// DMA_disableInterrupt(), DMA_getInterruptStatus(), DMA_clearInterrupt(),
// DMA_getNMIAbortStatus(), and DMA_clearNMIAbort(); the param parameter for
// functions: DMA_init().
//
//*****************************************************************************
#define DMA_CHANNEL_0                                                    (0x00)
#define DMA_CHANNEL_1                                                    (0x10)
#define DMA_CHANNEL_2                                                    (0x20)
#define DMA_CHANNEL_3                                                    (0x30)
#define DMA_CHANNEL_4                                                    (0x40)
#define DMA_CHANNEL_5                                                    (0x50)
#define DMA_CHANNEL_6                                                    (0x60)
#define DMA_CHANNEL_7                                                    (0x70)

//*****************************************************************************
//
// The following are values that can be passed to the triggerTypeSelect
// parameter for functions: DMA_init(); the param parameter for functions:
// DMA_init().
//
//*****************************************************************************
#define DMA_TRIGGER_RISINGEDGE                                    (!(DMALEVEL))
#define DMA_TRIGGER_HIGH                                             (DMALEVEL)

//*****************************************************************************
//
// The following are values that can be passed to the transferUnitSelect
// parameter for functions: DMA_init(); the param parameter for functions:
// DMA_init().
//
//*****************************************************************************
#define DMA_SIZE_SRCWORD_DSTWORD                   (!(DMASRCBYTE + DMADSTBYTE))
#define DMA_SIZE_SRCBYTE_DSTWORD                                   (DMASRCBYTE)
#define DMA_SIZE_SRCWORD_DSTBYTE                                   (DMADSTBYTE)
#define DMA_SIZE_SRCBYTE_DSTBYTE                      (DMASRCBYTE + DMADSTBYTE)

//*****************************************************************************
//
// The following are values that can be passed to the directionSelect parameter
// for functions: DMA_setSrcAddress(), and DMA_setDstAddress().
//
//*****************************************************************************
#define DMA_DIRECTION_UNCHANGED                                  (DMASRCINCR_0)
#define DMA_DIRECTION_DECREMENT                                  (DMASRCINCR_2)
#define DMA_DIRECTION_INCREMENT                                  (DMASRCINCR_3)

//*****************************************************************************
//
// The following are values that can be passed toThe following are values that
// can be returned by the DMA_getInterruptStatus() function.
//
//*****************************************************************************
#define DMA_INT_INACTIVE                                                  (0x0)
#define DMA_INT_ACTIVE                                                 (DMAIFG)

//*****************************************************************************
//
// The following are values that can be passed toThe following are values that
// can be returned by the DMA_getNMIAbortStatus() function.
//
//*****************************************************************************
#define DMA_NOTABORTED                                                    (0x0)
#define DMA_ABORTED                                                  (DMAABORT)

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************

//*****************************************************************************
//
//! \brief Initializes the specified DMA channel.
//!
//! This function initializes the specified DMA channel. Upon successful
//! completion of initialization of the selected channel the control registers
//! will be cleared and the given variables will be set. Please note, if
//! transfers have been enabled with the enableTransfers() function, then a
//! call to disableTransfers() is necessary before re-initialization. Also
//! note, that the trigger sources are device dependent and can be found in the
//! device family data sheet. The amount of DMA channels available are also
//! device specific.
//!
//! \param param is the pointer to struct for initialization.
//!
//! \return STATUS_SUCCESS or STATUS_FAILURE of the initialization process.
//
//*****************************************************************************
extern void DMA_init(DMA_initParam *param);

//*****************************************************************************
//
//! \brief Sets the specified amount of transfers for the selected DMA channel.
//!
//! This function sets the specified amount of transfers for the selected DMA
//! channel without having to reinitialize the DMA channel.
//!
//! \param channelSelect is the specified channel to set source address
//!        direction for.
//!        Valid values are:
//!        - \b DMA_CHANNEL_0
//!        - \b DMA_CHANNEL_1
//!        - \b DMA_CHANNEL_2
//!        - \b DMA_CHANNEL_3
//!        - \b DMA_CHANNEL_4
//!        - \b DMA_CHANNEL_5
//!        - \b DMA_CHANNEL_6
//!        - \b DMA_CHANNEL_7
//! \param transferSize is the amount of transfers to complete in a block
//!        transfer mode, as well as how many transfers to complete before the
//!        interrupt flag is set. Valid value is between 1-65535, if 0, no
//!        transfers will occur.
//!        \n Modified bits are \b DMAxSZ of \b DMAxSZ register.
//!
//! \return None
//
//*****************************************************************************
extern void DMA_setTransferSize(uint8_t channelSelect,
                                uint16_t transferSize);

//*****************************************************************************
//
//! \brief Gets the amount of transfers for the selected DMA channel.
//!
//! This function gets the amount of transfers for the selected DMA channel
//! without having to reinitialize the DMA channel.
//!
//! \param channelSelect is the specified channel to set source address
//!        direction for.
//!        Valid values are:
//!        - \b DMA_CHANNEL_0
//!        - \b DMA_CHANNEL_1
//!        - \b DMA_CHANNEL_2
//!        - \b DMA_CHANNEL_3
//!        - \b DMA_CHANNEL_4
//!        - \b DMA_CHANNEL_5
//!        - \b DMA_CHANNEL_6
//!        - \b DMA_CHANNEL_7
//!
//! \return the amount of transfers
//
//*****************************************************************************
extern uint16_t DMA_getTransferSize(uint8_t channelSelect);

//*****************************************************************************
//
//! \brief Sets source address and the direction that the source address will
//! move after a transfer.
//!
//! This function sets the source address and the direction that the source
//! address will move after a transfer is complete. It may be incremented,
//! decremented or unchanged.
//!
//! \param channelSelect is the specified channel to set source address
//!        direction for.
//!        Valid values are:
//!        - \b DMA_CHANNEL_0
//!        - \b DMA_CHANNEL_1
//!        - \b DMA_CHANNEL_2
//!        - \b DMA_CHANNEL_3
//!        - \b DMA_CHANNEL_4
//!        - \b DMA_CHANNEL_5
//!        - \b DMA_CHANNEL_6
//!        - \b DMA_CHANNEL_7
//! \param srcAddress is the address of where the data will be transferred
//!        from.
//!        \n Modified bits are \b DMAxSA of \b DMAxSA register.
//! \param directionSelect is the specified direction of the source address
//!        after a transfer.
//!        Valid values are:
//!        - \b DMA_DIRECTION_UNCHANGED
//!        - \b DMA_DIRECTION_DECREMENT
//!        - \b DMA_DIRECTION_INCREMENT
//!        \n Modified bits are \b DMASRCINCR of \b DMAxCTL register.
//!
//! \return None
//
//*****************************************************************************
extern void DMA_setSrcAddress(uint8_t channelSelect,
                              uint32_t srcAddress,
                              uint16_t directionSelect);

//*****************************************************************************
//
//! \brief Sets the destination address and the direction that the destination
//! address will move after a transfer.
//!
//! This function sets the destination address and the direction that the
//! destination address will move after a transfer is complete. It may be
//! incremented, decremented, or unchanged.
//!
//! \param channelSelect is the specified channel to set the destination
//!        address direction for.
//!        Valid values are:
//!        - \b DMA_CHANNEL_0
//!        - \b DMA_CHANNEL_1
//!        - \b DMA_CHANNEL_2
//!        - \b DMA_CHANNEL_3
//!        - \b DMA_CHANNEL_4
//!        - \b DMA_CHANNEL_5
//!        - \b DMA_CHANNEL_6
//!        - \b DMA_CHANNEL_7
//! \param dstAddress is the address of where the data will be transferred to.
//!        \n Modified bits are \b DMAxDA of \b DMAxDA register.
//! \param directionSelect is the specified direction of the destination
//!        address after a transfer.
//!        Valid values are:
//!        - \b DMA_DIRECTION_UNCHANGED
//!        - \b DMA_DIRECTION_DECREMENT
//!        - \b DMA_DIRECTION_INCREMENT
//!        \n Modified bits are \b DMADSTINCR of \b DMAxCTL register.
//!
//! \return None
//
//*****************************************************************************
extern void DMA_setDstAddress(uint8_t channelSelect,
                              uint32_t dstAddress,
                              uint16_t directionSelect);

//*****************************************************************************
//
//! \brief Enables transfers to be triggered.
//!
//! This function enables transfers upon appropriate trigger of the selected
//! trigger source for the selected channel.
//!
//! \param channelSelect is the specified channel to enable transfer for.
//!        Valid values are:
//!        - \b DMA_CHANNEL_0
//!        - \b DMA_CHANNEL_1
//!        - \b DMA_CHANNEL_2
//!        - \b DMA_CHANNEL_3
//!        - \b DMA_CHANNEL_4
//!        - \b DMA_CHANNEL_5
//!        - \b DMA_CHANNEL_6
//!        - \b DMA_CHANNEL_7
//!
//! \return None
//
//*****************************************************************************
extern void DMA_enableTransfers(uint8_t channelSelect);

//*****************************************************************************
//
//! \brief Disables transfers from being triggered.
//!
//! This function disables transfer from being triggered for the selected
//! channel. This function should be called before any re-initialization of the
//! selected DMA channel.
//!
//! \param channelSelect is the specified channel to disable transfers for.
//!        Valid values are:
//!        - \b DMA_CHANNEL_0
//!        - \b DMA_CHANNEL_1
//!        - \b DMA_CHANNEL_2
//!        - \b DMA_CHANNEL_3
//!        - \b DMA_CHANNEL_4
//!        - \b DMA_CHANNEL_5
//!        - \b DMA_CHANNEL_6
//!        - \b DMA_CHANNEL_7
//!
//! \return None
//
//*****************************************************************************
extern void DMA_disableTransfers(uint8_t channelSelect);

//*****************************************************************************
//
//! \brief Starts a transfer if using the default trigger source selected in
//! initialization.
//!
//! This functions triggers a transfer of data from source to destination if
//! the trigger source chosen from initialization is the DMA_TRIGGERSOURCE_0.
//! Please note, this function needs to be called for each (repeated-)single
//! transfer, and when transferAmount of transfers have been complete in
//! (repeated-)block transfers.
//!
//! \param channelSelect is the specified channel to start transfers for.
//!        Valid values are:
//!        - \b DMA_CHANNEL_0
//!        - \b DMA_CHANNEL_1
//!        - \b DMA_CHANNEL_2
//!        - \b DMA_CHANNEL_3
//!        - \b DMA_CHANNEL_4
//!        - \b DMA_CHANNEL_5
//!        - \b DMA_CHANNEL_6
//!        - \b DMA_CHANNEL_7
//!
//! \return None
//
//*****************************************************************************
extern void DMA_startTransfer(uint8_t channelSelect);

//*****************************************************************************
//
//! \brief Enables the DMA interrupt for the selected channel.
//!
//! Enables the DMA interrupt source.  Only the sources that are enabled can be
//! reflected to the processor interrupt; disabled sources have no effect on
//! the processor. Does not clear interrupt flags.
//!
//! \param channelSelect is the specified channel to enable the interrupt for.
//!        Valid values are:
//!        - \b DMA_CHANNEL_0
//!        - \b DMA_CHANNEL_1
//!        - \b DMA_CHANNEL_2
//!        - \b DMA_CHANNEL_3
//!        - \b DMA_CHANNEL_4
//!        - \b DMA_CHANNEL_5
//!        - \b DMA_CHANNEL_6
//!        - \b DMA_CHANNEL_7
//!
//! \return None
//
//*****************************************************************************
extern void DMA_enableInterrupt(uint8_t channelSelect);

//*****************************************************************************
//
//! \brief Disables the DMA interrupt for the selected channel.
//!
//! Disables the DMA interrupt source. Only the sources that are enabled can be
//! reflected to the processor interrupt; disabled sources have no effect on
//! the processor.
//!
//! \param channelSelect is the specified channel to disable the interrupt for.
//!        Valid values are:
//!        - \b DMA_CHANNEL_0
//!        - \b DMA_CHANNEL_1
//!        - \b DMA_CHANNEL_2
//!        - \b DMA_CHANNEL_3
//!        - \b DMA_CHANNEL_4
//!        - \b DMA_CHANNEL_5
//!        - \b DMA_CHANNEL_6
//!        - \b DMA_CHANNEL_7
//!
//! \return None
//
//*****************************************************************************
extern void DMA_disableInterrupt(uint8_t channelSelect);

//*****************************************************************************
//
//! \brief Returns the status of the interrupt flag for the selected channel.
//!
//! Returns the status of the interrupt flag for the selected channel.
//!
//! \param channelSelect is the specified channel to return the interrupt flag
//!        status from.
//!        Valid values are:
//!        - \b DMA_CHANNEL_0
//!        - \b DMA_CHANNEL_1
//!        - \b DMA_CHANNEL_2
//!        - \b DMA_CHANNEL_3
//!        - \b DMA_CHANNEL_4
//!        - \b DMA_CHANNEL_5
//!        - \b DMA_CHANNEL_6
//!        - \b DMA_CHANNEL_7
//!
//! \return One of the following:
//!         - \b DMA_INT_INACTIVE
//!         - \b DMA_INT_ACTIVE
//!         \n indicating the status of the current interrupt flag
//
//*****************************************************************************
extern uint16_t DMA_getInterruptStatus(uint8_t channelSelect);

//*****************************************************************************
//
//! \brief Clears the interrupt flag for the selected channel.
//!
//! This function clears the DMA interrupt flag is cleared, so that it no
//! longer asserts.
//!
//! \param channelSelect is the specified channel to clear the interrupt flag
//!        for.
//!        Valid values are:
//!        - \b DMA_CHANNEL_0
//!        - \b DMA_CHANNEL_1
//!        - \b DMA_CHANNEL_2
//!        - \b DMA_CHANNEL_3
//!        - \b DMA_CHANNEL_4
//!        - \b DMA_CHANNEL_5
//!        - \b DMA_CHANNEL_6
//!        - \b DMA_CHANNEL_7
//!
//! \return None
//
//*****************************************************************************
extern void DMA_clearInterrupt(uint8_t channelSelect);

//*****************************************************************************
//
//! \brief Returns the status of the NMIAbort for the selected channel.
//!
//! This function returns the status of the NMI Abort flag for the selected
//! channel. If this flag has been set, it is because a transfer on this
//! channel was aborted due to a interrupt from an NMI.
//!
//! \param channelSelect is the specified channel to return the status of the
//!        NMI Abort flag for.
//!        Valid values are:
//!        - \b DMA_CHANNEL_0
//!        - \b DMA_CHANNEL_1
//!        - \b DMA_CHANNEL_2
//!        - \b DMA_CHANNEL_3
//!        - \b DMA_CHANNEL_4
//!        - \b DMA_CHANNEL_5
//!        - \b DMA_CHANNEL_6
//!        - \b DMA_CHANNEL_7
//!
//! \return One of the following:
//!         - \b DMA_NOTABORTED
//!         - \b DMA_ABORTED
//!         \n indicating the status of the NMIAbort for the selected channel
//
//*****************************************************************************
extern uint16_t DMA_getNMIAbortStatus(uint8_t channelSelect);

//*****************************************************************************
//
//! \brief Clears the status of the NMIAbort to proceed with transfers for the
//! selected channel.
//!
//! This function clears the status of the NMI Abort flag for the selected
//! channel to allow for transfers on the channel to continue.
//!
//! \param channelSelect is the specified channel to clear the NMI Abort flag
//!        for.
//!        Valid values are:
//!        - \b DMA_CHANNEL_0
//!        - \b DMA_CHANNEL_1
//!        - \b DMA_CHANNEL_2
//!        - \b DMA_CHANNEL_3
//!        - \b DMA_CHANNEL_4
//!        - \b DMA_CHANNEL_5
//!        - \b DMA_CHANNEL_6
//!        - \b DMA_CHANNEL_7
//!
//! \return None
//
//*****************************************************************************
extern void DMA_clearNMIAbort(uint8_t channelSelect);

//*****************************************************************************
//
//! \brief Disables the DMA from stopping the CPU during a Read-Modify-Write
//! Operation to start a transfer.
//!
//! This function allows the CPU to finish any read-modify-write operations it
//! may be in the middle of before transfers of and DMA channel stop the CPU.
//!
//!
//! \return None
//
//*****************************************************************************
extern void DMA_disableTransferDuringReadModifyWrite(void);

//*****************************************************************************
//
//! \brief Enables the DMA to stop the CPU during a Read-Modify-Write Operation
//! to start a transfer.
//!
//! This function allows the DMA to stop the CPU in the middle of a read-
//! modify-write operation to transfer data.
//!
//!
//! \return None
//
//*****************************************************************************
extern void DMA_enableTransferDuringReadModifyWrite(void);

//*****************************************************************************
//
//! \brief Enables Round Robin prioritization.
//!
//! This function enables Round Robin Prioritization of DMA channels. In the
//! case of Round Robin Prioritization, the last DMA channel to have
//! transferred data then has the last priority, which comes into play when
//! multiple DMA channels are ready to transfer at the same time.
//!
//!
//! \return None
//
//*****************************************************************************
extern void DMA_enableRoundRobinPriority(void);

//*****************************************************************************
//
//! \brief Disables Round Robin prioritization.
//!
//! This function disables Round Robin Prioritization, enabling static
//! prioritization of the DMA channels. In static prioritization, the DMA
//! channels are prioritized with the lowest DMA channel index having the
//! highest priority (i.e. DMA Channel 0 has the highest priority).
//!
//!
//! \return None
//
//*****************************************************************************
extern void DMA_disableRoundRobinPriority(void);

//*****************************************************************************
//
//! \brief Enables a NMI to interrupt a DMA transfer.
//!
//! This function allow NMI's to interrupting any DMA transfer currently in
//! progress and stops any future transfers to begin before the NMI is done
//! processing.
//!
//!
//! \return None
//
//*****************************************************************************
extern void DMA_enableNMIAbort(void);

//*****************************************************************************
//
//! \brief Disables any NMI from interrupting a DMA transfer.
//!
//! This function disables NMI's from interrupting any DMA transfer currently
//! in progress.
//!
//!
//! \return None
//
//*****************************************************************************
extern void DMA_disableNMIAbort(void);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif // __MSP430WARE_DMA_H__
