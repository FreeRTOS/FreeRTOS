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

#ifndef __ALT_DMA_PROGRAM_H__
#define __ALT_DMA_PROGRAM_H__

#include "hwlib.h"
#include "alt_dma_common.h"

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*!
 * \addtogroup ALT_DMA_PRG DMA Controller Programming API
 *
 * This API provides functions for dynamically defining and assembling microcode
 * programs for execution on the DMA controller.
 *
 * The microcode program assembly API provides users with the ability to develop
 * highly optimized and tailored algorithms for data transfer between SoC FPGA
 * IP blocks and/or system memory.
 *
 * The same microcode program assembly facilities are also used to implement the
 * functions found in the HWLIB Common DMA Operations functional API.
 *
 * An ALT_DMA_PROGRAM_t structure is used to contain and assemble a DMA
 * microcode program. The storage for an ALT_DMA_PROGRAM_t stucture is allocated
 * from used specified system memory. Once a microcode program has been
 * assembled in a ALT_DMA_PROGRAM_t it may be excecuted on a designated DMA
 * channel thread. The microcode program may be rerun on any DMA channel thread
 * whenever required as long as the integrity of the ALT_DMA_PROGRAM_t
 * containing the program is maintained.
 *
 * @{
 */

/*!
 * This preprocessor declares the DMA channel thread microcode instruction
 * cache line width in bytes. It is recommended that the program buffers be
 * sized to a multiple of the cache line size. This will allow for the most
 * efficient microcode speed and space utilization.
 */
#define ALT_DMA_PROGRAM_CACHE_LINE_SIZE     (32)

/*!
 * This preprocessor declares the DMA channel thread microcode instruction
 * cache line count. Thus the total size of the cache is the cache line size
 * multipled by the cache line count. Programs larger than the cache size risk
 * having a cache miss while executing.
 */
#define ALT_DMA_PROGRAM_CACHE_LINE_COUNT    (16)

/*!
 * This preprocessor definition determines the size of the program buffer
 * within the ALT_DMA_PROGRAM_t structure. This size should provide adequate
 * size for most DMA microcode programs. If calls within this API are
 * reporting out of memory response codes, consider increasing the provisioned
 * program buffersize.
 *
 * To specify another DMA microcode program buffer size, redefine the macro
 * below by defining ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE to another size in
 * your Makefile. It is recommended that the size be a multiple of the
 * microcode engine cache line size. See ALT_DMA_PROGRAM_CACHE_LINE_SIZE for
 * more information. The largest supported buffer size is 65536 bytes.
 */
#ifndef ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE
#define ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE   (ALT_DMA_PROGRAM_CACHE_LINE_SIZE * ALT_DMA_PROGRAM_CACHE_LINE_COUNT)
#endif

/*!
 * This type defines the structure used to assemble and contain a microcode
 * program which can be executed by the DMA controller. The internal members
 * are undocumented and should not be altered outside of this API.
 */
typedef struct ALT_DMA_PROGRAM_s
{
    uint32_t flag;

    uint16_t buffer_start;
    uint16_t code_size;

    uint16_t loop0;
    uint16_t loop1;

    uint16_t sar;
    uint16_t dar;

    /*
     * Add a little extra space so that regardless of where this structure
     * sits in memory, a suitable start address can be aligned to the cache
     * line stride while providing the requested buffer space.
     */
    uint8_t program[ALT_DMA_PROGRAM_PROVISION_BUFFER_SIZE +
                    ALT_DMA_PROGRAM_CACHE_LINE_SIZE];
}
ALT_DMA_PROGRAM_t;

/*!
 * This type definition enumerates the DMA controller register names for use in
 * microcode program definition.
 */
typedef enum ALT_DMA_PROGRAM_REG_e
{
    /*! Source Address Register */
    ALT_DMA_PROGRAM_REG_SAR = 0x0,

    /*! Destination Address Register */
    ALT_DMA_PROGRAM_REG_DAR = 0x2,

    /*! Channel Control Register */
    ALT_DMA_PROGRAM_REG_CCR = 0x1
}
ALT_DMA_PROGRAM_REG_t;

/*!
 * This type definition enumerates the instruction modifier options available
 * for use with selected DMA microcode instructions.
 *
 * The enumerations values are context dependent upon the instruction being
 * modified.
 *
 * For the <b>DMALD[S|B]</b>, <b>DMALDP\<S|B></b>, <b>DMAST[S|B]</b>, and
 * <b>DMASTP\<S|B></b> microcode instructions, the enumeration
 * ALT_DMA_PROGRAM_INST_MOD_SINGLE specifies the <b>S</b> option modifier
 * while the enumeration ALT_DMA_PROGRAM_INST_MOD_BURST specifies the <b>B</b>
 * option modifier. The enumeration ALT_DMA_PROGRAM_INST_MOD_NONE specifies
 * that no modifier is present for instructions where use of <b>[S|B]</b> is
 * optional.
 *
 * For the <b>DMAWFP</b> microcode instruction, the enumerations
 * ALT_DMA_PROGRAM_INST_MOD_SINGLE, ALT_DMA_PROGRAM_INST_MOD_BURST, or
 * ALT_DMA_PROGRAM_INST_MOD_PERIPH each specify one of the corresponding
 * options <b>\<single|burst|periph></b>.
 */
typedef enum ALT_DMA_PROGRAM_INST_MOD_e
{
    /*!
     * This DMA instruction modifier specifies that no special modifier is
     * added to the instruction.
     */
    ALT_DMA_PROGRAM_INST_MOD_NONE,

    /*!
     * Depending on the DMA microcode instruction modified, this modifier
     * specifies <b>S</b> case for a <b>[S|B]</b> or a <b>\<single></b> for a
     * <b>\<single|burst|periph></b>.
     */
    ALT_DMA_PROGRAM_INST_MOD_SINGLE,

    /*!
     * Depending on the DMA microcode instruction modified, this modifier
     * specifies <b>B</b> case for a <b>[S|B]</b> or a <b>\<burst></b> for a
     * <b>\<single|burst|periph></b>.
     */
    ALT_DMA_PROGRAM_INST_MOD_BURST,

    /*!
     * This DMA instruction modifier specifies a <b>\<periph></b> for a
     * <b>\<single|burst|periph></b>.
     */
    ALT_DMA_PROGRAM_INST_MOD_PERIPH
}
ALT_DMA_PROGRAM_INST_MOD_t;

/*!
 * This function initializes a system memory buffer for use as a DMA microcode
 * program buffer. This should be the first API call made on the program
 * buffer type.
 *
 * \param       pgm
 *              A pointer to a DMA program buffer structure.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_dma_program_init(ALT_DMA_PROGRAM_t * pgm);

/*!
 * This function verifies that the DMA microcode program buffer is no longer
 * in use and performs any needed uninitialization steps.
 *
 * \param       pgm
 *              A pointer to a DMA program buffer structure.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_dma_program_uninit(ALT_DMA_PROGRAM_t * pgm);

/*!
 * This function clears the existing DMA microcode program in the given
 * program buffer.
 *
 * \param       pgm
 *              A pointer to a DMA program buffer structure.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     Details about error status code.
 */
ALT_STATUS_CODE alt_dma_program_clear(ALT_DMA_PROGRAM_t * pgm);

/*!
 * This function validate that the given DMA microcode program buffer contains
 * a well formed program. If caches are enabled, the program buffer contents
 * will be cleaned to RAM.
 *
 * \param       pgm
 *              A pointer to a DMA program buffer structure.
 *
 * \retval      ALT_E_SUCCESS   The given program is well formed.
 * \retval      ALT_E_ERROR     The given program is not well formed.
 * \retval      ALT_E_TMO       The cache operation timed out.
 */
ALT_STATUS_CODE alt_dma_program_validate(const ALT_DMA_PROGRAM_t * pgm);

/*!
 * This function reports the number bytes incremented for the register
 * specified. The purpose is to determine the progress of an ongoing DMA
 * transfer.
 *
 * It is implemented by calculating the difference of the programmed SAR or DAR
 * with the current channel SAR or DAR register value.
 *
 * \param       pgm
 *              A pointer to a DMA program buffer structure.
 *
 * \param       channel
 *              The channel that the program is running on.
 *
 * \param       reg
 *              Register to change the value for. Valid for only
 *              ALT_DMA_PROGRAM_REG_SAR and ALT_DMA_PROGRAM_REG_DAR.
 *
 * \param       current
 *              The current snapshot value of the register read from the DMA
 *              channel.
 *
 * \param       progress
 *              [out] A pointer to a memory location that will be used to store
 *              the number of bytes transfered.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     Details about error status code.
 * \retval      ALT_E_BAD_ARG   The specified channel is invalid, the specified
 *                              register is invalid, or the DMAMOV for the
 *                              specified register has not yet been assembled
 *                              in the current program buffer.
 */
ALT_STATUS_CODE alt_dma_program_progress_reg(ALT_DMA_PROGRAM_t * pgm,
                                             ALT_DMA_PROGRAM_REG_t reg,
                                             uint32_t current, uint32_t * progress);

/*!
 * This function updates a pre-existing DMAMOV value affecting the SAR or DAR
 * registers. This allows for pre-assembled programs that can be used on
 * different source and destination addresses.
 *
 * \param       pgm
 *              A pointer to a DMA program buffer structure.
 *
 * \param       reg
 *              Register to change the value for. Valid for only
 *              ALT_DMA_PROGRAM_REG_SAR and ALT_DMA_PROGRAM_REG_DAR.
 *
 * \param       val
 *              The value to update to.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     Details about error status code.
 * \retval      ALT_E_BAD_ARG   The specified register is invalid or the DMAMOV
 *                              for the specified register has not yet been
 *                              assembled in the current program buffer.
 */
ALT_STATUS_CODE alt_dma_program_update_reg(ALT_DMA_PROGRAM_t * pgm,
                                           ALT_DMA_PROGRAM_REG_t reg, uint32_t val);

/*!
 */

/*!
 * Assembles a DMAADDH (Add Halfword) instruction into the microcode program
 * buffer. This instruction uses 3 bytes of buffer space.
 *
 * \param       pgm
 *              The DMA program buffer to contain the assembled instruction.
 *
 * \param       addr_reg
 *              The channel address register (ALT_DMA_PROGRAM_REG_DAR or
 *              ALT_DMA_PROGRAM_REG_SAR) to add the value to.
 *
 * \param       val
 *              The 16-bit unsigned value to add to the channel address
 *              register.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 * \retval      ALT_E_BAD_ARG       Invalid channel register specified.
 */
// Assembler Syntax: DMAADDH <address_register>, <16-bit immediate>
ALT_STATUS_CODE alt_dma_program_DMAADDH(ALT_DMA_PROGRAM_t * pgm,
                                        ALT_DMA_PROGRAM_REG_t addr_reg, uint16_t val);

/*!
 * Assembles a DMAADNH (Add Negative Halfword) instruction into the microcode
 * program buffer. This instruction uses 3 bytes of buffer space.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \param       addr_reg
 *              The channel address register (ALT_DMA_PROGRAM_REG_DAR or
 *              ALT_DMA_PROGRAM_REG_SAR) to add the value to.
 *
 * \param       val
 *              The 16-bit unsigned value to add to the channel address
 *              register.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 * \retval      ALT_E_BAD_ARG       Invalid channel register specified.
 */
// Assembler Syntax: DMAADNH <address_register>, <16-bit immediate>
ALT_STATUS_CODE alt_dma_program_DMAADNH(ALT_DMA_PROGRAM_t * pgm,
                                        ALT_DMA_PROGRAM_REG_t addr_reg, uint16_t val);

/*!
 * Assembles a DMAEND (End) instruction into the microcode program buffer.
 * This instruction uses 1 byte of buffer space.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 */
// Assembler Syntax: DMAEND
ALT_STATUS_CODE alt_dma_program_DMAEND(ALT_DMA_PROGRAM_t * pgm);

/*!
 * Assembles a DMAFLUSHP (Flush Peripheral) instruction into the microcode
 * program buffer. This instruction uses 2 bytes of buffer space.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \param       periph
 *              The peripheral to flush.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 * \retval      ALT_E_BAD_ARG       Invalid peripheral specified.
 */
// Assembler Syntax: DMAFLUSHP <peripheral>
ALT_STATUS_CODE alt_dma_program_DMAFLUSHP(ALT_DMA_PROGRAM_t * pgm,
                                          ALT_DMA_PERIPH_t periph);

/*!
 * Assembles a DMAGO (Go) instruction into the microcode program buffer. This
 * instruction uses 6 bytes of buffer space.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \param       channel
 *              The stopped channel to act upon.
 *
 * \param       val
 *              The value to write to the channel program counter register.
 *
 * \param       sec
 *              The security state for the operation.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 * \retval      ALT_E_BAD_ARG       Invalid channel or security specified.
 */
// Assembler Syntax: DMAGO <channel_number>, <32-bit_immediate> [, ns]
ALT_STATUS_CODE alt_dma_program_DMAGO(ALT_DMA_PROGRAM_t * pgm,
                                      ALT_DMA_CHANNEL_t channel, uint32_t val,
                                      ALT_DMA_SECURITY_t sec);

/*!
 * Assembles a DMAKILL (Kill) instruction into the microcode program buffer.
 * This instruction uses 1 byte of buffer space.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 */
// Assembler Syntax: DMAKILL
ALT_STATUS_CODE alt_dma_program_DMAKILL(ALT_DMA_PROGRAM_t * pgm);

/*!
 * Assembles a DMALD (Load) instruction into the microcode program buffer.
 * This instruction uses 1 byte of buffer space.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \param       mod
 *              The program instruction modifier for the type of transfer.
 *              Only ALT_DMA_PROGRAM_INST_MOD_SINGLE and 
 *              ALT_DMA_PROGRAM_INST_MOD_BURST are valid options.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 * \retval      ALT_E_BAD_ARG       Invalid instruction modifier specified.
 */
// Assembler Syntax: DMALD[S|B]
ALT_STATUS_CODE alt_dma_program_DMALD(ALT_DMA_PROGRAM_t * pgm,
                                      ALT_DMA_PROGRAM_INST_MOD_t mod);

/*!
 * Assembles a DMALDP (Load and notify Peripheral) instruction into the
 * microcode program buffer. This instruction uses 2 bytes of buffer space.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \param       mod
 *              The program instruction modifier for the type of transfer.
 *              Only ALT_DMA_PROGRAM_INST_MOD_SINGLE and 
 *              ALT_DMA_PROGRAM_INST_MOD_BURST are valid options.
 *
 * \param       periph
 *              The peripheral to notify.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 * \retval      ALT_E_BAD_ARG       Invalid instruction modifier or peripheral
 *                                  specified.
 */
// Assembler Syntax: DMALDP<S|B> <peripheral>
ALT_STATUS_CODE alt_dma_program_DMALDP(ALT_DMA_PROGRAM_t * pgm,
                                       ALT_DMA_PROGRAM_INST_MOD_t mod, ALT_DMA_PERIPH_t periph);

/*!
 * Assembles a DMALP (Loop) instruction into the microcode program buffer.
 * This instruction uses 2 bytes of buffer space.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \param       iterations
 *              The number of iterations to run for. Valid values are 1 - 256.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 * \retval      ALT_E_BAD_ARG       Invalid iterations specified.
 * \retval      ALT_E_BAD_OPERATION All loop registers are in use.
 */
// Assembler Syntax: DMALP [<LC0>|<LC1>] <loop_iterations>
ALT_STATUS_CODE alt_dma_program_DMALP(ALT_DMA_PROGRAM_t * pgm,
                                      uint32_t iterations);

/*!
 * Assembles a DMALPEND (Loop End) instruction into the microcode program
 * buffer. This instruction uses 2 bytes of buffer space.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \param       mod
 *              The program instruction modifier for the loop terminator. Only
 *              ALT_DMA_PROGRAM_INST_MOD_NONE, ALT_DMA_PROGRAM_INST_MOD_SINGLE
 *              and ALT_DMA_PROGRAM_INST_MOD_BURST are valid options.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 * \retval      ALT_E_BAD_ARG       Invalid instruction modifier specified.
 * \retval      ALT_E_ARG_RANGE     Loop size is too large to be supported.
 * \retval      ALT_E_BAD_OPERATION A valid DMALP or DMALPFE was not added to
 *                                  the program buffer before adding this
 *                                  DMALPEND instruction.
 */
// Assembler Syntax: DMALPEND[S|B]
ALT_STATUS_CODE alt_dma_program_DMALPEND(ALT_DMA_PROGRAM_t * pgm,
                                         ALT_DMA_PROGRAM_INST_MOD_t mod);

/*!
 * Assembles a DMALPFE (Loop Forever) instruction into the microcode program
 * buffer. No instruction is added to the buffer but a previous DMALPEND to
 * create an infinite loop.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 */
// Assembler Syntax: DMALPFE
ALT_STATUS_CODE alt_dma_program_DMALPFE(ALT_DMA_PROGRAM_t * pgm);

/*!
 * Assembles a DMAMOV (Move) instruction into the microcode program buffer.
 * This instruction uses 6 bytes of buffer space.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \param       chan_reg
 *              The channel non-looping register (ALT_DMA_PROGRAM_REG_SAR,
 *              ALT_DMA_PROGRAM_REG_DAR or ALT_DMA_PROGRAM_REG_CCR) to copy
 *              the value to.
 *
 * \param       val
 *              The value to write to the specified register.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 * \retval      ALT_E_BAD_ARG       Invalid channel register specified.
 */
// Assembler Syntax: DMAMOV <destination_register>, <32-bit_immediate>
ALT_STATUS_CODE alt_dma_program_DMAMOV(ALT_DMA_PROGRAM_t * pgm,
                                       ALT_DMA_PROGRAM_REG_t chan_reg, uint32_t val);

/*!
 * Assembles a DMANOP (No Operation) instruction into the microcode program
 * buffer. This instruction uses 1 byte of buffer space.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 */
// Assembler Syntax: DMANOP
ALT_STATUS_CODE alt_dma_program_DMANOP(ALT_DMA_PROGRAM_t * pgm);

/*!
 * Assembles a DMARMB (Read Memory Barrier) instruction into the microcode
 * program buffer. This instruction uses 1 byte of buffer space.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 */
// Assembler Syntax: DMARMB
ALT_STATUS_CODE alt_dma_program_DMARMB(ALT_DMA_PROGRAM_t * pgm);

/*!
 * Assembles a DMASEV (Send Event) instruction into the microcode program
 * buffer. This instruction uses 2 byte of buffer space.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \param       evt
 *              The event to send.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 * \retval      ALT_E_BAD_ARG       Invalid event specified.
 */
// Assembler Syntax: DMASEV <event_num>
ALT_STATUS_CODE alt_dma_program_DMASEV(ALT_DMA_PROGRAM_t * pgm,
                                       ALT_DMA_EVENT_t evt);

/*!
 * Assembles a DMAST (Store) instruction into the microcode program buffer.
 * This instruction uses 1 byte of buffer space.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \param       mod
 *              The program instruction modifier for the type of transfer.
 *              Only ALT_DMA_PROGRAM_INST_MOD_SINGLE and 
 *              ALT_DMA_PROGRAM_INST_MOD_BURST are valid options.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 */
// Assembler Syntax: DMAST[S|B]
ALT_STATUS_CODE alt_dma_program_DMAST(ALT_DMA_PROGRAM_t * pgm,
                                      ALT_DMA_PROGRAM_INST_MOD_t mod);

/*!
 * Assembles a DMASTP (Store and notify Peripheral) instruction into the
 * microcode program buffer. This instruction uses 2 bytes of buffer space.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \param       mod
 *              The program instruction modifier for the type of transfer.
 *              Only ALT_DMA_PROGRAM_INST_MOD_SINGLE and 
 *              ALT_DMA_PROGRAM_INST_MOD_BURST are valid options.
 *
 * \param       periph
 *              The peripheral to notify.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 * \retval      ALT_E_BAD_ARG       Invalid instruction modifier or peripheral
 *                                  specified.
 */
// Assembler Syntax: DMASTP<S|B> <peripheral>
ALT_STATUS_CODE alt_dma_program_DMASTP(ALT_DMA_PROGRAM_t * pgm,
                                       ALT_DMA_PROGRAM_INST_MOD_t mod, ALT_DMA_PERIPH_t periph);

/*!
 * Assembles a DMASTZ (Store Zero) instruction into the microcode program
 * buffer. This instruction uses 1 byte of buffer space.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 */
// Assembler Syntax: DMASTZ
ALT_STATUS_CODE alt_dma_program_DMASTZ(ALT_DMA_PROGRAM_t * pgm);

/*!
 * Assembles a DMAWFE (Wait For Event) instruction into the microcode program
 * buffer. This instruction uses 2 byte of buffer space.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \param       evt
 *              The event to wait for.
 *
 * \param       invalid
 *              If invalid is set to true, the instruction will be configured
 *              to invalidate the instruction cache for the current DMA
 *              thread.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 * \retval      ALT_E_BAD_ARG       Invalid event specified.
 */
// Assembler Syntax: DMAWFE <event_num>[, invalid]
ALT_STATUS_CODE alt_dma_program_DMAWFE(ALT_DMA_PROGRAM_t * pgm,
                                       ALT_DMA_EVENT_t evt, bool invalid);

/*!
 * Assembles a DMAWFP (Wait for Peripheral) instruction into the microcode
 * program buffer. This instruction uses 2 bytes of buffer space.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \param       periph
 *              The peripheral to wait on.
 *
 * \param       mod
 *              The program instruction modifier for the type of transfer.
 *              Only ALT_DMA_PROGRAM_INST_MOD_SINGLE,
 *              ALT_DMA_PROGRAM_INST_MOD_BURST, or
 *              ALT_DMA_PROGRAM_INST_MOD_PERIPH are valid options.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 * \retval      ALT_E_BAD_ARG       Invalid peripheral or instruction modifier
 *                                  specified.
 */
// Assembler Syntax: DMAWFP <peripheral>, <single|burst|periph>
ALT_STATUS_CODE alt_dma_program_DMAWFP(ALT_DMA_PROGRAM_t * pgm,
                                       ALT_DMA_PERIPH_t periph, ALT_DMA_PROGRAM_INST_MOD_t mod);

/*!
 * Assembles a DMAWMB (Write Memory Barrier) instruction into the microcode
 * program buffer. This instruction uses 1 byte of buffer space.
 *
 * \param       pgm
 *              The DMA programm buffer to contain the assembled instruction.
 *
 * \retval      ALT_E_SUCCESS       Successful instruction assembly status.
 * \retval      ALT_E_DMA_BUF_OVF   DMA program buffer overflow.
 */
// Assembler Syntax: DMAWMB
ALT_STATUS_CODE alt_dma_program_DMAWMB(ALT_DMA_PROGRAM_t * pgm);

/*!
 * \addtogroup DMA_CCR Support for DMAMOV CCR
 *
 * The ALT_DMA_CCR_OPT_* macro definitions are defined here to facilitate the
 * dynamic microcode programming of the assembler directive:
\verbatim

DMAMOV CCR, [SB<1-16>] [SS<8|16|32|64|128>] [SA<I|F>]
            [SP<imm3>] [SC<imm4>]
            [DB<1-16>] [DS<8|16|32|64|128>] [DA<I|F>]
            [DP<imm3>] [DC<imm4>]
            [ES<8|16|32|64|128>]

\endverbatim
* with a DMAMOV instruction (see: alt_dma_program_DMAMOV()).
*
* For example the assembler directive:
\verbatim
DMAMOV CCR SB1 SS32 DB1 DS32
\endverbatim
* would be dynamically programmed with the following API call:
\verbatim
alt_dma_program_DMAMOV( pgm,
                        ALT_DMA_PROGRAM_REG_CCR,
                        (   ALT_DMA_CCR_OPT_SB1
                          | ALT_DMA_CCR_OPT_SS32
                          | ALT_DMA_CCR_OPT_SA_DEFAULT
                          | ALT_DMA_CCR_OPT_SP_DEFAULT
                          | ALT_DMA_CCR_OPT_SC_DEFAULT
                          | ALT_DMA_CCR_OPT_DB1
                          | ALT_DMA_CCR_OPT_DS32
                          | ALT_DMA_CCR_OPT_DA_DEFAULT
                          | ALT_DMA_CCR_OPT_DP_DEFAULT
                          | ALT_DMA_CCR_OPT_DC_DEFAULT
                          | ALT_DMA_CCR_OPT_ES8
                        )
                      );
\endverbatim
*
* Each CCR option category should be specified regardless of whether it
* specifies a custom value or the normal default value (i.e. an
* ALT_DMA_CCR_OPT_*_DEFAULT.
*
* @{
*/

/*
 * Source Address {Fixed,Incrementing}
 */
/*! Source Address Fixed address burst. */
#define ALT_DMA_CCR_OPT_SAF         (0 << 0)
/*! Source Address Incrementing address burst. */
#define ALT_DMA_CCR_OPT_SAI         (1 << 0)
/*! Source Address Default value. */
#define ALT_DMA_CCR_OPT_SA_DEFAULT  ALT_DMA_CCR_OPT_SAI

/*
 * Source burst Size (in bits)
 */
/*! Source burst Size of 8 bits. */
#define ALT_DMA_CCR_OPT_SS8         (0 << 1)
/*! Source burst Size of 16 bits. */
#define ALT_DMA_CCR_OPT_SS16        (1 << 1)
/*! Source burst Size of 32 bits. */
#define ALT_DMA_CCR_OPT_SS32        (2 << 1)
/*! Source burst Size of 64 bits. */
#define ALT_DMA_CCR_OPT_SS64        (3 << 1)
/*! Source burst Size of 128 bits. */
#define ALT_DMA_CCR_OPT_SS128       (4 << 1)
/*! Source burst Size default bits. */
#define ALT_DMA_CCR_OPT_SS_DEFAULT  ALT_DMA_CCR_OPT_SS8

/*
 * Source burst Length (in transfer(s))
 */
/*! Source Burst length of 1 transfer. */
#define ALT_DMA_CCR_OPT_SB1         (0x0 << 4)
/*! Source Burst length of 2 transfers. */
#define ALT_DMA_CCR_OPT_SB2         (0x1 << 4)
/*! Source Burst length of 3 transfers. */
#define ALT_DMA_CCR_OPT_SB3         (0x2 << 4)
/*! Source Burst length of 4 transfers. */
#define ALT_DMA_CCR_OPT_SB4         (0x3 << 4)
/*! Source Burst length of 5 transfers. */
#define ALT_DMA_CCR_OPT_SB5         (0x4 << 4)
/*! Source Burst length of 6 transfers. */
#define ALT_DMA_CCR_OPT_SB6         (0x5 << 4)
/*! Source Burst length of 7 transfers. */
#define ALT_DMA_CCR_OPT_SB7         (0x6 << 4)
/*! Source Burst length of 8 transfers. */
#define ALT_DMA_CCR_OPT_SB8         (0x7 << 4)
/*! Source Burst length of 9 transfers. */
#define ALT_DMA_CCR_OPT_SB9         (0x8 << 4)
/*! Source Burst length of 10 transfers. */
#define ALT_DMA_CCR_OPT_SB10        (0x9 << 4)
/*! Source Burst length of 11 transfers. */
#define ALT_DMA_CCR_OPT_SB11        (0xa << 4)
/*! Source Burst length of 12 transfers. */
#define ALT_DMA_CCR_OPT_SB12        (0xb << 4)
/*! Source Burst length of 13 transfers. */
#define ALT_DMA_CCR_OPT_SB13        (0xc << 4)
/*! Source Burst length of 14 transfers. */
#define ALT_DMA_CCR_OPT_SB14        (0xd << 4)
/*! Source Burst length of 15 transfers. */
#define ALT_DMA_CCR_OPT_SB15        (0xe << 4)
/*! Source Burst length of 16 transfers. */
#define ALT_DMA_CCR_OPT_SB16        (0xf << 4)
/*! Source Burst length default transfers. */
#define ALT_DMA_CCR_OPT_SB_DEFAULT  ALT_DMA_CCR_OPT_SB1

/*
 * Source Protection
 */
/*! Source Protection bits for AXI bus ARPROT[2:0]. */
#define ALT_DMA_CCR_OPT_SP(imm3)    ((imm3) << 8)
/*! Source Protection bits default value. */
#define ALT_DMA_CCR_OPT_SP_DEFAULT  ALT_DMA_CCR_OPT_SP(0)

/*
 * Source cache
 */
/*! Source Cache bits for AXI bus ARCACHE[2:0]. */
#define ALT_DMA_CCR_OPT_SC(imm4)    ((imm4) << 11)
/*! Source Cache bits default value. */
#define ALT_DMA_CCR_OPT_SC_DEFAULT  ALT_DMA_CCR_OPT_SC(0)

/*
 * Destination Address {Fixed,Incrementing}
 */
/*! Destination Address Fixed address burst. */
#define ALT_DMA_CCR_OPT_DAF         (0 << 14)
/*! Destination Address Incrementing address burst. */
#define ALT_DMA_CCR_OPT_DAI         (1 << 14)
/*! Destination Address Default value. */
#define ALT_DMA_CCR_OPT_DA_DEFAULT  ALT_DMA_CCR_OPT_DAI

/*
 * Destination burst Size (in bits)
 */
/*! Destination burst Size of 8 bits. */
#define ALT_DMA_CCR_OPT_DS8         (0 << 15)
/*! Destination burst Size of 16 bits. */
#define ALT_DMA_CCR_OPT_DS16        (1 << 15)
/*! Destination burst Size of 32 bits. */
#define ALT_DMA_CCR_OPT_DS32        (2 << 15)
/*! Destination burst Size of 64 bits. */
#define ALT_DMA_CCR_OPT_DS64        (3 << 15)
/*! Destination burst Size of 128 bits. */
#define ALT_DMA_CCR_OPT_DS128       (4 << 15)
/*! Destination burst Size default bits. */
#define ALT_DMA_CCR_OPT_DS_DEFAULT  ALT_DMA_CCR_OPT_DS8

/*
 * Destination Burst length (in transfer(s))
 */
/*! Destination Burst length of 1 transfer. */
#define ALT_DMA_CCR_OPT_DB1         (0x0 << 18)
/*! Destination Burst length of 2 transfers. */
#define ALT_DMA_CCR_OPT_DB2         (0x1 << 18)
/*! Destination Burst length of 3 transfers. */
#define ALT_DMA_CCR_OPT_DB3         (0x2 << 18)
/*! Destination Burst length of 4 transfers. */
#define ALT_DMA_CCR_OPT_DB4         (0x3 << 18)
/*! Destination Burst length of 5 transfers. */
#define ALT_DMA_CCR_OPT_DB5         (0x4 << 18)
/*! Destination Burst length of 6 transfers. */
#define ALT_DMA_CCR_OPT_DB6         (0x5 << 18)
/*! Destination Burst length of 7 transfers. */
#define ALT_DMA_CCR_OPT_DB7         (0x6 << 18)
/*! Destination Burst length of 8 transfers. */
#define ALT_DMA_CCR_OPT_DB8         (0x7 << 18)
/*! Destination Burst length of 9 transfers. */
#define ALT_DMA_CCR_OPT_DB9         (0x8 << 18)
/*! Destination Burst length of 10 transfers. */
#define ALT_DMA_CCR_OPT_DB10        (0x9 << 18)
/*! Destination Burst length of 11 transfers. */
#define ALT_DMA_CCR_OPT_DB11        (0xa << 18)
/*! Destination Burst length of 12 transfers. */
#define ALT_DMA_CCR_OPT_DB12        (0xb << 18)
/*! Destination Burst length of 13 transfers. */
#define ALT_DMA_CCR_OPT_DB13        (0xc << 18)
/*! Destination Burst length of 14 transfers. */
#define ALT_DMA_CCR_OPT_DB14        (0xd << 18)
/*! Destination Burst length of 15 transfers. */
#define ALT_DMA_CCR_OPT_DB15        (0xe << 18)
/*! Destination Burst length of 16 transfers. */
#define ALT_DMA_CCR_OPT_DB16        (0xf << 18)
/*! Destination Burst length default transfers. */
#define ALT_DMA_CCR_OPT_DB_DEFAULT  ALT_DMA_CCR_OPT_DB1

/*
 * Destination Protection
 */
/*! Destination Protection bits for AXI bus AWPROT[2:0]. */
#define ALT_DMA_CCR_OPT_DP(imm3)    ((imm3) << 22)
/*! Destination Protection bits default value. */
#define ALT_DMA_CCR_OPT_DP_DEFAULT  ALT_DMA_CCR_OPT_DP(0)

/*
 * Destination Cache
 */
/*! Destination Cache bits for AXI bus AWCACHE[3,1:0]. */
#define ALT_DMA_CCR_OPT_DC(imm4)    ((imm4) << 25)
/*! Destination Cache bits default value. */
#define ALT_DMA_CCR_OPT_DC_DEFAULT  ALT_DMA_CCR_OPT_DC(0)

/*
 * Endian Swap size (in bits)
 */
/*! Endian Swap: No swap, 8-bit data. */
#define ALT_DMA_CCR_OPT_ES8         (0 << 28)
/*! Endian Swap: Swap bytes within 16-bit data. */
#define ALT_DMA_CCR_OPT_ES16        (1 << 28)
/*! Endian Swap: Swap bytes within 32-bit data. */
#define ALT_DMA_CCR_OPT_ES32        (2 << 28)
/*! Endian Swap: Swap bytes within 64-bit data. */
#define ALT_DMA_CCR_OPT_ES64        (3 << 28)
/*! Endian Swap: Swap bytes within 128-bit data. */
#define ALT_DMA_CCR_OPT_ES128       (4 << 28)
/*! Endian Swap: Default byte swap. */
#define ALT_DMA_CCR_OPT_ES_DEFAULT  ALT_DMA_CCR_OPT_ES8

/*! Default CCR register options for a DMAMOV CCR assembler directive. */
#define ALT_DMA_CCR_OPT_DEFAULT \
    (ALT_DMA_CCR_OPT_SB1 | ALT_DMA_CCR_OPT_SS8 | ALT_DMA_CCR_OPT_SAI | \
     ALT_DMA_CCR_OPT_SP(0) | ALT_DMA_CCR_OPT_SC(0) | \
     ALT_DMA_CCR_OPT_DB1 | ALT_DMA_CCR_OPT_DS8 | ALT_DMA_CCR_OPT_DAI | \
     ALT_DMA_CCR_OPT_DP(0) | ALT_DMA_CCR_OPT_DC(0) | \
     ALT_DMA_CCR_OPT_ES8)

/*!
 * @}
 */

/*!
 * @}
 */

#ifdef __cplusplus
}
#endif  /* __cplusplus */

#endif /* __ALT_DMA_PROGRAM_H__ */
