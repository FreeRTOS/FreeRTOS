/******************************************************************************
*
* Copyright (C) 2018 Xilinx, Inc.  All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
* XILINX  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/
/*****************************************************************************/

/**
 *
 * @file xqspipsu.h
 * @addtogroup qspipsu_v1_7
 * @{
 * @details
 *
 * This is the header file for the implementation of QSPIPSU driver.
 * Generic QSPI interface allows for communication to any QSPI slave device.
 * GQSPI contains a GENFIFO into which the bus transfers required are to be
 * pushed with appropriate configuration. The controller provides TX and RX
 * FIFO's and a DMA to be used for RX transfers. The controller executes each
 * GENFIFO entry noting the configuration and places data on the bus as required
 *
 * The different options in GENFIFO are as follows:
 * IMM_DATA : Can be one byte of data to be transmitted, number of clocks or
 *            number of bytes in transfer.
 * DATA_XFER : Indicates that data/clocks need to be transmitted or received.
 * EXPONENT : e when 2^e bytes are involved in transfer.
 * SPI_MODE : SPI/Dual SPI/Quad SPI
 * CS : Lower or Upper CS or Both
 * Bus : Lower or Upper Bus or Both
 * TX : When selected, controller transmits data in IMM or fetches number of
 *      bytes mentioned form TX FIFO. If not selected, dummies are pumped.
 * RX : When selected, controller receives and fills the RX FIFO/allows RX DMA
 *      of requested number of bytes. If not selected, RX data is discarded.
 * Stripe : Byte stripe over lower and upper bus or not.
 * Poll : Polls response to match for to a set value (used along with POLL_CFG
 *        registers) and then proceeds to next GENFIFO entry.
 *        This feature is not currently used in the driver.
 *
 * GENFIFO has manual and auto start options.
 * All DMA requests need a 4-byte aligned destination address buffer and
 * size of transfer should also be a multiple of 4.
 * This driver supports DMA RX and IO RX.
 *
 * Initialization:
 * This driver uses the GQSPI controller with RX DMA. It supports both
 * interrupt and polled transfers. Manual start of GENFIFO is used.
 * XQspiPsu_CfgInitialize() initializes the instance variables.
 * Additional setting can be done using SetOptions/ClearOptions functions
 * and SelectSlave function.
 *
 * Transfer:
 * Polled or Interrupt transfers can be done. The transfer function needs the
 * message(s) to be transmitted in the form of an array of type XQspiPsu_Msg.
 * This is supposed to contain the byte count and any TX/RX buffers as required.
 * Flags can be used indicate further information such as whether the message
 * should be striped. The transfer functions form and write GENFIFO entries,
 * check the status of the transfer and report back to the application
 * when done.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who Date     Changes
 * ----- --- -------- -----------------------------------------------.
 * 1.0   hk  08/21/14 First release
 *       sk  03/13/15 Added IO mode support.
 *       hk  03/18/15 Switch to I/O mode before clearing RX FIFO.
 *                    Clear and disbale DMA interrupts/status in abort.
 *                    Use DMA DONE bit instead of BUSY as recommended.
 *       sk  04/24/15 Modified the code according to MISRAC-2012.
 *       sk  06/17/15 Removed NULL checks for Rx/Tx buffers. As
 *                    writing/reading from 0x0 location is permitted.
 * 1.1   sk  04/12/16 Added debug message prints.
 * 1.2	nsk 07/01/16 Added LQSPI support
 *		     Modified XQspiPsu_Select() macro in xqspipsu.h
 *		     Added XQspiPsu_GetLqspiConfigReg() in xqspipsu.h
 *		     Added required macros in xqspipsu_hw.h
 *		     Modified XQspiPsu_SetOptions() to support
 *		     LQSPI options and updated OptionsTable in
 *		     xqspipsu_options.c
 *       rk  07/15/16 Added support for TapDelays at different frequencies.
 *	nsk 08/05/16 Added example support PollData and PollTimeout
 *		     Added  XQSPIPSU_MSG_FLAG_POLL macro in xqspipsu.h
 *		     Added XQspiPsu_Create_PollConfigData and
 *		     XQspiPsu_PollData() functions in xqspipsu.c
 * 1.3	nsk 09/16/16 Update PollData and Polltimeout support for dual parallel
 *	             configuration. Updated XQspiPsu_PollData() and
 *	             XQspiPsu_Create_PollConfigData() functions in xqspipsu.c
 *                    and also modified the polldata example
 *       ms  03/17/17 Added readme.txt file in examples folder for doxygen
 *                    generation.
 *       ms  04/05/17 Modified Comment lines in functions of qspipsu
 *                    examples to recognize it as documentation block
 *                    and modified filename tag to include them in
 *                    doxygen examples.
 * 1.4	tjs 05/26/17 Added support for accessing upper DDR (0x800000000)
 *		     while booting images from QSPI
 * 1.5	tjs	08/08/17 Added index.html file for importing examples from system.mss
 * 1.5	nsk 08/14/17 Added CCI support
 * 1.5	tjs 09/14/17 Modified the checks for 4 byte addressing and commands.
 * 1.6	tjs 10/16/17 Flow for accessing flash is made similar to u-boot and linux
 *                   For CR-984966
 * 1.6   tjs 11/02/17 Resolved the compilation errors for ICCARM. CR-988625
 * 1.7   tjs 11/16/17 Removed the unsupported 4 Byte write and sector erase
 *                    commands.
 * 1.7	tjs	12/01/17 Added support for MT25QL02G Flash from Micron. CR-990642
 * 1.7	tjs 12/19/17 Added support for S25FL064L from Spansion. CR-990724
 * 1.7	tjs 01/11/18 Added support for MX66L1G45G flash from Macronix CR-992367
 * 1.7	tjs	01/16/18 Removed the check for DMA MSB to be written. (CR#992560)
 * 1.7	tjs	01/17/18 Added support to toggle the WP pin of flash. (PR#2448)
 *                    Added XQspiPsu_SetWP() in xqspipsu_options.c
 *                    Added XQspiPsu_WriteProtectToggle() in xqspipsu.c and
 *                    also added write protect example.
 * 1.7	tjs	03/14/18 Added support in EL1 NS mode (CR#974882)
 * 1.7	tjs 26/03/18 In dual parallel mode enable both CS when issuing Write
 *		             enable command. CR-998478
 * </pre>
 *
 ******************************************************************************/
#ifndef XQSPIPSU_H_     /* prevent circular inclusions */
    #define XQSPIPSU_H_ /* by using protection macros */

    #ifdef __cplusplus
    extern "C" {
    #endif

/***************************** Include Files *********************************/

    #include "xstatus.h"
    #include "xqspipsu_hw.h"
    #include "xil_cache.h"

/**************************** Type Definitions *******************************/

/**
 * The handler data type allows the user to define a callback function to
 * handle the asynchronous processing for the QSPIPSU device.  The application
 * using this driver is expected to define a handler of this type to support
 * interrupt driven mode.  The handler executes in an interrupt context, so
 * only minimal processing should be performed.
 *
 * @param	CallBackRef is the callback reference passed in by the upper
 *		layer when setting the callback functions, and passed back to
 *		the upper layer when the callback is invoked. Its type is
 *		not important to the driver, so it is a void pointer.
 * @param   StatusEvent holds one or more status events that have occurred.
 *		See the XQspiPsu_SetStatusHandler() for details on the status
 *		events that can be passed in the callback.
 * @param	ByteCount indicates how many bytes of data were successfully
 *		transferred.  This may be less than the number of bytes
 *		requested if the status event indicates an error.
 */
    typedef void (* XQspiPsu_StatusHandler) ( void * CallBackRef,
                                              u32 StatusEvent,
                                              u32 ByteCount );

/**
 * This typedef contains configuration information for a flash message.
 */
    typedef struct
    {
        u8 * TxBfrPtr;
        u8 * RxBfrPtr;
        u32 ByteCount;
        u32 BusWidth;
        u32 Flags;
        u8 PollData;
        u32 PollTimeout;
        u8 PollStatusCmd;
        u8 PollBusMask;
    } XQspiPsu_Msg;

/**
 * This typedef contains configuration information for the device.
 */
    typedef struct
    {
        u16 DeviceId;       /**< Unique ID  of device */
        u32 BaseAddress;    /**< Base address of the device */
        u32 InputClockHz;   /**< Input clock frequency */
        u8 ConnectionMode;  /**< Single, Stacked and Parallel mode */
        u8 BusWidth;        /**< Bus width available on board */
        u8 IsCacheCoherent; /**< Describes whether Cache Coherent or not */
    } XQspiPsu_Config;

/**
 * The XQspiPsu driver instance data. The user is required to allocate a
 * variable of this type for every QSPIPSU device in the system. A pointer
 * to a variable of this type is then passed to the driver API functions.
 */
    typedef struct
    {
        XQspiPsu_Config Config; /**< Configuration structure */
        u32 IsReady;            /**< Device is initialized and ready */

        u8 * SendBufferPtr;     /**< Buffer to send (state) */
        u8 * RecvBufferPtr;     /**< Buffer to receive (state) */
        u8 * GenFifoBufferPtr;  /**< Gen FIFO entries */
        s32 TxBytes;            /**< Number of bytes to transfer (state) */
        s32 RxBytes;            /**< Number of bytes left to transfer(state) */
        s32 GenFifoEntries;     /**< Number of Gen FIFO entries remaining */
        u32 IsBusy;             /**< A transfer is in progress (state) */
        u32 ReadMode;           /**< DMA or IO mode */
        u32 GenFifoCS;
        u32 GenFifoBus;
        s32 NumMsg;
        s32 MsgCnt;
        s32 IsUnaligned;
        u8 IsManualstart;
        XQspiPsu_Msg * Msg;
        XQspiPsu_StatusHandler StatusHandler;
        void * StatusRef; /**< Callback reference for status handler */
    } XQspiPsu;

/***************** Macros (Inline Functions) Definitions *********************/

    #define XQSPIPSU_READMODE_DMA                0x0U
    #define XQSPIPSU_READMODE_IO                 0x1U

    #define XQSPIPSU_SELECT_FLASH_CS_LOWER       0x1U
    #define XQSPIPSU_SELECT_FLASH_CS_UPPER       0x2U
    #define XQSPIPSU_SELECT_FLASH_CS_BOTH        0x3U

    #define XQSPIPSU_SELECT_FLASH_BUS_LOWER      0x1U
    #define XQSPIPSU_SELECT_FLASH_BUS_UPPER      0x2U
    #define XQSPIPSU_SELECT_FLASH_BUS_BOTH       0x3U

    #define XQSPIPSU_SELECT_MODE_SPI             0x1U
    #define XQSPIPSU_SELECT_MODE_DUALSPI         0x2U
    #define XQSPIPSU_SELECT_MODE_QUADSPI         0x4U

    #define XQSPIPSU_GENFIFO_CS_SETUP            0x05U
    #define XQSPIPSU_GENFIFO_CS_HOLD             0x04U

    #define XQSPIPSU_CLK_ACTIVE_LOW_OPTION       0x2U
    #define XQSPIPSU_CLK_PHASE_1_OPTION          0x4U
    #define XQSPIPSU_MANUAL_START_OPTION         0x8U
    #define XQSPIPSU_LQSPI_MODE_OPTION           0x20U

    #define XQSPIPSU_GENFIFO_EXP_START           0x100U

    #define XQSPIPSU_DMA_BYTES_MAX               0x10000000U

    #define XQSPIPSU_CLK_PRESCALE_2              0x00U
    #define XQSPIPSU_CLK_PRESCALE_4              0x01U
    #define XQSPIPSU_CLK_PRESCALE_8              0x02U
    #define XQSPIPSU_CLK_PRESCALE_16             0x03U
    #define XQSPIPSU_CLK_PRESCALE_32             0x04U
    #define XQSPIPSU_CLK_PRESCALE_64             0x05U
    #define XQSPIPSU_CLK_PRESCALE_128            0x06U
    #define XQSPIPSU_CLK_PRESCALE_256            0x07U
    #define XQSPIPSU_CR_PRESC_MAXIMUM            7U

    #define XQSPIPSU_CONNECTION_MODE_SINGLE      0U
    #define XQSPIPSU_CONNECTION_MODE_STACKED     1U
    #define XQSPIPSU_CONNECTION_MODE_PARALLEL    2U

/*QSPI Frequencies*/
    #define XQSPIPSU_FREQ_40MHZ                  40000000
    #define XQSPIPSU_FREQ_100MHZ                 100000000
    #define XQSPIPSU_FREQ_150MHZ                 150000000

/* Add more flags as required */
    #define XQSPIPSU_MSG_FLAG_STRIPE             0x1U
    #define XQSPIPSU_MSG_FLAG_RX                 0x2U
    #define XQSPIPSU_MSG_FLAG_TX                 0x4U
    #define XQSPIPSU_MSG_FLAG_POLL               0x8U

/* GQSPI configuration to toggle WP of flash*/
    #define XQSPIPSU_SET_WP                      1

    #define XQspiPsu_Select( InstancePtr, Mask )         XQspiPsu_Out32( ( ( InstancePtr )->Config.BaseAddress ) + XQSPIPSU_SEL_OFFSET, Mask )

    #define XQspiPsu_Enable( InstancePtr )               XQspiPsu_Out32( ( ( InstancePtr )->Config.BaseAddress ) + XQSPIPSU_EN_OFFSET, XQSPIPSU_EN_MASK )

    #define XQspiPsu_Disable( InstancePtr )              XQspiPsu_Out32( ( ( InstancePtr )->Config.BaseAddress ) + XQSPIPSU_EN_OFFSET, 0x0U )

    #define XQspiPsu_GetLqspiConfigReg( InstancePtr )    XQspiPsu_In32( ( XQSPIPS_BASEADDR ) + XQSPIPSU_LQSPI_CR_OFFSET )


/************************** Function Prototypes ******************************/

/* Initialization and reset */
    XQspiPsu_Config * XQspiPsu_LookupConfig( u16 DeviceId );
    s32 XQspiPsu_CfgInitialize( XQspiPsu * InstancePtr,
                                XQspiPsu_Config * ConfigPtr,
                                u32 EffectiveAddr );
    void XQspiPsu_Reset( XQspiPsu * InstancePtr );
    void XQspiPsu_Abort( XQspiPsu * InstancePtr );

/* Transfer functions and handlers */
    s32 XQspiPsu_PolledTransfer( XQspiPsu * InstancePtr,
                                 XQspiPsu_Msg * Msg,
                                 u32 NumMsg );
    s32 XQspiPsu_InterruptTransfer( XQspiPsu * InstancePtr,
                                    XQspiPsu_Msg * Msg,
                                    u32 NumMsg );
    s32 XQspiPsu_InterruptHandler( XQspiPsu * InstancePtr );
    void XQspiPsu_SetStatusHandler( XQspiPsu * InstancePtr,
                                    void * CallBackRef,
                                    XQspiPsu_StatusHandler FuncPointer );

/* Configuration functions */
    s32 XQspiPsu_SetClkPrescaler( XQspiPsu * InstancePtr,
                                  u8 Prescaler );
    void XQspiPsu_SelectFlash( XQspiPsu * InstancePtr,
                               u8 FlashCS,
                               u8 FlashBus );
    s32 XQspiPsu_SetOptions( XQspiPsu * InstancePtr,
                             u32 Options );
    s32 XQspiPsu_ClearOptions( XQspiPsu * InstancePtr,
                               u32 Options );
    u32 XQspiPsu_GetOptions( XQspiPsu * InstancePtr );
    s32 XQspiPsu_SetReadMode( XQspiPsu * InstancePtr,
                              u32 Mode );
    void XQspiPsu_SetWP( XQspiPsu * InstancePtr,
                         u8 Value );
    void XQspiPsu_WriteProtectToggle( XQspiPsu * InstancePtr,
                                      u32 Toggle );

    #ifdef __cplusplus
}
    #endif


#endif /* XQSPIPSU_H_ */
/** @} */
