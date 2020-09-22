/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products. No 
* other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all 
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, 
* FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED. TO THE MAXIMUM 
* EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES 
* SHALL BE LIABLE FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS 
* SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability of 
* this software. By using this software, you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer 
*
* Copyright (C) 2016-2019 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/**********************************************************************************************************************
* File Name    : r_sci_rx.c
* Description  : Functions for using SCI on RX devices. 
***********************************************************************************************************************
* History : DD.MM.YYYY Version Description
*           01.10.2016 1.80    Initial Release. (The remake of the r01an1815ju0170 to the base.)
*           19.12.2016 1.90    FIT_NO_PTR check added to NULL check.
*                              Fixed a bug that may receive data more than the specified number of bytes
*                               on Clock Synchronous Mode.
*                              Fixed that R_SCI_Control function returns SCI_ERR_INVALID_ARG
*                               when using SCI_CMD_EN_CTS_IN on Simple SPI mode.
*                              Fix to clear error flag even if callback function is not set.
*                              Deleted unnecessary bit mask of SSR register from sci_error function.
*           07.03.2017 2.00    Fixed a bug that error condition not clear when FIFO enabled.
*                              Fixed a bug that where commands used only when FIFO mode is enable did not NULL check.
*                              Fixed a bug that sending data is overwrote by new R_SCI_Send() when FIFO(async) enabled.
*                              Fixed a bug that sending data is break up by new R_SCI_Send() when FIFO(sync) enabled.
*                              Fixed a bug that the new FIFO threshold was retained only on first receive.
*                              Fixed a bug that callback function work many times at receive interrupt
*                               when FIFO(async) enabled.
*                              Fixed a bug that the interrupt priority level can be changed only in async mode.
*          28.09.2018  2.10    Added support RX66T
*                              Add WAIT_LOOP comments.
*                              Fixed a bug that leaking memory in R_SCI_Open() when FIFO(async) enabled.
*                              Fix GSCE Code Checker errors.
*          01.02.2019  2.20    Added support RX72T, RX65N-64pin.
*                              Fix GSCE Code Checker errors.
*          20.05.2019  3.00    Added support for GNUC and ICCRX.
*          28.06.2019  3.10    Added support for RX23W
*          15.08.2019  3.20    Added support for RX72M
*          25.11.2019  3.30    Added support RX13T.
*                              Modified comment of API function to Doxygen style.
*                              Added support for atomic control.
*                              Fixed to comply with GSCE Coding Standards Rev.6.00.
*                              Fixed a bug that error when a reception interrupt occurs before incrementing "u_tx_data.buf"
*                               in "sci_send_sync_data" and "sci_receive" functions
*          30.12.2019  3.40    Added support RX66N, RX72N.
***********************************************************************************************************************/

/*****************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include "platform.h"

/* Defines for SCI support */
#include "r_sci_rx_private.h"

/* Include specifics for chosen MCU.  */
#include "r_sci_rx_platform.h"

#if (SCI_CFG_ASYNC_INCLUDED)
#include "r_byteq_if.h"
#endif


/*****************************************************************************
Typedef definitions
******************************************************************************/

/*****************************************************************************
Macro definitions
******************************************************************************/

/*****************************************************************************
Private global variables and functions
******************************************************************************/
#if (SCI_CFG_ASYNC_INCLUDED)
static sci_err_t sci_init_async(sci_hdl_t const     hdl,
                                sci_uart_t * const  p_cfg,
                                uint8_t * const     p_priority);

static sci_err_t sci_init_queues(uint8_t const  chan);

static sci_err_t sci_send_async_data(sci_hdl_t const hdl,
                                     uint8_t         *p_src,
                                     uint16_t const  length);

static byteq_err_t sci_put_byte(sci_hdl_t const    hdl,
                                uint8_t const      byte);

static void sci_transfer(sci_hdl_t const hdl);

#if SCI_CFG_FIFO_INCLUDED
static void sci_fifo_transfer(sci_hdl_t const hdl);
#endif

static sci_err_t sci_receive_async_data(sci_hdl_t const hdl,
                                        uint8_t         *p_dst,
                                        uint16_t const  length);
#endif

#if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
static sci_err_t sci_init_sync(sci_hdl_t const         hdl,
                               sci_sync_sspi_t * const p_cfg,
                               uint8_t * const         p_priority);

static sci_err_t sci_send_sync_data(sci_hdl_t const hdl,
                                    uint8_t         *p_src,
                                    uint8_t         *p_dst,
                                    uint16_t const  length,
                                    bool            save_rx_data);

static sci_err_t sci_receive_sync_data(sci_hdl_t const hdl,
                                       uint8_t         *p_dst,
                                       uint16_t const  length);
#endif

static void power_on(sci_hdl_t const hdl);
static void power_off(sci_hdl_t const hdl);

#if SCI_CFG_FIFO_INCLUDED
static sci_err_t sci_init_fifo(sci_hdl_t const hdl);
#endif

static void sci_receive(sci_hdl_t const hdl);

#if SCI_CFG_FIFO_INCLUDED

#if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
static void sci_fifo_receive_sync(sci_hdl_t const hdl);
#endif

static void sci_fifo_receive(sci_hdl_t const hdl);

#endif

#if SCI_CFG_DATA_MATCH_INCLUDED
static void sci_receive_data_match(sci_hdl_t const hdl);
#endif

static void sci_error(sci_hdl_t const hdl);

#if SCI_CFG_FIFO_INCLUDED
static void sci_fifo_error(sci_hdl_t const hdl);
#endif

/* queue buffers */
#if (SCI_CFG_ASYNC_INCLUDED)

#if SCI_CFG_CH0_INCLUDED
static uint8_t  ch0_tx_buf[SCI_CFG_CH0_TX_BUFSIZ];
static uint8_t  ch0_rx_buf[SCI_CFG_CH0_RX_BUFSIZ];
#endif

#if SCI_CFG_CH1_INCLUDED
static uint8_t  ch1_tx_buf[SCI_CFG_CH1_TX_BUFSIZ];
static uint8_t  ch1_rx_buf[SCI_CFG_CH1_RX_BUFSIZ];
#endif

#if SCI_CFG_CH2_INCLUDED
static uint8_t  ch2_tx_buf[SCI_CFG_CH2_TX_BUFSIZ];
static uint8_t  ch2_rx_buf[SCI_CFG_CH2_RX_BUFSIZ];
#endif

#if SCI_CFG_CH3_INCLUDED
static uint8_t  ch3_tx_buf[SCI_CFG_CH3_TX_BUFSIZ];
static uint8_t  ch3_rx_buf[SCI_CFG_CH3_RX_BUFSIZ];
#endif

#if SCI_CFG_CH4_INCLUDED
static uint8_t  ch4_tx_buf[SCI_CFG_CH4_TX_BUFSIZ];
static uint8_t  ch4_rx_buf[SCI_CFG_CH4_RX_BUFSIZ];
#endif

#if SCI_CFG_CH5_INCLUDED
static uint8_t  ch5_tx_buf[SCI_CFG_CH5_TX_BUFSIZ];
static uint8_t  ch5_rx_buf[SCI_CFG_CH5_RX_BUFSIZ];
#endif

#if SCI_CFG_CH6_INCLUDED
static uint8_t  ch6_tx_buf[SCI_CFG_CH6_TX_BUFSIZ];
static uint8_t  ch6_rx_buf[SCI_CFG_CH6_RX_BUFSIZ];
#endif

#if SCI_CFG_CH7_INCLUDED
static uint8_t  ch7_tx_buf[SCI_CFG_CH7_TX_BUFSIZ];
static uint8_t  ch7_rx_buf[SCI_CFG_CH7_RX_BUFSIZ];
#endif

#if SCI_CFG_CH8_INCLUDED
static uint8_t  ch8_tx_buf[SCI_CFG_CH8_TX_BUFSIZ];
static uint8_t  ch8_rx_buf[SCI_CFG_CH8_RX_BUFSIZ];
#endif

#if SCI_CFG_CH9_INCLUDED
static uint8_t  ch9_tx_buf[SCI_CFG_CH9_TX_BUFSIZ];
static uint8_t  ch9_rx_buf[SCI_CFG_CH9_RX_BUFSIZ];
#endif

#if SCI_CFG_CH10_INCLUDED
static uint8_t  ch10_tx_buf[SCI_CFG_CH10_TX_BUFSIZ];
static uint8_t  ch10_rx_buf[SCI_CFG_CH10_RX_BUFSIZ];
#endif

#if SCI_CFG_CH11_INCLUDED
static uint8_t  ch11_tx_buf[SCI_CFG_CH11_TX_BUFSIZ];
static uint8_t  ch11_rx_buf[SCI_CFG_CH11_RX_BUFSIZ];
#endif

#if SCI_CFG_CH12_INCLUDED
static uint8_t  ch12_tx_buf[SCI_CFG_CH12_TX_BUFSIZ];
static uint8_t  ch12_rx_buf[SCI_CFG_CH12_RX_BUFSIZ];
#endif

#endif /* #if (SCI_CFG_ASYNC_INCLUDED) */

extern const sci_hdl_t g_handles[SCI_NUM_CH];


/***********************************************************************************************************************
* Function Name: R_SCI_Open
********************************************************************************************************************//**
* @brief This function applies power to the SCI channel, initializes the associated registers, enables interrupts, and
* provides the channel handle for use with other API functions. This function must be called before calling any
* other API functions
* @param[in]    chan  Channel to initialize.
*
* @param[in]    mode  Operational mode (see enumeration below)
* @code
typedef enum e_sci_mode     // SCI operational modes
{
    SCI_MODE_OFF=0,         // channel not in use
    SCI_MODE_ASYNC,         // Asynchronous
    SCI_MODE_SSPI,          // Simple SPI
    SCI_MODE_SYNC,          // Synchronous
    SCI_MODE_MAX            // End of modes currently supported
} sci_mode_t;
* @endcode
* @param[in]    p_cfg  Pointer to configuration union, structure elements (see below) are specific to mode
* @code
typedef union
{
    sci_uart_t      async;
    sci_sync_sspi_t sync;
    sci_sync_sspi_t sspi;
} sci_cfg_t;
* @endcode
*
* @param[in]    p_callback Pointer to function called from interrupt when an RXI or receiver error is detected or
* for transmit end (TEI) condition. See Section 2.11 Callback Function in application note for details.
*
* @param[in]    p_hdl  Pointer to a handle for channel (value set here)
* Confirm the return value from R_SCI_Open is “SCI_SUCCESS” and then set the first parameter for the
* other APIs except R_SCI_GetVersion(). See Section 2.9 Parameters in the application note for details.
*
*
* @retval   SCI_SUCCESS  Successful; channel initialized 
*
* @retval   SCI_ERR_BAD_CHAN  Channel number is invalid for part
*
* @retval   SCI_ERR_OMITTED_CHAN  Corresponding SCI_CHx_INCLUDED is invalid (0) 
*
* @retval   SCI_ERR_CH_NOT_CLOSED  Channel currently in operation; Perform R_SCI_Close() first
*
* @retval   SCI_ERR_BAD_MODE  Mode specified not currently supported
*
* @retval   SCI_ERR_NULL_PTR  p_cfg pointer is NULL
*
* @retval   SCI_ERR_INVALID_ARG  An element of the p_cfg structure contains an invalid value.
*
* @retval   SCI_ERR_QUEUE_UNAVAILABLE  Cannot open transmit or receive queue or both (Asynchronous mode).
* @details  Initializes an SCI channel for a particular mode and provides a Handle in *p_hdl for use with other API
* functions. RXI and ERI interrupts are enabled in all modes. TXI is enabled in Asynchronous mode
* @note  The driver calculates the optimum values for BRR, SEMR.ABCS, and SMR.CKS using BSP_PCLKA_HZ and
* BSP_PCLKB_HZ as defined in mcu_info.h of the board support package. This however does not guarantee
* a low bit error rate for all peripheral clock/baud rate combinations.
* If an external clock is used in Asynchronous mode, the pin direction must be selected before calling the
* R_SCI_Open() function, and the pin function and mode must be selected after calling the R_SCI_Open()
* function. See Section 3. R_SCI_Open() in the application note for details.
*/
sci_err_t R_SCI_Open(uint8_t const      chan,
                     sci_mode_t const   mode,
                     sci_cfg_t * const  p_cfg,
                     void               (* const p_callback)(void *p_args),
                     sci_hdl_t * const  p_hdl)
{
    sci_err_t   err = SCI_SUCCESS;
    uint8_t     priority = 1;

    /* CHECK ARGUMENTS */
#if SCI_CFG_PARAM_CHECKING_ENABLE
    err = sci_mcu_param_check(chan);
    if (SCI_SUCCESS != err)
    {
        return err;
    }

    /* Check argument g_handles */
    if ((NULL == g_handles[chan]) || (FIT_NO_PTR == g_handles[chan]))
    {
        return SCI_ERR_OMITTED_CHAN;
    }
    if (SCI_MODE_OFF != g_handles[chan]->mode)
    {
        return SCI_ERR_CH_NOT_CLOSED;
    }
    if ((SCI_MODE_OFF == mode) || (SCI_MODE_MAX <= mode))
    {
        return SCI_ERR_BAD_MODE;
    }

    /* Check argument p_cfg, p_hdl */
    if (((NULL == p_cfg) || (NULL == p_hdl)) || ((FIT_NO_PTR == p_cfg) || (FIT_NO_PTR == p_hdl)))
    {
        return SCI_ERR_NULL_PTR;
    }
#endif
    
     /* APPLY POWER TO CHANNEL */
    power_on(g_handles[chan]);

    /* INITIALIZE REGISTER */
    sci_init_register(g_handles[chan]);

    /* INITIALIZE MODE SPECIFIC FEATURES */
    g_handles[chan]->mode = mode;
    if (SCI_MODE_ASYNC == mode)
    {
#if (SCI_CFG_ASYNC_INCLUDED)
        /* Casting sci_cfg_t type to sci_uart_t type is valid */
        err = sci_init_async(g_handles[chan], (sci_uart_t *)p_cfg, &priority);
#endif
    }
    else
    {
#if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
        /* Casting sci_cfg_t type to sci_sync_sspi_t type is valid */
        err = sci_init_sync(g_handles[chan], (sci_sync_sspi_t *)p_cfg, &priority);
#endif
    }

    if (SCI_SUCCESS != err)
    {
        g_handles[chan]->mode = SCI_MODE_OFF;
        return err;
    }
    g_handles[chan]->callback = p_callback;

    /* INITIALIZE TX AND RX QUEUES */
#if (SCI_CFG_ASYNC_INCLUDED)
    if (SCI_MODE_ASYNC == mode)
    {
        err = sci_init_queues(chan);
        if (SCI_SUCCESS != err)
        {
            g_handles[chan]->mode = SCI_MODE_OFF;
            return err;
        }
    }
#endif

#if SCI_CFG_FIFO_INCLUDED
    if (true == g_handles[chan]->fifo_ctrl)
    {
        /* INITIALIZE TX AND RX FIFO */
        err = sci_init_fifo(g_handles[chan]);
        if (SCI_SUCCESS != err)
        {
#if (SCI_CFG_ASYNC_INCLUDED)
            /* DE-INITIALIZE TX AND RX QUEUES */
            if (SCI_MODE_ASYNC == mode)
            {
                R_BYTEQ_Close(g_handles[chan]->u_tx_data.que);
                R_BYTEQ_Close(g_handles[chan]->u_rx_data.que);
            }
#endif
            g_handles[chan]->mode = SCI_MODE_OFF;
            return err;
        }
    }
#endif

    /* ENABLE INTERRUPTS */
    sci_initialize_ints(g_handles[chan], priority);

    /* FINISH */
    *p_hdl = g_handles[chan];

    return SCI_SUCCESS;
}  /* End of function R_SCI_Open() */

/*****************************************************************************
* Function Name: power_on
* Description  : This function provides power to the channel referenced by
*                the handle by taking it out of the module stop state.
* Arguments    : hdl -
*                    handle for channel (ptr to chan control block)
* Return Value : none
******************************************************************************/
static void power_on(sci_hdl_t const hdl)
{
#if ((R_BSP_VERSION_MAJOR == 5) && (R_BSP_VERSION_MINOR >= 30)) || (R_BSP_VERSION_MAJOR >= 6)
    bsp_int_ctrl_t int_ctrl;
#endif

    R_BSP_RegisterProtectDisable(BSP_REG_PROTECT_LPC_CGC_SWR);

#if ((R_BSP_VERSION_MAJOR == 5) && (R_BSP_VERSION_MINOR >= 30)) || (R_BSP_VERSION_MAJOR >= 6)
    R_BSP_InterruptControl(BSP_INT_SRC_EMPTY, BSP_INT_CMD_FIT_INTERRUPT_DISABLE, &int_ctrl);
#endif

    (*hdl->rom->mstp) &= (~hdl->rom->stop_mask);

#if ((R_BSP_VERSION_MAJOR == 5) && (R_BSP_VERSION_MINOR >= 30)) || (R_BSP_VERSION_MAJOR >= 6)
    R_BSP_InterruptControl(BSP_INT_SRC_EMPTY, BSP_INT_CMD_FIT_INTERRUPT_ENABLE, &int_ctrl);
#endif

    R_BSP_RegisterProtectEnable(BSP_REG_PROTECT_LPC_CGC_SWR);

    return;
}  /* End of function power_on() */

/*****************************************************************************
* Function Name: power_off
* Description  : This function removes power to the channel referenced by
*                handle by putting it into the module stop state.
* Arguments    : hdl -
*                    handle for channel (ptr to chan control block)
* Return Value : none
******************************************************************************/
static void power_off(sci_hdl_t const hdl)
{
#if ((R_BSP_VERSION_MAJOR == 5) && (R_BSP_VERSION_MINOR >= 30)) || (R_BSP_VERSION_MAJOR >= 6)
    bsp_int_ctrl_t int_ctrl;
#endif

    R_BSP_RegisterProtectDisable(BSP_REG_PROTECT_LPC_CGC_SWR);

#if ((R_BSP_VERSION_MAJOR == 5) && (R_BSP_VERSION_MINOR >= 30)) || (R_BSP_VERSION_MAJOR >= 6)
    R_BSP_InterruptControl(BSP_INT_SRC_EMPTY, BSP_INT_CMD_FIT_INTERRUPT_DISABLE, &int_ctrl);
#endif

    (*hdl->rom->mstp) |= (hdl->rom->stop_mask);

#if ((R_BSP_VERSION_MAJOR == 5) && (R_BSP_VERSION_MINOR >= 30)) || (R_BSP_VERSION_MAJOR >= 6)
    R_BSP_InterruptControl(BSP_INT_SRC_EMPTY, BSP_INT_CMD_FIT_INTERRUPT_ENABLE, &int_ctrl);
#endif

    R_BSP_RegisterProtectEnable(BSP_REG_PROTECT_LPC_CGC_SWR);

    return;
}  /* End of function power_off() */

#if (SCI_CFG_ASYNC_INCLUDED)
/*****************************************************************************
* Function Name: sci_init_queues
* Description  : This function attaches transmit and receive queues to the
*                channel.
*
* Arguments    : chan -
*                    channel (ptr to chan control block)
* Return Value : SCI_SUCCESS -
*                    channel initialized successfully
*                SCI_ERR_QUEUE_UNAVAILABLE -
*                    no queue control blocks available
******************************************************************************/
static sci_err_t sci_init_queues(uint8_t const chan)
{
    byteq_err_t q_err1 = BYTEQ_ERR_INVALID_ARG;
    byteq_err_t q_err2 = BYTEQ_ERR_INVALID_ARG;
    sci_err_t   err = SCI_SUCCESS;

    /* channel number verified as legal prior to calling this function */
    switch (chan)
    {
#if SCI_CFG_CH0_INCLUDED
        case (SCI_CH0):
        {
            q_err1 = R_BYTEQ_Open(ch0_tx_buf, SCI_CFG_CH0_TX_BUFSIZ, &g_handles[SCI_CH0]->u_tx_data.que);
            q_err2 = R_BYTEQ_Open(ch0_rx_buf, SCI_CFG_CH0_RX_BUFSIZ, &g_handles[SCI_CH0]->u_rx_data.que);
            break;
        }
#endif
#if SCI_CFG_CH1_INCLUDED
        case (SCI_CH1):
        {
            q_err1 = R_BYTEQ_Open(ch1_tx_buf, SCI_CFG_CH1_TX_BUFSIZ, &g_handles[SCI_CH1]->u_tx_data.que);
            q_err2 = R_BYTEQ_Open(ch1_rx_buf, SCI_CFG_CH1_RX_BUFSIZ, &g_handles[SCI_CH1]->u_rx_data.que);
            break;
        }
#endif
#if SCI_CFG_CH2_INCLUDED
        case (SCI_CH2):
        {
            q_err1 = R_BYTEQ_Open(ch2_tx_buf, SCI_CFG_CH2_TX_BUFSIZ, &g_handles[SCI_CH2]->u_tx_data.que);
            q_err2 = R_BYTEQ_Open(ch2_rx_buf, SCI_CFG_CH2_RX_BUFSIZ, &g_handles[SCI_CH2]->u_rx_data.que);
            break;
        }
#endif
#if SCI_CFG_CH3_INCLUDED
        case (SCI_CH3):
        {
            q_err1 = R_BYTEQ_Open(ch3_tx_buf, SCI_CFG_CH3_TX_BUFSIZ, &g_handles[SCI_CH3]->u_tx_data.que);
            q_err2 = R_BYTEQ_Open(ch3_rx_buf, SCI_CFG_CH3_RX_BUFSIZ, &g_handles[SCI_CH3]->u_rx_data.que);
            break;
        }
#endif
#if SCI_CFG_CH4_INCLUDED
        case (SCI_CH4):
        {
            q_err1 = R_BYTEQ_Open(ch4_tx_buf, SCI_CFG_CH4_TX_BUFSIZ, &g_handles[SCI_CH4]->u_tx_data.que);
            q_err2 = R_BYTEQ_Open(ch4_rx_buf, SCI_CFG_CH4_RX_BUFSIZ, &g_handles[SCI_CH4]->u_rx_data.que);
            break;
        }
#endif
#if SCI_CFG_CH5_INCLUDED
        case (SCI_CH5):
        {
            q_err1 = R_BYTEQ_Open(ch5_tx_buf, SCI_CFG_CH5_TX_BUFSIZ, &g_handles[SCI_CH5]->u_tx_data.que);
            q_err2 = R_BYTEQ_Open(ch5_rx_buf, SCI_CFG_CH5_RX_BUFSIZ, &g_handles[SCI_CH5]->u_rx_data.que);
            break;
        }
#endif
#if SCI_CFG_CH6_INCLUDED
        case (SCI_CH6):
        {
            q_err1 = R_BYTEQ_Open(ch6_tx_buf, SCI_CFG_CH6_TX_BUFSIZ, &g_handles[SCI_CH6]->u_tx_data.que);
            q_err2 = R_BYTEQ_Open(ch6_rx_buf, SCI_CFG_CH6_RX_BUFSIZ, &g_handles[SCI_CH6]->u_rx_data.que);
            break;
        }
#endif
#if SCI_CFG_CH7_INCLUDED
        case (SCI_CH7):
        {
            q_err1 = R_BYTEQ_Open(ch7_tx_buf, SCI_CFG_CH7_TX_BUFSIZ, &g_handles[SCI_CH7]->u_tx_data.que);
            q_err2 = R_BYTEQ_Open(ch7_rx_buf, SCI_CFG_CH7_RX_BUFSIZ, &g_handles[SCI_CH7]->u_rx_data.que);
            break;
        }
#endif
#if SCI_CFG_CH8_INCLUDED
        case (SCI_CH8):
        {
            q_err1 = R_BYTEQ_Open(ch8_tx_buf, SCI_CFG_CH8_TX_BUFSIZ, &g_handles[SCI_CH8]->u_tx_data.que);
            q_err2 = R_BYTEQ_Open(ch8_rx_buf, SCI_CFG_CH8_RX_BUFSIZ, &g_handles[SCI_CH8]->u_rx_data.que);
            break;
        }
#endif
#if SCI_CFG_CH9_INCLUDED
        case (SCI_CH9):
        {
            q_err1 = R_BYTEQ_Open(ch9_tx_buf, SCI_CFG_CH9_TX_BUFSIZ, &g_handles[SCI_CH9]->u_tx_data.que);
            q_err2 = R_BYTEQ_Open(ch9_rx_buf, SCI_CFG_CH9_RX_BUFSIZ, &g_handles[SCI_CH9]->u_rx_data.que);
            break;
        }
#endif
#if SCI_CFG_CH10_INCLUDED
        case (SCI_CH10):
        {
            q_err1 = R_BYTEQ_Open(ch10_tx_buf, SCI_CFG_CH10_TX_BUFSIZ, &g_handles[SCI_CH10]->u_tx_data.que);
            q_err2 = R_BYTEQ_Open(ch10_rx_buf, SCI_CFG_CH10_RX_BUFSIZ, &g_handles[SCI_CH10]->u_rx_data.que);
            break;
        }
#endif
#if SCI_CFG_CH11_INCLUDED
        case (SCI_CH11):
        {
            q_err1 = R_BYTEQ_Open(ch11_tx_buf, SCI_CFG_CH11_TX_BUFSIZ, &g_handles[SCI_CH11]->u_tx_data.que);
            q_err2 = R_BYTEQ_Open(ch11_rx_buf, SCI_CFG_CH11_RX_BUFSIZ, &g_handles[SCI_CH11]->u_rx_data.que);
            break;
        }
#endif
#if SCI_CFG_CH12_INCLUDED
        case (SCI_CH12):
        {
            q_err1 = R_BYTEQ_Open(ch12_tx_buf, SCI_CFG_CH12_TX_BUFSIZ, &g_handles[SCI_CH12]->u_tx_data.que);
            q_err2 = R_BYTEQ_Open(ch12_rx_buf, SCI_CFG_CH12_RX_BUFSIZ, &g_handles[SCI_CH12]->u_rx_data.que);
            break;
        }
#endif
        default:
        {
            err = SCI_ERR_QUEUE_UNAVAILABLE;
            break;
        }
    }

    if ((BYTEQ_SUCCESS != q_err1) || (BYTEQ_SUCCESS != q_err2))
    {
        err = SCI_ERR_QUEUE_UNAVAILABLE;
    }
    return err;
}  /* End of function sci_init_queues() */
#endif /* End of SCI_CFG_ASYNC_INCLUDED */

#if SCI_CFG_FIFO_INCLUDED
/*****************************************************************************
* Function Name: sci_init_fifo
* Description  : This function the setting of the FIFO mode, reset of the
*                TX/RX FIFO, and the threshold setting of the TX/RX FIFO.
* Arguments    : hdl -
*                    handle for channel (ptr to chan control block)
* Return Value : SCI_SUCCESS - 
*                    fifo initialized successfully
*                SCI_ERR_INVALID_ARG -
*                    element of hdl contains illegal value
******************************************************************************/
static sci_err_t sci_init_fifo(sci_hdl_t const hdl)
{
    /* CHECK ARGUMENTS */
#if SCI_CFG_PARAM_CHECKING_ENABLE
    if (hdl->tx_dflt_thresh > 15)
    {
        return SCI_ERR_INVALID_ARG;
    }
    if ((hdl->rx_dflt_thresh < 1) || (hdl->rx_dflt_thresh > 15))
    {
        return SCI_ERR_INVALID_ARG;
    }
#if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
    if (hdl->tx_dflt_thresh != hdl->rx_dflt_thresh)
    {
        return SCI_ERR_INVALID_ARG;
    }
#endif
#endif

    /* FIFO Mode Select (1:FIFO mode) */
    hdl->rom->regs->FCR.BIT.FM = 0x01;

    /* reset TX/RX FIFO */
    hdl->rom->regs->FCR.BIT.TFRST = 0x01;
    hdl->rom->regs->FCR.BIT.RFRST = 0x01;

    /* set TX/RX FIFO threshold initial value */
    hdl->rom->regs->FCR.BIT.TTRG = hdl->tx_dflt_thresh;
    hdl->rom->regs->FCR.BIT.RTRG = hdl->rx_dflt_thresh;

    return SCI_SUCCESS;
}  /* End of function sci_init_fifo() */
#endif /* End of SCI_CFG_FIFO_INCLUDED */

#if (SCI_CFG_ASYNC_INCLUDED)
/*****************************************************************************
* Function Name: sci_init_async
* Description  : This function initializes the control block and UART 
*                registers for an SCI channel.
*
* NOTE: p_cfg is checked to be non-NULL prior to this function.
*       The TE and RE bits in SCR must be 0 prior to calling this function.
*
* Arguments    : hdl - 
*                    handle for channel (ptr to chan control block)
*                p_cfg -
*                    ptr to Uart configuration argument structure
*                p_priority -
*                    pointer to location to load interrupt priority into
* Return Value : SCI_SUCCESS - 
*                    channel initialized successfully
*                SCI_ERR_INVALID_ARG -
*                    element of p_cfg contains illegal value
******************************************************************************/
static sci_err_t sci_init_async(sci_hdl_t const      hdl,
                                sci_uart_t * const   p_cfg,
                                uint8_t * const      p_priority)
{
    sci_err_t   err=SCI_SUCCESS;
    int32_t     bit_err;

    /* Check arguments */    

#if SCI_CFG_PARAM_CHECKING_ENABLE
    if (((SCI_DATA_8BIT != p_cfg->data_size) && (SCI_DATA_7BIT != p_cfg->data_size))
     || ((SCI_STOPBITS_1 != p_cfg->stop_bits) && (SCI_STOPBITS_2 != p_cfg->stop_bits))
     || ((p_cfg->int_priority < (BSP_MCU_IPL_MIN+1)) || (p_cfg->int_priority > BSP_MCU_IPL_MAX)))
    {
        return SCI_ERR_INVALID_ARG;
    }

    if (SCI_PARITY_ON == p_cfg->parity_en)
    {
        if ((SCI_EVEN_PARITY != p_cfg->parity_type) && (SCI_ODD_PARITY != p_cfg->parity_type))
        {
            return SCI_ERR_INVALID_ARG;
        }
    }
    else if (SCI_PARITY_OFF != p_cfg->parity_en)
    {
        return SCI_ERR_INVALID_ARG;
    }
    else
    {
        /* Do Nothing */
    }
    if (SCI_CLK_INT == p_cfg->clk_src)
    {
        if (0 == p_cfg->baud_rate)
        {
            return SCI_ERR_INVALID_ARG;
        }
    }
    else if ((SCI_CLK_EXT8X != p_cfg->clk_src) && (SCI_CLK_EXT16X != p_cfg->clk_src))
    {
        return SCI_ERR_INVALID_ARG;
    }
    else
    {
        /* Do Nothing */
    }
#endif /* End of SCI_CFG_PARAM_CHECKING_ENABLE */


    /* Initialize channel control block flags */
    hdl->tx_idle = true;

        
    /* Configure SMR for asynchronous mode, single processor, and user settings */
    if (SCI_PARITY_OFF == p_cfg->parity_en)
    {
        p_cfg->parity_type = 0;         // ensure random value is not ORed into SMR
    }

    /* Configure SMR */
    hdl->rom->regs->SMR.BYTE = (uint8_t)((p_cfg->data_size | p_cfg->stop_bits) | (p_cfg->parity_en | p_cfg->parity_type));

    /* SETUP CLOCK FOR BAUD RATE */

    if (SCI_CLK_INT == p_cfg->clk_src)
    {
        /* Use internal clock for baud rate */
        bit_err = sci_init_bit_rate(hdl, hdl->pclk_speed, p_cfg->baud_rate);
        if (1000 == bit_err)
        {
            err = SCI_ERR_INVALID_ARG;          // impossible baud rate; 100% error
        }
        else
        {
            hdl->baud_rate = p_cfg->baud_rate;   // save baud rate for break generation
        }
    }
    else
    {
        /* Use external clock for baud rate */
        hdl->rom->regs->SCR.BIT.CKE = 0x02;
        hdl->rom->regs->SEMR.BIT.ABCS = (SCI_CLK_EXT8X == p_cfg->clk_src) ? 1 : 0;
    }

    *p_priority = p_cfg->int_priority;
    return err;
}  /* End of function sci_init_async() */
#endif /* End of SCI_CFG_ASYNC_INCLUDED */

#if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
/*****************************************************************************
* Function Name: sci_init_sync
* Description  : This function initializes the control block and SYNC/SSPI
*                registers for an SCI channel.
*
* NOTE: p_cfg is checked to be non-NULL prior to this function.
*       The TE and RE bits in SCR must be 0 prior to calling this function.
*
* Arguments    : hdl -
*                    handle for channel (ptr to chan control block)
*                p_cfg -
*                    ptr to SSPI configuration argument structure
*                p_priority -
*                    pointer to location to load interrupt priority into
* Return Value : SCI_SUCCESS -
*                    channel initialized successfully
*                SCI_ERR_INVALID_ARG -
*                    element of p_cfg contains illegal value
******************************************************************************/
static sci_err_t sci_init_sync(sci_hdl_t const         hdl,
                               sci_sync_sspi_t * const p_cfg,
                               uint8_t * const         p_priority)
{
    sci_err_t   err = SCI_SUCCESS;
    int32_t     bit_err;


    /* Check arguments */

#if SCI_CFG_PARAM_CHECKING_ENABLE
    if ((SCI_MODE_SSPI == hdl->mode)
     && (SCI_SPI_MODE_0 != p_cfg->spi_mode) && (SCI_SPI_MODE_1 != p_cfg->spi_mode)
     && (SCI_SPI_MODE_2 != p_cfg->spi_mode) && (SCI_SPI_MODE_3 != p_cfg->spi_mode))
    {
        return SCI_ERR_INVALID_ARG;
    }
    else if ((SCI_MODE_SYNC == hdl->mode) && (SCI_SPI_MODE_OFF != p_cfg->spi_mode))
    {
        return SCI_ERR_INVALID_ARG;
    }
    else
    {
        /* Do Nothing */
    }

    if (0 == p_cfg->bit_rate)
    {
        return SCI_ERR_INVALID_ARG;
    }

    if ((0 == p_cfg->int_priority) || (p_cfg->int_priority > BSP_MCU_IPL_MAX))
    {
        return SCI_ERR_INVALID_ARG;
    }
#endif

    /* Initialize channel control block flags */
    hdl->tx_idle = true;
    hdl->tx_dummy = false;

    /* Configure SMR for SSPI/SYNC mode */
    hdl->rom->regs->SMR.BYTE = 0x80;
    hdl->rom->regs->SCMR.BIT.SMIF = 0;          /* default */
    hdl->rom->regs->SIMR1.BIT.IICM = 0;         /* default */

    /* Configure SPI register for clock polarity/phase and single master */
    if (SCI_MODE_SSPI == hdl->mode)
    {
        hdl->rom->regs->SPMR.BYTE = p_cfg->spi_mode;
    }
    else    /* synchronous operation */
    {
        hdl->rom->regs->SPMR.BYTE = 0;
    }

    /* Configure data inversion */
    hdl->rom->regs->SCMR.BIT.SINV = (uint8_t)((true == p_cfg->invert_data) ? 1 : 0);

    /* Configure bit order */
    hdl->rom->regs->SCMR.BIT.SDIR = (uint8_t)((true == p_cfg->msb_first) ? 1 : 0);


    /* SETUP CLOCK FOR BIT RATE */

    /* Use internal clock for bit rate (master) */
    bit_err = sci_init_bit_rate(hdl, hdl->pclk_speed, p_cfg->bit_rate);
    if (1000 == bit_err)
    {
        err = SCI_ERR_INVALID_ARG;      /* impossible bit rate; 100% error */
    }

    *p_priority = p_cfg->int_priority;
    return err;
} /* End of function sci_init_sync() */
#endif /* End of SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED */

/***********************************************************************************************************************
* Function Name: R_SCI_Send
********************************************************************************************************************//**
* @brief  Initiates transmit if transmitter is not in use. Queues data for later transmit when in Asynchronous mode.
*
* @param[in]    hdl  Handle for channel. Set hdl when R_SCI_Open() is successfully processed.
*
* @param[in]    p_src  Pointer to data to transmit
*
* @param[in]    length  Number of bytes to send
*
* @retval   SCI_SUCCESS  Transmit initiated or loaded into queue (Asynchronous)
*
* @retval   SCI_ERR_NULL_PTR  hdl value is NULL
*
* @retval   SCI_ERR_BAD_MODE  Mode specified not currently supported
*
* @retval   SCI_ERR_INSUFFICIENT_SPACE  Insufficient space in queue to load all data (Asynchronous)
*
* @retval   SCI_ERR_XCVR_BUSY  Channel currently busy (SSPI/Synchronous)
*
*
* @details  In asynchronous mode, this function places data into a transmit queue if the transmitter for the SCI channel
* referenced by the handle is not in use. In SSPI and Synchronous modes, no data is queued and transmission begins immediately
* if the transceiver is not already in use. All transmissions are handled at the interrupt level.\n
* Note that the toggling of Slave Select lines when in SSPI mode is not handled by this driver. The Slave Select line
* for the target device must be enabled prior to calling this function.
* Also, toggling of the CTS/RTS pin in Synchronous/Asynchronous mode is not handled by this driver.
* @note None
*/
sci_err_t R_SCI_Send(sci_hdl_t const    hdl,
                     uint8_t            *p_src,
                     uint16_t const     length)
{
    sci_err_t   err=SCI_SUCCESS;

    /* Check arguments */

#if SCI_CFG_PARAM_CHECKING_ENABLE
    /* Check argument hdl, p_src */
    if (((NULL == hdl)   || (FIT_NO_PTR == hdl)) || ((NULL == p_src) || (FIT_NO_PTR == p_src)))
    {
        return SCI_ERR_NULL_PTR;
    }
    if ((SCI_MODE_OFF == hdl->mode) || (SCI_MODE_MAX <= hdl->mode))
    {
        return SCI_ERR_BAD_MODE;
    }
    if (0 == length)
    {
        return SCI_ERR_INVALID_ARG;
    }
#endif

    if (SCI_MODE_ASYNC == hdl->mode)
    {
#if (SCI_CFG_ASYNC_INCLUDED)
        err = sci_send_async_data(hdl, p_src, length);
#endif
    }
    else
    {
        /* SSPI or SYNC */
#if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
        err = sci_send_sync_data(hdl, p_src, NULL, length, false);
#endif
    }

    return err;
} /* End of function R_SCI_Send() */


#if (SCI_CFG_ASYNC_INCLUDED)
/*****************************************************************************
* Function Name: sci_send_async_data
* Description  : This function determines if the tx byte queue of the channel
*                referenced by the handle is not full, and call the byte
*                transmission function.
* Arguments    : hdl -
*                    handle for channel (ptr to chan control block)
*                p_src -
*                    ptr to data to transmit
*                length -
*                    number of bytes to send and possibly receive
* Return Value : SCI_SUCCESS -
*                    data transfer started
*                SCI_ERR_XCVR_BUSY -
*                    channel currently busy
*                SCI_ERR_INSUFFICIENT_SPACE - 
*                    not enough space in tx queue to store data (Async)
******************************************************************************/
static sci_err_t sci_send_async_data(sci_hdl_t const hdl,
                                     uint8_t         *p_src,
                                     uint16_t const  length)
{
    sci_err_t   err = SCI_SUCCESS;
    uint16_t    cnt;
    byteq_err_t byteq_err = BYTEQ_ERR_QUEUE_FULL;

    if (true != hdl->tx_idle  )
    {
        return SCI_ERR_XCVR_BUSY;
    }

#if SCI_CFG_FIFO_INCLUDED
    if (true == hdl->fifo_ctrl)
    {
        /* TX FIFO use check */
        if (0x00 < hdl->rom->regs->FDR.BIT.T)
        {
            return SCI_ERR_XCVR_BUSY;
        }

        /* reset TX FIFO */
        hdl->rom->regs->FCR.BIT.TFRST = 0x01;
    }
#endif

    /* Determine amount of space left in tx queue */
    R_BYTEQ_Unused(hdl->u_tx_data.que, &cnt);

    if (cnt < length)
    {
        /* If can't fit, return */
        return SCI_ERR_INSUFFICIENT_SPACE;
    }

    /* Else load bytes into tx queue for transmission */
    /* WAIT_LOOP */
    for (cnt = 0; cnt < length; cnt++)
    {
        byteq_err = sci_put_byte(hdl, *p_src++);
        if (BYTEQ_SUCCESS != byteq_err)
        {
            /* If the return value is not BYTEQ_SUCCESS. */
            err = SCI_ERR_INSUFFICIENT_SPACE;
            break;
        }
    }

    if (SCI_SUCCESS == err)
    {
        hdl->tx_idle = false;
        ENABLE_TXI_INT;
    }

    return err;
} /* End of function sci_send_async_data() */

/*****************************************************************************
* Function Name: sci_put_byte
* Description  : Transmits byte if channel is not busy. Otherwise, byte is
*                stored in tx queue until can transmit. If buffer is full
*                and cannot store it, an error code is returned.
* Arguments    : hdl -
*                    handle for channel (ptr to chan control block)
*                byte -
*                    byte to transmit
* Return Value : SCI_SUCCESS -
*                    data transfer started
*                SCI_ERR_INSUFFICIENT_SPACE - 
*                    not enough space in tx queue to store data (Async)
******************************************************************************/
static byteq_err_t sci_put_byte(sci_hdl_t const   hdl,
                                uint8_t const     byte)
{
    byteq_err_t err = BYTEQ_ERR_QUEUE_FULL;

    /* else load next byte into tx queue (space checked in calling func) */
    err = R_BYTEQ_Put(hdl->u_tx_data.que, byte);

    return err;
} /* End of function sci_put_byte() */
#endif /* SCI_CFG_ASYNC_INCLUDED */


#if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
/*****************************************************************************
* Function Name: sci_send_sync_data
* Description  : This function determines if the channel referenced by the
*                handle is not busy, and begins the data transfer process
*                (both sending and receiving data).
*
* Arguments    : hdl -
*                    handle for channel (ptr to chan control block)
*                p_src -
*                    ptr to data to transmit
*                p_dst -
*                    ptr to buffer to store receive data (optional)
*                length -
*                    number of bytes to send and possibly receive
*                save_rx_data -
*                    true if data clocked in should be saved to p_dst.
* Return Value : SCI_SUCCESS -
*                    data transfer started
*                SCI_ERR_XCVR_BUSY -
*                    channel currently busy
******************************************************************************/
static sci_err_t sci_send_sync_data(sci_hdl_t const hdl,
                                    uint8_t         *p_src,
                                    uint8_t         *p_dst,
                                    uint16_t const  length,
                                    bool            save_rx_data)
{
#if SCI_CFG_FIFO_INCLUDED
    uint8_t cnt;
    uint8_t thresh_cnt;
#endif

    if (true == hdl->tx_idle)
    {
        if (true == save_rx_data)
        {
            hdl->u_rx_data.buf = p_dst;
        }
        hdl->save_rx_data  = save_rx_data;

        hdl->u_tx_data.buf = p_src;
        hdl->tx_cnt        = length;
        hdl->rx_cnt        = length;
        hdl->tx_idle       = false;
        hdl->tx_dummy      = false;

#if SCI_CFG_FIFO_INCLUDED
        if (true == hdl->fifo_ctrl)
        {
            /* reset TX FIFO */
            hdl->rom->regs->FCR.BIT.TFRST = 0x01;

            /* reset RX FIFO */
            hdl->rom->regs->FCR.BIT.RFRST = 0x01;

            /* If length is lower than SCI_CFG_CHXX_RX_FIFO_THRESH, FCR.BIT.RTRG register is set to length */
            if (length < hdl->rx_curr_thresh)
            {
                hdl->rom->regs->FCR.BIT.RTRG = length;
            }

            thresh_cnt = hdl->rom->regs->FCR.BIT.RTRG;
            
            hdl->tx_cnt -= thresh_cnt;

            /* Repeated FIFO RX threshold count */
            /* WAIT_LOOP */
            for (cnt = 0; cnt < thresh_cnt; cnt++)
            {
                if(0 != cnt)
                {
                    hdl->u_tx_data.buf++;
                }
                SCI_TDR(*hdl->u_tx_data.buf);    /* start transmit */
            }
        }
        else
#endif
        {
            hdl->tx_cnt--;
            SCI_TDR(*hdl->u_tx_data.buf);    /* start transmit */
        }

        return SCI_SUCCESS;
    }

    return SCI_ERR_XCVR_BUSY;
} /* End of function sci_send_sync_data() */
#endif /* SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED */


#if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
/***********************************************************************************************************************
* Function Name: R_SCI_SendReceive
********************************************************************************************************************//**
* @brief  For Synchronous and SSPI modes only. Transmits and receives data simultaneously if the transceiver is not
* in use.
*
* @param[in]    hdl  Handle for channel. Set hdl when R_SCI_Open() is successfully processed.
* @param[in]    p_src  Pointer to data to transmit
*
* @param[in]    p_dst  Pointer to buffer to load data into
*
* @param[in]    length  Number of bytes to send
*
* @retval   SCI_SUCCESS  Data transfer initiated
*
* @retval   SCI_ERR_NULL_PTR  hdl value is NULL
*
* @retval   SCI_ERR_BAD_MODE  Channel mode not SSPI or Synchronous
*
* @retval   SCI_ERR_XCVR_BUSY  Channel currently busy
* @details   If the transceiver is not in use, this function clocks out data from the p_src buffer while simultaneously
* clocking in data and placing it in the p_dst buffer.
* Note that the toggling of Slave Select lines for SSPI is not handled by this driver. The Slave Select line for
* the target device must be enabled prior to calling this function.
* Also, toggling of the CTS/RTS pin in Synchronous/Asynchronous mode is not handled by this driver.
*
* @note See section 2.11 Callback Function in application note for values passed to arguments of the callback function.
*/
sci_err_t R_SCI_SendReceive(sci_hdl_t const hdl,
                            uint8_t         *p_src,
                            uint8_t         *p_dst,
                            uint16_t const  length)
{
    sci_err_t   err;

#if SCI_CFG_PARAM_CHECKING_ENABLE
    /* Check arguments */
    if ((((NULL == hdl)   || (FIT_NO_PTR == hdl))    /* Check if hdl is available or not   */
     ||  ((NULL == p_src) || (FIT_NO_PTR == p_src))) /* Check if p_src is available or not */
     ||  ((NULL == p_dst) || (FIT_NO_PTR == p_dst))) /* Check if p_dst is available or not */
    {
        return SCI_ERR_NULL_PTR;
    }

    if ((SCI_MODE_SSPI != hdl->mode) && (SCI_MODE_SYNC != hdl->mode))
    {
        return SCI_ERR_BAD_MODE;
    }

    if (0 == length)
    {
        return SCI_ERR_INVALID_ARG;
    }
#endif

    err = sci_send_sync_data(hdl, p_src, p_dst, length, true);

    return err;
} /* End of function R_SCI_SendReceive() */
#endif /* End of SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED */

#if (SCI_CFG_ASYNC_INCLUDED)
/*****************************************************************************
* Function Name: sci_transfer
* Description  : Transfer for SCI
* Arguments    : hdl - 
*                    handle for channel (ptr to chan control block)
* Return Value : none
******************************************************************************/
static void sci_transfer(sci_hdl_t const hdl)
{
    uint16_t    num;
    uint8_t     byte;

    /* Get bytes from tx queue */
    (void)R_BYTEQ_Get(hdl->u_tx_data.que, (uint8_t *)&byte);

    /* TDR/FTDR register write access */
    SCI_TDR(byte);

    /* Get data byte number from que and if the number of data bytes is 0, to disable the transfer */
    R_BYTEQ_Used(hdl->u_tx_data.que, &num);
    if (0 >= num)
    {
        /* Disable transmit interrupt */
        DISABLE_TXI_INT;
#if SCI_CFG_TEI_INCLUDED
        /* Enable transmit end interrupt */
        hdl->rom->regs->SCR.BIT.TEIE = 1;
        ENABLE_TEI_INT;
#endif
        hdl->tx_idle = true;    // set flag if queue empty
    }
} /* End of function sci_transfer() */

#if SCI_CFG_FIFO_INCLUDED
/*****************************************************************************
* Function Name: sci_fifo_transfer
* Description  : FIFO Transfer for SCI
* Arguments    : hdl - 
*                    handle for channel (ptr to chan control block)
* Return Value : none
******************************************************************************/
static void sci_fifo_transfer(sci_hdl_t const hdl)
{
    uint8_t cnt;
    uint8_t fifo_num;

    /* Repeated empty FIFO buffer count */
    fifo_num = SCI_FIFO_FRAME_SIZE - hdl->rom->regs->FDR.BIT.T;

    /* WAIT_LOOP */
    for (cnt = 0; cnt < fifo_num; cnt++)
    {
        /* SCI Transfer */
        sci_transfer(hdl);

        /* If the queue is empty(true == hdl->tx_idle), exit from FIFO transfer loop */
        if (true == hdl->tx_idle)
        {
            break;
        }
    }

    /* When the settings of transmit data are completed, set the SSRFIFO.TDFE flag to 0. */
    if (1 == hdl->rom->regs->SSRFIFO.BIT.TDFE)
    {
        /* Casting register 8 bits to unsigned char type is valid */
        hdl->rom->regs->SSRFIFO.BYTE = (unsigned char)~SCI_SSRFIFO_TDFE_MASK;
    }
} /* End of function sci_fifo_transfer() */
#endif /*End of SCI_CFG_FIFO_INCLUDED */

/*****************************************************************************
* Function Name: txi_handler
* Description  : TXI interrupt handler for SCI
* Arguments    : hdl - 
*                    handle for channel (ptr to chan control block)
* Return Value : none
******************************************************************************/
void txi_handler(sci_hdl_t const hdl)
{
#if SCI_CFG_FIFO_INCLUDED
    if (true == hdl->fifo_ctrl)
    {
        /* SCI FIFO Transfer */
        sci_fifo_transfer(hdl);
    }
    else
#endif
    {
        /* SCI Transfer */
        sci_transfer(hdl);
    }
} /* End of function txi_handler() */
#endif /* SCI_CFG_ASYNC_INCLUDED */


#if SCI_CFG_TEI_INCLUDED
/*****************************************************************************
* Function Name: tei_handler
* Description  : TEI interrupt handler for SCI
* Arguments    : hdl - 
*                    handle for channel (ptr to chan control block)
* Return Value : none
******************************************************************************/
void tei_handler(sci_hdl_t const hdl)
{
    sci_cb_args_t   args;

    /* Disable transmit end interrupt */
    DISABLE_TEI_INT;
    hdl->rom->regs->SCR.BIT.TEIE = 0;

    /* Activate callback function if available */
    if ((NULL != hdl->callback) && (FIT_NO_FUNC != hdl->callback))
    {
        args.hdl = hdl;
        args.event = SCI_EVT_TEI;

        /* Activate callback function */
        hdl->callback((void *)&args);
    }
} /* End of function tei_handler() */
#endif


/***********************************************************************************************************************
* Function Name: R_SCI_Receive
********************************************************************************************************************//**
* @brief In Asynchronous mode, fetches data from a queue which is filled by RXI interrupts. In other modes, initiates
* reception if transceiver is not in use.
* @param[in]    hdl Handle for channel. Set hdl when R_SCI_Open() is successfully processed.
*
* @param[in]    p_dst  Pointer to buffer to load data into
*
* @param[in]    length  Number of bytes to read
*
* @retval SCI_SUCCESS  Requested number of bytes were loaded into p_dst (Asynchronous) Clocking in of data initiated
* (SSPI/Synchronous)
*
* @retval SCI_ERR_NULL_PTR  hdl value is NULL
*
* @retval SCI_ERR_BAD_MODE  Mode specified not currently supported
*
* @retval SCI_ERR_INSUFFICIENT_DATA  Insufficient data in receive queue to fetch all data (Asynchronous)
*
* @retval SCI_ERR_XCVR_BUSY  Channel currently busy (SSPI/Synchronous)
*
* @details In Asynchronous mode, this function gets data received on an SCI channel referenced by the handle from its
* receive queue. This function will not block if the requested number of bytes is not available. In
* SSPI/Synchronous modes, the clocking in of data begins immediately if the transceiver is not already in use.
* The value assigned to SCI_CFG_DUMMY_TX_BYTE in r_sci_config.h is clocked out while the receive data is being clocked in.\n
* If any errors occurred during reception, the callback function specified in R_SCI_Open() is executed. Check
* an event passed with the argument of the callback function to see if the reception has been successfully
* completed. See Section 2.11 Callback Function in application note for details.\n
* Note that the toggling of Slave Select lines when in SSPI mode is not handled by this driver. The Slave
* Select line for the target device must be enabled prior to calling this function.
* @note See section 2.11 Callback Function in application note for values passed to arguments of the callback function.
* In Asynchronous mode, when data match detected, received data stored in a queue and notify to user by callback function
* with event SCI_EVT_RX_CHAR_MATCH.
*/
sci_err_t R_SCI_Receive(sci_hdl_t const hdl,
                        uint8_t         *p_dst,
                        uint16_t const  length)
{
sci_err_t   err = SCI_SUCCESS;


    /* Check arguments */

#if SCI_CFG_PARAM_CHECKING_ENABLE
    /* Check argument hdl, p_dst */
    if (((NULL == hdl)   || (FIT_NO_PTR == hdl))|| ((NULL == p_dst) || (FIT_NO_PTR == p_dst)))
    {
        return SCI_ERR_NULL_PTR;
    }
    if ((SCI_MODE_OFF == hdl->mode) || (SCI_MODE_MAX <= hdl->mode))
    {
        return SCI_ERR_BAD_MODE;
    }
    if (0 == length)
    {
        return SCI_ERR_INVALID_ARG;
    }
#endif

    if (SCI_MODE_ASYNC == hdl->mode)
    {
#if (SCI_CFG_ASYNC_INCLUDED)
        err = sci_receive_async_data(hdl, p_dst, length);
#endif
    }

    else
    {
        /* mode is SSPI/SYNC */
#if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
        err = sci_receive_sync_data(hdl, p_dst, length);
#endif
    }

    return err;
} /* End of function R_SCI_Receive() */

#if (SCI_CFG_ASYNC_INCLUDED)
/*****************************************************************************
* Function Name: sci_receive_async_data
* Description  : This function determines if the rx byte queue of the channel 
*                referenced by the handle, the requested number of bytes 
*                is available, and get the data from the rx byte queue.
* Arguments    : hdl -
*                    handle for channel (ptr to chan control block)
*                p_dst -
*                    ptr to buffer to load data into
*                length - 
*                    number of bytes to read
* Return Value : SCI_SUCCESS -
*                    requested number of byte loaded into p_dst
*                SCI_ERR_INSUFFICIENT_DATA -
*                    rx queue does not contain requested amount of data
******************************************************************************/
static sci_err_t sci_receive_async_data(sci_hdl_t const hdl,
                                        uint8_t         *p_dst,
                                        uint16_t const  length)
{
    sci_err_t   err = SCI_SUCCESS;
    uint16_t    cnt;
    byteq_err_t byteq_err = BYTEQ_SUCCESS;

    /* CHECK FOR SUFFICIENT DATA IN QUEUE, AND FETCH IF AVAILABLE */
    R_BYTEQ_Used(hdl->u_rx_data.que, &cnt);

    if (cnt < length)
    {
        return SCI_ERR_INSUFFICIENT_DATA;
    }

    /* Get bytes from rx queue */
    /* WAIT_LOOP */
    for (cnt = 0; cnt < length; cnt++)
    {
        /* Disable RXI Interrupt */
        DISABLE_RXI_INT;
        byteq_err = R_BYTEQ_Get(hdl->u_rx_data.que, p_dst++);
        ENABLE_RXI_INT;
        if (BYTEQ_SUCCESS != byteq_err)
        {
            err = SCI_ERR_INSUFFICIENT_DATA;
            break;
        }
    }

    return err;
} /* End of function sci_receive_async_data() */
#endif /* SCI_CFG_ASYNC_INCLUDED */

#if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
/*****************************************************************************
* Function Name: sci_receive_sync_data
* Description  : This function determines if the channel referenced by the
*                handle is not busy, and dummy data send.
* Arguments    : hdl -
*                    handle for channel (ptr to chan control block)
*                p_dst -
*                    ptr to buffer to load data into
*                length - 
*                    number of bytes to read
* Return Value : SCI_SUCCESS -
*                    requested number of byte loaded into p_dst
*                SCI_ERR_XCVR_BUSY -
*                    channel currently busy
******************************************************************************/
static sci_err_t sci_receive_sync_data(sci_hdl_t const hdl,
                                       uint8_t         *p_dst,
                                       uint16_t const  length)
{
#if SCI_CFG_FIFO_INCLUDED
    uint8_t cnt;
    uint8_t thresh_cnt;
#endif

    /* IF TRANCEIVER NOT IN USE, START DUMMY TRANSMIT TO CLOCK IN DATA */
    if (true == hdl->tx_idle)
    {
        hdl->u_rx_data.buf = p_dst;
        hdl->save_rx_data  = true;               /* save the data clocked in */
        hdl->tx_idle       = false;
        hdl->tx_cnt        = length;
        hdl->rx_cnt        = length;
        hdl->tx_dummy      = true;

#if SCI_CFG_FIFO_INCLUDED
        if (true == hdl->fifo_ctrl)
        {
            /* reset TX FIFO */
            hdl->rom->regs->FCR.BIT.TFRST = 0x01;

            /* reset RX FIFO */
            hdl->rom->regs->FCR.BIT.RFRST = 0x01;

            if (length > SCI_FIFO_FRAME_SIZE)
            {
                thresh_cnt = SCI_FIFO_FRAME_SIZE;
            }
            else
            {
                /* If length is lower than SCI_CFG_CHXX_RX_FIFO_THRESH, FCR.BIT.RTRG register is set to length */
                if (length < hdl->rx_curr_thresh)
                {
                    hdl->rom->regs->FCR.BIT.RTRG = length;
                }
                thresh_cnt = length;
            }

            hdl->tx_cnt -= thresh_cnt;

            /* WAIT_LOOP */
            for (cnt = 0; cnt < thresh_cnt; cnt++)
            {
                SCI_TDR(SCI_CFG_DUMMY_TX_BYTE);    /* start transmit */
            }
        }
        else
#endif /* End of SCI_CFG_FIFO_INCLUDED */
        {
            hdl->tx_cnt--;
            SCI_TDR(SCI_CFG_DUMMY_TX_BYTE);    /* start transfer */
        }

        return SCI_SUCCESS;
    }

    return SCI_ERR_XCVR_BUSY;
} /* End of function sci_receive_sync_data() */
#endif /* End of SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED */

/*****************************************************************************
* Function Name: sci_receive
* Description  : Receive for SCI
* Arguments    : hdl - 
*                    handle for channel (ptr to chan control block)
* Return Value : none
******************************************************************************/
static void sci_receive(sci_hdl_t const hdl)
{
    sci_cb_args_t   args;
    uint8_t         byte;

    /* Read byte */
    SCI_RDR(byte);
    if (SCI_MODE_ASYNC == hdl->mode)
    {
#if (SCI_CFG_ASYNC_INCLUDED)

        /* Place byte in queue */
        if (R_BYTEQ_Put(hdl->u_rx_data.que, byte) == BYTEQ_SUCCESS)
        {
            args.event = SCI_EVT_RX_CHAR;
        }
        else
        {
            args.event = SCI_EVT_RXBUF_OVFL;
        }

        /* Do callback if available */
        if ((NULL != hdl->callback) && (FIT_NO_FUNC != hdl->callback))
        {
            args.hdl = hdl;
            args.byte = byte;

           /* Casting to void type is valid */
            hdl->callback((void *)&args);
        }
#endif
    }
    else
    {
#if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
        hdl->rx_cnt--;

        /* Place byte in buffer if Receive() or SendReceive() */
        if (true == hdl->save_rx_data)
        {
            *hdl->u_rx_data.buf++ = byte;
        }

        /* See if more bytes to transfer */
        if (0 < hdl->rx_cnt)
        {
            if (0 < hdl->tx_cnt)
            {
                /* send another byte */
                if (true == hdl->tx_dummy)
                {
                    hdl->tx_cnt--;
                    SCI_TDR(SCI_CFG_DUMMY_TX_BYTE);
                }
                else
                {
                    hdl->tx_cnt--;
                    hdl->u_tx_data.buf++;
                    SCI_TDR(*hdl->u_tx_data.buf);
                }
            }
        }
        else
        {
            hdl->tx_idle = true;

            /* Do callback if available */
            if ((NULL != hdl->callback) && (FIT_NO_FUNC != hdl->callback))
            {
                args.hdl = hdl;
                args.event = SCI_EVT_XFER_DONE;

                /* Casting to void type is valid */
                hdl->callback((void *)&args);
            }
        }
#endif /* End of SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED */
    }
} /* End of function sci_receive() */

#if SCI_CFG_FIFO_INCLUDED
#if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
/*****************************************************************************
* Function Name: sci_fifo_receive_sync
* Description  : FIFO Receive for SCI mode is SYNC and SSPI
* Arguments    : hdl - 
*                    handle for channel (ptr to chan control block)
* Return Value : none
******************************************************************************/
static void sci_fifo_receive_sync(sci_hdl_t const hdl)
{
    uint8_t       cnt;
    uint8_t       fifo_num_rx;
    uint8_t       fifo_num_tx;
    sci_cb_args_t args;
    uint8_t       byte_rx[SCI_FIFO_FRAME_SIZE];

    fifo_num_rx = hdl->rom->regs->FDR.BIT.R;

    /* WAIT_LOOP */
    for (cnt = 0; cnt < fifo_num_rx; cnt++)
    {
        SCI_RDR(byte_rx[cnt]);
    }

    hdl->rx_cnt -= fifo_num_rx;

    /* Place byte in buffer if Receive() or SendReceive() */
    if (true == hdl->save_rx_data)
    {
        /* WAIT_LOOP */
        for (cnt = 0; cnt < fifo_num_rx; cnt++)
        {
            /* SCI Receive */
            *hdl->u_rx_data.buf++ = byte_rx[cnt];
        }
    }

    /* See if more bytes to transfer */
    if (0 < hdl->rx_cnt)
    {
        if (hdl->rom->regs->FCR.BIT.RTRG > hdl->rx_cnt)
        {
            hdl->rom->regs->FCR.BIT.RTRG = hdl->rx_cnt;
        }
        
        if (0 < hdl->tx_cnt)
        {
            if (hdl->tx_cnt > fifo_num_rx)
            {
                fifo_num_tx  = fifo_num_rx;
                hdl->tx_cnt -= fifo_num_rx;
            }
            else
            {
                fifo_num_tx  = hdl->tx_cnt;
                hdl->tx_cnt  = 0;
            }

            /* send another byte */
            if (true == hdl->tx_dummy)
            {
                /* WAIT_LOOP */
                for (cnt = 0; cnt < fifo_num_tx; cnt++)
                {
                    SCI_TDR(SCI_CFG_DUMMY_TX_BYTE);
                }
            }
            else
            {
                /* WAIT_LOOP */
                for (cnt = 0; cnt < fifo_num_tx; cnt++)
                {
                    hdl->u_tx_data.buf++;
                    SCI_TDR(*hdl->u_tx_data.buf);
                }
            }
        }
    }
    else
    {
        hdl->rom->regs->FCR.BIT.RTRG = hdl->rx_curr_thresh;
        hdl->tx_idle = true;

        /* Do callback if available */
        if ((NULL != hdl->callback) && (FIT_NO_FUNC != hdl->callback))
        {
            args.hdl = hdl;
            args.event = SCI_EVT_XFER_DONE;

            /* Casting pointer to void* type is valid */
            hdl->callback((void *)&args);
        }
    }
} /* End of function sci_fifo_receive_sync() */
#endif /* End of SCI_CFG_FIFO_INCLUDED */
#endif /* End of SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED */

#if SCI_CFG_FIFO_INCLUDED
/*****************************************************************************
* Function Name: sci_fifo_receive
* Description  : FIFO Receive for SCI
* Arguments    : hdl - 
*                    handle for channel (ptr to chan control block)
* Return Value : none
******************************************************************************/
static void sci_fifo_receive(sci_hdl_t const hdl)
{
#if (SCI_CFG_ASYNC_INCLUDED)
    uint16_t        cnt;
    uint16_t        fifo_num;
    sci_cb_args_t   args;
    uint8_t         byte_rx[SCI_FIFO_FRAME_SIZE];
#endif

    if (SCI_MODE_ASYNC == hdl->mode)
    {
#if (SCI_CFG_ASYNC_INCLUDED)
        /* Casting unsigned char type to uint16_t type is valid */
        fifo_num = (uint16_t)hdl->rom->regs->FDR.BIT.R;

        /* RX FIFO flush */
        /* WAIT_LOOP */
        for (cnt = 0; cnt < fifo_num; cnt++)
        {
            /* Read byte */
            SCI_RDR(byte_rx[cnt]);
        }

        /* Determine amount of space left in rx queue */
        (void)R_BYTEQ_Unused(hdl->u_rx_data.que, &cnt);
        if (cnt >= fifo_num)
        {
            /* free space is enough */
            args.event = SCI_EVT_RX_CHAR;
        }
        else
        {
            /* insufficient free space, store as much as possible */
            fifo_num = cnt;
            args.event = SCI_EVT_RXBUF_OVFL;
        }

        /* WAIT_LOOP */
        for (cnt = 0; cnt < fifo_num; cnt++)
        {
            /* store bytes to rx queue for R_SCI_Receive */
            (void)R_BYTEQ_Put(hdl->u_rx_data.que, byte_rx[cnt]);
        }

        /* Do callback if available */
        if ((NULL != hdl->callback) && (FIT_NO_FUNC != hdl->callback))
        {
            args.hdl = hdl;

            /* Number of bytes were stored to queue */
            args.num = (uint8_t)fifo_num;

            /* Casting pointer to void* type is valid */
            hdl->callback((void *)&args);
        }
#endif /* End of SCI_CFG_ASYNC_INCLUDED*/
    }
    else
    {
#if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
        /* SCI Receive */
        sci_fifo_receive_sync(hdl);
#endif
    }

    /* When the readings of receive data are completed, set the SSRFIFO.RDF flag to 0. */
    if (1 == hdl->rom->regs->SSRFIFO.BIT.RDF)
    {
        /* Casting 8 bits to unsigned char type is valid */
        hdl->rom->regs->SSRFIFO.BYTE = (unsigned char)~SCI_SSRFIFO_RDF_MASK;
    }

    if (SCI_MODE_ASYNC == hdl->mode)
    {
        if (1 == hdl->rom->regs->SSRFIFO.BIT.DR)
        {
            /* Casting 8 bits to unsigned char type is valid */
            hdl->rom->regs->SSRFIFO.BYTE = (unsigned char)~SCI_SSRFIFO_DR_MASK;
        }
    }
} /* End of function sci_fifo_receive() */
#endif /* End of SCI_CFG_FIFO_INCLUDED */

#if SCI_CFG_DATA_MATCH_INCLUDED
/*****************************************************************************
* Function Name: sci_receive_data_match
* Description  : SCI receive data match
* Arguments    : hdl -
*                    handle for channel (ptr to chan control block)
* Return Value : none
******************************************************************************/
static void sci_receive_data_match(sci_hdl_t const hdl)
{
    sci_cb_args_t   args;
    uint8_t         byte;

    if (SCI_MODE_ASYNC == hdl->mode)
    {
#if (SCI_CFG_ASYNC_INCLUDED)
        if (0 == hdl->rom->regs->DCCR.BIT.DCME) /* DCME automatically set 0 when data matched */
        {
            hdl->rom->regs->DCCR.BIT.DCMF = 0; /* Clear Data Match Flag */

            if ((0 == hdl->rom->regs->DCCR.BIT.DFER )  &&  (0 == hdl->rom->regs->DCCR.BIT.DPER )) /* Check framing error and parity error */
            {
                /* Casting unsigned char type to unin8_t type is valid */
                byte = (uint8_t)(hdl->rom->regs->CDR.BYTE.L); /* Read data from comparison data register */

                /* Place byte in queue */
                if (R_BYTEQ_Put(hdl->u_rx_data.que, byte) == BYTEQ_SUCCESS)
                {
                    args.event = SCI_EVT_RX_CHAR_MATCH;
                }
                else
                {
                    args.event = SCI_EVT_RXBUF_OVFL;
                }

                /* Do callback if available */
                if ((NULL != hdl->callback) && (FIT_NO_FUNC != hdl->callback))
                {
                    args.hdl = hdl;
                    args.byte = byte;

                    /* Casting to void* type is valid  */
                    hdl->callback((void *)&args);
                }
            }
        }
#endif /* End of SCI_CFG_ASYNC_INCLUDED */
    }
} /* End of function sci_receive_data_match() */
#endif /* End of SCI_CFG_DATA_MATCH_INCLUDED */

/*****************************************************************************
* Function Name: rxi_handler
* Description  : RXI interrupt handler for SCI
* Arguments    : hdl - 
*                    handle for channel (ptr to chan control block)
* Return Value : none
******************************************************************************/
void rxi_handler(sci_hdl_t const hdl)
{
#if SCI_CFG_DATA_MATCH_INCLUDED
    if (1 == hdl->rom->regs->DCCR.BIT.DCMF) /* Check Data match flag */
    {
        sci_receive_data_match(hdl);
    }
    else
#endif
#if SCI_CFG_FIFO_INCLUDED
    if (true == hdl->fifo_ctrl)
    {
        /* SCI FIFO Receive */
        sci_fifo_receive(hdl);
    }
    else
#endif
    {
        /* SCI Receive */
        sci_receive(hdl);
    }
} /* End of function rxi_handler() */


/*****************************************************************************
* Function Name: sci_error
* Description  : Error for SCI
* Arguments    : hdl - 
*                    handle for channel (ptr to chan control block)
* Return Value : none
******************************************************************************/
static void sci_error(sci_hdl_t const hdl)
{
    sci_cb_args_t   args;
    uint8_t         byte;
    uint8_t         reg;

    reg = SCI_SSR;
    if (0 != (reg & SCI_RCVR_ERR_MASK))
    {
        if (0 != (reg & SCI_SSR_ORER_MASK))
        {
            args.event = SCI_EVT_OVFL_ERR;
        }
#if (SCI_CFG_ASYNC_INCLUDED)
        else if (0 != (reg & SCI_SSR_PER_MASK))
        {
            args.event = SCI_EVT_PARITY_ERR;
        }
        else if (0 != (reg & SCI_SSR_FER_MASK))
        {
            args.event = SCI_EVT_FRAMING_ERR;
        }
#endif
        else
        {
            /* Do Nothing */
        }

        /* Flush register */
        SCI_RDR(byte);

        /* Clear error condition */
        /* WAIT_LOOP */
        while (0 != (SCI_SSR & SCI_RCVR_ERR_MASK))
        {
            SCI_RDR(byte);

            reg      = SCI_SSR;
            reg     &= (~SCI_RCVR_ERR_MASK);
            reg     |= SCI_SSR_CLR_MASK;
            SCI_SSR  = reg;

            if (0 != (SCI_SSR & SCI_RCVR_ERR_MASK))
            {
                R_BSP_NOP(); /* read and Compare */
            }
        }

        /* Do callback for error */
        if ((NULL != hdl->callback) && (FIT_NO_FUNC != hdl->callback))
        {
            args.hdl = hdl;
            args.byte = byte;

            /* Casting to void* type is valid */
            hdl->callback((void *)&args);
        }
    }

} /* End of function sci_error() */

#if SCI_CFG_FIFO_INCLUDED
/*****************************************************************************
* Function Name: sci_fifo_error
* Description  : FIFO Error for SCI
* Arguments    : hdl - 
*                    handle for channel (ptr to chan control block)
* Return Value : none
******************************************************************************/
static void sci_fifo_error(sci_hdl_t const hdl)
{
    sci_cb_args_t       args;
    uint8_t             reg;
    volatile uint8_t    ssrfifo_data;
    volatile uint16_t   dummy;

    reg = SCI_SSRFIFO;
    if (0 != (reg & SCI_RCVR_ERR_MASK))
    {
        if (0 != (reg & SCI_SSR_ORER_MASK))
        {
            args.event = SCI_EVT_OVFL_ERR;
        }
#if (SCI_CFG_ASYNC_INCLUDED)
        else if (0 != (reg & SCI_SSR_PER_MASK))
        {
            args.event = SCI_EVT_PARITY_ERR;
        }
        else if (0 != (reg & SCI_SSR_FER_MASK))
        {
            args.event = SCI_EVT_FRAMING_ERR;
        }
#endif
        else
        {
            /* Do Nothing */
        }

        /* Do callback for error */
        if ((NULL != hdl->callback) && (FIT_NO_FUNC != hdl->callback))
        {
            args.hdl = hdl;
            args.byte = 0;

            /* Casting pointer to void* type is valid */
            hdl->callback((void *)&args);
        }

        /* if error condition don't clear in callback when it clear at here */
        reg = SCI_SSRFIFO;
        if (0 != (reg & SCI_RCVR_ERR_MASK))
        {
            /* Flush register */
            /* WAIT_LOOP */
            while (0 != hdl->rom->regs->FDR.BIT.R)
            {
                dummy = hdl->rom->regs->FRDR.WORD;              /* FRDR dummy read */
            }

            /* Clear error condition */
            /* WAIT_LOOP */
            while (0x00 != (SCI_SSRFIFO & SCI_RCVR_ERR_MASK))   /* Check PER, FER, ORER flags */
            {
                ssrfifo_data = SCI_SSRFIFO;                     /* SSRFIFO dummy read */
                SCI_SSRFIFO = (uint8_t)~SCI_RCVR_ERR_MASK;      /* PER, FER, ORER clear */
                if (0x00 != (SCI_SSRFIFO & SCI_RCVR_ERR_MASK))
                {
                    R_BSP_NOP();                                /* read and Compare */
                }
            }
        }
    }

    return;
} /* End of function sci_fifo_error() */
#endif /* End of SCI_CFG_FIFO_INCLUDED */

/*****************************************************************************
* Function Name: eri_handler
* Description  : ERI interrupt handler for SCI UART mode
* Arguments    : hdl -
*                    handle for channel (ptr to chan control block)
* Return Value : none
******************************************************************************/
void eri_handler(sci_hdl_t const hdl)
{
#if SCI_CFG_FIFO_INCLUDED
    if (true == hdl->fifo_ctrl)
    {
        /* SCI FIFO Error */
        sci_fifo_error(hdl);
    }
    else
#endif
    {
        /* SCI error */
        sci_error(hdl);
    }
} /* End of function eri_handler() */

/***********************************************************************************************************************
* Function Name: R_SCI_Control
********************************************************************************************************************//**
* @brief  This function configures and controls the operating mode for the SCI channel.
*
* @param[in] hdl  Handle for channel. Set hdl when R_SCI_Open() is successfully processed.
*
* @param[in] cmd  Command to run (see Section 3. R_SCI_Control() in application note for details)
*
* @param[in] p_args   Pointer to arguments (see Section 3. R_SCI_Control() in application note for details) specific to
* command, casted to void *
*
* @retval SCI_SUCCESS  Successful; channel initialized.
*
* @retval SCI_ERR_NULL_PTR  hdl or p_args pointer is NULL (when required)
*
* @retval SCI_ERR_BAD_MODE  Mode specified not currently supported
*
* @retval SCI_ERR_INVALID_ARG
*                    The cmd value or an element of p_args contains an invalid value.
* @details This function is used for configuring special hardware features such as changing driver configuration and
* obtaining driver status.
* The CTS/ RTS pin functions as RTS by default hardware control. By issuing an SCI_CMD_EN_CTS_IN, the pin functions as CTS.
* @note When SCI_CMD_CHANGE_BAUD is used, the optimum values for BRR, SEMR.ABCS, and SMR.CKS is calculated based on
* the bit rate specified. This however does not guarantee a low bit error rate for all peripheral clock/baud rate
* combinations.\n
* If the command SCI_CMD_EN_CTS_IN is to be used, the pin direction must be selected before calling the
* R_SCI_Open() function, and the pin function and mode must be selected after calling the R_SCI_Open()
* function. See Section 3. R_SCI_Control() for details.
*/
sci_err_t R_SCI_Control(sci_hdl_t const     hdl,
                        sci_cmd_t const     cmd,
                        void                *p_args)
{
    sci_err_t   err = SCI_SUCCESS;
    sci_baud_t  *baud;
    int32_t     bit_err;


#if SCI_CFG_PARAM_CHECKING_ENABLE
    /* Check argument hdl */
    if ((NULL == hdl) || (FIT_NO_PTR == hdl))
    {
        return SCI_ERR_NULL_PTR;
    }

    /* Check argument p_args*/
    if ((NULL == p_args) || (FIT_NO_PTR == p_args))
    {
        if (SCI_CMD_CHANGE_BAUD == cmd)
        {
            return SCI_ERR_NULL_PTR;
        }
#if SCI_CFG_FIFO_INCLUDED
        if ((SCI_CMD_CHANGE_TX_FIFO_THRESH == cmd) || (SCI_CMD_CHANGE_RX_FIFO_THRESH == cmd))
        {
            return SCI_ERR_NULL_PTR;
        }
#endif
#if defined(BSP_MCU_RX64M) || defined(BSP_MCU_RX71M) || defined(BSP_MCU_RX65N) || defined(BSP_MCU_RX66T) || defined(BSP_MCU_RX72T) || defined(BSP_MCU_RX72M) || defined(BSP_MCU_RX72N) || defined(BSP_MCU_RX66N)
        if ((SCI_CMD_SET_TXI_PRIORITY == cmd) || (SCI_CMD_SET_RXI_PRIORITY == cmd))
        {
            return SCI_ERR_NULL_PTR;
        }
#endif
    }
    if ((SCI_MODE_OFF == hdl->mode) || (SCI_MODE_MAX <= hdl->mode))
    {
        return SCI_ERR_BAD_MODE;
    }
#if SCI_CFG_FIFO_INCLUDED
    if (SCI_CMD_CHANGE_TX_FIFO_THRESH == cmd)
    {
        /* Casting void* type is valid */
        if (15 < (*(uint8_t *)p_args))
        {
            return SCI_ERR_INVALID_ARG;
        }
    }
    if (SCI_CMD_CHANGE_RX_FIFO_THRESH == cmd)
    {
        /* Casting void* type is valid */
        if ((1 > (*(uint8_t *)p_args)) || (15 < (*(uint8_t *)p_args)))
        {
            return SCI_ERR_INVALID_ARG;
        }
    }
#endif
#if defined(BSP_MCU_RX64M) || defined(BSP_MCU_RX71M) || defined(BSP_MCU_RX65N) || defined(BSP_MCU_RX66T) || defined(BSP_MCU_RX72T) || defined(BSP_MCU_RX72M) || defined(BSP_MCU_RX72N) || defined(BSP_MCU_RX66N)
    if ((SCI_CMD_SET_TXI_PRIORITY == cmd) || (SCI_CMD_SET_RXI_PRIORITY == cmd))
    {
        /* Casting void* type is valid */
        if ((1 > (*(uint8_t *)p_args)) || (BSP_MCU_IPL_MAX < (*(uint8_t *)p_args)))
        {
            return SCI_ERR_INVALID_ARG;
        }
    }
#endif
#endif /* End of SCI_CFG_PARAM_CHECKING_ENABLE */
    
    /* COMMANDS COMMON TO ALL MODES */

    switch (cmd)
    {
    case (SCI_CMD_CHANGE_BAUD):
    {
        /* Casting void* type is valid */
        baud = (sci_baud_t *)p_args;
#if (SCI_CFG_ASYNC_INCLUDED)
        hdl->pclk_speed = baud->pclk;           // save for break generation
#endif
        hdl->rom->regs->SCR.BYTE &= (~SCI_EN_XCVR_MASK);
        SCI_SCR_DUMMY_READ;
        bit_err = sci_init_bit_rate(hdl, baud->pclk, baud->rate);
        SCI_IR_TXI_CLEAR;
        hdl->rom->regs->SCR.BYTE |= SCI_EN_XCVR_MASK;
        if (1000 == bit_err)
        {
            err = SCI_ERR_INVALID_ARG;      // impossible baud rate; 100% error
        }
        else
        {
            hdl->baud_rate = baud->rate;    // save for break generation
        }
        break;
    }

    case (SCI_CMD_EN_CTS_IN):
    {
        if (SCI_MODE_SSPI != hdl->mode)
        {
            /* PFS & port pins must be configured for CTS prior to calling this */
            hdl->rom->regs->SCR.BYTE &= (~SCI_EN_XCVR_MASK);
            SCI_SCR_DUMMY_READ;
            hdl->rom->regs->SPMR.BIT.CTSE = 1;      // enable CTS input
            SCI_IR_TXI_CLEAR;
            hdl->rom->regs->SCR.BYTE |= SCI_EN_XCVR_MASK;
        }
        else
        {
            /* Can not use CTS in smart card interface mode, simple SPI mode, and simple I2C mode */
            err = SCI_ERR_INVALID_ARG;
        }
        break;
    }

#if SCI_CFG_FIFO_INCLUDED
    case (SCI_CMD_CHANGE_TX_FIFO_THRESH):
    {
        if (true == hdl->fifo_ctrl)
        {
            /* save current TX FIFO threshold */
            hdl->tx_curr_thresh = *((uint8_t *)p_args);

            /* change TX FIFO threshold */
            hdl->rom->regs->SCR.BYTE &= (~SCI_EN_XCVR_MASK);
            SCI_SCR_DUMMY_READ;

            /* Casting void* type is valid */
            hdl->rom->regs->FCR.BIT.TTRG = *((uint8_t *)p_args);
            SCI_IR_TXI_CLEAR;
            hdl->rom->regs->SCR.BYTE |= SCI_EN_XCVR_MASK;
        }
        else
        {
            err = SCI_ERR_INVALID_ARG;
        }
        break;
    }

    case (SCI_CMD_CHANGE_RX_FIFO_THRESH):
    {
        if (true == hdl->fifo_ctrl)
        {
            /* save current RX FIFO threshold */
            hdl->rx_curr_thresh = *((uint8_t *)p_args);

            /* change RX FIFO threshold */
            hdl->rom->regs->SCR.BYTE &= (~SCI_EN_XCVR_MASK);
            SCI_SCR_DUMMY_READ;

            /* Casting void* type is valid */
            hdl->rom->regs->FCR.BIT.RTRG = *((uint8_t *)p_args);
            SCI_IR_TXI_CLEAR;
            hdl->rom->regs->SCR.BYTE |= SCI_EN_XCVR_MASK;
        }
        else
        {
            err = SCI_ERR_INVALID_ARG;
        }
        break;
    }
#endif /* End of SCI_CFG_FIFO_INCLUDED */

#if defined(BSP_MCU_RX64M) || defined(BSP_MCU_RX71M) || defined(BSP_MCU_RX65N) || defined(BSP_MCU_RX66T) || defined(BSP_MCU_RX72T) || defined(BSP_MCU_RX72M) || defined(BSP_MCU_RX72N) || defined(BSP_MCU_RX66N)
    case (SCI_CMD_SET_TXI_PRIORITY):
    {
        /* Casting void type to uint8_t type is valid */
        *hdl->rom->ipr_txi = *((uint8_t *)p_args);
        break;
    }

    case (SCI_CMD_SET_RXI_PRIORITY):
    {
        /* Casting void type to uint8_t type is valid */
        *hdl->rom->ipr_rxi = *((uint8_t *)p_args);
        break;
    }
#endif

    default:
    {
        /* ASYNC-SPECIFIC COMMANDS */
        if (SCI_MODE_ASYNC == hdl->mode)
        {
#if (SCI_CFG_ASYNC_INCLUDED)
            err = sci_async_cmds(hdl, cmd, p_args);
#endif
        }

        /* SSPI/SYNC-SPECIFIC COMMANDS */
        else
        {
#if (SCI_CFG_SSPI_INCLUDED || SCI_CFG_SYNC_INCLUDED)
            err = sci_sync_cmds(hdl, cmd, p_args);
#endif
        }
        break;
    }
    }

    return err;
} /* End of function R_SCI_Control() */

/***********************************************************************************************************************
* Function Name: R_SCI_Close
********************************************************************************************************************//**
* @brief This function removes power from the SCI channel and disables the associated interrupts.
*
* @param[in] hdl  Handle for channel. Set hdl when R_SCI_Open() is successfully processed.
*
* @retval SCI_SUCCESS Successful; channel closed
*
* @retval SCI_ERR_NULL_PTR hdl is NULL 
*
* @details    Disables the SCI channel designated by the handle and enters module-stop state.
* @note This function will abort any transmission or reception that may be in progress.
*/
sci_err_t R_SCI_Close(sci_hdl_t const hdl)
{

#if SCI_CFG_PARAM_CHECKING_ENABLE
    /* Check argument hdl */
    if ((NULL == hdl) || (FIT_NO_PTR == hdl))
    {
        return SCI_ERR_NULL_PTR;
    }
#endif

    /* disable ICU interrupts */
    sci_disable_ints(hdl);

    /* free tx and rx queues */
#if (SCI_CFG_ASYNC_INCLUDED)
    if (SCI_MODE_ASYNC == hdl->mode)
    {
        R_BYTEQ_Close(hdl->u_tx_data.que);
        R_BYTEQ_Close(hdl->u_rx_data.que);
    }
#endif
#if SCI_CFG_FIFO_INCLUDED
    if (true == hdl->fifo_ctrl)
    {
        /* reset FIFO threshold */
        hdl->rx_curr_thresh = hdl->rx_dflt_thresh;
        hdl->tx_curr_thresh = hdl->tx_dflt_thresh;
    }
#endif

    /* mark the channel as not in use and power down */
    hdl->mode = SCI_MODE_OFF;
    power_off(hdl);

    return SCI_SUCCESS;
} /* End of function R_SCI_Close() */


/***********************************************************************************************************************
* Function Name: R_SCI_GetVersion
********************************************************************************************************************//**
* @brief This function returns the driver version number at runtime.
* @return Version number.
* @details  Returns the version of this module. The version number is encoded such that the top 2 bytes are the major
* version number and the bottom 2 bytes are the minor version number.
* @note None
*/
uint32_t  R_SCI_GetVersion(void)
{
    uint32_t const version = (SCI_VERSION_MAJOR << 16) | SCI_VERSION_MINOR;

    return version;
} /* End of function R_SCI_GetVersion() */
