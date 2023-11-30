/******************************************************************************
 * @file     usci_uart.h
 * @version  V3.00
 * @brief    M2351 series USCI UART (UUART) driver header file
 *
 * @note
 * Copyright (C) 2016 Nuvoton Technology Corp. All rights reserved.
*****************************************************************************/
#ifndef __USCI_UART_H__
#define __USCI_UART_H__


#ifdef __cplusplus
extern "C"
{
#endif


/** @addtogroup Standard_Driver Standard Driver
  @{
*/

/** @addtogroup USCI_UART_Driver USCI_UART Driver
  @{
*/

/** @addtogroup USCI_UART_EXPORTED_CONSTANTS USCI_UART Exported Constants
  @{
*/

/*---------------------------------------------------------------------------------------------------------*/
/* UUART_LINECTL constants definitions                                                                     */
/*---------------------------------------------------------------------------------------------------------*/
#define UUART_WORD_LEN_6     (6UL << UUART_LINECTL_DWIDTH_Pos) /*!< UUART_LINECTL setting to set UART word length to 6 bits */
#define UUART_WORD_LEN_7     (7UL << UUART_LINECTL_DWIDTH_Pos) /*!< UUART_LINECTL setting to set UART word length to 7 bits */
#define UUART_WORD_LEN_8     (8UL << UUART_LINECTL_DWIDTH_Pos) /*!< UUART_LINECTL setting to set UART word length to 8 bits */
#define UUART_WORD_LEN_9     (9UL << UUART_LINECTL_DWIDTH_Pos) /*!< UUART_LINECTL setting to set UART word length to 9 bits */

/*---------------------------------------------------------------------------------------------------------*/
/* UUART_PROTCTL constants definitions                                                                     */
/*---------------------------------------------------------------------------------------------------------*/
#define UUART_PARITY_NONE    (0x0UL << UUART_PROTCTL_PARITYEN_Pos)    /*!< UUART_PROTCTL setting to set UART as no parity */
#define UUART_PARITY_ODD     (0x1UL << UUART_PROTCTL_PARITYEN_Pos)    /*!< UUART_PROTCTL setting to set UART as odd parity */
#define UUART_PARITY_EVEN    (0x3UL << UUART_PROTCTL_PARITYEN_Pos)    /*!< UUART_PROTCTL setting to set UART as even parity */

#define UUART_STOP_BIT_1     (0x0UL) /*!< UUART_PROTCTL setting for one stop bit */
#define UUART_STOP_BIT_2     (0x1UL) /*!< UUART_PROTCTL setting for two stop bit */

/*---------------------------------------------------------------------------------------------------------*/
/* USCI UART interrupt mask definitions                                                                            */
/*---------------------------------------------------------------------------------------------------------*/
#define UUART_ABR_INT_MASK      (0x002UL) /*!< Auto-baud rate interrupt mask */
#define UUART_RLS_INT_MASK      (0x004UL) /*!< Receive line status interrupt mask */
#define UUART_BUF_RXOV_INT_MASK (0x008UL) /*!< Buffer RX overrun interrupt mask */
#define UUART_TXST_INT_MASK     (0x010UL) /*!< TX start interrupt mask */
#define UUART_TXEND_INT_MASK    (0x020UL) /*!< Tx end interrupt mask */
#define UUART_RXST_INT_MASK     (0x040UL) /*!< RX start interrupt mask */
#define UUART_RXEND_INT_MASK    (0x080UL) /*!< RX end interrupt mask */


/*@}*/ /* end of group USCI_UART_EXPORTED_CONSTANTS */


/** @addtogroup USCI_UART_EXPORTED_FUNCTIONS USCI_UART Exported Functions
  @{
*/


/**
 *    @brief        Write USCI_UART data
 *
 *    @param[in]    uuart   The pointer of the specified USCI_UART module
 *    @param[in]    u8Data  Data byte to transmit.
 *
 *    @return       None
 *
 *    @details      This macro write Data to Tx data register.
 */
#define UUART_WRITE(uuart, u8Data)    ((uuart)->TXDAT = (u8Data))


/**
 *    @brief        Read USCI_UART data
 *
 *    @param[in]    uuart    The pointer of the specified USCI_UART module
 *
 *    @return       The oldest data byte in RX buffer.
 *
 *    @details      This macro read Rx data register.
 */
#define UUART_READ(uuart)    ((uuart)->RXDAT)


/**
 *    @brief        Get Tx empty
 *
 *    @param[in]    uuart    The pointer of the specified USCI_UART module
 *
 *    @retval       0   Tx buffer is not empty
 *    @retval       >=1 Tx buffer is empty
 *
 *    @details      This macro get Transmitter buffer empty register value.
 */
#define UUART_GET_TX_EMPTY(uuart)    ((uuart)->BUFSTS & UUART_BUFSTS_TXEMPTY_Msk)


/**
 *    @brief        Get Rx empty
 *
 *    @param[in]    uuart    The pointer of the specified USCI_UART module
 *
 *    @retval       0   Rx buffer is not empty
 *    @retval       >=1 Rx buffer is empty
 *
 *    @details      This macro get Receiver buffer empty register value.
 */
#define UUART_GET_RX_EMPTY(uuart)    ((uuart)->BUFSTS & UUART_BUFSTS_RXEMPTY_Msk)


/**
 *    @brief        Check specified usci_uart port transmission is over.
 *
 *    @param[in]    uuart    The pointer of the specified USCI_UART module
 *
 *    @retval       0 Tx transmission is not over
 *    @retval       1 Tx transmission is over
 *
 *    @details      This macro return Transmitter Empty Flag register bit value. \n
 *                  It indicates if specified usci_uart port transmission is over nor not.
 */
#define UUART_IS_TX_EMPTY(uuart)    (((uuart)->BUFSTS & UUART_BUFSTS_TXEMPTY_Msk) >> UUART_BUFSTS_TXEMPTY_Pos)


/**
 *    @brief        Check specified usci_uart port receiver is empty.
 *
 *    @param[in]    uuart    The pointer of the specified USCI_UART module
 *
 *    @retval       0 Rx receiver is not empty
 *    @retval       1 Rx receiver is empty
 *
 *    @details      This macro return Receive Empty Flag register bit value. \n
 *                  It indicates if specified usci_uart port receiver is empty nor not.
 */
#define UUART_IS_RX_EMPTY(uuart)    (((uuart)->BUFSTS & UUART_BUFSTS_RXEMPTY_Msk) >> UUART_BUFSTS_RXEMPTY_Pos)


/**
 *    @brief        Wait specified usci_uart port transmission is over
 *
 *    @param[in]    uuart    The pointer of the specified USCI_UART module
 *
 *    @return       None
 *
 *    @details      This macro wait specified usci_uart port transmission is over.
 */
#define UUART_WAIT_TX_EMPTY(uuart)    while(!((((uuart)->BUFSTS) & UUART_BUFSTS_TXEMPTY_Msk) >> UUART_BUFSTS_TXEMPTY_Pos))


/**
 *    @brief        Check TX buffer is full or not
 *
 *    @param[in]    uuart    The pointer of the specified USCI_UART module
 *
 *    @retval       1 TX buffer is full
 *    @retval       0 TX buffer is not full
 *
 *    @details      This macro check TX buffer is full or not.
 */
#define UUART_IS_TX_FULL(uuart)    (((uuart)->BUFSTS & UUART_BUFSTS_TXFULL_Msk)>>UUART_BUFSTS_TXFULL_Pos)


/**
 *    @brief        Check RX buffer is full or not
 *
 *    @param[in]    uuart    The pointer of the specified USCI_UART module
 *
 *    @retval       1 RX buffer is full
 *    @retval       0 RX buffer is not full
 *
 *    @details      This macro check RX buffer is full or not.
 */
#define UUART_IS_RX_FULL(uuart)    (((uuart)->BUFSTS & UUART_BUFSTS_RXFULL_Msk)>>UUART_BUFSTS_RXFULL_Pos)


/**
 *    @brief        Get Tx full register value
 *
 *    @param[in]    uuart    The pointer of the specified USCI_UART module
 *
 *    @retval       0   Tx buffer is not full.
 *    @retval       >=1 Tx buffer is full.
 *
 *    @details      This macro get Tx full register value.
 */
#define UUART_GET_TX_FULL(uuart)    ((uuart)->BUFSTS & UUART_BUFSTS_TXFULL_Msk)


/**
 *    @brief        Get Rx full register value
 *
 *    @param[in]    uuart    The pointer of the specified USCI_UART module
 *
 *    @retval       0   Rx buffer is not full.
 *    @retval       >=1 Rx buffer is full.
 *
 *    @details      This macro get Rx full register value.
 */
#define UUART_GET_RX_FULL(uuart)    ((uuart)->BUFSTS & UUART_BUFSTS_RXFULL_Msk)


/**
 *    @brief        Enable specified USCI_UART protocol interrupt
 *
 *    @param[in]    uuart      The pointer of the specified USCI_UART module
 *    @param[in]    u32IntSel  Interrupt type select
 *                             - \ref UUART_PROTIEN_RLSIEN_Msk   : Rx Line status interrupt
 *                             - \ref UUART_PROTIEN_ABRIEN_Msk   : Auto-baud rate interrupt
 *
 *    @return       None
 *
 *    @details      This macro enable specified USCI_UART protocol interrupt.
 */
#define UUART_ENABLE_PROT_INT(uuart, u32IntSel)    ((uuart)->PROTIEN |= (u32IntSel))


/**
 *    @brief        Disable specified USCI_UART protocol interrupt
 *
 *    @param[in]    uuart      The pointer of the specified USCI_UART module
 *    @param[in]    u32IntSel  Interrupt type select
 *                             - \ref UUART_PROTIEN_RLSIEN_Msk   : Rx Line status interrupt
 *                             - \ref UUART_PROTIEN_ABRIEN_Msk   : Auto-baud rate interrupt
 *
 *    @return       None
 *
 *    @details      This macro disable specified USCI_UART protocol interrupt.
 */
#define UUART_DISABLE_PROT_INT(uuart, u32IntSel)    ((uuart)->PROTIEN &= ~(u32IntSel))


/**
 *    @brief        Enable specified USCI_UART buffer interrupt
 *
 *    @param[in]    uuart      The pointer of the specified USCI_UART module
 *    @param[in]    u32IntSel  Interrupt type select
 *                             - \ref UUART_BUFCTL_RXOVIEN_Msk     : Receive buffer overrun error interrupt
 *
 *    @return       None
 *
 *    @details      This macro enable specified USCI_UART buffer interrupt.
 */
#define UUART_ENABLE_BUF_INT(uuart, u32IntSel)    ((uuart)->BUFCTL |= (u32IntSel))


/**
 *    @brief        Disable specified USCI_UART buffer interrupt
 *
 *    @param[in]    uuart      The pointer of the specified USCI_UART module
 *    @param[in]    u32IntSel  Interrupt type select
 *                             - \ref UUART_BUFCTL_RXOVIEN_Msk     : Receive buffer overrun error interrupt
 *
 *    @return       None
 *
 *    @details      This macro disable specified USCI_UART buffer interrupt.
 */
#define UUART_DISABLE_BUF_INT(uuart, u32IntSel)    ((uuart)->BUFCTL &= ~ (u32IntSel))


/**
 *    @brief        Enable specified USCI_UART transfer interrupt
 *
 *    @param[in]    uuart      The pointer of the specified USCI_UART module
 *    @param[in]    u32IntSel  Interrupt type select
 *                             - \ref UUART_INTEN_RXENDIEN_Msk  : Receive end interrupt
 *                             - \ref UUART_INTEN_RXSTIEN_Msk   : Receive start interrupt
 *                             - \ref UUART_INTEN_TXENDIEN_Msk  : Transmit end interrupt
 *                             - \ref UUART_INTEN_TXSTIEN_Msk   : Transmit start interrupt
 *
 *    @return       None
 *
 *    @details      This macro enable specified USCI_UART transfer interrupt.
 */
#define UUART_ENABLE_TRANS_INT(uuart, u32IntSel)    ((uuart)->INTEN |= (u32IntSel))


/**
 *    @brief        Disable specified USCI_UART transfer interrupt
 *
 *    @param[in]    uuart      The pointer of the specified USCI_UART module
 *    @param[in]    u32IntSel  Interrupt type select
 *                             - \ref UUART_INTEN_RXENDIEN_Msk  : Receive end interrupt
 *                             - \ref UUART_INTEN_RXSTIEN_Msk   : Receive start interrupt
 *                             - \ref UUART_INTEN_TXENDIEN_Msk  : Transmit end interrupt
 *                             - \ref UUART_INTEN_TXSTIEN_Msk   : Transmit start interrupt
 *
 *    @return       None
 *
 *    @details      This macro disable specified USCI_UART transfer interrupt.
 */
#define UUART_DISABLE_TRANS_INT(uuart, u32IntSel)    ((uuart)->INTEN &= ~(u32IntSel))


/**
 *    @brief        Get protocol interrupt flag/status
 *
 *    @param[in]    uuart        The pointer of the specified USCI_UART module
 *
 *    @return       The interrupt flag/status of protocol status register.
 *
 *    @details      This macro get protocol status register value.
 */
#define UUART_GET_PROT_STATUS(uuart)    ((uuart)->PROTSTS)


/**
 *    @brief        Clear specified protocol interrupt flag
 *
 *    @param[in]    uuart           The pointer of the specified USCI_UART module
 *    @param[in]    u32IntTypeFlag  Interrupt Type Flag, should be
 *                                  - \ref UUART_PROTSTS_ABERRSTS_Msk    : Auto-baud Rate Error Interrupt Indicator
 *                                  - \ref UUART_PROTSTS_ABRDETIF_Msk    : Auto-baud Rate Detected Interrupt Flag
 *                                  - \ref UUART_PROTSTS_BREAK_Msk       : Break Flag
 *                                  - \ref UUART_PROTSTS_FRMERR_Msk      : Framing Error Flag
 *                                  - \ref UUART_PROTSTS_PARITYERR_Msk   : Parity Error Flag
 *                                  - \ref UUART_PROTSTS_RXENDIF_Msk     : Receive End Interrupt Flag
 *                                  - \ref UUART_PROTSTS_RXSTIF_Msk      : Receive Start Interrupt Flag
 *                                  - \ref UUART_PROTSTS_TXENDIF_Msk     : Transmit End Interrupt Flag
 *                                  - \ref UUART_PROTSTS_TXSTIF_Msk      : Transmit Start Interrupt Flag
 *
 *    @return       None
 *
 *    @details      This macro clear specified protocol interrupt flag.
 */
#define UUART_CLR_PROT_INT_FLAG(uuart,u32IntTypeFlag)    ((uuart)->PROTSTS = (u32IntTypeFlag))


/**
 *    @brief        Get transmit/receive buffer interrupt flag/status
 *
 *    @param[in]    uuart        The pointer of the specified USCI_UART module
 *
 *    @return       The interrupt flag/status of buffer status register.
 *
 *    @details      This macro get buffer status register value.
 */
#define UUART_GET_BUF_STATUS(uuart)    ((uuart)->BUFSTS)


/**
 *    @brief        Clear specified buffer interrupt flag
 *
 *    @param[in]    uuart           The pointer of the specified USCI_UART module
 *    @param[in]    u32IntTypeFlag  Interrupt Type Flag, should be
 *                                  - \ref UUART_BUFSTS_RXOVIF_Msk : Receive Buffer Over-run Error  Interrupt Indicator
 *
 *    @return       None
 *
 *    @details      This macro clear specified buffer interrupt flag.
 */
#define UUART_CLR_BUF_INT_FLAG(uuart,u32IntTypeFlag)    ((uuart)->BUFSTS = (u32IntTypeFlag))


/**
 *    @brief        Get wakeup flag
 *
 *    @param[in]    uuart    The pointer of the specified USCI_UART module
 *
 *    @retval       0       Chip did not wake up from power-down mode.
 *    @retval       1       Chip waked up from power-down mode.
 *
 *    @details      This macro get wakeup flag.
 */
#define UUART_GET_WAKEUP_FLAG(uuart)    ((uuart)->WKSTS & UUART_WKSTS_WKF_Msk ? 1: 0 )


/**
 *    @brief        Clear wakeup flag
 *
 *    @param[in]    uuart        The pointer of the specified USCI_UART module
 *
 *    @return       None
 *
 *    @details      This macro clear wakeup flag.
 */
#define UUART_CLR_WAKEUP_FLAG(uuart)    ((uuart)->WKSTS = UUART_WKSTS_WKF_Msk)


void UUART_ClearIntFlag(UUART_T* uuart, uint32_t u32Mask);
uint32_t UUART_GetIntFlag(UUART_T* uuart, uint32_t u32Mask);
void UUART_Close(UUART_T* uuart);
void UUART_DisableInt(UUART_T*  uuart, uint32_t u32Mask);
void UUART_EnableInt(UUART_T*  uuart, uint32_t u32Mask);
uint32_t UUART_Open(UUART_T* uuart, uint32_t u32baudrate);
uint32_t UUART_Read(UUART_T* uuart, uint8_t pu8RxBuf[], uint32_t u32ReadBytes);
uint32_t UUART_SetLine_Config(UUART_T* uuart, uint32_t u32baudrate, uint32_t u32data_width, uint32_t u32parity, uint32_t u32stop_bits);
uint32_t UUART_Write(UUART_T* uuart, uint8_t pu8TxBuf[], uint32_t u32WriteBytes);
void UUART_EnableWakeup(UUART_T* uuart, uint32_t u32WakeupMode);
void UUART_DisableWakeup(UUART_T* uuart);
void UUART_EnableFlowCtrl(UUART_T* uuart);
void UUART_DisableFlowCtrl(UUART_T* uuart);


/*@}*/ /* end of group USCI_UART_EXPORTED_FUNCTIONS */

/*@}*/ /* end of group USCI_UART_Driver */

/*@}*/ /* end of group Standard_Driver */

#ifdef __cplusplus
}
#endif

#endif /* __USCI_UART_H__ */

/*** (C) COPYRIGHT 2016 Nuvoton Technology Corp. ***/
