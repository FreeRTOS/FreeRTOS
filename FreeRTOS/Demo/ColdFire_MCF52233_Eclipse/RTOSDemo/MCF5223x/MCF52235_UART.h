/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.91
 */

#ifndef __MCF52235_UART_H__
#define __MCF52235_UART_H__


/*********************************************************************
*
* Universal Asynchronous Receiver Transmitter (UART)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_UART0_UMR1                       (*(vuint8 *)(&__IPSBAR[0x200]))
#define MCF_UART0_UMR2                       (*(vuint8 *)(&__IPSBAR[0x200]))
#define MCF_UART0_USR                        (*(vuint8 *)(&__IPSBAR[0x204]))
#define MCF_UART0_UCSR                       (*(vuint8 *)(&__IPSBAR[0x204]))
#define MCF_UART0_UCR                        (*(vuint8 *)(&__IPSBAR[0x208]))
#define MCF_UART0_URB                        (*(vuint8 *)(&__IPSBAR[0x20C]))
#define MCF_UART0_UTB                        (*(vuint8 *)(&__IPSBAR[0x20C]))
#define MCF_UART0_UIPCR                      (*(vuint8 *)(&__IPSBAR[0x210]))
#define MCF_UART0_UACR                       (*(vuint8 *)(&__IPSBAR[0x210]))
#define MCF_UART0_UIMR                       (*(vuint8 *)(&__IPSBAR[0x214]))
#define MCF_UART0_UISR                       (*(vuint8 *)(&__IPSBAR[0x214]))
#define MCF_UART0_UBG1                       (*(vuint8 *)(&__IPSBAR[0x218]))
#define MCF_UART0_UBG2                       (*(vuint8 *)(&__IPSBAR[0x21C]))
#define MCF_UART0_UIP                        (*(vuint8 *)(&__IPSBAR[0x234]))
#define MCF_UART0_UOP1                       (*(vuint8 *)(&__IPSBAR[0x238]))
#define MCF_UART0_UOP0                       (*(vuint8 *)(&__IPSBAR[0x23C]))

#define MCF_UART1_UMR1                       (*(vuint8 *)(&__IPSBAR[0x240]))
#define MCF_UART1_UMR2                       (*(vuint8 *)(&__IPSBAR[0x240]))
#define MCF_UART1_USR                        (*(vuint8 *)(&__IPSBAR[0x244]))
#define MCF_UART1_UCSR                       (*(vuint8 *)(&__IPSBAR[0x244]))
#define MCF_UART1_UCR                        (*(vuint8 *)(&__IPSBAR[0x248]))
#define MCF_UART1_URB                        (*(vuint8 *)(&__IPSBAR[0x24C]))
#define MCF_UART1_UTB                        (*(vuint8 *)(&__IPSBAR[0x24C]))
#define MCF_UART1_UIPCR                      (*(vuint8 *)(&__IPSBAR[0x250]))
#define MCF_UART1_UACR                       (*(vuint8 *)(&__IPSBAR[0x250]))
#define MCF_UART1_UIMR                       (*(vuint8 *)(&__IPSBAR[0x254]))
#define MCF_UART1_UISR                       (*(vuint8 *)(&__IPSBAR[0x254]))
#define MCF_UART1_UBG1                       (*(vuint8 *)(&__IPSBAR[0x258]))
#define MCF_UART1_UBG2                       (*(vuint8 *)(&__IPSBAR[0x25C]))
#define MCF_UART1_UIP                        (*(vuint8 *)(&__IPSBAR[0x274]))
#define MCF_UART1_UOP1                       (*(vuint8 *)(&__IPSBAR[0x278]))
#define MCF_UART1_UOP0                       (*(vuint8 *)(&__IPSBAR[0x27C]))

#define MCF_UART2_UMR1                       (*(vuint8 *)(&__IPSBAR[0x280]))
#define MCF_UART2_UMR2                       (*(vuint8 *)(&__IPSBAR[0x280]))
#define MCF_UART2_USR                        (*(vuint8 *)(&__IPSBAR[0x284]))
#define MCF_UART2_UCSR                       (*(vuint8 *)(&__IPSBAR[0x284]))
#define MCF_UART2_UCR                        (*(vuint8 *)(&__IPSBAR[0x288]))
#define MCF_UART2_URB                        (*(vuint8 *)(&__IPSBAR[0x28C]))
#define MCF_UART2_UTB                        (*(vuint8 *)(&__IPSBAR[0x28C]))
#define MCF_UART2_UIPCR                      (*(vuint8 *)(&__IPSBAR[0x290]))
#define MCF_UART2_UACR                       (*(vuint8 *)(&__IPSBAR[0x290]))
#define MCF_UART2_UIMR                       (*(vuint8 *)(&__IPSBAR[0x294]))
#define MCF_UART2_UISR                       (*(vuint8 *)(&__IPSBAR[0x294]))
#define MCF_UART2_UBG1                       (*(vuint8 *)(&__IPSBAR[0x298]))
#define MCF_UART2_UBG2                       (*(vuint8 *)(&__IPSBAR[0x29C]))
#define MCF_UART2_UIP                        (*(vuint8 *)(&__IPSBAR[0x2B4]))
#define MCF_UART2_UOP1                       (*(vuint8 *)(&__IPSBAR[0x2B8]))
#define MCF_UART2_UOP0                       (*(vuint8 *)(&__IPSBAR[0x2BC]))

#define MCF_UART_UMR(x)                      (*(vuint8 *)(&__IPSBAR[0x200 + ((x)*0x40)]))
#define MCF_UART_USR(x)                      (*(vuint8 *)(&__IPSBAR[0x204 + ((x)*0x40)]))
#define MCF_UART_UCSR(x)                     (*(vuint8 *)(&__IPSBAR[0x204 + ((x)*0x40)]))
#define MCF_UART_UCR(x)                      (*(vuint8 *)(&__IPSBAR[0x208 + ((x)*0x40)]))
#define MCF_UART_URB(x)                      (*(vuint8 *)(&__IPSBAR[0x20C + ((x)*0x40)]))
#define MCF_UART_UTB(x)                      (*(vuint8 *)(&__IPSBAR[0x20C + ((x)*0x40)]))
#define MCF_UART_UIPCR(x)                    (*(vuint8 *)(&__IPSBAR[0x210 + ((x)*0x40)]))
#define MCF_UART_UACR(x)                     (*(vuint8 *)(&__IPSBAR[0x210 + ((x)*0x40)]))
#define MCF_UART_UIMR(x)                     (*(vuint8 *)(&__IPSBAR[0x214 + ((x)*0x40)]))
#define MCF_UART_UISR(x)                     (*(vuint8 *)(&__IPSBAR[0x214 + ((x)*0x40)]))
#define MCF_UART_UBG1(x)                     (*(vuint8 *)(&__IPSBAR[0x218 + ((x)*0x40)]))
#define MCF_UART_UBG2(x)                     (*(vuint8 *)(&__IPSBAR[0x21C + ((x)*0x40)]))
#define MCF_UART_UIP(x)                      (*(vuint8 *)(&__IPSBAR[0x234 + ((x)*0x40)]))
#define MCF_UART_UOP1(x)                     (*(vuint8 *)(&__IPSBAR[0x238 + ((x)*0x40)]))
#define MCF_UART_UOP0(x)                     (*(vuint8 *)(&__IPSBAR[0x23C + ((x)*0x40)]))

/* Bit definitions and macros for MCF_UART_UMR */
#define MCF_UART_UMR_BC(x)                   (((x)&0x3)<<0)
#define MCF_UART_UMR_BC_5                    (0)
#define MCF_UART_UMR_BC_6                    (0x1)
#define MCF_UART_UMR_BC_7                    (0x2)
#define MCF_UART_UMR_BC_8                    (0x3)
#define MCF_UART_UMR_PT                      (0x4)
#define MCF_UART_UMR_PM(x)                   (((x)&0x3)<<0x3)
#define MCF_UART_UMR_ERR                     (0x20)
#define MCF_UART_UMR_RXIRQ                   (0x40)
#define MCF_UART_UMR_RXRTS                   (0x80)
#define MCF_UART_UMR_PM_MULTI_ADDR           (0x1C)
#define MCF_UART_UMR_PM_MULTI_DATA           (0x18)
#define MCF_UART_UMR_PM_NONE                 (0x10)
#define MCF_UART_UMR_PM_FORCE_HI             (0xC)
#define MCF_UART_UMR_PM_FORCE_LO             (0x8)
#define MCF_UART_UMR_PM_ODD                  (0x4)
#define MCF_UART_UMR_PM_EVEN                 (0)
#define MCF_UART_UMR_SB(x)                   (((x)&0xF)<<0)
#define MCF_UART_UMR_SB_STOP_BITS_1          (0x7)
#define MCF_UART_UMR_SB_STOP_BITS_15         (0x8)
#define MCF_UART_UMR_SB_STOP_BITS_2          (0xF)
#define MCF_UART_UMR_TXCTS                   (0x10)
#define MCF_UART_UMR_TXRTS                   (0x20)
#define MCF_UART_UMR_CM(x)                   (((x)&0x3)<<0x6)
#define MCF_UART_UMR_CM_NORMAL               (0)
#define MCF_UART_UMR_CM_ECHO                 (0x40)
#define MCF_UART_UMR_CM_LOCAL_LOOP           (0x80)
#define MCF_UART_UMR_CM_REMOTE_LOOP          (0xC0)

/* Bit definitions and macros for MCF_UART_USR */
#define MCF_UART_USR_RXRDY                   (0x1)
#define MCF_UART_USR_FFULL                   (0x2)
#define MCF_UART_USR_TXRDY                   (0x4)
#define MCF_UART_USR_TXEMP                   (0x8)
#define MCF_UART_USR_OE                      (0x10)
#define MCF_UART_USR_PE                      (0x20)
#define MCF_UART_USR_FE                      (0x40)
#define MCF_UART_USR_RB                      (0x80)

/* Bit definitions and macros for MCF_UART_UCSR */
#define MCF_UART_UCSR_TCS(x)                 (((x)&0xF)<<0)
#define MCF_UART_UCSR_TCS_SYS_CLK            (0xD)
#define MCF_UART_UCSR_TCS_CTM16              (0xE)
#define MCF_UART_UCSR_TCS_CTM                (0xF)
#define MCF_UART_UCSR_RCS(x)                 (((x)&0xF)<<0x4)
#define MCF_UART_UCSR_RCS_SYS_CLK            (0xD0)
#define MCF_UART_UCSR_RCS_CTM16              (0xE0)
#define MCF_UART_UCSR_RCS_CTM                (0xF0)

/* Bit definitions and macros for MCF_UART_UCR */
#define MCF_UART_UCR_RC(x)                   (((x)&0x3)<<0)
#define MCF_UART_UCR_RX_ENABLED              (0x1)
#define MCF_UART_UCR_RX_DISABLED             (0x2)
#define MCF_UART_UCR_TC(x)                   (((x)&0x3)<<0x2)
#define MCF_UART_UCR_TX_ENABLED              (0x4)
#define MCF_UART_UCR_TX_DISABLED             (0x8)
#define MCF_UART_UCR_MISC(x)                 (((x)&0x7)<<0x4)
#define MCF_UART_UCR_NONE                    (0)
#define MCF_UART_UCR_RESET_MR                (0x10)
#define MCF_UART_UCR_RESET_RX                (0x20)
#define MCF_UART_UCR_RESET_TX                (0x30)
#define MCF_UART_UCR_RESET_ERROR             (0x40)
#define MCF_UART_UCR_RESET_BKCHGINT          (0x50)
#define MCF_UART_UCR_START_BREAK             (0x60)
#define MCF_UART_UCR_STOP_BREAK              (0x70)

/* Bit definitions and macros for MCF_UART_URB */
#define MCF_UART_URB_RB(x)                   (((x)&0xFF)<<0)

/* Bit definitions and macros for MCF_UART_UTB */
#define MCF_UART_UTB_TB(x)                   (((x)&0xFF)<<0)

/* Bit definitions and macros for MCF_UART_UIPCR */
#define MCF_UART_UIPCR_CTS                   (0x1)
#define MCF_UART_UIPCR_COS                   (0x10)

/* Bit definitions and macros for MCF_UART_UACR */
#define MCF_UART_UACR_IEC                    (0x1)

/* Bit definitions and macros for MCF_UART_UIMR */
#define MCF_UART_UIMR_TXRDY                  (0x1)
#define MCF_UART_UIMR_FFULL_RXRDY            (0x2)
#define MCF_UART_UIMR_DB                     (0x4)
#define MCF_UART_UIMR_COS                    (0x80)

/* Bit definitions and macros for MCF_UART_UISR */
#define MCF_UART_UISR_TXRDY                  (0x1)
#define MCF_UART_UISR_FFULL_RXRDY            (0x2)
#define MCF_UART_UISR_DB                     (0x4)
#define MCF_UART_UISR_COS                    (0x80)

/* Bit definitions and macros for MCF_UART_UBG1 */
#define MCF_UART_UBG1_Divider_MSB(x)         (((x)&0xFF)<<0)

/* Bit definitions and macros for MCF_UART_UBG2 */
#define MCF_UART_UBG2_Divider_LSB(x)         (((x)&0xFF)<<0)

/* Bit definitions and macros for MCF_UART_UIP */
#define MCF_UART_UIP_CTS                     (0x1)

/* Bit definitions and macros for MCF_UART_UOP1 */
#define MCF_UART_UOP1_RTS                    (0x1)

/* Bit definitions and macros for MCF_UART_UOP0 */
#define MCF_UART_UOP0_RTS                    (0x1)


#endif /* __MCF52235_UART_H__ */
