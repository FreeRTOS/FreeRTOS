/* Coldfire C Header File
 * Copyright Freescale Semiconductor Inc
 * All rights reserved.
 *
 * 2007/03/19 Revision: 0.9
 */

#ifndef __MCF5282_GPIO_H__
#define __MCF5282_GPIO_H__


/*********************************************************************
*
* General Purpose I/O (GPIO)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_GPIO_PORTA                       (*(vuint8 *)(&__IPSBAR[0x100000]))
#define MCF_GPIO_DDRA                        (*(vuint8 *)(&__IPSBAR[0x100014]))
#define MCF_GPIO_SETA                        (*(vuint8 *)(&__IPSBAR[0x100028]))
#define MCF_GPIO_CLRA                        (*(vuint8 *)(&__IPSBAR[0x10003C]))

#define MCF_GPIO_PORTB                       (*(vuint8 *)(&__IPSBAR[0x100001]))
#define MCF_GPIO_DDRB                        (*(vuint8 *)(&__IPSBAR[0x100015]))
#define MCF_GPIO_SETB                        (*(vuint8 *)(&__IPSBAR[0x100029]))
#define MCF_GPIO_CLRB                        (*(vuint8 *)(&__IPSBAR[0x10003D]))

#define MCF_GPIO_PORTC                       (*(vuint8 *)(&__IPSBAR[0x100002]))
#define MCF_GPIO_DDRC                        (*(vuint8 *)(&__IPSBAR[0x100016]))
#define MCF_GPIO_SETC                        (*(vuint8 *)(&__IPSBAR[0x10002A]))
#define MCF_GPIO_CLRC                        (*(vuint8 *)(&__IPSBAR[0x10003E]))

#define MCF_GPIO_PORTD                       (*(vuint8 *)(&__IPSBAR[0x100003]))
#define MCF_GPIO_DDRD                        (*(vuint8 *)(&__IPSBAR[0x100017]))
#define MCF_GPIO_SETD                        (*(vuint8 *)(&__IPSBAR[0x10002B]))
#define MCF_GPIO_CLRD                        (*(vuint8 *)(&__IPSBAR[0x10003F]))

#define MCF_GPIO_PORTE                       (*(vuint8 *)(&__IPSBAR[0x100004]))
#define MCF_GPIO_DDRE                        (*(vuint8 *)(&__IPSBAR[0x100018]))
#define MCF_GPIO_SETE                        (*(vuint8 *)(&__IPSBAR[0x10002C]))
#define MCF_GPIO_CLRE                        (*(vuint8 *)(&__IPSBAR[0x100040]))

#define MCF_GPIO_PORTF                       (*(vuint8 *)(&__IPSBAR[0x100005]))
#define MCF_GPIO_DDRF                        (*(vuint8 *)(&__IPSBAR[0x100019]))
#define MCF_GPIO_SETF                        (*(vuint8 *)(&__IPSBAR[0x10002D]))
#define MCF_GPIO_CLRF                        (*(vuint8 *)(&__IPSBAR[0x100041]))

#define MCF_GPIO_PORTG                       (*(vuint8 *)(&__IPSBAR[0x100006]))
#define MCF_GPIO_DDRG                        (*(vuint8 *)(&__IPSBAR[0x10001A]))
#define MCF_GPIO_SETG                        (*(vuint8 *)(&__IPSBAR[0x10002E]))
#define MCF_GPIO_CLRG                        (*(vuint8 *)(&__IPSBAR[0x100042]))

#define MCF_GPIO_PORTH                       (*(vuint8 *)(&__IPSBAR[0x100007]))
#define MCF_GPIO_DDRH                        (*(vuint8 *)(&__IPSBAR[0x10001B]))
#define MCF_GPIO_SETH                        (*(vuint8 *)(&__IPSBAR[0x10002F]))
#define MCF_GPIO_CLRH                        (*(vuint8 *)(&__IPSBAR[0x100043]))

#define MCF_GPIO_PORTJ                       (*(vuint8 *)(&__IPSBAR[0x100008]))
#define MCF_GPIO_DDRJ                        (*(vuint8 *)(&__IPSBAR[0x10001C]))
#define MCF_GPIO_SETJ                        (*(vuint8 *)(&__IPSBAR[0x100030]))
#define MCF_GPIO_CLRJ                        (*(vuint8 *)(&__IPSBAR[0x100044]))

#define MCF_GPIO_PORTDD                      (*(vuint8 *)(&__IPSBAR[0x100009]))
#define MCF_GPIO_DDRDD                       (*(vuint8 *)(&__IPSBAR[0x10001D]))
#define MCF_GPIO_SETDD                       (*(vuint8 *)(&__IPSBAR[0x100031]))
#define MCF_GPIO_CLRDD                       (*(vuint8 *)(&__IPSBAR[0x100045]))

#define MCF_GPIO_PORTEH                      (*(vuint8 *)(&__IPSBAR[0x10000A]))
#define MCF_GPIO_DDREH                       (*(vuint8 *)(&__IPSBAR[0x10001E]))
#define MCF_GPIO_SETEH                       (*(vuint8 *)(&__IPSBAR[0x100032]))
#define MCF_GPIO_CLREH                       (*(vuint8 *)(&__IPSBAR[0x100046]))

#define MCF_GPIO_PORTEL                      (*(vuint8 *)(&__IPSBAR[0x10000B]))
#define MCF_GPIO_DDREL                       (*(vuint8 *)(&__IPSBAR[0x10001F]))
#define MCF_GPIO_SETEL                       (*(vuint8 *)(&__IPSBAR[0x100033]))
#define MCF_GPIO_CLREL                       (*(vuint8 *)(&__IPSBAR[0x100047]))

#define MCF_GPIO_PORTAS                      (*(vuint8 *)(&__IPSBAR[0x10000C]))
#define MCF_GPIO_DDRAS                       (*(vuint8 *)(&__IPSBAR[0x100020]))
#define MCF_GPIO_SETAS                       (*(vuint8 *)(&__IPSBAR[0x100034]))
#define MCF_GPIO_CLRAS                       (*(vuint8 *)(&__IPSBAR[0x100048]))

#define MCF_GPIO_PORTQS                      (*(vuint8 *)(&__IPSBAR[0x10000D]))
#define MCF_GPIO_DDRQS                       (*(vuint8 *)(&__IPSBAR[0x100021]))
#define MCF_GPIO_SETQS                       (*(vuint8 *)(&__IPSBAR[0x100035]))
#define MCF_GPIO_CLRQS                       (*(vuint8 *)(&__IPSBAR[0x100049]))

#define MCF_GPIO_PORTSD                      (*(vuint8 *)(&__IPSBAR[0x10000E]))
#define MCF_GPIO_DDRSD                       (*(vuint8 *)(&__IPSBAR[0x100022]))
#define MCF_GPIO_SETSD                       (*(vuint8 *)(&__IPSBAR[0x100036]))
#define MCF_GPIO_CLRSD                       (*(vuint8 *)(&__IPSBAR[0x10004A]))

#define MCF_GPIO_PORTTC                      (*(vuint8 *)(&__IPSBAR[0x10000F]))
#define MCF_GPIO_DDRTC                       (*(vuint8 *)(&__IPSBAR[0x100023]))
#define MCF_GPIO_SETTC                       (*(vuint8 *)(&__IPSBAR[0x100037]))
#define MCF_GPIO_CLRTC                       (*(vuint8 *)(&__IPSBAR[0x10004B]))

#define MCF_GPIO_PORTTD                      (*(vuint8 *)(&__IPSBAR[0x100010]))
#define MCF_GPIO_DDRTD                       (*(vuint8 *)(&__IPSBAR[0x100024]))
#define MCF_GPIO_SETTD                       (*(vuint8 *)(&__IPSBAR[0x100038]))
#define MCF_GPIO_CLRTD                       (*(vuint8 *)(&__IPSBAR[0x10004C]))

#define MCF_GPIO_PORTUA                      (*(vuint8 *)(&__IPSBAR[0x100011]))
#define MCF_GPIO_DDRUA                       (*(vuint8 *)(&__IPSBAR[0x100025]))
#define MCF_GPIO_SETUA                       (*(vuint8 *)(&__IPSBAR[0x100039]))
#define MCF_GPIO_CLRUA                       (*(vuint8 *)(&__IPSBAR[0x10004D]))



/* Bit definitions and macros for MCF_GPIO_PORTA */
#define MCF_GPIO_PORTA_PORTA0                (0x1)
#define MCF_GPIO_PORTA_PORTA1                (0x2)
#define MCF_GPIO_PORTA_PORTA2                (0x4)
#define MCF_GPIO_PORTA_PORTA3                (0x8)
#define MCF_GPIO_PORTA_PORTA4                (0x10)
#define MCF_GPIO_PORTA_PORTA5                (0x20)
#define MCF_GPIO_PORTA_PORTA6                (0x40)
#define MCF_GPIO_PORTA_PORTA7                (0x80)

/* Bit definitions and macros for MCF_GPIO_DDRA */
#define MCF_GPIO_DDRA_DDRA0                  (0x1)
#define MCF_GPIO_DDRA_DDRA1                  (0x2)
#define MCF_GPIO_DDRA_DDRA2                  (0x4)
#define MCF_GPIO_DDRA_DDRA3                  (0x8)
#define MCF_GPIO_DDRA_DDRA4                  (0x10)
#define MCF_GPIO_DDRA_DDRA5                  (0x20)
#define MCF_GPIO_DDRA_DDRA6                  (0x40)
#define MCF_GPIO_DDRA_DDRA7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_SETA */
#define MCF_GPIO_SETA_SETA0                  (0x1)
#define MCF_GPIO_SETA_SETA1                  (0x2)
#define MCF_GPIO_SETA_SETA2                  (0x4)
#define MCF_GPIO_SETA_SETA3                  (0x8)
#define MCF_GPIO_SETA_SETA4                  (0x10)
#define MCF_GPIO_SETA_SETA5                  (0x20)
#define MCF_GPIO_SETA_SETA6                  (0x40)
#define MCF_GPIO_SETA_SETA7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_CLRA */
#define MCF_GPIO_CLRA_CLRA0                  (0x1)
#define MCF_GPIO_CLRA_CLRA1                  (0x2)
#define MCF_GPIO_CLRA_CLRA2                  (0x4)
#define MCF_GPIO_CLRA_CLRA3                  (0x8)
#define MCF_GPIO_CLRA_CLRA4                  (0x10)
#define MCF_GPIO_CLRA_CLRA5                  (0x20)
#define MCF_GPIO_CLRA_CLRA6                  (0x40)
#define MCF_GPIO_CLRA_CLRA7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_PORTB */
#define MCF_GPIO_PORTB_PORTB0                (0x1)
#define MCF_GPIO_PORTB_PORTB1                (0x2)
#define MCF_GPIO_PORTB_PORTB2                (0x4)
#define MCF_GPIO_PORTB_PORTB3                (0x8)
#define MCF_GPIO_PORTB_PORTB4                (0x10)
#define MCF_GPIO_PORTB_PORTB5                (0x20)
#define MCF_GPIO_PORTB_PORTB6                (0x40)
#define MCF_GPIO_PORTB_PORTB7                (0x80)

/* Bit definitions and macros for MCF_GPIO_DDRB */
#define MCF_GPIO_DDRB_DDRB0                  (0x1)
#define MCF_GPIO_DDRB_DDRB1                  (0x2)
#define MCF_GPIO_DDRB_DDRB2                  (0x4)
#define MCF_GPIO_DDRB_DDRB3                  (0x8)
#define MCF_GPIO_DDRB_DDRB4                  (0x10)
#define MCF_GPIO_DDRB_DDRB5                  (0x20)
#define MCF_GPIO_DDRB_DDRB6                  (0x40)
#define MCF_GPIO_DDRB_DDRB7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_SETB */
#define MCF_GPIO_SETB_SETB0                  (0x1)
#define MCF_GPIO_SETB_SETB1                  (0x2)
#define MCF_GPIO_SETB_SETB2                  (0x4)
#define MCF_GPIO_SETB_SETB3                  (0x8)
#define MCF_GPIO_SETB_SETB4                  (0x10)
#define MCF_GPIO_SETB_SETB5                  (0x20)
#define MCF_GPIO_SETB_SETB6                  (0x40)
#define MCF_GPIO_SETB_SETB7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_CLRB */
#define MCF_GPIO_CLRB_CLRB0                  (0x1)
#define MCF_GPIO_CLRB_CLRB1                  (0x2)
#define MCF_GPIO_CLRB_CLRB2                  (0x4)
#define MCF_GPIO_CLRB_CLRB3                  (0x8)
#define MCF_GPIO_CLRB_CLRB4                  (0x10)
#define MCF_GPIO_CLRB_CLRB5                  (0x20)
#define MCF_GPIO_CLRB_CLRB6                  (0x40)
#define MCF_GPIO_CLRB_CLRB7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_PORTC */
#define MCF_GPIO_PORTC_PORTC0                (0x1)
#define MCF_GPIO_PORTC_PORTC1                (0x2)
#define MCF_GPIO_PORTC_PORTC2                (0x4)
#define MCF_GPIO_PORTC_PORTC3                (0x8)
#define MCF_GPIO_PORTC_PORTC4                (0x10)
#define MCF_GPIO_PORTC_PORTC5                (0x20)
#define MCF_GPIO_PORTC_PORTC6                (0x40)
#define MCF_GPIO_PORTC_PORTC7                (0x80)

/* Bit definitions and macros for MCF_GPIO_DDRC */
#define MCF_GPIO_DDRC_DDRC0                  (0x1)
#define MCF_GPIO_DDRC_DDRC1                  (0x2)
#define MCF_GPIO_DDRC_DDRC2                  (0x4)
#define MCF_GPIO_DDRC_DDRC3                  (0x8)
#define MCF_GPIO_DDRC_DDRC4                  (0x10)
#define MCF_GPIO_DDRC_DDRC5                  (0x20)
#define MCF_GPIO_DDRC_DDRC6                  (0x40)
#define MCF_GPIO_DDRC_DDRC7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_SETC */
#define MCF_GPIO_SETC_SETC0                  (0x1)
#define MCF_GPIO_SETC_SETC1                  (0x2)
#define MCF_GPIO_SETC_SETC2                  (0x4)
#define MCF_GPIO_SETC_SETC3                  (0x8)
#define MCF_GPIO_SETC_SETC4                  (0x10)
#define MCF_GPIO_SETC_SETC5                  (0x20)
#define MCF_GPIO_SETC_SETC6                  (0x40)
#define MCF_GPIO_SETC_SETC7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_CLRC */
#define MCF_GPIO_CLRC_CLRC0                  (0x1)
#define MCF_GPIO_CLRC_CLRC1                  (0x2)
#define MCF_GPIO_CLRC_CLRC2                  (0x4)
#define MCF_GPIO_CLRC_CLRC3                  (0x8)
#define MCF_GPIO_CLRC_CLRC4                  (0x10)
#define MCF_GPIO_CLRC_CLRC5                  (0x20)
#define MCF_GPIO_CLRC_CLRC6                  (0x40)
#define MCF_GPIO_CLRC_CLRC7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_PORTD */
#define MCF_GPIO_PORTD_PORTD0                (0x1)
#define MCF_GPIO_PORTD_PORTD1                (0x2)
#define MCF_GPIO_PORTD_PORTD2                (0x4)
#define MCF_GPIO_PORTD_PORTD3                (0x8)
#define MCF_GPIO_PORTD_PORTD4                (0x10)
#define MCF_GPIO_PORTD_PORTD5                (0x20)
#define MCF_GPIO_PORTD_PORTD6                (0x40)
#define MCF_GPIO_PORTD_PORTD7                (0x80)

/* Bit definitions and macros for MCF_GPIO_DDRD */
#define MCF_GPIO_DDRD_DDRD0                  (0x1)
#define MCF_GPIO_DDRD_DDRD1                  (0x2)
#define MCF_GPIO_DDRD_DDRD2                  (0x4)
#define MCF_GPIO_DDRD_DDRD3                  (0x8)
#define MCF_GPIO_DDRD_DDRD4                  (0x10)
#define MCF_GPIO_DDRD_DDRD5                  (0x20)
#define MCF_GPIO_DDRD_DDRD6                  (0x40)
#define MCF_GPIO_DDRD_DDRD7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_SETD */
#define MCF_GPIO_SETD_SETD0                  (0x1)
#define MCF_GPIO_SETD_SETD1                  (0x2)
#define MCF_GPIO_SETD_SETD2                  (0x4)
#define MCF_GPIO_SETD_SETD3                  (0x8)
#define MCF_GPIO_SETD_SETD4                  (0x10)
#define MCF_GPIO_SETD_SETD5                  (0x20)
#define MCF_GPIO_SETD_SETD6                  (0x40)
#define MCF_GPIO_SETD_SETD7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_CLRD */
#define MCF_GPIO_CLRD_CLRD0                  (0x1)
#define MCF_GPIO_CLRD_CLRD1                  (0x2)
#define MCF_GPIO_CLRD_CLRD2                  (0x4)
#define MCF_GPIO_CLRD_CLRD3                  (0x8)
#define MCF_GPIO_CLRD_CLRD4                  (0x10)
#define MCF_GPIO_CLRD_CLRD5                  (0x20)
#define MCF_GPIO_CLRD_CLRD6                  (0x40)
#define MCF_GPIO_CLRD_CLRD7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_PORTE */
#define MCF_GPIO_PORTE_PORTE0                (0x1)
#define MCF_GPIO_PORTE_PORTE1                (0x2)
#define MCF_GPIO_PORTE_PORTE2                (0x4)
#define MCF_GPIO_PORTE_PORTE3                (0x8)
#define MCF_GPIO_PORTE_PORTE4                (0x10)
#define MCF_GPIO_PORTE_PORTE5                (0x20)
#define MCF_GPIO_PORTE_PORTE6                (0x40)
#define MCF_GPIO_PORTE_PORTE7                (0x80)

/* Bit definitions and macros for MCF_GPIO_DDRE */
#define MCF_GPIO_DDRE_DDRE0                  (0x1)
#define MCF_GPIO_DDRE_DDRE1                  (0x2)
#define MCF_GPIO_DDRE_DDRE2                  (0x4)
#define MCF_GPIO_DDRE_DDRE3                  (0x8)
#define MCF_GPIO_DDRE_DDRE4                  (0x10)
#define MCF_GPIO_DDRE_DDRE5                  (0x20)
#define MCF_GPIO_DDRE_DDRE6                  (0x40)
#define MCF_GPIO_DDRE_DDRE7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_SETE */
#define MCF_GPIO_SETE_SETE0                  (0x1)
#define MCF_GPIO_SETE_SETE1                  (0x2)
#define MCF_GPIO_SETE_SETE2                  (0x4)
#define MCF_GPIO_SETE_SETE3                  (0x8)
#define MCF_GPIO_SETE_SETE4                  (0x10)
#define MCF_GPIO_SETE_SETE5                  (0x20)
#define MCF_GPIO_SETE_SETE6                  (0x40)
#define MCF_GPIO_SETE_SETE7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_CLRE */
#define MCF_GPIO_CLRE_CLRE0                  (0x1)
#define MCF_GPIO_CLRE_CLRE1                  (0x2)
#define MCF_GPIO_CLRE_CLRE2                  (0x4)
#define MCF_GPIO_CLRE_CLRE3                  (0x8)
#define MCF_GPIO_CLRE_CLRE4                  (0x10)
#define MCF_GPIO_CLRE_CLRE5                  (0x20)
#define MCF_GPIO_CLRE_CLRE6                  (0x40)
#define MCF_GPIO_CLRE_CLRE7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_PORTF */
#define MCF_GPIO_PORTF_PORTF0                (0x1)
#define MCF_GPIO_PORTF_PORTF1                (0x2)
#define MCF_GPIO_PORTF_PORTF2                (0x4)
#define MCF_GPIO_PORTF_PORTF3                (0x8)
#define MCF_GPIO_PORTF_PORTF4                (0x10)
#define MCF_GPIO_PORTF_PORTF5                (0x20)
#define MCF_GPIO_PORTF_PORTF6                (0x40)
#define MCF_GPIO_PORTF_PORTF7                (0x80)

/* Bit definitions and macros for MCF_GPIO_DDRF */
#define MCF_GPIO_DDRF_DDRF0                  (0x1)
#define MCF_GPIO_DDRF_DDRF1                  (0x2)
#define MCF_GPIO_DDRF_DDRF2                  (0x4)
#define MCF_GPIO_DDRF_DDRF3                  (0x8)
#define MCF_GPIO_DDRF_DDRF4                  (0x10)
#define MCF_GPIO_DDRF_DDRF5                  (0x20)
#define MCF_GPIO_DDRF_DDRF6                  (0x40)
#define MCF_GPIO_DDRF_DDRF7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_SETF */
#define MCF_GPIO_SETF_SETF0                  (0x1)
#define MCF_GPIO_SETF_SETF1                  (0x2)
#define MCF_GPIO_SETF_SETF2                  (0x4)
#define MCF_GPIO_SETF_SETF3                  (0x8)
#define MCF_GPIO_SETF_SETF4                  (0x10)
#define MCF_GPIO_SETF_SETF5                  (0x20)
#define MCF_GPIO_SETF_SETF6                  (0x40)
#define MCF_GPIO_SETF_SETF7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_CLRF */
#define MCF_GPIO_CLRF_CLRF0                  (0x1)
#define MCF_GPIO_CLRF_CLRF1                  (0x2)
#define MCF_GPIO_CLRF_CLRF2                  (0x4)
#define MCF_GPIO_CLRF_CLRF3                  (0x8)
#define MCF_GPIO_CLRF_CLRF4                  (0x10)
#define MCF_GPIO_CLRF_CLRF5                  (0x20)
#define MCF_GPIO_CLRF_CLRF6                  (0x40)
#define MCF_GPIO_CLRF_CLRF7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_PORTG */
#define MCF_GPIO_PORTG_PORTG0                (0x1)
#define MCF_GPIO_PORTG_PORTG1                (0x2)
#define MCF_GPIO_PORTG_PORTG2                (0x4)
#define MCF_GPIO_PORTG_PORTG3                (0x8)
#define MCF_GPIO_PORTG_PORTG4                (0x10)
#define MCF_GPIO_PORTG_PORTG5                (0x20)
#define MCF_GPIO_PORTG_PORTG6                (0x40)
#define MCF_GPIO_PORTG_PORTG7                (0x80)

/* Bit definitions and macros for MCF_GPIO_DDRG */
#define MCF_GPIO_DDRG_DDRG0                  (0x1)
#define MCF_GPIO_DDRG_DDRG1                  (0x2)
#define MCF_GPIO_DDRG_DDRG2                  (0x4)
#define MCF_GPIO_DDRG_DDRG3                  (0x8)
#define MCF_GPIO_DDRG_DDRG4                  (0x10)
#define MCF_GPIO_DDRG_DDRG5                  (0x20)
#define MCF_GPIO_DDRG_DDRG6                  (0x40)
#define MCF_GPIO_DDRG_DDRG7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_SETG */
#define MCF_GPIO_SETG_SETG0                  (0x1)
#define MCF_GPIO_SETG_SETG1                  (0x2)
#define MCF_GPIO_SETG_SETG2                  (0x4)
#define MCF_GPIO_SETG_SETG3                  (0x8)
#define MCF_GPIO_SETG_SETG4                  (0x10)
#define MCF_GPIO_SETG_SETG5                  (0x20)
#define MCF_GPIO_SETG_SETG6                  (0x40)
#define MCF_GPIO_SETG_SETG7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_CLRG */
#define MCF_GPIO_CLRG_CLRG0                  (0x1)
#define MCF_GPIO_CLRG_CLRG1                  (0x2)
#define MCF_GPIO_CLRG_CLRG2                  (0x4)
#define MCF_GPIO_CLRG_CLRG3                  (0x8)
#define MCF_GPIO_CLRG_CLRG4                  (0x10)
#define MCF_GPIO_CLRG_CLRG5                  (0x20)
#define MCF_GPIO_CLRG_CLRG6                  (0x40)
#define MCF_GPIO_CLRG_CLRG7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_PORTH */
#define MCF_GPIO_PORTH_PORTH0                (0x1)
#define MCF_GPIO_PORTH_PORTH1                (0x2)
#define MCF_GPIO_PORTH_PORTH2                (0x4)
#define MCF_GPIO_PORTH_PORTH3                (0x8)
#define MCF_GPIO_PORTH_PORTH4                (0x10)
#define MCF_GPIO_PORTH_PORTH5                (0x20)
#define MCF_GPIO_PORTH_PORTH6                (0x40)
#define MCF_GPIO_PORTH_PORTH7                (0x80)

/* Bit definitions and macros for MCF_GPIO_DDRH */
#define MCF_GPIO_DDRH_DDRH0                  (0x1)
#define MCF_GPIO_DDRH_DDRH1                  (0x2)
#define MCF_GPIO_DDRH_DDRH2                  (0x4)
#define MCF_GPIO_DDRH_DDRH3                  (0x8)
#define MCF_GPIO_DDRH_DDRH4                  (0x10)
#define MCF_GPIO_DDRH_DDRH5                  (0x20)
#define MCF_GPIO_DDRH_DDRH6                  (0x40)
#define MCF_GPIO_DDRH_DDRH7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_SETH */
#define MCF_GPIO_SETH_SETH0                  (0x1)
#define MCF_GPIO_SETH_SETH1                  (0x2)
#define MCF_GPIO_SETH_SETH2                  (0x4)
#define MCF_GPIO_SETH_SETH3                  (0x8)
#define MCF_GPIO_SETH_SETH4                  (0x10)
#define MCF_GPIO_SETH_SETH5                  (0x20)
#define MCF_GPIO_SETH_SETH6                  (0x40)
#define MCF_GPIO_SETH_SETH7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_CLRH */
#define MCF_GPIO_CLRH_CLRH0                  (0x1)
#define MCF_GPIO_CLRH_CLRH1                  (0x2)
#define MCF_GPIO_CLRH_CLRH2                  (0x4)
#define MCF_GPIO_CLRH_CLRH3                  (0x8)
#define MCF_GPIO_CLRH_CLRH4                  (0x10)
#define MCF_GPIO_CLRH_CLRH5                  (0x20)
#define MCF_GPIO_CLRH_CLRH6                  (0x40)
#define MCF_GPIO_CLRH_CLRH7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_PORTJ */
#define MCF_GPIO_PORTJ_PORTJ0                (0x1)
#define MCF_GPIO_PORTJ_PORTJ1                (0x2)
#define MCF_GPIO_PORTJ_PORTJ2                (0x4)
#define MCF_GPIO_PORTJ_PORTJ3                (0x8)
#define MCF_GPIO_PORTJ_PORTJ4                (0x10)
#define MCF_GPIO_PORTJ_PORTJ5                (0x20)
#define MCF_GPIO_PORTJ_PORTJ6                (0x40)
#define MCF_GPIO_PORTJ_PORTJ7                (0x80)

/* Bit definitions and macros for MCF_GPIO_DDRJ */
#define MCF_GPIO_DDRJ_DDRJ0                  (0x1)
#define MCF_GPIO_DDRJ_DDRJ1                  (0x2)
#define MCF_GPIO_DDRJ_DDRJ2                  (0x4)
#define MCF_GPIO_DDRJ_DDRJ3                  (0x8)
#define MCF_GPIO_DDRJ_DDRJ4                  (0x10)
#define MCF_GPIO_DDRJ_DDRJ5                  (0x20)
#define MCF_GPIO_DDRJ_DDRJ6                  (0x40)
#define MCF_GPIO_DDRJ_DDRJ7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_SETJ */
#define MCF_GPIO_SETJ_SETJ0                  (0x1)
#define MCF_GPIO_SETJ_SETJ1                  (0x2)
#define MCF_GPIO_SETJ_SETJ2                  (0x4)
#define MCF_GPIO_SETJ_SETJ3                  (0x8)
#define MCF_GPIO_SETJ_SETJ4                  (0x10)
#define MCF_GPIO_SETJ_SETJ5                  (0x20)
#define MCF_GPIO_SETJ_SETJ6                  (0x40)
#define MCF_GPIO_SETJ_SETJ7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_CLRJ */
#define MCF_GPIO_CLRJ_CLRJ0                  (0x1)
#define MCF_GPIO_CLRJ_CLRJ1                  (0x2)
#define MCF_GPIO_CLRJ_CLRJ2                  (0x4)
#define MCF_GPIO_CLRJ_CLRJ3                  (0x8)
#define MCF_GPIO_CLRJ_CLRJ4                  (0x10)
#define MCF_GPIO_CLRJ_CLRJ5                  (0x20)
#define MCF_GPIO_CLRJ_CLRJ6                  (0x40)
#define MCF_GPIO_CLRJ_CLRJ7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_PORTDD */
#define MCF_GPIO_PORTDD_PORTDD0              (0x1)
#define MCF_GPIO_PORTDD_PORTDD1              (0x2)
#define MCF_GPIO_PORTDD_PORTDD2              (0x4)
#define MCF_GPIO_PORTDD_PORTDD3              (0x8)
#define MCF_GPIO_PORTDD_PORTDD4              (0x10)
#define MCF_GPIO_PORTDD_PORTDD5              (0x20)
#define MCF_GPIO_PORTDD_PORTDD6              (0x40)
#define MCF_GPIO_PORTDD_PORTDD7              (0x80)

/* Bit definitions and macros for MCF_GPIO_DDRDD */
#define MCF_GPIO_DDRDD_DDRDD0                (0x1)
#define MCF_GPIO_DDRDD_DDRDD1                (0x2)
#define MCF_GPIO_DDRDD_DDRDD2                (0x4)
#define MCF_GPIO_DDRDD_DDRDD3                (0x8)
#define MCF_GPIO_DDRDD_DDRDD4                (0x10)
#define MCF_GPIO_DDRDD_DDRDD5                (0x20)
#define MCF_GPIO_DDRDD_DDRDD6                (0x40)
#define MCF_GPIO_DDRDD_DDRDD7                (0x80)

/* Bit definitions and macros for MCF_GPIO_SETDD */
#define MCF_GPIO_SETDD_SETDD0                (0x1)
#define MCF_GPIO_SETDD_SETDD1                (0x2)
#define MCF_GPIO_SETDD_SETDD2                (0x4)
#define MCF_GPIO_SETDD_SETDD3                (0x8)
#define MCF_GPIO_SETDD_SETDD4                (0x10)
#define MCF_GPIO_SETDD_SETDD5                (0x20)
#define MCF_GPIO_SETDD_SETDD6                (0x40)
#define MCF_GPIO_SETDD_SETDD7                (0x80)

/* Bit definitions and macros for MCF_GPIO_CLRDD */
#define MCF_GPIO_CLRDD_CLRDD0                (0x1)
#define MCF_GPIO_CLRDD_CLRDD1                (0x2)
#define MCF_GPIO_CLRDD_CLRDD2                (0x4)
#define MCF_GPIO_CLRDD_CLRDD3                (0x8)
#define MCF_GPIO_CLRDD_CLRDD4                (0x10)
#define MCF_GPIO_CLRDD_CLRDD5                (0x20)
#define MCF_GPIO_CLRDD_CLRDD6                (0x40)
#define MCF_GPIO_CLRDD_CLRDD7                (0x80)

/* Bit definitions and macros for MCF_GPIO_PORTEH */
#define MCF_GPIO_PORTEH_PORTEH0              (0x1)
#define MCF_GPIO_PORTEH_PORTEH1              (0x2)
#define MCF_GPIO_PORTEH_PORTEH2              (0x4)
#define MCF_GPIO_PORTEH_PORTEH3              (0x8)
#define MCF_GPIO_PORTEH_PORTEH4              (0x10)
#define MCF_GPIO_PORTEH_PORTEH5              (0x20)
#define MCF_GPIO_PORTEH_PORTEH6              (0x40)
#define MCF_GPIO_PORTEH_PORTEH7              (0x80)

/* Bit definitions and macros for MCF_GPIO_DDREH */
#define MCF_GPIO_DDREH_DDREH0                (0x1)
#define MCF_GPIO_DDREH_DDREH1                (0x2)
#define MCF_GPIO_DDREH_DDREH2                (0x4)
#define MCF_GPIO_DDREH_DDREH3                (0x8)
#define MCF_GPIO_DDREH_DDREH4                (0x10)
#define MCF_GPIO_DDREH_DDREH5                (0x20)
#define MCF_GPIO_DDREH_DDREH6                (0x40)
#define MCF_GPIO_DDREH_DDREH7                (0x80)

/* Bit definitions and macros for MCF_GPIO_SETEH */
#define MCF_GPIO_SETEH_SETEH0                (0x1)
#define MCF_GPIO_SETEH_SETEH1                (0x2)
#define MCF_GPIO_SETEH_SETEH2                (0x4)
#define MCF_GPIO_SETEH_SETEH3                (0x8)
#define MCF_GPIO_SETEH_SETEH4                (0x10)
#define MCF_GPIO_SETEH_SETEH5                (0x20)
#define MCF_GPIO_SETEH_SETEH6                (0x40)
#define MCF_GPIO_SETEH_SETEH7                (0x80)

/* Bit definitions and macros for MCF_GPIO_CLREH */
#define MCF_GPIO_CLREH_CLREH0                (0x1)
#define MCF_GPIO_CLREH_CLREH1                (0x2)
#define MCF_GPIO_CLREH_CLREH2                (0x4)
#define MCF_GPIO_CLREH_CLREH3                (0x8)
#define MCF_GPIO_CLREH_CLREH4                (0x10)
#define MCF_GPIO_CLREH_CLREH5                (0x20)
#define MCF_GPIO_CLREH_CLREH6                (0x40)
#define MCF_GPIO_CLREH_CLREH7                (0x80)

/* Bit definitions and macros for MCF_GPIO_PORTEL */
#define MCF_GPIO_PORTEL_PORTEL0              (0x1)
#define MCF_GPIO_PORTEL_PORTEL1              (0x2)
#define MCF_GPIO_PORTEL_PORTEL2              (0x4)
#define MCF_GPIO_PORTEL_PORTEL3              (0x8)
#define MCF_GPIO_PORTEL_PORTEL4              (0x10)
#define MCF_GPIO_PORTEL_PORTEL5              (0x20)
#define MCF_GPIO_PORTEL_PORTEL6              (0x40)
#define MCF_GPIO_PORTEL_PORTEL7              (0x80)

/* Bit definitions and macros for MCF_GPIO_DDREL */
#define MCF_GPIO_DDREL_DDREL0                (0x1)
#define MCF_GPIO_DDREL_DDREL1                (0x2)
#define MCF_GPIO_DDREL_DDREL2                (0x4)
#define MCF_GPIO_DDREL_DDREL3                (0x8)
#define MCF_GPIO_DDREL_DDREL4                (0x10)
#define MCF_GPIO_DDREL_DDREL5                (0x20)
#define MCF_GPIO_DDREL_DDREL6                (0x40)
#define MCF_GPIO_DDREL_DDREL7                (0x80)

/* Bit definitions and macros for MCF_GPIO_SETEL */
#define MCF_GPIO_SETEL_SETEL0                (0x1)
#define MCF_GPIO_SETEL_SETEL1                (0x2)
#define MCF_GPIO_SETEL_SETEL2                (0x4)
#define MCF_GPIO_SETEL_SETEL3                (0x8)
#define MCF_GPIO_SETEL_SETEL4                (0x10)
#define MCF_GPIO_SETEL_SETEL5                (0x20)
#define MCF_GPIO_SETEL_SETEL6                (0x40)
#define MCF_GPIO_SETEL_SETEL7                (0x80)

/* Bit definitions and macros for MCF_GPIO_CLREL */
#define MCF_GPIO_CLREL_CLREL0                (0x1)
#define MCF_GPIO_CLREL_CLREL1                (0x2)
#define MCF_GPIO_CLREL_CLREL2                (0x4)
#define MCF_GPIO_CLREL_CLREL3                (0x8)
#define MCF_GPIO_CLREL_CLREL4                (0x10)
#define MCF_GPIO_CLREL_CLREL5                (0x20)
#define MCF_GPIO_CLREL_CLREL6                (0x40)
#define MCF_GPIO_CLREL_CLREL7                (0x80)

/* Bit definitions and macros for MCF_GPIO_PORTAS */
#define MCF_GPIO_PORTAS_PORTAS0              (0x1)
#define MCF_GPIO_PORTAS_PORTAS1              (0x2)
#define MCF_GPIO_PORTAS_PORTAS2              (0x4)
#define MCF_GPIO_PORTAS_PORTAS3              (0x8)
#define MCF_GPIO_PORTAS_PORTAS4              (0x10)
#define MCF_GPIO_PORTAS_PORTAS5              (0x20)

/* Bit definitions and macros for MCF_GPIO_DDRAS */
#define MCF_GPIO_DDRAS_DDRAS0                (0x1)
#define MCF_GPIO_DDRAS_DDRAS1                (0x2)
#define MCF_GPIO_DDRAS_DDRAS2                (0x4)
#define MCF_GPIO_DDRAS_DDRAS3                (0x8)
#define MCF_GPIO_DDRAS_DDRAS4                (0x10)
#define MCF_GPIO_DDRAS_DDRAS5                (0x20)

/* Bit definitions and macros for MCF_GPIO_SETAS */
#define MCF_GPIO_SETAS_SETAS0                (0x1)
#define MCF_GPIO_SETAS_SETAS1                (0x2)
#define MCF_GPIO_SETAS_SETAS2                (0x4)
#define MCF_GPIO_SETAS_SETAS3                (0x8)
#define MCF_GPIO_SETAS_SETAS4                (0x10)
#define MCF_GPIO_SETAS_SETAS5                (0x20)

/* Bit definitions and macros for MCF_GPIO_CLRAS */
#define MCF_GPIO_CLRAS_CLRAS0                (0x1)
#define MCF_GPIO_CLRAS_CLRAS1                (0x2)
#define MCF_GPIO_CLRAS_CLRAS2                (0x4)
#define MCF_GPIO_CLRAS_CLRAS3                (0x8)
#define MCF_GPIO_CLRAS_CLRAS4                (0x10)
#define MCF_GPIO_CLRAS_CLRAS5                (0x20)

/* Bit definitions and macros for MCF_GPIO_PORTQS */
#define MCF_GPIO_PORTQS_PORTQS0              (0x1)
#define MCF_GPIO_PORTQS_PORTQS1              (0x2)
#define MCF_GPIO_PORTQS_PORTQS2              (0x4)
#define MCF_GPIO_PORTQS_PORTQS3              (0x8)
#define MCF_GPIO_PORTQS_PORTQS4              (0x10)
#define MCF_GPIO_PORTQS_PORTQS5              (0x20)
#define MCF_GPIO_PORTQS_PORTQS6              (0x40)

/* Bit definitions and macros for MCF_GPIO_DDRQS */
#define MCF_GPIO_DDRQS_DDRQS0                (0x1)
#define MCF_GPIO_DDRQS_DDRQS1                (0x2)
#define MCF_GPIO_DDRQS_DDRQS2                (0x4)
#define MCF_GPIO_DDRQS_DDRQS3                (0x8)
#define MCF_GPIO_DDRQS_DDRQS4                (0x10)
#define MCF_GPIO_DDRQS_DDRQS5                (0x20)
#define MCF_GPIO_DDRQS_DDRQS6                (0x40)

/* Bit definitions and macros for MCF_GPIO_SETQS */
#define MCF_GPIO_SETQS_SETQS0                (0x1)
#define MCF_GPIO_SETQS_SETQS1                (0x2)
#define MCF_GPIO_SETQS_SETQS2                (0x4)
#define MCF_GPIO_SETQS_SETQS3                (0x8)
#define MCF_GPIO_SETQS_SETQS4                (0x10)
#define MCF_GPIO_SETQS_SETQS5                (0x20)
#define MCF_GPIO_SETQS_SETQS6                (0x40)

/* Bit definitions and macros for MCF_GPIO_CLRQS */
#define MCF_GPIO_CLRQS_CLRQS0                (0x1)
#define MCF_GPIO_CLRQS_CLRQS1                (0x2)
#define MCF_GPIO_CLRQS_CLRQS2                (0x4)
#define MCF_GPIO_CLRQS_CLRQS3                (0x8)
#define MCF_GPIO_CLRQS_CLRQS4                (0x10)
#define MCF_GPIO_CLRQS_CLRQS5                (0x20)
#define MCF_GPIO_CLRQS_CLRQS6                (0x40)

/* Bit definitions and macros for MCF_GPIO_PORTSD */
#define MCF_GPIO_PORTSD_PORTSD0              (0x1)
#define MCF_GPIO_PORTSD_PORTSD1              (0x2)
#define MCF_GPIO_PORTSD_PORTSD2              (0x4)
#define MCF_GPIO_PORTSD_PORTSD3              (0x8)
#define MCF_GPIO_PORTSD_PORTSD4              (0x10)
#define MCF_GPIO_PORTSD_PORTSD5              (0x20)

/* Bit definitions and macros for MCF_GPIO_DDRSD */
#define MCF_GPIO_DDRSD_DDRSD0                (0x1)
#define MCF_GPIO_DDRSD_DDRSD1                (0x2)
#define MCF_GPIO_DDRSD_DDRSD2                (0x4)
#define MCF_GPIO_DDRSD_DDRSD3                (0x8)
#define MCF_GPIO_DDRSD_DDRSD4                (0x10)
#define MCF_GPIO_DDRSD_DDRSD5                (0x20)

/* Bit definitions and macros for MCF_GPIO_SETSD */
#define MCF_GPIO_SETSD_SETSD0                (0x1)
#define MCF_GPIO_SETSD_SETSD1                (0x2)
#define MCF_GPIO_SETSD_SETSD2                (0x4)
#define MCF_GPIO_SETSD_SETSD3                (0x8)
#define MCF_GPIO_SETSD_SETSD4                (0x10)
#define MCF_GPIO_SETSD_SETSD5                (0x20)

/* Bit definitions and macros for MCF_GPIO_CLRSD */
#define MCF_GPIO_CLRSD_CLRSD0                (0x1)
#define MCF_GPIO_CLRSD_CLRSD1                (0x2)
#define MCF_GPIO_CLRSD_CLRSD2                (0x4)
#define MCF_GPIO_CLRSD_CLRSD3                (0x8)
#define MCF_GPIO_CLRSD_CLRSD4                (0x10)
#define MCF_GPIO_CLRSD_CLRSD5                (0x20)

/* Bit definitions and macros for MCF_GPIO_PORTTC */
#define MCF_GPIO_PORTTC_PORTTC0              (0x1)
#define MCF_GPIO_PORTTC_PORTTC1              (0x2)
#define MCF_GPIO_PORTTC_PORTTC2              (0x4)
#define MCF_GPIO_PORTTC_PORTTC3              (0x8)

/* Bit definitions and macros for MCF_GPIO_DDRTC */
#define MCF_GPIO_DDRTC_DDRTC0                (0x1)
#define MCF_GPIO_DDRTC_DDRTC1                (0x2)
#define MCF_GPIO_DDRTC_DDRTC2                (0x4)
#define MCF_GPIO_DDRTC_DDRTC3                (0x8)

/* Bit definitions and macros for MCF_GPIO_SETTC */
#define MCF_GPIO_SETTC_SETTC0                (0x1)
#define MCF_GPIO_SETTC_SETTC1                (0x2)
#define MCF_GPIO_SETTC_SETTC2                (0x4)
#define MCF_GPIO_SETTC_SETTC3                (0x8)

/* Bit definitions and macros for MCF_GPIO_CLRTC */
#define MCF_GPIO_CLRTC_CLRTC0                (0x1)
#define MCF_GPIO_CLRTC_CLRTC1                (0x2)
#define MCF_GPIO_CLRTC_CLRTC2                (0x4)
#define MCF_GPIO_CLRTC_CLRTC3                (0x8)

/* Bit definitions and macros for MCF_GPIO_PORTTD */
#define MCF_GPIO_PORTTD_PORTTD0              (0x1)
#define MCF_GPIO_PORTTD_PORTTD1              (0x2)
#define MCF_GPIO_PORTTD_PORTTD2              (0x4)
#define MCF_GPIO_PORTTD_PORTTD3              (0x8)

/* Bit definitions and macros for MCF_GPIO_DDRTD */
#define MCF_GPIO_DDRTD_DDRTD0                (0x1)
#define MCF_GPIO_DDRTD_DDRTD1                (0x2)
#define MCF_GPIO_DDRTD_DDRTD2                (0x4)
#define MCF_GPIO_DDRTD_DDRTD3                (0x8)

/* Bit definitions and macros for MCF_GPIO_SETTD */
#define MCF_GPIO_SETTD_SETTD0                (0x1)
#define MCF_GPIO_SETTD_SETTD1                (0x2)
#define MCF_GPIO_SETTD_SETTD2                (0x4)
#define MCF_GPIO_SETTD_SETTD3                (0x8)

/* Bit definitions and macros for MCF_GPIO_CLRTD */
#define MCF_GPIO_CLRTD_CLRTD0                (0x1)
#define MCF_GPIO_CLRTD_CLRTD1                (0x2)
#define MCF_GPIO_CLRTD_CLRTD2                (0x4)
#define MCF_GPIO_CLRTD_CLRTD3                (0x8)

/* Bit definitions and macros for MCF_GPIO_PORTUA */
#define MCF_GPIO_PORTUA_PORTUA0              (0x1)
#define MCF_GPIO_PORTUA_PORTUA1              (0x2)
#define MCF_GPIO_PORTUA_PORTUA2              (0x4)
#define MCF_GPIO_PORTUA_PORTUA3              (0x8)

/* Bit definitions and macros for MCF_GPIO_DDRUA */
#define MCF_GPIO_DDRUA_DDRUA0                (0x1)
#define MCF_GPIO_DDRUA_DDRUA1                (0x2)
#define MCF_GPIO_DDRUA_DDRUA2                (0x4)
#define MCF_GPIO_DDRUA_DDRUA3                (0x8)

/* Bit definitions and macros for MCF_GPIO_SETUA */
#define MCF_GPIO_SETUA_SETUA0                (0x1)
#define MCF_GPIO_SETUA_SETUA1                (0x2)
#define MCF_GPIO_SETUA_SETUA2                (0x4)
#define MCF_GPIO_SETUA_SETUA3                (0x8)

/* Bit definitions and macros for MCF_GPIO_CLRUA */
#define MCF_GPIO_CLRUA_CLRUA0                (0x1)
#define MCF_GPIO_CLRUA_CLRUA1                (0x2)
#define MCF_GPIO_CLRUA_CLRUA2                (0x4)
#define MCF_GPIO_CLRUA_CLRUA3                (0x8)


#endif /* __MCF5282_GPIO_H__ */
