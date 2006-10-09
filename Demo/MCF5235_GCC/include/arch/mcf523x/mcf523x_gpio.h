/*
 * These files are taken from the MCF523X source code example package
 * which is available on the Freescale website. Freescale explicitly 
 * grants the redistribution and modification of these source files.
 * The complete licensing information is available in the file 
 * LICENSE_FREESCALE.TXT.
 *
 * File:	mcf523x_gpio.h
 * Purpose:	Register and bit definitions for the MCF523X
 *
 * Notes:	
 *	
 */

#ifndef __MCF523X_GPIO_H__
#define __MCF523X_GPIO_H__

/*********************************************************************
*
* General Purpose I/O (GPIO)
*
*********************************************************************/

/* Register read/write macros */
#define MCF_GPIO_PODR_ADDR        (*(vuint8 *)(void*)(&__IPSBAR[0x100000]))
#define MCF_GPIO_PODR_DATAH       (*(vuint8 *)(void*)(&__IPSBAR[0x100001]))
#define MCF_GPIO_PODR_DATAL       (*(vuint8 *)(void*)(&__IPSBAR[0x100002]))
#define MCF_GPIO_PODR_BUSCTL      (*(vuint8 *)(void*)(&__IPSBAR[0x100003]))
#define MCF_GPIO_PODR_BS          (*(vuint8 *)(void*)(&__IPSBAR[0x100004]))
#define MCF_GPIO_PODR_CS          (*(vuint8 *)(void*)(&__IPSBAR[0x100005]))
#define MCF_GPIO_PODR_SDRAM       (*(vuint8 *)(void*)(&__IPSBAR[0x100006]))
#define MCF_GPIO_PODR_FECI2C      (*(vuint8 *)(void*)(&__IPSBAR[0x100007]))
#define MCF_GPIO_PODR_UARTH       (*(vuint8 *)(void*)(&__IPSBAR[0x100008]))
#define MCF_GPIO_PODR_UARTL       (*(vuint8 *)(void*)(&__IPSBAR[0x100009]))
#define MCF_GPIO_PODR_QSPI        (*(vuint8 *)(void*)(&__IPSBAR[0x10000A]))
#define MCF_GPIO_PODR_TIMER       (*(vuint8 *)(void*)(&__IPSBAR[0x10000B]))
#define MCF_GPIO_PODR_ETPU        (*(vuint8 *)(void*)(&__IPSBAR[0x10000C]))
#define MCF_GPIO_PDDR_APDDR       (*(vuint8 *)(void*)(&__IPSBAR[0x100010]))
#define MCF_GPIO_PDDR_DATAH       (*(vuint8 *)(void*)(&__IPSBAR[0x100011]))
#define MCF_GPIO_PDDR_DATAL       (*(vuint8 *)(void*)(&__IPSBAR[0x100012]))
#define MCF_GPIO_PDDR_BUSCTL      (*(vuint8 *)(void*)(&__IPSBAR[0x100013]))
#define MCF_GPIO_PDDR_BS          (*(vuint8 *)(void*)(&__IPSBAR[0x100014]))
#define MCF_GPIO_PDDR_CS          (*(vuint8 *)(void*)(&__IPSBAR[0x100015]))
#define MCF_GPIO_PDDR_SDRAM       (*(vuint8 *)(void*)(&__IPSBAR[0x100016]))
#define MCF_GPIO_PDDR_FECI2C      (*(vuint8 *)(void*)(&__IPSBAR[0x100017]))
#define MCF_GPIO_PDDR_UARTH       (*(vuint8 *)(void*)(&__IPSBAR[0x100018]))
#define MCF_GPIO_PDDR_UARTL       (*(vuint8 *)(void*)(&__IPSBAR[0x100019]))
#define MCF_GPIO_PDDR_QSPI        (*(vuint8 *)(void*)(&__IPSBAR[0x10001A]))
#define MCF_GPIO_PDDR_TIMER       (*(vuint8 *)(void*)(&__IPSBAR[0x10001B]))
#define MCF_GPIO_PDDR_ETPU        (*(vuint8 *)(void*)(&__IPSBAR[0x10001C]))
#define MCF_GPIO_PPDSDR_ADDR      (*(vuint8 *)(void*)(&__IPSBAR[0x100020]))
#define MCF_GPIO_PPDSDR_DATAH     (*(vuint8 *)(void*)(&__IPSBAR[0x100021]))
#define MCF_GPIO_PPDSDR_DATAL     (*(vuint8 *)(void*)(&__IPSBAR[0x100022]))
#define MCF_GPIO_PPDSDR_BUSCTL    (*(vuint8 *)(void*)(&__IPSBAR[0x100023]))
#define MCF_GPIO_PPDSDR_BS        (*(vuint8 *)(void*)(&__IPSBAR[0x100024]))
#define MCF_GPIO_PPDSDR_FECI2C    (*(vuint8 *)(void*)(&__IPSBAR[0x100027]))
#define MCF_GPIO_PPDSDR_CS        (*(vuint8 *)(void*)(&__IPSBAR[0x100025]))
#define MCF_GPIO_PPDSDR_SDRAM     (*(vuint8 *)(void*)(&__IPSBAR[0x100026]))
#define MCF_GPIO_PPDSDR_UARTH     (*(vuint8 *)(void*)(&__IPSBAR[0x100028]))
#define MCF_GPIO_PPDSDR_UARTL     (*(vuint8 *)(void*)(&__IPSBAR[0x100029]))
#define MCF_GPIO_PPDSDR_QSPI      (*(vuint8 *)(void*)(&__IPSBAR[0x10002A]))
#define MCF_GPIO_PPDSDR_TIMER     (*(vuint8 *)(void*)(&__IPSBAR[0x10002B]))
#define MCF_GPIO_PPDSDR_ETPU      (*(vuint8 *)(void*)(&__IPSBAR[0x10002C]))
#define MCF_GPIO_PCLRR_ADDR       (*(vuint8 *)(void*)(&__IPSBAR[0x100030]))
#define MCF_GPIO_PCLRR_DATAH      (*(vuint8 *)(void*)(&__IPSBAR[0x100031]))
#define MCF_GPIO_PCLRR_DATAL      (*(vuint8 *)(void*)(&__IPSBAR[0x100032]))
#define MCF_GPIO_PCLRR_BUSCTL     (*(vuint8 *)(void*)(&__IPSBAR[0x100033]))
#define MCF_GPIO_PCLRR_BS         (*(vuint8 *)(void*)(&__IPSBAR[0x100034]))
#define MCF_GPIO_PCLRR_CS         (*(vuint8 *)(void*)(&__IPSBAR[0x100035]))
#define MCF_GPIO_PCLRR_SDRAM      (*(vuint8 *)(void*)(&__IPSBAR[0x100036]))
#define MCF_GPIO_PCLRR_FECI2C     (*(vuint8 *)(void*)(&__IPSBAR[0x100037]))
#define MCF_GPIO_PCLRR_UARTH      (*(vuint8 *)(void*)(&__IPSBAR[0x100038]))
#define MCF_GPIO_PCLRR_UARTL      (*(vuint8 *)(void*)(&__IPSBAR[0x100039]))
#define MCF_GPIO_PCLRR_QSPI       (*(vuint8 *)(void*)(&__IPSBAR[0x10003A]))
#define MCF_GPIO_PCLRR_TIMER      (*(vuint8 *)(void*)(&__IPSBAR[0x10003B]))
#define MCF_GPIO_PCLRR_ETPU       (*(vuint8 *)(void*)(&__IPSBAR[0x10003C]))
#define MCF_GPIO_PAR_AD           (*(vuint8 *)(void*)(&__IPSBAR[0x100040]))
#define MCF_GPIO_PAR_BUSCTL       (*(vuint16*)(void*)(&__IPSBAR[0x100042]))
#define MCF_GPIO_PAR_BS           (*(vuint8 *)(void*)(&__IPSBAR[0x100044]))
#define MCF_GPIO_PAR_CS           (*(vuint8 *)(void*)(&__IPSBAR[0x100045]))
#define MCF_GPIO_PAR_SDRAM        (*(vuint8 *)(void*)(&__IPSBAR[0x100046]))
#define MCF_GPIO_PAR_FECI2C       (*(vuint8 *)(void*)(&__IPSBAR[0x100047]))
#define MCF_GPIO_PAR_UART         (*(vuint16*)(void*)(&__IPSBAR[0x100048]))
#define MCF_GPIO_PAR_QSPI         (*(vuint8 *)(void*)(&__IPSBAR[0x10004A]))
#define MCF_GPIO_PAR_TIMER        (*(vuint16*)(void*)(&__IPSBAR[0x10004C]))
#define MCF_GPIO_PAR_ETPU         (*(vuint8 *)(void*)(&__IPSBAR[0x10004E]))
#define MCF_GPIO_DSCR_EIM         (*(vuint8 *)(void*)(&__IPSBAR[0x100050]))
#define MCF_GPIO_DSCR_ETPU        (*(vuint8 *)(void*)(&__IPSBAR[0x100051]))
#define MCF_GPIO_DSCR_FECI2C      (*(vuint8 *)(void*)(&__IPSBAR[0x100052]))
#define MCF_GPIO_DSCR_UART        (*(vuint8 *)(void*)(&__IPSBAR[0x100053]))
#define MCF_GPIO_DSCR_QSPI        (*(vuint8 *)(void*)(&__IPSBAR[0x100054]))
#define MCF_GPIO_DSCR_TIMER       (*(vuint8 *)(void*)(&__IPSBAR[0x100055]))

/* Bit definitions and macros for MCF_GPIO_PODR_ADDR */
#define MCF_GPIO_PODR_ADDR_PODR_ADDR5            (0x20)
#define MCF_GPIO_PODR_ADDR_PODR_ADDR6            (0x40)
#define MCF_GPIO_PODR_ADDR_PODR_ADDR7            (0x80)

/* Bit definitions and macros for MCF_GPIO_PODR_DATAH */
#define MCF_GPIO_PODR_DATAH_PODR_DATAH0          (0x01)
#define MCF_GPIO_PODR_DATAH_PODR_DATAH1          (0x02)
#define MCF_GPIO_PODR_DATAH_PODR_DATAH2          (0x04)
#define MCF_GPIO_PODR_DATAH_PODR_DATAH3          (0x08)
#define MCF_GPIO_PODR_DATAH_PODR_DATAH4          (0x10)
#define MCF_GPIO_PODR_DATAH_PODR_DATAH5          (0x20)
#define MCF_GPIO_PODR_DATAH_PODR_DATAH6          (0x40)
#define MCF_GPIO_PODR_DATAH_PODR_DATAH7          (0x80)

/* Bit definitions and macros for MCF_GPIO_PODR_DATAL */
#define MCF_GPIO_PODR_DATAL_PODR_DATAL0          (0x01)
#define MCF_GPIO_PODR_DATAL_PODR_DATAL1          (0x02)
#define MCF_GPIO_PODR_DATAL_PODR_DATAL2          (0x04)
#define MCF_GPIO_PODR_DATAL_PODR_DATAL3          (0x08)
#define MCF_GPIO_PODR_DATAL_PODR_DATAL4          (0x10)
#define MCF_GPIO_PODR_DATAL_PODR_DATAL5          (0x20)
#define MCF_GPIO_PODR_DATAL_PODR_DATAL6          (0x40)
#define MCF_GPIO_PODR_DATAL_PODR_DATAL7          (0x80)

/* Bit definitions and macros for MCF_GPIO_PODR_BUSCTL */
#define MCF_GPIO_PODR_BUSCTL_PODR_BUSCTL0        (0x01)
#define MCF_GPIO_PODR_BUSCTL_PODR_BUSCTL1        (0x02)
#define MCF_GPIO_PODR_BUSCTL_PODR_BUSCTL2        (0x04)
#define MCF_GPIO_PODR_BUSCTL_PODR_BUSCTL3        (0x08)
#define MCF_GPIO_PODR_BUSCTL_PODR_BUSCTL4        (0x10)
#define MCF_GPIO_PODR_BUSCTL_PODR_BUSCTL5        (0x20)
#define MCF_GPIO_PODR_BUSCTL_PODR_BUSCTL6        (0x40)
#define MCF_GPIO_PODR_BUSCTL_PODR_BUSCTL7        (0x80)

/* Bit definitions and macros for MCF_GPIO_PODR_BS */
#define MCF_GPIO_PODR_BS_PODR_BS0                (0x01)
#define MCF_GPIO_PODR_BS_PODR_BS1                (0x02)
#define MCF_GPIO_PODR_BS_PODR_BS2                (0x04)
#define MCF_GPIO_PODR_BS_PODR_BS3                (0x08)

/* Bit definitions and macros for MCF_GPIO_PODR_CS */
#define MCF_GPIO_PODR_CS_PODR_CS1                (0x02)
#define MCF_GPIO_PODR_CS_PODR_CS2                (0x04)
#define MCF_GPIO_PODR_CS_PODR_CS3                (0x08)
#define MCF_GPIO_PODR_CS_PODR_CS4                (0x10)
#define MCF_GPIO_PODR_CS_PODR_CS5                (0x20)
#define MCF_GPIO_PODR_CS_PODR_CS6                (0x40)
#define MCF_GPIO_PODR_CS_PODR_CS7                (0x80)

/* Bit definitions and macros for MCF_GPIO_PODR_SDRAM */
#define MCF_GPIO_PODR_SDRAM_PODR_SDRAM0          (0x01)
#define MCF_GPIO_PODR_SDRAM_PODR_SDRAM1          (0x02)
#define MCF_GPIO_PODR_SDRAM_PODR_SDRAM2          (0x04)
#define MCF_GPIO_PODR_SDRAM_PODR_SDRAM3          (0x08)
#define MCF_GPIO_PODR_SDRAM_PODR_SDRAM4          (0x10)
#define MCF_GPIO_PODR_SDRAM_PODR_SDRAM5          (0x20)

/* Bit definitions and macros for MCF_GPIO_PODR_FECI2C */
#define MCF_GPIO_PODR_FECI2C_PODR_FECI2C0        (0x01)
#define MCF_GPIO_PODR_FECI2C_PODR_FECI2C1        (0x02)
#define MCF_GPIO_PODR_FECI2C_PODR_FECI2C2        (0x04)
#define MCF_GPIO_PODR_FECI2C_PODR_FECI2C3        (0x08)

/* Bit definitions and macros for MCF_GPIO_PODR_UARTH */
#define MCF_GPIO_PODR_UARTH_PODR_UARTH0          (0x01)
#define MCF_GPIO_PODR_UARTH_PODR_UARTH1          (0x02)

/* Bit definitions and macros for MCF_GPIO_PODR_UARTL */
#define MCF_GPIO_PODR_UARTL_PODR_UARTL0          (0x01)
#define MCF_GPIO_PODR_UARTL_PODR_UARTL1          (0x02)
#define MCF_GPIO_PODR_UARTL_PODR_UARTL2          (0x04)
#define MCF_GPIO_PODR_UARTL_PODR_UARTL3          (0x08)
#define MCF_GPIO_PODR_UARTL_PODR_UARTL4          (0x10)
#define MCF_GPIO_PODR_UARTL_PODR_UARTL5          (0x20)
#define MCF_GPIO_PODR_UARTL_PODR_UARTL6          (0x40)
#define MCF_GPIO_PODR_UARTL_PODR_UARTL7          (0x80)

/* Bit definitions and macros for MCF_GPIO_PODR_QSPI */
#define MCF_GPIO_PODR_QSPI_PODR_QSPI0            (0x01)
#define MCF_GPIO_PODR_QSPI_PODR_QSPI1            (0x02)
#define MCF_GPIO_PODR_QSPI_PODR_QSPI2            (0x04)
#define MCF_GPIO_PODR_QSPI_PODR_QSPI3            (0x08)
#define MCF_GPIO_PODR_QSPI_PODR_QSPI4            (0x10)

/* Bit definitions and macros for MCF_GPIO_PODR_TIMER */
#define MCF_GPIO_PODR_TIMER_PODR_TIMER0          (0x01)
#define MCF_GPIO_PODR_TIMER_PODR_TIMER1          (0x02)
#define MCF_GPIO_PODR_TIMER_PODR_TIMER2          (0x04)
#define MCF_GPIO_PODR_TIMER_PODR_TIMER3          (0x08)
#define MCF_GPIO_PODR_TIMER_PODR_TIMER4          (0x10)
#define MCF_GPIO_PODR_TIMER_PODR_TIMER5          (0x20)
#define MCF_GPIO_PODR_TIMER_PODR_TIMER6          (0x40)
#define MCF_GPIO_PODR_TIMER_PODR_TIMER7          (0x80)

/* Bit definitions and macros for MCF_GPIO_PODR_ETPU */
#define MCF_GPIO_PODR_ETPU_PODR_ETPU0            (0x01)
#define MCF_GPIO_PODR_ETPU_PODR_ETPU1            (0x02)
#define MCF_GPIO_PODR_ETPU_PODR_ETPU2            (0x04)

/* Bit definitions and macros for MCF_GPIO_PDDR_APDDR */
#define MCF_GPIO_PDDR_APDDR_PDDR_APDDR5          (0x20)
#define MCF_GPIO_PDDR_APDDR_PDDR_APDDR6          (0x40)
#define MCF_GPIO_PDDR_APDDR_PDDR_APDDR7          (0x80)

/* Bit definitions and macros for MCF_GPIO_PDDR_DATAH */
#define MCF_GPIO_PDDR_DATAH_PDDR_DATAH0          (0x01)
#define MCF_GPIO_PDDR_DATAH_PDDR_DATAH1          (0x02)
#define MCF_GPIO_PDDR_DATAH_PDDR_DATAH2          (0x04)
#define MCF_GPIO_PDDR_DATAH_PDDR_DATAH3          (0x08)
#define MCF_GPIO_PDDR_DATAH_PDDR_DATAH4          (0x10)
#define MCF_GPIO_PDDR_DATAH_PDDR_DATAH5          (0x20)
#define MCF_GPIO_PDDR_DATAH_PDDR_DATAH6          (0x40)
#define MCF_GPIO_PDDR_DATAH_PDDR_DATAH7          (0x80)

/* Bit definitions and macros for MCF_GPIO_PDDR_DATAL */
#define MCF_GPIO_PDDR_DATAL_PDDR_DATAL0          (0x01)
#define MCF_GPIO_PDDR_DATAL_PDDR_DATAL1          (0x02)
#define MCF_GPIO_PDDR_DATAL_PDDR_DATAL2          (0x04)
#define MCF_GPIO_PDDR_DATAL_PDDR_DATAL3          (0x08)
#define MCF_GPIO_PDDR_DATAL_PDDR_DATAL4          (0x10)
#define MCF_GPIO_PDDR_DATAL_PDDR_DATAL5          (0x20)
#define MCF_GPIO_PDDR_DATAL_PDDR_DATAL6          (0x40)
#define MCF_GPIO_PDDR_DATAL_PDDR_DATAL7          (0x80)

/* Bit definitions and macros for MCF_GPIO_PDDR_BUSCTL */
#define MCF_GPIO_PDDR_BUSCTL_PDDR_BUSCTL0        (0x01)
#define MCF_GPIO_PDDR_BUSCTL_PDDR_BUSCTL1        (0x02)
#define MCF_GPIO_PDDR_BUSCTL_PDDR_BUSCTL2        (0x04)
#define MCF_GPIO_PDDR_BUSCTL_PDDR_BUSCTL3        (0x08)
#define MCF_GPIO_PDDR_BUSCTL_PDDR_BUSCTL4        (0x10)
#define MCF_GPIO_PDDR_BUSCTL_PDDR_BUSCTL5        (0x20)
#define MCF_GPIO_PDDR_BUSCTL_PDDR_BUSCTL6        (0x40)
#define MCF_GPIO_PDDR_BUSCTL_PDDR_BUSCTL7        (0x80)

/* Bit definitions and macros for MCF_GPIO_PDDR_BS */
#define MCF_GPIO_PDDR_BS_PDDR_BS0                (0x01)
#define MCF_GPIO_PDDR_BS_PDDR_BS3(x)             (((x)&0x07)<<1)

/* Bit definitions and macros for MCF_GPIO_PDDR_CS */
#define MCF_GPIO_PDDR_CS_PDDR_CS1                (0x02)
#define MCF_GPIO_PDDR_CS_PDDR_CS2                (0x04)
#define MCF_GPIO_PDDR_CS_PDDR_CS3                (0x08)
#define MCF_GPIO_PDDR_CS_PDDR_CS4                (0x10)
#define MCF_GPIO_PDDR_CS_PDDR_CS5                (0x20)
#define MCF_GPIO_PDDR_CS_PDDR_CS6                (0x40)
#define MCF_GPIO_PDDR_CS_PDDR_CS7                (0x80)

/* Bit definitions and macros for MCF_GPIO_PDDR_SDRAM */
#define MCF_GPIO_PDDR_SDRAM_PDDR_SDRAM0          (0x01)
#define MCF_GPIO_PDDR_SDRAM_PDDR_SDRAM1          (0x02)
#define MCF_GPIO_PDDR_SDRAM_PDDR_SDRAM2          (0x04)
#define MCF_GPIO_PDDR_SDRAM_PDDR_SDRAM3          (0x08)
#define MCF_GPIO_PDDR_SDRAM_PDDR_SDRAM4          (0x10)
#define MCF_GPIO_PDDR_SDRAM_PDDR_SDRAM5          (0x20)

/* Bit definitions and macros for MCF_GPIO_PDDR_FECI2C */
#define MCF_GPIO_PDDR_FECI2C_PDDR_FECI2C0        (0x01)
#define MCF_GPIO_PDDR_FECI2C_PDDR_FECI2C1        (0x02)
#define MCF_GPIO_PDDR_FECI2C_PDDR_FECI2C2        (0x04)
#define MCF_GPIO_PDDR_FECI2C_PDDR_FECI2C3        (0x08)

/* Bit definitions and macros for MCF_GPIO_PDDR_UARTH */
#define MCF_GPIO_PDDR_UARTH_PDDR_UARTH0          (0x01)
#define MCF_GPIO_PDDR_UARTH_PDDR_UARTH1          (0x02)

/* Bit definitions and macros for MCF_GPIO_PDDR_UARTL */
#define MCF_GPIO_PDDR_UARTL_PDDR_UARTL0          (0x01)
#define MCF_GPIO_PDDR_UARTL_PDDR_UARTL1          (0x02)
#define MCF_GPIO_PDDR_UARTL_PDDR_UARTL2          (0x04)
#define MCF_GPIO_PDDR_UARTL_PDDR_UARTL3          (0x08)
#define MCF_GPIO_PDDR_UARTL_PDDR_UARTL4          (0x10)
#define MCF_GPIO_PDDR_UARTL_PDDR_UARTL5          (0x20)
#define MCF_GPIO_PDDR_UARTL_PDDR_UARTL6          (0x40)
#define MCF_GPIO_PDDR_UARTL_PDDR_UARTL7          (0x80)

/* Bit definitions and macros for MCF_GPIO_PDDR_QSPI */
#define MCF_GPIO_PDDR_QSPI_PDDR_QSPI0            (0x01)
#define MCF_GPIO_PDDR_QSPI_PDDR_QSPI1            (0x02)
#define MCF_GPIO_PDDR_QSPI_PDDR_QSPI2            (0x04)
#define MCF_GPIO_PDDR_QSPI_PDDR_QSPI3            (0x08)
#define MCF_GPIO_PDDR_QSPI_PDDR_QSPI4            (0x10)

/* Bit definitions and macros for MCF_GPIO_PDDR_TIMER */
#define MCF_GPIO_PDDR_TIMER_PDDR_TIMER0          (0x01)
#define MCF_GPIO_PDDR_TIMER_PDDR_TIMER1          (0x02)
#define MCF_GPIO_PDDR_TIMER_PDDR_TIMER2          (0x04)
#define MCF_GPIO_PDDR_TIMER_PDDR_TIMER3          (0x08)
#define MCF_GPIO_PDDR_TIMER_PDDR_TIMER4          (0x10)
#define MCF_GPIO_PDDR_TIMER_PDDR_TIMER5          (0x20)
#define MCF_GPIO_PDDR_TIMER_PDDR_TIMER6          (0x40)
#define MCF_GPIO_PDDR_TIMER_PDDR_TIMER7          (0x80)

/* Bit definitions and macros for MCF_GPIO_PDDR_ETPU */
#define MCF_GPIO_PDDR_ETPU_PDDR_ETPU0            (0x01)
#define MCF_GPIO_PDDR_ETPU_PDDR_ETPU1            (0x02)
#define MCF_GPIO_PDDR_ETPU_PDDR_ETPU2            (0x04)

/* Bit definitions and macros for MCF_GPIO_PPDSDR_ADDR */
#define MCF_GPIO_PPDSDR_ADDR_PPDSDR_ADDR5        (0x20)
#define MCF_GPIO_PPDSDR_ADDR_PPDSDR_ADDR6        (0x40)
#define MCF_GPIO_PPDSDR_ADDR_PPDSDR_ADDR7        (0x80)

/* Bit definitions and macros for MCF_GPIO_PPDSDR_DATAH */
#define MCF_GPIO_PPDSDR_DATAH_PPDSDR_DATAH0      (0x01)
#define MCF_GPIO_PPDSDR_DATAH_PPDSDR_DATAH1      (0x02)
#define MCF_GPIO_PPDSDR_DATAH_PPDSDR_DATAH2      (0x04)
#define MCF_GPIO_PPDSDR_DATAH_PPDSDR_DATAH3      (0x08)
#define MCF_GPIO_PPDSDR_DATAH_PPDSDR_DATAH4      (0x10)
#define MCF_GPIO_PPDSDR_DATAH_PPDSDR_DATAH5      (0x20)
#define MCF_GPIO_PPDSDR_DATAH_PPDSDR_DATAH6      (0x40)
#define MCF_GPIO_PPDSDR_DATAH_PPDSDR_DATAH7      (0x80)

/* Bit definitions and macros for MCF_GPIO_PPDSDR_DATAL */
#define MCF_GPIO_PPDSDR_DATAL_PPDSDR_DATAL0      (0x01)
#define MCF_GPIO_PPDSDR_DATAL_PPDSDR_DATAL1      (0x02)
#define MCF_GPIO_PPDSDR_DATAL_PPDSDR_DATAL2      (0x04)
#define MCF_GPIO_PPDSDR_DATAL_PPDSDR_DATAL3      (0x08)
#define MCF_GPIO_PPDSDR_DATAL_PPDSDR_DATAL4      (0x10)
#define MCF_GPIO_PPDSDR_DATAL_PPDSDR_DATAL5      (0x20)
#define MCF_GPIO_PPDSDR_DATAL_PPDSDR_DATAL6      (0x40)
#define MCF_GPIO_PPDSDR_DATAL_PPDSDR_DATAL7      (0x80)

/* Bit definitions and macros for MCF_GPIO_PPDSDR_BUSCTL */
#define MCF_GPIO_PPDSDR_BUSCTL_PPDSDR_BUSCTL0    (0x01)
#define MCF_GPIO_PPDSDR_BUSCTL_PPDSDR_BUSCTL1    (0x02)
#define MCF_GPIO_PPDSDR_BUSCTL_PPDSDR_BUSCTL2    (0x04)
#define MCF_GPIO_PPDSDR_BUSCTL_PPDSDR_BUSCTL3    (0x08)
#define MCF_GPIO_PPDSDR_BUSCTL_PPDSDR_BUSCTL4    (0x10)
#define MCF_GPIO_PPDSDR_BUSCTL_PPDSDR_BUSCTL5    (0x20)
#define MCF_GPIO_PPDSDR_BUSCTL_PPDSDR_BUSCTL6    (0x40)
#define MCF_GPIO_PPDSDR_BUSCTL_PPDSDR_BUSCTL7    (0x80)

/* Bit definitions and macros for MCF_GPIO_PPDSDR_BS */
#define MCF_GPIO_PPDSDR_BS_PPDSDR_BS0            (0x01)
#define MCF_GPIO_PPDSDR_BS_PPDSDR_BS1            (0x02)
#define MCF_GPIO_PPDSDR_BS_PPDSDR_BS2            (0x04)
#define MCF_GPIO_PPDSDR_BS_PPDSDR_BS3            (0x08)

/* Bit definitions and macros for MCF_GPIO_PPDSDR_FECI2C */
#define MCF_GPIO_PPDSDR_FECI2C_PPDSDR_FECI2C0    (0x01)
#define MCF_GPIO_PPDSDR_FECI2C_PPDSDR_FECI2C1    (0x02)
#define MCF_GPIO_PPDSDR_FECI2C_PPDSDR_FECI2C2    (0x04)
#define MCF_GPIO_PPDSDR_FECI2C_PPDSDR_FECI2C3    (0x08)

/* Bit definitions and macros for MCF_GPIO_PPDSDR_CS */
#define MCF_GPIO_PPDSDR_CS_PPDSDR_CS1            (0x02)
#define MCF_GPIO_PPDSDR_CS_PPDSDR_CS2            (0x04)
#define MCF_GPIO_PPDSDR_CS_PPDSDR_CS3            (0x08)
#define MCF_GPIO_PPDSDR_CS_PPDSDR_CS4            (0x10)
#define MCF_GPIO_PPDSDR_CS_PPDSDR_CS5            (0x20)
#define MCF_GPIO_PPDSDR_CS_PPDSDR_CS6            (0x40)
#define MCF_GPIO_PPDSDR_CS_PPDSDR_CS7            (0x80)

/* Bit definitions and macros for MCF_GPIO_PPDSDR_SDRAM */
#define MCF_GPIO_PPDSDR_SDRAM_PPDSDR_SDRAM0      (0x01)
#define MCF_GPIO_PPDSDR_SDRAM_PPDSDR_SDRAM1      (0x02)
#define MCF_GPIO_PPDSDR_SDRAM_PPDSDR_SDRAM2      (0x04)
#define MCF_GPIO_PPDSDR_SDRAM_PPDSDR_SDRAM3      (0x08)
#define MCF_GPIO_PPDSDR_SDRAM_PPDSDR_SDRAM4      (0x10)
#define MCF_GPIO_PPDSDR_SDRAM_PPDSDR_SDRAM5      (0x20)
#define MCF_GPIO_PPDSDR_SDRAM_PPDSDR_SDRAM6      (0x40)
#define MCF_GPIO_PPDSDR_SDRAM_PPDSDR_SDRAM7      (0x80)

/* Bit definitions and macros for MCF_GPIO_PPDSDR_UARTH */
#define MCF_GPIO_PPDSDR_UARTH_PPDSDR_UARTH0      (0x01)
#define MCF_GPIO_PPDSDR_UARTH_PPDSDR_UARTH1      (0x02)

/* Bit definitions and macros for MCF_GPIO_PPDSDR_UARTL */
#define MCF_GPIO_PPDSDR_UARTL_PPDSDR_UARTL0      (0x01)
#define MCF_GPIO_PPDSDR_UARTL_PPDSDR_UARTL1      (0x02)
#define MCF_GPIO_PPDSDR_UARTL_PPDSDR_UARTL2      (0x04)
#define MCF_GPIO_PPDSDR_UARTL_PPDSDR_UARTL3      (0x08)
#define MCF_GPIO_PPDSDR_UARTL_PPDSDR_UARTL4      (0x10)
#define MCF_GPIO_PPDSDR_UARTL_PPDSDR_UARTL5      (0x20)
#define MCF_GPIO_PPDSDR_UARTL_PPDSDR_UARTL6      (0x40)
#define MCF_GPIO_PPDSDR_UARTL_PPDSDR_UARTL7      (0x80)

/* Bit definitions and macros for MCF_GPIO_PPDSDR_QSPI */
#define MCF_GPIO_PPDSDR_QSPI_PPDSDR_QSPI0        (0x01)
#define MCF_GPIO_PPDSDR_QSPI_PPDSDR_QSPI1        (0x02)
#define MCF_GPIO_PPDSDR_QSPI_PPDSDR_QSPI2        (0x04)
#define MCF_GPIO_PPDSDR_QSPI_PPDSDR_QSPI3        (0x08)
#define MCF_GPIO_PPDSDR_QSPI_PPDSDR_QSPI4        (0x10)

/* Bit definitions and macros for MCF_GPIO_PPDSDR_TIMER */
#define MCF_GPIO_PPDSDR_TIMER_PPDSDR_TIMER0      (0x01)
#define MCF_GPIO_PPDSDR_TIMER_PPDSDR_TIMER1      (0x02)
#define MCF_GPIO_PPDSDR_TIMER_PPDSDR_TIMER2      (0x04)
#define MCF_GPIO_PPDSDR_TIMER_PPDSDR_TIMER3      (0x08)
#define MCF_GPIO_PPDSDR_TIMER_PPDSDR_TIMER4      (0x10)
#define MCF_GPIO_PPDSDR_TIMER_PPDSDR_TIMER5      (0x20)
#define MCF_GPIO_PPDSDR_TIMER_PPDSDR_TIMER6      (0x40)
#define MCF_GPIO_PPDSDR_TIMER_PPDSDR_TIMER7      (0x80)

/* Bit definitions and macros for MCF_GPIO_PPDSDR_ETPU */
#define MCF_GPIO_PPDSDR_ETPU_PPDSDR_ETPU0        (0x01)
#define MCF_GPIO_PPDSDR_ETPU_PPDSDR_ETPU1        (0x02)
#define MCF_GPIO_PPDSDR_ETPU_PPDSDR_ETPU2        (0x04)

/* Bit definitions and macros for MCF_GPIO_PCLRR_ADDR */
#define MCF_GPIO_PCLRR_ADDR_PCLRR_ADDR5          (0x20)
#define MCF_GPIO_PCLRR_ADDR_PCLRR_ADDR6          (0x40)
#define MCF_GPIO_PCLRR_ADDR_PCLRR_ADDR7          (0x80)

/* Bit definitions and macros for MCF_GPIO_PCLRR_DATAH */
#define MCF_GPIO_PCLRR_DATAH_PCLRR_DATAH0        (0x01)
#define MCF_GPIO_PCLRR_DATAH_PCLRR_DATAH1        (0x02)
#define MCF_GPIO_PCLRR_DATAH_PCLRR_DATAH2        (0x04)
#define MCF_GPIO_PCLRR_DATAH_PCLRR_DATAH3        (0x08)
#define MCF_GPIO_PCLRR_DATAH_PCLRR_DATAH4        (0x10)
#define MCF_GPIO_PCLRR_DATAH_PCLRR_DATAH5        (0x20)
#define MCF_GPIO_PCLRR_DATAH_PCLRR_DATAH6        (0x40)
#define MCF_GPIO_PCLRR_DATAH_PCLRR_DATAH7        (0x80)

/* Bit definitions and macros for MCF_GPIO_PCLRR_DATAL */
#define MCF_GPIO_PCLRR_DATAL_PCLRR_DATAL0        (0x01)
#define MCF_GPIO_PCLRR_DATAL_PCLRR_DATAL1        (0x02)
#define MCF_GPIO_PCLRR_DATAL_PCLRR_DATAL2        (0x04)
#define MCF_GPIO_PCLRR_DATAL_PCLRR_DATAL3        (0x08)
#define MCF_GPIO_PCLRR_DATAL_PCLRR_DATAL4        (0x10)
#define MCF_GPIO_PCLRR_DATAL_PCLRR_DATAL5        (0x20)
#define MCF_GPIO_PCLRR_DATAL_PCLRR_DATAL6        (0x40)
#define MCF_GPIO_PCLRR_DATAL_PCLRR_DATAL7        (0x80)

/* Bit definitions and macros for MCF_GPIO_PCLRR_BUSCTL */
#define MCF_GPIO_PCLRR_BUSCTL_PCLRR_BUSCTL0      (0x01)
#define MCF_GPIO_PCLRR_BUSCTL_PCLRR_BUSCTL1      (0x02)
#define MCF_GPIO_PCLRR_BUSCTL_PCLRR_BUSCTL2      (0x04)
#define MCF_GPIO_PCLRR_BUSCTL_PCLRR_BUSCTL3      (0x08)
#define MCF_GPIO_PCLRR_BUSCTL_PCLRR_BUSCTL4      (0x10)
#define MCF_GPIO_PCLRR_BUSCTL_PCLRR_BUSCTL5      (0x20)
#define MCF_GPIO_PCLRR_BUSCTL_PCLRR_BUSCTL6      (0x40)
#define MCF_GPIO_PCLRR_BUSCTL_PCLRR_BUSCTL7      (0x80)

/* Bit definitions and macros for MCF_GPIO_PCLRR_BS */
#define MCF_GPIO_PCLRR_BS_PCLRR_BS0              (0x01)
#define MCF_GPIO_PCLRR_BS_PCLRR_BS1              (0x02)
#define MCF_GPIO_PCLRR_BS_PCLRR_BS2              (0x04)
#define MCF_GPIO_PCLRR_BS_PCLRR_BS3              (0x08)

/* Bit definitions and macros for MCF_GPIO_PCLRR_CS */
#define MCF_GPIO_PCLRR_CS_PCLRR_CS1              (0x02)
#define MCF_GPIO_PCLRR_CS_PCLRR_CS2              (0x04)
#define MCF_GPIO_PCLRR_CS_PCLRR_CS3              (0x08)
#define MCF_GPIO_PCLRR_CS_PCLRR_CS4              (0x10)
#define MCF_GPIO_PCLRR_CS_PCLRR_CS5              (0x20)
#define MCF_GPIO_PCLRR_CS_PCLRR_CS6              (0x40)
#define MCF_GPIO_PCLRR_CS_PCLRR_CS7              (0x80)

/* Bit definitions and macros for MCF_GPIO_PCLRR_SDRAM */
#define MCF_GPIO_PCLRR_SDRAM_PCLRR_SDRAM0        (0x01)
#define MCF_GPIO_PCLRR_SDRAM_PCLRR_SDRAM1        (0x02)
#define MCF_GPIO_PCLRR_SDRAM_PCLRR_SDRAM2        (0x04)
#define MCF_GPIO_PCLRR_SDRAM_PCLRR_SDRAM3        (0x08)
#define MCF_GPIO_PCLRR_SDRAM_PCLRR_SDRAM4        (0x10)
#define MCF_GPIO_PCLRR_SDRAM_PCLRR_SDRAM5        (0x20)

/* Bit definitions and macros for MCF_GPIO_PCLRR_FECI2C */
#define MCF_GPIO_PCLRR_FECI2C_PCLRR_FECI2C0      (0x01)
#define MCF_GPIO_PCLRR_FECI2C_PCLRR_FECI2C1      (0x02)
#define MCF_GPIO_PCLRR_FECI2C_PCLRR_FECI2C2      (0x04)
#define MCF_GPIO_PCLRR_FECI2C_PCLRR_FECI2C3      (0x08)

/* Bit definitions and macros for MCF_GPIO_PCLRR_UARTH */
#define MCF_GPIO_PCLRR_UARTH_PCLRR_UARTH0        (0x01)
#define MCF_GPIO_PCLRR_UARTH_PCLRR_UARTH1        (0x02)

/* Bit definitions and macros for MCF_GPIO_PCLRR_UARTL */
#define MCF_GPIO_PCLRR_UARTL_PCLRR_UARTL0        (0x01)
#define MCF_GPIO_PCLRR_UARTL_PCLRR_UARTL1        (0x02)
#define MCF_GPIO_PCLRR_UARTL_PCLRR_UARTL2        (0x04)
#define MCF_GPIO_PCLRR_UARTL_PCLRR_UARTL3        (0x08)
#define MCF_GPIO_PCLRR_UARTL_PCLRR_UARTL4        (0x10)
#define MCF_GPIO_PCLRR_UARTL_PCLRR_UARTL5        (0x20)
#define MCF_GPIO_PCLRR_UARTL_PCLRR_UARTL6        (0x40)
#define MCF_GPIO_PCLRR_UARTL_PCLRR_UARTL7        (0x80)

/* Bit definitions and macros for MCF_GPIO_PCLRR_QSPI */
#define MCF_GPIO_PCLRR_QSPI_PCLRR_QSPI0          (0x01)
#define MCF_GPIO_PCLRR_QSPI_PCLRR_QSPI1          (0x02)
#define MCF_GPIO_PCLRR_QSPI_PCLRR_QSPI2          (0x04)
#define MCF_GPIO_PCLRR_QSPI_PCLRR_QSPI3          (0x08)
#define MCF_GPIO_PCLRR_QSPI_PCLRR_QSPI4          (0x10)

/* Bit definitions and macros for MCF_GPIO_PCLRR_TIMER */
#define MCF_GPIO_PCLRR_TIMER_PCLRR_TIMER0        (0x01)
#define MCF_GPIO_PCLRR_TIMER_PCLRR_TIMER1        (0x02)
#define MCF_GPIO_PCLRR_TIMER_PCLRR_TIMER2        (0x04)
#define MCF_GPIO_PCLRR_TIMER_PCLRR_TIMER3        (0x08)
#define MCF_GPIO_PCLRR_TIMER_PCLRR_TIMER4        (0x10)
#define MCF_GPIO_PCLRR_TIMER_PCLRR_TIMER5        (0x20)
#define MCF_GPIO_PCLRR_TIMER_PCLRR_TIMER6        (0x40)
#define MCF_GPIO_PCLRR_TIMER_PCLRR_TIMER7        (0x80)

/* Bit definitions and macros for MCF_GPIO_PCLRR_ETPU */
#define MCF_GPIO_PCLRR_ETPU_PCLRR_ETPU0          (0x01)
#define MCF_GPIO_PCLRR_ETPU_PCLRR_ETPU1          (0x02)
#define MCF_GPIO_PCLRR_ETPU_PCLRR_ETPU2          (0x04)

/* Bit definitions and macros for MCF_GPIO_PAR_AD */
#define MCF_GPIO_PAR_AD_PAR_DATAL                (0x01)
#define MCF_GPIO_PAR_AD_PAR_ADDR21               (0x20)
#define MCF_GPIO_PAR_AD_PAR_ADDR22               (0x40)
#define MCF_GPIO_PAR_AD_PAR_ADDR23               (0x80)

/* Bit definitions and macros for MCF_GPIO_PAR_BUSCTL */
#define MCF_GPIO_PAR_BUSCTL_PAR_TIP(x)           (((x)&0x0003)<<0)
#define MCF_GPIO_PAR_BUSCTL_PAR_TS(x)            (((x)&0x0003)<<2)
#define MCF_GPIO_PAR_BUSCTL_PAR_TSIZ0            (0x0010)
#define MCF_GPIO_PAR_BUSCTL_PAR_TSIZ1            (0x0040)
#define MCF_GPIO_PAR_BUSCTL_PAR_RWB              (0x0100)
#define MCF_GPIO_PAR_BUSCTL_PAR_TEA(x)           (((x)&0x0003)<<10)
#define MCF_GPIO_PAR_BUSCTL_PAR_TA               (0x1000)
#define MCF_GPIO_PAR_BUSCTL_PAR_OE               (0x4000)
#define MCF_GPIO_PAR_BUSCTL_PAR_TEA_GPIO         (0x0000)
#define MCF_GPIO_PAR_BUSCTL_PAR_TEA_DMA          (0x0800)
#define MCF_GPIO_PAR_BUSCTL_PAR_TEA_TEA          (0x0C00)
#define MCF_GPIO_PAR_BUSCTL_PAR_TS_GPIO          (0x0000)
#define MCF_GPIO_PAR_BUSCTL_PAR_TS_DMA           (0x0080)
#define MCF_GPIO_PAR_BUSCTL_PAR_TS_TS            (0x00C0)
#define MCF_GPIO_PAR_BUSCTL_PAR_TIP_GPIO         (0x0000)
#define MCF_GPIO_PAR_BUSCTL_PAR_TIP_DMA          (0x0002)
#define MCF_GPIO_PAR_BUSCTL_PAR_TIP_TEA          (0x0003)

/* Bit definitions and macros for MCF_GPIO_PAR_BS */
#define MCF_GPIO_PAR_BS_PAR_BS0                  (0x01)
#define MCF_GPIO_PAR_BS_PAR_BS1                  (0x02)
#define MCF_GPIO_PAR_BS_PAR_BS2                  (0x04)
#define MCF_GPIO_PAR_BS_PAR_BS3                  (0x08)

/* Bit definitions and macros for MCF_GPIO_PAR_CS */
#define MCF_GPIO_PAR_CS_PAR_CS1                  (0x02)
#define MCF_GPIO_PAR_CS_PAR_CS2                  (0x04)
#define MCF_GPIO_PAR_CS_PAR_CS3                  (0x08)
#define MCF_GPIO_PAR_CS_PAR_CS4                  (0x10)
#define MCF_GPIO_PAR_CS_PAR_CS5                  (0x20)
#define MCF_GPIO_PAR_CS_PAR_CS6                  (0x40)
#define MCF_GPIO_PAR_CS_PAR_CS7                  (0x80)

/* Bit definitions and macros for MCF_GPIO_PAR_SDRAM */
#define MCF_GPIO_PAR_SDRAM_PAR_SDCS0             (0x01)
#define MCF_GPIO_PAR_SDRAM_PAR_SDCS1             (0x02)
#define MCF_GPIO_PAR_SDRAM_PAR_SCKE              (0x04)
#define MCF_GPIO_PAR_SDRAM_PAR_SRAS              (0x08)
#define MCF_GPIO_PAR_SDRAM_PAR_SCAS              (0x10)
#define MCF_GPIO_PAR_SDRAM_PAR_SDWE              (0x20)
#define MCF_GPIO_PAR_SDRAM_PAR_CSSDCS(x)         (((x)&0x03)<<6)

/* Bit definitions and macros for MCF_GPIO_PAR_FECI2C */
#define MCF_GPIO_PAR_FECI2C_PAR_SDA(x)           (((x)&0x03)<<0)
#define MCF_GPIO_PAR_FECI2C_PAR_SCL(x)           (((x)&0x03)<<2)
#define MCF_GPIO_PAR_FECI2C_PAR_EMDIO(x)         (((x)&0x03)<<4)
#define MCF_GPIO_PAR_FECI2C_PAR_EMDC(x)          (((x)&0x03)<<6)
#define MCF_GPIO_PAR_FECI2C_PAR_EMDC_GPIO        (0x00)
#define MCF_GPIO_PAR_FECI2C_PAR_EMDC_UART2       (0x40)
#define MCF_GPIO_PAR_FECI2C_PAR_EMDC_I2C         (0x80)
#define MCF_GPIO_PAR_FECI2C_PAR_EMDC_FEC         (0xC0)
#define MCF_GPIO_PAR_FECI2C_PAR_EMDIO_GPIO       (0x00)
#define MCF_GPIO_PAR_FECI2C_PAR_EMDIO_UART2      (0x10)
#define MCF_GPIO_PAR_FECI2C_PAR_EMDIO_I2C        (0x20)
#define MCF_GPIO_PAR_FECI2C_PAR_EMDIO_FEC        (0x30)
#define MCF_GPIO_PAR_FECI2C_PAR_SCL_GPIO         (0x00)
#define MCF_GPIO_PAR_FECI2C_PAR_SCL_FLEX         (0x08)
#define MCF_GPIO_PAR_FECI2C_PAR_SCL_I2C          (0x0C)
#define MCF_GPIO_PAR_FECI2C_PAR_SDA_GPIO         (0x00)
#define MCF_GPIO_PAR_FECI2C_PAR_SDA_FLEX         (0x02)
#define MCF_GPIO_PAR_FECI2C_PAR_SDA_I2C          (0x03)

/* Bit definitions and macros for MCF_GPIO_PAR_UART */
#define MCF_GPIO_PAR_UART_PAR_U0RTS              (0x0001)
#define MCF_GPIO_PAR_UART_PAR_U0CTS              (0x0002)
#define MCF_GPIO_PAR_UART_PAR_U0TXD              (0x0004)
#define MCF_GPIO_PAR_UART_PAR_U0RXD              (0x0008)
#define MCF_GPIO_PAR_UART_PAR_U1RTS(x)           (((x)&0x0003)<<4)
#define MCF_GPIO_PAR_UART_PAR_U1CTS(x)           (((x)&0x0003)<<6)
#define MCF_GPIO_PAR_UART_PAR_U1TXD(x)           (((x)&0x0003)<<8)
#define MCF_GPIO_PAR_UART_PAR_U1RXD(x)           (((x)&0x0003)<<10)
#define MCF_GPIO_PAR_UART_PAR_U2TXD              (0x1000)
#define MCF_GPIO_PAR_UART_PAR_U2RXD              (0x2000)
#define MCF_GPIO_PAR_UART_PAR_CAN1EN             (0x4000)
#define MCF_GPIO_PAR_UART_PAR_DREQ2              (0x8000)
#define MCF_GPIO_PAR_UART_PAR_U1RXD_GPIO         (0x0000)
#define MCF_GPIO_PAR_UART_PAR_U1RXD_FLEX         (0x0800)
#define MCF_GPIO_PAR_UART_PAR_U1RXD_UART1        (0x0C00)
#define MCF_GPIO_PAR_UART_PAR_U1TXD_GPIO         (0x0000)
#define MCF_GPIO_PAR_UART_PAR_U1TXD_FLEX         (0x0200)
#define MCF_GPIO_PAR_UART_PAR_U1TXD_UART1        (0x0300)
#define MCF_GPIO_PAR_UART_PAR_U1CTS_GPIO         (0x0000)
#define MCF_GPIO_PAR_UART_PAR_U1CTS_UART2        (0x0080)
#define MCF_GPIO_PAR_UART_PAR_U1CTS_UART1        (0x00C0)
#define MCF_GPIO_PAR_UART_PAR_U1RTS_GPIO         (0x0000)
#define MCF_GPIO_PAR_UART_PAR_U1RTS_UART2        (0x0020)
#define MCF_GPIO_PAR_UART_PAR_U1RTS_UART1        (0x0030)

/* Bit definitions and macros for MCF_GPIO_PAR_QSPI */
#define MCF_GPIO_PAR_QSPI_PAR_SCK(x)             (((x)&0x03)<<0)
#define MCF_GPIO_PAR_QSPI_PAR_DOUT               (0x04)
#define MCF_GPIO_PAR_QSPI_PAR_DIN(x)             (((x)&0x03)<<3)
#define MCF_GPIO_PAR_QSPI_PAR_PCS0               (0x20)
#define MCF_GPIO_PAR_QSPI_PAR_PCS1(x)            (((x)&0x03)<<6)
#define MCF_GPIO_PAR_QSPI_PAR_PCS1_GPIO          (0x00)
#define MCF_GPIO_PAR_QSPI_PAR_PCS1_SDRAMC        (0x80)
#define MCF_GPIO_PAR_QSPI_PAR_PCS1_QSPI          (0xC0)
#define MCF_GPIO_PAR_QSPI_PAR_DIN_GPIO           (0x00)
#define MCF_GPIO_PAR_QSPI_PAR_DIN_I2C            (0x10)
#define MCF_GPIO_PAR_QSPI_PAR_DIN_QSPI           (0x1C)
#define MCF_GPIO_PAR_QSPI_PAR_SCK_GPIO           (0x00)
#define MCF_GPIO_PAR_QSPI_PAR_SCK_I2C            (0x02)
#define MCF_GPIO_PAR_QSPI_PAR_SCK_QSPI           (0x03)

/* Bit definitions and macros for MCF_GPIO_PAR_TIMER */
#define MCF_GPIO_PAR_TIMER_PAR_T0OUT(x)          (((x)&0x0003)<<0)
#define MCF_GPIO_PAR_TIMER_PAR_T1OUT(x)          (((x)&0x0003)<<2)
#define MCF_GPIO_PAR_TIMER_PAR_T2OUT(x)          (((x)&0x0003)<<4)
#define MCF_GPIO_PAR_TIMER_PAR_T3OUT(x)          (((x)&0x0003)<<6)
#define MCF_GPIO_PAR_TIMER_PAR_T0IN(x)           (((x)&0x0003)<<8)
#define MCF_GPIO_PAR_TIMER_PAR_T1IN(x)           (((x)&0x0003)<<10)
#define MCF_GPIO_PAR_TIMER_PAR_T2IN(x)           (((x)&0x0003)<<12)
#define MCF_GPIO_PAR_TIMER_PAR_T3IN(x)           (((x)&0x0003)<<14)
#define MCF_GPIO_PAR_TIMER_PAR_T3IN_GPIO         (0x0000)
#define MCF_GPIO_PAR_TIMER_PAR_T3IN_QSPI         (0x4000)
#define MCF_GPIO_PAR_TIMER_PAR_T3IN_UART2        (0x8000)
#define MCF_GPIO_PAR_TIMER_PAR_T3IN_T3IN         (0xC000)
#define MCF_GPIO_PAR_TIMER_PAR_T2IN_GPIO         (0x0000)
#define MCF_GPIO_PAR_TIMER_PAR_T2IN_T2OUT        (0x1000)
#define MCF_GPIO_PAR_TIMER_PAR_T2IN_DMA          (0x2000)
#define MCF_GPIO_PAR_TIMER_PAR_T2IN_T2IN         (0x3000)
#define MCF_GPIO_PAR_TIMER_PAR_T1IN_GPIO         (0x0000)
#define MCF_GPIO_PAR_TIMER_PAR_T1IN_T1OUT        (0x0400)
#define MCF_GPIO_PAR_TIMER_PAR_T1IN_DMA          (0x0800)
#define MCF_GPIO_PAR_TIMER_PAR_T1IN_T1IN         (0x0C00)
#define MCF_GPIO_PAR_TIMER_PAR_T0IN_GPIO         (0x0000)
#define MCF_GPIO_PAR_TIMER_PAR_T0IN_DMA          (0x0200)
#define MCF_GPIO_PAR_TIMER_PAR_T0IN_T0IN         (0x0300)
#define MCF_GPIO_PAR_TIMER_PAR_T3OUT_GPIO        (0x0000)
#define MCF_GPIO_PAR_TIMER_PAR_T3OUT_QSPI        (0x0040)
#define MCF_GPIO_PAR_TIMER_PAR_T3OUT_UART2       (0x0080)
#define MCF_GPIO_PAR_TIMER_PAR_T3OUT_T3OUT       (0x00C0)
#define MCF_GPIO_PAR_TIMER_PAR_T2OUT_GPIO        (0x0000)
#define MCF_GPIO_PAR_TIMER_PAR_T2OUT_DMA         (0x0020)
#define MCF_GPIO_PAR_TIMER_PAR_T2OUT_T2OUT       (0x0030)
#define MCF_GPIO_PAR_TIMER_PAR_T1OUT_GPIO        (0x0000)
#define MCF_GPIO_PAR_TIMER_PAR_T1OUT_DMA         (0x0008)
#define MCF_GPIO_PAR_TIMER_PAR_T1OUT_T1OUT       (0x000C)
#define MCF_GPIO_PAR_TIMER_PAR_T0OUT_GPIO        (0x0000)
#define MCF_GPIO_PAR_TIMER_PAR_T0OUT_DMA         (0x0002)
#define MCF_GPIO_PAR_TIMER_PAR_T0OUT_T0OUT       (0x0003)

/* Bit definitions and macros for MCF_GPIO_PAR_ETPU */
#define MCF_GPIO_PAR_ETPU_PAR_LTPU_ODIS          (0x01)
#define MCF_GPIO_PAR_ETPU_PAR_UTPU_ODIS          (0x02)
#define MCF_GPIO_PAR_ETPU_PAR_TCRCLK             (0x04)

/* Bit definitions and macros for MCF_GPIO_DSCR_EIM */
#define MCF_GPIO_DSCR_EIM_DSCR_EIM0              (0x01)
#define MCF_GPIO_DSCR_EIM_DSCR_EIM1              (0x10)

/* Bit definitions and macros for MCF_GPIO_DSCR_ETPU */
#define MCF_GPIO_DSCR_ETPU_DSCR_ETPU_7_0         (0x01)
#define MCF_GPIO_DSCR_ETPU_DSCR_ETPU_15_8        (0x04)
#define MCF_GPIO_DSCR_ETPU_DSCR_ETPU_23_16       (0x10)
#define MCF_GPIO_DSCR_ETPU_DSCR_ETPU_31_24       (0x40)

/* Bit definitions and macros for MCF_GPIO_DSCR_FECI2C */
#define MCF_GPIO_DSCR_FECI2C_DSCR_I2C            (0x01)
#define MCF_GPIO_DSCR_FECI2C_DSCR_FEC            (0x10)

/* Bit definitions and macros for MCF_GPIO_DSCR_UART */
#define MCF_GPIO_DSCR_UART_DSCR_UART0            (0x01)
#define MCF_GPIO_DSCR_UART_DSCR_UART1            (0x04)
#define MCF_GPIO_DSCR_UART_DSCR_UART2            (0x10)
#define MCF_GPIO_DSCR_UART_DSCR_IRQ              (0x40)

/* Bit definitions and macros for MCF_GPIO_DSCR_QSPI */
#define MCF_GPIO_DSCR_QSPI_DSCR_QSPI             (0x01)

/* Bit definitions and macros for MCF_GPIO_DSCR_TIMER */
#define MCF_GPIO_DSCR_TIMER_DSCR_TIMER           (0x01)

/********************************************************************/

#endif /* __MCF523X_GPIO_H__ */
