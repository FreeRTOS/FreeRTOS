/** @file gio.h
*   @brief GIO Driver Definition File
*   @date 11.August.2009
*   @version 1.01.000
*   
*/

/* (c) Texas Instruments 2009-2010, All rights reserved. */


#ifndef __GIO_H__
#define __GIO_H__

/** @struct gioBase
*   @brief GIO Base Register Definition
*
*   This structure is used to access the GIO module egisters.
*/
/** @typedef gioBASE_t
*   @brief GIO Register Frame Type Definition
*
*   This type is used to access the GIO Registers.
*/
typedef volatile struct gioBase
{
    unsigned GCR0;      /**< 0x0000: Global Control Register */
    unsigned PWDN;      /**< 0x0004: Power Down Register */
    unsigned INTDET;    /**< 0x0008: Interrupt Detect Regsiter*/
    unsigned POL;       /**< 0x000C: Interrupt Polarity Register */
    unsigned INTENASET; /**< 0x0010: Interrupt Enable Set Register */
    unsigned INTENACLR; /**< 0x0014: Interrupt Enable Clear Register */
    unsigned LVLSET;    /**< 0x0018: Interrupt Priority Set Register */
    unsigned LVLCLR;    /**< 0x001C: Interrupt Priority Clear Register */
    unsigned FLG;       /**< 0x0020: Interrupt Flag Register */
    unsigned OFFSET0;   /**< 0x0024: Interrupt Offset A Register */
    unsigned OFFSET1;   /**< 0x0028: Interrupt Offset B Register */
} gioBASE_t;


/** @struct gioPort
*   @brief GIO Port Register Definition
*/
/** @typedef gioPORT_t
*   @brief GIO Port Register Type Definition
*
*   This type is used to access the GIO Port Registers.
*/
typedef volatile struct gioPort
{
    unsigned DIR;    /**< 0x0000: Data Direction Register */
    unsigned DIN;    /**< 0x0004: Data Input Register */
    unsigned DOUT;   /**< 0x0008: Data Output Register */
    unsigned DSET;   /**< 0x000C: Data Output Set Register */
    unsigned DCLR;   /**< 0x0010: Data Output Clear Register */
    unsigned PDR;    /**< 0x0014: Open Drain Regsiter */
    unsigned PULDIS; /**< 0x0018: Pullup Disable Register */
    unsigned PSL;    /**< 0x001C: Pull Up/Down Selection Register */
} gioPORT_t;


/** @def gioREG
*   @brief GIO Register Frame Pointer
*
*   This pointer is used by the GIO driver to access the gio module registers.
*/
#define gioREG   ((gioBASE_t *)0xFFF7BC00U)

/** @def gioPORTA
*   @brief GIO Port (A) Register Pointer
*
*   Pointer used by the GIO driver to access PORTA
*/
#define gioPORTA ((gioPORT_t *)0xFFF7BC34U)

/** @def gioPORTB
*   @brief GIO Port (B) Register Pointer
*
*   Pointer used by the GIO driver to access PORTB
*/
#define gioPORTB ((gioPORT_t *)0xFFF7BC54U)


/* GIO Interface Functions */
void gioInit(void);
void gioSetDirection(gioPORT_t *port, unsigned dir);
void gioSetBit(gioPORT_t *port, unsigned bit, unsigned value);
void gioSetPort(gioPORT_t *port, unsigned value);
unsigned gioGetBit(gioPORT_t *port, unsigned bit);
unsigned gioGetPort(gioPORT_t *port);
void gioEnableNotification(unsigned bit);
void gioDisableNotification(unsigned bit);
void gioNotification(int bit);

#endif
