/** @file gio.c 
*   @brief GIO Driver Inmplmentation File
*   @date 10.June.2010
*   @version 1.01.000
*
*/

/* (c) Texas Instruments 2009-2010, All rights reserved. */


#include "gio.h"


/** @fn void gioInit(void)
*   @brief Initializes the GIO Driver
*
*   This function initializes the GIO module and set the GIO ports 
*   to the inital values.
*/
void gioInit(void)
{
    /** bring GIO module out of reset */
    gioREG->GCR0      = 1;
    gioREG->INTENACLR = 0xFF;
    gioREG->LVLCLR    = 0xFF;              

    /** @b initalise @b Port @b A */

    /** - Port A output values */
    gioPORTA->DOUT =  0        /* Bit 0 */
                   | (0 << 1)  /* Bit 1 */
                   | (0 << 2)  /* Bit 2 */
                   | (0 << 3)  /* Bit 3 */
                   | (0 << 4)  /* Bit 4 */
                   | (0 << 5)  /* Bit 5 */
                   | (0 << 6)  /* Bit 6 */
                   | (0 << 7); /* Bit 7 */

    /** - Port A direction */
    gioPORTA->DIR  =  1        /* Bit 0 */
                   | (1 << 1)  /* Bit 1 */
                   | (0 << 2)  /* Bit 2 */
                   | (0 << 3)  /* Bit 3 */
                   | (0 << 4)  /* Bit 4 */
                   | (0 << 5)  /* Bit 5 */
                   | (0 << 6)  /* Bit 6 */
                   | (0 << 7); /* Bit 7 */

    /** - Port A open drain enable */
    gioPORTA->PDR  =  0        /* Bit 0 */
                   | (0 << 1)  /* Bit 1 */
                   | (0 << 2)  /* Bit 2 */
                   | (0 << 3)  /* Bit 3 */
                   | (0 << 4)  /* Bit 4 */
                   | (0 << 5)  /* Bit 5 */
                   | (0 << 6)  /* Bit 6 */
                   | (0 << 7); /* Bit 7 */

    /** - Port A pullup / pulldown selection */
    gioPORTA->PSL  =  0        /* Bit 0 */
                   | (0 << 1)  /* Bit 1 */
                   | (0 << 2)  /* Bit 2 */
                   | (0 << 3)  /* Bit 3 */
                   | (0 << 4)  /* Bit 4 */
                   | (0 << 5)  /* Bit 5 */
                   | (0 << 6)  /* Bit 6 */
                   | (0 << 7); /* Bit 7 */

    /** - Port A pullup / pulldown enable*/
    gioPORTA->PULDIS  =  0        /* Bit 0 */
                      | (0 << 1)  /* Bit 1 */
                      | (0 << 2)  /* Bit 2 */
                      | (0 << 3)  /* Bit 3 */
                      | (0 << 4)  /* Bit 4 */
                      | (0 << 5)  /* Bit 5 */
                      | (0 << 6)  /* Bit 6 */
                      | (0 << 7); /* Bit 7 */

    /** @b initalise @b Port @b B */

    /** - Port B output values */
    gioPORTB->DOUT =  0        /* Bit 0 */
                   | (0 << 1)  /* Bit 1 */
                   | (0 << 2)  /* Bit 2 */
                   | (0 << 3)  /* Bit 3 */
                   | (0 << 4)  /* Bit 4 */
                   | (0 << 5)  /* Bit 5 */
                   | (0 << 6)  /* Bit 6 */
                   | (0 << 7); /* Bit 7 */

    /** - Port B direction */
    gioPORTB->DIR  =  0        /* Bit 0 */
                   | (0 << 1)  /* Bit 1 */
                   | (0 << 2)  /* Bit 2 */
                   | (0 << 3)  /* Bit 3 */
                   | (0 << 4)  /* Bit 4 */
                   | (0 << 5)  /* Bit 5 */
                   | (0 << 6)  /* Bit 6 */
                   | (0 << 7); /* Bit 7 */

    /** - Port B open drain enable */
    gioPORTB->PDR  =  0        /* Bit 0 */
                   | (0 << 1)  /* Bit 1 */
                   | (0 << 2)  /* Bit 2 */
                   | (0 << 3)  /* Bit 3 */
                   | (0 << 4)  /* Bit 4 */
                   | (0 << 5)  /* Bit 5 */
                   | (0 << 6)  /* Bit 6 */
                   | (0 << 7); /* Bit 7 */

    /** - Port B pullup / pulldown selection */
    gioPORTB->PSL  =  0        /* Bit 0 */
                   | (0 << 1)  /* Bit 1 */
                   | (0 << 2)  /* Bit 2 */
                   | (0 << 3)  /* Bit 3 */
                   | (0 << 4)  /* Bit 4 */
                   | (0 << 5)  /* Bit 5 */
                   | (0 << 6)  /* Bit 6 */
                   | (0 << 7); /* Bit 7 */

    /** - Port B pullup / pulldown enable*/
    gioPORTB->PULDIS  =  0        /* Bit 0 */
                      | (0 << 1)  /* Bit 1 */
                      | (0 << 2)  /* Bit 2 */
                      | (0 << 3)  /* Bit 3 */
                      | (0 << 4)  /* Bit 4 */
                      | (0 << 5)  /* Bit 5 */
                      | (0 << 6)  /* Bit 6 */
                      | (0 << 7); /* Bit 7 */


    /** @b initalise @b interrupts */

    /** - interrupt polarity */
    gioREG->POL =  0        /* Bit 0 */
                | (0 << 1)  /* Bit 1 */
                | (0 << 2)  /* Bit 2 */
                | (0 << 3)  /* Bit 3 */
                | (0 << 4)  /* Bit 4 */
                | (0 << 5)  /* Bit 5 */
                | (0 << 6)  /* Bit 6 */
                | (0 << 7); /* Bit 7 */

    /** - interrupt level */
    gioREG->LVLSET =  0        /* Bit 0 */
                   | (0 << 1)  /* Bit 1 */
                   | (0 << 2)  /* Bit 2 */
                   | (0 << 3)  /* Bit 3 */
                   | (0 << 4)  /* Bit 4 */
                   | (0 << 5)  /* Bit 5 */
                   | (0 << 6)  /* Bit 6 */
                   | (0 << 7); /* Bit 7 */


    /** - clear all pending interrupts */
    gioREG->FLG = 0xFF;

    /** - enable interrupts */
    gioREG->INTENASET =  0        /* Bit 0 */
                      | (0 << 1)  /* Bit 1 */
                      | (0 << 2)  /* Bit 2 */
                      | (0 << 3)  /* Bit 3 */
                      | (0 << 4)  /* Bit 4 */
                      | (0 << 5)  /* Bit 5 */
                      | (0 << 6)  /* Bit 6 */
                      | (0 << 7); /* Bit 7 */
}


/** @fn void gioSetDirection(gioPORT_t *port, unsigned dir)
*   @brief Set Port Direction
*   @param[in] port pointer to GIO port:
*              - gioPORTA: PortA pointer
*              - gioPORTB: PortB pointer
*   @param[in] dir value to write to DIR register
*
*   Set the direction of GIO pins at runtime.
*/
void gioSetDirection(gioPORT_t *port, unsigned dir)
{
    port->DIR = dir;
}


/** @fn void gioSetBit(gioPORT_t *port, unsigned bit, unsigned value)
*   @brief Write Bit
*   @param[in] port pointer to GIO port:
*              - gioPORTA: PortA pointer
*              - gioPORTB: PortB pointer
*   @param[in] bit number 0-7 that specifies the bit to be written to.
*              - 0: LSB
*              - 7: MSB
*   @param[in] value binrary value to write to bit
*
*   Writes a value to the specified pin of the given GIO port
*/
void gioSetBit(gioPORT_t *port, unsigned bit, unsigned value)
{
    if (value)
    {
        port->DSET = 1 << bit;
    }
    else
    {
        port->DCLR = 1 << bit;
    }
}


/** @fn void gioSetPort(gioPORT_t *port, unsigned value)
*   @brief Write Port Value
*   @param[in] port pointer to GIO port:
*              - gioPORTA: PortA pointer
*              - gioPORTB: PortB pointer
*   @param[in] value value to write to port
*
*   Writes a value to all pin of a given GIO port
*/
void gioSetPort(gioPORT_t *port, unsigned value)
{
    port->DOUT = value;
}


/** @fn unsigned gioGetBit(gioPORT_t *port, unsigned bit)
*   @brief Read Bit
*   @param[in] port pointer to GIO port:
*              - gioPORTA: PortA pointer
*              - gioPORTB: PortB pointer
*   @param[in] bit number 0-7 that specifies the bit to be written to.
*              - 0: LSB
*              - 7: MSB
*
*   Reads a the current value from the specified pin of the given GIO port
*/
unsigned gioGetBit(gioPORT_t *port, unsigned bit)
{
    return (port->DIN >> bit) & 1U;
}


/** @fn unsigned gioGetPort(gioPORT_t *port)
*   @brief Read Port Value
*   @param[in] port pointer to GIO port:
*              - gioPORTA: PortA pointer
*              - gioPORTB: PortB pointer
*
*   Reads a the current value of a given GIO port
*/
unsigned gioGetPort(gioPORT_t *port)
{
    return port->DIN;
}


/** @fn void gioEnableNotification(unsigned bit)
*   @brief Enable Interrupt
*   @param[in] bit interrupt pin to enable
*              - 0: LSB
*              - 7: MSB
*
*   Enables an innterrupt pin of PortA
*/
void gioEnableNotification(unsigned bit)
{
    gioREG->INTENASET = 1 << bit;
}


/** @fn void gioDisableNotification(unsigned bit)
*   @brief Disable Interrupt
*   @param[in] bit interrupt pin to enable
*              - 0: LSB
*              - 7: MSB
*
*   Disables an innterrupt pin of PortA
*/
void gioDisableNotification(unsigned bit)
{
    gioREG->INTENACLR = 1 << bit;
}
