/*
 * File:		mcf52xx.c
 * Purpose:		Source to select CF derivative
 *
 * Notes:
 * 
 * License:     All software covered by license agreement in -
 *              docs/Freescale_Software_License.pdf
 */
/********************************************************************/

#include "common.h"

/********************************************************************/
/*
 * Pause for the specified number of micro-seconds.
 * Uses DTIM3 as a timer
 */
void
cpu_pause(int usecs)
{
    /* Enable the DMA Timer 3 */
    MCF_DTIM3_DTRR = (vuint32)(usecs - 1);
    MCF_DTIM3_DTER = MCF_DTIM_DTER_REF;
    MCF_DTIM3_DTMR = 0
        | MCF_DTIM_DTMR_PS(SYSTEM_CLOCK)
        | MCF_DTIM_DTMR_FRR
        | MCF_DTIM_DTMR_CLK_DIV1
        | MCF_DTIM_DTMR_RST;

    while ((MCF_DTIM3_DTER & MCF_DTIM_DTER_REF) == 0) 
    {};
    
    /* Disable the timer */
    MCF_DTIM3_DTMR = 0;
}

/********************************************************************/
void
board_handle_interrupt (int vector)
{
    switch (vector)
    {
        case 65: /* Eport Interrupt 1 */
            printf("SW2\n");
            MCF_EPORT_EPFR = MCF_EPORT_EPFR_EPF1;
            break;
        case 69: /* Eport Interrupt 5 */
            printf("SW1\n");
            MCF_EPORT_EPFR = MCF_EPORT_EPFR_EPF5;
            break;
        case 71: /* Eport Interrupt 7 */
            printf("ABORT\n");
            MCF_EPORT_EPFR = MCF_EPORT_EPFR_EPF7;
            break;
        case 66: /* Eport Interrupt 2 */
        case 67: /* Eport Interrupt 3 */
        case 68: /* Eport Interrupt 4 */
        case 70: /* Eport Interrupt 6 */
        default:
            MCF_EPORT_EPFR = (uint8)(0x01 << (vector - 64));
            printf("Edge Port Interrupt #%d\n",vector - 64);
            break;
    }
}
/********************************************************************/

/********************************************************************/
void
cpu_handle_interrupt (int vector)
{
    if (vector < 64 || vector > 192)
        return;
    
    if (vector >= 64 && vector <= 71)
        board_handle_interrupt(vector);
    else
        printf("User Defined Vector #%d\n",vector);
}
/********************************************************************/

