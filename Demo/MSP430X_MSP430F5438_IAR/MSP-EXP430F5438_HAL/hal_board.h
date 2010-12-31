/**********************************************************************//**
    Filename: hal_board.h

    Copyright 2010 Texas Instruments, Inc.
***************************************************************************/
#ifndef HAL_BOARD_H
#define HAL_BOARD_H

#define LED_PORT_DIR      P1DIR
#define LED_PORT_OUT      P1OUT
#define LED_1             BIT0
#define LED_2             BIT1

#define CLK_PORT_DIR      P11DIR //outputs clocks to testpoints
#define CLK_PORT_OUT      P11OUT
#define CLK_PORT_SEL      P11SEL

/*----------------------------------------------------------------
 *                  Function Prototypes
 *----------------------------------------------------------------
 */
static void halBoardGetSystemClockSettings(unsigned char systemClockSpeed, 
                                           unsigned char *setDcoRange,
                                           unsigned char *setVCore,
                                           unsigned int  *setMultiplier);

extern void halBoardOutputSystemClock(void);
extern void halBoardStopOutputSystemClock(void);
extern void halBoardInit(void);

#endif /* HAL_BOARD_H */
