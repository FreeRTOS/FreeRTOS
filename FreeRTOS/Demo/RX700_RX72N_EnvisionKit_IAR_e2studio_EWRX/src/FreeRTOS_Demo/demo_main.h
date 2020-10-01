#ifndef DEMO_MAIN_H
#define DEMO_MAIN_H

/* Set mainCREATE_SIMPLE_BLINKY_DEMO_ONLY to one to run the simple blinky demo,
or 0 to run the more comprehensive test and demo application. */
#define mainCREATE_SIMPLE_BLINKY_DEMO_ONLY	0

/* demo_main() is placed in the src/frtos_startup/freertos_start.c and it calls
main_blinky() or main_full() according to the mainCREATE_SIMPLE_BLINKY_DEMO_ONLY
setting. */
extern void demo_main( void );

#endif
