#ifndef _LPC18XX_UTILS_H
#define _LPC18XX_UTILS_H

#include "lpc_types.h"
extern uint32_t msec;
extern volatile uint32_t u32Milliseconds;
void SysTick_Handler (void);
int timer_delay_us( int cnt);
int timer_delay_ms( int cnt);
#endif
