#ifndef _LCDTEST_H
#define _LCDTEST_H

#include "FreeRTOS.h"
#include "task.h"

#include "lcdcontroller.h"

/*
 * The task that writes to the LCD.
 */
void vLCDTask( void *pvParameters );

#endif
