/*
 * A simple demo for NTP using FreeRTOS+TCP
 */

#ifndef NTPDEMO_H

#define NTPDEMO_H

void vStartNTPTask( uint16_t usTaskStackSize, UBaseType_t uxTaskPriority );

#endif