// Copyright (c) 2020, XMOS Ltd, All rights reserved

#include <stdint.h>
#include <platform.h>

out port p_led_0_4 = PORT_LEDS;

#define MAX(a,b) ((a) > (b) ? (a) : (b))

#define LED_COUNT 4

void led_driver(uint16_t led_value)
{
	p_led_0_4 <: 0;
	p_led_0_4 <: (unsigned)( led_value & 0x000F );
}
