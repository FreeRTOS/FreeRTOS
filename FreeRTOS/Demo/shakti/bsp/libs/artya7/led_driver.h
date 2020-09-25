/***************************************************************************
 * Project           		    : shakti devt board
 * Name of the file	            : led_driver.h
 * Brief Description of file        : Header file for leds
 * Name of Author    	            : Kotteeswaran
 * Email ID                         : kottee.1@gmail.com

 Copyright (C) 2019  IIT Madras. All rights reserved.

 This program is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program.  If not, see <https://www.gnu.org/licenses/>.

 ***************************************************************************/
 /**
 * @file led_driver.h
 * @brief  All the definitions are very specific to ARTY A7 (35T & 100T) boards
 */

#ifndef LED_DRIVER_H
#define LED_DRIVER_H

#include "platform.h" //Contains arty a7 gpio definitions.
#include "gpio.h"  //Contains the methods to Access GPIOs

#if defined(ARTIX7_35T) || defined(ARTIX7_100T)
/*! RGB LED 0 defines */
#define LED0_R GPIO16 
#define LED0_G GPIO17
#define LED0_B GPIO18

/*! RGB LED 1 defines */
#define LED1_R GPIO19
#define LED1_G GPIO20
#define LED1_B GPIO21

/*! Normal LED 1 defines */
#define LED2 GPIO22

/*! Normal LED 2 defines */
#define LED3 GPIO23


/*! Combined RGB LED defines */
#define RGB0 (LED0_R | LED0_G | LED0_B )
#define RGB1 (LED1_R | LED1_G | LED1_B )

/*! Combined Normal LED defines */
#define NORMAL_LEDS ( LED2 | LED3 )
#define RGB_LEDS ( RGB0 | RGB1 )

/*! Combines ALL LED defines */
#define ALL_LEDS (RGB_LEDS | NORMAL_LEDS)


/*! Control for all LEDS */
#define NORMAL_LED0 0
#define NORMAL_LED1 1

#define RGB_LED0 0
#define RGB_LED1 1

// function prototype
void configure_ledx(unsigned long pin_cntrl);
void configure_rgb_ledx(unsigned char led_no);
void configure_normal_leds();
void configure_rgb_leds();
void configure_all_leds();
void turn_on_ledx(unsigned long pin_cntrl);
void turn_off_ledx(unsigned long pin_cntrl);
void turn_on_normal_leds();
void turn_off_normal_leds();
void turn_on_rgb_ledx(unsigned char led_no);
void turn_off_rgb_ledx(unsigned char led_no);
void turn_on_rgb_leds();
void turn_off_rgb_leds();
void turn_on_all_leds();
void turn_off_all_leds();
void toggle_ledx(unsigned long pin_cntrl, unsigned long delay1, unsigned long delay2);
void toggle_normal_leds( unsigned long delay1, unsigned long delay2 );
void toggle_rgb_leds( unsigned long delay1, unsigned long delay2 );
void toggle_all_leds( unsigned long delay1, unsigned long delay2);


#endif
#endif
