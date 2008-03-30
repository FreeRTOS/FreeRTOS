#define TESTAPP_GEN

/* $Id: xgpio_tapp_example.c,v 1.1 2007/05/15 06:49:42 mta Exp $ */
/******************************************************************************
*
*       XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION "AS IS"
*       AS A COURTESY TO YOU, SOLELY FOR USE IN DEVELOPING PROGRAMS AND
*       SOLUTIONS FOR XILINX DEVICES.  BY PROVIDING THIS DESIGN, CODE,
*       OR INFORMATION AS ONE POSSIBLE IMPLEMENTATION OF THIS FEATURE,
*       APPLICATION OR STANDARD, XILINX IS MAKING NO REPRESENTATION
*       THAT THIS IMPLEMENTATION IS FREE FROM ANY CLAIMS OF INFRINGEMENT,
*       AND YOU ARE RESPONSIBLE FOR OBTAINING ANY RIGHTS YOU MAY REQUIRE
*       FOR YOUR IMPLEMENTATION.  XILINX EXPRESSLY DISCLAIMS ANY
*       WARRANTY WHATSOEVER WITH RESPECT TO THE ADEQUACY OF THE
*       IMPLEMENTATION, INCLUDING BUT NOT LIMITED TO ANY WARRANTIES OR
*       REPRESENTATIONS THAT THIS IMPLEMENTATION IS FREE FROM CLAIMS OF
*       INFRINGEMENT, IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
*       FOR A PARTICULAR PURPOSE.
*
*       (c) Copyright 2005 Xilinx Inc.
*       All rights reserved.
*
******************************************************************************/
/*****************************************************************************/
/**
* @file xgpio_tapp_example.c
*
* This file contains a example for using GPIO hardware and driver.
* This example assumes that there is a UART Device or STDIO Device in the
* hardware system.
*
* This example can be run on the Xilinx ML300 board with either the PowerPC or
* the MicroBlaze processor using the Prototype Pins & LEDs of the board
* connected to the GPIO and the Push Buttons connected.
*
* @note
*
* None
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a sv   04/15/05 Initial release for TestApp integration.
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xparameters.h"
#include "xgpio.h"
#include "stdio.h"
#include "xstatus.h"

/************************** Constant Definitions ****************************/

/*
 * The following constant is used to wait after an LED is turned on to make
 * sure that it is visible to the human eye.  This constant might need to be
 * tuned for faster or slower processor speeds.
 */
#define LED_DELAY     1000000

/* following constant is used to determine which channel of the GPIO is
 * used if there are 2 channels supported in the GPIO.
 */
#define LED_CHANNEL 1

#define LED_MAX_BLINK   0x1     /* Number of times the LED Blinks */

#define GPIO_BITWIDTH   16      /* This is the width of the GPIO */

#define printf xil_printf       /* A smaller footprint printf */

/*
 * The following constants map to the XPAR parameters created in the
 * xparameters.h file. They are defined here such that a user can easily
 * change all the needed parameters in one place.
 */
#ifndef TESTAPP_GEN
#define GPIO_OUTPUT_DEVICE_ID  XPAR_LEDS_4BIT_DEVICE_ID
#define GPIO_INPUT_DEVICE_ID   XPAR_LEDS_4BIT_DEVICE_ID
#endif /* TESTAPP_GEN */

/**************************** Type Definitions ******************************/


/***************** Macros (Inline Functions) Definitions *******************/


/************************** Function Prototypes ****************************/

XStatus GpioOutputExample(Xuint16 DeviceId, Xuint32 GpioWidth);

XStatus GpioInputExample(Xuint16 DeviceId, Xuint32 *DataRead);

void GpioDriverHandler(void *CallBackRef);



/************************** Variable Definitions **************************/

/*
 * The following are declared globally so they are zeroed and so they are
 * easily accessible from a debugger
 */
XGpio GpioOutput;   /* The driver instance for GPIO Device configured as O/P */
XGpio GpioInput;    /* The driver instance for GPIO Device configured as I/P */


/*****************************************************************************/
/**
* Main function to call the example.This function is not included if the
* example is generated from the TestAppGen test tool.
*
* @param    None
*
* @return   XST_SUCCESS if successful, XST_FAILURE if unsuccessful
*
* @note     None
*
******************************************************************************/
#ifndef TESTAPP_GEN
int main(void)
{
    XStatus Status;
    Xuint32 InputData;

    Status = GpioOutputExample(GPIO_OUTPUT_DEVICE_ID, GPIO_BITWIDTH);
    if (Status != XST_SUCCESS)
    {
        return XST_FAILURE;
    }

    Status = GpioInputExample(GPIO_INPUT_DEVICE_ID, &InputData);
    if (Status != XST_SUCCESS)
    {
        return XST_FAILURE;
    }

    printf("Data read from GPIO Input is  0x%x \n", (int)InputData);

    return XST_SUCCESS;
}
#endif


/*****************************************************************************/
/**
*
* This function does a minimal test on the GPIO device configured as OUTPUT
* and driver as a  example.
*
*
* @param    DeviceId is the XPAR_<GPIO_instance>_DEVICE_ID value from
*           xparameters.h
* @param    GpioWidth is the width of the GPIO
*
* @return   XST_SUCCESS if successful, XST_FAILURE if unsuccessful
*
* @note     None
*
****************************************************************************/
XStatus GpioOutputExample(Xuint16 DeviceId, Xuint32 GpioWidth)
{
    Xuint32 Data;
    volatile int Delay;
    Xuint32 LedBit;
    Xuint32 LedLoop;
    XStatus Status;

    /*
     * Initialize the GPIO driver so that it's ready to use,
     * specify the device ID that is generated in xparameters.h
     */
    Status = XGpio_Initialize(&GpioOutput, DeviceId);
    if (Status != XST_SUCCESS)
    {
        return XST_FAILURE;
    }


    /*
     * Set the direction for all signals to be outputs
     */
    XGpio_SetDataDirection(&GpioOutput, LED_CHANNEL, 0x0);

    /*
     * Set the GPIO outputs to low
     */
    XGpio_DiscreteWrite(&GpioOutput, LED_CHANNEL, 0x0);

    for (LedBit = 0x0; LedBit < GpioWidth; LedBit++)
    {

        for (LedLoop = 0; LedLoop < LED_MAX_BLINK; LedLoop++)
        {

            /*
             * Set the GPIO Output to High
             */
            XGpio_DiscreteWrite(&GpioOutput, LED_CHANNEL, 1 << LedBit);

#ifndef __SIM__
            /*
             * Wait a small amount of time so the LED is visible
             */
            for (Delay = 0; Delay < LED_DELAY; Delay++);

#endif
            /*
             * Read the state of the data so that it can be  verified
             */
            /* Data = XGpio_DiscreteRead(&GpioOutput, LED_CHANNEL); */


            /*
             * If the data read back is not the same as the data
             * written then return FAILURE
             */
            /*if (Data != (1 << LedBit))
            {
                return XST_FAILURE;
            }*/


            /*
             * Clear the GPIO Output
             */
            XGpio_DiscreteClear(&GpioOutput, LED_CHANNEL, 1 << LedBit);


            /*
             * Read the state of the data so that it can be verified
             */
            /* Data = XGpio_DiscreteRead(&GpioOutput, LED_CHANNEL);*/


            /*
             * If the data read back is not the same as the data
             * written then return FAILURE
             */
            /* if (Data & ( 1 << LedBit))
            {
                return XST_FAILURE;
            }*/


#ifndef __SIM__
            /*
             * Wait a small amount of time so the LED is visible
             */
            for (Delay = 0; Delay < LED_DELAY; Delay++);
#endif

        }

    }

    return XST_SUCCESS;

}


/******************************************************************************/
/**
*
* This function  performs a test on the GPIO driver/device with the GPIO
* configured as INPUT
*
* @param    DeviceId is the XPAR_<GPIO_instance>_DEVICE_ID value from
*           xparameters.h
* @param    DataRead is the pointer where the data read from GPIO Input is
*           returned
*
* @return   XST_SUCCESS if the Test is successful, otherwise XST_FAILURE
*
* @note     None.
*
******************************************************************************/
XStatus GpioInputExample(Xuint16 DeviceId, Xuint32 *DataRead)
{
    XStatus Status;

    /*
     * Initialize the GPIO driver so that it's ready to use,
     * specify the device ID that is generated in xparameters.h
     */
    Status = XGpio_Initialize(&GpioInput, DeviceId);
    if (Status != XST_SUCCESS)
    {
        return XST_FAILURE;
    }

    /*
     * Set the direction for all signals to be inputs
     */
    XGpio_SetDataDirection(&GpioInput, LED_CHANNEL, 0xFFFFFFFF);

    /*
     * Read the state of the data so that it can be  verified
     */
    *DataRead = XGpio_DiscreteRead(&GpioInput, LED_CHANNEL);

    return XST_SUCCESS;

}


