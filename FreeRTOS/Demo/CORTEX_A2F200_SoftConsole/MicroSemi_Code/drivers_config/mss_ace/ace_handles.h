/*****************************************************************************
* (c) Copyright  Actel Corporation. All rights reserved.
*
*ACE configuration .h file
*Created by Actel MSS_ACE Configurator Fri Dec 17 12:12:19 2010
*
*/

#ifndef ACE_HANDLES_H
#define ACE_HANDLES_H


/*-----------------------------------------------------------------------------
*Analog input channel handles
*---------------------------------------------------------------------------*/
typedef enum {
    CurrentMonitor_0 = 0,
    VoltageMonitor_0,
    TemperatureMonitor_0,
    NB_OF_ACE_CHANNEL_HANDLES
} ace_channel_handle_t;

/*-----------------------------------------------------------------------------
*Flag Handles
*---------------------------------------------------------------------------*/
typedef enum {
    NB_OF_ACE_FLAG_HANDLES = 0
} ace_flag_handle_t;

/*-----------------------------------------------------------------------------
*Procedure Handles
*---------------------------------------------------------------------------*/
typedef enum {
    ADC0_MAIN = 0,
    ADC1_MAIN,
    ADC2_MAIN,
    NB_OF_ACE_PROCEDURE_HANDLES
} ace_procedure_handle_t;


#endif
