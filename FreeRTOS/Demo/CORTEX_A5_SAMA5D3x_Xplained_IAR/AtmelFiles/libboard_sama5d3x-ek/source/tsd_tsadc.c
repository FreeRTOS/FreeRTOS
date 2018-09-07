/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2013, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */
 
/** \file */

/*----------------------------------------------------------------------------
 *         Headers
 *----------------------------------------------------------------------------*/

#include <board.h>

#include <string.h>

#ifdef REG_ADC_TSMR
/** \addtogroup tsd_module
 *@{
 */

/*----------------------------------------------------------------------------
 *         Local definitions
 *----------------------------------------------------------------------------*/

/** SWAP X & Y */
#define TS_XY_SWAP

/** Status that used for touchscreen */
#define TS_STATUSES ( ADC_ISR_PENS | ADC_ISR_PEN | ADC_ISR_NOPEN \
                    | ADC_ISR_XRDY | ADC_ISR_YRDY | ADC_ISR_PRDY )

/*----------------------------------------------------------------------------
 *         Local types
 *----------------------------------------------------------------------------*/

/** X value is ready */
#define TS_X_RDY        (1 << 0)
/** Y value is ready */
#define TS_Y_RDY        (1 << 1)
/** Pressure value is ready */
#define TS_P_RDY        (1 << 2)
/** Pen status */
#define TS_PEN_STAT     (1 << 7)
/** All data is ready (X,Y & P) */
#define TS_DATA_RDY     (TS_X_RDY|TS_Y_RDY|TS_P_RDY)

/*----------------------------------------------------------------------------
 *         Local variables
 *----------------------------------------------------------------------------*/

/** Raw register value */
static uint32_t dwRaw[3];
/** Touchscreen data sampling results */
static uint32_t dwTsData[3];
/** Last Touchscreen sampling results */
static uint32_t dwLastTsData[3];
/** Touchscreen data ready */
static uint8_t  bTsFlags = 0;

/*----------------------------------------------------------------------------
 *         External functions
 *----------------------------------------------------------------------------*/

extern uint32_t TSD_GetRaw(uint32_t i);

/**
 * Return raw register value.
 */
uint32_t TSD_GetRaw(uint32_t i)
{
    return dwRaw[i];
}

/*----------------------------------------------------------------------------
 *        Local definitions
 *----------------------------------------------------------------------------*/

/**
 * Interrupt handler for the TouchScreen.
 * Handles pen press, pen move and pen release events
 * by invoking three callback functions.
 */
void TSD_Handler(uint32_t dwAdcStatus)
{
    Adc *pAdc = ADC;

    uint32_t status;

    /* TSADC status */
    status  = dwAdcStatus;
    status &= /*ADC_GetItMask(pAdc) &*/ TS_STATUSES;
    if (status == 0)    return;

    /* Pen released */
    if (status & ADC_ISR_NOPEN)
    {
        if ((bTsFlags & TS_PEN_STAT) == 0)
        {
            /* Register last data */
            memcpy(dwLastTsData, dwTsData, sizeof(dwTsData));
            /* Invoke PenReleased callback */
            if (TSDCom_IsCalibrationOk())
                TSD_PenReleased(dwTsData[0], dwTsData[1]);
        }
        bTsFlags = 0;
        /* Stop periodic trigger & enable pen */
        ADC_SetTsAverage(pAdc, ADC_TSMR_TSAV_NO_FILTER);
        ADC_SetTsDebounce(pAdc, BOARD_TOUCHSCREEN_DEBOUNCE);
        ADC_SetTriggerMode(pAdc, ADC_TRGR_TRGMOD_PEN_TRIG);
        /* Disable pen release detect */
        ADC_DisableIt(pAdc, ADC_IDR_NOPEN);
        /* Enable pen press detect */
        ADC_EnableIt(pAdc, ADC_IER_PEN);
    }
    /* Pen pressed */
    else if (status & ADC_ISR_PEN)
    {
        bTsFlags |= TS_PEN_STAT;
        /* Configure for peripdic trigger */
        ADC_SetTsAverage(pAdc, ADC_TSMR_TSAV_AVG8CONV);
        ADC_SetTsDebounce(pAdc, 300);         /* 300ns */
        ADC_SetTriggerMode(pAdc, ADC_TRGR_TRGMOD_PERIOD_TRIG);
        /* Disable pen press detect */
        ADC_DisableIt(pAdc, ADC_IDR_PEN);
        /* Enable pen release detect */
        ADC_EnableIt(pAdc, ADC_IER_NOPEN|ADC_IER_XRDY|ADC_IER_YRDY|ADC_IER_PRDY);
    }
    else if (status & ADC_ISR_PENS)
    {
        /* X */
        if (status & ADC_ISR_XRDY)
        {
            bTsFlags |= TS_X_RDY;
        }
        /* Y */
        if (status & ADC_ISR_YRDY)
        {
            bTsFlags |= TS_Y_RDY;
        }
        /* P: (X/1024)*[(Z2/Z1)-1] */
        if (status & ADC_ISR_PRDY)
        {
            bTsFlags |= TS_P_RDY;
        }
    }
    /* X,Y,P are ready */
    if ((bTsFlags & TS_DATA_RDY) == TS_DATA_RDY)
    {
        uint32_t xpos, z2, z1;
        bTsFlags &= ~TS_DATA_RDY;

        /* Get X,Y */
        TSD_GetRawMeasurement(dwRaw);

        /* Interprate X,Y */
        TSDCom_InterpolateMeasurement(dwRaw, dwTsData);

        /* Get P: Rp = Rxp*(Xpos/1024)*[(Z2/Z1)-1] */
        dwRaw[2] = ADC_GetTsPressure(pAdc);
        #ifdef TS_XY_SWAP
        xpos = (dwRaw[1]);
        #else
        xpos = (dwRaw[0]);
        #endif
        xpos = (xpos & ADC_XPOSR_XPOS_Msk) >> ADC_XPOSR_XPOS_Pos;
        z2 = (dwRaw[2] & ADC_PRESSR_Z2_Msk) >> ADC_PRESSR_Z2_Pos;
        z1 = (dwRaw[2] & ADC_PRESSR_Z1_Msk) >> ADC_PRESSR_Z1_Pos;
        dwTsData[2] = (xpos) * (z2 - z1) / z1;

        /* PenPress */
        if (bTsFlags & TS_PEN_STAT)
        {
            bTsFlags &= ~TS_PEN_STAT;
            /* Invoke PenPress callback */
            if (TSDCom_IsCalibrationOk())
                TSD_PenPressed(dwTsData[0], dwTsData[1], dwTsData[2]);
        }
        /* Periodic if data change invoke callback */
        if (dwTsData[0] != dwLastTsData[0]
            ||   dwTsData[1] != dwLastTsData[1]
            ||   dwTsData[2] != dwLastTsData[2] )
        {
            /* Register last data */
            memcpy(dwLastTsData, dwTsData, sizeof(dwTsData));
            /* Invoke PenMoved callback */
            if (TSDCom_IsCalibrationOk())
                TSD_PenMoved(dwTsData[0], dwTsData[1], dwTsData[2]);
        }
        
    }
}

/*----------------------------------------------------------------------------
 *         Global functions
 *----------------------------------------------------------------------------*/

/**
 * Reads and store a touchscreen measurement in the provided array.
 * The value stored are:
 *  - data[0] = XPOS * 1024 / XSCALE
 *  - data[1] = YPOS * 1024 / YSCALE
 * \param pData  Array where the measurements will be stored
 */
void TSD_GetRawMeasurement(uint32_t *pData)
{
    Adc *pAdc = ADC;
    uint32_t xr, yr;
    #ifdef TS_XY_SWAP
    yr = ADC_GetTsXPosition(pAdc);
    xr = ADC_GetTsYPosition(pAdc);
    #else
    xr = ADC_GetTsXPosition(pAdc);
    yr = ADC_GetTsYPosition(pAdc);
    #endif
    pData[0]  = ((xr & ADC_XPOSR_XPOS_Msk) >> ADC_XPOSR_XPOS_Pos) * 1024 * 4;
    pData[0] /= ((xr & ADC_XPOSR_XSCALE_Msk) >> ADC_XPOSR_XSCALE_Pos);
    pData[1]  = ((yr & ADC_YPOSR_YPOS_Msk) >> ADC_YPOSR_YPOS_Pos) * 1024 * 4;
    pData[1] /= ((yr & ADC_YPOSR_YSCALE_Msk) >> ADC_YPOSR_YSCALE_Pos);
}

/**
 * Wait pen pressed
 */
void TSD_WaitPenPressed(void)
{
    Adc *pAdc = ADC;
    uint8_t bFlags = 0;
    uint32_t dwStatus;
    /* Wait for touch & end of conversion */
    while (1)
    {
        dwStatus = ADC_GetStatus(pAdc);
        if (dwStatus & ADC_ISR_PEN) bFlags |= 8;
        if (dwStatus & ADC_ISR_XRDY)bFlags |= 1;
        if (dwStatus & ADC_ISR_YRDY)bFlags |= 2;
        if (dwStatus & ADC_ISR_PRDY)bFlags |= 4;
        if (bFlags == 0xF) break;
    }
}

/**
 * Wait pen released
 */
void TSD_WaitPenReleased(void)
{
    Adc *pAdc = ADC;

    /* Wait for contact loss */
    while((ADC_GetStatus(pAdc) & ADC_ISR_NOPEN) == 0);
}

/**
 * Initializes the touchscreen driver and starts the calibration process. When
 * finished, the touchscreen is operational.
 * The configuration is taken from the board.h of the device being compiled.
 * Important: the LCD driver must have been initialized prior to calling this
 * function.
 */
void TSD_Initialize(void)
{
    Adc *pAdc = ADC;

    bTsFlags = 0;

    /* Configuration */
    PMC_EnablePeripheral(ID_ADC);

    ADC_SetClock(pAdc, BOARD_TOUCHSCREEN_ADCCLK, BOARD_MCK);
    ADC_SetStartupTime(pAdc, BOARD_TOUCHSCREEN_STARTUP);
    ADC_SetTrackingTime(pAdc, BOARD_TOUCHSCREEN_SHTIM);

    ADC_SetTriggerPeriod(pAdc, 20000000); /*  20ms */

    ADC_SetTsMode(pAdc, ADC_TSMR_TSMODE_4_WIRE);
    ADC_SetTsAverage(pAdc, ADC_TSMR_TSAV_NO_FILTER);

    ADC_SetTsPenDetect(pAdc, 1);
    ADC_SetTsDebounce(pAdc, BOARD_TOUCHSCREEN_DEBOUNCE);

    pAdc->ADC_MR &= ~(3<<28);
    pAdc->ADC_ACR = 0x102;    
}

/**
 * Enable/Disable TSD capturing
 */
void TSD_Enable(uint8_t bEnDis)
{
    Adc *pAdc = ADC;
    if (bEnDis)
    {
        ADC_SetTsAverage(pAdc, ADC_TSMR_TSAV_NO_FILTER);
        ADC_TsCalibration(pAdc);
        ADC_SetTriggerMode(pAdc, ADC_TRGR_TRGMOD_PEN_TRIG);
        ADC_EnableIt(pAdc, ADC_IER_PEN);
    }
    else
    {
        ADC_SetTriggerMode(pAdc, ADC_TRGR_TRGMOD_NO_TRIGGER);
        ADC_DisableIt(pAdc, TS_STATUSES);
        ADC_GetStatus(pAdc);
        ADC_GetTsXPosition(pAdc);
        ADC_GetTsYPosition(pAdc);
        ADC_GetTsPressure(pAdc);
    }
}

/**
 * Do touchscreen calibration
 * \param pLcdBuffer  LCD buffer to use for displaying the calibration info.
 * \return 1 if calibration is Ok, 0 else
 */
uint8_t TSD_Calibrate(void)
{
    Adc *pAdc = ADC;
    uint8_t ret = 0;

    /* Calibration is done only once */
    if(TSDCom_IsCalibrationOk())    return 1;

    /* Disable touch */
    TSD_Enable(0);

    /* Enable capturing */
    ADC_SetTriggerMode(pAdc, ADC_TRGR_TRGMOD_PEN_TRIG);

    /* Do calibration */
    ret = TSDCom_Calibrate();

    /* Configure interrupt generation
       Do it only if the calibration is Ok. */
    //TSD_Enable(ret);

    return ret;
}

/**
 * Reset/stop the touchscreen
 */
void TSD_DeInitialize(void)
{
    Adc *pAdc = ADC;
    /* Disable TS related interrupts */
    ADC_DisableIt(pAdc, TS_STATUSES);
    /* Disable Trigger */
    ADC_SetTriggerMode(pAdc, ADC_TRGR_TRGMOD_NO_TRIGGER);
    /* Disable TS mode */
    ADC_SetTsMode(pAdc, ADC_TSMR_TSMODE_NONE);
    bTsFlags = 0;
}

/**@}*/
#endif /* #ifdef REG_ADC_TSMR */

