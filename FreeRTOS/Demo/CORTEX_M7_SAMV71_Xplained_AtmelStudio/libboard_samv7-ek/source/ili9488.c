/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
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

/**
 * \file
 *
 * Implementation of ILI9488 driver.
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "board.h"
#include <string.h>
#include <stdio.h>

#ifdef BOARD_LCD_ILI9488

/*----------------------------------------------------------------------------
 *        Local variables
 *----------------------------------------------------------------------------*/

/** Pio pins to configure. */
static const Pin ILI9488_Reset[] = {LCD_PIN_RESET};
static const Pin ILI9488_Pwm[] = {BOARD_LCD_PIN_BACKLIGHT};
/** Pins to configure for the application. */
static const Pin lcd_pins[] = BOARD_LCD_PINS;
/** Pins to configure for the application. */
static const Pin ILI9488_CDS[] = {BOARD_LCD_PIN_CDS};

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/
/**
 * \brief ILI9488 Hardware Initialization for SPI/SMC LCD.
 */
static void _ILI9488_HW_Initialize(void) 
{
    /* Pin configurations */
    PIO_Configure(ILI9488_Reset, PIO_LISTSIZE(ILI9488_Reset));
    PIO_Configure(ILI9488_CDS, PIO_LISTSIZE(ILI9488_CDS));
    PIO_Configure(lcd_pins, PIO_LISTSIZE(lcd_pins));
    PIO_Configure(ILI9488_Pwm, PIO_LISTSIZE(ILI9488_Pwm));

#if !defined(BOARD_LCD_SMC)
    /* Enable PWM peripheral clock */
    PMC_EnablePeripheral(ID_PWM0);
    PMC_EnablePeripheral(ILI9488_ID);
    /* Set clock A and clock B */
    // set for 14.11 KHz for CABC control
    //    mode = PWM_CLK_PREB(0x0A) | (PWM_CLK_DIVB(110)) |
    //           PWM_CLK_PREA(0x0A) | (PWM_CLK_DIVA(110));
    PWMC_ConfigureClocks(PWM0, 14200, 0,  BOARD_MCK);

    /* Configure PWM channel 1 for LED0  */
    PWMC_DisableChannel(PWM0, CHANNEL_PWM_LCD);

    PWMC_ConfigureChannel(PWM0, CHANNEL_PWM_LCD, PWM_CMR_CPRE_CLKA,0,PWM_CMR_CPOL);
    PWMC_SetPeriod(PWM0, CHANNEL_PWM_LCD, 16);
    PWMC_SetDutyCycle(PWM0, CHANNEL_PWM_LCD, 8);
    PWMC_EnableChannel(PWM0, CHANNEL_PWM_LCD);

    SPI_Configure(ILI9488, ILI9488_ID, (SPI_MR_MSTR | SPI_MR_MODFDIS | SPI_PCS( SMC_EBI_LCD_CS )));
    SPI_ConfigureNPCS( ILI9488, 
                       SMC_EBI_LCD_CS,
                       SPI_CSR_CPOL | SPI_CSR_BITS_8_BIT | SPI_DLYBS(6, BOARD_MCK) | SPI_DLYBCT(100, BOARD_MCK) | 
                       SPI_SCBR( 20000000, BOARD_MCK) ) ;
    SPI_Enable(ILI9488);
#else
    PIO_Set(ILI9488_Pwm);
#endif
}

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Set ILI9488 Pixel Format in SPI/SMC mode.
 * \param format Format of pixel
 */
void ILI9488_SetPixelFormat(uint16_t format)
{
    ILI9488_WriteReg(ILI9488_CMD_COLMOD_PIXEL_FORMAT_SET, &format, sizeof(format));
}

/**
 * \brief ILI9488 issue MEMORY write command in SPI/SMC mode.
 */
void ILI9488_MemWriteCmd(void)
{
    ILI9488_SendCmd(ILI9488_CMD_MEMORY_WRITE);
}

/**
 * \brief ILI9488 issue MEMORY read command in SPI/SMC mode.
 */
void ILI9488_MemReadCmd(void)
{
    ILI9488_SendCmd(ILI9488_CMD_MEMORY_READ);
}

/**
 * \brief ILI9488 Write memory with give buffer in SPI/SMC mode.
 * \Param  pBuf Point to buffer to be written.
 * \Param  size Size of buffer in byte.
 */
void ILI9488_WriteMemory( const uint16_t *pBuf, uint32_t size)
{
    ILI9488DmaTxTransfer((uint16_t *)pBuf,size);
}

/**
 * \brief ILI9488 Read memory to give buffer in SPI/SMC mode.
 * \Param  pBuf Point to buffer to be read.
 * \Param  size Size of buffer in byte.
 */
void ILI9488_ReadMemory( const uint16_t *pBuf, uint32_t size)
{
    uint32_t cnt;
#if !defined(BOARD_LCD_SMC)
    cnt = size*3;
#else
    cnt = size;
#endif
    ILI9488DmaRxTransfer((uint32_t *)pBuf,cnt);
}

/**
 * \brief Initialize the ILI9488 controller in SPI/SMC mode.
 */
uint32_t ILI9488_Initialize( void )
{
    uint32_t chipid;
    uint16_t param;

    _ILI9488_HW_Initialize();
    ILI9488_InitializeWithDma();

    ILI9488_WriteReg(ILI9488_CMD_SOFTWARE_RESET,&param,0);
    Wait(200);

    ILI9488_WriteReg(ILI9488_CMD_SLEEP_OUT,&param,0);
    Wait(200);

    // make it tRGB and reverse the column order
    param = 0x48;
    ILI9488_WriteReg(ILI9488_CMD_MEMORY_ACCESS_CONTROL,&param,1);
    Wait(100);

    param = 0x04;
    ILI9488_WriteReg(ILI9488_CMD_CABC_CONTROL_9,&param,1);

    chipid = ILI9488ReadExtReg(ILI9488_CMD_READ_ID4,3);
    if ( chipid != ILI9488_DEVICE_CODE )
    {
        printf( "Read ILI9488 chip ID (0x%04x) error, skip initialization.\r\n", (unsigned int)chipid ) ;
        return 1 ;
    }

#if !defined(BOARD_LCD_SMC)
    ILI9488_SetPixelFormat(6);
#else
    ILI9488_SetPixelFormat(5);
#endif
    ILI9488_WriteReg(ILI9488_CMD_NORMAL_DISP_MODE_ON,&param,0);
    ILI9488_WriteReg(ILI9488_CMD_DISPLAY_ON,&param,0);
    return 0 ;
}

/**
 * \brief ILI9488 configure cursor in SPI/SMC mode.
 * \Param x X position.
 * \Param y Y position.
 */
void ILI9488_SetCursor(uint16_t x, uint16_t y)
{
    /* Set Horizontal Address Start Position */
    uint32_t cnt = 0;

#if !defined(BOARD_LCD_SMC)
    uint8_t buf[4];
    cnt = sizeof(buf);
#else
    uint16_t buf[4];
    cnt = sizeof(buf)/sizeof(uint16_t);
#endif

    buf[0] = get_8b_to_16b(x);
    buf[1] = get_0b_to_8b(x);
    x+=1;
    buf[2] = get_8b_to_16b(x);
    buf[3] = get_0b_to_8b(x);
    ILI9488_WriteReg(ILI9488_CMD_COLUMN_ADDRESS_SET,(uint16_t*)buf,cnt);
    ILI9488_SendCmd(ILI9488_CMD_NOP);


    /* Set Horizontal Address End Position */
    buf[0] = get_8b_to_16b(y);
    buf[1] = get_0b_to_8b(y);
    y+=1;
    buf[2] = get_8b_to_16b(y);
    buf[3] = get_0b_to_8b(y);
    ILI9488_WriteReg(ILI9488_CMD_PAGE_ADDRESS_SET,(uint16_t*)buf,cnt);
    ILI9488_SendCmd(ILI9488_CMD_NOP);
}

/**
 * \brief ILI9488 configure window.
 * \Param dwX X start position.
 * \Param dwX Y start position.
 * \Param dwWidth  Width of window.
 * \Param dwHeight Height of window.
 */
void ILI9488_SetWindow( uint16_t dwX, uint16_t dwY, uint16_t dwWidth, uint16_t dwHeight )
{
    uint16_t ColStart, ColEnd, RowStart, RowEnd;

    uint32_t cnt = 0;

#if !defined(BOARD_LCD_SMC)
    uint8_t buf[4];
    cnt = sizeof(buf);
#else
    uint16_t buf[4];
    cnt = sizeof(buf)/sizeof(uint16_t);
#endif

    ColStart  =  dwX ;
    ColEnd    =  dwWidth;

    RowStart = dwY ;
    RowEnd   = dwHeight;

    buf[0] = get_8b_to_16b(ColStart);
    buf[1] = get_0b_to_8b(ColStart);
    buf[2] = get_8b_to_16b(ColEnd);
    buf[3] = get_0b_to_8b(ColEnd);
    ILI9488_WriteReg(ILI9488_CMD_COLUMN_ADDRESS_SET, (uint16_t*)buf, cnt);
    ILI9488_SendCmd(ILI9488_CMD_NOP);

    /* Set Horizontal Address End Position */
    buf[0] = get_8b_to_16b(RowStart);
    buf[1] = get_0b_to_8b(RowStart);
    buf[2] = get_8b_to_16b(RowEnd);
    buf[3] = get_0b_to_8b(RowEnd);
    ILI9488_WriteReg(ILI9488_CMD_PAGE_ADDRESS_SET,(uint16_t*)buf,cnt);
    ILI9488_SendCmd(ILI9488_CMD_NOP);
}

/**
 * \brief ILI9488 configure window with full size.
 */
void ILI9488_SetFullWindow(void)
{
    uint16_t c_start,c_end,r_start,r_end;
    uint32_t cnt = 0;

#if !defined(BOARD_LCD_SMC)
    uint8_t buf[4];
    cnt = sizeof(buf);
#else
    uint16_t buf[4];
    cnt = sizeof(buf)/sizeof(uint16_t);
#endif

    c_start  =  0 ;
    c_end    =  ILI9488_LCD_WIDTH- 1;

    r_start = 0 ;
    r_end   = ILI9488_LCD_HEIGHT - 1;

    /* Set Horizontal Address Start Position */
    buf[0] = get_8b_to_16b(c_start);
    buf[1] = get_0b_to_8b(c_start);
    buf[2] = get_8b_to_16b(c_end);
    buf[3] = get_0b_to_8b(c_end);
    ILI9488_WriteReg(ILI9488_CMD_COLUMN_ADDRESS_SET,(uint16_t*)buf,cnt);
    ILI9488_SendCmd(ILI9488_CMD_NOP);

    /* Set Horizontal Address End Position */
    buf[0] = get_8b_to_16b(r_start);
    buf[1] = get_0b_to_8b(r_start);
    buf[2] = get_8b_to_16b(r_end);
    buf[3] = get_0b_to_8b(r_end);
    ILI9488_WriteReg(ILI9488_CMD_COLUMN_ADDRESS_SET,(uint16_t*)buf,cnt);
    ILI9488_SendCmd(ILI9488_CMD_NOP);
}


/**
 * \brief Turn on the ILI9488.
 */
void ILI9488_On( void )
{
    ILI9488_SendCmd(ILI9488_CMD_PIXEL_OFF);
    ILI9488_SendCmd(ILI9488_CMD_DISPLAY_ON);
    ILI9488_SendCmd(ILI9488_CMD_NORMAL_DISP_MODE_ON);
}

/**
 * \brief Turn off the ILI9488.
 */
void ILI9488_Off( void )
{
    ILI9488_SendCmd(ILI9488_CMD_DISPLAY_OFF);
}

/**
 * \brief ILI9488 configure landscape.
 * \Param dwRGB RGB mode.
 * \Param LandscaprMode Landscape Mode.
 */
void ILI9488_SetDisplayLandscape( uint8_t dwRGB, uint8_t LandscapeMode )
{
    uint16_t value;
    if(LandscapeMode)
    {
        if(dwRGB)
        {
            value = 0xE8;
        }
        else
        {
            value = 0xE0;
        }
    }
    else
    {
        if(dwRGB)
        {
            value = 0x48;
        }
        else
        {
            value = 0x40;
        }
    }
    ILI9488_WriteReg(ILI9488_CMD_MEMORY_ACCESS_CONTROL, &value, sizeof(value));
}

#endif
