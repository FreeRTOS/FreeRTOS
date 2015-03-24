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

#define ILI9488     SPI0
#define ILI9488_ID  ID_SPI0

/** Pio pins to configure. */
static const Pin ILI9488_Reset[] = LCD_PIN_RESET;

static const Pin ILI9488_Pwm[] = BOARD_LCD_BACKLIGHT_PIN;

/** Pins to configure for the application. */
static const Pin spi_pins[] = BOARD_LCD_PINS;


/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/




static void ILI9488_InitInterface(void)
{

    PIO_Configure(ILI9488_Reset, PIO_LISTSIZE(ILI9488_Reset));    
    PIO_Configure(spi_pins, PIO_LISTSIZE(spi_pins));


    PIO_Configure(ILI9488_Pwm, PIO_LISTSIZE(ILI9488_Pwm));
    /* Enable PWM peripheral clock */
    PMC_EnablePeripheral(ID_PWM0);

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

    SPI_Configure(ILI9488, ILI9488_ID, (SPI_MR_MSTR | SPI_MR_MODFDIS | SPI_PCS( ILI9488_cs )));
    SPI_ConfigureNPCS( ILI9488, ILI9488_cs, 
            SPI_CSR_CPOL | SPI_CSR_BITS_9_BIT | 
            SPI_DLYBS(100, BOARD_MCK) | SPI_DLYBCT(100, BOARD_MCK) |
            SPI_SCBR( 35000000, BOARD_MCK) ) ;  

    SPI_Enable(ILI9488);

}

/**
 * \brief Send Command to ILI9488.
 *
 * \param reg   Command Register address.
 *
 */
static void ILI9488_SendCmd( uint8_t reg )
{    
    SPI_Write(ILI9488, ILI9488_cs, ILI9488_CMD(reg));  
}



/**
 * \brief Write Parameter to ILI9488 Register.
 *
 * \param data  Data to be written.
 */
static void ILI9488_WriteReg( uint8_t data )
{
    SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM(data));
}

/**
 * \brief Write 16 bit Parameter to ILI9488 Register.
 *
 * \param data  Data to be written.
 */
static void ILI9488_WriteReg16( uint16_t data )
{
    SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM(((data & 0xFF00) >> 0x08)));
    SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM((data & 0xFF)));
}

/**
 * \brief Write 24 bit Parameter to ILI9488 Register.
 *
 * \param data  Data to be written.
 */
static void ILI9488_WriteReg24( uint32_t data )
{
    SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM(((data & 0xFF0000) >> 0x10)));
    SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM(((data & 0xFF00) >> 0x08)));
    SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM((data & 0xFF)));
}

/**
 * \brief Write 32 bit Parameter to ILI9488 Register.
 *
 * \param data  Data to be written.
 */
static void ILI9488_WriteReg32( uint32_t data )
{
    SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM((data >> 0x18) & 0xFF));
    SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM(((data >> 0x10) & 0x00FF)));
    SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM(((data >> 0x08) & 0x0000FF)));
    SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM((data & 0x000000FF)));
}

/**
 * \brief Read data from ILI9488 Register.
 *
 * \param reg   Register address.
 *
 * \return      Readed data.
 */
static uint8_t ILI9488_ReadReg( uint8_t reg)
{
    uint8_t value;

    SPI_Write(ILI9488, ILI9488_cs, ILI9488_CMD(reg));
    while(SPI_IsFinished(ILI9488) !=1);
    SPI_Read(ILI9488);
    SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM(0xFF));
    while(SPI_IsFinished(ILI9488) !=1);
    value = (uint8_t)SPI_Read(ILI9488);

    ILI9488_SendCmd(ILI9488_CMD_SPI_READ_SETTINGS);
    ILI9488_WriteReg(0);

    return value;

}    
/**
 * \brief Read data from ILI9488 Register.
 *
 * \param reg   Register address.
 *
 * \return      Readed data.
 */
static uint16_t ILI9488_ReadReg16( uint8_t reg)
{
    uint16_t value;
    uint8_t SPI_CNT = 0x81;

    ILI9488_SendCmd(ILI9488_CMD_SPI_READ_SETTINGS);
    ILI9488_WriteReg(SPI_CNT);         
    value = (ILI9488_ReadReg(reg) << 0x08);

    SPI_CNT++;
    ILI9488_SendCmd(ILI9488_CMD_SPI_READ_SETTINGS);
    ILI9488_WriteReg(SPI_CNT);  
    value |= ILI9488_ReadReg(reg);

    ILI9488_SendCmd(ILI9488_CMD_SPI_READ_SETTINGS);
    ILI9488_WriteReg(0);

    return value;

}

/**
 * \brief Read data from ILI9488 Register.
 *
 * \param reg   Register address.
 *
 * \return      Readed data.
 */
static uint32_t ILI9488_ReadReg24( uint8_t reg)
{
    uint32_t value=0;
    uint8_t SPI_CNT = 0x81;

    //Set ILI9488 count to 0
    ILI9488_SendCmd(ILI9488_CMD_SPI_READ_SETTINGS);
    ILI9488_WriteReg(SPI_CNT);

    // Send Command
    value = (ILI9488_ReadReg(reg) << 0x10);

    SPI_CNT++;
    ILI9488_SendCmd(ILI9488_CMD_SPI_READ_SETTINGS);
    ILI9488_WriteReg(SPI_CNT);  

    value |= (ILI9488_ReadReg(reg) << 0x08);

    SPI_CNT++;
    ILI9488_SendCmd(ILI9488_CMD_SPI_READ_SETTINGS);
    ILI9488_WriteReg(SPI_CNT);  
    value |= ILI9488_ReadReg(reg);

    ILI9488_SendCmd(ILI9488_CMD_SPI_READ_SETTINGS);
    ILI9488_WriteReg(0);


    return value;


}

/**
 * \brief Read data from ILI9488 Register.
 *
 * \param reg   Register address.
 *
 * \return      Readed data.
 */
static uint32_t ILI9488_ReadReg32( uint8_t reg)
{
    uint32_t value;
    uint8_t SPI_CNT = 0x81;

    ILI9488_SendCmd(ILI9488_CMD_SPI_READ_SETTINGS);
    ILI9488_WriteReg(SPI_CNT);
    value = ILI9488_ReadReg(reg) ;
    value  <<=  24;

    SPI_CNT++;
    ILI9488_SendCmd(ILI9488_CMD_SPI_READ_SETTINGS);
    ILI9488_WriteReg(SPI_CNT);  
    value |= (ILI9488_ReadReg(reg) << 16);

    SPI_CNT++;
    ILI9488_SendCmd(ILI9488_CMD_SPI_READ_SETTINGS);
    ILI9488_WriteReg(SPI_CNT);  
    value |= (ILI9488_ReadReg(reg) << 8);

    SPI_CNT++;
    ILI9488_SendCmd(ILI9488_CMD_SPI_READ_SETTINGS);
    ILI9488_WriteReg(SPI_CNT);  
    value |= ILI9488_ReadReg(reg);

    ILI9488_SendCmd(ILI9488_CMD_SPI_READ_SETTINGS);
    ILI9488_WriteReg(0);

    return value;
}

static void ILI9488_NOP(void)
{
    ILI9488_SendCmd(ILI9488_CMD_NOP);
}





/**
 * \brief Write data to ILI9488 Register.
 *
 * \param reg   Register address.
 * \param data  Data to be written.
 */
void ILI9488_WriteSingle( LcdColor_t data )
{


    ILI9488_SendCmd(ILI9488_CMD_MEMORY_WRITE);
    ILI9488_WriteReg24(data);

}

/**
 * \brief Prpare to write data to ILI9488 Register.
 *
 */
void ILI9488_WriteRAM_Prepare(void)
{
    ILI9488_SendCmd(ILI9488_CMD_MEMORY_WRITE);
}

/**
 * \brief Prpare to write data to ILI9488 Register.
 *
 */
void ILI9488_ReadRAM_Prepare(void)
{
    ILI9488_SendCmd(ILI9488_CMD_MEMORY_READ);
}

/**
 * \brief Write data to ILI9488 Register.
 *
 * \param reg   Register address.
 * \param data  Data to be written.
 */
void ILI9488_WriteRAM( LcdColor_t data )
{  
    ILI9488_WriteReg24(data);  
}


/**
 * \brief Write data to ILI9488 Register.
 *
 * \param reg   Register address.
 * \param data  Data to be written.
 */
void ILI9488_WriteRAMBuffer( const LcdColor_t *pBuf, uint32_t size)
{
    uint32_t addr ;


    for ( addr = 0 ; addr < size ; addr++ )
    {
        ILI9488_WriteRAM(pBuf[addr]);
    }
}

void ILI9488_SetCursor(uint16_t x, uint16_t y)
{
    /* Set Horizontal Address Start Position */
    ILI9488_SendCmd(ILI9488_CMD_COLUMN_ADDRESS_SET);    
    ILI9488_WriteReg16(x);
    ILI9488_WriteReg16(x+1);
    ILI9488_NOP();


    /* Set Horizontal Address End Position */
    ILI9488_SendCmd(ILI9488_CMD_PAGE_ADDRESS_SET);
    ILI9488_WriteReg16(y);
    ILI9488_WriteReg16(y+1);
    ILI9488_NOP();
}



/**
 * \brief Initialize the ILI9488 controller.
 */
extern uint32_t ILI9488_Initialize( void )
{
    uint32_t chipid;

    ILI9488_InitInterface();

    ILI9488_SendCmd(ILI9488_CMD_SOFTWARE_RESET);    
    Wait(200);

    ILI9488_SendCmd(ILI9488_CMD_SLEEP_OUT);
    Wait(200);

    // make it tRGB and reverse the column order
    ILI9488_SendCmd(ILI9488_CMD_MEMORY_ACCESS_CONTROL);
    ILI9488_WriteReg(0x48);
    Wait(100);

    ILI9488_SendCmd(ILI9488_CMD_CABC_CONTROL_9); // set PWm to 14.11 KHz
    ILI9488_WriteReg(0x04);

    //    ILI9488_SendCmd(ILI9488_CMD_COLMOD_PIXEL_FORMAT_SET); // set 16bit/pixel
    //    ILI9488_WriteReg(0x05);

    /* Check ILI9488 chipid */
    chipid = ILI9488_ReadReg24(ILI9488_CMD_READ_ID4); /* Driver Code Read  */
    if ( chipid != ILI9488_DEVICE_CODE )
    {
        printf( "Read ILI9488 chip ID (0x%04x) error, skip initialization.\r\n", chipid ) ;
        assert(0);
        return 1 ;
    }

    ILI9488_SendCmd(ILI9488_CMD_NORMAL_DISP_MODE_ON);
    ILI9488_SendCmd(ILI9488_CMD_DISPLAY_ON);

    return 0 ;
}




/**
 * \brief Turn on the ILI9488.
 */
extern void ILI9488_On( void )
{
    ILI9488_SendCmd(ILI9488_CMD_PIXEL_OFF);
    ILI9488_SendCmd(ILI9488_CMD_DISPLAY_ON);
    ILI9488_SendCmd(ILI9488_CMD_NORMAL_DISP_MODE_ON);
}


/**
 * \brief Turn off the ILI9488.
 */
extern void ILI9488_Off( void )
{    
    ILI9488_SendCmd(ILI9488_CMD_DISPLAY_OFF);
    ILI9488_SendCmd(ILI9488_CMD_DISPLAY_OFF);
}

/**
 * \brief Power down the ILI9488.
 */
extern void ILI9488_PowerDown( void )
{

}




/**
 * \brief Set a partial display window
 *
 * Initialize a partial window on ILI9488
 * \param Start Starting address of window.
 * \param End  End address of window.
 * \return 0 for successfull operation.
 */
extern void ILI9488_SetPartialWindow( uint16_t Start, uint16_t End)
{

    ILI9488_SendCmd(ILI9488_CMD_POWER_CONTROL_PARTIAL_5);
    ILI9488_WriteReg(0x44 ) ;

    ILI9488_SendCmd(ILI9488_CMD_PARTIAL_AREA);
    ILI9488_WriteReg16(Start ) ;
    ILI9488_WriteReg16(End)  ;

    ILI9488_SendCmd(ILI9488_CMD_PARTIAL_MODE_ON);
    Wait(10);


}



extern void ILI9488_SetWindow( uint16_t dwX, uint16_t dwY, uint16_t dwWidth, uint16_t dwHeight )
{
    uint16_t ColStart, ColEnd, RowStart, RowEnd;

    ColStart  =  dwX ;
    ColEnd    =  dwWidth;

    RowStart = dwY ;
    RowEnd   = dwHeight;

    if (  ( ColEnd > (ILI9488_LCD_WIDTH)) || ( RowEnd > (ILI9488_LCD_HEIGHT))) 
    {
        printf("\n\rWindow too large\n\r");
        assert(1);
    }

    if (  ( ColEnd < ColStart) || ( RowEnd < RowStart) )
    {
        printf("\n\rWindow's hight or width is not large enough\n\r");
        assert(1);     
    }
    /* Set Horizontal Address Start Position */
    ILI9488_SendCmd(ILI9488_CMD_COLUMN_ADDRESS_SET);    
    ILI9488_WriteReg16(ColStart);
    ILI9488_WriteReg16(ColEnd);
    ILI9488_NOP();


    /* Set Horizontal Address End Position */
    ILI9488_SendCmd(ILI9488_CMD_PAGE_ADDRESS_SET);
    ILI9488_WriteReg16(RowStart);
    ILI9488_WriteReg16(RowEnd);
    ILI9488_NOP();

}

extern void ILI9488_SetDisplayLandscape( uint8_t dwRGB, uint8_t LandscaprMode )
{
    uint8_t Value;
    if(LandscaprMode)
    {
        if(dwRGB)
        {
            Value = 0xA8;
        }
        else
        {
            Value = 0xA0;
        }
    }
    else
    {
        if(dwRGB)
        {
            Value = 0xE8;
        }
        else
        {
            Value = 0xE0;
        }
    }
    // make it tRGB and reverse the column order
    ILI9488_SendCmd(ILI9488_CMD_MEMORY_ACCESS_CONTROL);
    ILI9488_WriteReg(Value);
    Wait(50);

    ILI9488_SetWindow( 0, 0, BOARD_LCD_WIDTH, BOARD_LCD_HEIGHT  ) ;
}

extern void ILI9488_SetDisplayPortrait( uint8_t dwRGB )
{
    uint8_t Value;
    if(dwRGB)
    {
        Value = 0x48;
    }
    else
    {
        Value = 0x40;
    }
    // make it tRGB and reverse the column order
    ILI9488_SendCmd(ILI9488_CMD_MEMORY_ACCESS_CONTROL);
    ILI9488_WriteReg(Value);
    Wait(50);

    ILI9488_SetWindow( 0, 0, BOARD_LCD_WIDTH, BOARD_LCD_HEIGHT) ;
}


extern void ILI9488_SetVerticalScrollWindow( uint16_t dwStartAdd, uint16_t dwHeight )
{
    ILI9488_SendCmd(ILI9488_CMD_VERT_SCROLL_DEFINITION);
    ILI9488_WriteReg16(dwStartAdd-1);
    ILI9488_WriteReg16(dwStartAdd);
    ILI9488_WriteReg16((dwStartAdd + dwHeight + 1));
}


extern void ILI9488_VerticalScroll( uint16_t wY )
{
    ILI9488_SendCmd(ILI9488_CMD_VERT_SCROLL_START_ADDRESS);
    ILI9488_WriteReg16(wY);
}



extern void ILI9488_ExitScrollMode(void )
{
    ILI9488_SendCmd(ILI9488_CMD_DISPLAY_OFF);
    ILI9488_SendCmd(ILI9488_CMD_NORMAL_DISP_MODE_ON);
    ILI9488_SendCmd(ILI9488_CMD_DISPLAY_ON);
}


extern void ILI9488_TestPattern(void)
{
    uint32_t i, data;

    ILI9488_SetWindow( 0, 0, 319, 479 ) ;  

    data = COLOR_WHITE;
    ILI9488_SendCmd(ILI9488_CMD_MEMORY_WRITE);
    for(i = 0; i< (BOARD_LCD_WIDTH * BOARD_LCD_HEIGHT); i++)
    {
        SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM(data >> 16));
        SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM(data >> 8));
        SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM(data & 0xFF));
    }

    ILI9488_SetWindow( 50, 50, 300, 300 ) ;  
    data = COLOR_BLUE;
    ILI9488_SendCmd(ILI9488_CMD_MEMORY_WRITE);
    for(i = 0; i< (BOARD_LCD_WIDTH * BOARD_LCD_HEIGHT); i++)
    {
        SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM(data >> 16));
        SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM(data >> 8));
        SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM(data & 0xFF));
    }

    ILI9488_SetWindow( 150, 150, 300, 300 ) ;  
    data = COLOR_GREEN;
    ILI9488_SendCmd(ILI9488_CMD_MEMORY_WRITE);
    for(i = 0; i< (BOARD_LCD_WIDTH * BOARD_LCD_HEIGHT); i++)
    {
        SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM(data >> 16));
        SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM(data >> 8));
        SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM(data & 0xFF));
    }

    ILI9488_SetWindow(200, 200, 300, 300 ) ;  
    data = COLOR_RED;
    ILI9488_SendCmd(ILI9488_CMD_MEMORY_WRITE);
    for(i = 0; i< (BOARD_LCD_WIDTH * BOARD_LCD_HEIGHT); i++)
    {
        SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM(data >> 16));
        SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM(data >> 8));
        SPI_Write(ILI9488, ILI9488_cs, ILI9488_PARAM(data & 0xFF));
    }

}

#endif
