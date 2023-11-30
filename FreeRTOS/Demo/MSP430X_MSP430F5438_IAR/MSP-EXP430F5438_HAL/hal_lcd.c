/**
 * @file  hal_lcd.c
 *
 * Copyright 2010 Texas Instruments, Inc.
***************************************************************************/

#include "msp430.h"
#include "hal_MSP-EXP430F5438.h"
#include "hal_lcd_fonts.h"

unsigned char LcdInitMacro[]={
            0x74,0x00,0x00,0x76,0x00,0x01,  // R00 start oscillation
            0x74,0x00,0x01,0x76,0x00,0x0D,  // R01 driver output control
            0x74,0x00,0x02,0x76,0x00,0x4C,  // R02 LCD - driving waveform control
            0x74,0x00,0x03,0x76,0x12,0x14,  // R03 Power control
            0x74,0x00,0x04,0x76,0x04,0x66,  // R04 Contrast control
            0x74,0x00,0x05,0x76,0x00,0x10,  // R05 Entry mode
            0x74,0x00,0x06,0x76,0x00,0x00,  // R06 RAM data write mask
            0x74,0x00,0x07,0x76,0x00,0x15,  // R07 Display control
            0x74,0x00,0x08,0x76,0x00,0x03,  // R08 Cursor Control
            0x74,0x00,0x09,0x76,0x00,0x00,  // R09 RAM data write mask
            0x74,0x00,0x0A,0x76,0x00,0x15,  // R0A
            0x74,0x00,0x0B,0x76,0x00,0x03,  // R0B Horizontal Cursor Position
            0x74,0x00,0x0C,0x76,0x00,0x03,  // R0C Vertical Cursor Position
            0x74,0x00,0x0D,0x76,0x00,0x00,  // R0D
            0x74,0x00,0x0E,0x76,0x00,0x15,  // R0E
            0x74,0x00,0x0F,0x76,0x00,0x03,  // R0F
            0x74,0x00,0x10,0x76,0x00,0x15,  // R0E
            0x74,0x00,0x11,0x76,0x00,0x03,  // R0F
};

unsigned char Read_Block_Address_Macro[]= {0x74,0x00,0x12,0x77,0x00,0x00};
unsigned char Draw_Block_Value_Macro[]={0x74,0x00,0x12,0x76,0xFF,0xFF};
unsigned char Draw_Block_Address_Macro[]={0x74,0x00,0x11,0x76,0x00,0x00};

unsigned int  LcdAddress = 0, LcdTableAddress = 0;
unsigned char contrast   = 0x66;
unsigned char backlight  = 8;
int LCD_MEM[110*17];		//This array stores a copy of all data on the LCD
					  		//screen. If memory is an issue though, this array
					  		//can be eliminated and the halLcdReadBlock()
					 		//command can be used instead whenever you are
					 		//manipulating the currently displayed data.

/**********************************************************************//**
 * @brief  Sends 3+3 bytes of data to the LCD using the format specified
 *         by the LCD Guide.
 *
 * @param  Data[] Data array for transmission
 *
 * @return none
 *************************************************************************/
void halLcdSendCommand(unsigned char Data[])
{
  unsigned char i;

  LCD_CS_RST_OUT &= ~LCD_CS_PIN;            //CS = 0 --> Start Transfer
  for ( i = 0; i < 6; i++ )
  {
    while (!(UCB2IFG & UCTXIFG));           // Wait for TXIFG
    UCB2TXBUF = Data[i];                    // Load data

    if (i == 2)                             //Pull CS up after 3 bytes
    {
      while (UCB2STAT & UCBUSY);    	
      LCD_CS_RST_OUT |= LCD_CS_PIN;         //CS = 1 --> Stop Transfer
      LCD_CS_RST_OUT &= ~LCD_CS_PIN;        //CS = 0 --> Start Transfer	
    }
  }
  while (UCB2STAT & UCBUSY);    	
  LCD_CS_RST_OUT |= LCD_CS_PIN;             //CS = 1 --> Stop Transfer
}

/**********************************************************************//**
 * @brief  Initializes the USCI module, LCD device for communication.
 *
 * - Sets up the SPI2C Communication Module
 * - Performs Hitachi LCD Initialization Procedure
 *
 * @param  none
 *
 * @return none
 *************************************************************************/
void halLcdInit(void)
{
  volatile unsigned int i=0;

  LCD_CS_RST_OUT |= LCD_CS_PIN | LCD_RESET_PIN ;
  LCD_CS_RST_DIR |= LCD_CS_PIN | LCD_RESET_PIN ;

  LCD_BACKLT_SEL |= LCD_BACKLIGHT_PIN;

  LCD_CS_RST_OUT &= ~LCD_RESET_PIN;         // Reset LCD
  __delay_cycles(0x47FF);                   //Reset Pulse
  LCD_CS_RST_OUT |= LCD_RESET_PIN;

  // UCLK,MOSI setup, SOMI cleared
  LCD_SPI_SEL |= LCD_MOSI_PIN + LCD_CLK_PIN;
  LCD_SPI_SEL &= ~LCD_MISO_PIN;
  LCD_SPI_DIR &= ~(LCD_MISO_PIN + LCD_MOSI_PIN);            // Pin direction controlled by module,
                                                            // Set both pins to input as default

  // Initialize the USCI_B2 module for SPI operation
  UCB2CTL1 = UCSWRST;                       // Hold USCI in SW reset mode while configuring it
  UCB2CTL0 = UCMST+UCSYNC+UCCKPL+UCMSB;     // 3-pin, 8-bit SPI master
  UCB2CTL1 |= UCSSEL_2;                     // SMCLK
  UCB2BR0 = 4;                              // Note: Do not exceed D/S spec for UCLK!
  UCB2BR1 = 0;
  UCB2CTL1 &= ~UCSWRST;                     // Release USCI state machine
  UCB2IFG &= ~UCRXIFG;

  // Wake-up the LCD as per datasheet specifications
  halLcdActive();

  // LCD Initialization Routine Using Predefined Macros
  halLcdSendCommand(&LcdInitMacro[ 1 * 6 ]);
  halLcdSendCommand(&LcdInitMacro[ 2 * 6 ]);
  halLcdSendCommand(&LcdInitMacro[ 4 * 6 ]);
  halLcdSendCommand(&LcdInitMacro[ 5 * 6 ]);
  halLcdSendCommand(&LcdInitMacro[ 6 * 6 ]);
  halLcdSendCommand(&LcdInitMacro[ 7 * 6 ]);

}

/**********************************************************************//**
 * @brief  Shuts down the LCD display and hdisables the USCI communication.
 *
 * @param  none
 *
 * @return none
 *************************************************************************/
void halLcdShutDown(void)
{
  halLcdStandby();

  LCD_CS_RST_DIR |= LCD_CS_PIN | LCD_RESET_PIN ;
  LCD_CS_RST_OUT &= ~(LCD_CS_PIN | LCD_RESET_PIN );
  LCD_CS_RST_OUT &= ~LCD_RESET_PIN;

  LCD_SPI_SEL &= ~(LCD_MOSI_PIN + LCD_CLK_PIN + LCD_MISO_PIN);
  LCD_CS_RST_DIR |= LCD_MOSI_PIN + LCD_CLK_PIN + LCD_MISO_PIN;
  LCD_CS_RST_OUT &= ~(LCD_MOSI_PIN + LCD_CLK_PIN + LCD_MISO_PIN);

  UCB2CTL0 = UCSWRST;
}

/**********************************************************************//**
 * @brief  Initializes the LCD backlight PWM signal.
 *
 * @param  none
 *
 * @return none
 *
 *************************************************************************/
void halLcdBackLightInit(void)
{
  LCD_BACKLT_DIR |= LCD_BACKLIGHT_PIN;
  LCD_BACKLT_OUT |= LCD_BACKLIGHT_PIN;
  LCD_BACKLT_SEL |= LCD_BACKLIGHT_PIN;

  TA0CCTL3 = OUTMOD_7;
  TA0CCR3 = TA0CCR0 >> 1 ;
  backlight = 8;

  TA0CCR0 = 400;
  TA0CTL = TASSEL_2+MC_1;
}

/**********************************************************************//**
 * @brief  Get function for the backlight PWM's duty cycle.
 *
 * @param  none
 *
 * @return backlight One of the the 17 possible settings - valued 0 to 16.
 *
 *************************************************************************/
unsigned int halLcdGetBackLight(void)
{
  return backlight;
}

/**********************************************************************//**
 * @brief  Set function for the backlight PWM's duty cycle
 *
 * @param  BackLightLevel The target backlight duty cycle - valued 0 to 16.
 *
 * @return none
 *************************************************************************/
void halLcdSetBackLight(unsigned char BackLightLevel)
{
  unsigned int dutyCycle = 0, i, dummy;

  if (BackLightLevel > 0)
  {
    TA0CCTL3 = OUTMOD_7;
    dummy = (TA0CCR0 >> 4);

    for (i = 0; i < BackLightLevel; i++)
      dutyCycle += dummy;

    TA0CCR3 = dutyCycle;

    // If the backlight was previously turned off, turn it on.
    if (!backlight)
      TA0CTL |= MC0;
  }
  else
  {   	
    TA0CCTL3 = 0;
    TA0CTL &= ~MC0;
  }
  backlight = BackLightLevel;
}

/**********************************************************************//**
 * @brief  Turns off the backlight.
 *
 * Clears the respective GPIO and timer settings.
 *
 * @param  none
 *
 * @return none
 *************************************************************************/
void halLcdShutDownBackLight(void)
{
  LCD_BACKLT_DIR |= LCD_BACKLIGHT_PIN;
  LCD_BACKLT_OUT &= ~(LCD_BACKLIGHT_PIN);
  LCD_BACKLT_SEL &= ~LCD_BACKLIGHT_PIN;

  TA0CCTL3 = 0;
  TA0CTL = 0;

  backlight = 0;
}

/**********************************************************************//**
 * @brief  Set function for the contrast level of the LCD.
 *
 * @param  ContrastLevel The target contrast level
 *
 * @return none
 *************************************************************************/
void halLcdSetContrast(unsigned char ContrastLevel)
{
  if (ContrastLevel > 127) ContrastLevel = 127;
  if (ContrastLevel < 70) ContrastLevel = 70;
  LcdInitMacro[ 0x04 * 6 + 5 ] = ContrastLevel;
  halLcdSendCommand(&LcdInitMacro[ 0x04 * 6 ]);
}

/**********************************************************************//**
 * @brief  Get function for the contrast level of the LCD.
 *
 * @param  none
 *
 * @return ContrastLevel The LCD constrast level
 *************************************************************************/
unsigned char halLcdGetContrast(void)
{
  return LcdInitMacro[ 0x04 * 6 + 5 ] ;
}

/**********************************************************************//**
 * @brief  Turns the LCD cursor on at the current text position.
 *
 * @param  none
 *
 * @return none
 *************************************************************************/
void halLcdCursor(void)
{
  LcdInitMacro[  8 * 6 + 5 ] ^= BIT2;
  halLcdSendCommand(&LcdInitMacro[ 8 * 6 ]);

  LcdInitMacro[ 0x0B * 6 + 5 ] = ((LcdAddress & 0x1F) << 3) ;
  LcdInitMacro[ 0x0B * 6 + 4 ] = ( (LcdAddress & 0x1F) << 3 ) + 3;
  LcdInitMacro[ 0x0C * 6 + 5 ] = (LcdAddress >> 5);
  LcdInitMacro[ 0x0C * 6 + 4 ] = (LcdAddress >> 5) + 7;
  halLcdSendCommand(&LcdInitMacro[ 0x0B * 6 ]);
  halLcdSendCommand(&LcdInitMacro[ 0x0C * 6 ]);

  halLcdSetAddress(LcdAddress);
}

/**********************************************************************//**
 * @brief  Turns off the LCD cursor.
 *
 * @param  none
 *
 * @return none
 *************************************************************************/
void halLcdCursorOff(void)
{
  LcdInitMacro[  8 * 6 + 5 ] &= ~BIT2;
  halLcdSendCommand(&LcdInitMacro[ 8 * 6 ]);
}

/**********************************************************************//**
 * @brief  Inverts the grayscale values of the LCD display (Black <> white).
 *
 * @param  none
 *
 * @return none
 *************************************************************************/
void halLcdReverse(void)
{
  LcdInitMacro[  7 * 6 + 5 ] ^= BIT1;
  halLcdSendCommand(&LcdInitMacro[ 7 * 6 ]);
}

/**********************************************************************//**
 * @brief  Sets the LCD in standby mode to reduce power consumption.
 *
 * @param  none
 *
 * @return none
 *************************************************************************/
void halLcdStandby(void)
{
  LcdInitMacro[ 3 * 6 + 5 ] &= (~BIT3) & (~BIT2);
  LcdInitMacro[ 3 * 6 + 5 ] |= BIT0;
  halLcdSendCommand(&LcdInitMacro[ 3 * 6 ]);
}

/**********************************************************************//**
 * @brief  Puts the LCD into active mode.
 *
 * @param  none
 *
 * @return none
 *************************************************************************/
void halLcdActive(void)
{
  halLcdSendCommand(LcdInitMacro);                  // R00 start oscillation

  // Wait a minimum of 25ms after issuing "start oscillation"
  // command (to accomodate for MCLK up to 25MHz)
  __delay_cycles(250000);

  LcdInitMacro[ 3 * 6 + 5 ] |= BIT3;
  LcdInitMacro[ 3 * 6 + 5 ] &= ~BIT0;
  halLcdSendCommand(&LcdInitMacro[ 3 * 6 ]);        // R03 Power control
}

/**********************************************************************//**
 * @brief  Sets the pointer location in the LCD.
 *
 * - LcdAddress      = Address  					
 * - LcdTableAddress = Correct Address Row + Column
 *                   = (Address / 0x20)* 17 + Column
 *
 * @param  Address The target pointer location in the LCD.
 *
 * @return none
 *************************************************************************/
void halLcdSetAddress(int Address)
{
  int temp;

  Draw_Block_Address_Macro[4] = Address >> 8;
  Draw_Block_Address_Macro[5] = Address & 0xFF;
  halLcdSendCommand(Draw_Block_Address_Macro);
  LcdAddress = Address;
  temp = Address >> 5;                      // Divided by 0x20
  temp = temp + (temp << 4);
  //Multiplied by (1+16) and added by the offset
  LcdTableAddress = temp + (Address & 0x1F);
}

/**********************************************************************//**
 * @brief  Draws a block at the specified LCD address.
 *
 * A block is the smallest addressable memory on the LCD and is
 * equivalent to 8 pixels, each of which is represented by 2 bits
 * that represent a grayscale value between 00b and 11b.
 *
 * @param  Address The address at which to draw the block.
 *
 * @param  Value   The value of the block
 *
 * @return none
 *************************************************************************/
void halLcdDrawBlock(unsigned int Address, unsigned int Value)
{
  halLcdSetAddress(Address);
  halLcdDrawCurrentBlock(Value);
}

/**********************************************************************//**
 * @brief  Writes Value to LCD CGram and MSP430 internal LCD table.
 *
 * Also updates the LcdAddress and LcdTableAddress to the correct values.
 *
 * @param  Value The value of the block to be written to the LCD.
 *
 * @return none
 *************************************************************************/
void halLcdDrawCurrentBlock(unsigned int Value)
{
  int temp;

  Draw_Block_Value_Macro[4] = Value >> 8;
  Draw_Block_Value_Macro[5] = Value & 0xFF;
  LCD_MEM[ LcdTableAddress ] = Value;

  halLcdSendCommand(Draw_Block_Value_Macro);

  LcdAddress++;
  temp = LcdAddress >> 5;                   // Divided by 0x20
  temp = temp + (temp << 4);
  // Multiplied by (1+16) and added by the offset
  LcdTableAddress = temp + (LcdAddress & 0x1F);

  // If LcdAddress gets off the right edge, move to next line
  if ((LcdAddress & 0x1F) > 0x11)
    halLcdSetAddress( (LcdAddress & 0xFFE0) + 0x20 );
  if (LcdAddress == LCD_Size)
    halLcdSetAddress( 0 );
}

/**********************************************************************//**
 * @brief  Returns the LCD CGRAM value at location Address.
 *
 * @param  Address The address of the block to be read from the LCD.
 *
 * @return Value   The value held at the specified address.
 *************************************************************************/
int halLcdReadBlock(unsigned int Address)
{
  int i = 0, Value = 0, ReadData[7];

  halLcdSetAddress( Address );
  halLcdSendCommand(Read_Block_Address_Macro);

  LCD_CS_RST_OUT &= ~LCD_CS_PIN;              // start transfer CS=0
  UCB2TXBUF = 0x77;                         // Transmit first character 0x77

  while (!(UCB2IFG & UCTXIFG));
  while (UCB2STAT & UCBUSY);

  //Read 5 dummies values and 2 valid address data
  LCD_SPI_SEL &= ~LCD_MOSI_PIN;             //Change SPI2C Dir
  LCD_SPI_SEL |= LCD_MISO_PIN;

  for (i = 0; i < 7; i ++ )
  {
    UCB2IFG &= ~UCRXIFG;
    UCB2TXBUF = 1;                          // load dummy byte 1 for clk
    while (!(UCB2IFG & UCRXIFG));
    ReadData[i] = UCB2RXBUF;
  }
  LCD_CS_RST_OUT |= LCD_CS_PIN;              // Stop Transfer CS = 1

  LCD_SPI_SEL |= LCD_MOSI_PIN;               //Change SPI2C Dir
  LCD_SPI_SEL &= ~LCD_MISO_PIN;
  LCD_CS_RST_DIR |= LCD_MOSI_PIN + LCD_CLK_PIN;
  LCD_CS_RST_DIR &= ~LCD_MISO_PIN;

  Value = (ReadData[5] << 8) + ReadData[6];
  return Value;
}

/**********************************************************************//**
 * @brief  Draw a Pixel of grayscale at coordinate (x,y) to LCD
 *
 * @param  x         x-coordinate for grayscale value
 *
 * @param  y         y-coordinate for grayscale value
 *
 * @param  GrayScale The intended grayscale value of the pixel - one of
 *                   four possible settings.
 *
 * @return none
 *************************************************************************/
void halLcdPixel( int x, int y, unsigned char GrayScale)
{
  int  Address, Value;
  unsigned char offset;

  //Each line increments by 0x20
  if ( (x>=0 ) && (x<LCD_COL) && (y>=0) && (y<LCD_ROW))
  {
    Address = (y << 5) + (x >> 3) ;         //Narrow down to 8 possible pixels

    Value = LCD_MEM[(y << 4)+ y + (x>>3)];  //y * 17 --> row. x>>3 --> column

    offset = (x & 0x07) << 1;      //3 LSBs = pos. within the 8 columns
    Value &= ~  (3 << offset);     //clear out the corresponding bits
    Value |= GrayScale << offset;  //set pixel to GrayScale level

    halLcdDrawBlock( Address, Value );
  }
}

/**********************************************************************//**
 * @brief  Clears entire LCD CGRAM as well as LCD_MEM.
 *
 * @param  none
 *
 * @return none
 *************************************************************************/
void halLcdClearScreen(void)
{
  int i, j, k, Current_Location = 0;
  halLcdSetAddress(0);

  for (i=0; i < 110; i++)
  {
    //prepare to send image
    LCD_CS_RST_OUT &= ~LCD_CS_PIN;            //CS = 0 --> Start Transfer
    for ( k = 0; k < 3; k++ )
    {
      while (!(UCB2IFG & UCTXIFG));           // Wait for TXIFG
      UCB2TXBUF = Draw_Block_Value_Macro[k];     // Load data
    }
    while (UCB2STAT & UCBUSY);    	
    LCD_CS_RST_OUT |= LCD_CS_PIN;         //CS = 1 --> Stop Transfer
    LCD_CS_RST_OUT &= ~LCD_CS_PIN;        //CS = 0 --> Start Transfer	
    while (!(UCB2IFG & UCTXIFG));           // Wait for TXIFG
    UCB2TXBUF = Draw_Block_Value_Macro[3];     // Load data

    //send blank line
    for (j=0; j < 17; j++)
    {
  	  LCD_MEM[ LcdTableAddress++ ] = 0x00;
      while (!(UCB2IFG & UCTXIFG));       // Wait for TXIFG
      UCB2TXBUF = 0x00;                   // Load data
      while (!(UCB2IFG & UCTXIFG));       // Wait for TXIFG
      UCB2TXBUF = 0x00;                   // Load data
    }
    //Clear the partially visible block at the edge of the screen
    while (!(UCB2IFG & UCTXIFG));       // Wait for TXIFG
      UCB2TXBUF = 0x00;                   // Load data
    while (!(UCB2IFG & UCTXIFG));       // Wait for TXIFG
      UCB2TXBUF = 0x00;                   // Load data
    while (UCB2STAT & UCBUSY);    	
    LCD_CS_RST_OUT |= LCD_CS_PIN;             //CS = 1 --> Stop Transfer

    Current_Location += 0x20;
    halLcdSetAddress(Current_Location );
  }

  halLcdSetAddress(0);
}

/**********************************************************************//**
 * @brief  Loads an image of size = rows * columns, starting at the
 *         coordinate (x,y).
 *
 * @param  Image[] The image to be loaded
 *
 * @param  Rows    The number of rows in the image. Size = Rows * Columns.
 *
 * @param  Columns The number of columns in the image. Size = Rows * Columns.
 *
 * @param  x       x-coordinate of the image's starting location
 *
 * @param  y       y-coordinate of the image's starting location
 *
 * @return none
 *************************************************************************/
void halLcdImage(const unsigned int Image[], int Columns, int Rows, int x, int y)
{
  int i, CurrentLocation;

  CurrentLocation = (y << 5) + (x >> 3);
  halLcdSetAddress(CurrentLocation);
  for (i=0; i < Rows; i++)
  {
    halLcdDrawCurrentLine(Image, Columns);
    Image += Columns;
    CurrentLocation += 0x20;
    halLcdSetAddress(CurrentLocation);
  }
}

/**********************************************************************//**
 * @brief  Writes Value to LCD CGram and MSP430 internal LCD table.
 *
 * Also updates the LcdAddress and LcdTableAddress to the correct values.
 *
 * @param  *value Pointer to the line to be written to the LCD.
 *
 * @return none
 *************************************************************************/
void halLcdDrawCurrentLine(const unsigned int *value, int Columns)
{
  unsigned char i;

  //prepare to send image
  LCD_CS_RST_OUT &= ~LCD_CS_PIN;            //CS = 0 --> Start Transfer
  for ( i = 0; i < 3; i++ )
  {
      while (!(UCB2IFG & UCTXIFG));           // Wait for TXIFG
      UCB2TXBUF = Draw_Block_Value_Macro[i];     // Load data
  }
  while (UCB2STAT & UCBUSY);    	
  LCD_CS_RST_OUT |= LCD_CS_PIN;         //CS = 1 --> Stop Transfer
  LCD_CS_RST_OUT &= ~LCD_CS_PIN;        //CS = 0 --> Start Transfer	
  while (!(UCB2IFG & UCTXIFG));           // Wait for TXIFG
  UCB2TXBUF = Draw_Block_Value_Macro[3];     // Load data

  //send the image
  for ( i = 0; i < Columns; i++ )
  {	
    // Make sure we are not writing outside LCD_MEM[]
    if (LcdTableAddress >= sizeof(LCD_MEM)) {
    	break;
    }
  	LCD_MEM[ LcdTableAddress++ ] = *value;
  	while (!(UCB2IFG & UCTXIFG));           // Wait for TXIFG
    UCB2TXBUF = (*value) >> 8;                   // Load data
    while (!(UCB2IFG & UCTXIFG));           // Wait for TXIFG
    UCB2TXBUF = (*value++) & 0xFF;                   // Load data
  }

  while (UCB2STAT & UCBUSY);    	
  LCD_CS_RST_OUT |= LCD_CS_PIN;             //CS = 1 --> Stop Transfer
}

/**********************************************************************//**
 * @brief  Clears an image of size rows x columns starting at (x, y).
 *
 * @param  Columns The size, in columns, of the image to be cleared.
 *
 * @param  Rows    The size, in rows, of the image to be cleared.
 *
 * @param  x       x-coordinate of the image to be cleared
 *
 * @param  y       y-coordinate of the image to be cleared
 *
 * @return none
 *************************************************************************/
void halLcdClearImage(int Columns, int Rows, int x, int y)
{
  int i,j,k, Current_Location;
  Current_Location = (y << 5) + (x >> 3);
  halLcdSetAddress( Current_Location );

  for (i=0; i < Rows; i++)
  {
    //prepare to send image
    LCD_CS_RST_OUT &= ~LCD_CS_PIN;            //CS = 0 --> Start Transfer
    for ( k = 0; k < 3; k++ )
    {
      while (!(UCB2IFG & UCTXIFG));           // Wait for TXIFG
      UCB2TXBUF = Draw_Block_Value_Macro[k];     // Load data
    }
    while (UCB2STAT & UCBUSY);    	
    LCD_CS_RST_OUT |= LCD_CS_PIN;         //CS = 1 --> Stop Transfer
    LCD_CS_RST_OUT &= ~LCD_CS_PIN;        //CS = 0 --> Start Transfer	
    while (!(UCB2IFG & UCTXIFG));           // Wait for TXIFG
    UCB2TXBUF = Draw_Block_Value_Macro[3];     // Load data

    //send blank line
    for (j=0; j < Columns; j++)
    {
  	  LCD_MEM[ LcdTableAddress++ ] = 0x00;
      while (!(UCB2IFG & UCTXIFG));       // Wait for TXIFG
      UCB2TXBUF = 0x00;                   // Load data
      while (!(UCB2IFG & UCTXIFG));       // Wait for TXIFG
      UCB2TXBUF = 0x00;                   // Load data
    }
    while (UCB2STAT & UCBUSY);    	
    LCD_CS_RST_OUT |= LCD_CS_PIN;             //CS = 1 --> Stop Transfer

    Current_Location += 0x20;
    halLcdSetAddress(Current_Location );
  }
}

/**********************************************************************//**
 * @brief  Writes Value to LCD CGRAM. Pointers internal to the LCD
 *         are also updated.
 *
 * @param  Value The value to be written to the current LCD pointer
 *
 * @return none
 *************************************************************************/
void halLcdDrawTextBlock(unsigned int Value)
{
  int temp;

  Draw_Block_Value_Macro[4] = Value >> 8;
  Draw_Block_Value_Macro[5] = Value & 0xFF;
  LCD_MEM[ LcdTableAddress ] = Value;

  halLcdSendCommand(Draw_Block_Value_Macro);

  LcdAddress++;
  temp = LcdAddress >> 5;                   // Divided by 0x20
  temp = temp + (temp << 4);
  //Multiplied by (1+16) and added by the offset
  LcdTableAddress = temp + (LcdAddress & 0x1F);

  // If LcdAddress gets off the right edge, move to next line
  if ((LcdAddress & 0x1F) > 0x10)
    halLcdSetAddress( (LcdAddress & 0xFFE0) + 0x20 );

  if (LcdAddress >= LCD_Size)
    halLcdSetAddress( 0 );
}

/**********************************************************************//**
 * @brief  Displays the string to the LCD starting at current location.
 *
 * Writes all the data to LCD_MEM first, then updates all corresponding
 * LCD CGRAM locations at once, in a continuous fashion.
 *
 * @param  String[]  The string to be displayed on LCD.
 *
 * @param  TextStyle Value that specifies whether the string is to be
 *                   inverted or overwritten.
 *                   - Invert    = 0x01
 *                   - Overwrite = 0x04
 *
 * @return none
 *************************************************************************/
void halLcdPrint( char String[], unsigned char TextStyle)
{
  int i, j, Counter=0, BlockValue;
  int Address, LCD_MEM_Add, ActualAddress;
  int temp;
  char LookUpChar;

  ActualAddress = LcdAddress;
  Counter =  LcdAddress & 0x1F;
  i=0;

  while (String[i]!=0)                      // Stop on null character
  {
    LookUpChar = fonts_lookup[String[i]];

    for (j=0;j < FONT_HEIGHT ;j++)
    {
      Address = ActualAddress + j*0x20;
      temp = Address >> 5;
      temp += (temp <<4);

      LCD_MEM_Add = temp + (Address & 0x1F);

      BlockValue = LCD_MEM[ LCD_MEM_Add ];

      if(TextStyle & GRAYSCALE_TEXT)
      {
      	if (TextStyle & INVERT_TEXT)
      	  if (TextStyle & OVERWRITE_TEXT)
      	    BlockValue = 0xAAAA - GrayScale_fonts[LookUpChar*(FONT_HEIGHT+1) +j];
      	  else
      	    BlockValue |= 0xAAAA - GrayScale_fonts[LookUpChar*(FONT_HEIGHT+1) +j];
      	else
      	  if (TextStyle & OVERWRITE_TEXT)
            BlockValue = GrayScale_fonts[LookUpChar*(FONT_HEIGHT+1) +j];
          else
            BlockValue |= GrayScale_fonts[LookUpChar*(FONT_HEIGHT+1) +j];
      }
      else
      {
        if (TextStyle & INVERT_TEXT)
          if (TextStyle & OVERWRITE_TEXT)
            BlockValue = 0xFFFF - fonts[LookUpChar*13+j];
          else
            BlockValue |= 0xFFFF - fonts[LookUpChar*13+j];

        else
          if (TextStyle & OVERWRITE_TEXT)
            BlockValue = fonts[LookUpChar*(FONT_HEIGHT+1) +j];
          else
            BlockValue |= fonts[LookUpChar*(FONT_HEIGHT+1) +j];
      }
      halLcdDrawBlock( Address, BlockValue);
    }

    Counter++;
    if (Counter == 17)
    {
      Counter = 0;
      ActualAddress += 0x20*FONT_HEIGHT  - 16;
      if (ActualAddress > LCD_Last_Pixel-0x20*FONT_HEIGHT )
        ActualAddress = 0;
    }
    else
      ActualAddress++;
    i++;
  }
  halLcdSetAddress(ActualAddress);

}

/**********************************************************************//**
 * @brief  Displays the string to the LCD starting at (x,y) location.
 *
 * Writes all the data to LCD_MEM first, then updates all corresponding
 * LCD CGRAM locations at once, in a continuous fashion.
 *
 * @param  String[]  String to be displayed on LCD
 *
 * @param  x         x-coordinate of the write location on the LCD
 *
 * @param  y         y-coordinate of the write location on the LCD
 *
 * @param  TextStyle Value that specifies whether the string is to be
 *                   inverted or overwritten.
 *                   - Invert    = 0x01
 *                   - Overwrite = 0x04
 *************************************************************************/
void halLcdPrintXY( char String[], int x, int y, unsigned char TextStyle)
{
  //Each line increments by 0x20
  halLcdSetAddress( (y << 5) + (x >> 3)) ;  //Narrow down to 8 possible pixels
  halLcdPrint(String,  TextStyle);
}

/**********************************************************************//**
 * @brief  Displays a string on the LCD on the specified line.
 *
 * @param  String[]  The string to be displayed on LCD.
 *
 * @param  Line      The line on the LCD on which to print the string.
 *
 * @param  TextStyle Value that specifies whether the string is to be
 *                   inverted or overwritten.
 *                   - Invert    = 0x01
 *                   - Overwrite = 0x04
 *
 * @return none
 *************************************************************************/
void halLcdPrintLine(char String[], unsigned char Line, unsigned char TextStyle)
{
  int temp;
  temp = Line * FONT_HEIGHT ;
  halLcdSetAddress( temp << 5 ) ;           // 0x20 = 2^5
  halLcdPrint(String, TextStyle);
}

/**********************************************************************//**
 * @brief  Prints a string beginning on a given line and column.
 *
 * @param  String[]  The string to be displayed on LCD.
 *
 * @param  Line      The line on which to print the string of text
 *
 * @param  Col       The column on which to print the string of text
 *
 * @param  TextStyle Value that specifies whether the string is to be
 *                   inverted or overwritten.
 *                   - Invert    = 0x01
 *                   - Overwrite = 0x04
 *
 * @return none
 *************************************************************************/
void halLcdPrintLineCol(char String[], unsigned char Line, unsigned char Col,
                        unsigned char TextStyle)
{
  int temp;

  temp = Line * FONT_HEIGHT;
  temp <<= 5;
  temp += Col;

  halLcdSetAddress( temp ) ;                // 0x20 = 2^5
  halLcdPrint(String, TextStyle);
}


/**********************************************************************//**
 * @brief  Draws a horizontral line from (x1,y) to (x2,y) of GrayScale level
 *
 * @param  x1        x-coordinate of the first point
 *
 * @param  x2        x-coordinate of the second point
 *
 * @param  y         y-coordinate of both points
 *
 * @param  GrayScale Grayscale level of the horizontal line
 *
 * @return none
 *************************************************************************/
void halLcdHLine( int x1, int x2, int y, unsigned char GrayScale)
{
  int x_dir, x;
  if ( x1 < x2 )
    x_dir = 1;
  else
    x_dir = -1;
  x = x1;
  while (x != x2)
  {
    halLcdPixel( x,y, GrayScale);
    x += x_dir;
  }
}

/**********************************************************************//**
 * @brief  Draws a vertical line from (x,y1) to (x,y2) of GrayScale level
 *
 * @param  x         x-coordinate of both points
 *
 * @param  y1        y-coordinate of the first point
 *
 * @param  y2        y-coordinate of the second point
 *
 * @param  GrayScale GrayScale level of the vertical line
 *
 * @return none
 *************************************************************************/
void halLcdVLine( int x, int y1, int y2, unsigned char GrayScale)
{
  int y_dir, y;
  if ( y1 < y2 )
    y_dir = 1;
  else
    y_dir = -1;
  y = y1;
  while (y != y2)
  {
    halLcdPixel( x,y, GrayScale);
    y += y_dir;
  }
}

/**********************************************************************//**
 * @brief  Draws a line from (x1,y1) to (x2,y2) of GrayScale level.
 *
 * Uses Bresenham's line algorithm.
 *
 * @param  x1         x-coordinate of the first point
 *
 * @param  y1         y-coordinate of the first point
 *
 * @param  x2         x-coordinate of the second point
 *
 * @param  y2         y-coordinate of the second point
 *
 * @param  GrayScale  Grayscale level of the line
 *
 * @return none
 *************************************************************************/
void halLcdLine( int x1, int y1, int x2, int y2, unsigned char GrayScale)
{
  int x, y, deltay, deltax, d;
  int x_dir, y_dir;

  if ( x1 == x2 )
    halLcdVLine( x1, y1, y2, GrayScale );
  else
  {
    if ( y1 == y2 )
      halLcdHLine( x1, x2, y1, GrayScale );
    else                                    // a diagonal line
    {
      if (x1 > x2)
        x_dir = -1;
      else x_dir = 1;
      if (y1 > y2)
        y_dir = -1;
      else y_dir = 1;

      x = x1;
      y = y1;
      deltay = ABS(y2 - y1);
      deltax = ABS(x2 - x1);

      if (deltax >= deltay)
      {
        d = (deltay << 1) - deltax;
        while (x != x2)
        {
          halLcdPixel(x, y,  GrayScale);
          if ( d < 0 )
            d += (deltay << 1);
          else
          {
            d += ((deltay - deltax) << 1);
            y += y_dir;
          }
          x += x_dir;
        }
      }
      else
      {
        d = (deltax << 1) - deltay;
        while (y != y2)
        {
          halLcdPixel(x, y, GrayScale);
          if ( d < 0 )
            d += (deltax << 1);
          else
          {
            d += ((deltax - deltay) << 1);
            x += x_dir;
          }
          y += y_dir;
        }
      }
    }
  }
}


/**********************************************************************//**
 * @brief  Draw a circle of Radius with center at (x,y) of GrayScale level.
 *
 * Uses Bresenham's circle algorithm
 *
 * @param  x         x-coordinate of the circle's center point
 *
 * @param  y         y-coordinate of the circle's center point
 *
 * @param  Radius    Radius of the circle
 *
 * @param  GrayScale Grayscale level of the circle
 *************************************************************************/
void halLcdCircle(int x, int y, int Radius, int GrayScale)
{
  int xx, yy, ddF_x, ddF_y, f;

  ddF_x = 0;
  ddF_y = -(2 * Radius);
  f = 1 - Radius;

  xx = 0;
  yy = Radius;
  halLcdPixel(x + xx, y + yy, GrayScale);
  halLcdPixel(x + xx, y - yy, GrayScale);
  halLcdPixel(x - xx, y + yy, GrayScale);
  halLcdPixel(x - xx, y - yy, GrayScale);
  halLcdPixel(x + yy, y + xx, GrayScale);
  halLcdPixel(x + yy, y - xx, GrayScale);
  halLcdPixel(x - yy, y + xx, GrayScale);
  halLcdPixel(x - yy, y - xx, GrayScale);
  while (xx < yy)
  {
    if (f >= 0)
    {
      yy--;
      ddF_y += 2;
      f += ddF_y;
    }
    xx++;
    ddF_x += 2;
    f += ddF_x + 1;
    halLcdPixel(x + xx, y + yy, GrayScale);
    halLcdPixel(x + xx, y - yy, GrayScale);
    halLcdPixel(x - xx, y + yy, GrayScale);
    halLcdPixel(x - xx, y - yy, GrayScale);
    halLcdPixel(x + yy, y + xx, GrayScale);
    halLcdPixel(x + yy, y - xx, GrayScale);
    halLcdPixel(x - yy, y + xx, GrayScale);
    halLcdPixel(x - yy, y - xx, GrayScale);
  }
}

/**********************************************************************//**
 * @brief  Scrolls a single row of pixels one column to the left.
 *
 * The column that is scrolled out of the left side of the LCD will be
 * displayed the right side of the LCD.
 *
 * @param  y    The row of pixels to scroll. y = 0 is at the top-left
 *              corner of the LCD.
 *
 * @return none
 *************************************************************************/
void halLcdScrollRow(int y)
{
  int i, Address, LcdTableAddressTemp;
  unsigned int temp;

  Address = y << 5;

  halLcdSetAddress( Address );

  //Multiplied by (1+16) and added by the offset
  LcdTableAddressTemp = y + (y << 4);
  temp = ((LCD_MEM[LcdTableAddressTemp] & 0x0003) <<14);

  for (i = 0; i < 0x10; i++)
    halLcdDrawCurrentBlock( ( (LCD_MEM[LcdTableAddressTemp+i] & 0xFFFC ) >> 2 ) \
    + ((LCD_MEM[LcdTableAddressTemp+i+1] & 0x0003) << 14 ));

  halLcdDrawCurrentBlock( (( LCD_MEM[LcdTableAddressTemp + 0x10] & 0xFFFC ) >> 2) + temp);
}

/**********************************************************************//**
 * @brief  Scrolls multiple rows of pixels, yStart to yEnd,
 *         one column to the left.
 *
 * The column that is scrolled out of the left side of the LCD will be
 * displayed the right side of the LCD. y = 0 is at the top-left of the
 * LCD screen.
 *
 * @param  yStart The beginning row to be scrolled
 *
 * @param  yEnd   The last row to be scrolled
 *
 * @return none
 *************************************************************************/
void halLcdHScroll(int yStart, int yEnd)
{
  int i ;

  for (i = yStart; i < yEnd+1; i++)
    halLcdScrollRow(i);
}

/**********************************************************************//**
 * @brief  Scrolls a line of text one column to the left.
 *
 * @param  Line The line of text to be scrolled.
 *
 * @return none
 *************************************************************************/
void halLcdScrollLine(int Line)
{
  int i, Row ;

  Row = Line * FONT_HEIGHT;

  for (i = Row; i < Row + FONT_HEIGHT ; i++)
    halLcdScrollRow(i);
}
