/*****************************************************************************
 * (c) Copyright 2009 Actel Corporation.  All rights reserved.
 *
 * Author : Actel Application Team
 * Rev    : 1.0.0.0
 * Description: Device driver for the on-board OLED for SmartFusion KITS
 *  Implementation of sample basic driver for OLED display found on Actel
 *  SmartFusion development boards.
 *  This code is intended as an example of using the SmartFusion I2C driver.
 *****************************************************************************/

  #include "oled.h"
#include "../bsp_config.h"

/***************************************************************************//**
  Command definitions for the SSD300 controller inside the OLED display module.
 */
#define CMD_DISPLAY_OFF_SET   0xD3
#define CMD_PANEL_ON          0xAF
#define CMD_PANEL_OFF         0xAE
#define CMD_DC_DC             0xAD
#define CMD_DC_DC_DEFAULT_ON  0x8B
#define CMD_DC_DC_OFF         0x8A
#define CMD_DISPLAY_ALL_ON    0xA5
#define CMD_DISPLAY_ALL_OFF   0xA4
#define CMD_DISPLAY_NON_INV   0xA6
#define CMD_DISPLAY_INV       0xA7
#define CMD_ARECOL_LPM        0xD8
#define CMD_ARECOL_MONO       0x00
#define CMD_ARECOL_COLOR      0x30
#define CMD_LPM_ON            0x05
#define CMD_LPM_OFF           0x00
#define CMD_CONTRAST          0x81
#define CMD_MIRROR_HORI_ON    0xC8
#define CMD_MIRROR_HORI_OFF   0xC0
#define CMD_MIRROR_VERT_ON    0xA1
#define CMD_MIRROR_VERT_OFF   0xA0
#define CMD_HORI_SCRL         0x26
#define CMD_HORI_SCRL_ON      0x2F
#define CMD_HORI_SCRL_OFF     0x2E
#define CMD_MUX_RATIO          0xA8
#define CMD_MUX_RATIO_31      0x23

#define CMD_PAGE_0            0xB0
#define CMD_PAGE_1            0xB1
#define CMD_PAGE_2            0xB2
#define CMD_PAGE_3            0xB3
#define CMD_PAGE_4            0xB4
#define CMD_PAGE_5            0xB5

#define CMD_LOW_NIB_COL       0x00
#define CMD_HIGH_NIB_COL      0x10

#define CMD_START_LINE        0x50
#define CONTRAST_DEFAULT      0xFF
#define CONTRAST_25_PERC      0x40
#define CONTRAST_100_PERC     0xFF
#define CONTRAST_0_PERC       0x00
#define SCROLL_1_COLUMN       0x01
#define SCROLL_2_COLUMN       0x02
#define SCROLL_3_COLUMN       0x03
#define SCROLL_4_COLUMN       0x04
#define SCROLL_PAGE_0         0x00
#define SCROLL_PAGE_1         0x01
#define SCROLL_PAGE_2         0x02
#define SCROLL_PAGE_3         0x03
#define SCROLL_PAGE_4         0x04
#define SCROLL_PAGE_5         0x05
#define SCROLL_12_FRAMES      0x00
#define SCROLL_64_FRAMES      0x01
#define SCROLL_128_FRAMES     0x02
#define SCROLL_256_FRAMES     0x03
#define SCROLL_PER_STEP       0x01
#define PAGE0_COLOR_BAG       0x92
#define PAGE1_COLOR_BAG       0x93

/***************************************************************************//**
  OLED display I2C communication protocol control byte values. Used to indicate
  whether the byte following the control byte is to be interpreted by the OLED
  display as a command or data byte.
 */
#define  OLED_COMMAND_CODE  0x80
#define  OLED_DATA_CODE     0xC0

/***************************************************************************//**
  I2C serial address of OLED display.
 */
#define OLED_SLAVE_ADDRESS    0x78

/***************************************************************************//**
  Bitmaps of the character set.
  Each character is 5 pixels wide and 7 pixels high.
  The table is indexed on ASCII character codes.
 */
#define CHARACTER_WIDTH   5

const unsigned char oled_ascii_character_set[255][CHARACTER_WIDTH] =
{
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},

    {0x00, 0x00, 0x5F, 0x00, 0x00},
    {0x00, 0x07, 0x00, 0x07, 0x00},
    {0x14, 0x7F, 0x14, 0x7F, 0x14},
    {0x24, 0x2A, 0x7F, 0x2A, 0x12},
    {0x23, 0x13, 0x08, 0x64, 0x62},
    {0x36, 0x49, 0x55, 0x22, 0x50},
    {0x00, 0x05, 0x03, 0x00, 0x00},
    {0x00, 0x1C, 0x22, 0x41, 0x00},
    {0x00, 0x41, 0x22, 0x1C, 0x00},
    {0x14, 0x08, 0x3E, 0x08, 0x14},
    {0x08, 0x08, 0x3E, 0x08, 0x08},
    {0x00, 0x50, 0x30, 0x00, 0x00},
    {0x08, 0x08, 0x08, 0x08, 0x08},
    {0x00, 0x60, 0x60, 0x00, 0x00},
    {0x20, 0x10, 0x08, 0x04, 0x02},
    {0x3E, 0x51, 0x49, 0x45, 0x3E},
    {0x00, 0x42, 0x7F, 0x40, 0x00},
    {0x42, 0x61, 0x51, 0x49, 0x46},
    {0x21, 0x41, 0x45, 0x4B, 0x31},
    {0x18, 0x14, 0x12, 0x7F, 0x10},
    {0x27, 0x45, 0x45, 0x45, 0x39},
    {0x3C, 0x4A, 0x49, 0x49, 0x30},
    {0x01, 0x71, 0x09, 0x05, 0x03},
    {0x36, 0x49, 0x49, 0x49, 0x36},
    {0x06, 0x49, 0x49, 0x29, 0x1E},
    {0x00, 0x36, 0x36, 0x00, 0x00},
    {0x00, 0x56, 0x36, 0x00, 0x00},
    {0x08, 0x14, 0x22, 0x41, 0x00},
    {0x14, 0x14, 0x14, 0x14, 0x14},
    {0x00, 0x41, 0x22, 0x14, 0x08},
    {0x02, 0x01, 0x51, 0x09, 0x06},
    {0x32, 0x49, 0x79, 0x41, 0x3E},
    {0x7E, 0x11, 0x11, 0x11, 0x7E},
    {0x7F, 0x49, 0x49, 0x49, 0x36},
    {0x3E, 0x41, 0x41, 0x41, 0x22},
    {0x7F, 0x41, 0x41, 0x22, 0x1C},
    {0x7F, 0x49, 0x49, 0x49, 0x41},
    {0x7F, 0x09, 0x09, 0x09, 0x01},
    {0x3E, 0x41, 0x49, 0x49, 0x7A},
    {0x7F, 0x08, 0x08, 0x08, 0x7F},
    {0x00, 0x41, 0x7F, 0x41, 0x00},
    {0x20, 0x40, 0x41, 0x3F, 0x01},
    {0x7F, 0x08, 0x14, 0x22, 0x41},
    {0x3F, 0x40, 0x40, 0x40, 0x40},
    {0x7F, 0x02, 0x0C, 0x02, 0x7F},
    {0x7F, 0x04, 0x08, 0x10, 0x7F},
    {0x3E, 0x41, 0x41, 0x41, 0x3E},
    {0x7F, 0x09, 0x09, 0x09, 0x06},
    {0x3E, 0x41, 0x51, 0x21, 0x5E},
    {0x7F, 0x09, 0x19, 0x29, 0x46},
    {0x46, 0x49, 0x49, 0x49, 0x31},
    {0x01, 0x01, 0x7F, 0x01, 0x01},
    {0x3F, 0x40, 0x40, 0x40, 0x3F},
    {0x1F, 0x20, 0x40, 0x20, 0x1F},
    {0x3F, 0x40, 0x38, 0x40, 0x3F},
    {0x63, 0x14, 0x08, 0x14, 0x63},
    {0x07, 0x08, 0x70, 0x08, 0x07},
    {0x61, 0x51, 0x49, 0x45, 0x43},
    {0x00, 0x7F, 0x41, 0x41, 0x00},
    {0x02, 0x04, 0x08, 0x10, 0x20},
    {0x00, 0x41, 0x41, 0x7F, 0x00},
    {0x04, 0x02, 0x01, 0x02, 0x04},
    {0x40, 0x40, 0x40, 0x40, 0x40},
    {0x00, 0x01, 0x02, 0x04, 0x00},
    {0x20, 0x54, 0x54, 0x54, 0x78},
    {0x7F, 0x48, 0x44, 0x44, 0x38},
    {0x38, 0x44, 0x44, 0x44, 0x20},
    {0x30, 0x48, 0x48, 0x50, 0x7F},
    {0x38, 0x54, 0x54, 0x54, 0x18},
    {0x10, 0x7E, 0x11, 0x01, 0x02},
    {0x0C, 0x52, 0x52, 0x52, 0x3E},
    {0x7F, 0x08, 0x04, 0x04, 0x78},
    {0x00, 0x44, 0x7D, 0x40, 0x00},
    {0x20, 0x40, 0x44, 0x3D, 0x00},
    {0x7F, 0x10, 0x28, 0x44, 0x00},
    {0x00, 0x41, 0x7F, 0x40, 0x00},
    {0x7C, 0x04, 0x18, 0x04, 0x78},
    {0x7C, 0x08, 0x04, 0x04, 0x78},
    {0x38, 0x44, 0x44, 0x44, 0x38},
    {0x7C, 0x14, 0x14, 0x14, 0x08},
    {0x08, 0x14, 0x14, 0x18, 0x7C},
    {0x7C, 0x08, 0x04, 0x04, 0x08},
    {0x48, 0x54, 0x54, 0x54, 0x20},
    {0x04, 0x3F, 0x44, 0x40, 0x20},
    {0x3C, 0x40, 0x40, 0x20, 0x7C},
    {0x1C, 0x20, 0x40, 0x20, 0x1C},
    {0x3C, 0x40, 0x30, 0x40, 0x3C},
    {0x44, 0x28, 0x10, 0x28, 0x44},
    {0x0C, 0x50, 0x50, 0x50, 0x3C},
    {0x44, 0x64, 0x54, 0x4C, 0x44},

    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00},

    {0x07, 0x05, 0x07, 0x00, 0x00},
    {0x12, 0x19, 0x16, 0x00, 0x00},
    {0x00, 0x00, 0x00, 0x00, 0x00}

};

#define FIRST_CHARACTER       0

/***************************************************************************//**
  The g_p_oled_i2c global variable is only used inside the OLED driver. It
  identifies the MSS I2C block used to communicate with the OLED display.
 */
static mss_i2c_instance_t * g_p_oled_i2c = OLED_I2C_INSTANCE;

/***************************************************************************//**
  The OLED_set_cursor function sets the cursor position.

  @param line
  The line parameter specifies the line at which to set the cursor. It can
  take the values:
  - FIRST_LINE
  - SECOND_LINE

  @param char_offset
  The char_offset paraemter specifies the character offset on a line where to
  set the cursor location. It can be set to FIRST_CHARACTER to set the cursor
  at the start of a line.
 */
void OLED_set_cursor
(
    uint8_t line,
    uint8_t char_offset
);
/***************************************************************************//**
  The OLED_write_string function displays the input string to the OLED panel.

  @param string
  The string parameter is a pointer to the zero-terminated to display on the
  OLED.
 */
void OLED_write_string( const char *string);

/***************************************************************************//**
  The OLED_write_char function displays a single character to the display.

  @param data_char
    The data_char parameter is the ASCII code of the character to display.
*/
void OLED_write_char( const uint8_t data_char );
/***************************************************************************//**
  OLED_init()
  See "oled.h" for details of how to use this function.
 */
void OLED_init(void )
{
    uint8_t oled_init_sequence1[] =
    {
        OLED_COMMAND_CODE, CMD_DISPLAY_NON_INV,
        OLED_COMMAND_CODE, CMD_DISPLAY_ALL_OFF,
        OLED_COMMAND_CODE, CMD_MIRROR_HORI_ON,
        OLED_COMMAND_CODE, CMD_MIRROR_VERT_OFF,
        OLED_COMMAND_CODE, CMD_HORI_SCRL_OFF,
        OLED_COMMAND_CODE, CMD_CONTRAST,
        OLED_COMMAND_CODE, CONTRAST_DEFAULT,
        OLED_COMMAND_CODE, CMD_ARECOL_LPM,
        OLED_COMMAND_CODE, CMD_ARECOL_MONO^CMD_LPM_OFF
    };

    uint8_t oled_init_sequence2[] =
    {
        OLED_COMMAND_CODE, CMD_START_LINE,
        OLED_COMMAND_CODE, CMD_PANEL_ON
    };

    MSS_I2C_init( g_p_oled_i2c, OLED_SLAVE_ADDRESS, MSS_I2C_PCLK_DIV_60 );

    MSS_I2C_write( g_p_oled_i2c, OLED_SLAVE_ADDRESS, oled_init_sequence1, sizeof(oled_init_sequence1), MSS_I2C_RELEASE_BUS );
    MSS_I2C_wait_complete( g_p_oled_i2c );

    OLED_clear_display(BOTH_LINES);

    MSS_I2C_write( g_p_oled_i2c, OLED_SLAVE_ADDRESS, oled_init_sequence2, sizeof(oled_init_sequence2), MSS_I2C_RELEASE_BUS );
    MSS_I2C_wait_complete( g_p_oled_i2c );

    OLED_set_cursor( FIRST_LINE, FIRST_CHARACTER );
}

/***************************************************************************//**
  OLED_clear_display()
  See "oled.h" for details of how to use this function.
 */
void OLED_clear_display( oled_no_of_line LINES )
{
    uint8_t i, j,start_line,end_line;
    uint8_t clear_8_columns[] =
    {
        OLED_DATA_CODE, 0x00,
        OLED_DATA_CODE, 0x00,
        OLED_DATA_CODE, 0x00,
        OLED_DATA_CODE, 0x00,
        OLED_DATA_CODE, 0x00,
        OLED_DATA_CODE, 0x00,
        OLED_DATA_CODE, 0x00,
        OLED_DATA_CODE, 0x00
    };

    switch(LINES)
    {
        case FIRST_LINE:
        {
            start_line = FIRST_LINE;
            end_line = FIRST_LINE;
        }

        case SECOND_LINE:
        {
            start_line = SECOND_LINE;
            end_line = SECOND_LINE;
        }

        case BOTH_LINES:
        {
            start_line = FIRST_LINE;
            end_line = SECOND_LINE;
        }

    }

    for( j = start_line; j <= end_line; ++j )
    {
        OLED_set_cursor( j, FIRST_CHARACTER );
        for( i = 0; i < 13; ++i )
        {
            MSS_I2C_write( g_p_oled_i2c, OLED_SLAVE_ADDRESS, clear_8_columns, sizeof(clear_8_columns), MSS_I2C_RELEASE_BUS );
            MSS_I2C_wait_complete( g_p_oled_i2c );
        }
    }
}

/***************************************************************************//**
  OLED_set_cursor()
  See definition of OLED_set_cursor() for details of how to use this function.
 */
void OLED_set_cursor
(
    uint8_t line,
    uint8_t char_offset
)
{
    uint8_t command_sequence[] =
    {
        OLED_COMMAND_CODE, CMD_LOW_NIB_COL,
        OLED_COMMAND_CODE, CMD_HIGH_NIB_COL,
        OLED_COMMAND_CODE, CMD_PAGE_0
    };
    uint8_t low_nib, high_nib;

    ++char_offset;
    char_offset *= CHARACTER_WIDTH;
    low_nib = 0x0F & char_offset;
    high_nib = (0xF0 & char_offset) >> 4;
    line += 2;

    command_sequence[1] |= low_nib;
    command_sequence[3] |= high_nib;
    command_sequence[5] |= line;
    MSS_I2C_write( g_p_oled_i2c, OLED_SLAVE_ADDRESS, command_sequence, sizeof(command_sequence), MSS_I2C_RELEASE_BUS );
    MSS_I2C_wait_complete( g_p_oled_i2c );
}

/***************************************************************************//**
  OLED_write_string()
  See definition of OLED_write_string for details of how to use this function.
 */
void OLED_write_string
(
    const char *string
)
{
  while (*string != 0)
  {
      OLED_write_char( *string );
      ++string;
  }
}

/***************************************************************************//**
  OLED_write_char()
  See definition of OLED_write_char()  for details of how to use this function.
 */
void OLED_write_char
(
    const uint8_t data_char
)
{
    uint8_t txbuff[10];
    uint8_t i;

    for ( i = 0; i < CHARACTER_WIDTH; ++i )
    {
        txbuff[i * 2] = OLED_DATA_CODE;
        txbuff[(i * 2) + 1] = oled_ascii_character_set[data_char][i];
    }
    MSS_I2C_write( g_p_oled_i2c, OLED_SLAVE_ADDRESS, txbuff, sizeof(txbuff), MSS_I2C_RELEASE_BUS );
    MSS_I2C_wait_complete( g_p_oled_i2c );
}

/***************************************************************************//**
  OLED_horizontal_scroll()
  See "oled.h" for details of how to use this function.
 */
void OLED_horizontal_scroll(struct oled_data * horiz_scroll)
{
    uint8_t horiz_scroll_on_off[] =
    {
        OLED_COMMAND_CODE, CMD_HORI_SCRL_OFF,
    };

    uint8_t horiz_scroll_setup_data[] =
    {
        OLED_COMMAND_CODE, CMD_HORI_SCRL,
        OLED_COMMAND_CODE, SCROLL_PER_STEP,
        OLED_COMMAND_CODE, SCROLL_PAGE_0,
        OLED_COMMAND_CODE, SCROLL_12_FRAMES,
        OLED_COMMAND_CODE, SCROLL_PAGE_1,
    };
    MSS_I2C_write( g_p_oled_i2c, OLED_SLAVE_ADDRESS, horiz_scroll_on_off, sizeof(horiz_scroll_on_off), MSS_I2C_RELEASE_BUS );
    MSS_I2C_wait_complete( g_p_oled_i2c );

    if(horiz_scroll->on_off == 1)
    {
        horiz_scroll_setup_data[3] = horiz_scroll->column_scrool_per_step;
        horiz_scroll_setup_data[5] = horiz_scroll->start_page;
        horiz_scroll_setup_data[7] = horiz_scroll->time_intrval_btw_scroll_step;
        horiz_scroll_setup_data[9] = horiz_scroll->end_page;
        MSS_I2C_write( g_p_oled_i2c, OLED_SLAVE_ADDRESS, horiz_scroll_setup_data, sizeof(horiz_scroll_setup_data), MSS_I2C_RELEASE_BUS );
        MSS_I2C_wait_complete( g_p_oled_i2c );

        horiz_scroll_on_off[1] = CMD_HORI_SCRL_ON;
        MSS_I2C_write( g_p_oled_i2c, OLED_SLAVE_ADDRESS, horiz_scroll_on_off, sizeof(horiz_scroll_on_off), MSS_I2C_RELEASE_BUS );
        MSS_I2C_wait_complete( g_p_oled_i2c );
    }
}

/***************************************************************************//**
  OLED_contrast()
  See "oled.h" for details of how to use this function.
 */
void OLED_contrast(uint8_t color_contrast)
{
    uint8_t oled_contrast[] =
    {
        OLED_COMMAND_CODE, CMD_CONTRAST,
        OLED_COMMAND_CODE, CONTRAST_DEFAULT,
    };

    oled_contrast[3] = color_contrast;
    MSS_I2C_write( g_p_oled_i2c, OLED_SLAVE_ADDRESS, oled_contrast, sizeof(oled_contrast), MSS_I2C_RELEASE_BUS );
    MSS_I2C_wait_complete( g_p_oled_i2c );

}

/***************************************************************************//**
  OLED_write_data()
  See "oled.h" for details of how to use this function.
 */
void OLED_write_data(struct oled_data* data, oled_no_of_line LINES)
{
    uint8_t line;
    uint8_t char_offset;
    char *string;

    switch(LINES)
    {

        case FIRST_LINE:
        {
            OLED_clear_display(FIRST_LINE);
            line = data->line1;
            char_offset = data->char_offset1;
            string = data->string1;
        }

        case SECOND_LINE:
        {
            OLED_clear_display(SECOND_LINE);
            line = data->line2;
            char_offset = data->char_offset2;
           string = data->string2;
        }

        case BOTH_LINES:
        {
            OLED_clear_display(BOTH_LINES);
            line = data->line1;
            char_offset = data->char_offset1;
            string = data->string1;
            OLED_set_cursor(line,char_offset);
            OLED_write_string(string);
            line = data->line2;
            char_offset = data->char_offset2;
            string = data->string2;
        }

        OLED_set_cursor(line,char_offset);
        OLED_write_string(string);
        OLED_contrast(data->contrast_val);
    }
}
