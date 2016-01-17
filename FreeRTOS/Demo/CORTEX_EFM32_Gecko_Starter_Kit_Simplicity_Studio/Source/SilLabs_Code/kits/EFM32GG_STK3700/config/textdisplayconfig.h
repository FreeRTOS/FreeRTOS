/***************************************************************************//**
 * @file textdisplayconfig.h
 * @brief Configuration file for textdisplay module.
 * @version 4.0.0
 *******************************************************************************
 * @section License
 * <b>(C) Copyright 2014 Silicon Labs, http://www.silabs.com</b>
 *******************************************************************************
 *
 * This file is licensed under the Silabs License Agreement. See the file
 * "Silabs_License_Agreement.txt" for details. Before using this software for
 * any purpose, you must agree to the terms of that agreement.
 *
 ******************************************************************************/

#ifndef _TEXTDISPLAYCONFIG_H_
#define _TEXTDISPLAYCONFIG_H_

/* Include display configuration files here because the textdisplay
   configuration depends on the display configuration. */
#include "displayconfig.h"
#include "displayconfigapp.h"

/**
 * Maximum number of text display devices the display module is configured
 * to support. This number may be increased if the system includes more than
 * one display device. However, the number should be kept low in order to
 * save memory.
 */
#define TEXTDISPLAY_DEVICES_MAX   (1)


/* Font definitions depending on which font is selected. */
#ifdef TEXTDISPLAY_FONT_8x8
  #define FONT_WIDTH   (8)
  #define FONT_HEIGHT  (8)
#endif
#ifdef TEXTDISPLAY_FONT_6x8
  #define FONT_WIDTH   (6)
  #define FONT_HEIGHT  (8)
#endif


/**
 * Determine the number of lines and columns of the text display devices.
 * These constants are used for static memory allocation in the textdisplay
 * device driver.
 *
 * Please make sure that the combined selection of font, lines and columns fits
 * inside the DISPLAY geometry.
 */
#define TEXTDISPLAY_DEVICE_0_LINES        (DISPLAY0_HEIGHT / FONT_HEIGHT)
#define TEXTDISPLAY_DEVICE_0_COLUMNS      (DISPLAY0_WIDTH / FONT_WIDTH)


/* Enable PixelMatrix allocation support in the display device driver.
   The textdisplay module allocates a pixel matrix corresponding to one line of
   text on the display. Therefore we need support for pixel matrix allocation.
*/
#define PIXEL_MATRIX_ALLOC_SUPPORT

/* Enable allocation of pixel matrices from the static pixel matrix pool.
   NOTE:
   The allocator does not support free'ing pixel matrices. It allocates
   continuosly from the static pool without keeping track of the sizes of
   old allocations. I.e. this is a one-shot allocator, and the  user should
   allocate buffers once at the beginning of the program.
*/
#define USE_STATIC_PIXEL_MATRIX_POOL

/* Specify the size of the static pixel matrix pool. For the textdisplay
   we need one line of text, that is, the font height (8) times the
   display width (128 pixels divided by 8 bits per byte). */
#define PIXEL_MATRIX_POOL_SIZE    (FONT_HEIGHT * DISPLAY0_WIDTH/8)

#endif /* _TEXTDISPLAYCONFIG_H_ */
