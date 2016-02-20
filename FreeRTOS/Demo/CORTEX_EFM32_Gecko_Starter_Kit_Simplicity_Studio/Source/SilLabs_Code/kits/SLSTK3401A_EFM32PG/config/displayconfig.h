/***************************************************************************//**
 * @file displayconfig.h
 * @brief Configuration file for DISPLAY device driver interface.
 * @version 4.2.1
 *******************************************************************************
 * @section License
 * <b>(C) Copyright 2015 Silicon Labs, http://www.silabs.com</b>
 *******************************************************************************
 *
 * This file is licensed under the Silabs License Agreement. See the file
 * "Silabs_License_Agreement.txt" for details. Before using this software for
 * any purpose, you must agree to the terms of that agreement.
 *
 ******************************************************************************/

#ifndef __SILICON_LABS_DISPLAYCONFIG_H__
#define __SILICON_LABS_DISPLAYCONFIG_H__

/* Include the application specific configuration file. */
#include "displayconfigapp.h"

/* Include support for the SHARP Memory LCD model LS013B7DH03 */
#define INCLUDE_DISPLAY_SHARP_LS013B7DH03

#include "displayls013b7dh03config.h"
#include "displayls013b7dh03.h"

/**
 * Maximum number of display devices the display module is configured
 * to support. This number may be increased if the system includes more than
 * one display device. However, the number should be kept low in order to
 * save memory.
 */
#define DISPLAY_DEVICES_MAX   (1)

/**
 * Geometry of display device #0 in the system. Display device #0 on this kit
 * is the SHARP Memory LCD LS013B7DH03 which has 128x128 pixels.
 * These defines can be used to declare static framebuffers in order to save
 * extra memory consumed by malloc.
 */
#define DISPLAY0_WIDTH    (LS013B7DH03_WIDTH)
#define DISPLAY0_HEIGHT   (LS013B7DH03_HEIGHT)


/**
 * Define all display device driver initialization functions here.
 */
#define DISPLAY_DEVICE_DRIVER_INIT_FUNCTIONS \
  {                                          \
    DISPLAY_Ls013b7dh03Init,                 \
    NULL                                     \
  }

#endif /* __SILICON_LABS_DISPLAYCONFIG_H__ */
