/***************************************************************************//**
 * @file
 * @brief capsense configuration parameters.
 * @version 4.2.1
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

#ifndef __SILICON_LABS_CAPSENSCONFIG_H__
#define __SILICON_LABS_CAPSENSCONFIG_H__
#ifdef __cplusplus
extern "C" {
#endif

/* Use ACMP0 module for capsense */
#define ACMP_CAPSENSE                           ACMP0
#define ACMP_CAPSENSE_CMUCLOCK                  cmuClock_ACMP0
#define PRS_CH_CTRL_SOURCESEL_ACMP_CAPSENSE     PRS_CH_CTRL_SOURCESEL_ACMP0
#define PRS_CH_CTRL_SIGSEL_ACMPOUT_CAPSENSE    PRS_CH_CTRL_SIGSEL_ACMP0OUT

/* On the SLSTK3401A the touch buttons are connected to PB11 and PB12.
 *
 * Pin  | APORT Channel (for ACMP0)
 * -------------------------
 * PB11 | APORT4XCH27
 * PB12 | APORT3XCH28
 *
 */
#define CAPSENSE_CHANNELS       { acmpInputAPORT4XCH27, acmpInputAPORT3XCH28 }
#define BUTTON0_CHANNEL         0             /**< Button 0 channel */
#define BUTTON1_CHANNEL         1             /**< Button 1 channel */
#define ACMP_CHANNELS           2             /**< Number of channels in use for capsense */
#define NUM_SLIDER_CHANNELS     0             /**< The kit does not have a slider */

#ifdef __cplusplus
}
#endif
#endif /* __SILICON_LABS_CAPSENSCONFIG_H__ */
