/*******************************************************************************
 * (c) Copyright 2008 Actel Corporation.  All rights reserved.
 * 
 *  Manufacturing Test Data data structures.
 *  This header files specified the layout of the various data structures used
 *  to store manaufacturing test data within eNVM.
 *
 * SVN $Revision: 700 $
 * SVN $Date: 2009-03-13 13:22:03 +0000 (Fri, 13 Mar 2009) $
 */
#ifndef MTD_DATA_H
#define MTD_DATA_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif 

/*
 * Analog block specifications
 */
#define NB_OF_QUADS                     6
#define NB_OF_ABPS_PER_QUAD             2
#define TOTAL_NB_OF_ABPS                (NB_OF_QUADS * NB_OF_ABPS_PER_QUAD)
#define NB_OF_ABPS_RANGES               4
#define NB_OF_ANALOG_MODULES            3
#define NB_OF_OBD_MODES                 2
#define NB_OF_QUADS_PER_MODULE          2
#define NB_OF_CHOPPING_OPTIONS          2
#define NB_OF_DIRECT_INPUTS_PER_ADC     4

#define NB_OF_ADC_CHANNELS      13

/*------------------------------------------------------------------------------
 * mtd_global_settings_t
 *------------------------------------------------------------------------------
 * This typedef specifies the layout of the data structure holding the 
 * manufacturing test data global settings.
 */
typedef struct __mtd_global_settings_t
{
    uint16_t    crc16;
    uint8_t     serial[6];
    uint32_t    revision;
    uint16_t    sram_repair[8];
    uint16_t    varef_m;
    uint16_t    spare;
    uint8_t     big_dec;
    uint8_t     reserved0;
    uint16_t    reserved1;
} mtd_global_settings_t;

/*------------------------------------------------------------------------------
 * mtd_abps_trim_t
 *------------------------------------------------------------------------------
 * The following data structure is used to store ABPS trimming information.
 */
typedef struct __mtd_abps_trim_t
{
    uint8_t dacdec;
    uint8_t negtrim_per4_per3b_gtdec;
} mtd_abps_trim_t;


/*------------------------------------------------------------------------------
 * mtd_calibration_mc_t
 *------------------------------------------------------------------------------
 * The following data structure is used to store M and C calibration
 * coefficients.
 */
typedef struct __mtd_calibration_mc_t
{
    uint16_t m;
    uint16_t c;
} mtd_calibration_mc_t;


/*------------------------------------------------------------------------------
 * mtd_data_t
 *------------------------------------------------------------------------------
 * The following data structure is used to hold the full set of manufacturing
 * test data.
 */
typedef struct __mtd_data_t
{
    mtd_global_settings_t   global_settings;
    mtd_abps_trim_t         abps_trimming[NB_OF_QUADS][NB_OF_ABPS_PER_QUAD][NB_OF_ABPS_RANGES];
    uint8_t                 odb_trimming[NB_OF_ANALOG_MODULES][NB_OF_OBD_MODES][NB_OF_CHOPPING_OPTIONS];
    mtd_calibration_mc_t    abps_calibration[NB_OF_QUADS][NB_OF_ABPS_PER_QUAD][NB_OF_ABPS_RANGES];
    mtd_calibration_mc_t    obd_calibration[NB_OF_ANALOG_MODULES][NB_OF_OBD_MODES][NB_OF_CHOPPING_OPTIONS];
    mtd_calibration_mc_t    cm_calibration[NB_OF_QUADS];
    mtd_calibration_mc_t    tm_calibration[NB_OF_QUADS];
    mtd_calibration_mc_t    quads_direct_input_cal[NB_OF_QUADS][2];
    mtd_calibration_mc_t    adc_direct_input_cal[NB_OF_ANALOG_MODULES][NB_OF_DIRECT_INPUTS_PER_ADC];
    uint16_t                comparators_offsets[NB_OF_QUADS];
    uint32_t                ccc_delays_cal;
} mtd_data_t;

#ifdef __cplusplus
}
#endif

#endif
