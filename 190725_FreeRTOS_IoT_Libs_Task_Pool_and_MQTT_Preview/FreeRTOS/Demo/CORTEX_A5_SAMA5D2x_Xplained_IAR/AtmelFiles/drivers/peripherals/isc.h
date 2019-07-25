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

/** \addtogroup isc_module
 * @{
 * \section isc_usage Usage
 * - isc_start_capture: Send Capture Input Stream Command to start a single
 *						shot capture or a multiple frame
 */
/**@}*/

#ifndef ISC_H
#define ISC_H

#include <stdint.h>

/*------------------------------------------------------------------------------
 *         Type
 *----------------------------------------------------------------------------*/
/** color correction components structure */
struct _color_correct {
	/** Red Component Offset (signed 13 bits, 1:12:0) */
	uint16_t rOffset;
	/** Green Component Offset (signed 13 bits, 1:12:0)*/
	uint16_t gOffset;
	/** Green Component Offset (signed 13 bits, 1:12:0)*/
	uint16_t bOffset;
	/** Red Gain for Red Component (signed 12 bits, 1:3:8)*/
	uint16_t rrGain;
	/** Green Component (Red row) Gain (unsigned 13 bits, 0:4:9)*/
	uint16_t rgGain;
	/** Blue Gain for Red Component (signed 12 bits, 1:3:8)*/
	uint16_t rbGain;
	/** Green Gain for Green Component (signed 12 bits, 1:3:8)*/
	uint16_t ggGain;
	/** Red Gain for Green Component (signed 12 bits, 1:3:8)*/
	uint16_t grGain;
	/** Blue Gain for Green Component (signed 12 bits, 1:3:8)*/
	uint16_t gbGain;
	/** Green Gain for Blue Component (signed 12 bits, 1:3:8) */
	uint16_t bgGain;
	/** Red Gain for Blue Component (signed 12 bits, 1:3:8) */
	uint16_t brGain;
	/** Blue Gain for Blue Component (signed 12 bits, 1:3:8)*/
	uint16_t bbGain;
};

/** color space convertion components structure */
struct _color_space {
	/** Red Gain for Luminance (signed 12 bits 1:3:8) */
	uint16_t YrGain;
	/** Green Gain for Luminance (signed 12 bits 1:3:8)*/
	uint16_t YgGain;
	/** Blue Gain for Luminance Component (12 bits signed 1:3:8)*/
	uint16_t YbGain;
	/** Luminance Offset (11 bits signed 1:10:0)*/
	uint16_t Yoffset;
	/** Green Gain for Blue Chrominance (signed 12 bits 1:3:8)*/
	uint16_t cbrGain;
	/** Red Gain for Blue Chrominance (signed 12 bits, 1:3:8)*/
	uint16_t cbgGain;
	/** Blue Gain for Blue Chrominance (signed 12 bits 1:3:8)*/
	uint16_t cbbGain;
	/** Blue Chrominance Offset (signed 11 bits 1:10:0)*/
	uint16_t cbOffset;
	/** Red Gain for Red Chrominance (signed 12 bits 1:3:8)*/
	uint16_t crrGain;
	/** Green Gain for Red Chrominance (signed 12 bits 1:3:8)*/
	uint16_t crgGain;
	/** Blue Gain for Red Chrominance (signed 12 bits 1:3:8)*/
	uint16_t crbGain;
	/** Red Chrominance Offset (signed 11 bits 1:10:0)*/
	uint16_t crOffset;
};

/** \brief Structure for ISC DMA descriptor view0 that can be
 * performed when the pixel or data stream is packed.*/
struct _isc_dma_view0
{
	/** ISC DMA Control. */
	uint32_t ctrl;
	/** Next ISC DMA Descriptor Address number. */
	uint32_t next_desc;
	/** Transfer Address. */
	uint32_t addr;
	/** stride . */
	uint32_t stride;
};

/** \brief Structure for ISC DMA descriptor view1 that can be
 * performed for YCbCr semi-planar pixel stream.*/
struct _isc_dma_view1
{
	/** ISC DMA Control. */
	uint32_t ctrl;
	/** Next ISC DMA Descriptor Address number. */
	uint32_t next_desc;
	/** Transfer Address 0. */
	uint32_t addr0;
	/** stride 0 . */
	uint32_t stride0;
	/** Transfer Address 1. */
	uint32_t addr1;
	/** stride 1 . */
	uint32_t stride1;

};

/** \brief Structure for ISC DMA descriptor view2 that can be
 * performed for used for YCbCr planar pixel stream.*/
struct _isc_dma_view2
{
	/** ISC DMA Control. */
	uint32_t ctrl;
	/** Next ISC DMA Descriptor Address number. */
	uint32_t next_desc;
	/** Transfer Address 0. */
	uint32_t addr0;
	/** stride 0. */
	uint32_t stride0;
	/** Transfer Address 1. */
	uint32_t addr1;
	/** stride 1 . */
	uint32_t stride1;
	/** Transfer Address 2. */
	uint32_t addr2;
	/** stride 2. */
	uint32_t stride2;
};

/*------------------------------------------------------------------------------
 *         Exported functions
 *----------------------------------------------------------------------------*/
/*------------------------------------------
 *         ISC Control functions
 *----------------------------------------*/
extern void isc_start_capture(void);
extern void isc_stop_capture(void);
extern uint32_t isc_get_ctrl_status(void);
extern void isc_update_profile(void);
extern void isc_software_reset(void);

/*------------------------------------------
 *      PFE(Parallel Front End) functions
 *----------------------------------------*/
extern void isc_pfe_set_video_mode(uint32_t vmode);
extern void isc_pfe_set_sync_polarity(uint32_t hpol, uint32_t vpol);
extern void isc_pfe_set_pixel_polarity(uint32_t ppol);
extern void isc_pfe_set_field_polarity(uint32_t fpol);
extern void isc_pfe_set_gated_clock(uint8_t en);
extern void isc_pfe_set_cropping_enabled(uint8_t enCol, uint8_t enRow);
extern void isc_pfe_set_bps(uint32_t bps);
extern void isc_pfe_set_single_shot(void);
extern void isc_pfe_set_continuous_shot(void);
extern void isc_pfe_set_cropping_area(uint32_t Hstart, uint32_t Hend,
				      uint32_t Vstart, uint32_t Vend);

/*------------------------------------------
 *         Clock configuration functions
 *----------------------------------------*/
 extern void isc_configure_isp_clock(uint32_t isp_clk_div,
				     uint32_t isp_clk_sel);
extern void isc_enable_isp_clock(void);
extern void isc_disable_isp_clock(void);
extern void isc_reset_isp_clock(void);
extern void isc_configure_master_clock(uint32_t master_clk_div,
				       uint32_t master_clk_sel);
extern void isc_enable_master_clock(void);
extern void isc_disable_master_clock(void);
extern void isc_reset_master_clock(void);
extern uint32_t isc_get_clock_status(void);

/*------------------------------------------
 *         Interrupt functions
 *----------------------------------------*/
extern void isc_enable_interrupt(uint32_t flag);
extern void isc_disable_interrupt(uint32_t flag);
extern uint32_t isc_interrupt_status(void);

/*------------------------------------------
 *         White Balance functions
 *----------------------------------------*/
extern void isc_wb_enabled(uint8_t enabled);
extern void isc_wb_set_bayer_pattern(uint8_t pattern);
extern void isc_wb_adjust_bayer_color(uint32_t rOffset, uint32_t grOffset,
				      uint32_t bOffset, uint32_t gbOffset,
				      uint32_t rGain, uint32_t grGain,
				      uint32_t bGain, uint32_t gbGain);

/*------------------------------------------
 *         Color Filter Array functions
 *----------------------------------------*/
extern void isc_cfa_enabled(uint8_t enabled);
extern void isc_cfa_configure(uint8_t pattern, uint8_t edge);

/*------------------------------------------
 *         Color Correction functions
 *----------------------------------------*/
extern void isc_cc_enabled(uint8_t enabled);
extern void isc_cc_configure(struct _color_correct* cc);

/*------------------------------------------
 *         Gamma Correction functions
 *----------------------------------------*/
extern void isc_gamma_enabled(uint8_t enabled, uint8_t channels);
extern void isc_gamma_configure(uint16_t* rGamConstant, uint16_t* rGamSlope,
				uint16_t* gGamConstant, uint16_t* gGamSlope,
				uint16_t* bGamConstant, uint16_t* bGamSlope);

/*------------------------------------------
 *        Color Space Conversion functions
 *----------------------------------------*/
extern void isc_csc_enabled(uint8_t enabled);
extern void isc_csc_configure(struct _color_space* cs);

/*------------------------------------------
 *       Contrast And Brightness functions
 *----------------------------------------*/
extern void isc_cbc_enabled(uint8_t enabled);
extern void isc_cbc_configure(uint8_t ccir656, uint8_t byteOrder,
			      uint16_t brightness, uint16_t contrast);

/*------------------------------------------
 *       Sub-sampling functions
 *----------------------------------------*/
extern void isc_sub422_enabled(uint8_t enabled);
extern void isc_sub422_configure(uint8_t ccir656, uint8_t byte_order,
				 uint8_t lpf);
extern void isc_sub420_configure(uint8_t enabled, uint8_t filter);

/*------------------------------------------
 * Rounding, Limiting and Packing functions
 *----------------------------------------*/
extern void isc_rlp_configure(uint8_t rlpMode, uint8_t alpha);

/*------------------------------------------
 *         Histogram functions
 *----------------------------------------*/
extern void isc_histogram_enabled(uint8_t enabled);
extern void isc_histogram_configure(uint8_t mode, uint8_t bay_sel,
				    uint8_t reset);
extern void isc_update_histogram_table(void);
extern void isc_clear_histogram_table(void);

/*------------------------------------------
 *         DMA functions
 *----------------------------------------*/
extern void isc_dma_configure_input_mode(uint32_t mode);
extern void isc_dma_configure_desc_entry(uint32_t desc_entry);
extern void isc_dma_enable(uint32_t ctrl);
extern void isc_dma_adderss(uint8_t channel, uint32_t address, uint32_t stride);

#endif //#ifndef ISC_H
