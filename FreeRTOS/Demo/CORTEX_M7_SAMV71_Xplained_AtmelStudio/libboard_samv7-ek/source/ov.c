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
 
 
/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "board.h"


const capture_size ov_sizes[] = {
		//{width, height}
		{ 160, 120 },   // QQVGA
		{ 352, 288 },   // CIF
		{ 320, 240 },
		{ 640, 360 },
		{ 640, 480 },
		// SWVGA
		{ 800, 600 },
		/// SXGA
		{1280, 960 },
		{1280, 720 },
		/// UXGA
		{1600, 1200 },
};

/*----------------------------------------------------------------------------
 *        Global Functions
 *----------------------------------------------------------------------------*/
 
/**
 * \brief  Configure the OV for a specified image size, pixel format, 
 * and frame period.
 */
void ov_configure(Twid *pTwid, uint8_t ovType, uint32_t width, uint32_t heigth)
{
	const struct ov_reg *reg_conf;
	uint8_t goodCaptureSize = 0;
	uint8_t i;

	reg_conf = ov5640_yuv_vga;
	TRACE_DEBUG("ovxxx_configure\n\r");
	for( i = 0; i< sizeof(ov_sizes); i++ ) {
		if( ov_sizes[i].width == width ) {
			if( ov_sizes[i].height != heigth ) {
				TRACE_INFO("ov configure vsize not define\n\r");
			} else {
				goodCaptureSize = 1;
				break;
			}
		}
	}
	if( goodCaptureSize == 0 ) {
		TRACE_ERROR("Problem size\n\r");
		while(1);
	}
	switch (ovType){
	case OV_2640: {
		 // Default value
		reg_conf = ov2640_yuv_qvga;
		// common register initialization
		switch(width) {
		case 320: //VGA
			printf("-I- QVGA 640 x 480\n\r");
			reg_conf = ov2640_yuv_qvga;
			break;
		case 640: //VGA
			TRACE_INFO("VGA 640 x 480\n\r");
			reg_conf = ov2640_yuv_vga;
			break;
		default:
			TRACE_DEBUG("ov2640_configure problem\n\r");
			break;
		}
			 break;
		}
	case OV_7740: {
		// Default value
		reg_conf = OV7740_VGA_YUV422;
		// common register initialization
		switch(width) {
		case 640: //VGA
			 TRACE_INFO(" VGA 640 x 480\n\r");
			 reg_conf = OV7740_VGA_YUV422;
			 break;

		case 352: //CIF
			 TRACE_INFO(" VGA 640 x 480\n\r");
			 reg_conf = OV7740_CIF_YUV422;
			 break;

		case 320: //QVGA
			 TRACE_INFO(" QVGA 320 x 240\n\r");
			 reg_conf = OV7740_QVGA_YUV422;
			 break;

		case 160: //QQVGA
			TRACE_INFO(" QVGA 320 x 240\n\r");
			 reg_conf = OV7740_QQVGA_YUV422;
			 break;

		default:
			 TRACE_DEBUG("ov7740_configure problem\n\r");
			 break;
		}
		 break;
		}
	case OV_9740: {
		 // Default value
		 reg_conf = ov9740_yuv_vga;
		 // common register initialization
		 switch(width) {
		 case 640: //VGA
			 TRACE_INFO(" VGA 640 x 360\n\r");
			 reg_conf = ov9740_yuv_vga;
			 break;
		 case 1280: //VGA
			 TRACE_INFO(" VGA 1280 x 720\n\r");
			 reg_conf = ov9740_yuv_sxga;
			 break;
		 default:
			 TRACE_DEBUG("ov9740_configure problem\n\r");
			 break;
		 }
		 break;
		}
	case OV_2643: {
		 // Default value
		 reg_conf = ov2643_yuv_vga;
		 // common register initialization
		 switch(width) {
		 case 1600: //UXGA
			 TRACE_INFO(" UXGA 1600 x 1200 \n\r");
			 reg_conf = ov2643_yuv_uxga;
			 break;
		 case 800: //SWVGA
			 TRACE_INFO("SWVGA 800 x 600\n\r");
			 reg_conf = ov2643_yuv_swvga;
			 break;
		 case 640: //VGA
			 TRACE_INFO(" VGA 640 x 480\n\r");
			 reg_conf = ov2643_yuv_vga;
			 break; 
		 default:  
			 TRACE_DEBUG("ov2643_configure problem\n\r");
			 break;
		 }
		break;
		}
	case OV_5640: {
		 // Default value
		 reg_conf = ov5640_yuv_vga;
		 // common register initialization
		 switch(width) {
		 case 640: //VGA
			 TRACE_INFO(" VGA 640 x 480\n\r");
			 reg_conf = ov5640_yuv_vga;
			 break;
		 case 1280: //SXGA
			 TRACE_INFO(" SXGA 1280 x 720\n\r");
			 reg_conf = ov5640_yuv_sxga;
			 break;
		 default:  
			 TRACE_DEBUG("ov5640_configure problem\n\r");
			 break;
		 }
		 break;
	}
	}
	if ((ovType == OV_5640) || (ovType == OV_9740))
		ov_write_regs16(pTwid, reg_conf);
	else 
		ov_write_regs8(pTwid, reg_conf);
}

/**
 * \brief  Configure the OV 5640 afc firmware. 
 */
void ov_5640Afc_Firmware(Twid *pTwid)
{
	const struct ov_reg *reg_conf;
	reg_conf = ov5640_afc;
	ov_write_regs16(pTwid, reg_conf);
}
