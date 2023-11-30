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

#include "chip.h"

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/
 
/**
 * \brief Workaround for ISI CFG2 register read.
 * \note The ISI_CFG2[31:27] can be written correctly, because the input writing 
 * data are assigned directly to the internal control bits as specified, 
 * the mismatch only happens in reading operation.
 * [31:28] are shift right 1 bit, so [31:27] can be read from [30:27].
 */
__STATIC_INLINE uint32_t _ISI_GetCFG2_Workaround(void)
{
	uint32_t wrongfield;
	wrongfield = ISI->ISI_CFG2 >> (ISI_CFG2_YCC_SWAP_Pos - 1);
	return (ISI->ISI_CFG2 & 0x07FFFFFF) | (wrongfield << ISI_CFG2_YCC_SWAP_Pos);
}

/*----------------------------------------------------------------------------
 *        Export functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Enable ISI
 */
void ISI_Enable(void)
{
	ISI->ISI_CR |= ISI_CR_ISI_EN;
	while( (ISI->ISI_SR & ISI_CR_ISI_EN)!=ISI_CR_ISI_EN);
}

/**
 * \brief Enable ISI Dma channel
 * \param  channel to be enabled
 */
void ISI_DmaChannelEnable(uint32_t channel)
{
	ISI->ISI_DMA_CHER |= channel;
}

/**
 * \brief Disable ISI Dma channel
 * \param  channel to be disabled
 */
void ISI_DmaChannelDisable(uint32_t channel)
{
	ISI->ISI_DMA_CHDR |=channel;
}

/**
 * \brief Disable ISI
 */
void ISI_Disable(void)
{
	/* Write one to this field to disable the module */
	ISI->ISI_CR |= ISI_CR_ISI_DIS;
	/* Software must poll DIS_DONE field in the ISI_STATUS register to verify that the command
	has successfully completed.*/
	while( (ISI->ISI_SR & ISI_SR_DIS_DONE) != ISI_SR_DIS_DONE);
}


/**
 * \brief Enable ISI interrupt
 * \param  flag of interrupt to enable
 */
void ISI_EnableInterrupt(uint32_t flag)
{
	ISI->ISI_IER = flag;
}

/**
 * \brief Disable ISI interrupt
 * \param  flag of interrupt to disable
 */
void ISI_DisableInterrupt(uint32_t flag)
{
	ISI->ISI_IDR = flag;
}

/**
 * \brief Return ISI status register
 * \return Status of ISI register
 */
uint32_t ISI_StatusRegister(void)
{
	return(ISI->ISI_SR);
}

/**
 * \brief Enable Codec path for capture next frame
 */
void ISI_CodecPathFull(void)
{
	// The codec path is enabled and the next frame is captured.
	// Both codec and preview data-paths are working simultaneously
	ISI->ISI_CR |= ISI_CR_ISI_CDC;
	ISI->ISI_CFG1 |= ISI_CFG1_FULL;
}

/**
 * \brief Set frame rate
 * \param frame frame rate capture
 */
void ISI_SetFrameRate(uint32_t frame)
{
	if( frame > 7 ) {
		TRACE_ERROR("rate too big\n\r");
		frame = 7;
	}
	ISI->ISI_CFG1 |= ISI_CFG1_FRATE(frame);
}

/**
 * \brief Get the number of byte per pixels
 * \param bmpRgb BMP type can be YUV or RGB
 */
uint8_t ISI_BytesForOnePixel(uint8_t bmpRgb)
{
	uint8_t nbByte_Pixel;

	if (bmpRgb == RGB) {
		if ((_ISI_GetCFG2_Workaround() & ISI_CFG2_RGB_MODE) == ISI_CFG2_RGB_MODE){
			// RGB: 5:6:5 16bits/pixels
			nbByte_Pixel = 2;
		} else {
			// RGB: 8:8:8 24bits/pixels
			nbByte_Pixel = 3;
		}
	} else {
		// YUV: 2 pixels for 4 bytes
		nbByte_Pixel = 2;
	}
	return nbByte_Pixel;
}

/**
 * \brief Reset ISI
 */
void ISI_Reset(void)
{
	uint32_t timeout=0;

	// Resets the image sensor interface.
	// Finish capturing the current frame and then shut down the module.
	ISI->ISI_CR = ISI_CR_ISI_SRST | ISI_CR_ISI_DIS;
	// wait Software reset has completed successfully.
	while( (!(ISI->ISI_SR & ISI_SR_SRST))
			&& (timeout < 0x5000) ) {
		timeout++;
	}
	if( timeout == 0x5000 ) {
		TRACE_ERROR("ISI-Reset timeout\n\r");
	}
}


/**
 * \brief Set the windows blank
 * \param hBlank  pixel clock periods to wait before the beginning of a line.
 * \param vBlank  lines are skipped at the beginning of the frame.
 */
void ISI_SetBlank(uint8_t hBlank, uint8_t vBlank)
{
	ISI->ISI_CFG1 |= ISI_CFG1_SLD(hBlank) + ISI_CFG1_SFD(vBlank);
}


/**
 * \brief Set vertical and horizontal Size of the Image Sensor
 * \param hSize  Horizontal size of the Image sensor [0..2047].
 * \param vSize  Vertical size of the Image sensor [0..2047].
 */
void ISI_SetSensorSize(uint32_t hSize, uint32_t vSize)
{
	// IM_VSIZE: Vertical size of the Image sensor [0..2047]
	// Vertical size = IM_VSIZE + 1
	// IM_HSIZE: Horizontal size of the Image sensor [0..2047]
	// Horizontal size = IM_HSIZE + 1
	ISI->ISI_CFG2 = _ISI_GetCFG2_Workaround() | ISI_CFG2_IM_VSIZE(vSize - 1)
			| ISI_CFG2_IM_HSIZE(hSize - 1);
}

/**
 * \brief Defines RGB pattern when RGB_MODE is set to 1.
 * \param wRgbPixelMapping  RGB pattern
 */
void ISI_RgbPixelMapping(uint32_t wRgbPixelMapping)
{
	ISI->ISI_CFG2 = _ISI_GetCFG2_Workaround() & (~ISI_CFG2_RGB_CFG_Msk);
	if (wRgbPixelMapping != ISI_CFG2_RGB_CFG_DEFAULT)
		ISI->ISI_CFG2 = _ISI_GetCFG2_Workaround() | wRgbPixelMapping 
			| ISI_CFG2_RGB_MODE; 
	else 
		ISI->ISI_CFG2 = _ISI_GetCFG2_Workaround();
}

/**
 * \brief Enables RGB swap
 * \param swapMode  0: D7-R7, 1: D0-R7
 */
void ISI_RgbSwapMode(uint32_t swapMode)
{
	ISI->ISI_CFG2 = _ISI_GetCFG2_Workaround() & (~ISI_CFG2_RGB_SWAP);
	if(swapMode) ISI->ISI_CFG2 = _ISI_GetCFG2_Workaround() | ISI_CFG2_RGB_SWAP;
}
 
/**
 * \brief Defines YCrCb swap format.
 * \param wYuvSwapMode YUV Swap format
 */
void ISI_YCrCbFormat(uint32_t wYuvSwapMode)
{
	ISI->ISI_CFG2 = _ISI_GetCFG2_Workaround() & (~ISI_CFG2_YCC_SWAP_Msk);
	ISI->ISI_CFG2 = _ISI_GetCFG2_Workaround() | wYuvSwapMode;
}

/**
 * \brief Input image is assumed to be grayscale-coded.
 * \param wPixelFormat  0: 2 pixels per word, 1:1 pixel per word.
 */
void ISI_setGrayScaleMode(uint32_t wPixelFormat)
{
	ISI->ISI_CFG2 = _ISI_GetCFG2_Workaround() | ISI_CFG2_GRAYSCALE ;
	if(wPixelFormat) ISI->ISI_CFG2 = _ISI_GetCFG2_Workaround() | ISI_CFG2_GS_MODE;
	
}

/**
 * \brief Set data stream format.
 * \param wStreamMode  0: YUV input, 1: RGB 8:8:8/5:6:5 input
 */
void ISI_setInputStream(uint32_t wStreamMode)
{
	ISI->ISI_CFG2 = _ISI_GetCFG2_Workaround() & (~ISI_CFG2_COL_SPACE);
	if(wStreamMode) ISI->ISI_CFG2 = _ISI_GetCFG2_Workaround() | ISI_CFG2_COL_SPACE;
}

/**
 * \brief Set preview size.
 * \param hSize  Horizontal Preview size  (640 max only in RGB mode).
 * \param vSize  Vertical Preview size  (480 max only in RGB mode).
 */
void ISI_setPreviewSize(uint32_t hSize, uint32_t vSize)
{
	if (hSize > 640) hSize = 640;
	if (vSize > 480) vSize = 480;
	ISI->ISI_PSIZE = ISI_PSIZE_PREV_VSIZE(vSize - 1) | ISI_PSIZE_PREV_HSIZE(hSize - 1);
}

/**
 * \brief calculate scaler factor automatically.
 * \note The sensor size and preview size for LCD was configured before this setting.
 */
void ISI_calcScalerFactor(void)
{
	uint32_t hLcdSize, hSensorSize;
	uint32_t hRatio;
	hLcdSize = ((ISI->ISI_PSIZE & ISI_PSIZE_PREV_HSIZE_Msk) >> ISI_PSIZE_PREV_HSIZE_Pos) +1 ;
	hSensorSize = ((_ISI_GetCFG2_Workaround() & ISI_CFG2_IM_HSIZE_Msk ) 
			>> ISI_CFG2_IM_HSIZE_Pos) + 1;
	hRatio = 1600 * hSensorSize / hLcdSize;
	ISI->ISI_PDECF = (hRatio/100);
}

/**
 * \brief Configure DMA for preview path.
 * \param baseFrameBufDesc  Preview Descriptor Address.
 * \param dmaCtrl  DMA Preview Control.
 * \param frameBufferStartAddr  DMA Preview Base Address.
 */
void ISI_setDmaInPreviewPath(uint32_t baseFrameBufDesc, 
		uint32_t dmaCtrl, uint32_t frameBufferStartAddr)
{
	ISI->ISI_DMA_P_DSCR = baseFrameBufDesc;
	ISI->ISI_DMA_P_CTRL = dmaCtrl;
	ISI->ISI_DMA_P_ADDR = frameBufferStartAddr;
}

/**
 * \brief Configure DMA for Codec path.
 * \param baseFrameBufDesc  Preview Descriptor Address.
 * \param dmaCtrl  DMA Preview Control.
 * \param frameBufferStartAddr  DMA Preview Base Address.
 */
void ISI_setDmaInCodecPath(uint32_t baseFrameBufDesc, 
		uint32_t dmaCtrl, uint32_t frameBufferStartAddr)
{
	ISI->ISI_DMA_C_DSCR = baseFrameBufDesc;
	ISI->ISI_DMA_C_CTRL = dmaCtrl;
	ISI->ISI_DMA_C_ADDR = frameBufferStartAddr;
}
 
/**
 * \brief ISI set matrix for YUV to RGB color space for preview path.
 * \param yuv2rgb structure of YUV to RBG parameters.
 */
void ISI_SetMatrix4Yuv2Rgb (ISI_Y2R* yuv2rgb)
{
   ISI->ISI_Y2R_SET0 = ISI_Y2R_SET0_C0(yuv2rgb->C0)
					 | ISI_Y2R_SET0_C1(yuv2rgb->C1)
					 | ISI_Y2R_SET0_C2(yuv2rgb->C2)
					 | ISI_Y2R_SET0_C3(yuv2rgb->C3);
					 
   ISI->ISI_Y2R_SET1 = ISI_Y2R_SET1_C4(yuv2rgb->C4)
					 | ((yuv2rgb->Yoff == 1)? ISI_Y2R_SET1_Yoff: 0)
					 | ((yuv2rgb->Croff == 1)? ISI_Y2R_SET1_Croff: 0)
					 | ((yuv2rgb->Cboff == 1)? ISI_Y2R_SET1_Cboff: 0);
}

/**
 * \brief ISI set matrix for RGB to YUV color space for codec path.
 * \param rgb2yuv structure of RGB to YUV parameters.
 */
void ISI_SetMatrix4Rgb2Yuv (ISI_R2Y* rgb2yuv)
{
	ISI->ISI_R2Y_SET0 = ISI_R2Y_SET0_C0(rgb2yuv->C0) 
					  | ISI_R2Y_SET0_C1(rgb2yuv->C1)
					  | ISI_R2Y_SET0_C2(rgb2yuv->C2)
					  | ((rgb2yuv->Roff == 1)? ISI_R2Y_SET0_Roff: 0);
				 
	ISI->ISI_R2Y_SET1 = ISI_R2Y_SET1_C3(rgb2yuv->C3) 
					  | ISI_R2Y_SET1_C4(rgb2yuv->C4)
					  | ISI_R2Y_SET1_C5(rgb2yuv->C5)
					  | ((rgb2yuv->Goff == 1)? ISI_R2Y_SET1_Goff: 0);
				 
	ISI->ISI_R2Y_SET2 = ISI_R2Y_SET2_C6(rgb2yuv->C6) 
					  | ISI_R2Y_SET2_C7(rgb2yuv->C7)
					  | ISI_R2Y_SET2_C8(rgb2yuv->C8)
					  | ((rgb2yuv->Boff == 1)? ISI_R2Y_SET2_Boff: 0);
}

