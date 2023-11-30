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

/** \addtogroup isi_module
 * @{
 * \section gmac_usage Usage
 * - ISI_Init: initialize ISI with default parameters
 * - ISI_EnableInterrupt: enable one or more interrupts
 * - ISI_DisableInterrupt: disable one or more interrupts
 * - ISI_Enable: enable isi module
 * - ISI_Disable: disable isi module
 * - ISI_CodecPathFull: enable codec path
 * - ISI_SetFrame: set frame rate
 * - ISI_BytesForOnePixel: return number of byte for one pixel
 * - ISI_StatusRegister: return ISI status register
 * - ISI_Reset: make a software reset
 */
/**@}*/

#ifndef ISI_H
#define ISI_H



/*----------------------------------------------------------------------------
 *        Definition
 *----------------------------------------------------------------------------*/
#define YUV_INPUT          0
#define RGB_INPUT          1
#define GRAYSCALE_INPUT    2
 
/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

/** ISI descriptors */
typedef struct
{
	/** Current LCD index, used with AT91C_ISI_MAX_PREV_BUFFER */
	uint32_t CurrentLcdIndex;
	/** set if Fifo Codec Empty is present */
	volatile uint32_t DisplayCodec;
	/** upgrade for each Fifo Codec Overflow (statistics use) */
	uint32_t nb_codec_ovf;
	/** upgrade for each Fifo Preview Overflow (statistics use) */
	uint32_t nb_prev_ovf;
}ISI_Descriptors;

/** Frame Buffer Descriptors */
typedef struct
{
	/** Address of the Current FrameBuffer */
	uint32_t Current;
	/** Address of the Control */
	uint32_t Control;
	/** Address of the Next FrameBuffer */
	uint32_t Next;
}ISI_FrameBufferDescriptors;


/** ISI Matrix Color Space Conversion YCrCb to RGB */
typedef struct
{
	/** Color Space Conversion Matrix Coefficient C0*/
	uint8_t C0;
	/** Color Space Conversion Matrix Coefficient C1 */
	uint8_t C1;
	/** Color Space Conversion Matrix Coefficient C2 */
	uint8_t C2;
	/** Color Space Conversion Matrix Coefficient C3 */
	uint8_t C3;
   /** Color Space Conversion Red Chrominance Default Offset */
	uint8_t Croff;
	/** Color Space Conversion Blue Chrominance Default Offset */
	uint8_t Cboff;
	/** Color Space Conversion Luminance Default Offset */
	uint8_t Yoff;
	 /** Color Space Conversion Matrix Coefficient C4 */
	uint16_t C4;
}ISI_Y2R;

/** ISI Matrix Color Space Conversion RGB to YCrCb */
typedef struct
{
	/** Color Space Conversion Matrix Coefficient C0*/
	uint8_t C0;
	/** Color Space Conversion Matrix Coefficient C1 */
	uint8_t C1;
	/** Color Space Conversion Matrix Coefficient C2 */
	uint8_t C2;
	/** Color Space Conversion Red Component Offset */
	uint8_t Roff;
	/** Color Space Conversion Matrix Coefficient C3*/
	uint8_t C3;
	/** Color Space Conversion Matrix Coefficient C4 */
	uint8_t C4;
	/** Color Space Conversion Matrix Coefficient C5 */
	uint8_t C5;
	/** Color Space Conversion Green Component Offset */
	uint8_t Goff;
	/** Color Space Conversion Matrix Coefficient C6*/
	uint8_t C6;
	/** Color Space Conversion Matrix Coefficient C7 */
	uint8_t C7;
	/** Color Space Conversion Matrix Coefficient C8 */
	uint8_t C8;
	/** Color Space Conversion Blue Component Offset */
	uint8_t Boff;
}ISI_R2Y;

/*----------------------------------------------------------------------------
 *         Exported functions
 *----------------------------------------------------------------------------*/
extern void ISI_Enable(void);

extern void ISI_Disable(void);

void ISI_DmaChannelEnable(uint32_t channel);

void ISI_DmaChannelDisable(uint32_t channel);

extern void ISI_EnableInterrupt(uint32_t flag);

extern void ISI_DisableInterrupt(uint32_t flag);

extern void ISI_CodecPathFull(void);

extern void ISI_SetFrameRate(uint32_t frame);

extern uint8_t ISI_BytesForOnePixel(uint8_t bmpRgb);

extern void ISI_Reset(void);

extern void ISI_Init(pIsi_Video pVideo);

extern uint32_t ISI_StatusRegister(void);

extern void ISI_SetBlank(
	uint8_t hBlank, 
	uint8_t vBlank);

extern void ISI_SetSensorSize(
	uint32_t hSize, 
	uint32_t vSize);

extern void ISI_RgbPixelMapping(uint32_t wRgbPixelMapping);

extern void ISI_RgbSwapMode(uint32_t swapMode);

extern void ISI_YCrCbFormat(uint32_t wYuvSwapMode);

extern void ISI_setGrayScaleMode(uint32_t wPixelFormat);

extern void ISI_setInputStream(uint32_t wStreamMode);

extern void ISI_setPreviewSize(
	uint32_t hSize, 
	uint32_t vSize);

extern void ISI_calcScalerFactor( void );

extern void ISI_setDmaInPreviewPath(
	uint32_t baseFrameBufDesc, 
	uint32_t dmaCtrl, 
	uint32_t frameBufferStartAddr);

extern void ISI_setDmaInCodecPath(
	uint32_t baseFrameBufDesc, 
	uint32_t dmaCtrl, 
	uint32_t frameBufferStartAddr);

extern void ISI_SetMatrix4Yuv2Rgb (ISI_Y2R* yuv2rgb);
extern void ISI_SetMatrix4Rgb2Yuv (ISI_R2Y* rgb2yuv);

#endif //#ifndef ISI_H

