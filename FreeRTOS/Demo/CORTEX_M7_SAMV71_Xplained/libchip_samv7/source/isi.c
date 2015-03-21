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
 *        Export functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Enable ISI
 */
void ISI_Enable(void)
{
    REG_ISI_CR |= ISI_CR_ISI_EN;
    while( (REG_ISI_SR & ISI_CR_ISI_EN)!=ISI_CR_ISI_EN);
    REG_ISI_DMA_CHER |= ISI_DMA_CHER_P_CH_EN | ISI_DMA_CHER_C_CH_EN;
}


/**
 * \brief Disable ISI
 */
void ISI_Disable(void)
{
    REG_ISI_CR |= ISI_CR_ISI_DIS;
    REG_ISI_DMA_CHDR |= ISI_DMA_CHDR_P_CH_DIS;
}


/**
 * \brief Enable ISI interrupt
 * \param  flag of interrupt to enable
 */
void ISI_EnableInterrupt(uint32_t flag)
{
    REG_ISI_IER = flag;
}


/**
 * \brief Disable ISI interrupt
 * \param  flag of interrupt to disable
 */
void ISI_DisableInterrupt(uint32_t flag)
{
    REG_ISI_IDR = flag;
}



/**
 * \brief Return ISI status register
 * \return Status of ISI register
 */
uint32_t ISI_StatusRegister(void)
{
    return(REG_ISI_SR);
}


/**
 * \brief Enable Codec path for capture next frame
 */
void ISI_CodecPathFull(void)
{
    // The codec path is enabled and the next frame is captured.
    // Both codec and preview datapaths are working simultaneously
    REG_ISI_CR |= ISI_CR_ISI_CDC;
    REG_ISI_CFG1 |= ISI_CFG1_FULL;
}


/**
 * \brief Set frame rate
 * \param frate frame rate capture
 */
void ISI_SetFrame(uint32_t frate)
{
    if( frate > 7 ) {
        TRACE_ERROR("FRate too big\n\r");
        frate = 7;
    }
    REG_ISI_CFG1 |= ISI_CFG1_FRATE(frate);
}


/**
 * \brief Get the number of byte per pixels
 * \param bmpRgb BMP type can be YUV or RGB
 */
uint8_t ISI_BytesForOnePixel(uint8_t bmpRgb)
{
    uint8_t nbByte_Pixel;

    if (bmpRgb == RGB) {
        if ((REG_ISI_CFG2 & ISI_CFG2_RGB_MODE) == ISI_CFG2_RGB_MODE){
            // RGB: 5:6:5 16bits/pixels
            nbByte_Pixel = 2;
        } 
        else {
            // RGB: 8:8:8 24bits/pixels
            nbByte_Pixel = 3;
        }
    } 
    else {
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
    REG_ISI_CR = ISI_CR_ISI_SRST | ISI_CR_ISI_DIS;
    // wait Software reset has completed successfully.
    while( (!(REG_ISI_SR & ISI_SR_SRST))
        && (timeout < 0x5000) ){
        timeout++;
    }
    if( timeout == 0x5000 ) {
        TRACE_ERROR("ISI-Reset timeout\n\r");
    }
}

/**
 * \brief ISI initialize
 * \param pVideo structure of video driver
 */
void ISI_Init(pIsi_Video pVideo)
{
    uint32_t hRatio, vRatio;
    ISI_Reset();

    // SLD pixel clock periods to wait before the beginning of a line.
    // SFD lines are skipped at the beginning of the frame.
    REG_ISI_CFG1 |= ISI_CFG1_SLD(pVideo->Hblank) + ISI_CFG1_SFD(pVideo->Vblank);
    REG_ISI_CFG1 |=ISI_CFG1_DISCR;
    TRACE_DEBUG("ISI_CFG1=0x%X\n\r", REG_ISI_CFG1);

    // IM_VSIZE: Vertical size of the Image sensor [0..2047]
    // Vertical size = IM_VSIZE + 1
    // IM_HSIZE: Horizontal size of the Image sensor [0..2047]
    // Horizontal size = IM_HSIZE + 1
    // YCC_SWAP : YCC image data    
    REG_ISI_CFG2 = ISI_CFG2_IM_VSIZE(pVideo->codec_vsize - 1)
                 + ISI_CFG2_IM_HSIZE(pVideo->codec_hsize - 1);
    
    if (pVideo->rgb_or_yuv == RGB) {
        REG_ISI_CFG2 |= ISI_CFG2_COL_SPACE | ISI_CFG2_RGB_MODE ;
    }
    else {
         REG_ISI_CFG2|= ISI_CFG2_YCC_SWAP_MODE2 ;
    }
    TRACE_DEBUG("ISI_CFG2=0x%X\n\r", REG_ISI_CFG2);

    // Vertical Preview size = PREV_VSIZE + 1 (480 max only in RGB mode).
    // Horizontal Preview size = PREV_HSIZE + 1 (640 max only in RGB mode).

    if( (pVideo->lcd_vsize > 480) || (pVideo->lcd_hsize > 640)) {
        TRACE_ERROR("Size LCD bad define %d, %d\n\r",pVideo->lcd_vsize ,pVideo->lcd_hsize);
        REG_ISI_PSIZE = ((480 - 1) ) + (((640-1) << 16) );
    }
    else {
        REG_ISI_PSIZE = ((pVideo->lcd_vsize -1)) + (((pVideo->lcd_hsize -1) << 16) );
    }
    // DEC_FACTOR is 8-bit width, range is from 16 to 255. 
    // Values from 0 to 16 do not perform any decimation.
    //REG_ISI_PDECF = (16 * pVideo->codec_hsize)/640;
    hRatio = (16 * pVideo->codec_hsize)/(pVideo->lcd_hsize); 
    vRatio = (16 * pVideo->codec_vsize)/(pVideo->lcd_vsize); 
    REG_ISI_PDECF = (hRatio > vRatio )? vRatio: hRatio;

    if (REG_ISI_PDECF < 16) REG_ISI_PDECF = 16;

    REG_ISI_DMA_P_DSCR = pVideo->Isi_fbd_base;
    REG_ISI_DMA_P_CTRL = ISI_DMA_P_CTRL_P_FETCH;
    REG_ISI_DMA_P_ADDR = pVideo->lcd_fb_addr;

    REG_ISI_DMA_C_DSCR = pVideo->codec_fbd_base;
    REG_ISI_DMA_C_CTRL = ISI_DMA_C_CTRL_C_FETCH;
    REG_ISI_DMA_C_ADDR = pVideo->codec_fb_addr;

    // C0: Color Space Conversion Matrix Coefficient C0
    // C1: Color Space Conversion Matrix Coefficient C1
    // C2: Color Space Conversion Matrix Coefficient C2
    // C3: Color Space Conversion Matrix Coefficient C3
    REG_ISI_Y2R_SET0  = ISI_Y2R_SET0_C0(0x95)
                      + ISI_Y2R_SET0_C1(0xFF)
                      + ISI_Y2R_SET0_C2(0x68)
                      + ISI_Y2R_SET0_C3(0x32);

    // C4: Color Space Conversion Matrix coefficient C4
    // Yoff: Color Space Conversion Luminance 128 offset
    // Croff: Color Space Conversion Red Chrominance 16 offset
    // Cboff: Color Space Conversion Blue Chrominance 16 offset
    REG_ISI_Y2R_SET1  = ISI_Y2R_SET1_C4(0xCC)
                      + ISI_Y2R_SET1_Yoff
                      + ISI_Y2R_SET1_Croff
                      + ISI_Y2R_SET1_Cboff;
}

