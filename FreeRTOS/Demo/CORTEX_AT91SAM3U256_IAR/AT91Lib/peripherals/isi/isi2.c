/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
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

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include <board.h>
#include <utility/trace.h>
#include <utility/video.h>
#include "isi.h"

#if defined (BOARD_ISI_V200)

//-----------------------------------------------------------------------------
/// Enable ISI
//-----------------------------------------------------------------------------
void ISI_Enable(void)
{
    AT91C_BASE_ISI->ISI_CTRL |= AT91C_ISI_EN_1;
    while( (AT91C_BASE_ISI->ISI_SR & AT91C_ISI_EN_1)!=AT91C_ISI_EN_1);
    AT91C_BASE_ISI->ISI_DMACHER |= AT91C_ISI_P_CH_EN_1;
}

//-----------------------------------------------------------------------------
/// Disable ISI
//-----------------------------------------------------------------------------
void ISI_Disable(void)
{
    AT91C_BASE_ISI->ISI_CTRL |= AT91C_ISI_DIS_1;
    AT91C_BASE_ISI->ISI_DMACHDR &= ~AT91C_ISI_P_CH_DIS_1;
}

//-----------------------------------------------------------------------------
/// Enable ISI interrupt
/// \param  flag of interrupt to enable
//-----------------------------------------------------------------------------
void ISI_EnableInterrupt(unsigned int flag)
{
    AT91C_BASE_ISI->ISI_IER = flag;
}

//-----------------------------------------------------------------------------
/// Disable ISI interrupt
/// \param  flag of interrupt to disable
//-----------------------------------------------------------------------------
void ISI_DisableInterrupt(unsigned int flag)
{
    AT91C_BASE_ISI->ISI_IDR = flag;
}

//-----------------------------------------------------------------------------
/// Return ISI status register
/// \return Status of ISI register
//-----------------------------------------------------------------------------
unsigned int ISI_StatusRegister(void)
{
    return(AT91C_BASE_ISI->ISI_SR);
}

//-----------------------------------------------------------------------------
/// Enable Codec path for capture next frame
//-----------------------------------------------------------------------------
void ISI_CodecPathFull(void)
{
    // The codec path is enabled and the next frame is captured.
    // Both codec and preview datapaths are working simultaneously
    AT91C_BASE_ISI->ISI_CTRL |= AT91C_ISI_CDC_1;
    AT91C_BASE_ISI->ISI_CFG1 |= AT91C_ISI_FULL;
}

//-----------------------------------------------------------------------------
/// Set frame rate
/// \param  frate frame rate capture
/// \return 
//-----------------------------------------------------------------------------
void ISI_SetFrame(unsigned int frate)
{
    if( frate > 7 ) {
        TRACE_ERROR("FRate too big\n\r");
        frate = 7;
    }
    AT91C_BASE_ISI->ISI_CFG1 |= ((frate<<8) & AT91C_ISI_FRATE);
}

//-----------------------------------------------------------------------------
/// Get the number of byte per pixels
/// \param  bmpRgb BMP type can be YUV or RGB
/// \return Number of byte for one pixel
//-----------------------------------------------------------------------------
unsigned char ISI_BytesForOnePixel(unsigned char bmpRgb)
{
    unsigned char nbByte_Pixel;

    if (bmpRgb == RGB) {
        if ((AT91C_BASE_ISI->ISI_CFG2 & AT91C_ISI_RGB_MODE) == AT91C_ISI_RGB_MODE_RGB_565){
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

//-----------------------------------------------------------------------------
/// Reset ISI
//-----------------------------------------------------------------------------
void ISI_Reset(void)
{
    unsigned int timeout=0;

    // Resets the image sensor interface.
    // Finish capturing the current frame and then shut down the module.
    AT91C_BASE_ISI->ISI_CTRL = AT91C_ISI_SRST_1 | AT91C_ISI_DIS_1;
    // wait Software reset has completed successfully.
    while( (!(volatile int)AT91C_BASE_ISI->ISI_SR & AT91C_ISI_SRST)
        && (timeout < 0x5000) ){
        timeout++;
    }
    if( timeout == 0x5000 ) {
        TRACE_ERROR("ISI-Reset timeout\n\r");
    }
}

//-----------------------------------------------------------------------------
/// ISI initialize
/// \param pVideo structure of video driver
//-----------------------------------------------------------------------------
void ISI_Init(AT91PS_VIDEO pVideo)
{
    ISI_Reset();

    // AT91C_ISI_HSYNC_POL    Horizontal synchronisation polarity
    // AT91C_ISI_VSYNC_POL    Vertical synchronisation polarity
    // AT91C_ISI_PIXCLK_POL   Pixel Clock Polarity

    // SLD pixel clock periods to wait before the beginning of a line.
    // SFD lines are skipped at the beginning of the frame.
    AT91C_BASE_ISI->ISI_CFG1 |= ((pVideo->Hblank << 16) & AT91C_ISI_SLD)
                              + ((pVideo->Vblank << 24) & AT91C_ISI_SFD);
    TRACE_DEBUG("ISI_CFG1=0x%X\n\r", AT91C_BASE_ISI->ISI_CFG1);

    // IM_VSIZE: Vertical size of the Image sensor [0..2047]
    // Vertical size = IM_VSIZE + 1
    // IM_HSIZE: Horizontal size of the Image sensor [0..2047]
    // Horizontal size = IM_HSIZE + 1
    // YCC_SWAP : YCC image data    
    AT91C_BASE_ISI->ISI_CFG2 = ((pVideo->codec_vsize-1) & AT91C_ISI_IM_VSIZE)
                            + (((pVideo->codec_hsize-1) << 16) & AT91C_ISI_IM_HSIZE)
                            + AT91C_ISI_YCC_SWAP_YCC_MODE2;

    if (pVideo->rgb_or_yuv == RGB) {
        AT91C_BASE_ISI->ISI_CFG2 |= AT91C_ISI_COL_SPACE | AT91C_ISI_RGB_MODE_RGB_565
            | AT91C_ISI_RGB_CFG_RGB_DEFAULT;
    }
    else {
    //    AT91C_BASE_HISI->ISI_CFG2 &=  ~AT91C_ISI_COL_SPACE;    
    }
    TRACE_DEBUG("ISI_CFG2=0x%X\n\r", AT91C_BASE_ISI->ISI_CFG2);

    // Vertical Preview size = PREV_VSIZE + 1 (480 max only in RGB mode).
    // Horizontal Preview size = PREV_HSIZE + 1 (640 max only in RGB mode).    
#if defined (AT91C_ID_LCDC)
    if( (pVideo->lcd_vsize > 480) || (pVideo->lcd_hsize > 640)) {
        TRACE_ERROR("Size LCD bad define\n\r");
        AT91C_BASE_ISI->ISI_PSIZE = ((BOARD_LCD_HEIGHT-1) & AT91C_ISI_PREV_VSIZE)
                                  + (((BOARD_LCD_WIDTH-1) << 16) & AT91C_ISI_PREV_HSIZE);
    }
    else {

        AT91C_BASE_ISI->ISI_PSIZE = ((pVideo->lcd_vsize -1) & AT91C_ISI_PREV_VSIZE)
                                  + (((pVideo->lcd_hsize -1) << 16) & AT91C_ISI_PREV_HSIZE);
    }
#endif


    // DEC_FACTOR is 8-bit width, range is from 16 to 255. 
    // Values from 0 to 16 do not perform any decimation.
    AT91C_BASE_ISI->ISI_PDECF = (16 * pVideo->codec_hsize) / pVideo->lcd_hsize;

    TRACE_DEBUG("codec_hsize: %d\n\r", pVideo->codec_hsize);
    TRACE_DEBUG("lcd_hsize: %d\n\r", pVideo->lcd_hsize);
    TRACE_DEBUG("ISI_PDECF: %d\n\r", AT91C_BASE_ISI->ISI_PDECF);
    if( AT91C_BASE_ISI->ISI_PDECF <16) {
        TRACE_ERROR("ISI_PDECF, forbidden value: %d\n\r", AT91C_BASE_ISI->ISI_PDECF);
        AT91C_BASE_ISI->ISI_PDECF = 16;
    }

    AT91C_BASE_ISI->ISI_DMAPDSCR = pVideo->Isi_fbd_base;
    AT91C_BASE_ISI->ISI_DMAPCTRL = AT91C_ISI_P_FETCH_ENABLE;
    AT91C_BASE_ISI->ISI_DMAPADDR = pVideo->lcd_fb_addr;

    // C0: Color Space Conversion Matrix Coefficient C0
    // C1: Color Space Conversion Matrix Coefficient C1
    // C2: Color Space Conversion Matrix Coefficient C2
    // C3: Color Space Conversion Matrix Coefficient C3
    AT91C_BASE_ISI->ISI_Y2RSET0  = ( (0x95<< 0) & AT91C_ISI_Y2R_C0)
                                 + ( (0xFF<< 8) & AT91C_ISI_Y2R_C1)
                                 + ( (0x68<<16) & AT91C_ISI_Y2R_C2)
                                 + ( (0x32<<24) & AT91C_ISI_Y2R_C3);

    // C4: Color Space Conversion Matrix coefficient C4
    // Yoff: Color Space Conversion Luminance 128 offset
    // Croff: Color Space Conversion Red Chrominance 16 offset
    // Cboff: Color Space Conversion Blue Chrominance 16 offset
    AT91C_BASE_ISI->ISI_Y2RSET1  = ( (0xCC<< 0) & AT91C_ISI_Y2R_C4)
                                 + ( AT91C_ISI_Y2R_YOFF_128)
                                 + ( AT91C_ISI_Y2R_CROFF_16)
                                 + ( AT91C_ISI_Y2R_CBOFF_16);
}

#endif // defined (BOARD_ISI_V200)

