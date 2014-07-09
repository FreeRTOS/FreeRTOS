/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
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

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"

#include <stdint.h>
#include <math.h>
#include <string.h>

#ifdef LCDC
/** \addtogroup lcdd_base
 * Implementation of LCD driver, Include LCD initialization,
 * LCD on/off and LCD backlight control.
 */
/**@{*/

/*----------------------------------------------------------------------------
 *        Local types
 *----------------------------------------------------------------------------*/

/** DMA descriptor for LCDC */
typedef struct _LCDCDescriptor {
    uint32_t addr;
    uint32_t ctrl;
    uint32_t next;
}sLCDCDescriptor;

/** CULT information */
typedef struct _CLUTInfo {
    uint8_t bpp;
    uint8_t nbColors;
}sCLUTInfo;

/** LCDC General Layer information */
typedef struct _Layer {
    sLCDCDescriptor dmaD;
    void* pBuffer;
    sCLUTInfo clut;
    uint16_t  reserved;
} sLayer;

/** LCDC HEO Layer information */
typedef struct _HeoLayer {
    sLCDCDescriptor dmaD[3];
    void* pBuffer;
    sCLUTInfo clut;
    uint16_t  reserved;
} sHeoLayer;

/** Pins for LCDC */
static const Pin pPinsLCD[] = {PINS_LCD};

/** Current selected canvas information */
static sLCDDLayer lcddCanvas;
/** Base Layer */

#if defined ( __ICCARM__ ) /* IAR Ewarm */
#pragma data_alignment=64
#elif defined (  __GNUC__  ) /* GCC CS3 */
__attribute__((aligned(64)))
#endif
static sLayer lcddBase;

/** Overlay 1 Layer */
#if defined ( __ICCARM__ ) /* IAR Ewarm */
#pragma data_alignment=64
#elif defined (  __GNUC__  ) /* GCC CS3 */
__attribute__((aligned(64)))
#endif
static sLayer lcddOvr1;

#if defined ( __ICCARM__ ) /* IAR Ewarm */
#pragma data_alignment=64
#elif defined (  __GNUC__  ) /* GCC CS3 */
__attribute__((aligned(64)))
#endif
static sLayer lcddOvr2;

/** High End Overlay Layer */
#if defined ( __ICCARM__ ) /* IAR Ewarm */
#pragma data_alignment=64
#elif defined (  __GNUC__  ) /* GCC CS3 */
__attribute__((aligned(64)))
#endif
static sHeoLayer lcddHeo;

/** Hardware cursor Layer */
#if defined ( __ICCARM__ ) /* IAR Ewarm */
#pragma data_alignment=64
#elif defined (  __GNUC__  ) /* GCC CS3 */
__attribute__((aligned(64)))
#endif
static sLayer lcddHcc;

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

/**
 * Return a pointer to layer.
 * \param bLayer Layer ID.
 */
static sLayer *pLayer( uint8_t bLayer )
{
    switch( bLayer )
    {
        case LCDD_BASE:       return &lcddBase;
        case LCDD_OVR1:       return &lcddOvr1;
        case LCDD_OVR2:       return &lcddOvr2;
        case LCDD_HEO:        return (sLayer*)&lcddHeo;
        case LCDD_CUR:        return &lcddHcc;
    }
    return NULL;
}

/**
 * Return true if Pixel stride supported.
 * \param bLayer Layer ID.
 */
static uint8_t LCDD_IsPStrideSupported( uint8_t bLayer )
{
    switch( bLayer )
    {
        case LCDD_OVR1: case LCDD_OVR2:case LCDD_HEO: return 1;
        default:                       return 0;
    }
}

/**
 * Return a pointer to enable register.
 * (Starts following register list: _ER, _DR, _SR, _IER, _IDR, _IMR, _ISR)
 * \param bLayer Layer ID.
 */
static volatile uint32_t *pEnableReg( uint8_t bLayer )
{
    Lcdc *pHw = LCDC;
    switch( bLayer )
    {
        case LCDD_CONTROLLER: return (volatile uint32_t*)&pHw->LCDC_LCDEN;
        case LCDD_BASE:       return (volatile uint32_t*)&pHw->LCDC_BASECHER;
        case LCDD_OVR1:       return (volatile uint32_t*)&pHw->LCDC_OVR1CHER;
        case LCDD_OVR2:       return (volatile uint32_t*)&pHw->LCDC_OVR2CHER;
        case LCDD_HEO:        return (volatile uint32_t*)&pHw->LCDC_HEOCHER;
        case LCDD_CUR:        return (volatile uint32_t*)&pHw->LCDC_HCRCHER;
    }
    return NULL;
}

/**
 * Return a pointer to blender configuration register.
 * \param bLayer Layer ID.
 */
static volatile uint32_t *pBlenderReg( uint8_t bLayer )
{
    Lcdc *pHw = LCDC;
    switch( bLayer )
    {
        case LCDD_BASE: return (volatile uint32_t *)&pHw->LCDC_BASECFG4;
        case LCDD_OVR1: return (volatile uint32_t *)&pHw->LCDC_OVR1CFG9;
        case LCDD_OVR2: return (volatile uint32_t *)&pHw->LCDC_OVR2CFG9;
        case LCDD_HEO:  return (volatile uint32_t *)&pHw->LCDC_HEOCFG12;
        case LCDD_CUR:  return (volatile uint32_t *)&pHw->LCDC_HCRCFG9;
    }
    return NULL;
}

/**
 * Return a pointer to DMA head register.
 * (Starts following register list: _HEAD, _ADDRESS, _CONTROL, _NEXT)
 * \param bLayer Layer ID.
 */
static volatile uint32_t *pHeadReg( uint8_t bLayer )
{
    Lcdc *pHw = LCDC;
    switch( bLayer )
    {
        case LCDD_BASE:       return (volatile uint32_t*)&pHw->LCDC_BASEHEAD;
        case LCDD_OVR1:       return (volatile uint32_t*)&pHw->LCDC_OVR1HEAD;
        case LCDD_OVR2:       return (volatile uint32_t*)&pHw->LCDC_OVR2HEAD;
        case LCDD_HEO:        return (volatile uint32_t*)&pHw->LCDC_HEOHEAD;
        case LCDD_CUR:        return (volatile uint32_t*)&pHw->LCDC_HCRHEAD;
    }
    return NULL;
}

/**
 * Return a pointer to layer configure register.
 * (Including: _CFG0, _CFG1 (RGB mode ...))
 * \param bLayer Layer ID.
 */
static volatile uint32_t *pCfgReg( uint8_t bLayer )
{
    Lcdc *pHw = LCDC;
    switch( bLayer )
    {
        case LCDD_BASE:       return (volatile uint32_t*)&pHw->LCDC_BASECFG0;
        case LCDD_OVR1:       return (volatile uint32_t*)&pHw->LCDC_OVR1CFG0;
        case LCDD_OVR2:       return (volatile uint32_t*)&pHw->LCDC_OVR2CFG0;
        case LCDD_HEO:        return (volatile uint32_t*)&pHw->LCDC_HEOCFG0;
        case LCDD_CUR:        return (volatile uint32_t*)&pHw->LCDC_HCRCFG0;
    }
    return NULL;
}

/**
 * Return a pointer to Window configure register.
 * (Including: X Y register, W H register)
 * \param bLayer Layer ID.
 */
static volatile uint32_t *pWinReg( uint8_t bLayer )
{
    Lcdc *pHw = LCDC;
    switch( bLayer )
    {
        case LCDD_OVR1:       return (volatile uint32_t*)&pHw->LCDC_OVR1CFG2;
        case LCDD_OVR2:       return (volatile uint32_t*)&pHw->LCDC_OVR2CFG2;
        case LCDD_HEO:        return (volatile uint32_t*)&pHw->LCDC_HEOCFG2;
        case LCDD_CUR:        return (volatile uint32_t*)&pHw->LCDC_HCRCFG2;
    }
    return NULL;
}

/**
 * Return a pointer to striding regiters.
 * \param bLayer Layer ID.
 */
static volatile uint32_t *pStrideReg( uint8_t bLayer )
{
    Lcdc *pHw = LCDC;
    switch( bLayer )
    {
        case LCDD_BASE: return (volatile uint32_t*)&pHw->LCDC_BASECFG2;
        case LCDD_OVR1: return (volatile uint32_t*)&pHw->LCDC_OVR1CFG4;
        case LCDD_OVR2: return (volatile uint32_t*)&pHw->LCDC_OVR2CFG4;
        case LCDD_HEO:  return (volatile uint32_t*)&pHw->LCDC_HEOCFG5;
        case LCDD_CUR:  return (volatile uint32_t*)&pHw->LCDC_HCRCFG4;
    }
    return NULL;
}

/**
 * Return a pointer to Color configure regiters.
 * (Including: RGB Default, RGB Key, RGB Mask)
 * Note that base layer only has one register (default).
 * \param bLayer Layer ID.
 */
static volatile uint32_t *pColorReg( uint8_t bLayer )
{
    Lcdc *pHw = LCDC;
    switch( bLayer )
    {
        case LCDD_BASE: return (volatile uint32_t*)&pHw->LCDC_BASECFG3;
        case LCDD_OVR1: return (volatile uint32_t*)&pHw->LCDC_OVR1CFG6;
        case LCDD_OVR2: return (volatile uint32_t*)&pHw->LCDC_OVR2CFG6;
        case LCDD_HEO:  return (volatile uint32_t*)&pHw->LCDC_HEOCFG9;
        case LCDD_CUR:  return (volatile uint32_t*)&pHw->LCDC_HCRCFG6;
    }
    return NULL;
}

/**
 * Return a pointer to scaling register.
 * \param bLayer Layer ID.
 */
static volatile uint32_t *pScaleReg( uint8_t bLayer )
{
    Lcdc *pHw = LCDC;
    switch( bLayer )
    {
        case LCDD_HEO:  return (volatile uint32_t*)&pHw->LCDC_HEOCFG13;
    }
    return NULL;
}

/**
 * Return bits per pixel from RGB mode settings.
 * (Note the bits is bits occupied in memory, including reserved)
 */
static uint32_t LCDD_GetBitsPerPixel(uint32_t modeReg)
{
    switch (modeReg)
    {
        /* RGB mode */
        case LCDC_HEOCFG1_RGBMODE_12BPP_RGB_444:
        case LCDC_HEOCFG1_RGBMODE_16BPP_ARGB_4444:
        case LCDC_HEOCFG1_RGBMODE_16BPP_RGBA_4444:
        case LCDC_HEOCFG1_RGBMODE_16BPP_RGB_565:
        case LCDC_HEOCFG1_RGBMODE_16BPP_TRGB_1555:
            return 2*8;

        case LCDC_HEOCFG1_RGBMODE_18BPP_RGB_666PACKED:
        case LCDC_HEOCFG1_RGBMODE_19BPP_TRGB_PACKED:
        case LCDC_HEOCFG1_RGBMODE_24BPP_RGB_888_PACKED:
            return 3*8;

        case LCDC_HEOCFG1_RGBMODE_18BPP_RGB_666:
        case LCDC_HEOCFG1_RGBMODE_19BPP_TRGB_1666:
        case LCDC_HEOCFG1_RGBMODE_24BPP_RGB_888:
        case LCDC_HEOCFG1_RGBMODE_25BPP_TRGB_1888:
        case LCDC_HEOCFG1_RGBMODE_32BPP_ARGB_8888:
        case LCDC_HEOCFG1_RGBMODE_32BPP_RGBA_8888:
            return 3*8;

        /* CLUT mode */
 
        case LCDC_HEOCFG1_CLUTMODE_CLUT_1BPP | LCDC_HEOCFG1_CLUTEN: return 1;
        case LCDC_HEOCFG1_CLUTMODE_CLUT_2BPP | LCDC_HEOCFG1_CLUTEN: return 2;
        case LCDC_HEOCFG1_CLUTMODE_CLUT_4BPP | LCDC_HEOCFG1_CLUTEN: return 4;
        case LCDC_HEOCFG1_CLUTMODE_CLUT_8BPP | LCDC_HEOCFG1_CLUTEN: return 8;

        /* YUV mode */
        case LCDC_HEOCFG1_YUVEN | LCDC_HEOCFG1_YUVMODE_32BPP_AYCBCR:
            return 32;
        case LCDC_HEOCFG1_YUVEN | LCDC_HEOCFG1_YUVMODE_16BPP_YCBCR_MODE0:
        case LCDC_HEOCFG1_YUVEN | LCDC_HEOCFG1_YUVMODE_16BPP_YCBCR_MODE1:
        case LCDC_HEOCFG1_YUVEN | LCDC_HEOCFG1_YUVMODE_16BPP_YCBCR_MODE2:
        case LCDC_HEOCFG1_YUVEN | LCDC_HEOCFG1_YUVMODE_16BPP_YCBCR_MODE3:
        case LCDC_HEOCFG1_YUVEN | LCDC_HEOCFG1_YUVMODE_16BPP_YCBCR_SEMIPLANAR:
        case LCDC_HEOCFG1_YUVEN | LCDC_HEOCFG1_YUVMODE_16BPP_YCBCR_PLANAR:
        case LCDC_HEOCFG1_YUVEN | LCDC_HEOCFG1_YUVMODE_12BPP_YCBCR_SEMIPLANAR:
        case LCDC_HEOCFG1_YUVEN | LCDC_HEOCFG1_YUVMODE_12BPP_YCBCR_PLANAR:
            return 16;
    }
    return 0;
}

/**
 * Enable a LCDC DMA channel
 */
static void LCDD_SetDMA( void* pBuffer,
                         sLCDCDescriptor *pTD,
                         uint32_t regAddr)
{
    volatile uint32_t *pDmaR = (volatile uint32_t*)regAddr;
    /* Modify descriptor */
    pTD->addr = (uint32_t)pBuffer;
    pTD->ctrl = LCDC_BASECTRL_DFETCH;
    pTD->next = (uint32_t)pTD;
    /* Modify registers */
    pDmaR[1] = (uint32_t)pBuffer;
    pDmaR[2] = LCDC_BASECTRL_DFETCH;
    pDmaR[3] = (uint32_t)pTD;
}

/**
 * Disable a LCDC DMA channel
 */
static void LCDD_ClearDMA( sLCDCDescriptor *pTD, uint32_t regAddr )
{
    uint32_t *pReg = (uint32_t *)regAddr;
    volatile uint32_t *pRegCtrl = (volatile uint32_t*)&pReg[1];
    volatile uint32_t *pRegNext = (volatile uint32_t*)&pReg[2];

    /* Modify descriptor */
    if (pTD)
    {
        pTD->ctrl &= ~LCDC_BASECTRL_DFETCH;
        pTD->next  =  (uint32_t)pTD;
    }
    /* Modify control registers */
    *pRegCtrl &= ~LCDC_BASECTRL_DFETCH;
    *pRegNext  =  (uint32_t)pTD;
}

/**
 * Return scaling factor
 */
static uint32_t LCDD_CalcScaleFactor(uint32_t targetW, uint32_t imgW)
{
    uint32_t factor;

    factor = 2048 * (imgW + 1) / (targetW + 1);
    
    //factor = 1024 * (imgW + 1) / (targetW + 1);
    //if (targetW > imgW * 2)
    //    factor -= 7;
    return factor;
}

/**
 * Return a pointer to Color Palette lookup regiters.
 * \param bLayer Layer ID.
 */
static volatile uint32_t *pCLUTReg( uint8_t bLayer )
{
    Lcdc *pHw = LCDC;
    switch( bLayer )
    {
        case LCDD_BASE: return (volatile uint32_t*)&pHw->LCDC_BASECLUT[0];
        case LCDD_OVR1: return (volatile uint32_t*)&pHw->LCDC_OVR1CLUT[0];
        case LCDD_OVR2: return (volatile uint32_t*)&pHw->LCDC_OVR2CLUT[0];
        case LCDD_HEO:  return (volatile uint32_t*)&pHw->LCDC_HEOCLUT[0];
        case LCDD_CUR:  return (volatile uint32_t*)&pHw->LCDC_HCRCLUT[0];
    }
    return NULL;
}

/**
 * Build 8-bit color palette (actually true color)
 */
static void LCDD_BuildCLUT8(volatile uint32_t* pCLUT)
{
    uint32_t r, g, b; /* 3:3:2 */
    for (r = 0; r < 8; r ++)
    {
        for (g = 0; g < 8; g ++)
        {
            for (b = 0; b < 4; b ++)
            {
                *pCLUT ++ =   (r << (16 + 5))
                            + (g << (8  + 5))
                            + (b << (0  + 6));
            }
        }
    }
}

/**
 * Build 4-bit color palette (16 color)
 */
static void LCDD_BuildCLUT4(volatile uint32_t* pCLUT)
{
    uint32_t r, g, b;
    for (r = 0; r < 4; r ++)
    {
        for (g = 0; g < 2; g ++)
        {
            for (b = 0; b < 2; b ++)
            {
                *pCLUT ++ =  (r << (16 + 6))
                           + (g << (8  + 7))
                           + (b << (0  + 7));
            }
        }
    }
}

/**
 * Build 2-bit color palette (4 gray)
 */
static void LCDD_BuildCLUT2(volatile uint32_t* pCLUT)
{
    pCLUT[0] = 0x000000;
    pCLUT[1] = 0x505050;
    pCLUT[2] = 0xA0A0A0;
    pCLUT[3] = 0xFFFFFF;
}

/**
 * Build 1-bit color palette (black & white)
 */
static void LCDD_BuildCLUT1(volatile uint32_t* pCLUT)
{
    pCLUT[0] = 0x000000;
    pCLUT[1] = 0xFFFFFF;
}

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
/**
 * \brief Initializes the LCD controller.
 * Configure SMC to access LCD controller at 64MHz MCK.
 */
void LCDD_Initialize( void )
{
    Lcdc *pHw = LCDC;
    Pmc *pPmc = PMC;

    /* Configure PIO */
    PIO_Configure(pPinsLCD, PIO_LISTSIZE(pPinsLCD));

    LCDD_Off();
    
    /* Reset CLUT information */
    lcddBase.clut.bpp = 0;
    lcddOvr1.clut.bpp = 0;
    lcddOvr2.clut.bpp = 0;
    lcddHeo.clut.bpp  = 0;
    lcddHcc.clut.bpp  = 0;

    /* Reset layer information */
    lcddBase.pBuffer = NULL;
    lcddOvr1.pBuffer = NULL;
    lcddOvr2.pBuffer = NULL;
    lcddHeo.pBuffer  = NULL;
    lcddHcc.pBuffer  = NULL;

    /* No canvas selected */
    lcddCanvas.pBuffer = NULL;

    /* Enable peripheral clock */
    PMC_EnablePeripheral(ID_LCDC);
    pPmc->PMC_SCER = (0x1u << 3);

    /* Timing Engine Configuration */
    
    /* Disable interrupt */
    pHw->LCDC_LCDIDR = 0xFFFFFFFF;

    /* Configure channels */

    /* Base */
    pHw->LCDC_BASECFG0 =  LCDC_BASECFG0_DLBO | LCDC_BASECFG0_BLEN_AHB_INCR16;
    pHw->LCDC_BASECFG1 =  LCDC_BASECFG1_RGBMODE_24BPP_RGB_888_PACKED;

    /* Overlay 1, GA 0xFF */                   
    pHw->LCDC_OVR1CFG0 =  LCDC_OVR1CFG0_DLBO | LCDC_OVR1CFG0_BLEN_AHB_BLEN_INCR16
                       |  LCDC_OVR1CFG0_ROTDIS
                       ;
    pHw->LCDC_OVR1CFG1 =  LCDC_OVR1CFG1_RGBMODE_24BPP_RGB_888_PACKED;
    pHw->LCDC_OVR1CFG9 =  LCDC_OVR1CFG9_GA(0xFF) | LCDC_OVR1CFG9_GAEN;

    /* Overlay 2, GA 0xFF */
    pHw->LCDC_OVR2CFG0 =  LCDC_OVR2CFG0_DLBO | LCDC_OVR2CFG0_BLEN_AHB_INCR16
                       |  LCDC_OVR2CFG0_ROTDIS
                       ;
    pHw->LCDC_OVR2CFG1 =  LCDC_OVR2CFG1_RGBMODE_24BPP_RGB_888_PACKED;
    pHw->LCDC_OVR2CFG9 =  LCDC_OVR2CFG9_GA(0xFF) | LCDC_OVR2CFG9_GAEN;
    
    /* High End Overlay, GA 0xFF */
    pHw->LCDC_HEOCFG0  =  LCDC_HEOCFG0_DLBO | LCDC_HEOCFG0_BLEN_AHB_BLEN_INCR16
                       |  LCDC_HEOCFG0_ROTDIS
                       ;
    pHw->LCDC_HEOCFG1  =  LCDC_HEOCFG1_RGBMODE_24BPP_RGB_888_PACKED;
    pHw->LCDC_HEOCFG12 =  LCDC_HEOCFG12_GA(0xFF) | LCDC_HEOCFG12_GAEN;

    /* Hardware Cursor, GA 0xFF, Key #000000 */
    pHw->LCDC_HCRCFG0  =  LCDC_HCRCFG0_DLBO | LCDC_HCRCFG0_BLEN_AHB_BLEN_INCR16;
    pHw->LCDC_HCRCFG1  =  LCDC_HCRCFG1_RGBMODE_24BPP_RGB_888_PACKED;
    pHw->LCDC_HCRCFG7  =  0x000000;
    pHw->LCDC_HCRCFG8  =  0xFFFFFF;
    pHw->LCDC_HCRCFG9  =  LCDC_HCRCFG9_GA(0xFF) | LCDC_HCRCFG9_GAEN;

    LCDD_On();
}

/**
 * Check if specified layer is working.
 * \param bLayer Layer ID.
 * \return 1 if layer is on.
 */
uint8_t LCDD_IsLayerOn( uint8_t bLayer )
{
    volatile uint32_t *pReg = pEnableReg(bLayer);
    if (pReg) return ((pReg[2] & LCDC_BASECHSR_CHSR) > 0);
    return 0;
}

/**
 * Enable(turn on)/Disable(hide) specified layer.
 * \param bLayer Layer ID.
 * \param bEnDis Enable/Disable.
 */
void LCDD_EnableLayer( uint8_t bLayer, uint8_t bEnDis )
{
    volatile uint32_t *pReg = pEnableReg(bLayer);
    volatile uint32_t *pBlR = pBlenderReg(bLayer);
    if (pReg && bLayer > LCDD_CONTROLLER)
    {
        if (bEnDis)
        {
            pReg[0]  = LCDC_BASECHER_CHEN | LCDC_BASECHER_UPDATEEN;
            pBlR[0] |= LCDC_HEOCFG12_DMA | LCDC_HEOCFG12_OVR;
        }
        else
        {
            pReg[1]  = LCDC_BASECHDR_CHDIS;
            pBlR[0] &= ~(LCDC_HEOCFG12_DMA | LCDC_HEOCFG12_OVR);
        }
    }
}

/**
 * Refresh layer
 * \param bLayer Layer ID.
 */
void LCDD_Refresh( uint8_t bLayer )
{
    volatile uint32_t *pBlR = pBlenderReg(bLayer);
    volatile uint32_t *pEnR = pEnableReg(bLayer);
    if (pBlR)
    {
        if (pEnR[2] & LCDC_OVR1CHSR_CHSR)
        {
            pBlR[0] |=  LCDC_HEOCFG12_DMA;
            pEnR[0] = LCDC_OVR1CHER_UPDATEEN;
        }
    }
}

/**
 * Set display window position.
 * \param bLayer Layer ID.
 * \param x X position.
 * \param y Y position.
 */
void LCDD_SetPosition( uint8_t bLayer,
                       uint32_t x, uint32_t y )
{
    volatile uint32_t *pChReg = pEnableReg(bLayer);
    volatile uint32_t *pXyReg = pWinReg(bLayer);
    uint32_t w, h;

    w = (pXyReg[1] & LCDC_OVR1CFG3_XSIZE_Msk) >> LCDC_OVR1CFG3_XSIZE_Pos;
    h = (pXyReg[1] & LCDC_OVR1CFG3_YSIZE_Msk) >> LCDC_OVR1CFG3_YSIZE_Pos;

    if (x+w >= BOARD_LCD_WIDTH)  x = BOARD_LCD_WIDTH - w;
    if (y+h >= BOARD_LCD_HEIGHT) y = BOARD_LCD_HEIGHT - h;

    if (pXyReg)
    {
        pXyReg[0] = LCDC_OVR1CFG2_XPOS(x) | LCDC_OVR1CFG2_YPOS(y);
        if (pChReg[2] & LCDC_OVR1CHSR_CHSR)
            pChReg[0] = LCDC_OVR1CHER_UPDATEEN;
    }
}

/**
 * Set Prioty of layer (only for HEO now).
 * \param bLayer Layer ID (HEO).
 * \param bPri   Prority value.
 */
void LCDD_SetPrioty( uint8_t bLayer, uint8_t bPri )
{
    Lcdc * pHw = LCDC;
    if ( bLayer != LCDD_HEO ) return;
    if (bPri)
        pHw->LCDC_HEOCFG12 |=  LCDC_HEOCFG12_VIDPRI;
    else
        pHw->LCDC_HEOCFG12 &= ~LCDC_HEOCFG12_VIDPRI;
    pHw->LCDC_HEOCHER = LCDC_HEOCHER_UPDATEEN;
}

/**
 * Return Prioty of layer (only for HEO now).
 * \param bLayer Layer ID (HEO).
 */
uint8_t LCDD_GetPrioty( uint8_t bLayer )
{
    Lcdc * pHw = LCDC;
    if ( bLayer != LCDD_HEO ) return 0;
    return (pHw->LCDC_HEOCFG12 & LCDC_HEOCFG12_VIDPRI) > 0;
}

/**
 * Global & Local Alpha Enable/Disable
 * \param bLayer   Layer ID.
 * \param bEnDisLA Enable/Disable local  alpha.
 * \param bEnDisGA Enable/Disable global alpha.
 */
void LCDD_EnableAlpha( uint8_t bLayer,
                       uint8_t bEnDisLA,
                       uint8_t bEnDisGA )
{
    volatile uint32_t *pEnR  = pEnableReg(bLayer);
    volatile uint32_t *pCfgR = pBlenderReg(bLayer);
    uint32_t cfg;
    if (pCfgR)
    {
        cfg = (*pCfgR) & ~(LCDC_OVR1CFG9_LAEN | LCDC_OVR1CFG9_GAEN);
        if (bEnDisGA) cfg |= LCDC_OVR1CFG9_GAEN;
        if (bEnDisLA) cfg |= LCDC_OVR1CFG9_LAEN;
        (*pCfgR) = cfg;

        pEnR[0] = LCDC_OVR1CHER_UPDATEEN;
    }
}

/**
 * Set alpha value
 * \param bLayer Layer ID (OVR1, HEO or CUR).
 * \param bReverse Reverse alpha (alpha -> 1 - alpha).
 * \param bAlpha   Global alpha value.
 */
void LCDD_SetAlpha( uint8_t bLayer,
                    uint8_t bReverse,
                    uint8_t bAlpha )
{
    volatile uint32_t *pEnR  = pEnableReg(bLayer);
    volatile uint32_t *pCfgR = pBlenderReg(bLayer);
    uint32_t cfg;

    if (pCfgR)
    {
        cfg = (*pCfgR) & ~(LCDC_OVR1CFG9_REVALPHA | LCDC_OVR1CFG9_GA_Msk);
        if (bReverse) cfg |= LCDC_OVR1CFG9_REVALPHA;
        (*pCfgR) = cfg | LCDC_OVR1CFG9_GA(bAlpha);

        pEnR[0] = LCDC_OVR1CHER_UPDATEEN;
    }
}

/**
 * Get alpha value
 * \param bLayer Layer ID (OVR1, HEO or CUR).
 */
uint8_t LCDD_GetAlpha( uint8_t bLayer )
{
    Lcdc * pHw = LCDC;
    volatile uint32_t *pCfg;
    uint32_t bmMask = LCDC_OVR1CFG9_GA_Msk;
    uint32_t bShift = LCDC_OVR1CFG9_GA_Pos;

    switch( bLayer )
    {
        case LCDD_OVR1: pCfg = (volatile uint32_t *)&pHw->LCDC_OVR1CFG9; break;
        case LCDD_OVR2: pCfg = (volatile uint32_t *)&pHw->LCDC_OVR2CFG9; break;
        case LCDD_HEO:  pCfg = (volatile uint32_t *)&pHw->LCDC_HEOCFG9;  break;
        case LCDD_CUR:  pCfg = (volatile uint32_t *)&pHw->LCDC_HCRCFG9;  break;
        default: return 0;
    }

    return (((*pCfg) >> bShift) & bmMask);
}

/**
 * Enable and Set Color Keying
 * \param bLayer  Layer ID (OVR1, HEO or CUR).
 * \param bDstSrc Destination/Source keying.
 * \param dwColor Color to matching.
 * \param dwMask  Color bit mask.
 */
void LCDD_SetColorKeying( uint8_t bLayer, uint8_t bDstSrc,
                          uint32_t dwColor, uint32_t dwMask )
{
    volatile uint32_t *pEnR    = pEnableReg(bLayer);
    volatile uint32_t *pBCfgR  = pBlenderReg(bLayer);
    volatile uint32_t *pColorR = pColorReg(bLayer);
    if (pBCfgR == NULL) return;
    /* Select the Overlay to Blit */
    /* Dest/Source Keying */
    if (bDstSrc)    *pBCfgR |=  LCDC_HEOCFG12_DSTKEY;
    else            *pBCfgR &= ~LCDC_HEOCFG12_DSTKEY;
    /* Activate Color Keying */
    *pBCfgR |= LCDC_HEOCFG12_CRKEY;
    /* Program Color Keying */
    pColorR[1] = dwColor;
    pColorR[2] = dwMask;
    /* Update */
    pEnR[0] = LCDC_HEOCHER_UPDATEEN;
}

/**
 * Disable Color Keying
 * \param bLayer  Layer ID (OVR1, HEO or CUR).
 */
void LCDD_DisableColorKeying( uint8_t bLayer )
{
    volatile uint32_t *pEnR    = pEnableReg(bLayer);
    volatile uint32_t *pBCfgR  = pBlenderReg(bLayer);
    volatile uint32_t *pColorR = pColorReg(bLayer);
    if (pBCfgR == NULL) return;
    *pBCfgR &= ~LCDC_HEOCFG12_CRKEY;
    pColorR[2] = 0;
    /* Update */
    pEnR[0] = LCDC_HEOCHER_UPDATEEN;
}

/**
 * Set Color Lookup Table
 * \param bLayer   Layer ID (OVR1, HEO or CUR).
 * \param pCLUT    Pointer to color lookup table.
 * \param bpp      Bits Per Pixel (1, 2, 4, 8).
 * \param nbColors Number of colors indexed in table.
 */
void LCDD_SetCLUT( uint8_t bLayer,
                   uint32_t *pCLUT,
                   uint8_t bpp, uint8_t nbColors )
{
    //Lcdc *pHw = LCDC;
    volatile uint32_t* pCLUTR = pCLUTReg(bLayer);
    sCLUTInfo *        pInfo  = &pLayer(bLayer)->clut;

    if (pInfo == NULL) return;

    pInfo->bpp = bpp;
    /* Customize CLUT */
    if (pCLUT)
    {
        uint32_t i;
        if (nbColors == 0) nbColors = 1 << bpp;
        pInfo->nbColors = nbColors;
        for (i = 0; i < nbColors; i ++) pCLUTR[i] = pCLUT[i];
    }
    /* Build CLUT */
    else
    {
        pInfo->nbColors = 1 << bpp;
        switch (bpp)
        {
            case 1: LCDD_BuildCLUT1(pCLUTR); break;
            case 2: LCDD_BuildCLUT2(pCLUTR); break;
            case 4: LCDD_BuildCLUT4(pCLUTR); break;
            case 8: LCDD_BuildCLUT8(pCLUTR); break;
        }
    }
}

/**
 * Display an image on specified layer.
 * (Image scan origion: Left -> Right, Top -> Bottom.)
 * \note w & h should be the rotated result.
 * \note for LCDD_BASE: x, y don't care. w always > 0.
 * \note for LCDD_HEO:imgW & imgH is used.
 * \param bLayer  Layer ID (OVR1, HEO or CUR).
 * \param pBuffer Pointer to image data.
 * \param bPP     Bits Per Pixel.
 *                - 16: TRGB 1555
 *                - 24:  RGB  888  packed
 *                - 32: ARGB 8888
 * \param x       X position.
 * \param y       Y position.
 * \param w       Width  (<0 means Right  -> Left data).
 * \param h       Height (<0 means Bottom -> Top data).
 * \param imgW    Source image width.
 * \param imgH    Source image height.
 * \param wRotate Rotation (clockwise, 0, 90, 180, 270 accepted).
 */
void *LCDD_ShowBMPRotated( uint8_t bLayer,
                           void* pBuffer, uint8_t bpp,
                           uint32_t x, uint32_t y,
                           int32_t  w, int32_t  h,
                           uint32_t imgW, uint32_t imgH,
                           int16_t wRotate)
{
  
    //Lcdc *pHw = LCDC;
    sLayer            *pLD   = pLayer(bLayer);
    //sCLUTInfo         *pClut = &pLD->clut;
    sLCDCDescriptor   *pTD   = &pLD->dmaD;
    volatile uint32_t *pEnR  = pEnableReg(bLayer);
    volatile uint32_t *pDmaR = pHeadReg(bLayer);
    volatile uint32_t *pWinR = pWinReg(bLayer);
    volatile uint32_t *pStrR = pStrideReg(bLayer);
    volatile uint32_t *pSclR = pScaleReg(bLayer);
    volatile uint32_t *pBlR  = pBlenderReg(bLayer);
    volatile uint32_t *pCfgR = pCfgReg(bLayer);
    uint8_t bPStride = LCDD_IsPStrideSupported(bLayer);

    uint8_t bBottomUp  = (h < 0);
    uint8_t bRightLeft = (w < 0);
    uint32_t padding = 0;
    int32_t srcW, srcH;
    uint32_t bitsPRow, bytesPRow;
    uint32_t bytesPPix = bpp >> 3;

    void* pOldBuffer = pLD->pBuffer;

    if (pCfgR == NULL)  return pOldBuffer;

    //printf("Show %x @ %d: (%d,%d)+(%d,%d) img %d x %d * %d\n\r", pBuffer, bLayer, x, y, w, h, imgW, imgH, bpp);

    switch (bpp)
    {
        case 16: /*  RGB 565 */
            if((pCfgR[1] & LCDC_HEOCFG1_YUVEN)!= LCDC_HEOCFG1_YUVEN)
            {
                pCfgR[1] = LCDC_HEOCFG1_RGBMODE_16BPP_RGB_565;//LCDC_HEOCFG1_RGBMODE_16BPP_TRGB_1555;
            }
            break;
        case 24: /*  RGB  888 packed */
            pCfgR[1] = LCDC_HEOCFG1_RGBMODE_24BPP_RGB_888_PACKED;
            break;
        case 32: /* ARGB 8888 */
            pCfgR[1] = LCDC_HEOCFG1_RGBMODE_32BPP_ARGB_8888;
            break;
         default: return pOldBuffer;
    }
    /* Windows position & size check */
    if (h < 0)          h =- h;
    if (w < 0)          w =- w;
    if (x + w > BOARD_LCD_WIDTH)
    {
        //printf("! w %d -> %d\n\r", w, BOARD_LCD_WIDTH-x);
        w = BOARD_LCD_WIDTH - x;
    }
    if (y + h > BOARD_LCD_HEIGHT)
    {
        //printf("! h %d -> %d\n\r", h, BOARD_LCD_HEIGHT-y);
        h = BOARD_LCD_HEIGHT - y;
    }
    if (w == 0) w ++;
    if (h == 0) h ++;
    if (imgW == 0) imgW ++;
    if (imgH == 0) imgH ++;

    /* Only 0,(-)90,(-)180,(-)270 accepted */
    switch(wRotate)
    {
        case 0: case 90: case 180: case 270:
            break;
        case -90: case -180: case -270:
            wRotate += 360;
            break;
        default: return NULL;
    }

    /* Setup display buffer & window */
    if (pBuffer) pLD->pBuffer = pBuffer;
    else         pBuffer = pLD->pBuffer;

    /* Set display buffer & mode */
    bitsPRow  = imgW * bpp;
    bytesPRow = bitsPRow >> 3;
    if (bitsPRow & 0x7) bytesPRow ++;
    if (bytesPRow & 0x3) padding = 4 - (bytesPRow & 0x3);

    /* No X mirror supported layer, no Right->Left scan */
    if (!bPStride)  bRightLeft = 0;

    /* --------- Mirror & then rotate --------- */
    /* Normal direction: Left,Top -> Right,Down */
    if (   (!bRightLeft && !bBottomUp && wRotate ==   0)
        || ( bRightLeft &&  bBottomUp && wRotate == 180) )
    {
        /* No rotation optimization */
        pCfgR[0] |= LCDC_HEOCFG0_ROTDIS;
        /* X0 ++ */
        if (bPStride)   pStrR[1] = LCDC_HEOCFG6_PSTRIDE(0);
        /* Y0 ++ */
        pStrR[0] = LCDC_HEOCFG5_XSTRIDE(padding);
        /* Pointer to Left,Top (x0,y0) */
    }
    /* X mirror: Right,Top -> Left,Down */
    else if ( ( bRightLeft && !bBottomUp && wRotate ==   0)
            ||(!bRightLeft &&  bBottomUp && wRotate == 180) )
    {
        /* No rotation optimization */
        pCfgR[0] |= LCDC_HEOCFG0_ROTDIS;
        /* X1 -- */
        if (bPStride)   pStrR[1] = LCDC_HEOCFG6_PSTRIDE(0-2*bytesPPix);
        /* Y0 ++ */
        pStrR[0] = LCDC_HEOCFG5_XSTRIDE(bytesPRow*2+padding-2*bytesPPix);
        /* Pointer to Right,Top (x1,y0) */
        pBuffer = (void*)((uint32_t)pBuffer
                + bytesPPix*(imgW-1));
    }
    /* Y mirror: Left,Down -> Right,Top */
    else if ( (!bRightLeft &&  bBottomUp && wRotate ==   0)
            ||( bRightLeft && !bBottomUp && wRotate == 180) )
    {
        /* No rotation optimization */
        pCfgR[0] |= LCDC_HEOCFG0_ROTDIS;
        /* X0 ++ */
        if (bPStride)   pStrR[1] = LCDC_HEOCFG6_PSTRIDE(0);
        /* Y1 -- */
        pStrR[0] = LCDC_HEOCFG5_XSTRIDE(0-(bytesPRow*2+padding));
        /* Pointer to Left,Down (x0,y1) */
        pBuffer = (void*)((uint32_t)pBuffer
                + (bytesPRow+padding)*(imgH-1));
    }
    /* X,Y mirror: Right,Top -> Left,Down */
    else if ( ( bRightLeft &&  bBottomUp && wRotate ==   0)
            ||(!bRightLeft && !bBottomUp && wRotate == 180) )
    {
        /* No rotation optimization */
        pCfgR[0] |= LCDC_HEOCFG0_ROTDIS;
        /* X1 -- */
        if (bPStride)   pStrR[1] = LCDC_HEOCFG6_PSTRIDE(0-2*bytesPPix);
        /* Y1 -- */
        pStrR[0] = LCDC_HEOCFG5_XSTRIDE(0-(bytesPPix*2+padding));
        /* Pointer to Left,Down (x1,y1) */
        pBuffer = (void*)((uint32_t)pBuffer
                + (bytesPRow+padding)*(imgH-1)
                + (bytesPPix)*(imgW-1));
    }
    /* Rotate  90: Down,Left -> Top,Right (with w,h swap) */
    else if ( (!bRightLeft && !bBottomUp && wRotate ==  90)
            ||( bRightLeft &&  bBottomUp && wRotate == 270) )
    {
        /* No rotation optimization */
        pCfgR[0] |= LCDC_HEOCFG0_ROTDIS;
        /* Y -- as pixels in row */
        if (bPStride)   pStrR[1] = LCDC_HEOCFG6_PSTRIDE(0-(bytesPPix+bytesPRow+padding));
        /* X ++ as rows */
        pStrR[0] = LCDC_HEOCFG5_XSTRIDE((bytesPRow+padding)*(imgH-1));
        /* Pointer to Bottom,Left */
        pBuffer = (void*)((uint32_t)pBuffer
                + (bytesPRow+padding)*(imgH-1));
    }
    /* Rotate 270: Top,Right -> Down,Left (with w,h swap) */
    else if ( (!bRightLeft && !bBottomUp && wRotate == 270)
            ||( bRightLeft &&  bBottomUp && wRotate ==  90) )
    {
        /* No rotation optimization */
        pCfgR[0] |= LCDC_HEOCFG0_ROTDIS;
        /* Y ++ as pixels in row */
        if (bPStride)   pStrR[1] = LCDC_HEOCFG6_PSTRIDE(bytesPRow+padding-bytesPPix);
        /* X -- as rows */
        pStrR[0] = LCDC_HEOCFG5_XSTRIDE(0-2*bytesPPix-(bytesPRow+padding)*(imgH-1));
        /* Pointer to top right */
        pBuffer = (void*)((uint32_t)pBuffer
                + bytesPPix*(imgW-1));
    }
    /* Mirror X then Rotate 90: Down,Right -> Top,Left */
    else if ( ( bRightLeft && !bBottomUp && wRotate ==  90)
            ||(!bRightLeft &&  bBottomUp && wRotate == 270) )
    {
        /* No rotation optimization */
        pCfgR[0] |= LCDC_HEOCFG0_ROTDIS;
        /* Y -- as pixels in row */
        if (bPStride)   pStrR[1] = LCDC_HEOCFG6_PSTRIDE(0-(bytesPPix+bytesPRow+padding));
        /* X -- as rows */
        pStrR[0] = LCDC_HEOCFG5_XSTRIDE(0-2*bytesPPix+(bytesPRow+padding)*(imgH-1));
        /* Pointer to down right (x1,y1) */
        pBuffer = (void*)((uint32_t)pBuffer
                + (bytesPRow+padding)*(imgH-1)
                + (bytesPPix)*(imgW-1));
    }
    /* Mirror Y then Rotate 90: Top,Left -> Down,Right */
    else if ( (!bRightLeft &&  bBottomUp && wRotate ==  90)
            ||( bRightLeft && !bBottomUp && wRotate == 270) )
    {
        /* No rotation optimization */
        pCfgR[0] |= LCDC_HEOCFG0_ROTDIS;
        /* Y ++ as pixels in row */
        if (bPStride)   pStrR[1] = LCDC_HEOCFG6_PSTRIDE(bytesPRow+padding-bytesPPix);
        /* X ++ as rows */
        pStrR[0] = LCDC_HEOCFG5_XSTRIDE(0-(bytesPRow+padding)*(imgH-1));
        /* Pointer to top left (x0,y0) */
    }
    /** DMA is running, just add new descriptor to queue */
    if (pBlR[0] & LCDC_HEOCFG12_DMA)
    {
        pTD->addr = (uint32_t)pBuffer;
        pTD->ctrl = LCDC_HEOCTRL_DFETCH;
        pTD->next = (uint32_t)pTD;
        pDmaR[0] = (uint32_t)pTD;
        pEnR[0] = LCDC_HEOCHER_A2QEN;
    }
    else
    {
        /* 2. Write the channel descriptor (DSCR) structure in the system memory by
              writing DSCR.CHXADDR Frame base address, DSCR.CHXCTRL channel control
              and DSCR.CHXNEXT next descriptor location.        
           3. If more than one descriptor is expected, the DFETCH field of
              DSCR.CHXCTRL is set to one to enable the descriptor fetch operation.      
           4. Write the DSCR.CHXNEXT register with the address location of the
              descriptor structure and set DFETCH field of the DSCR.CHXCTRL register
              to one. */
        LCDD_SetDMA(pBuffer, pTD, (uint32_t)pDmaR);
    }
    CP15_flush_dcache_for_dma ((uint32_t)pTD, ((uint32_t)pTD) + sizeof(pTD));
    /* Set window & position */
    if (pWinR)
    {
        pWinR[0] = LCDC_HEOCFG2_XPOS(x) | LCDC_HEOCFG2_YPOS(y);
        pWinR[1] = LCDC_HEOCFG3_XSIZE(w-1) | LCDC_HEOCFG3_YSIZE(h-1);
    }
    /* Scaling setup */
    if (pSclR)
    {

        /* Image size only used in scaling */
        /* Scaling target */
        if (wRotate == 90 || wRotate == 270)
        {
            srcW = imgH; srcH = imgW;
        }
        else
        {
            srcW = imgW; srcH = imgH;
        }
        pWinR[2] = LCDC_HEOCFG4_XMEM_SIZE(srcW-1) | LCDC_HEOCFG4_YMEM_SIZE(srcH-1);
        /* Scaled */
        if (w != srcW || h != srcH)
        {
            uint16_t wYf, wXf;
            wXf = LCDD_CalcScaleFactor(w, srcW);
            wYf = LCDD_CalcScaleFactor(h, srcH);
            //printf("- Scale(%d,%d)\n\r", wXf, wYf);
            pSclR[0] = LCDC_HEOCFG13_YFACTOR(wYf)
                     | LCDC_HEOCFG13_XFACTOR(wXf)
                     | LCDC_HEOCFG13_SCALEN
                     ;
        }
        /* Disable scaling */
        else
        {
            pSclR[0] = 0;
        }
    }
    /* Enable DMA */
    if (pBuffer)
    {
        pBlR[0] |= LCDC_HEOCFG12_DMA
                 | LCDC_HEOCFG12_OVR
                 ;
    }
    /* Enable & Update */
    /* 5. Enable the relevant channel by writing one to the CHEN field of the
          CHXCHER register. */
    pEnR[0] = LCDC_HEOCHER_UPDATEEN | LCDC_HEOCHER_CHEN;

    /* 6. An interrupt may be raised if unmasked when the descriptor has been
          loaded.  */

    return pOldBuffer;
}

/**
 * Display an image on specified layer.
 * (Image scan: Left -> Right, Top -> Bottom.)
 * \param bLayer  Layer ID (OVR1, HEO or CUR).
 * \param pBuffer Pointer to image data.
 * \param bPP     Bits Per Pixel.
 *                - 16: TRGB 1555
 *                - 24:  RGB  888  packed
 *                - 32: ARGB 8888
 * \param x       X position.
 * \param y       Y position.
 * \param w       Width  (<0 means Right  -> Left data).
 * \param h       Height (<0 means Bottom -> Top data).
 * \param imgW    Source image width.
 * \param imgH    Source image height.
 * \return Pointer to old display image data.
 */
void *LCDD_ShowBMPScaled( uint8_t bLayer,
                          void* pBuffer, uint8_t bpp,
                          uint32_t x, uint32_t y,
                          int32_t  w, int32_t  h,
                          uint32_t imgW, uint32_t imgH )
{
    return LCDD_ShowBMPRotated(bLayer, pBuffer, bpp,
                               x, y, w, h, imgW, imgH, 0);
}

/**
 * Display an image on specified layer.
 * (Image scan: Left -> Right, Top -> Bottom.)
 * \param bLayer  Layer ID (OVR1, HEO or CUR).
 * \param pBuffer Pointer to image data.
 * \param bPP     Bits Per Pixel.
 *                - 16: TRGB 1555
 *                - 24:  RGB  888  packed
 *                - 32: ARGB 8888
 * \param x       X position.
 * \param y       Y position.
 * \param w       Width
 * \param h       Height (<0 means Bottom -> Top data).
 * \return Pointer to old display image data.
 */
void *LCDD_ShowBMP( uint8_t bLayer,
                    void* pBuffer, uint8_t bpp,
                    uint32_t x, uint32_t y,
                    int32_t  w, int32_t  h )
{
    return LCDD_ShowBMPRotated(bLayer, pBuffer, bpp,
                               x, y, w, h,
                               w, (h < 0) ? (-h) : h,
                               0);
}

/**
 * Start display on base layer
 * \param pBuffer   Pointer to image data.
 * \param bpp       Bits Per Pixel.
 * \param bBottomUp Scan from bottom to top.
 * \return Pointer to old display image data.
 */
void *LCDD_ShowBase( void* pBuffer, uint8_t bpp, uint8_t bBottomUp )
{
    return LCDD_ShowBMP(LCDD_BASE, pBuffer, bpp,
                        0, 0,
                        BOARD_LCD_WIDTH,
                        bBottomUp ? -BOARD_LCD_HEIGHT : BOARD_LCD_HEIGHT);
}

/**
 * Stop display on base layer
 */
void LCDD_StopBase( void )
{
    Lcdc *pHw = LCDC;

    if (!(pHw->LCDC_BASECHSR & LCDC_BASECHSR_CHSR))
        return;

    /* 1. Clear the DFETCH bit in the DSCR.CHXCTRL field of the DSCR structure
          will disable the channel at the end of the frame. */
    /* 2. Set the DSCR.CHXNEXT field of the DSCR structure will disable the
          channel at the end of the frame. */
    LCDD_ClearDMA(&lcddBase.dmaD, (uint32_t)&pHw->LCDC_BASEADDR);

    /* 3. Writing one to the CHDIS field of the CHXCHDR register will disable
          the channel at the end of the frame. */
    pHw->LCDC_BASECHDR = LCDC_BASECHDR_CHDIS;

    /* 4. Writing one to the CHRST field of the CHXCHDR register will disable
          the channel immediately. This may occur in the middle of the image. */

    /* 5. Poll CHSR field in the CHXCHSR register until the channel is
          successfully disabled. */
    while (pHw->LCDC_BASECHSR & LCDC_BASECHSR_CHSR);
}

/**
 * Start display on overlay 1 layer
 */
void *LCDD_ShowOvr1( void* pBuffer, uint8_t bpp,
                     uint32_t x, uint32_t y, int32_t w, int32_t h )
{
    return LCDD_ShowBMP(LCDD_OVR1,
                        pBuffer, bpp, x, y, w, h);
}

/**
 * Stop display on overlay 1 layer
 */
void LCDD_StopOvr1( void )
{
    Lcdc *pHw = LCDC;

    if (!(pHw->LCDC_OVR1CHSR & LCDC_OVR1CHSR_CHSR))
        return;

    /* 1. Clear the DFETCH bit in the DSCR.CHXCTRL field of the DSCR structure
          will disable the channel at the end of the frame. */
    /* 2. Set the DSCR.CHXNEXT field of the DSCR structure will disable the
          channel at the end of the frame. */
    LCDD_ClearDMA(&lcddOvr1.dmaD, (uint32_t)&pHw->LCDC_OVR1ADDR);

    /* 3. Writing one to the CHDIS field of the CHXCHDR register will disable
          the channel at the end of the frame. */
    pHw->LCDC_OVR1CHDR = LCDC_OVR1CHDR_CHDIS;

    /* 4. Writing one to the CHRST field of the CHXCHDR register will disable
          the channel immediately. This may occur in the middle of the image. */

    /* 5. Poll CHSR field in the CHXCHSR register until the channel is
          successfully disabled. */
    while (pHw->LCDC_OVR1CHSR & LCDC_OVR1CHSR_CHSR);
}

/**
 * Start display on High End Overlay layer
 */
void * LCDD_ShowHeo( void *pBuffer, uint8_t bpp,
                     uint32_t x, uint32_t y, int32_t w, int32_t h,
                     uint32_t imgW, uint32_t imgH )
{
    return LCDD_ShowBMPRotated(LCDD_HEO,
                               pBuffer, bpp,
                               x, y, w, h,
                               imgW,imgH,
                               0);
}

/**
 * Stop display on High End Overlay layer
 */
void LCDD_StopHeo( void )
{
    Lcdc *pHw = LCDC;

    if (!(pHw->LCDC_HEOCHSR  & LCDC_HEOCHSR_CHSR))
        return;

    /* 1. Clear the DFETCH bit in the DSCR.CHXCTRL field of the DSCR structure
          will disable the channel at the end of the frame. */
    /* 2. Set the DSCR.CHXNEXT field of the DSCR structure will disable the
          channel at the end of the frame. */
    LCDD_ClearDMA(&lcddHeo.dmaD[0], (uint32_t)&pHw->LCDC_HEOADDR);
    LCDD_ClearDMA(&lcddHeo.dmaD[1], (uint32_t)&pHw->LCDC_HEOUADDR);
    LCDD_ClearDMA(&lcddHeo.dmaD[2], (uint32_t)&pHw->LCDC_HEOVADDR);

    /* 3. Writing one to the CHDIS field of the CHXCHDR register will disable
          the channel at the end of the frame. */
    pHw->LCDC_HEOCHDR  = LCDC_HEOCHDR_CHDIS;

    /* 4. Writing one to the CHRST field of the CHXCHDR register will disable
          the channel immediately. This may occur in the middle of the image. */

    /* 5. Poll CHSR field in the CHXCHSR register until the channel is
          successfully disabled. */
    while (pHw->LCDC_HEOCHSR  & LCDC_HEOCHSR_CHSR);
}

/**
 * Start display on Hardware Cursor layer
 * (Default transparent color is set to #000000, black)
 */
void *LCDD_ShowHcr( void* pBuffer, uint8_t bpp,
                    uint32_t x, uint32_t y, int32_t w, int32_t h )
{
    Lcdc *pHw = LCDC;

    /* Enable default transparent keying */
    if (!(pHw->LCDC_HCRCFG9 & LCDC_HCRCFG9_CRKEY))
    {
        pHw->LCDC_HCRCFG7 = 0x000000;
        pHw->LCDC_HCRCFG8 = 0xFFFFFF;
        pHw->LCDC_HCRCFG9 |= LCDC_HCRCFG9_CRKEY;
    }
    return LCDD_ShowBMP(LCDD_CUR,
                        pBuffer, bpp,
                        x, y, w, h);
}

/**
 * Stop display on Hardware Cursor layer
 */
void LCDD_StopHcr( void )
{
    Lcdc *pHw = LCDC;

    if (!(pHw->LCDC_HCRCHDR  & LCDC_HCRCHSR_CHSR))
        return;

    /* 1. Clear the DFETCH bit in the DSCR.CHXCTRL field of the DSCR structure
          will disable the channel at the end of the frame. */
    /* 2. Set the DSCR.CHXNEXT field of the DSCR structure will disable the
          channel at the end of the frame. */
    LCDD_ClearDMA(&lcddHcc.dmaD, (uint32_t)&pHw->LCDC_HCRADDR);

    /* 3. Writing one to the CHDIS field of the CHXCHDR register will disable
          the channel at the end of the frame. */
    pHw->LCDC_HCRCHDR  = LCDC_HCRCHDR_CHDIS;

    /* 4. Writing one to the CHRST field of the CHXCHDR register will disable
          the channel immediately. This may occur in the middle of the image. */

    /* 5. Poll CHSR field in the CHXCHSR register until the channel is
          successfully disabled. */
    while (pHw->LCDC_HCRCHSR  & LCDC_HCRCHSR_CHSR);
}


/**
 * \brief Turn on the LCD.
 */
void LCDD_On(void)
{
    Pmc *pPmc = PMC;
    Lcdc *pHw = LCDC;

    /* Enable peripheral clock */
    PMC_EnablePeripheral(ID_LCDC);
    pPmc->PMC_SCER = (0x1u << 3);

    /* 1. Configure LCD timing parameters, signal polarity and clock period. */
    pHw->LCDC_LCDCFG0 = LCDC_LCDCFG0_CLKDIV((BOARD_MCK*2)/BOARD_LCD_PIXELCLOCK-2)
                       |LCDC_LCDCFG0_CGDISHCR
                       |LCDC_LCDCFG0_CGDISHEO
                       |LCDC_LCDCFG0_CGDISOVR1
                       |LCDC_LCDCFG0_CGDISOVR2
                       |LCDC_LCDCFG0_CGDISBASE
                       |LCDC_LCDCFG0_CLKPWMSEL
                       |LCDC_LCDCFG0_CLKSEL
                       |LCDC_LCDCFG0_CLKPOL;

    pHw->LCDC_LCDCFG1 = LCDC_LCDCFG1_VSPW(BOARD_LCD_TIMING_VPW-1)
                       |LCDC_LCDCFG1_HSPW(BOARD_LCD_TIMING_HPW-1);

    pHw->LCDC_LCDCFG2 = LCDC_LCDCFG2_VBPW(BOARD_LCD_TIMING_VBP)
                       |LCDC_LCDCFG2_VFPW(BOARD_LCD_TIMING_VFP-1);

    pHw->LCDC_LCDCFG3 = LCDC_LCDCFG3_HBPW(BOARD_LCD_TIMING_HBP-1)
                       |LCDC_LCDCFG3_HFPW(BOARD_LCD_TIMING_HFP-1);

    pHw->LCDC_LCDCFG4 = LCDC_LCDCFG4_RPF(BOARD_LCD_HEIGHT-1)
                       |LCDC_LCDCFG4_PPL(BOARD_LCD_WIDTH-1);

    pHw->LCDC_LCDCFG5 = LCDC_LCDCFG5_GUARDTIME(30)
                       |LCDC_LCDCFG5_MODE_OUTPUT_24BPP
                       |LCDC_LCDCFG5_DISPDLY
                       |LCDC_LCDCFG5_VSPDLYS
                       |LCDC_LCDCFG5_VSPOL
                       |LCDC_LCDCFG5_HSPOL;

    pHw->LCDC_LCDCFG6 = LCDC_LCDCFG6_PWMCVAL(0xF0)
                       |LCDC_LCDCFG6_PWMPOL
                       |LCDC_LCDCFG6_PWMPS(6);

    /* 2. Enable the Pixel Clock by writing one to the CLKEN field of the
          LCDC_LCDEN register. */
    pHw->LCDC_LCDEN = LCDC_LCDEN_CLKEN;
    /* 3. Poll CLKSTS field of the LCDC_LCDSR register to check that the clock
       is running. */
    while(!(pHw->LCDC_LCDSR & LCDC_LCDSR_CLKSTS));

    /* 4. Enable Horizontal and Vertical Synchronization by writing one to the
          SYNCEN field of the LCDC_LCDEN register. */
    pHw->LCDC_LCDEN = LCDC_LCDEN_SYNCEN;
    /* 5. Poll LCDSTS field of the LCDC_LCDSR register to check that the
          synchronization is up. */
    while(!(pHw->LCDC_LCDSR & LCDC_LCDSR_LCDSTS));

    /* 6. Enable the display power signal writing one to the DISPEN field of the
          LCDC_LCDEN register. */
    pHw->LCDC_LCDEN = LCDC_LCDEN_DISPEN;
    /* 7. Poll DISPSTS field of the LCDC_LCDSR register to check that the power
          signal is activated. */
    while(!(pHw->LCDC_LCDSR & LCDC_LCDSR_DISPSTS));
    /* 8. Enable backlight */
    pHw->LCDC_LCDEN = LCDC_LCDEN_PWMEN;
}

/**
 * \brief Turn off the LCD.
 */
void LCDD_Off(void)
{
    Lcdc *pHw  = LCDC;
    Pmc  *pPmc = PMC;

    /* 1. Clear the DFETCH bit in the DSCR.CHXCTRL field of the DSCR structure
          will disable the channel at the end of the frame. */

    /* 2. Set the DSCR.CHXNEXT field of the DSCR structure will disable the
          channel at the end of the frame. */

    /* Disable all DMA channel descriptors */
    LCDD_ClearDMA(&lcddBase.dmaD, (uint32_t)&pHw->LCDC_BASEADDR);
    LCDD_ClearDMA(&lcddOvr1.dmaD, (uint32_t)&pHw->LCDC_OVR1ADDR);
    LCDD_ClearDMA(&lcddOvr2.dmaD, (uint32_t)&pHw->LCDC_OVR2ADDR);
    LCDD_ClearDMA(&lcddHeo.dmaD[0], (uint32_t)&pHw->LCDC_HEOADDR);
    LCDD_ClearDMA(&lcddHeo.dmaD[1], (uint32_t)&pHw->LCDC_HEOUADDR);
    LCDD_ClearDMA(&lcddHeo.dmaD[2], (uint32_t)&pHw->LCDC_HEOVADDR);
    LCDD_ClearDMA(&lcddHcc.dmaD, (uint32_t)&pHw->LCDC_HCRADDR);

    /* 3. Writing one to the CHDIS field of the CHXCHDR register will disable
          the channel at the end of the frame. */

    /* Disable DMA channels */
    pHw->LCDC_BASECHDR = LCDC_BASECHDR_CHDIS;
    pHw->LCDC_OVR1CHDR = LCDC_OVR1CHDR_CHDIS;
    pHw->LCDC_HEOCHDR  = LCDC_HEOCHDR_CHDIS;
    pHw->LCDC_HCRCHDR  = LCDC_HCRCHDR_CHDIS;
    pHw->LCDC_BASECFG4 = 0;

    /* 4. Writing one to the CHRST field of the CHXCHDR register will disable
          the channel immediately. This may occur in the middle of the image. */

    /* 5. Poll CHSR field in the CHXCHSR register until the channel is
          successfully disabled. */
    while (pHw->LCDC_BASECHSR & LCDC_BASECHSR_CHSR);
    while (pHw->LCDC_OVR1CHSR & LCDC_OVR1CHSR_CHSR);
    while (pHw->LCDC_HEOCHSR  & LCDC_HEOCHSR_CHSR);
    while (pHw->LCDC_HCRCHDR  & LCDC_HCRCHSR_CHSR);

    
    /* Timing Engine Power Down Software Operation */

    /* Disable backlight */
    pHw->LCDC_LCDDIS = LCDC_LCDDIS_PWMDIS;
    while (pHw->LCDC_LCDSR & LCDC_LCDSR_PWMSTS);

    /* 1. Disable the DISP signal writing DISPDIS field of the LCDC_LCDDIS
          register. */
    pHw->LCDC_LCDDIS = LCDC_LCDDIS_DISPDIS;
    /* 2. Poll DISPSTS field of the LCDC_LCDSR register to verify that the DISP
          is no longer activated. */
    while (pHw->LCDC_LCDSR & LCDC_LCDSR_DISPSTS);
    
    /* 3. Disable the hsync and vsync signals by writing one to SYNCDIS field of
          the LCDC_LCDDIS register. */
    pHw->LCDC_LCDDIS = LCDC_LCDDIS_SYNCDIS;
    /* 4. Poll LCDSTS field of the LCDC_LCDSR register to check that the
          synchronization is off. */
    while (pHw->LCDC_LCDSR & LCDC_LCDSR_LCDSTS);
    
    /* 5. Disable the Pixel clock by writing one in the CLKDIS field of the
          LCDC_LCDDIS register. */
    pHw->LCDC_LCDDIS = LCDC_LCDDIS_CLKDIS;
    /* 6. Poll CLKSTS field of the LCDC_LCDSR register to check that Pixel Clock
          is disabled. */
    while(pHw->LCDC_LCDSR & LCDC_LCDSR_CLKSTS);

    /* Disable peripheral clock */
    PMC_DisablePeripheral(ID_LCDC);
    /* LCD Clock Disable */
     pPmc->PMC_SCDR = (0x1u << 3);
    
}

/**
 * \brief Set the backlight of the LCD.
 *
 * \param level   Backlight brightness level [1..255],
 *                255 means maximum brightness.
 */
void LCDD_SetBacklight (uint32_t level)
{
    Lcdc *pHw = LCDC;
    uint32_t cfg = pHw->LCDC_LCDCFG6 & ~LCDC_LCDCFG6_PWMCVAL_Msk;

    pHw->LCDC_LCDCFG6 = cfg | LCDC_LCDCFG6_PWMCVAL(level);
}

/**
 * Get canvas layer for LCDD_Draw*
 * \return Layer information pointer.
 */
sLCDDLayer *LCDD_GetCanvas(void)
{
    return &lcddCanvas;
}

/**
 * Flush the current canvas layer*
 */
void LCDD_Flush_CurrentCanvas(void)
{
    sLCDDLayer *pCurrentLayer;
    uint32_t base, height, width;
    pCurrentLayer = LCDD_GetCanvas();
    base = (uint32_t)pCurrentLayer->pBuffer;
    height = pCurrentLayer->wImgH;
    width = pCurrentLayer->wImgW;
    CP15_flush_dcache_for_dma ((uint32_t)base, ((uint32_t)base) + height*width*4);
}

/**
 * Select an LCD layer as canvas layer.
 * Then all drawing operations will apply to current display buffer
 * of selected layer.
 * \note If there is no display buffer for the layer (not running)
 *       selection fails.
 */
uint8_t LCDD_SelectCanvas(uint8_t bLayer)
{
    sLayer *pLD = pLayer(bLayer);
    volatile uint32_t *pXyR = pWinReg(bLayer);
    volatile uint32_t *pCfR = pCfgReg(bLayer);

    if (pLD == NULL) return 0;

    lcddCanvas.pBuffer = (void*)pLD->pBuffer;
    if (pXyR)
    {
        lcddCanvas.wImgW = (pXyR[1] & LCDC_HEOCFG3_XSIZE_Msk) >> LCDC_HEOCFG3_XSIZE_Pos;
        lcddCanvas.wImgH = (pXyR[1] & LCDC_HEOCFG3_YSIZE_Msk) >> LCDC_HEOCFG3_YSIZE_Pos;
    }
    else
    {
        lcddCanvas.wImgW = BOARD_LCD_WIDTH;
        lcddCanvas.wImgH = BOARD_LCD_HEIGHT;
    }
    lcddCanvas.bMode = LCDD_GetBitsPerPixel(pCfR[1] & LCDC_HEOCFG1_RGBMODE_Msk);
    lcddCanvas.bLayer = bLayer;

    return 1;
}

/**
 * Create a blank canvas on a display layer for further operations.
 * \param bLayer    Layer ID.
 * \param pBuffer   Pointer to canvas display buffer.
 * \param bBPP      Bits Per Pixel.
 * \param wX        Canvas X coordinate on base.
 * \param wY        Canvas Y coordinate on base.
 * \param wW        Canvas width.
 * \param wH        Canvas height.
 * \note The content in buffer is destroied.
 */
void *LCDD_CreateCanvas(uint8_t bLayer,
                        void* pBuffer, uint8_t bBPP,
                        uint16_t wX, uint16_t wY,
                        uint16_t wW, uint16_t wH )
{
    void* pOldBuffer;
    uint32_t maxW = BOARD_LCD_WIDTH;
    uint32_t maxH = BOARD_LCD_HEIGHT;

    uint32_t bitsPR, bytesPR;

    switch (bLayer)
    {
        case LCDD_BASE:
            wX = 0; wY = 0;
            break;
        case LCDD_OVR1:case LCDD_OVR2: case LCDD_HEO:
            /* Size check */
            if (wX + wW > BOARD_LCD_WIDTH || wY + wH > BOARD_LCD_HEIGHT)
                return NULL;
            break;
        case LCDD_CUR:
            /* Size check */
            if (wX + wW > BOARD_LCD_WIDTH || wY + wH > BOARD_LCD_HEIGHT
                || wW > 128 || wH > 128)
                return NULL;
            maxW = maxH = 128;
            break;
    }
    if (wW == 0) wW = maxW - wX;
    if (wH == 0) wH = maxH - wY;

    bitsPR = wW * bBPP;
    bytesPR = (bitsPR&0x7) ? (bitsPR/8 + 1) : (bitsPR/8);
    memset(pBuffer, 0xFF, bytesPR*wH);
    pOldBuffer = LCDD_ShowBMPRotated(bLayer, pBuffer, bBPP,
                                     wX, wY, wW, wH, wW, wH,
                                     0);

    lcddCanvas.bLayer  = bLayer;
    lcddCanvas.bMode   = bBPP;
    lcddCanvas.pBuffer = pBuffer;
    lcddCanvas.wImgW   = wW;
    lcddCanvas.wImgH   = wH;

    return pOldBuffer;
}

/**@}*/
#endif /* ifdef LCDC */

