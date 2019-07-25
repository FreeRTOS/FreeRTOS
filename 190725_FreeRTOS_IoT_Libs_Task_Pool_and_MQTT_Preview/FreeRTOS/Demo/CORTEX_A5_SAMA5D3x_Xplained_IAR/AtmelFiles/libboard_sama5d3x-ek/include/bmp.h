/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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

/**
 *  \file
 *  \section Purpose
 * 
 *  Utility for BMP
 * 
 */

#ifndef BMP_H
#define BMP_H

/**  BMP magic number ('BM'). */
#define BMP_TYPE       0x4D42

/**  headerSize must be set to 40 */
#define BITMAPINFOHEADER   40

/*------------------------------------------------------------------------------
 *         Exported types
 *------------------------------------------------------------------------------*/

/*
 * In case of IAR EWARM use, we define an empty macro to turn useless GCC and MDK __attribute__ keyword
 */
#if defined __ICCARM__ || defined __CC_ARM || defined __GNUC__
#    pragma pack( 1 )
#endif

/** BMP (Windows) File Header Format */
typedef struct _BMPFileHeader
{
    /** signature, must be 4D42 hex */
    uint16_t type;
    /** size of BMP file in bytes (unreliable) */
    uint32_t fileSize;
    /** reserved, must be zero */
    uint16_t reserved1;
    /** reserved, must be zero */
    uint16_t reserved2;
    /** offset to start of image data in bytes */
    uint32_t offset;
} BMPFileHeader;

/** BMP (Windows 2.x) Header */
typedef struct _BMP2XHeader
{
    /** size of this header in bytes */
    uint32_t size;
    /** image width in pixels */
    uint16_t width;
    /** image height in pixels */
    uint16_t height;
    /** number of color planes */
    uint16_t planes;
    /** number of bits per pixel */
    uint16_t bitsPerPixel;
} BMP2XHeader;

/** BMP (Windows 3.x) Header, 40 bytes */
typedef struct _BMP3XHeader
{
    /** size of this header in bytes */
    uint32_t size;
    /** image width in pixels */
    int32_t  width;
    /** image height in pixels */
    int32_t  height;
    /** number of color planes */
    uint16_t planes;
    /** number of bits per pixel */
    uint16_t bitsPerPixel;
    /** Compression methods used */
    uint32_t compression;
    /** Size of bitmap in bytes */
    uint32_t sizeOfBitmap;
    /** horizontal resolution in pixels per meter */
    int32_t  xResolution;
    /** vertical resolution in pixels per meter */
    int32_t  yResolution;
    /** number of colors in the image */
    uint32_t colorsUsed;
    /** minimum number of important colors */
    uint32_t colorsImportant;
}  BMP3XHeader;

/** BMP (Windows 95, V4) Header, 108 bytes */
typedef struct _BMP4Header
{
    /** size of this header in bytes */
    uint32_t size;
    /** image width in pixels */
    int32_t  width;
    /** image height in pixels */
    int32_t  height;
    /** number of color planes */
    uint16_t planes;
    /** number of bits per pixel */
    uint16_t bitsPerPixel;
    /** Compression methods used */
    uint32_t compression;
    /** Size of bitmap in bytes */
    uint32_t sizeOfBitmap;
    /** horizontal resolution in pixels per meter */
    int32_t  xResolution;
    /** vertical resolution in pixels per meter */
    int32_t  yResolution;
    /** number of colors in the image */
    uint32_t colorsUsed;
    /** minimum number of important colors */
    uint32_t colorsImportant;

    /** Mask identifying bits of red component */
    uint32_t redMask;
    /** Mask identifying bits of green component */
    uint32_t greenMask;
    /** Mask identifying bits of blue component */
    uint32_t blueMask;
    /** Mask identifying bits of alpha component */
    uint32_t alphaMask;
    /** Color space type */
    uint32_t csType;
    /** X coordinate of red endpoint */
    int32_t  redX;
    /** Y coordinate of red endpoint */
    int32_t  redY;
    /** Z coordinate of red endpoint */
    int32_t  redZ;
    /** X coordinate of green endpoint */
    int32_t  greenX;
    /** Y coordinate of green endpoint */
    int32_t  greenY;
    /** Z coordinate of green endpoint */
    int32_t  greenZ;
    /** X coordinate of blue endpoint */
    int32_t  blueX;
    /** Y coordinate of blue endpoint */
    int32_t  blueY;
    /** Z coordinate of blue endpoint */
    int32_t  blueZ;
    /** Gamma red coordinate scale value */
    uint32_t gammaRed;
    /** Gamma green coordinate scale value */
    uint32_t gammaGreen;
    /** Gamma blue coordinate scale value */
    uint32_t gammaBlue;
}  BMP4Header;

/** BMP (Windows) Header Format */
typedef struct _BMPHeader
{
    /*  signature, must be 4D42 hex */
    uint16_t type;
    /*  size of BMP file in bytes (unreliable) */
    uint32_t fileSize;
    /*  reserved, must be zero */
    uint16_t reserved1;
    /*  reserved, must be zero */
    uint16_t reserved2;
    /*  offset to start of image data in bytes */
    uint32_t offset;
    /*  size of BITMAPINFOHEADER structure, must be 40 */
    uint32_t headerSize;
    /*  image width in pixels */
    uint32_t width;
    /*  image height in pixels */
    uint32_t height;
    /*  number of planes in the image, must be 1 */
    uint16_t planes;
    /*  number of bits per pixel (1, 4, 8, 16, 24, 32) */
    uint16_t bits;
    /*  compression type (0=none, 1=RLE-8, 2=RLE-4) */
    uint32_t compression;
    /*  size of image data in bytes (including padding) */
    uint32_t imageSize;
    /*  horizontal resolution in pixels per meter (unreliable) */
    uint32_t xresolution;
    /*  vertical resolution in pixels per meter (unreliable) */
    uint32_t yresolution;
    /*  number of colors in image, or zero */
    uint32_t ncolours;
    /*  number of important colors, or zero */
    uint32_t importantcolours;

} BMPHeader  ; // GCC

#if defined __ICCARM__ || defined __CC_ARM || defined __GNUC__
#    pragma pack()
#endif

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/

extern uint8_t BMP_IsValid(void *file);

extern uint32_t BMP_GetFileSize(void *file);

extern uint8_t BMP_Decode(
    void *file,
    uint8_t*buffer,
    uint32_t width,
    uint32_t height,
    unsigned char bpp);

extern void WriteBMPheader(uint32_t* pAddressHeader,
                    uint32_t  bmpHSize,
                    uint32_t  bmpVSize,
                    uint8_t bmpRgb,
                    uint8_t nbByte_Pixels);

extern void BMP_displayHeader(uint32_t* pAddressHeader);

extern void RGB565toBGR555(
    uint8_t *fileSource,
    uint8_t *fileDestination,
    uint32_t width,
    uint32_t height,
    uint8_t bpp);

#endif //#ifndef BMP_H

