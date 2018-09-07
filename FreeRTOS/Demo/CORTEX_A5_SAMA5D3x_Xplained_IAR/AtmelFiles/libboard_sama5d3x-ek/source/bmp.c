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

/** \file */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"
#include <string.h>

/*----------------------------------------------------------------------------
 *        Definition
 *----------------------------------------------------------------------------*/

/// BMP offset for header
#define  IMAGE_OFFSET       0x100

/*----------------------------------------------------------------------------
 *        Internal types
 *----------------------------------------------------------------------------*/
/** Describe the BMP palette */
typedef struct _BMPPaletteEntry
{
    /** Blue value */
    uint8_t b;
    /** Green value */
    uint8_t g;
    /** Red value */
    uint8_t r;
    /** Filler character value */
    uint8_t filler;
} BMPPaletteEntry ;

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
/**
 * \brief Test if BMP is valid.
 * \param file  Buffer holding the file to examinate.
 * \return 1 if the header of a BMP file is valid; otherwise returns 0.
 */
uint8_t BMP_IsValid( void *file )
{
    return ((BMPHeader*) file)->type == BMP_TYPE ;
}

/**
 * \brief Returns the size of a BMP image given at least its header (the file does
 * not have to be complete).
 * \param file  Pointer to the buffer which holds the BMP file.
 * \return size of BMP image
 */
uint32_t BMP_GetFileSize( void *file )
{
    return ((BMPHeader *) file)->fileSize ;
}

/**
 * \brief Write a BMP header
 * \param pAddressHeader Begin address of the BMP
 * \param bmpHSize BMP heigth size
 * \param bmpVSize BMP width size
 * \param bmpRgb Type of BMP (YUV or RGB)
 * \param nbByte_Pixels Number of byte per pixels
 */
void WriteBMPheader( uint32_t* pAddressHeader, uint32_t  bmpHSize, uint32_t  bmpVSize, uint8_t bmpRgb, uint8_t nbByte_Pixels )
{
    uint32_t i;
    uint32_t* fill;
    BMPHeader *Header;
    bmpRgb = bmpRgb;

    fill = pAddressHeader;
    for ( i=0 ; i < IMAGE_OFFSET ; i+=4 )
    {
        *fill++ = 0;
    }

    Header = (BMPHeader*) pAddressHeader;

    Header->type = BMP_TYPE;
    Header->fileSize = (bmpHSize * bmpVSize * nbByte_Pixels) + IMAGE_OFFSET;
    Header->reserved1 = 0;
    Header->reserved2 = 0;
    Header->offset = IMAGE_OFFSET;
    Header->headerSize = BITMAPINFOHEADER;
    Header->width  = bmpHSize;
    Header->height = bmpVSize;
    Header->planes = 1;
    Header->bits = nbByte_Pixels * 8;
    Header->compression = 0;
    Header->imageSize = bmpHSize * bmpVSize * nbByte_Pixels;
    Header->xresolution = 0;
    Header->yresolution = 0;
    Header->ncolours = 0;
    Header->importantcolours = 0;
}


/**
 * \brief Debug function, dislay BMP header
 * \param pAddressHeader Address of the BMP
 */
void BMP_displayHeader( uint32_t* pAddressHeader )
{
  #if (TRACE_LEVEL >= TRACE_LEVEL_INFO)
    BMPHeader *header;

    header = (BMPHeader*) pAddressHeader;
    
    TRACE_INFO("BMP\n\r");
    TRACE_INFO("type       0x%X \n\r", header->type);
    TRACE_INFO("fileSize   %ld \n\r", header->fileSize);
    TRACE_INFO("reserved1  %d \n\r", header->reserved1);
    TRACE_INFO("reserved2  %d \n\r", header->reserved2);
    TRACE_INFO("offset     %ld \n\r", header->offset);
    TRACE_INFO("headerSize %ld \n\r", header->headerSize);
    TRACE_INFO("width      %ld \n\r", header->width);
    TRACE_INFO("height     %ld \n\r", header->height);
    TRACE_INFO("planes     %d \n\r", header->planes);
    TRACE_INFO("bits       %d \n\r", header->bits);
    TRACE_INFO("compression %ld \n\r", header->compression);
    TRACE_INFO("imageSize   %ld \n\r", header->imageSize);
    TRACE_INFO("xresolution %ld \n\r", header->xresolution);
    TRACE_INFO("yresolution %ld \n\r", header->yresolution);
    TRACE_INFO("ncolours    %ld \n\r", header->ncolours);
    TRACE_INFO("importantcolours %ld\n\r", header->importantcolours);
  #else
    pAddressHeader = pAddressHeader;
  #endif
}

/**
 * \brief Loads a BMP image located at the given address, decodes it and stores the
 * resulting image inside the provided buffer. Image must have the specified
 * width & height.
 * If no buffer is provided, this function simply checks if it is able to
 * decode the image.
 * \param file  Buffer which holds the BMP file.
 * \param buffer  Buffer in which to store the decoded image.
 * \param width  Buffer width in pixels.
 * \param height  Buffer height in pixels.
 * \param bpp  Number of bits per pixels that the buffer stores.
 * \return 0 if the image has been loaded; otherwise returns an error code.
 */
uint8_t BMP_Decode( void *file, uint8_t *buffer, uint32_t width, uint32_t height, uint8_t bpp )
{
    BMPHeader *header;
    uint32_t i, j;
    uint8_t r, g, b;
    uint8_t *image;

    // Read header information
    header = (BMPHeader*) file;

    // Verify that the file is valid
    if ( !BMP_IsValid( file ) )
    {
        TRACE_ERROR("BMP_Decode: File type is not 'BM' (0x%04X).\n\r",header->type);

        return 1;
    }

    // Check that parameters match
    if ( (header->compression != 0) || (header->width != width) || (header->height != height))
    {
        TRACE_ERROR("BMP_Decode: File format not supported\n\r");
        TRACE_ERROR(" -> .compression = %u\n\r", (unsigned int)header->compression);
        TRACE_ERROR(" -> .width = %u\n\r", (unsigned int)header->width);
        TRACE_ERROR(" -> .height = %u\n\r", (unsigned int)header->height);
        TRACE_ERROR(" -> .bits = %d\n\r", header->bits);

        return 2;
    }

    // Get image data
    image = (uint8_t *) ((uint32_t) file + header->offset);

    // Check that the bpp resolution is supported
    // Only a 24-bit output & 24- or 8-bit input are supported
    if ( bpp != 24 )
    {
        TRACE_ERROR("BMP_Decode: Output resolution not supported\n\r");

        return 3;
    }
    else
    {
        if (header->bits == 24)
        {
            // Decoding is ok
            if (!buffer) return 0;

            // Get image data (swapping red & blue)
            for ( i=0 ; i < height ; i++ )
            {
                for ( j=0 ; j < width; j++ )
                {
                    r = image[((height - i - 1) * width + j) * 3 + 2];
                    g = image[((height - i - 1) * width + j) * 3 + 1];
                    b = image[((height - i - 1) * width + j) * 3];

    #if defined(BOARD_LCD_RGB565)
                    // Interlacing
                    r = ((r << 1) & 0xF0) | ((g & 0x80) >> 4) | ((r & 0x80) >> 5);
                    g = (g << 1) & 0xF8;
                    b = b & 0xF8;

                    buffer[(i * width + j) * 3] = b;
                    buffer[(i * width + j) * 3 + 1] = g;
                    buffer[(i * width + j) * 3 + 2] = r;

    #else
                    buffer[(i * width + j) * 3] = r;
                    buffer[(i * width + j) * 3 + 1] = g;
                    buffer[(i * width + j) * 3 + 2] = b;
    #endif //#if defined(BOARD_LCD_RGB565)
                }
            }
        }
        else
        {
            if ( header->bits == 8 )
            {
                // Decoding is ok
                if (!buffer) return 0;

                // Retrieve palette
                BMPPaletteEntry palette[256];
                memcpy( palette, (uint8_t *) ((uint32_t) file + sizeof( BMPHeader )), header->offset - sizeof( BMPHeader ) ) ;

                // Decode image (reversing row order)
                for ( i=0 ; i < height ; i++ )
                {
                    for (j=0; j < width; j++)
                    {
                        r = palette[image[(height - i - 1) * width + j]].r;
                        g = palette[image[(height - i - 1) * width + j]].g;
                        b = palette[image[(height - i - 1) * width + j]].b;

                        buffer[(i * width + j) * 3] = r;
                        buffer[(i * width + j) * 3 + 1] = g;
                        buffer[(i * width + j) * 3 + 2] = b;
                    }
                }
            }
            else
            {

                TRACE_ERROR("BMP_Decode: Input resolution not supported\n\r");
                TRACE_INFO("header->bits 0x%X \n\r", header->bits);
                return 4 ;
            }
        }
    }

    return 0 ;
}

/**
 * \brief Convert RGB 565 to RGB 555 (RGB 555 is adapted to LCD)
 *
 * \param fileSource  Buffer which holds the RGB file
 * \param fileDestination  Buffer in which to store the decoded image
 * \param width  Buffer width in pixels.
 * \param height  Buffer height in pixels.
 * \param bpp  Number of bits per pixels that the buffer stores.
  */
void RGB565toBGR555( uint8_t *fileSource, uint8_t *fileDestination, uint32_t width, uint32_t height, uint8_t bpp )
{
    uint32_t i;
    uint32_t j;
    uint32_t row;

    for (i=0; i < height*(bpp/8); i++)
    {
        row = (i*width*(bpp/8));

        for (j=0; j <= width*(bpp/8); j+=2)
        {
            fileDestination[row+j] = ((fileSource[row+j+1]>>3)&0x1F)
                                    | (fileSource[row+j]&0xE0);
            fileDestination[row+j+1] = (fileSource[row+j+1]&0x03)
                                    | ((fileSource[row+j]&0x1F)<<2);
        }
    }
}
