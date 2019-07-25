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

#ifndef _YUV_H_
#define _YUV_H_

/*---------------------------------------------------------------------------
 *         Headers
 *---------------------------------------------------------------------------*/


/** Slave address of OMNIVISION chip. */
#define OV_I2C_SENSOR_ADDRESS          (0x42u >> 1)   /* OV7740 -> 0x42 */


/** Register definitions. */
/* -------- OV7740_GAIN : (Address: 0x00) AGC Gain Control LSBs -------- */
#define OV7740_GAIN                    (0x00u)

/* -------- OV7740_BGAIN : (Address: 0x01) AWB - Blue channel gain setting -- */
#define OV7740_BLUE_GAIN               (0x01u)

/* -------- OV7740_RGAIN : (Address: 0x02) AWB - Red channel gain setting --- */
#define OV7740_RED_GAIN                (0x02u)

/* -------- OV7740_GGAIN : (Address: 0x03) AWB - Green channel gain setting - */
#define OV7740_GREEN_GAIN              (0x03u)

/* -------- OV7740_REG04 : (Address: 0x04) Analog setting -------- */
#define OV7740_REG04                   (0x04u)

/* -------- OV7740_BAVG : (Address: 0x05) B Channel Average -------- */
#define OV7740_BLUE_AVG                (0x05u)

/* -------- OV7740_GAVG : (Address: 0x06) G Channel Average -------- */
#define OV7740_GREEN_AVG               (0x06u)

/* -------- OV7740_RAVG : (Address: 0x07) R Channel Average -------- */
#define OV7740_RED_AVG                 (0x07u)

/* -------- OV7740_PIDH : (Address: 0x0a) Product ID number MSB -------- */
#define OV7740_PIDH                    (0x0au)
#define OV7740_PIDH_DEFAULT            (0x77u << 0)

/* -------- OV7740_PIDL : (Address: 0x0b) Product ID number LSB -------- */
#define OV7740_PIDL                    (0x0bu)
#define OV7740_PIDL_DEFAULT            (0x40u << 0)

/* -------- OV7740_REG0C : (Address: 0x0b) -------- */
#define OV7740_REG0C                   (0x0c)
#define OV7740_REG0C_MAX_EXPOSURE_Pos    (1)
 /**< \brief (OV7740_REG0C) Max exposure = frame length - limit x 2 */
#define OV7740_REG0C_MAX_EXPOSURE_Msk    (0x3u << OV7740_REG0C_MAX_EXPOSURE_Pos)
#define OV7740_REG0C_MAX_EXPOSURE(value) \
((OV7740_REG0C_MAX_EXPOSURE_Msk & ((value) << OV7740_REG0C_MAX_EXPOSURE_Pos)))
/**< \brief (OV7740_REG0C) High 8-bit MSB and LSB swap */
#define OV7740_REG0C_BYTE_SWAP_Msk       (0x1u << 3) 
/**< \brief (OV7740_REG0C) output Y9,Y8...Y3,Y2,Y1,Y0 */
#define OV7740_REG0C_BYTE_SWAP_DISABLE   (0x0u << 3) 
/**< \brief (OV7740_REG0C) output Y3,Y2...Y8,Y9,Y1,Y0 */
#define OV7740_REG0C_BYTE_SWAP_ENABLE    (0x1u << 3) 
/**< \brief (OV7740_REG0C) YUV output, Y <-> UV swap */
#define OV7740_REG0C_YUV_SWAP_Msk        (0x1u << 4) 
/**< \brief (OV7740_REG0C) output YUYVYUYV */
#define OV7740_REG0C_YUV_SWAP_DISABLE    (0x0u << 4) 
/**< \brief (OV7740_REG0C) output UYVYUYVY */
#define OV7740_REG0C_YUV_SWAP_ENABLE     (0x1u << 4) 
/**< \brief (OV7740_REG0C) Mirror enable */
#define OV7740_REG0C_MIRROR_ENABLE       (0x1u << 6) 
/**< \brief (OV7740_REG0C) Flip enable */
#define OV7740_REG0C_FLIP_ENABLE         (0x1u << 7) 

/* -------- OV7740_REG0D : (Address: 0x0d) Analog setting -------- */
#define OV7740_REG0D                   (0x0du)

/* -------- OV7740_REG0E : (Address: 0x0e) Analog setting -------- */
/* default value: OV7740_REG0E_BLC_BOTH|OV7740_REG0E_BLC_OPTICAL */
#define OV7740_REG0E                   (0x0eu)
#define OV7740_REG0E_OUTPUT_Pos          (0)
/**< \brief (OV7740_REG0E) Output driving capability */
#define OV7740_REG0E_OUTPUT_Msk          (0x3u << OV7740_REG0E_OUTPUT_Pos)
/**< \brief (OV7740_REG0E) 1x */
#define OV7740_REG0E_OUTPUT_1X           (0x0u << OV7740_REG0E_OUTPUT_Pos)
/**< \brief (OV7740_REG0E) 2x */
#define OV7740_REG0E_OUTPUT_2X           (0x1u << OV7740_REG0E_OUTPUT_Pos)
/**< \brief (OV7740_REG0E) 3x */
#define OV7740_REG0E_OUTPUT_3X           (0x2u << OV7740_REG0E_OUTPUT_Pos)
/**< \brief (OV7740_REG0E) 4x */
#define OV7740_REG0E_OUTPUT_4X          (0x3u << OV7740_REG0E_OUTPUT_Pos)
/**< \brief (OV7740_REG0E) Sleep mode */
#define OV7740_REG0E_SLEEP_MODE          (0x1u << 3) 
#define OV7740_REG0E_BLC_Pos             (5)
/**< \brief (OV7740_REG0E) BLC line selection */
#define OV7740_REG0E_BLC_Msk             (0x3u << OV7740_REG0E_BLC_Pos)
/**< \brief (OV7740_REG0E) Select both blue line and red line as BLC line. */
#define OV7740_REG0E_BLC_BOTH0           (0x0u << OV7740_REG0E_BLC_Pos)
/**< \brief (OV7740_REG0E) Select red line as BLC line. */
#define OV7740_REG0E_BLC_RED             (0x1u << OV7740_REG0E_BLC_Pos)
/**< \brief (OV7740_REG0E) Select blue line as BLC line. */
#define OV7740_REG0E_BLC_BLUE            (0x2u << OV7740_REG0E_BLC_Pos)
/**< \brief (OV7740_REG0E) Select both blue line and red line as BLC line. */
#define OV7740_REG0E_BLC_BOTH            (0x3u << OV7740_REG0E_BLC_Pos)
/**< \brief (OV7740_REG0E) BLC line selection */
#define OV7740_REG0E_BLC_LINE_Msk        (0x1u << 7)
/**< \brief (OV7740_REG0E) Electrical BLC */
#define OV7740_REG0E_BLC_LINE_ELECTRICAL (0x0u << 7)
/**< \brief (OV7740_REG0E) Optical BLC */
#define OV7740_REG0E_BLC_LINE_OPTICAL    (0x1u << 7)

/* ----- OV7740_HAEC : (Address: 0x0f) Automatic exposure control bit [15:8] - */
#define OV7740_HAEC                    (0x0fu)

/* -------- OV7740_AEC : (Address: 0x10) Automatic exposure control bit [7:0]- */
#define OV7740_AEC                     (0x10u)

/* -------- OV7740_CLK : (Address: 0x11) Clock settings -------- */
/**< \brief (OV7740_CLK) sysclk=XVCLK1 x PLLDIV / [(CLK[5:0]+1) x2 xPreDiv] */
#define OV7740_CLK                     (0x11u) 
#define OV7740_CLK_DIVIDER_Pos           (0)
/**< \brief (OV7740_CLK) Clock divider */
#define OV7740_CLK_DIVIDER_Msk           (0x3fu << OV7740_CLK_DIVIDER_Pos) 
#define OV7740_CLK_DIVIDER(value) \
		((OV7740_CLK_DIVIDER_Msk & ((value) << OV7740_CLK_DIVIDER_Pos)))
#define OV7740_CLK_PLL_Pos               (6)
/**< \brief (OV7740_CLK) PLL setting - Changing this value is not recommended */
#define OV7740_CLK_PLL_Msk               (0x3u << OV7740_CLK_PLL_Pos) 
#define OV7740_CLK_PLL(value) \
		((OV7740_CLK_PLL_Msk & ((value) << OV7740_CLK_PLL_Pos)))

#define FRAME_RATE_60           0x00
#define FRAME_RATE_30           0x01
#define FRAME_RATE_20           0x02
#define FRAME_RATE_15           0x03
#define FRAME_RATE_10           0x05
#define FRAME_RATE_7            0x07
#define PLL_DIV_DEFAULT         0x40
#define FRAME_RATE_7_MCK_132    0x0A
#define PLL_DIV_7_MCK_132       0xC0

/* -------- OV7740_REG12 : (Address: 0x12) -------- */
#define OV7740_REG12                   (0x12u)
#define OV7740_REG12_RAW_RGB             (0x1u << 0)
#define OV7740_REG12_SENSOR_RAW          (0x1u << 4)
#define OV7740_REG12_CC656_MODE          (0x1u << 5)
#define OV7740_REG12_VSKIP               (0x1u << 6)
#define OV7740_REG12_RESET               (0x1u << 7)

/* -------- OV7740_REG13 : (Address: 0x13) -------- */
#define OV7740_REG13                   (0x13u)
/**< \brief (OV7740_REG13) Exposure auto/manual control selection */
#define OV7740_REG13_EXPOSURE_Msk        (0x01u << 0) 
#define OV7740_REG13_EXPOSURE_MANUAL     (0x0u << 0)
#define OV7740_REG13_EXPOSURE_AUTO       (0x1u << 0)
/**< \brief (OV7740_REG13) Auto white balance control selection */
#define OV7740_REG13_WBAL_Msk            (0x1u << 1) 
#define OV7740_REG13_WBAL_MANUAL         (0x0u << 1)
#define OV7740_REG13_WBAL_AUTO           (0x1u << 1)
/**< \brief (OV7740_REG13) AGC auto/manual control selection */
#define OV7740_REG13_AGC_Msk             (0x1u << 2) 
#define OV7740_REG13_AGC_MANUAL          (0x0u << 2)
#define OV7740_REG13_AGC_AUTO            (0x1u << 2)
/**< \brief (OV7740_REG13) LAEC enable */
#define OV7740_REG13_LAEC_Msk            (0x1u << 3) 
#define OV7740_REG13_LAEC_DISABLE        (0x0u << 3)
#define OV7740_REG13_LAEC_ENABLE         (0x1u << 3)
 /**< \brief (OV7740_REG13) Banding option */
#define OV7740_REG13_BANDING_OPT_Msk     (0x1u << 4)
/**< \brief (OV7740_REG13) Minimum exposure is limited to 1/120 or 1/100 second 
 when banding filter is enabled */
#define OV7740_REG13_BANDING_OPT_LIMITED (0x0u << 4)
/**< \brief (OV7740_REG13) Minimum exposure is allowed to be less than 1/120 or
 1/100 second when banding filter is enabled */
#define OV7740_REG13_BANDING_OPT_ENABLE  (0x1u << 4)
/**< \brief (OV7740_REG13) Banding enable */
#define OV7740_REG13_BANDING_Mask        (0x1u << 5) 
#define OV7740_REG13_BANDING_DISABLE     (0x0u << 5)
#define OV7740_REG13_BANDING_ENABLE      (0x1u << 5)
/**< \brief (OV7740_REG13) Enable frame drop function */
#define OV7740_REG13_FRAME_DROP_Mask     (0x1u << 6) 
#define OV7740_REG13_FRAME_DROP_DISABLE  (0x0u << 6)
#define OV7740_REG13_FRAME_DROP_ENABLE   (0x1u << 6)
/**< \brief (OV7740_REG13) AEC speed selection */
#define OV7740_REG13_AEC_Mask            (0x1u << 7)
/**< \brief (OV7740_REG13) Normal */
#define OV7740_REG13_AEC_NORMAL          (0x0u << 7)
/**< \brief (OV7740_REG13) Faster AEC correction */
#define OV7740_REG13_AEC_FASTER          (0x1u << 7) 

/* -------- OV7740_REG14 : (Address: 0x14) -------- */
#define OV7740_REG14                   (0x14u)

/* -------- OV7740_REG15 : (Address: 0x15) -------- */
#define OV7740_REG15                   (0x15u)
#define OV7740_REG15_GAIN_Pos          (0)
/**< \brief (OV7740_REG15) AGC MSBs (digital gain) (LSBs in GAIN[7:0]) */
#define OV7740_REG15_GAIN_Msk          (0x3u << OV7740_REG15_GAIN_Pos) 
#define OV7740_REG15_GAIN(value) \
		((OV7740_REG15_GAIN_Msk & ((value) << OV7740_REG15_GAIN_Pos)))
/**< \brief (OV7740_REG15) Night mode triggering point */
#define OV7740_REG15_NIGHT_Mask        (0x3u << 2) 
/**< \brief (OV7740_REG15) 2x gain */
#define OV7740_REG15_NIGHT_2X_GAIN     (0x0u << 2) 
/**< \brief (OV7740_REG15) 4x gain */
#define OV7740_REG15_NIGHT_4X_GAIN     (0x1u << 2) 
/**< \brief (OV7740_REG15) 8x gain */
#define OV7740_REG15_NIGHT_8X_GAIN     (0x2u << 2)
/**< \brief (OV7740_REG15) 16x gain */
#define OV7740_REG15_NIGHT_16X_GAIN    (0x3u << 2)
/**< \brief (OV7740_REG15) Ceiling of inserting frames */
#define OV7740_REG15_CEIL_Mask         (0x3u << 4)
/**< \brief (OV7740_REG15) Up to 0 frames */
#define OV7740_REG15_CEIL_0            (0x0u << 4)
/**< \brief (OV7740_REG15) Up to 1 frames */
#define OV7740_REG15_CEIL_1            (0x1u << 4)
/**< \brief (OV7740_REG15) Up to 2 frames */
#define OV7740_REG15_CEIL_2            (0x2u << 4)
/**< \brief (OV7740_REG15) Up to 3 frames */
#define OV7740_REG15_CEIL_3            (0x3u << 4)
/**< \brief (OV7740_REG15) Up to 7 frames */
#define OV7740_REG15_CEIL_7            (0x7u << 4)
/**< \brief (OV7740_REG15) Enable inserting frames in night mode */
#define OV7740_REG15_ENABLE_NIGHT      (0x1u << 7)  

/*   OV7740_REG16 : (Address: 0x16)   */
#define OV7740_REG16                   (0x16u)

/*
 * OV7740_AHSTART : (Address: 0x17) Sensor Horizontal output start point
 * 8 MSBs (LSBs in REG16[1:0])
 */
#define OV7740_AHSTART                 (0x17u)

/* 
 * OV7740_AHSIZE : (Address: 0x18) Sensor Horizontal output size 8 MSBs 
 * (LSBs in REG16[4:3])
 */
#define OV7740_AHSIZE                  (0x18u)

/* 
 * OV7740_AVSTART : (Address: 0x19) Sensor Vertical output start point 8 MSBs 
 * (LSBs in REG16[2])
 */
#define OV7740_AVSTART                 (0x19u)

/* 
 * OV7740_AVSIZE : (Address: 0x1a) Sensor Vertical output size 8 MSBs 
 * (LSBs in REG16[5])
 */
#define OV7740_AVSIZE                  (0x1au)

/* -------- OV7740_PIXEL_SHIFT : (Address: 0x1b) Pixel shift -------- */
#define OV7740_PIXEL_SHIFT             (0x1bu)

/* -------- OV7740_MIDH : (Address: 0x1c) Manufacturer ID Byte - High ------- */
#define OV7740_MIDH                    (0x1cu)
#define OV7740_MIDH_DEFAULT              (0x7fu << 0)

/* -------- OV7740_MIDL : (Address: 0x1d) Manufacturer ID Byte - Low -------- */
#define OV7740_MIDL                    (0x1du)
#define OV7740_MIDL_DEFAULT              (0xa2u << 0)

/* -------- OV7740_REG1E : (Address: 0x1e) -------- */
#define OV7740_REG1E                   (0x1eu)

/* -------- OV7740_REG1F : (Address: 0x1f) -------- */
#define OV7740_REG1F                   (0x1fu)

/* -------- OV7740_REG1E : (Address: 0x1e) -------- */
#define OV7740_REG1E                   (0x1eu)

/* -------- OV7740_REG20 : (Address: 0x20) -------- */
#define OV7740_REG20                   (0x20u)

/* -------- OV7740_REG21 : (Address: 0x21) -------- */
#define OV7740_REG21                   (0x21u)

/*  OV7740_REG21 : (Address: 0x24) Luminance signal high range for AEC/AGC 
 * operation.
 */
#define OV7740_WPT                     (0x24u)

/*
 * OV7740_REG21 : (Address: 0x25) Luminance signal low range for AEC/AGC 
 * operation 
 */
#define OV7740_BPT                     (0x25u)

/* ---  OV7740_VPT : (Address: 0x26) effective only in AEG/AGC fast mode ---- */
#define OV7740_VPT                     (0x26u)

/* -------- OV7740_REG27 : (Address: 0x27) -------- */
#define OV7740_REG27                   (0x27u)
/**< \brief (OV7740_REG27) Black sun cancellation enable */
#define OV7740_REG27_BLACKSUN            (0x1u << 7) 

/* -------- OV7740_REG28 : (Address: 0x28) -------- */
#define OV7740_REG28                   (0x28u)
/**< \brief (OV7740_REG28) VSYNC polarity */
#define OV7740_REG28_VSYNC_Msk           (0x1u << 1)
/**< \brief (OV7740_REG28) Positive */
#define OV7740_REG28_VSYNC_POSITIVE      (0x1u << 0)
/**< \brief (OV7740_REG28) Negative */
#define OV7740_REG28_VSYNC_NEGATIVE      (0x1u << 1)
/**< \brief (OV7740_REG28) No VSYNC output option */
#define OV7740_REG28_VSYNC_OUTPUT_Msk    (0x1u << 3)
/**< \brief (OV7740_REG28) Still output VSYNC when frame drop */
#define OV7740_REG28_VSYNC_OUTPUT_STILL  (0x0u << 3)
/**< \brief (OV7740_REG28) No VSYNC output when frame drop */
#define OV7740_REG28_VSYNC_OUTPUT_NONE   (0x1u << 3)
/**< \brief (OV7740_REG28) HREF polarity */
#define OV7740_REG28_HREF_Msk            (0x1u << 4)
/**< \brief (OV7740_REG28) Output positive HREF */
#define OV7740_REG28_HREF_POSITIVE       (0x0u << 4)
 /**< \brief (OV7740_REG28) Output negative HREF for data valid */
#define OV7740_REG28_HREF_NEGATIVE       (0x1u << 4)
/**< \brief (OV7740_REG28) HSYNC polarity */
#define OV7740_REG28_HSYNC_Msk           (0x1u << 5)
/**< \brief (OV7740_REG28) Positive */
#define OV7740_REG28_HSYNC_POSITIVE      (0x0u << 5)
/**< \brief (OV7740_REG28) Negative */
#define OV7740_REG28_HSYNC_NEGATIVE      (0x1u << 5)
/**< \brief (OV7740_REG28) HREF pin output swap */
#define OV7740_REG28_HREF_OUTPUT_Msk     (0x1u << 6)
/**< \brief (OV7740_REG28) HREF */
#define OV7740_REG28_HREF_OUTPUT_HREF    (0x0u << 6)
/**< \brief (OV7740_REG28) HSYNC */
#define OV7740_REG28_HREF_OUTPUT_HSYNC   (0x1u << 6)
/**< \brief (OV7740_REG28) Output data bit reverse option */
#define OV7740_REG28_OUTPUT_REVERSE      (0x1u << 7) 

/* -------- OV7740_REG65 : (Address: 0x65) -------- */
#define OV7740_REG65                  (0x65u)
/**< \brief (OV7740_REG65) Output data bit swap option */
#define OV7740_REG65_BIT_SWAP_Msk       (0x1u << 3)
 /**< \brief (OV7740_REG65) Output DATA[9:0] */
#define OV7740_REG65_BIT_SWAP_NORMAL    (0x0u << 3)
/**< \brief (OV7740_REG65) Output DATA[0:9] */
#define OV7740_REG65_BIT_SWAP_REVERSE   (0x1u << 3) 

/* -------- OV7740_YUV422CTRL : (Address: 0xd9) -------- */
#define OV7740_YUV422CTRL             (0xd9u)
 /**< \brief (OV7740_YUV422CTRL) cnv_opt */
#define OV7740_YUV422CTRL_CNV_OPT_Msk   (0x1u << 0)
/**< \brief (OV7740_YUV422CTRL) Average mode */
#define OV7740_YUV422CTRL_CNV_OPT_AVERAGE (0x0u << 0)
/**< \brief (OV7740_YUV422CTRL) Drop mode */
#define OV7740_YUV422CTRL_CNV_OPT_DROP    (0x1u << 0)

/**< \brief (OV7740_YUV422CTRL) v_first */
#define OV7740_YUV422CTRL_V_FIRST_Msk   (0x1u << 1)
/**< \brief (OV7740_YUV422CTRL) Output line will be YUYV... */
#define OV7740_YUV422CTRL_V_FIRST_YUYV  (0x0u << 1)
/**< \brief (OV7740_YUV422CTRL) Output line will be YVYU... (it will affect 
definition of U/V in SDE. If it is set, all registers in SDE about U/V must be 
swapped */
#define OV7740_YUV422CTRL_V_FIRST_YVYU  (0x1u << 1) 



#endif // #ifndef _YUV_H_

