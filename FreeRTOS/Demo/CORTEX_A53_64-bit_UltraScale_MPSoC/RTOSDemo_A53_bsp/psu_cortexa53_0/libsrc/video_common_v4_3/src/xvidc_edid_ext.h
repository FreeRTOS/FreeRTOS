/* vim: set et fde fdm=syntax ft=c.doxygen ts=4 sts=4 sw=4 : */
/*
 * Copyright © 2010-2011 Saleem Abdulrasool <compnerd@compnerd.org>.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO
 * EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#ifndef xvidc_edid_h
#define xvidc_edid_h

#include "stdbool.h"
#include "xvidc.h"
#include "xil_assert.h"
#include "xvidc_cea861.h"

#define XVIDC_EDID_BLOCK_SIZE                         (0x80)
#define XVIDC_EDID_MAX_EXTENSIONS                     (0xFE)


static const u8 XVIDC_EDID_EXT_HEADER[] =
                            { 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00 };
static const u8 XVIDC_EDID_STANDARD_TIMING_DESCRIPTOR_INVALID[] =
                                                                { 0x01, 0x01 };

enum xvidc_edid_extension_type {
    XVIDC_EDID_EXTENSION_TIMING           = 0x01, /* Timing Extension */
    XVIDC_EDID_EXTENSION_CEA              = 0x02, /* Additional Timing Block
                                             Data (CEA EDID Timing Extension)*/
    XVIDC_EDID_EXTENSION_VTB              = 0x10, /* Video Timing Block
                                                          Extension (VTB-EXT)*/
    XVIDC_EDID_EXTENSION_XVIDC_EDID_2_0= 0x20, /* EDID 2.0 Extension  */
    XVIDC_EDID_EXTENSION_DI               = 0x40, /* Display Information
                                                          Extension (DI-EXT) */
    XVIDC_EDID_EXTENSION_LS               = 0x50, /* Localised String
                                                          Extension (LS-EXT) */
    XVIDC_EDID_EXTENSION_MI               = 0x60, /* Microdisplay Interface
                                                          Extension (MI-EXT) */
    XVIDC_EDID_EXTENSION_DTCDB_1          = 0xA7, /* Display Transfer
                                          Characteristics Data Block (DTCDB) */
    XVIDC_EDID_EXTENSION_DTCDB_2          = 0xAF,
    XVIDC_EDID_EXTENSION_DTCDB_3          = 0xBF,
    XVIDC_EDID_EXTENSION_BLOCK_MAP        = 0xF0, /* Block Map*/
    XVIDC_EDID_EXTENSION_DDDB             = 0xFF, /* Display Device Data
                                                                 Block (DDDB)*/
};

enum xvidc_edid_display_type {
    XVIDC_EDID_DISPLAY_TYPE_MONOCHROME,
    XVIDC_EDID_DISPLAY_TYPE_RGB,
    XVIDC_EDID_DISPLAY_TYPE_NON_RGB,
    XVIDC_EDID_DISPLAY_TYPE_UNDEFINED,
};

enum xvidc_edid_aspect_ratio {
    XVIDC_EDID_ASPECT_RATIO_16_10,
    XVIDC_EDID_ASPECT_RATIO_4_3,
    XVIDC_EDID_ASPECT_RATIO_5_4,
    XVIDC_EDID_ASPECT_RATIO_16_9,
};

enum xvidc_edid_signal_sync {
    XVIDC_EDID_SIGNAL_SYNC_ANALOG_COMPOSITE,
    XVIDC_EDID_SIGNAL_SYNC_BIPOLAR_ANALOG_COMPOSITE,
    XVIDC_EDID_SIGNAL_SYNC_DIGITAL_COMPOSITE,
    XVIDC_EDID_SIGNAL_SYNC_DIGITAL_SEPARATE,
};

enum xvidc_edid_stereo_mode {
    XVIDC_EDID_STEREO_MODE_NONE,
    XVIDC_EDID_STEREO_MODE_RESERVED,
    XVIDC_EDID_STEREO_MODE_FIELD_SEQUENTIAL_RIGHT,
    XVIDC_EDID_STEREO_MODE_2_WAY_INTERLEAVED_RIGHT,
    XVIDC_EDID_STEREO_MODE_FIELD_SEQUENTIAL_LEFT,
    XVIDC_EDID_STEREO_MODE_2_WAY_INTERLEAVED_LEFT,
    XVIDC_EDID_STEREO_MODE_4_WAY_INTERLEAVED,
    XVIDC_EDID_STEREO_MODE_SIDE_BY_SIDE_INTERLEAVED,
};

enum xvidc_edid_monitor_descriptor_type {
    XVIDC_EDID_MONTIOR_DESCRIPTOR_MANUFACTURER_DEFINED        = 0x0F,
    XVIDC_EDID_MONITOR_DESCRIPTOR_STANDARD_TIMING_IDENTIFIERS = 0xFA,
    XVIDC_EDID_MONITOR_DESCRIPTOR_COLOR_POINT                 = 0xFB,
    XVIDC_EDID_MONITOR_DESCRIPTOR_MONITOR_NAME                = 0xFC,
    XVIDC_EDID_MONITOR_DESCRIPTOR_MONITOR_RANGE_LIMITS        = 0xFD,
    XVIDC_EDID_MONITOR_DESCRIPTOR_ASCII_STRING                = 0xFE,
    XVIDC_EDID_MONITOR_DESCRIPTOR_MONITOR_SERIAL_NUMBER       = 0xFF,
};

enum xvidc_edid_secondary_timing_support {
    XVIDC_EDID_SECONDARY_TIMING_NOT_SUPPORTED,
    XVIDC_EDID_SECONDARY_TIMING_GFT           = 0x02,
};


struct __attribute__ (( packed )) xvidc_edid_detailed_timing_descriptor {
    u16 pixel_clock;                               /* = value * 10000 */

    u8  horizontal_active_lo;
    u8  horizontal_blanking_lo;

    unsigned horizontal_blanking_hi         : 4;
    unsigned horizontal_active_hi           : 4;

    u8  vertical_active_lo;
    u8  vertical_blanking_lo;

    unsigned vertical_blanking_hi           : 4;
    unsigned vertical_active_hi             : 4;

    u8  horizontal_sync_offset_lo;
    u8  horizontal_sync_pulse_width_lo;

    unsigned vertical_sync_pulse_width_lo   : 4;
    unsigned vertical_sync_offset_lo        : 4;

    unsigned vertical_sync_pulse_width_hi   : 2;
    unsigned vertical_sync_offset_hi        : 2;
    unsigned horizontal_sync_pulse_width_hi : 2;
    unsigned horizontal_sync_offset_hi      : 2;

    u8  horizontal_image_size_lo;
    u8  vertical_image_size_lo;

    unsigned vertical_image_size_hi         : 4;
    unsigned horizontal_image_size_hi       : 4;

    u8  horizontal_border;
    u8  vertical_border;

    unsigned stereo_mode_lo                 : 1;
    unsigned signal_pulse_polarity          : 1; /* pulse on sync,
                                               composite/horizontal polarity */
    unsigned signal_serration_polarity      : 1; /* serrate on sync, vertical
                                                                    polarity */
    unsigned signal_sync                    : 2;
    unsigned stereo_mode_hi                 : 2;
    unsigned interlaced                     : 1;
};

static inline u32
xvidc_edid_detailed_timing_pixel_clock
            (const struct xvidc_edid_detailed_timing_descriptor * const dtb)
{
    return dtb->pixel_clock * 10000;
}

static inline u16
xvidc_edid_detailed_timing_horizontal_blanking
            (const struct xvidc_edid_detailed_timing_descriptor * const dtb)
{
    return (dtb->horizontal_blanking_hi << 8) | dtb->horizontal_blanking_lo;
}

static inline u16
xvidc_edid_detailed_timing_horizontal_active
            (const struct xvidc_edid_detailed_timing_descriptor * const dtb)
{
    return (dtb->horizontal_active_hi << 8) | dtb->horizontal_active_lo;
}

static inline u16
xvidc_edid_detailed_timing_vertical_blanking
            (const struct xvidc_edid_detailed_timing_descriptor * const dtb)
{
    return (dtb->vertical_blanking_hi << 8) | dtb->vertical_blanking_lo;
}

static inline u16
xvidc_edid_detailed_timing_vertical_active
            (const struct xvidc_edid_detailed_timing_descriptor * const dtb)
{
    return (dtb->vertical_active_hi << 8) | dtb->vertical_active_lo;
}

static inline u8
xvidc_edid_detailed_timing_vertical_sync_offset
            (const struct xvidc_edid_detailed_timing_descriptor * const dtb)
{
    return (dtb->vertical_sync_offset_hi << 4) | dtb->vertical_sync_offset_lo;
}

static inline u8
xvidc_edid_detailed_timing_vertical_sync_pulse_width
            (const struct xvidc_edid_detailed_timing_descriptor * const dtb)
{
    return (dtb->vertical_sync_pulse_width_hi << 4) |
                                             dtb->vertical_sync_pulse_width_lo;
}

static inline u8
xvidc_edid_detailed_timing_horizontal_sync_offset
            (const struct xvidc_edid_detailed_timing_descriptor * const dtb)
{
    return (dtb->horizontal_sync_offset_hi << 4) |
                                                dtb->horizontal_sync_offset_lo;
}

static inline u8
xvidc_edid_detailed_timing_horizontal_sync_pulse_width
            (const struct xvidc_edid_detailed_timing_descriptor * const dtb)
{
    return (dtb->horizontal_sync_pulse_width_hi << 4) |
                                           dtb->horizontal_sync_pulse_width_lo;
}

static inline u16
xvidc_edid_detailed_timing_horizontal_image_size
            (const struct xvidc_edid_detailed_timing_descriptor * const dtb)
{
    return
          (dtb->horizontal_image_size_hi << 8) | dtb->horizontal_image_size_lo;
}

static inline u16
xvidc_edid_detailed_timing_vertical_image_size
            (const struct xvidc_edid_detailed_timing_descriptor * const dtb)
{
    return (dtb->vertical_image_size_hi << 8) | dtb->vertical_image_size_lo;
}

static inline u8
xvidc_edid_detailed_timing_stereo_mode
            (const struct xvidc_edid_detailed_timing_descriptor * const dtb)
{
    return (dtb->stereo_mode_hi << 2 | dtb->stereo_mode_lo);
}


struct __attribute__ (( packed )) xvidc_edid_monitor_descriptor {
    u16 flag0;
    u8  flag1;
    u8  tag;
    u8  flag2;
    u8  data[13];
};

typedef char xvidc_edid_monitor_descriptor_string
            [sizeof(((struct xvidc_edid_monitor_descriptor *)0)->data) + 1];


struct __attribute__ (( packed )) xvidc_edid_monitor_range_limits {
    u8  minimum_vertical_rate;             /* Hz */
    u8  maximum_vertical_rate;             /* Hz */
    u8  minimum_horizontal_rate;           /* kHz */
    u8  maximum_horizontal_rate;           /* kHz */
    u8  maximum_supported_pixel_clock;     /* = (value * 10) Mhz
                                                   (round to 10 MHz) */

    /* secondary timing formula */
    u8  secondary_timing_support;
    u8  reserved;
    u8  secondary_curve_start_frequency;   /* horizontal frequency / 2 kHz */
    u8  c;                                 /* = (value >> 1) */
    u16 m;
    u8  k;
    u8  j;                                 /* = (value >> 1) */
};


struct __attribute__ (( packed )) xvidc_edid_standard_timing_descriptor {
    u8  horizontal_active_pixels;         /* = (value + 31) * 8 */

    unsigned refresh_rate       : 6;           /* = value + 60 */
    unsigned image_aspect_ratio : 2;
};

inline u32
xvidc_edid_standard_timing_horizontal_active
(const struct xvidc_edid_standard_timing_descriptor * const desc) {
    return ((desc->horizontal_active_pixels + 31) << 3);
}

inline u32
xvidc_edid_standard_timing_vertical_active
(const struct xvidc_edid_standard_timing_descriptor * const desc) {
    const u32 hres = xvidc_edid_standard_timing_horizontal_active(desc);

    switch (desc->image_aspect_ratio) {
    case XVIDC_EDID_ASPECT_RATIO_16_10:
        return ((hres * 10) >> 4);
    case XVIDC_EDID_ASPECT_RATIO_4_3:
        return ((hres * 3) >> 2);
    case XVIDC_EDID_ASPECT_RATIO_5_4:
        return ((hres << 2) / 5);
    case XVIDC_EDID_ASPECT_RATIO_16_9:
        return ((hres * 9) >> 4);
    }

    return hres;
}

inline u32
xvidc_edid_standard_timing_refresh_rate
(const struct xvidc_edid_standard_timing_descriptor * const desc) {
    return (desc->refresh_rate + 60);
}


struct __attribute__ (( packed )) edid {
    /* header information */
    u8  header[8];

    /* vendor/product identification */
    u16 manufacturer;
    union {
        u16 product_u16;
        u8  product[2];
    };
    union {
        u32 serial_number_u32;
        u8  serial_number[4];
    };
    u8  manufacture_week;
    u8  manufacture_year;                  /* = value + 1990 */

    /* EDID version */
    u8  version;
    u8  revision;

    /* basic display parameters and features */
    union {
        struct __attribute__ (( packed )) {
            unsigned dfp_1x                 : 1;    /* VESA DFP 1.x */
            unsigned                        : 6;
            unsigned digital                : 1;
        } digital;
        struct __attribute__ (( packed )) {
            unsigned vsync_serration        : 1;
            unsigned green_video_sync       : 1;
            unsigned composite_sync         : 1;
            unsigned separate_sync          : 1;
            unsigned blank_to_black_setup   : 1;
            unsigned signal_level_standard  : 2;
            unsigned digital                : 1;
        } analog;
    } video_input_definition;

    u8  maximum_horizontal_image_size;     /* cm */
    u8  maximum_vertical_image_size;       /* cm */

    u8  display_transfer_characteristics;  /* gamma = (value + 100) / 100 */

    struct __attribute__ (( packed )) {
        unsigned default_gtf                    : 1; /* generalised timing
                                                     formula */
        unsigned preferred_timing_mode          : 1;
        unsigned standard_default_color_space   : 1;
        unsigned display_type                   : 2;
        unsigned active_off                     : 1;
        unsigned suspend                        : 1;
        unsigned standby                        : 1;
    } feature_support;

    /* color characteristics block */
    unsigned green_y_low    : 2;
    unsigned green_x_low    : 2;
    unsigned red_y_low      : 2;
    unsigned red_x_low      : 2;

    unsigned white_y_low    : 2;
    unsigned white_x_low    : 2;
    unsigned blue_y_low     : 2;
    unsigned blue_x_low     : 2;

    u8  red_x;
    u8  red_y;
    u8  green_x;
    u8  green_y;
    u8  blue_x;
    u8  blue_y;
    u8  white_x;
    u8  white_y;

    /* established timings */
    struct __attribute__ (( packed )) {
        unsigned timing_800x600_60   : 1;
        unsigned timing_800x600_56   : 1;
        unsigned timing_640x480_75   : 1;
        unsigned timing_640x480_72   : 1;
        unsigned timing_640x480_67   : 1;
        unsigned timing_640x480_60   : 1;
        unsigned timing_720x400_88   : 1;
        unsigned timing_720x400_70   : 1;

        unsigned timing_1280x1024_75 : 1;
        unsigned timing_1024x768_75  : 1;
        unsigned timing_1024x768_70  : 1;
        unsigned timing_1024x768_60  : 1;
        unsigned timing_1024x768_87  : 1;
        unsigned timing_832x624_75   : 1;
        unsigned timing_800x600_75   : 1;
        unsigned timing_800x600_72   : 1;
    } established_timings;

    struct __attribute__ (( packed )) {
        unsigned reserved            : 7;
        unsigned timing_1152x870_75  : 1;
    } manufacturer_timings;

    /* standard timing id */
    struct  xvidc_edid_standard_timing_descriptor standard_timing_id[8];

    /* detailed timing */
    union {
        struct xvidc_edid_monitor_descriptor         monitor;
        struct xvidc_edid_detailed_timing_descriptor timing;
    } detailed_timings[4];

    u8  extensions;
    u8  checksum;
};

static inline void
xvidc_edid_manufacturer(const struct edid * const edid, char manufacturer[4])
{
    manufacturer[0] = '@' + ((edid->manufacturer & 0x007c) >> 2);
    manufacturer[1] = '@' + ((((edid->manufacturer & 0x0003) >> 00) << 3) | (((edid->manufacturer & 0xe000) >> 13) << 0));
    manufacturer[2] = '@' + ((edid->manufacturer & 0x1f00) >> 8);
    manufacturer[3] = '\0';
}

static inline double
xvidc_edid_gamma(const struct edid * const edid)
{
    return (edid->display_transfer_characteristics + 100) / 100.0;
}

static inline bool
xvidc_edid_detailed_timing_is_monitor_descriptor(const struct edid * const edid,
                                           const u8 timing)
{
    const struct xvidc_edid_monitor_descriptor * const mon =
        &edid->detailed_timings[timing].monitor;

    Xil_AssertNonvoid(timing < ARRAY_SIZE(edid->detailed_timings));

    return mon->flag0 == 0x0000 && mon->flag1 == 0x00 && mon->flag2 == 0x00;
}


struct __attribute__ (( packed )) xvidc_edid_color_characteristics_data {
    struct {
        u16 x;
        u16 y;
    } red, green, blue, white;
};

static inline struct xvidc_edid_color_characteristics_data
xvidc_edid_color_characteristics(const struct edid * const edid)
{
    const struct xvidc_edid_color_characteristics_data characteristics = {
        .red = {
            .x = (edid->red_x << 2) | edid->red_x_low,
            .y = (edid->red_y << 2) | edid->red_y_low,
        },
        .green = {
            .x = (edid->green_x << 2) | edid->green_x_low,
            .y = (edid->green_y << 2) | edid->green_y_low,
        },
        .blue = {
            .x = (edid->blue_x << 2) | edid->blue_x_low,
            .y = (edid->blue_y << 2) | edid->blue_y_low,
        },
        .white = {
            .x = (edid->white_x << 2) | edid->white_x_low,
            .y = (edid->white_y << 2) | edid->white_y_low,
        },
    };

    return characteristics;
}


struct __attribute__ (( packed )) xvidc_edid_block_map {
    u8 tag;
    u8 extension_tag[126];
    u8 checksum;
};


struct __attribute__ (( packed )) xvidc_edid_extension {
    u8 tag;
    u8 revision;
    u8 extension_data[125];
    u8 checksum;
};


static inline bool
xvidc_edid_verify_checksum(const u8 * const block)
{
    u8 checksum = 0;
    int i;

    for (i = 0; i < XVIDC_EDID_BLOCK_SIZE; i++)
        checksum += block[i];

    return (checksum == 0);
}

static inline double
xvidc_edid_decode_fixed_point(u16 value)
{
    double result = 0.0;

    Xil_AssertNonvoid((~value & 0xfc00) == 0xfc00);
                                                 /* edid fraction is 10 bits */

    for (u8 i = 0; value && (i < 10); i++, value >>= 1)
        result = result + ((value & 0x1) * (1.0 / (1 << (10 - i))));

    return result;
}

typedef enum {
    XVIDC_VERBOSE_DISABLE,
    XVIDC_VERBOSE_ENABLE
} XV_VidC_Verbose;

typedef enum {
    XVIDC_ISDVI,
    XVIDC_ISHDMI
} XV_VidC_IsHdmi;

typedef enum {
    XVIDC_NOT_SUPPORTED,
    XVIDC_SUPPORTED
} XV_VidC_Supp;
#if XVIDC_EDID_VERBOSITY > 1
typedef struct {
	u32 Integer;
	u32 Decimal;
} XV_VidC_DoubleRep;
#endif

typedef struct {
    u8 width;
    u8 height;
} XV_VidC_PicAspectRatio;

typedef struct {
    u16 hres;
    u16 vres;
    u16 htotal;
    u16 vtotal;
    XVidC_VideoFormat vidfrmt;
    u32 pixclk;
    u16 hsync_width;
    u16 vsync_width;
    u16 hfp;
    u16 vfp;
    u8 vfreq;
    XV_VidC_PicAspectRatio aspect_ratio;
    unsigned hsync_polarity : 1;
    unsigned vsync_polarity : 1;
} XV_VidC_TimingParam;

typedef struct {
	/*Checks whether Sink able to support HDMI*/
	XV_VidC_IsHdmi IsHdmi;
	/*Color Space Support*/
    XV_VidC_Supp   IsYCbCr444Supp;
    XV_VidC_Supp   IsYCbCr420Supp;
    XV_VidC_Supp   IsYCbCr422Supp;
	/*YCbCr444/YCbCr422/RGB444 Deep Color Support*/
    XV_VidC_Supp   IsYCbCr444DeepColSupp;
    XV_VidC_Supp   Is30bppSupp;
    XV_VidC_Supp   Is36bppSupp;
    XV_VidC_Supp   Is48bppSupp;
	/*YCbCr420 Deep Color Support*/
    XV_VidC_Supp   IsYCbCr420dc30bppSupp;
    XV_VidC_Supp   IsYCbCr420dc36bppSupp;
    XV_VidC_Supp   IsYCbCr420dc48bppSupp;
	/*SCDC and SCDC ReadRequest Support*/
    XV_VidC_Supp   IsSCDCReadRequestReady;
    XV_VidC_Supp   IsSCDCPresent;
	/*Sink Capability Support*/
    u8             MaxFrameRateSupp;
    u16            MaxTmdsMhz;
	/*CEA 861 Supported VIC Support*/
    u8             SuppCeaVIC[32];
	/*VESA Sink Preffered Timing Support*/
    XV_VidC_TimingParam PreferedTiming[4];
} XV_VidC_EdidCntrlParam;


XV_VidC_TimingParam
XV_VidC_timing
           (const struct xvidc_edid_detailed_timing_descriptor * const dtb);
#if XVIDC_EDID_VERBOSITY > 1
XV_VidC_DoubleRep Double2Int (double in_val);
#endif
void XV_VidC_EdidCtrlParamInit (XV_VidC_EdidCntrlParam *EdidCtrlParam);

void
XV_VidC_parse_edid(const u8 * const data,
                  XV_VidC_EdidCntrlParam *EdidCtrlParam,
                  XV_VidC_Verbose VerboseEn);

#ifdef __cplusplus
}
#endif
#endif
