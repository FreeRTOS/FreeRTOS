/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
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

#ifndef COLOR_H
#define COLOR_H

/**
 * \file
 *
 * RGB 24-bits color table definition.
 *
 */

#define color_t uint32_t

/*
 * RGB 24 Bpp
 */

// From HTML color names
// 140 color names are defined in the HTML and CSS color specification
//   (17 standard colors plus 123 more).
// The table below lists them all, along with their hexadecimal values.

// The 17 standard colors are: aqua, black, blue, fuchsia, gray, green,
// lime, maroon, navy, olive, orange, purple, red, silver, teal, white,
// and yellow.

#define COLOR_AliceBlue         0xF0F8FF
#define COLOR_AntiqueWhite      0xFAEBD7
#define COLOR_Aqua              0x00FFFF
#define COLOR_Aquamarine        0x7FFFD4
#define COLOR_AZUR              0xF0FFFF
#define COLOR_BEIGE             0xF5F5DC
#define COLOR_Bisque            0xFFE4C4
#define COLOR_BLACK             0x000000
#define COLOR_BlanchedAlmond    0xFFEBCD
#define COLOR_BLUE              0x0000FF
#define COLOR_BLUEVIOLET        0x8A2BE2
#define COLOR_BROWN             0xA52A2A
#define COLOR_BurlyWood         0xDEB887
#define COLOR_CadetBlue         0x5F9EA0
#define COLOR_Chartreuse        0x7FFF00
#define COLOR_Chocolate         0xD2691E
#define COLOR_Coral             0xFF7F50
#define COLOR_CornflowerBlue    0x6495ED
#define COLOR_Cornsilk          0xFFF8DC
#define COLOR_Crimson           0xDC143C
#define COLOR_CYAN              0x00FFFF
#define COLOR_DARKBLUE          0x00008B
#define COLOR_DARKCYAN          0x008B8B
#define COLOR_DarkGoldenRod     0xB8860B
#define COLOR_DARKGRAY          0xA9A9A9
#define COLOR_DARKGREEN         0x006400
#define COLOR_DarkKhaki         0xBDB76B
#define COLOR_DarkMagenta       0x8B008B
#define COLOR_DarkOliveGreen    0x556B2F
#define COLOR_DarkOrange        0xFF8C00
#define COLOR_DarkOrchid        0x9932CC
#define COLOR_DARKRED           0x8B0000
#define COLOR_DarkSalmon        0xE9967A
#define COLOR_DarkSeaGreen      0x8FBC8F
#define COLOR_DarkSlateBlue     0x483D8B
#define COLOR_DarkSlateGray     0x2F4F4F
#define COLOR_DarkTurquoise     0x00CED1
#define COLOR_DARKVIOLET        0x9400D3
#define COLOR_DeepPink          0xFF1493
#define COLOR_DeepSkyBlue       0x00BFFF
#define COLOR_DimGray           0x696969
#define COLOR_DodgerBlue        0x1E90FF
#define COLOR_FireBrick         0xB22222
#define COLOR_FloralWhite       0xFFFAF0
#define COLOR_ForestGreen       0x228B22
#define COLOR_Fuchsia           0xFF00FF
#define COLOR_Gainsboro         0xDCDCDC
#define COLOR_GhostWhite        0xF8F8FF
#define COLOR_GOLD              0xFFD700
#define COLOR_GoldenRod         0xDAA520
#define COLOR_GRAY              0x808080
#define COLOR_GREEN             0x008000
#define COLOR_GREENYELLOW       0xADFF2F
#define COLOR_HoneyDew          0xF0FFF0
#define COLOR_HotPink           0xFF69B4
#define COLOR_IndianRed         0xCD5C5C
#define COLOR_INDIGO            0x4B0082
#define COLOR_Ivory             0xFFFFF0
#define COLOR_Khaki             0xF0E68C
#define COLOR_Lavender          0xE6E6FA
#define COLOR_LavenderBlush     0xFFF0F5
#define COLOR_LawnGreen         0x7CFC00
#define COLOR_LemonChiffon      0xFFFACD
#define COLOR_LIGHTBLUE         0xADD8E6
#define COLOR_LightCoral        0xF08080
#define COLOR_LIGHTCYAN         0xE0FFFF
#define COLOR_LightGoldenRodYellow      0xFAFAD2
#define COLOR_LIGHTGREY         0xD3D3D3
#define COLOR_LIGHTGREEN        0x90EE90
#define COLOR_LightPink         0xFFB6C1
#define COLOR_LightSalmon       0xFFA07A
#define COLOR_LightSeaGreen     0x20B2AA
#define COLOR_LightSkyBlue      0x87CEFA
#define COLOR_LightSlateGray    0x778899
#define COLOR_LightSteelBlue    0xB0C4DE
#define COLOR_LightYellow       0xFFFFE0
#define COLOR_Lime              0x00FF00
#define COLOR_LimeGreen         0x32CD32
#define COLOR_Linen             0xFAF0E6
#define COLOR_MAGENTA           0xFF00FF
#define COLOR_Maroon            0x800000
#define COLOR_MediumAquaMarine  0x66CDAA
#define COLOR_MediumBlue        0x0000CD
#define COLOR_MediumOrchid      0xBA55D3
#define COLOR_MediumPurple      0x9370DB
#define COLOR_MediumSeaGreen    0x3CB371
#define COLOR_MediumSlateBlue   0x7B68EE
#define COLOR_MediumSpringGreen 0x00FA9A
#define COLOR_MediumTurquoise   0x48D1CC
#define COLOR_MediumVioletRed   0xC71585
#define COLOR_MidnightBlue      0x191970
#define COLOR_MintCream         0xF5FFFA
#define COLOR_MistyRose         0xFFE4E1
#define COLOR_Moccasin          0xFFE4B5
#define COLOR_NavajoWhite       0xFFDEAD
#define COLOR_NAVY              0x000080
#define COLOR_OldLace           0xFDF5E6
#define COLOR_OLIVE             0x808000
#define COLOR_OliveDrab         0x6B8E23
#define COLOR_ORANGE            0xFFA500
#define COLOR_OrangeRed         0xFF4500
#define COLOR_Orchid            0xDA70D6
#define COLOR_PaleGoldenRod     0xEEE8AA
#define COLOR_PaleGreen         0x98FB98
#define COLOR_PaleTurquoise     0xAFEEEE
#define COLOR_PaleVioletRed     0xDB7093
#define COLOR_PapayaWhip        0xFFEFD5
#define COLOR_PeachPuff         0xFFDAB9
#define COLOR_Peru              0xCD853F
#define COLOR_Pink              0xFFC0CB
#define COLOR_Plum              0xDDA0DD
#define COLOR_PowderBlue        0xB0E0E6
#define COLOR_Purple            0x800080
#define COLOR_RebeccaPurple     0x663399
#define COLOR_RED               0xFF0000
#define COLOR_RosyBrown         0xBC8F8F
#define COLOR_RoyalBlue         0x4169E1
#define COLOR_SaddleBrown       0x8B4513
#define COLOR_Salmon            0xFA8072
#define COLOR_SandyBrown        0xF4A460
#define COLOR_SeaGreen          0x2E8B57
#define COLOR_SeaShell          0xFFF5EE
#define COLOR_SIENNA            0xA0522D
#define COLOR_SILVER            0xC0C0C0
#define COLOR_SKYBLUE           0x87CEEB
#define COLOR_SlateBlue         0x6A5ACD
#define COLOR_SlateGray         0x708090
#define COLOR_SNOW              0xFFFAFA
#define COLOR_SpringGreen       0x00FF7F
#define COLOR_SteelBlue         0x4682B4
#define COLOR_Tan               0xD2B48C
#define COLOR_Teal              0x008080
#define COLOR_Thistle           0xD8BFD8
#define COLOR_TOMATO            0xFF6347
#define COLOR_TURQUOISE         0x40E0D0
#define COLOR_VIOLET            0xEE82EE
#define COLOR_Wheat             0xF5DEB3
#define COLOR_WHITE             0xFFFFFF
#define COLOR_WhiteSmoke        0xF5F5F5
#define COLOR_YELLOW            0xFFFF00
#define COLOR_YELLOWGREEN       0x9ACD32

#endif /* #define COLOR_H */
