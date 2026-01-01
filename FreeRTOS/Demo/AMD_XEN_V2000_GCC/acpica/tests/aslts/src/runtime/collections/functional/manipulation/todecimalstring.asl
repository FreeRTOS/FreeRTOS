    /*
     * Some or all of this work - Copyright (c) 2006 - 2021, Intel Corp.
     * All rights reserved.
     *
     * Redistribution and use in source and binary forms, with or without modification,
     * are permitted provided that the following conditions are met:
     *
     * Redistributions of source code must retain the above copyright notice,
     * this list of conditions and the following disclaimer.
     * Redistributions in binary form must reproduce the above copyright notice,
     * this list of conditions and the following disclaimer in the documentation
     * and/or other materials provided with the distribution.
     * Neither the name of Intel Corporation nor the names of its contributors
     * may be used to endorse or promote products derived from this software
     * without specific prior written permission.
     *
     * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
     * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
     * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
     * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
     * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
     * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
     * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
     * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
     * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
     * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
     */
    /*
     * Data type conversion and manipulation
     *
     * Convert Data to Decimal String
     */
    /* Integer */
    /* 32-bit */
    Name (P338, Package (0x0F)
    {
        0x00,
        0x01,
        0x0C,
        0x0159,
        0x1A85,
        0x3039,
        0x000A5BF5,
        0x0023CACE,
        0x055F2CC0,
        0x2F075F79,
        0xFFFFFFFF,
        0x075BCD15,
        0xFF,
        0xFFFF,
        0xFFFFFFFF
    })
    Name (P339, Package (0x0F)
    {
        "0",
        "1",
        "12",
        "345",
        "6789",
        "12345",
        "678901",
        "2345678",
        "90123456",
        "789012345",
        "4294967295",    /* == "0xffffffff" */
        "123456789",
        "255",
        "65535",
        "4294967295"   /* == "0xffffffff" */
    })
    /* 64-bit */

    Name (P340, Package (0x0B)
    {
        0x00000007037F7916,
        0x0000001CBE991A14,
        0x00000324D8AE5F79,
        0x0000185D4D9097A5,
        0x00007048860DDF79,
        0x000D76162EE9EC35,
        0x005355D348A6F34E,
        0x042E333E5528BAC0,
        0x1A3B1145078ADF79,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF
    })
    Name (P341, Package (0x0B)
    {
        "30123456790",
        "123456789012",
        "3456789012345",
        "26789012346789",
        "123456789012345",
        "3789012345678901",
        "23456789012345678",
        "301234567890123456",
        "1890123456789012345",
        "18446744073709551615",
        "18446744073709551615" /* == "0xffffffffffffffff" */
    })
    /* String */

    Name (P344, Package (0x06)
    {
        "",
        "0123456789",
        "ABCDEFGHIJKLMNOPQRSTUVWXYZ",
        "abcdefghijklmnopqrstuvwxyz",
        "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz",
        "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*"
    })
    /* Buffer */

    Name (P342, Package (0x0C)
    {
        Buffer (0x09){},
        Buffer (0x04)
        {
             0x09, 0x07, 0x05, 0x03                           // ....
        },

        Buffer (0x01)
        {
             0x01                                             // .
        },

        Buffer (0x04)
        {
             0x01, 0x02, 0x03, 0x04                           // ....
        },

        Buffer (0x08)
        {
             0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08   // ........
        },

        /* Results into 197 characters */

        Buffer (0x45)
        {
            /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
            /* 0008 */  0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10,  // ........
            /* 0010 */  0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,  // ........
            /* 0018 */  0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20,  // .......
            /* 0020 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
            /* 0028 */  0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30,  // )*+,-./0
            /* 0030 */  0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38,  // 12345678
            /* 0038 */  0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40,  // 9:;<=>?@
            /* 0040 */  0x41, 0x42, 0x43, 0x44, 0x45                     // ABCDE
        },

        Buffer (0x39)
        {
            /* 0000 */  0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D,  // FGHIJKLM
            /* 0008 */  0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55,  // NOPQRSTU
            /* 0010 */  0x56, 0x57, 0x58, 0x59, 0x5A, 0x5B, 0x5C, 0x5D,  // VWXYZ[\]
            /* 0018 */  0x5E, 0x5F, 0x60, 0x61, 0x62, 0x63, 0x64, 0x65,  // ^_`abcde
            /* 0020 */  0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D,  // fghijklm
            /* 0028 */  0x6E, 0x6F, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75,  // nopqrstu
            /* 0030 */  0x76, 0x77, 0x78, 0x79, 0x7A, 0x7B, 0x7C, 0x7D,  // vwxyz{|}
            /* 0038 */  0x7E                                             // ~
        },

        /* Results into 199 characters */

        Buffer (0x32)
        {
            /* 0000 */  0x7F, 0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86,  // ........
            /* 0008 */  0x87, 0x88, 0x89, 0x8A, 0x8B, 0x8C, 0x8D, 0x8E,  // ........
            /* 0010 */  0x8F, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96,  // ........
            /* 0018 */  0x97, 0x98, 0x99, 0x9A, 0x9B, 0x9C, 0x9D, 0x9E,  // ........
            /* 0020 */  0x9F, 0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6,  // ........
            /* 0028 */  0xA7, 0xA8, 0xA9, 0xAA, 0xAB, 0xAC, 0xAD, 0xAE,  // ........
            /* 0030 */  0xAF, 0xB0                                       // ..
        },

        Buffer (0x32)
        {
            /* 0000 */  0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,  // ........
            /* 0008 */  0xB9, 0xBA, 0xBB, 0xBC, 0xBD, 0xBE, 0xBF, 0xC0,  // ........
            /* 0010 */  0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7, 0xC8,  // ........
            /* 0018 */  0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF, 0xD0,  // ........
            /* 0020 */  0xD1, 0xD2, 0xD3, 0xD4, 0xD5, 0xD6, 0xD7, 0xD8,  // ........
            /* 0028 */  0xD9, 0xDA, 0xDB, 0xDC, 0xDD, 0xDE, 0xDF, 0xE0,  // ........
            /* 0030 */  0xE1, 0xE2                                       // ..
        },

        Buffer (0x1E)
        {
            /* 0000 */  0xE3, 0xE4, 0xE5, 0xE6, 0xE7, 0xE8, 0xE9, 0xEA,  // ........
            /* 0008 */  0xEB, 0xEC, 0xED, 0xEE, 0xEF, 0xF0, 0xF1, 0xF2,  // ........
            /* 0010 */  0xF3, 0xF4, 0xF5, 0xF6, 0xF7, 0xF8, 0xF9, 0xFA,  // ........
            /* 0018 */  0xFB, 0xFC, 0xFD, 0xFE, 0xFF, 0x00               // ......
        },

        /* Results into 200 characters */

        Buffer (0x64)
        {
            /* 0000 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0008 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0010 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0018 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0020 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0028 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0030 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0038 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0040 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0048 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0050 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0058 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0060 */  0x01, 0x01, 0x01, 0x0B                           // ....
        },

        Buffer (0x33)
        {
            /* 0000 */  0x6F, 0x6F, 0x6F, 0x6F, 0x6F, 0x6F, 0x6F, 0x6F,  // oooooooo
            /* 0008 */  0x6F, 0x6F, 0x6F, 0x6F, 0x6F, 0x6F, 0x6F, 0x6F,  // oooooooo
            /* 0010 */  0x6F, 0x6F, 0x6F, 0x6F, 0x6F, 0x6F, 0x6F, 0x6F,  // oooooooo
            /* 0018 */  0x6F, 0x6F, 0x6F, 0x6F, 0x6F, 0x6F, 0x6F, 0x6F,  // oooooooo
            /* 0020 */  0x6F, 0x6F, 0x6F, 0x6F, 0x6F, 0x6F, 0x6F, 0x6F,  // oooooooo
            /* 0028 */  0x6F, 0x6F, 0x6F, 0x6F, 0x6F, 0x6F, 0x6F, 0x6F,  // oooooooo
            /* 0030 */  0x6F, 0x0B, 0x01                                 // o..
        }
    })
    Name (P343, Package (0x0C)
    {
        "0,0,0,0,0,0,0,0,0",
        "9,7,5,3",
        "1",
        "1,2,3,4",
        "1,2,3,4,5,6,7,8",
        "1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69",
        "70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126",
        "127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176",
        "177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226",
        "227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,0",
        "1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,11",
        "111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,111,11,1"
    })
    /* Run-method */

    Method (TOD0, 0, Serialized)
    {
        Debug = "TEST: TOD0, Convert Data to Decimal String"
        /* From integer */

        If ((F64 == 0x01))
        {
            M302 (__METHOD__, 0x0F, "p338", P338, P339, 0x03)
            M302 (__METHOD__, 0x0B, "p340", P340, P341, 0x03)
        }
        Else
        {
            M302 (__METHOD__, 0x0F, "p338", P338, P339, 0x03)
        }

        /* From buffer */

        M302 (__METHOD__, 0x0C, "p342", P342, P343, 0x03)
        /* From string */

        M302 (__METHOD__, 0x06, "p344", P344, P344, 0x03)
    }
