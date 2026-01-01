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
     * Convert Data to Hexadecimal String
     */
    /* Integer */
    /* 32-bit */
    Name (P346, Package (0x0C)
    {
        0x00,
        0x01,
        0x83,
        0x0456,
        0x8232,
        0x000BCDEF,
        0x00123456,
        0x0789ABCD,
        0xFFFFFFFF,
        0x01234567,
        0xFF,
        0xFFFF
    })
    Name (P347, Package (0x0C)
    {
        "00000000",
        "00000001",
        "00000083",
        "00000456",
        "00008232",
        "000BCDEF",
        "00123456",
        "0789ABCD",
        "FFFFFFFF",
        "01234567",
        "000000FF",
        "0000FFFF"
    })
    /* 64-bit */

    Name (P348, Package (0x17)
    {
        0x00,
        0x01,
        0x83,
        0x0456,
        0x8232,
        0x000BCDEF,
        0x00123456,
        0x0789ABCD,
        0xFFFFFFFF,
        0x01234567,
        0xFF,
        0xFFFF,
        0x0000000123456789,
        0x0000008123456789,
        0x00000ABCDEF01234,
        0x0000876543210ABC,
        0x0001234567ABCDEF,
        0x008234567ABCDEF1,
        0x06789ABCDEF01234,
        0x76543201F89ABCDE,
        0xF89ABCDE76543201,
        0xFFFFFFFFFFFFFFFF,
        0x0123456789ABCDEF
    })
    Name (P349, Package (0x17)
    {
        "0000000000000000",
        "0000000000000001",
        "0000000000000083",
        "0000000000000456",
        "0000000000008232",
        "00000000000BCDEF",
        "0000000000123456",
        "000000000789ABCD",
        "00000000FFFFFFFF",
        "0000000001234567",
        "00000000000000FF",
        "000000000000FFFF",
        "0000000123456789",
        "0000008123456789",
        "00000ABCDEF01234",
        "0000876543210ABC",
        "0001234567ABCDEF",
        "008234567ABCDEF1",
        "06789ABCDEF01234",
        "76543201F89ABCDE",
        "F89ABCDE76543201",
        "FFFFFFFFFFFFFFFF",
        "0123456789ABCDEF"
    })
    /* Buffer */

    Name (P350, Package (0x0A)
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

        Buffer (0x10)
        {
            /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
            /* 0008 */  0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10   // ........
        },

        Buffer (0x37)
        {
            /* 0000 */  0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF, 0xD0, 0xD1,  // ........
            /* 0008 */  0xD2, 0xD3, 0xD4, 0xD5, 0xD6, 0xD7, 0xD8, 0xD9,  // ........
            /* 0010 */  0xDA, 0xDB, 0xDC, 0xDD, 0xDE, 0xDF, 0xE0, 0xE1,  // ........
            /* 0018 */  0xE2, 0xE3, 0xE4, 0xE5, 0xE6, 0xE7, 0xE8, 0xE9,  // ........
            /* 0020 */  0xEA, 0xEB, 0xEC, 0xED, 0xEE, 0xEF, 0xF0, 0xF1,  // ........
            /* 0028 */  0xF2, 0xF3, 0xF4, 0xF5, 0xF6, 0xF7, 0xF8, 0xF9,  // ........
            /* 0030 */  0xFA, 0xFB, 0xFC, 0xFD, 0xFE, 0xFF, 0x00         // .......
        },

        /* All buffers below result in 200 characters strings */

        Buffer (0x43)
        {
            /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
            /* 0008 */  0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10,  // ........
            /* 0010 */  0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,  // ........
            /* 0018 */  0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20,  // .......
            /* 0020 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
            /* 0028 */  0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30,  // )*+,-./0
            /* 0030 */  0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38,  // 12345678
            /* 0038 */  0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40,  // 9:;<=>?@
            /* 0040 */  0x41, 0x42, 0x43                                 // ABC
        },

        Buffer (0x43)
        {
            /* 0000 */  0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B,  // DEFGHIJK
            /* 0008 */  0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53,  // LMNOPQRS
            /* 0010 */  0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A, 0x5B,  // TUVWXYZ[
            /* 0018 */  0x5C, 0x5D, 0x5E, 0x5F, 0x60, 0x61, 0x62, 0x63,  // \]^_`abc
            /* 0020 */  0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B,  // defghijk
            /* 0028 */  0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71, 0x72, 0x73,  // lmnopqrs
            /* 0030 */  0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7A, 0x7B,  // tuvwxyz{
            /* 0038 */  0x7C, 0x7D, 0x7E, 0x7F, 0x80, 0x81, 0x82, 0x83,  // |}~.....
            /* 0040 */  0x84, 0x85, 0x86                                 // ...
        },

        Buffer (0x43)
        {
            /* 0000 */  0x87, 0x88, 0x89, 0x8A, 0x8B, 0x8C, 0x8D, 0x8E,  // ........
            /* 0008 */  0x8F, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96,  // ........
            /* 0010 */  0x97, 0x98, 0x99, 0x9A, 0x9B, 0x9C, 0x9D, 0x9E,  // ........
            /* 0018 */  0x9F, 0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6,  // ........
            /* 0020 */  0xA7, 0xA8, 0xA9, 0xAA, 0xAB, 0xAC, 0xAD, 0xAE,  // ........
            /* 0028 */  0xAF, 0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6,  // ........
            /* 0030 */  0xB7, 0xB8, 0xB9, 0xBA, 0xBB, 0xBC, 0xBD, 0xBE,  // ........
            /* 0038 */  0xBF, 0xC0, 0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6,  // ........
            /* 0040 */  0xC7, 0xC8, 0xC9                                 // ...
        }
    })
    Name (P351, Package (0x0A)
    {
        "00,00,00,00,00,00,00,00,00",
        "09,07,05,03",
        "01",
        "01,02,03,04",
        "01,02,03,04,05,06,07,08",
        "01,02,03,04,05,06,07,08,09,0A,0B,0C,0D,0E,0F,10",
        "CA,CB,CC,CD,CE,CF,D0,D1,D2,D3,D4,D5,D6,D7,D8,D9,DA,DB,DC,DD,DE,DF,E0,E1,E2,E3,E4,E5,E6,E7,E8,E9,EA,EB,EC,ED,EE,EF,F0,F1,F2,F3,F4,F5,F6,F7,F8,F9,FA,FB,FC,FD,FE,FF,00",
        "01,02,03,04,05,06,07,08,09,0A,0B,0C,0D,0E,0F,10,11,12,13,14,15,16,17,18,19,1A,1B,1C,1D,1E,1F,20,21,22,23,24,25,26,27,28,29,2A,2B,2C,2D,2E,2F,30,31,32,33,34,35,36,37,38,39,3A,3B,3C,3D,3E,3F,40,41,42,43",
        "44,45,46,47,48,49,4A,4B,4C,4D,4E,4F,50,51,52,53,54,55,56,57,58,59,5A,5B,5C,5D,5E,5F,60,61,62,63,64,65,66,67,68,69,6A,6B,6C,6D,6E,6F,70,71,72,73,74,75,76,77,78,79,7A,7B,7C,7D,7E,7F,80,81,82,83,84,85,86",
        "87,88,89,8A,8B,8C,8D,8E,8F,90,91,92,93,94,95,96,97,98,99,9A,9B,9C,9D,9E,9F,A0,A1,A2,A3,A4,A5,A6,A7,A8,A9,AA,AB,AC,AD,AE,AF,B0,B1,B2,B3,B4,B5,B6,B7,B8,B9,BA,BB,BC,BD,BE,BF,C0,C1,C2,C3,C4,C5,C6,C7,C8,C9"
    })
    /* Run-method */

    Method (TOH0, 0, Serialized)
    {
        Debug = "TEST: TOH0, Convert Data to Hexadecimal String"
        /* From integer */

        If ((F64 == 0x01))
        {
            M302 (__METHOD__, 0x17, "p348", P348, P349, 0x04)
        }
        Else
        {
            M302 (__METHOD__, 0x0C, "p346", P346, P347, 0x04)
        }

        /* From string */

        M302 (__METHOD__, 0x06, "p344", P344, P344, 0x04)
        /* From buffer */

        M302 (__METHOD__, 0x0A, "p350", P350, P351, 0x04)
    }
