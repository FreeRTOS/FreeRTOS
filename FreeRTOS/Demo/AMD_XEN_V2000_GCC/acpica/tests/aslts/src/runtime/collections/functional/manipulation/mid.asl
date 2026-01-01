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
     * Extract Portion of Buffer or String
     */
    Name (Z039, 0x27)
    Name (S200, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*")
    /* Verifying 3-parameters, 1-result operator */

    Method (M304, 6, Serialized)
    {
        Local5 = 0x00
        Local3 = Arg1
        While (Local3)
        {
            /* Operands */

            Local6 = (Local5 * 0x03)
            Local0 = DerefOf (Arg3 [Local6])
            Local6++
            Local1 = DerefOf (Arg3 [Local6])
            Local6++
            Local4 = DerefOf (Arg3 [Local6])
            /* Expected result */

            Local2 = DerefOf (Arg4 [Local5])
            Switch (ToInteger (Arg5))
            {
                Case (0x00)
                {
                    Mid (Local0, Local1, Local4, Local7)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z039, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x01)
                {
                    Mid (S200, Local1, Local4, Local7)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z039, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }

            }

            Local5++
            Local3--
        }
    }

    /* String */

    Name (P362, Package (0x2A)
    {
        /* Length > 0 */

        "0123456789a",
        0x00,
        0x06,            /* Index == 0, Index + Length < Size */
        "0123456789a",
        0x03,
        0x07,            /* Index < Size, Index + Length < Size */
        "0123456789a",
        0x05,
        0x06,            /* Index < Size, Index + Length == Size */
        "0123456789a",
        0x00,
        0x0B,       /* Index == 0, Index + Length == Size */
        "0123456789a",
        0x08,
        0x08,            /* Index < Size, Index + Length > Size */
        "0123456789a",
        0x0B,
        0x03,       /* Index == Size */
        "0123456789a",
        0x0E,
        0x01,       /* Index > Size */
        "0123456789a",
        0x00,
        0x0E,       /* Index == 0, Length > Size */
        /* Length == 0 */

        "0123456789a",
        0x00,
        0x00,            /* Index == 0 */
        "0123456789a",
        0x05,
        0x00,            /* Index < Size */
        "0123456789a",
        0x0B,
        0x00,       /* Index == Size */
        "0123456789a",
        0x0F,
        0x00,       /* Index > Size */
        /* Size == 0 */

        "",
        0x00,
        0x01,
        "",
        0x012C,
        0x012C
    })
    Name (P363, Package (0x0E)
    {
        "012345",
        "3456789",
        "56789a",
        "0123456789a",
        "89a",
        "",
        "",
        "0123456789a",
        "",
        "",
        "",
        "",
        "",
        ""
    })
    /* String, Size == 200, Length > 0 */

    Name (P364, Package (0x18)
    {
        0x00,
        0x00,
        0x7D,  /* Index == 0, Index + Length < Size */
        0x00,
        0x43,
        0x43,  /* Index < Size, Index + Length < Size */
        0x00,
        0x5D,
        0x6B,     /* Index < Size, Index + Length == Size */
        0x00,
        0x00,
        0xC8,  /* Index == 0, Index + Length == Size */
        0x00,
        0x7F,
        0x64,    /* Index < Size, Index + Length > Size */
        0x00,
        0xC8,
        0x03,  /* Index == Size */
        0x00,
        0xD6,
        0x01,  /* Index > Size */
        0x00,
        0x00,
        0xC9 /* Index == 0, Length > Size */
    })
    Name (P365, Package (0x08)
    {
        "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>",
        "defghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFG",
        "~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*",
        "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*",
        "ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*",
        "",
        "",
        "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*"
    })
    /* Buffer */

    Name (P366, Package (0x18)
    {
        /* Length > 0 */

        Buffer (0x0B)
        {
            /* 0000 */  0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,  // ........
            /* 0008 */  0x08, 0x09, 0x00                                 // ...
        },

        0x00,
        0x06,            /* Index == 0, Index + Length < Size */
        Buffer (0x0B)
        {
            /* 0000 */  0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,  // ........
            /* 0008 */  0x08, 0x09, 0x00                                 // ...
        },

        0x03,
        0x07,            /* Index < Size, Index + Length < Size */
        Buffer (0x0B)
        {
            /* 0000 */  0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x00, 0x07,  // ........
            /* 0008 */  0x08, 0x09, 0x00                                 // ...
        },

        0x03,
        0x07,            /* Index < Size, Index + Length < Size */
        Buffer (0x0B)
        {
            /* 0000 */  0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,  // ........
            /* 0008 */  0x08, 0x09, 0x00                                 // ...
        },

        0x05,
        0x06,            /* Index < Size, Index + Length == Size */
        Buffer (0x0B)
        {
            /* 0000 */  0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,  // ........
            /* 0008 */  0x08, 0x09, 0x00                                 // ...
        },

        0x00,
        0x0B,       /* Index == 0, Index + Length == Size */
        Buffer (0x0B)
        {
            /* 0000 */  0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,  // ........
            /* 0008 */  0x08, 0x09, 0x00                                 // ...
        },

        0x08,
        0x08,            /* Index < Size, Index + Length > Size */
        Buffer (0x0B)
        {
            /* 0000 */  0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,  // ........
            /* 0008 */  0x08, 0x09, 0x00                                 // ...
        },

        0x00,
        0xC9,      /* Index == 0, Length > Size */
        /* Length > 200 */

        Buffer (0xD3)
        {
            /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
            /* 0008 */  0x09, 0x00, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05,  // ........
            /* 0010 */  0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D,  // ........
            /* 0018 */  0x0E, 0x0F, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15,  // ........
            /* 0020 */  0x16, 0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D,  // ........
            /* 0028 */  0x1E, 0x1F, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25,  // .. !"#$%
            /* 0030 */  0x26, 0x27, 0x28, 0x29, 0x2A, 0x2B, 0x2C, 0x2D,  // &'()*+,-
            /* 0038 */  0x2E, 0x2F, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35,  // ./012345
            /* 0040 */  0x36, 0x37, 0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D,  // 6789:;<=
            /* 0048 */  0x3E, 0x3F, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45,  // >?@ABCDE
            /* 0050 */  0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D,  // FGHIJKLM
            /* 0058 */  0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55,  // NOPQRSTU
            /* 0060 */  0x56, 0x57, 0x58, 0x59, 0x5A, 0x5B, 0x5C, 0x5D,  // VWXYZ[\]
            /* 0068 */  0x5E, 0x5F, 0x60, 0x61, 0x62, 0x63, 0x64, 0x65,  // ^_`abcde
            /* 0070 */  0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D,  // fghijklm
            /* 0078 */  0x6E, 0x6F, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75,  // nopqrstu
            /* 0080 */  0x76, 0x77, 0x78, 0x79, 0x7A, 0x7B, 0x7C, 0x7D,  // vwxyz{|}
            /* 0088 */  0x7E, 0x7F, 0x80, 0x81, 0x82, 0x83, 0x84, 0x85,  // ~.......
            /* 0090 */  0x86, 0x87, 0x88, 0x89, 0x8A, 0x8B, 0x8C, 0x8D,  // ........
            /* 0098 */  0x8E, 0x8F, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95,  // ........
            /* 00A0 */  0x96, 0x97, 0x98, 0x99, 0x9A, 0x9B, 0x9C, 0x9D,  // ........
            /* 00A8 */  0x9E, 0x9F, 0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5,  // ........
            /* 00B0 */  0xA6, 0xA7, 0xA8, 0xA9, 0xAA, 0xAB, 0xAC, 0xAD,  // ........
            /* 00B8 */  0xAE, 0xAF, 0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5,  // ........
            /* 00C0 */  0xB6, 0xB7, 0xB8, 0xB9, 0xBA, 0xBB, 0xBC, 0xBD,  // ........
            /* 00C8 */  0xBE, 0xBF, 0xC0, 0xC1, 0xC2, 0xC3, 0xC4, 0xC5,  // ........
            /* 00D0 */  0xC6, 0xC7, 0xC8                                 // ...
        },

        0x02,
        0xCB
    })
    Name (P367, Package (0x08)
    {
        Buffer (0x06)
        {
             0x00, 0x01, 0x02, 0x03, 0x04, 0x05               // ......
        },

        Buffer (0x07)
        {
             0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09         // .......
        },

        Buffer (0x07)
        {
             0x03, 0x04, 0x05, 0x00, 0x07, 0x08, 0x09         // .......
        },

        Buffer (0x06)
        {
             0x05, 0x06, 0x07, 0x08, 0x09, 0x00               // ......
        },

        Buffer (0x0B)
        {
            /* 0000 */  0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,  // ........
            /* 0008 */  0x08, 0x09, 0x00                                 // ...
        },

        Buffer (0x03)
        {
             0x08, 0x09, 0x00                                 // ...
        },

        Buffer (0x0B)
        {
            /* 0000 */  0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,  // ........
            /* 0008 */  0x08, 0x09, 0x00                                 // ...
        },

        Buffer (0xCB)
        {
            /* 0000 */  0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x00,  // ........
            /* 0008 */  0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,  // ........
            /* 0010 */  0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,  // ........
            /* 0018 */  0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,  // ........
            /* 0020 */  0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F,  // ........
            /* 0028 */  0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27,  //  !"#$%&'
            /* 0030 */  0x28, 0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F,  // ()*+,-./
            /* 0038 */  0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,  // 01234567
            /* 0040 */  0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F,  // 89:;<=>?
            /* 0048 */  0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47,  // @ABCDEFG
            /* 0050 */  0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F,  // HIJKLMNO
            /* 0058 */  0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57,  // PQRSTUVW
            /* 0060 */  0x58, 0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F,  // XYZ[\]^_
            /* 0068 */  0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67,  // `abcdefg
            /* 0070 */  0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F,  // hijklmno
            /* 0078 */  0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77,  // pqrstuvw
            /* 0080 */  0x78, 0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x7F,  // xyz{|}~.
            /* 0088 */  0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87,  // ........
            /* 0090 */  0x88, 0x89, 0x8A, 0x8B, 0x8C, 0x8D, 0x8E, 0x8F,  // ........
            /* 0098 */  0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97,  // ........
            /* 00A0 */  0x98, 0x99, 0x9A, 0x9B, 0x9C, 0x9D, 0x9E, 0x9F,  // ........
            /* 00A8 */  0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6, 0xA7,  // ........
            /* 00B0 */  0xA8, 0xA9, 0xAA, 0xAB, 0xAC, 0xAD, 0xAE, 0xAF,  // ........
            /* 00B8 */  0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7,  // ........
            /* 00C0 */  0xB8, 0xB9, 0xBA, 0xBB, 0xBC, 0xBD, 0xBE, 0xBF,  // ........
            /* 00C8 */  0xC0, 0xC1, 0xC2                                 // ...
        }
    })
    /* Buffer, Mid() results in Buffer(0){} */

    Name (P368, Package (0x12)
    {
        /* Length > 0 */

        Buffer (0x0B)
        {
            /* 0000 */  0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,  // ........
            /* 0008 */  0x08, 0x09, 0x00                                 // ...
        },

        0x0B,
        0x03,           /* Index == Size */
        Buffer (0x0B)
        {
            /* 0000 */  0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,  // ........
            /* 0008 */  0x08, 0x09, 0x00                                 // ...
        },

        0x0E,
        0x01,           /* Index > Size */
        /* Length == 0 */

        Buffer (0x0B)
        {
            /* 0000 */  0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,  // ........
            /* 0008 */  0x08, 0x09, 0x00                                 // ...
        },

        0x00,
        0x00,                /* Index == 0 */
        Buffer (0x0B)
        {
            /* 0000 */  0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x00,  // ........
            /* 0008 */  0x08, 0x09, 0x00                                 // ...
        },

        0x05,
        0x00,                /* Index < Size */
        Buffer (0x0B)
        {
            /* 0000 */  0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,  // ........
            /* 0008 */  0x08, 0x09, 0x00                                 // ...
        },

        0x0B,
        0x00,           /* Index == Size */
        Buffer (0x0B)
        {
            /* 0000 */  0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,  // ........
            /* 0008 */  0x08, 0x09, 0x00                                 // ...
        },

        0x0F,
        0x00          /* Index > Size */
    })
    /* Run-method */

    Method (MID0, 0, Serialized)
    {
        Debug = "TEST: MID0, Extract Portion of Buffer or String"
        /* String */

        M304 (__METHOD__, 0x0E, "p362", P362, P363, 0x00)
        /* String, Size == 200, Length > 0 */

        M304 (__METHOD__, 0x08, "p364", P364, P365, 0x01)
        /* Buffer */

        M304 (__METHOD__, 0x08, "p366", P366, P367, 0x00)
        /* Prepare Package of Buffer(0){} elements */

        Local5 = Package (0x06){}
        Local1 = 0x00
        Local0 = 0x00
        While ((Local0 < 0x06))
        {
            Local5 [Local0] = Buffer (Local1){}
            Local0++
        }

        /* Buffer, Mid() results in Buffer(0){} */

        M304 (__METHOD__, 0x06, "p366", P368, Local5, 0x00)
        /* Buffer, Mid(Buffer(0){}) */

        Mid (Buffer (Local1){}, 0x00, 0x01, Local7)
        If ((Local7 != Buffer (Local1){}))
        {
            ERR (__METHOD__, Z039, __LINE__, 0x00, 0x00, 0x00, "Buffer(0)")
        }

        Mid (Buffer (Local1){}, 0x012C, 0x012C, Local7)
        If ((Local7 != Buffer (Local1){}))
        {
            ERR (__METHOD__, Z039, __LINE__, 0x00, 0x00, 0x00, "Buffer(0)")
        }
    }
