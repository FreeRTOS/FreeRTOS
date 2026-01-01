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
     * Concatenate two strings, integers or buffers
     */
    /*
     // !!!!!!!!!!!!!!!!!!!!!!!!!! ???????????????????
     // SEE: (Compare two buffers)
     // Remove (?) this method and replace it with the
     // LNotEqual, LEqual............ ????? !!!!!!!!!!
     // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
     */
    Name (Z036, 0x24)
    /* Compare two buffers */
    /* */
    /* Arg0 - name */
    /* Arg1 - buffer1 */
    /* Arg2 - buffer2 */
    /* Arg3 - length */
    Method (M310, 4, NotSerialized)
    {
        Local0 = 0x00
        While ((Local0 < Arg3))
        {
            Local1 = DerefOf (Arg1 [Local0])
            Local2 = DerefOf (Arg2 [Local0])
            If ((Local1 != Local2))
            {
                Return (Ones)
            }

            Local0++
        }

        Return (Zero)
    }

    /* Compare two buffers */
    /* */
    /* Arg0 - name */
    /* Arg1 - buffer1 */
    /* Arg2 - buffer2 */
    Method (M311, 3, NotSerialized)
    {
        If ((ObjectType (Arg1) != 0x03))
        {
            ERR ("m311: unexpected type of Arg1", Z036, __LINE__, 0x00, 0x00, 0x00, 0x00)
            Return (Ones)
        }

        If ((ObjectType (Arg2) != 0x03))
        {
            ERR ("m311: unexpected type of Arg2", Z036, __LINE__, 0x00, 0x00, 0x00, 0x00)
            Return (Ones)
        }

        Local0 = SizeOf (Arg1)
        If ((Local0 != SizeOf (Arg2)))
        {
            Return (Ones)
        }

        If (M310 (Arg0, Arg1, Arg2, Local0))
        {
            Return (Ones)
        }

        Return (Zero)
    }

    /* Verifying 2-parameters, 1-result operator */

    Method (M312, 6, Serialized)
    {
        Local5 = 0x00
        Local3 = Arg1
        While (Local3)
        {
            /* Operands */

            Local6 = (Local5 * 0x02)
            Local0 = DerefOf (Arg3 [Local6])
            Local6++
            Local1 = DerefOf (Arg3 [Local6])
            /* Expected result */

            Local2 = DerefOf (Arg4 [Local5])
            Switch (ToInteger (Arg5))
            {
                Case (0x00)
                {
                    /* Results in buffer */

                    Concatenate (Local0, Local1, Local7)
                    If (M311 (Arg0, Local7, Local2))
                    {
                        ERR (Arg0, Z036, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x01)
                {
                    /* Results in string */

                    Concatenate (Local0, Local1, Local7)
                    If ((ObjectType (Local7) != 0x02))
                    {
                        ERR (Arg0, Z036, __LINE__, 0x00, 0x00, Local7, Arg2)
                    }
                    ElseIf ((ObjectType (Local2) != 0x02))
                    {
                        ERR (Arg0, Z036, __LINE__, 0x00, 0x00, Local2, Arg2)
                    }
                    ElseIf ((Local7 != Local2))
                    {
                        ERR (Arg0, Z036, __LINE__, 0x00, 0x00, Local7, Arg2)
                    }
                }

            }

            Local5++
            Local3--
        }
    }

    /* Integers */

    Method (M313, 0, Serialized)
    {
        Name (P000, Package (0x18)
        {
            0x00,
            0x00,
            0xFFFFFFFF,
            0xFFFFFFFF,
            0x00,
            0xFFFFFFFF,
            0x00,
            0x81,
            0x00,
            0x9AC6,
            0x00,
            0xAB012345,
            0x92,
            0x81,
            0x93,
            0x8476,
            0xAB,
            0xDC816778,
            0xAC93,
            0x8476,
            0xF63B,
            0x8C8FC2DA,
            0x8790F6A4,
            0x98DE45BA
        })
        Name (P001, Package (0x0C)
        {
            Buffer (0x08)
            {
                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF   // ........
            },

            Buffer (0x08)
            {
                 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF   // ........
            },

            Buffer (0x08)
            {
                 0x00, 0x00, 0x00, 0x00, 0x81, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x00, 0x00, 0x00, 0x00, 0xC6, 0x9A, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x00, 0x00, 0x00, 0x00, 0x45, 0x23, 0x01, 0xAB   // ....E#..
            },

            Buffer (0x08)
            {
                 0x92, 0x00, 0x00, 0x00, 0x81, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x93, 0x00, 0x00, 0x00, 0x76, 0x84, 0x00, 0x00   // ....v...
            },

            Buffer (0x08)
            {
                 0xAB, 0x00, 0x00, 0x00, 0x78, 0x67, 0x81, 0xDC   // ....xg..
            },

            Buffer (0x08)
            {
                 0x93, 0xAC, 0x00, 0x00, 0x76, 0x84, 0x00, 0x00   // ....v...
            },

            Buffer (0x08)
            {
                 0x3B, 0xF6, 0x00, 0x00, 0xDA, 0xC2, 0x8F, 0x8C   // ;.......
            },

            Buffer (0x08)
            {
                 0xA4, 0xF6, 0x90, 0x87, 0xBA, 0x45, 0xDE, 0x98   // .....E..
            }
        })
        Name (P002, Package (0x0C)
        {
            Buffer (0x10)
            {
                /* 0000 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x10)
            {
                /* 0000 */  0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x10)
            {
                /* 0000 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x10)
            {
                /* 0000 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x81, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x10)
            {
                /* 0000 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0xC6, 0x9A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x10)
            {
                /* 0000 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x45, 0x23, 0x01, 0xAB, 0x00, 0x00, 0x00, 0x00   // E#......
            },

            Buffer (0x10)
            {
                /* 0000 */  0x92, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x81, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x10)
            {
                /* 0000 */  0x93, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x76, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x10)
            {
                /* 0000 */  0xAB, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x78, 0x67, 0x81, 0xDC, 0x00, 0x00, 0x00, 0x00   // xg......
            },

            Buffer (0x10)
            {
                /* 0000 */  0x93, 0xAC, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x76, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x10)
            {
                /* 0000 */  0x3B, 0xF6, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ;.......
                /* 0008 */  0xDA, 0xC2, 0x8F, 0x8C, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x10)
            {
                /* 0000 */  0xA4, 0xF6, 0x90, 0x87, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0xBA, 0x45, 0xDE, 0x98, 0x00, 0x00, 0x00, 0x00   // .E......
            }
        })
        Name (P003, Package (0x04)
        {
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0x1234567890ABCDEF,
            0x1122334455667788
        })
        Name (P004, Package (0x02)
        {
            Buffer (0x10)
            {
                /* 0000 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
                /* 0008 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF   // ........
            },

            ToUUID ("90abcdef-5678-1234-8877-665544332211")
        })
        If ((F64 == 0x01))
        {
            M312 (__METHOD__, 0x0C, "p000", P000, P002, 0x00)
            M312 (__METHOD__, 0x02, "p003", P003, P004, 0x00)
        }
        Else
        {
            M312 (__METHOD__, 0x0C, "p000", P000, P001, 0x00)
        }
    }

    /* Strings */

    Method (M314, 0, Serialized)
    {
        Name (P000, Package (0x2C)
        {
            "qwertyuiop",
            "qwertyuiop",
            "qwertyuiop",
            "qwertyuiop0",
            "qwertyuiop",
            "qwertyuio",
            "",
            "",
            " ",
            "",
            "",
            " ",
            " ",
            " ",
            "  ",
            " ",
            " ",
            "  ",
            "a",
            "",
            "",
            "a",
            " a",
            "a",
            "a",
            " a",
            "a ",
            "a",
            "a",
            "a ",
            "a b",
            "ab",
            "ab",
            "a b",
            "a  b",
            "a b",
            "a b",
            "a  b",
            "abcDef",
            "abcdef",
            /* 100 + 100 */

            "0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789",
            "0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789",
            "0",
            ""
        })
        Name (P001, Package (0x15)
        {
            "qwertyuiopqwertyuiop",
            "qwertyuiopqwertyuiop0",
            "qwertyuiopqwertyuio",
            "",
            " ",
            " ",
            "  ",
            "   ",
            "   ",
            "a",
            "a",
            " aa",
            "a a",
            "a a",
            "aa ",
            "a bab",
            "aba b",
            "a  ba b",
            "a ba  b",
            "abcDefabcdef",
            "01234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
        })
        M312 (__METHOD__, 0x15, "p000", P000, P001, 0x01)
    }

    /* Buffers */

    Method (M315, 0, Serialized)
    {
        Name (P000, Package (0x02)
        {
            Buffer (0x64){},
            Buffer (0x65){}
        })
        Name (P001, Package (0x01)
        {
            Buffer (0xC9){}
        })
        Name (P002, Package (0x03)
        {
            Buffer (0x05)
            {
                 0x01, 0x01, 0x02, 0x03, 0x04                     // .....
            },

            Buffer (0x88)
            {
                /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                /* 0008 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                /* 0010 */  0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10,  // ........
                /* 0018 */  0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,  // ........
                /* 0020 */  0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20,  // .......
                /* 0028 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
                /* 0030 */  0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30,  // )*+,-./0
                /* 0038 */  0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38,  // 12345678
                /* 0040 */  0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40,  // 9:;<=>?@
                /* 0048 */  0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48,  // ABCDEFGH
                /* 0050 */  0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50,  // IJKLMNOP
                /* 0058 */  0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58,  // QRSTUVWX
                /* 0060 */  0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, 0x60,  // YZ[\]^_`
                /* 0068 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68,  // abcdefgh
                /* 0070 */  0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70,  // ijklmnop
                /* 0078 */  0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78,  // qrstuvwx
                /* 0080 */  0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x7F, 0x80   // yz{|}~..
            },

            Buffer (0x01C9)
            {
                /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                /* 0008 */  0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10,  // ........
                /* 0010 */  0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,  // ........
                /* 0018 */  0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20,  // .......
                /* 0020 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
                /* 0028 */  0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30,  // )*+,-./0
                /* 0030 */  0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38,  // 12345678
                /* 0038 */  0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40,  // 9:;<=>?@
                /* 0040 */  0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48,  // ABCDEFGH
                /* 0048 */  0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50,  // IJKLMNOP
                /* 0050 */  0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58,  // QRSTUVWX
                /* 0058 */  0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, 0x60,  // YZ[\]^_`
                /* 0060 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68,  // abcdefgh
                /* 0068 */  0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70,  // ijklmnop
                /* 0070 */  0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78,  // qrstuvwx
                /* 0078 */  0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x7F, 0x80,  // yz{|}~..
                /* 0080 */  0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88,  // ........
                /* 0088 */  0x89, 0x8A, 0x8B, 0x8C, 0x8D, 0x8E, 0x8F, 0x90,  // ........
                /* 0090 */  0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98,  // ........
                /* 0098 */  0x99, 0x9A, 0x9B, 0x9C, 0x9D, 0x9E, 0x9F, 0xA0,  // ........
                /* 00A0 */  0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6, 0xA7, 0xA8,  // ........
                /* 00A8 */  0xA9, 0xAA, 0xAB, 0xAC, 0xAD, 0xAE, 0xAF, 0xB0,  // ........
                /* 00B0 */  0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,  // ........
                /* 00B8 */  0xB9, 0xBA, 0xBB, 0xBC, 0xBD, 0xBE, 0xBF, 0xC0,  // ........
                /* 00C0 */  0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7, 0xC8,  // ........
                /* 00C8 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                /* 00D0 */  0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10,  // ........
                /* 00D8 */  0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,  // ........
                /* 00E0 */  0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20,  // .......
                /* 00E8 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
                /* 00F0 */  0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30,  // )*+,-./0
                /* 00F8 */  0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38,  // 12345678
                /* 0100 */  0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40,  // 9:;<=>?@
                /* 0108 */  0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48,  // ABCDEFGH
                /* 0110 */  0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50,  // IJKLMNOP
                /* 0118 */  0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58,  // QRSTUVWX
                /* 0120 */  0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, 0x60,  // YZ[\]^_`
                /* 0128 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68,  // abcdefgh
                /* 0130 */  0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70,  // ijklmnop
                /* 0138 */  0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78,  // qrstuvwx
                /* 0140 */  0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x7F, 0x80,  // yz{|}~..
                /* 0148 */  0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88,  // ........
                /* 0150 */  0x89, 0x8A, 0x8B, 0x8C, 0x8D, 0x8E, 0x8F, 0x90,  // ........
                /* 0158 */  0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98,  // ........
                /* 0160 */  0x99, 0x9A, 0x9B, 0x9C, 0x9D, 0x9E, 0x9F, 0xA0,  // ........
                /* 0168 */  0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6, 0xA7, 0xA8,  // ........
                /* 0170 */  0xA9, 0xAA, 0xAB, 0xAC, 0xAD, 0xAE, 0xAF, 0xB0,  // ........
                /* 0178 */  0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,  // ........
                /* 0180 */  0xB9, 0xBA, 0xBB, 0xBC, 0xBD, 0xBE, 0xBF, 0xC0,  // ........
                /* 0188 */  0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7, 0xC8,  // ........
                /* 0190 */  0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF, 0xD0,  // ........
                /* 0198 */  0xD1, 0xD2, 0xD3, 0xD4, 0xD5, 0xD6, 0xD7, 0xD8,  // ........
                /* 01A0 */  0xD9, 0xDA, 0xDB, 0xDC, 0xDD, 0xDE, 0xDF, 0xE0,  // ........
                /* 01A8 */  0xE1, 0xE2, 0xE3, 0xE4, 0xE5, 0xE6, 0xE7, 0xE8,  // ........
                /* 01B0 */  0xE9, 0xEA, 0xEB, 0xEC, 0xED, 0xEE, 0xEF, 0xF0,  // ........
                /* 01B8 */  0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6, 0xF7, 0xF8,  // ........
                /* 01C0 */  0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE, 0xFF, 0x00,  // ........
                /* 01C8 */  0x01                                             // .
            }
        })
        M312 (__METHOD__, 0x01, "p000", P000, P001, 0x00)
        M312 (__METHOD__, 0x03, "p325", P325, P002, 0x00)
    }

    /* Run-method */

    Method (CCT0, 0, NotSerialized)
    {
        Debug = "TEST: CCT0, Concatenate two strings, integers or buffers"
        M313 ()
        M314 ()
        M315 ()
    }
