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
     ============================
     !!!!!!!!!!!!!!!!!!!!!!!!!!!!
     IT IS IN PROGRESS !!!!!!!!!!
     !!!!!!!!!!!!!!!!!!!!!!!!!!!!
     ============================
     */
    /* Implicit Result Object Conversion, complex test */
    Name (Z067, 0x43)
    /* Integers */

    Name (II00, 0x00)
    Name (II10, 0x00)
    /* Strings */

    Name (SS00, "")
    Name (SS10, "!@#$%^&*()_+=-[]{}")
    /* Buffers */

    Name (BB00, Buffer (0x01){})
    Name (BB80, Buffer (0x01){})
    /* Inside 32-bit Integer */

    Name (BB01, Buffer (0x03){})
    Name (BB81, Buffer (0x03){})
    /* 32-bit Integer */

    Name (BB02, Buffer (0x04){})
    Name (BB82, Buffer (0x04){})
    /* Inside 64-bit Integer */

    Name (BB03, Buffer (0x05){})
    Name (BB83, Buffer (0x05){})
    /* Inside 64-bit Integer */

    Name (BB04, Buffer (0x08){})
    Name (BB84, Buffer (0x08){})
    /* Size exceeding result */

    Name (BB05, Buffer (0x14){})
    Name (BB85, Buffer (0x14){})
    /* Buffer Fields */

    Name (BBFF, Buffer (0xA0){})
    CreateField (BBFF, 0x05, 0x1B, BF00)
    CreateField (BBFF, 0x20, 0x2F, BF01)
    CreateField (BBFF, 0x4F, 0x1B, BF10)
    CreateField (BBFF, 0x6A, 0x2F, BF11)
    /* Incomplete last byte */

    CreateField (BBFF, 0x99, 0x6F, BF02)
    CreateField (BBFF, 0x0108, 0x6F, BF12)
    /* Incomplete extra byte */

    CreateField (BBFF, 0x0177, 0x77, BF03)
    CreateField (BBFF, 0x01EE, 0x77, BF13)
    /* Size exceeding result */

    CreateField (BBFF, 0x028E, 0xA0, BF04)
    CreateField (BBFF, 0x032E, 0xA0, BF14)
    /* 32-bit Integer */

    CreateField (BBFF, 0x03CE, 0x20, BF05)
    CreateField (BBFF, 0x03EE, 0x20, BF15)
    /* 64-bit Integer */

    CreateField (BBFF, 0x040E, 0x40, BF06)
    CreateField (BBFF, 0x044E, 0x40, BF16)
    /* Set all bytes of Buffer bbff to 0xff */

    Method (M565, 0, Serialized)
    {
        Name (LPN0, 0xA0)
        Name (LPC0, 0x00)
        While (LPN0)
        {
            BBFF [LPC0] = 0xFF
            LPN0--
            LPC0++
        }
    }

    /* Acquire (mux, wrd) => Boolean */

    Method (M500, 1, Serialized)
    {
        Name (TS, "m500")
        TS00 (TS)
        Mutex (MT00, 0x00)
        Name (B000, Buffer (0x01)
        {
             0x00                                             // .
        })
        II10 = Acquire (MT00, 0x0000)
        M4C0 (TS, II10, Zero, Zero)
        SS10 = Acquire (MT00, 0x0010)
        M4C0 (TS, SS10, "0000000000000000", "00000000")
        BB80 = Acquire (MT00, 0x0020)
        M4C0 (TS, BB80, B000, B000)
    }

    /* Add (int, int, Result) => Integer */

    Method (M501, 1, Serialized)
    {
        Name (TS, "m501")
        TS00 (TS)
        Name (B000, Buffer (0x01)
        {
             0x63                                             // c
        })
        Name (B001, Buffer (0x01)
        {
             0x63                                             // c
        })
        Name (B002, Buffer (0x10)
        {
            /* 0000 */  0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,  // ........
            /* 0008 */  0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F   // ........
        })
        Name (B003, Buffer (0x10)
        {
            /* 0000 */  0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27,  //  !"#$%&'
            /* 0008 */  0x28, 0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F   // ()*+,-./
        })
        Name (B004, Buffer (0x10)
        {
            /* 0000 */  0x63, 0xF4, 0x9C, 0x52, 0x13, 0xCF, 0x8A, 0x00,  // c..R....
            /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
        })
        Name (B005, Buffer (0x10)
        {
            /* 0000 */  0x63, 0xF4, 0x9C, 0x52, 0x00, 0x00, 0x00, 0x00,  // c..R....
            /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
        })
        /* Integers */

        II10 = II00 = (0x00123456789ABCDA + 0x00789ABCDA023789)
        M4C0 (TS, II00, 0x008ACF13529CF463, 0x529CF463)
        M4C0 (TS, II10, 0x008ACF13529CF463, 0x529CF463)
        /* Strings */

        SS10 = SS00 = (0x00123456789ABCDA + 0x00789ABCDA023789)
        M4C0 (TS, SS00, "008ACF13529CF463", "529CF463")
        M4C0 (TS, SS10, "008ACF13529CF463", "529CF463")
        /* Buffers smaller than result */

        BB80 = BB00 = (0x00123456789ABCDA + 0x00789ABCDA023789)
        M4C0 (TS, BB00, B000, B001)
        M4C0 (TS, BB80, B000, B001)
        /* Buffers greater than result */

        B003 = B002 = (0x00123456789ABCDA + 0x00789ABCDA023789)
        M4C0 (TS, B002, B004, B005)
        M4C0 (TS, B003, B004, B005)
        /* Set fields (their source buffer) to zero */
        /* Store(bbff, Debug) */
        M565 ()
        BF10 = BF00 = (0x00123456789ABCDA + 0x00789ABCDA023789)
        M4C0 (TS, BF00, B004, B005)
        M4C0 (TS, BF10, B004, B005)
        /* !!! check the contents of bbff !!!!!!!!! */
    /* Store(bbff, Debug) */
    }

    /* And (int, int, Result) => Integer */

    Method (M502, 1, Serialized)
    {
        Name (TS, "m502")
        TS00 (TS)
    }

    /* Concatenate ({int|str|buf}, {int|str|buf}, Result) => ComputationalData */

    Method (M503, 1, NotSerialized)
    {
        M563 ()
        M564 ()
    }

    Method (M563, 0, Serialized)
    {
        Name (TS, "m503,s+s")
        /* s+s -->> s -->> all combinations of Result and ComputationalData */
        /* Result 64-bit, 32-bit, ComputationalData 64-bit, 32-bit */
        Name (P000, Package (0xAC)
        {
            /* ============= With Result */

            0x00ABCDEF12345678,
            0x12345678,
            0x00ABCDEF12345678,
            0x12345678,
            0x00ABCDEF12345678,
            0x12345678,
            "abcdef12345678",
            "abcdef12345678",
            0x00ABCDEF12345678,
            0x12345678,
            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            0x00ABCDEF12345678,
            0x12345678,
            0x04636261,
            0x04636261,
            0x00ABCDEF12345678,
            0x12345678,
            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            "abcdef12345678",
            "abcdef12345678",
            0x00ABCDEF12345678,
            0x12345678,
            "abcdef12345678",
            "abcdef12345678",
            "abcdef12345678",
            "abcdef12345678",
            "abcdef12345678",
            "abcdef12345678",
            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            "abcdef12345678",
            "abcdef12345678",
            0x04636261,
            0x04636261,
            "abcdef12345678",
            "abcdef12345678",
            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            0x00ABCDEF12345678,
            0x12345678,
            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            "abcdef12345678",
            "abcdef12345678",
            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            0x04636261,
            0x04636261,
            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            0x04636261,
            0x04636261,
            0x00ABCDEF12345678,
            0x12345678,
            0x04636261,
            0x04636261,
            "abcdef12345678",
            "abcdef12345678",
            0x04636261,
            0x04636261,
            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            0x04636261,
            0x04636261,
            0x04636261,
            0x04636261,
            0x04636261,
            0x04636261,
            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            0x00ABCDEF12345678,
            0x12345678,
            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            "abcdef12345678",
            "abcdef12345678",
            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            0x04636261,
            0x04636261,
            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            /* ============= Result omitted */

            0x00,
            0x00,
            0x00ABCDEF12345678,
            0x12345678,
            0x00,
            0x00,
            "abcdef12345678",
            "abcdef12345678",
            0x00,
            0x00,
            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            0x00,
            0x00,
            0x04636261,
            0x04636261,
            0x00,
            0x00,
            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            /* ============= Store omitted */

            0x00ABCDEF12345678,
            0x12345678,
            0x00,
            0x00,
            "abcdef12345678",
            "abcdef12345678",
            0x00,
            0x00,
            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            0x00,
            0x00,
            0x04636261,
            0x04636261,
            0x00,
            0x00,
            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            0x00,
            0x00,
            /* ============= Particular additional cases */

            Buffer (0x0E)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38               // 345678
            },

            Buffer (0x0E)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38               // 345678
            },

            Buffer (0x0E)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38               // 345678
            },

            Buffer (0x0E)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38               // 345678
            },

            Buffer (0x0F)
            {
                "abcdef12345678"
            },

            Buffer (0x0F)
            {
                "abcdef12345678"
            },

            Buffer (0x0F)
            {
                "abcdef12345678"
            },

            Buffer (0x0F)
            {
                "abcdef12345678"
            },

            Buffer (0x14)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x00, 0x00,  // 345678..
                /* 0010 */  0x00, 0x00, 0x00, 0x00                           // ....
            },

            Buffer (0x14)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x00, 0x00,  // 345678..
                /* 0010 */  0x00, 0x00, 0x00, 0x00                           // ....
            },

            Buffer (0x14)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x00, 0x00,  // 345678..
                /* 0010 */  0x00, 0x00, 0x00, 0x00                           // ....
            },

            Buffer (0x14)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x00, 0x00,  // 345678..
                /* 0010 */  0x00, 0x00, 0x00, 0x00                           // ....
            },

            Buffer (0x03)
            {
                 0x61, 0x62, 0x63                                 // abc
            },

            Buffer (0x03)
            {
                 0x61, 0x62, 0x63                                 // abc
            },

            Buffer (0x03)
            {
                 0x61, 0x62, 0x63                                 // abc
            },

            Buffer (0x03)
            {
                 0x61, 0x62, 0x63                                 // abc
            },

            Buffer (0x04)
            {
                 0x61, 0x62, 0x63, 0x64                           // abcd
            },

            Buffer (0x04)
            {
                 0x61, 0x62, 0x63, 0x64                           // abcd
            },

            Buffer (0x04)
            {
                 0x61, 0x62, 0x63, 0x64                           // abcd
            },

            Buffer (0x04)
            {
                 0x61, 0x62, 0x63, 0x64                           // abcd
            },

            Buffer (0x05)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65                     // abcde
            },

            Buffer (0x05)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65                     // abcde
            },

            Buffer (0x05)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65                     // abcde
            },

            Buffer (0x05)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65                     // abcde
            },

            Buffer (0x08)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32   // abcdef12
            },

            Buffer (0x08)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32   // abcdef12
            },

            Buffer (0x08)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32   // abcdef12
            },

            Buffer (0x08)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32   // abcdef12
            },

            Buffer (0x14)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x00, 0x00,  // 345678..
                /* 0010 */  0x00, 0x00, 0x00, 0x00                           // ....
            },

            Buffer (0x14)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x00, 0x00,  // 345678..
                /* 0010 */  0x00, 0x00, 0x00, 0x00                           // ....
            },

            Buffer (0x14)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x00, 0x00,  // 345678..
                /* 0010 */  0x00, 0x00, 0x00, 0x00                           // ....
            },

            Buffer (0x14)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x00, 0x00,  // 345678..
                /* 0010 */  0x00, 0x00, 0x00, 0x00                           // ....
            }
        })
        Local0 = "abcdef"
        Local1 = "12345678"
        M562 (TS, Local0, Local1, P000)
        /* Source values are not corrupted */

        Local2 = ObjectType (Local0)
        If ((Local2 != 0x02))
        {
            ERR (TS, Z067, __LINE__, 0x00, 0x00, Local2, 0x02)
        }
        ElseIf ((Local0 != "abcdef"))
        {
            ERR (TS, Z067, __LINE__, 0x00, 0x00, Local0, "abcdef")
        }

        Local2 = ObjectType (Local1)
        If ((Local2 != 0x02))
        {
            ERR (TS, Z067, __LINE__, 0x00, 0x00, Local2, 0x02)
        }
        ElseIf ((Local1 != "12345678"))
        {
            ERR (TS, Z067, __LINE__, 0x00, 0x00, Local1, "12345678")
        }
    }

    Method (M564, 0, Serialized)
    {
        Name (TS, "m503,b+b")
        /* b+b -->> b -->> all combinations of Result and ComputationalData */
        /* Result 64-bit, 32-bit, ComputationalData 64-bit, 32-bit */
        Name (P000, Package (0xAC)
        {
            /* ============= With Result */
            /* i,i */
            0x3231666564636261,
            0x64636261,
            0x3231666564636261,
            0x64636261,
            /* i,s */

            0x3231666564636261,
            0x64636261,
            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            /* i,b */

            0x3231666564636261,
            0x64636261,
            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            /* i,bf(i,i) */

            0x3231666564636261,
            0x64636261,
            0x04636261,
            0x04636261,
            /* i,bf(i,b) */

            0x3231666564636261,
            0x64636261,
            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            /* s,i */

            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            0x3231666564636261,
            0x64636261,
            /* s,s */

            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            /* s,b */

            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            /* s,bf(i,i) */

            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            0x04636261,
            0x04636261,
            /* s,bf(i,b) */

            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            /* b,i */

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            0x3231666564636261,
            0x64636261,
            /* b,s */

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            /* b,b */

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            /* b,bf(i,i) */

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            0x04636261,
            0x04636261,
            /* b,bf(i,b) */

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            /* bf(i,i),i */

            0x04636261,
            0x04636261,
            0x3231666564636261,
            0x64636261,
            /* bf(i,i),s */

            0x04636261,
            0x04636261,
            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            /* bf(i,i),b */

            0x04636261,
            0x04636261,
            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            /* bf(i,i),bf(i,i) */

            0x04636261,
            0x04636261,
            0x04636261,
            0x04636261,
            /* bf(i,i),bf(i,b) */

            0x04636261,
            0x04636261,
            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            /* bf(i,b),i */

            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            0x3231666564636261,
            0x64636261,
            /* bf(i,b),s */

            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            /* bf(i,b),b */

            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            /* bf(i,b),bf(i,i) */

            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            0x04636261,
            0x04636261,
            /* bf(i,b),bf(i,b) */

            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            /* ============= Result omitted */
            /* ,i */
            0x00,
            0x00,
            0x3231666564636261,
            0x64636261,
            /* ,s */

            0x00,
            0x00,
            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            /* ,b */

            0x00,
            0x00,
            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            /* ,bf(i,i) */

            0x00,
            0x00,
            0x04636261,
            0x04636261,
            /* b,bf(i,b) */

            0x00,
            0x00,
            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            /* ============= Store omitted */
            /* i, */
            0x3231666564636261,
            0x64636261,
            0x00,
            0x00,
            /* s, */

            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            "61 62 63 64 65 66 31 32 33 34 35 36 37 38",
            0x00,
            0x00,
            /* b, */

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            Buffer (0x01)
            {
                 0x61                                             // a
            },

            0x00,
            0x00,
            /* bf(i,i), */

            0x04636261,
            0x04636261,
            0x00,
            0x00,
            /* bf(i,b), */

            0x0000666564636261,
            Buffer (0x06)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
            },

            0x00,
            0x00,
            /* ============= Particular additional cases */
            /* Buffer Field, incomplete last byte */
            Buffer (0x0E)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38               // 345678
            },

            Buffer (0x0E)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38               // 345678
            },

            Buffer (0x0E)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38               // 345678
            },

            Buffer (0x0E)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38               // 345678
            },

            /* Buffer Field, incomplete extra byte */

            Buffer (0x0F)
            {
                "abcdef12345678"
            },

            Buffer (0x0F)
            {
                "abcdef12345678"
            },

            Buffer (0x0F)
            {
                "abcdef12345678"
            },

            Buffer (0x0F)
            {
                "abcdef12345678"
            },

            /* Buffer Field, size exceeding result */

            Buffer (0x14)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x00, 0x00,  // 345678..
                /* 0010 */  0x00, 0x00, 0x00, 0x00                           // ....
            },

            Buffer (0x14)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x00, 0x00,  // 345678..
                /* 0010 */  0x00, 0x00, 0x00, 0x00                           // ....
            },

            Buffer (0x14)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x00, 0x00,  // 345678..
                /* 0010 */  0x00, 0x00, 0x00, 0x00                           // ....
            },

            Buffer (0x14)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x00, 0x00,  // 345678..
                /* 0010 */  0x00, 0x00, 0x00, 0x00                           // ....
            },

            /* Buffer, inside 32-bit Integer */

            Buffer (0x03)
            {
                 0x61, 0x62, 0x63                                 // abc
            },

            Buffer (0x03)
            {
                 0x61, 0x62, 0x63                                 // abc
            },

            Buffer (0x03)
            {
                 0x61, 0x62, 0x63                                 // abc
            },

            Buffer (0x03)
            {
                 0x61, 0x62, 0x63                                 // abc
            },

            /* Buffer, 32-bit Integer */

            Buffer (0x04)
            {
                 0x61, 0x62, 0x63, 0x64                           // abcd
            },

            Buffer (0x04)
            {
                 0x61, 0x62, 0x63, 0x64                           // abcd
            },

            Buffer (0x04)
            {
                 0x61, 0x62, 0x63, 0x64                           // abcd
            },

            Buffer (0x04)
            {
                 0x61, 0x62, 0x63, 0x64                           // abcd
            },

            /* Buffer, inside 64-bit Integer */

            Buffer (0x05)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65                     // abcde
            },

            Buffer (0x05)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65                     // abcde
            },

            Buffer (0x05)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65                     // abcde
            },

            Buffer (0x05)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65                     // abcde
            },

            /* Buffer, 64-bit Integer */

            Buffer (0x08)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32   // abcdef12
            },

            Buffer (0x08)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32   // abcdef12
            },

            Buffer (0x08)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32   // abcdef12
            },

            Buffer (0x08)
            {
                 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32   // abcdef12
            },

            /* Buffer, size exceeding result */

            Buffer (0x14)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x00, 0x00,  // 345678..
                /* 0010 */  0x00, 0x00, 0x00, 0x00                           // ....
            },

            Buffer (0x14)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x00, 0x00,  // 345678..
                /* 0010 */  0x00, 0x00, 0x00, 0x00                           // ....
            },

            Buffer (0x14)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x00, 0x00,  // 345678..
                /* 0010 */  0x00, 0x00, 0x00, 0x00                           // ....
            },

            Buffer (0x14)
            {
                /* 0000 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x31, 0x32,  // abcdef12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x00, 0x00,  // 345678..
                /* 0010 */  0x00, 0x00, 0x00, 0x00                           // ....
            }
        })
        Name (B000, Buffer (0x06)
        {
             0x61, 0x62, 0x63, 0x64, 0x65, 0x66               // abcdef
        })
        Name (B001, Buffer (0x08)
        {
             0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38   // 12345678
        })
        Local0 = B000 /* \M564.B000 */
        Local1 = B001 /* \M564.B001 */
        M562 (TS, Local0, Local1, P000)
        /* Source values are not corrupted */

        Local2 = ObjectType (Local0)
        If ((Local2 != 0x03))
        {
            ERR (TS, Z067, __LINE__, 0x00, 0x00, Local2, 0x03)
        }
        ElseIf ((Local0 != B000))
        {
            ERR (TS, Z067, __LINE__, 0x00, 0x00, Local0, B000)
        }

        Local2 = ObjectType (Local1)
        If ((Local2 != 0x03))
        {
            ERR (TS, Z067, __LINE__, 0x00, 0x00, Local2, 0x03)
        }
        ElseIf ((Local1 != B001))
        {
            ERR (TS, Z067, __LINE__, 0x00, 0x00, Local1, B001)
        }
    }

    /* arg0 - name of test */
    /* arg1 - Source1 */
    /* arg2 - Source2 */
    /* arg3 - results */
    Method (M562, 4, NotSerialized)
    {
        TS00 (Arg0)
        /* ============= With Result */
        /* ii,is,ib,ibf */
        /* si,ss,sb,sbf */
        /* bi,bs,bb,bbf */
        /* bfi,bfs,bfb,bfbf */
        /* i,i */
        II10 = Concatenate (Arg1, Arg2, II00) /* \II00 */
        M4C1 (Arg0, Arg3, 0x00, 0x01, 0x01, II00, II10)
        /* i,s */

        SS10 = Concatenate (Arg1, Arg2, II00) /* \II00 */
        M4C1 (Arg0, Arg3, 0x01, 0x01, 0x01, II00, SS10)
        /* i,b */

        BB80 = Concatenate (Arg1, Arg2, II00) /* \II00 */
        M4C1 (Arg0, Arg3, 0x02, 0x01, 0x01, II00, BB80)
        /* i,bf(i,i) */

        BF10 = Concatenate (Arg1, Arg2, II00) /* \II00 */
        M4C1 (Arg0, Arg3, 0x03, 0x01, 0x01, II00, BF10)
        /* i,bf(i,b) */

        BF11 = Concatenate (Arg1, Arg2, II00) /* \II00 */
        M4C1 (Arg0, Arg3, 0x04, 0x01, 0x01, II00, BF11)
        /* s,i */

        II10 = Concatenate (Arg1, Arg2, SS00) /* \SS00 */
        M4C1 (Arg0, Arg3, 0x05, 0x01, 0x01, SS00, II10)
        /* s,s */

        SS10 = Concatenate (Arg1, Arg2, SS00) /* \SS00 */
        M4C1 (Arg0, Arg3, 0x06, 0x01, 0x01, SS00, SS10)
        /* s,b */

        BB80 = Concatenate (Arg1, Arg2, SS00) /* \SS00 */
        M4C1 (Arg0, Arg3, 0x07, 0x01, 0x01, SS00, BB80)
        /* s,bf(i,i) */

        BF10 = Concatenate (Arg1, Arg2, SS00) /* \SS00 */
        M4C1 (Arg0, Arg3, 0x08, 0x01, 0x01, SS00, BF10)
        /* s,bf(i,b) */

        BF11 = Concatenate (Arg1, Arg2, SS00) /* \SS00 */
        M4C1 (Arg0, Arg3, 0x09, 0x01, 0x01, SS00, BF11)
        /* b,i */

        II10 = Concatenate (Arg1, Arg2, BB00) /* \BB00 */
        M4C1 (Arg0, Arg3, 0x0A, 0x01, 0x01, BB00, II10)
        /* b,s */

        SS10 = Concatenate (Arg1, Arg2, BB00) /* \BB00 */
        M4C1 (Arg0, Arg3, 0x0B, 0x01, 0x01, BB00, SS10)
        /* b,b */

        BB80 = Concatenate (Arg1, Arg2, BB00) /* \BB00 */
        M4C1 (Arg0, Arg3, 0x0C, 0x01, 0x01, BB00, BB80)
        /* b,bf(i,i) */

        BF10 = Concatenate (Arg1, Arg2, BB00) /* \BB00 */
        M4C1 (Arg0, Arg3, 0x0D, 0x01, 0x01, BB00, BF10)
        /* b,bf(i,b) */

        BF11 = Concatenate (Arg1, Arg2, BB00) /* \BB00 */
        M4C1 (Arg0, Arg3, 0x0E, 0x01, 0x01, BB00, BF11)
        /* bf(i,i),i */

        II10 = Concatenate (Arg1, Arg2, BF00) /* \BF00 */
        M4C1 (Arg0, Arg3, 0x0F, 0x01, 0x01, BF00, II10)
        /* bf(i,i),s */

        SS10 = Concatenate (Arg1, Arg2, BF00) /* \BF00 */
        M4C1 (Arg0, Arg3, 0x10, 0x01, 0x01, BF00, SS10)
        /* bf(i,i),b */

        BB80 = Concatenate (Arg1, Arg2, BF00) /* \BF00 */
        M4C1 (Arg0, Arg3, 0x11, 0x01, 0x01, BF00, BB80)
        /* bf(i,i),bf(i,i) */

        BF10 = Concatenate (Arg1, Arg2, BF00) /* \BF00 */
        M4C1 (Arg0, Arg3, 0x12, 0x01, 0x01, BF00, BF10)
        /* bf(i,i),bf(i,b) */

        BF11 = Concatenate (Arg1, Arg2, BF00) /* \BF00 */
        M4C1 (Arg0, Arg3, 0x13, 0x01, 0x01, BF00, BF11)
        /* bf(i,b),i */

        II10 = Concatenate (Arg1, Arg2, BF01) /* \BF01 */
        M4C1 (Arg0, Arg3, 0x14, 0x01, 0x01, BF01, II10)
        /* bf(i,b),s */

        SS10 = Concatenate (Arg1, Arg2, BF01) /* \BF01 */
        M4C1 (Arg0, Arg3, 0x15, 0x01, 0x01, BF01, SS10)
        /* bf(i,b),b */

        BB80 = Concatenate (Arg1, Arg2, BF01) /* \BF01 */
        M4C1 (Arg0, Arg3, 0x16, 0x01, 0x01, BF01, BB80)
        /* bf(i,b),bf(i,i) */

        BF10 = Concatenate (Arg1, Arg2, BF01) /* \BF01 */
        M4C1 (Arg0, Arg3, 0x17, 0x01, 0x01, BF01, BF10)
        /* bf(i,b),bf(i,b) */

        BF11 = Concatenate (Arg1, Arg2, BF01) /* \BF01 */
        M4C1 (Arg0, Arg3, 0x18, 0x01, 0x01, BF01, BF11)
        /* ============= Result omitted */
        /* ,i,s,b,bf */
        /* ,i */
        II10 = Concatenate (Arg1, Arg2)
        M4C1 (Arg0, Arg3, 0x19, 0x00, 0x01, 0x00, II10)
        /* ,s */

        SS10 = Concatenate (Arg1, Arg2)
        M4C1 (Arg0, Arg3, 0x1A, 0x00, 0x01, 0x00, SS10)
        /* ,b */

        BB80 = Concatenate (Arg1, Arg2)
        M4C1 (Arg0, Arg3, 0x1B, 0x00, 0x01, 0x00, BB80)
        /* ,bf(i,i) */

        BF10 = Concatenate (Arg1, Arg2)
        M4C1 (Arg0, Arg3, 0x1C, 0x00, 0x01, 0x00, BF10)
        /* b,bf(i,b) */

        BF11 = Concatenate (Arg1, Arg2)
        M4C1 (Arg0, Arg3, 0x1D, 0x00, 0x01, 0x00, BF11)
        /* ============= Store omitted */
        /* i,s,b,bf, */
        /* i, */
        Concatenate (Arg1, Arg2, II00) /* \II00 */
        M4C1 (Arg0, Arg3, 0x1E, 0x01, 0x00, II00, 0x00)
        /* s, */

        Concatenate (Arg1, Arg2, SS00) /* \SS00 */
        M4C1 (Arg0, Arg3, 0x1F, 0x01, 0x00, SS00, 0x00)
        /* b, */

        Concatenate (Arg1, Arg2, BB00) /* \BB00 */
        M4C1 (Arg0, Arg3, 0x20, 0x01, 0x00, BB00, 0x00)
        /* bf(i,i), */

        Concatenate (Arg1, Arg2, BF00) /* \BF00 */
        M4C1 (Arg0, Arg3, 0x21, 0x01, 0x00, BF00, 0x00)
        /* bf(i,b), */

        Concatenate (Arg1, Arg2, BF01) /* \BF01 */
        M4C1 (Arg0, Arg3, 0x22, 0x01, 0x00, BF01, 0x00)
        /* ============= Particular additional cases */
        /* Buffer Field, incomplete last byte */
        BF12 = Concatenate (Arg1, Arg2, BF02) /* \BF02 */
        M4C1 (Arg0, Arg3, 0x23, 0x01, 0x01, BF02, BF12)
        /* Buffer Field, incomplete extra byte */

        BF13 = Concatenate (Arg1, Arg2, BF03) /* \BF03 */
        M4C1 (Arg0, Arg3, 0x24, 0x01, 0x01, BF03, BF13)
        /* Buffer Field, size exceeding result */

        BF14 = Concatenate (Arg1, Arg2, BF04) /* \BF04 */
        M4C1 (Arg0, Arg3, 0x25, 0x01, 0x01, BF04, BF14)
        /* Buffer, inside 32-bit Integer */

        BB81 = Concatenate (Arg1, Arg2, BB01) /* \BB01 */
        M4C1 (Arg0, Arg3, 0x26, 0x01, 0x01, BB01, BB81)
        /* Buffer, 32-bit Integer */

        BB82 = Concatenate (Arg1, Arg2, BB02) /* \BB02 */
        M4C1 (Arg0, Arg3, 0x27, 0x01, 0x01, BB02, BB82)
        /* Buffer, inside 64-bit Integer */

        BB83 = Concatenate (Arg1, Arg2, BB03) /* \BB03 */
        M4C1 (Arg0, Arg3, 0x28, 0x01, 0x01, BB03, BB83)
        /* Buffer, 64-bit Integer */

        BB84 = Concatenate (Arg1, Arg2, BB04) /* \BB04 */
        M4C1 (Arg0, Arg3, 0x29, 0x01, 0x01, BB04, BB84)
        /* Buffer, size exceeding result */

        BB85 = Concatenate (Arg1, Arg2, BB05) /* \BB05 */
        M4C1 (Arg0, Arg3, 0x2A, 0x01, 0x01, BB05, BB85)
    }

    /* ConcatenateResTemplate (rtb, rtb, Result) => Buffer */

    Method (M504, 1, Serialized)
    {
        Name (OP, 0x04)
        Name (TS, "m504")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* CondRefOf (any, Result) => Boolean */

    Method (M505, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m505")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* CopyObject (any, Destination) => DataRefObject */

    Method (M506, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m506")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* Decrement (int) => Integer */

    Method (M507, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m507")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* DerefOf ({ref|str}) => Object */

    Method (M508, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m508")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* Divide (int, int, Remainder, Result) => Integer */

    Method (M509, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m509")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* FindSetLeftBit (int, Result) => Integer */

    Method (M511, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m511")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* FindSetRightBit (int, Result) => Integer */

    Method (M512, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m512")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* FromBCD (int, Result) => Integer */

    Method (M513, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m513")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* Increment (int) => Integer */

    Method (M514, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m514")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* Index ({str|buf|pkg}, int, Destination) => ObjectReference */

    Method (M515, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m515")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* LAnd (int, int) => Boolean */

    Method (M516, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m516")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* LEqual ({int|str|buf}, {int|str|buf}) => Boolean */

    Method (M517, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m517")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* LGreater ({int|str|buf}, {int|str|buf}) => Boolean */

    Method (M518, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m518")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* LGreaterEqual ({int|str|buf}, {int|str|buf}) => Boolean */

    Method (M519, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m519")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* LLess ({int|str|buf}, {int|str|buf}) => Boolean */

    Method (M520, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m520")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* LLessEqual ({int|str|buf}, {int|str|buf}) => Boolean */

    Method (M521, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m521")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* LNot (int) => Boolean */

    Method (M522, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m522")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* LNotEqual ({int|str|buf}, {int|str|buf}) => Boolean */

    Method (M523, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m523")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* LOr (int, int) => Boolean */

    Method (M524, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m524")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* Match (pkg, byt, int, byt, int, int) => Ones | Integer */

    Method (M525, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m525")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* Mid ({str|buf}, int, int, Result) => Buffer or String */

    Method (M526, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m526")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* Mod (int, int, Result) => Integer */

    Method (M527, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m527")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* Multiply (int, int, Result) => Integer */

    Method (M528, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m528")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* NAnd (int, int, Result) => Integer */

    Method (M529, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m529")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* NOr (int, int, Result) => Integer */

    Method (M530, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m530")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* Not (int, Result) => Integer */

    Method (M531, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m531")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* ObjectType (any) => Integer */

    Method (M532, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m532")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* Or (int, int, Result) => Integer */

    Method (M533, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m533")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* RefOf (any) => ObjectReference */

    Method (M534, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m534")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* Return ({any|ref}) */

    Method (M537, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m537")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* ShiftLeft (int, int, Result) => Integer */

    Method (M538, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m538")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* ShiftRight (int, int, Result) => Integer */

    Method (M539, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m539")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* SizeOf ({int|str|buf|pkg}) => Integer */

    Method (M541, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m541")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* Store (any, Destination) => DataRefObject */

    Method (M544, 1, Serialized)
    {
        Name (TS, "m544")
        TS00 (TS)
        Name (SS00, "DEF")
        SS00 = "ABC"
        Local0 = ObjectType (SS00)
        If ((Local0 != 0x02))
        {
            ERR (TS, Z067, __LINE__, 0x00, 0x00, Local0, 0x02)
        }
        ElseIf ((SS00 != "ABC"))
        {
            ERR (TS, Z067, __LINE__, 0x00, 0x00, SS00, "ABC")
        }

        Name (B000, Buffer (0xC8){})
        Name (B001, Buffer (0x06)
        {
             0x41, 0x42, 0x43, 0x44, 0x45, 0x46               // ABCDEF
        })
        B000 = "ABCDEF"
        Local0 = ObjectType (B000)
        Local1 = SizeOf (B000)
        If ((Local0 != 0x03))
        {
            ERR (TS, Z067, __LINE__, 0x00, 0x00, Local0, 0x03)
        }
        ElseIf ((Local1 != 0x06))
        {
            ERR (TS, Z067, __LINE__, 0x00, 0x00, Local1, 0x06)
        }
        ElseIf ((B000 != B001))
        {
            ERR (TS, Z067, __LINE__, 0x00, 0x00, B000, B001)
        }
    }

    /* Subtract (int, int, Result) => Integer */

    Method (M545, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m545")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* ToBCD (int, Result) => Integer */

    Method (M546, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m546")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* ToBuffer ({int|str|buf}, Result) => Buffer */

    Method (M547, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m547")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* ToDecimalString ({int|str|buf}, Result) => String */

    Method (M548, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m548")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* ToHexString ({int|str|buf}, Result) => String */

    Method (M549, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m549")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* ToInteger ({int|str|buf}, Result) => Integer */

    Method (M550, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m550")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* ToString (buf, int, Result) => String */

    Method (M551, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m551")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* Wait (evt, int) => Boolean */

    Method (M552, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m552")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    /* XOr (int, int, Result) => Integer */

    Method (M553, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m553")
        TS00 (TS)
        If (Arg0){}
        Else
        {
        }
    }

    Method (M560, 1, NotSerialized)
    {
        /*
         m500(arg0)
         m501(arg0)
         m502(arg0)
         m503(arg0)
         m504(arg0)
         m505(arg0)
         m506(arg0)
         m507(arg0)
         m508(arg0)
         m509(arg0)
         m511(arg0)
         m512(arg0)
         m513(arg0)
         m514(arg0)
         m515(arg0)
         m516(arg0)
         m517(arg0)
         m518(arg0)
         m519(arg0)
         m520(arg0)
         m521(arg0)
         m522(arg0)
         m523(arg0)
         m524(arg0)
         m525(arg0)
         m526(arg0)
         m527(arg0)
         m528(arg0)
         m529(arg0)
         m530(arg0)
         m531(arg0)
         m532(arg0)
         m533(arg0)
         m534(arg0)
         m537(arg0)
         m538(arg0)
         m539(arg0)
         m541(arg0)
         m544(arg0)
         m545(arg0)
         m546(arg0)
         m547(arg0)
         m548(arg0)
         m549(arg0)
         m550(arg0)
         m551(arg0)
         m552(arg0)
         m553(arg0)
         */
        M500 (Arg0)
        M501 (Arg0)
        M502 (Arg0)
        M503 (Arg0)
        M544 (Arg0)
    }
