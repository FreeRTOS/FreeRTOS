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
     * Convert Buffer To String
     */
    Name (Z048, 0x30)
    Name (P330, Package (0x0D)
    {
        Buffer (0x08)
        {
             0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF   // ........
        },

        Buffer (0xC8)
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
            /* 00C0 */  0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7, 0xC8   // ........
        },

        Buffer (0x08)
        {
             0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF   // ........
        },

        Buffer (0x80)
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
            /* 0078 */  0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x7F, 0x80   // yz{|}~..
        },

        Buffer (0x08)
        {
             0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF   // ........
        },

        Buffer (0x10)
        {
            /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
            /* 0008 */  0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10   // ........
        },

        Buffer (0x08)
        {
             0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF   // ........
        },

        Buffer (0x08)
        {
             0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08   // ........
        },

        Buffer (0x08)
        {
             0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF   // ........
        },

        Buffer (0x04)
        {
             0x01, 0x02, 0x03, 0x04                           // ....
        },

        Buffer (0x08)
        {
             0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF   // ........
        },

        Buffer (0x01)
        {
             0x01                                             // .
        },

        Buffer (0x08)
        {
             0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF   // ........
        }
    })
    Name (B330, Buffer (0x06)
    {
         0xC8, 0x80, 0x10, 0x08, 0x04, 0x01               // ......
    })
    /* Init buffer with the symbols 1-255 */

    Method (M303, 2, NotSerialized)
    {
        Local0 = 0x00
        While ((Local0 < Arg1))
        {
            Local1 = ((Local0 + 0x01) % 0x0100)
            Arg0 [Local0] = Local1
            Local0++
        }
    }

    /* Verify the contents of result string */

    Method (M305, 5, NotSerialized)
    {
        Local0 = 0x00
        While ((Local0 < Arg2))
        {
            Local1 = ((Local0 + 0x01) % 0x0100)
            If ((DerefOf (Arg1 [Local0]) != Local1))
            {
                ERR (Arg0, Z048, __LINE__, 0x00, 0x00, Local0, Arg4)
            }

            Local0++
        }
    }

    /* Verify type, length of the obtained string, call to m305 */

    Method (M307, 5, NotSerialized)
    {
        If ((ObjectType (Arg1) != 0x02))
        {
            ERR (Arg0, Z048, __LINE__, 0x00, 0x00, Arg2, "Type")
        }
        ElseIf ((SizeOf (Arg1) != Arg2))
        {
            ERR (Arg0, Z048, __LINE__, 0x00, 0x00, Arg2, "Sizeof")
        }
        Else
        {
            M305 (Arg0, Arg1, Arg2, Arg3, Arg4)
        }
    }

    /* Check the surrounding control buffers are safe */

    Method (M309, 3, NotSerialized)
    {
        /* control buffer */

        Local1 = DerefOf (P330 [Arg1])
        Local0 = 0x00
        While ((Local0 < 0x08))
        {
            If ((DerefOf (Local1 [Local0]) != 0xFF))
            {
                ERR (Arg0, Z048, __LINE__, 0x00, 0x00, Local0, "buf8")
            }

            Local0++
        }
    }

    /* Check all positions of null character (0-200) */

    Method (M30A, 1, Serialized)
    {
        Name (LENS, Buffer (0x0A)
        {
            /* 0000 */  0xC8, 0xC7, 0x81, 0x80, 0x7F, 0x09, 0x08, 0x07,  // ........
            /* 0008 */  0x01, 0x00                                       // ..
        })
        Name (BUF0, Buffer (0xFF){})
        /* Buffer (255 bytes) initialized with non-zero bytes */

        M303 (BUF0, 0xFF)
        Local1 = 0x00
        While ((Local1 < 0x0A))
        {
            /* Fill zero byte in position specified by LENS */

            Local0 = DerefOf (LENS [Local1])
            Local5 = DerefOf (BUF0 [Local0])
            BUF0 [Local0] = 0x00
            /* The contents of buffer is not more changed in checkings below */
            /* Checking for unspecified Length parameter */
            /* Invoke ToString without Length */
            Local2 = ToString (BUF0, Ones)
            M307 (Arg0, Local2, Local0, 0x01, "Omit")
            /* Invoke ToString with Ones */

            ToString (BUF0, Ones, Local2)
            M307 (Arg0, Local2, Local0, 0x02, "Ones")
            /* Checking for particular values of Length parameter (0, 32, 64...) */

            Local3 = 0x00 /* Length */
            While ((Local3 < 0x0191))
            {
                Local4 = Local0 /* expected size */
                If ((Local3 < Local4))
                {
                    Local4 = Local3
                }

                ToString (BUF0, Local3, Local2)
                M307 (Arg0, Local2, Local4, 0x03, "Size")
                Local3 += 0x20
            }

            /* Restore position specified by LENS */

            BUF0 [Local0] = Local5
            Local1++
        }
    }

    Method (M333, 1, NotSerialized)
    {
        Local0 = 0x00
        Local0 = ToString (DerefOf (Arg0), Ones)
        Debug = Local0
    }

    /* Check Buffer->Length effective condition. */
    /* Don't put null characters. Check the surrounding */
    /* control buffers are safe. */
    Method (M30B, 1, Serialized)
    {
        Name (LOC8, 0x00)
        Local5 = 0x00    /* index of control buffer 1 */
        While ((LOC8 < 0x06))
        {
            /* Choose the buffer from package */

            Local0 = DerefOf (B330 [LOC8])   /* length */
            Local1 = (LOC8 * 0x02)           /* index of a buffer */
            Local1 += 0x01
            Local6 = (Local1 + 0x01)              /* index of control buffer 2 */
            Store (P330 [Local1], Local4)      /* ref to test buffer */
            /* Checking for unspecified Length parameter */
            /* Invoke ToString without Length */
            Local2 = ToString (DerefOf (Local4), Ones)
            M307 (Arg0, Local2, Local0, 0x04, "Omit")
            M309 (Arg0, Local5, 0x04)   /* check control buffers */
            M309 (Arg0, Local6, 0x04)
            /* Invoke ToString with Ones */

            ToString (DerefOf (Local4), Ones, Local2)
            M307 (Arg0, Local2, Local0, 0x05, "Ones")
            M309 (Arg0, Local5, 0x05)   /* check control buffers */
            M309 (Arg0, Local6, 0x05)
            /* Checking for particular values of Length parameter */
            /* exceeding (by 0, 1, 2, 3, ... 8) the actual lengths of Buffer */
            Local7 = (Local0 + 0x09) /* Max. Length */
            Local3 = Local0 /* Length */
            While ((Local3 < Local7))
            {
                ToString (DerefOf (Local4), Local3, Local2)
                M307 (Arg0, Local2, Local0, 0x06, "Size")
                M309 (Arg0, Local5, 0x06)   /* check control buffers */
                M309 (Arg0, Local6, 0x06)
                Local3++
            }

            Local5 = Local6
            LOC8++
        }
    }

    /* Check zero length buffer, and, in passing, */
    /* dynamically allocated buffers. */
    Method (M30C, 1, Serialized)
    {
        Name (LENS, Buffer (0x04)
        {
             0xC8, 0xC7, 0x01, 0x00                           // ....
        })
        Local1 = 0x00
        While ((Local1 < 0x04))
        {
            /* Allocate buffer dynamically and initialize it, */
            /* don't put null characters. */
            Local0 = DerefOf (LENS [Local1])
            Local4 = Buffer (Local0){}
            M303 (Local4, Local0)
            /* Checking for unspecified Length parameter */
            /* Invoke ToString without Length */
            Local2 = ToString (Local4, Ones)
            M307 (Arg0, Local2, Local0, 0x07, "Omit")
            /* Invoke ToString with Ones */

            ToString (Local4, Ones, Local2)
            M307 (Arg0, Local2, Local0, 0x08, "Ones")
            /* Allocate buffer of +1 size and put null characters */
            /* into the last byte. */
            Local4 = Buffer ((Local0 + 0x01)){}
            M303 (Local4, Local0)
            Local4 [Local0] = 0x00
            /* Invoke ToString without Length */

            Local2 = ToString (Local4, Ones)
            M307 (Arg0, Local2, Local0, 0x09, "Omit")
            /* Invoke ToString with Ones */

            ToString (Local4, Ones, Local2)
            M307 (Arg0, Local2, Local0, 0x0A, "Ones")
            Local1++
        }
    }

    /* Run-method */

    Method (TOS0, 0, Serialized)
    {
        Debug = "TEST: TOS0, Convert Buffer To String"
        M30A (__METHOD__)
        M30B (__METHOD__)
        M30C (__METHOD__)
    }
