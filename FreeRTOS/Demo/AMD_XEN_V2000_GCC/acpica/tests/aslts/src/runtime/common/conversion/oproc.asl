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
     SEE: ????????????
     1) Add 0 into the middle of any Buffer
     2) Do BOTH directions for Concatenation:
     - First argument - String
     - First argument - Buffer
     3) Extend the test, if possible, for all the operators
     4) add method m480 with the different objects creations.
     5) change Name(ss08, "1234567890abCdeF")
     to     Name(ss08, "1234567830abCdeF")
     6) do the same as m480() but use LocalX instead ArgX
     in Operators invocations:
     Store(Add(Local0, Local1, Local7), local7)
     */
    /* Methods for Conversion tests */
    /* */
    /* (low number of available arguments {Arg0-Arg6} complicates algorithms). */
    /* */
    /* Currently from the mask of exceptions to be forced are excluded bits */
    /* corresponding to the following types ("don't know how" have to be added): */
    /* */
    /* - Method        (don't know how) */
    /* - Thermal Zones (don't know how) */
    /* - DDB Handle    (don't know how) */
    /* - Debug Object  (impossible, Compiler refuses) */
    /* - Uninitialized (update needed, currently the test is implemented incorrectly. */
    /*                  Uninitialized type have to be passed immediately as operands */
    /*                  in m480). */
    /* */
    /* Currently excluded from all the total scales of unacceptable types */
    /* (to be added later): */
    /* */
    /*	0x0100 - Method */
    /*	0x2000 - Thermal Zone */
    /*	0x8000 - DDB Handle */
    /* */
    /* Total scale of acceptable types: */
    /* */
    /*	int - 0xc02e - Integer, String, Buffer, Field Unit, Buffer Field, DDB Handle */
    /* */
    /* NOTE: many entries are commented not to cause crashes. */
    /*       Have to be uncommented after ACPICA will be fixed. */
    /* */
    Name (Z064, 0x40)
    /* Commutative two operands operation */
    /* (CAUTION: don't forget to clean it) */
    Name (COM2, 0x00)
    /* Flags exception expected */
    /* (needed due to the lack of Arguments number) */
    Name (FLG0, 0x19283746)
    /* Flag - verify result with the contents of Package */

    Name (FLG1, 0x00)
    /* Package contains benchmarks of results */

    Name (PKG0, Package (0x01)
    {
        0x10000001
    })
    Name (PKG1, Package (0x01)
    {
        0x11111111
    })
    Name (PKG2, Package (0x01)
    {
        0x22222222
    })
    Name (DF00, 0x00)
    Name (DF01, 0x00)
    Name (DF02, 0x00)
    Name (DF03, 0x00)
    Name (DF04, 0x00)
    Event (E000)
    Mutex (MX00, 0x00)
    Name (I000, 0x58765432)
    Name (I001, 0xABCDEFABAABBCCDD)
    Name (S000, "qwrt")
    Name (B001, Buffer (0x03)
    {
         0x91, 0x22, 0x83                                 // .".
    })
    Name (P08B, Package (0x02)
    {
        0x13,
        0x1B
    })
    Device (DV00)
    {
    }

    Method (M4A3, 0, NotSerialized)
    {
        Return (0x00)
    }

    OperationRegion (RG00, SystemMemory, 0x0100, 0x0100)
    Field (RG00, ByteAcc, NoLock, Preserve)
    {
        FR20,   7
    }

    PowerResource (PWR0, 0x01, 0x0000)
    {
        Method (M000, 0, NotSerialized)
        {
            Return (0x00)
        }
    }

    Processor (PRC0, 0x00, 0xFFFFFFFF, 0x00){}
    Name (B002, Buffer (0x64){})
    CreateDWordField (B002, 0x03, BFZ0)
    /* Return object of required type */
    /* */
    /* arg0 - type of object */
    Method (M484, 1, Serialized)
    {
        Name (TS, "m484")
        Event (E001)
        Mutex (MX01, 0x00)
        Name (SS01, "svnmjkl")
        Name (SS02, "1234zyq")
        Name (SS03, "abcdefzyq")
        Name (SS04, "9876")
        Name (SS05, "aBcD")
        Name (SS06, "1234567890987654")
        Name (SS07, "daFeCBaabbddffee")
        Name (SS08, "1234567890abCdeF")
        Name (SS09, "FdeAcb0132547698")
        Name (SS0A, "12345678909876540")
        Name (SS0B, "fdeacb01325476980")
        Name (SS0C, "123456789011223344556677889998765432199983337744")
        Name (SS0D, "abcdefaAbbccddeeffffeeddccaabbddeeffaaaabbbbeeefffdd")
        Name (SS0E, "1234567890abcdef9876543210fedbca1122334455667788fdeacb")
        Name (SS0F, "defa1234567890abcdef9876543210fedbca1122334455667788fdeacb")
        Name (SS10, "123456789011223344556677889998765432199983337744z")
        Name (SS11, "0xF1dAB98e0D794Bc5")
        Name (BB01, Buffer (0x01)
        {
             0x80                                             // .
        })
        Name (BB02, Buffer (0x02)
        {
             0x81, 0x82                                       // ..
        })
        Name (BB03, Buffer (0x04)
        {
             0x83, 0x84, 0x85, 0x86                           // ....
        })
        Name (BB04, Buffer (0x05)
        {
             0x87, 0x98, 0x99, 0x9A, 0x9B                     // .....
        })
        Name (BB05, Buffer (0x08)
        {
             0x9C, 0x9D, 0x9E, 0x9F, 0xA0, 0xA1, 0xA2, 0xA3   // ........
        })
        Name (BB06, Buffer (0x09)
        {
            /* 0000 */  0xA4, 0xA5, 0xA6, 0xA7, 0xB8, 0xB9, 0xBA, 0xBB,  // ........
            /* 0008 */  0xBC                                             // .
        })
        Name (BB07, Buffer (0xC8)
        {
            /* 0000 */  0x91, 0x92, 0x93, 0x94, 0x5F, 0x60, 0x61, 0x62,  // ...._`ab
            /* 0008 */  0x63, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10,  // c.......
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
        })
        Name (BB08, Buffer (0x0101)
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
            /* 00C8 */  0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF, 0xD0,  // ........
            /* 00D0 */  0xD1, 0xD2, 0xD3, 0xD4, 0xD5, 0xD6, 0xD7, 0xD8,  // ........
            /* 00D8 */  0xD9, 0xDA, 0xDB, 0xDC, 0xDD, 0xDE, 0xDF, 0xE0,  // ........
            /* 00E0 */  0xE1, 0xE2, 0xE3, 0xE4, 0xE5, 0xE6, 0xE7, 0xE8,  // ........
            /* 00E8 */  0xE9, 0xEA, 0xEB, 0xEC, 0xED, 0xEE, 0xEF, 0xF0,  // ........
            /* 00F0 */  0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6, 0xF7, 0xF8,  // ........
            /* 00F8 */  0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE, 0xFF, 0x00,  // ........
            /* 0100 */  0x01                                             // .
        })
        /* Field Units */

        OperationRegion (R001, SystemMemory, 0x0100, 0x0100)
        Field (R001, ByteAcc, NoLock, Preserve)
        {
            F001,   3,
            F002,   8,
            F003,   16,
            F004,   32,
            F005,/*33 */   33,
            F006,/*63 */   63,
            F007,/*64 */   64,
            F008,/*65 */   65,
            F009,   127,
            F00A,   257
                /* f00b, 201*8, do it also */
        }

        /* Buffer Fields */

        Name (BB09, Buffer (0xC8){})
        CreateField (BB09, 0x01, 0x03, BF01)
        CreateField (BB09, 0x04, 0x08, BF02)
        CreateField (BB09, 0x0C, 0x10, BF03)
        CreateField (BB09, 0x1C, 0x20, BF04)
        CreateField (BB09, 0x3C, 0x21, BF05)
        CreateField (BB09, 0x5D, 0x3F, BF06)/*93 */
        CreateField (BB09, 0x9C, 0x40, BF07)/*156 */
        CreateField (BB09, 0xDC, 0x41, BF08)/*220 */
        CreateField (BB09, 0x011D, 0x7F, BF09)/*285 */
        CreateField (BB09, 0x019C, 0x0101, BF0A)/*412 */
        /*	CreateField(bb09, xxx, 201*8, bf0b) */

        CreateDWordField (BB09, 0x97, BF0B)
        /*/////////////////////////////////////////////////////////////////// */

        FR20 = 0xFF
        F001 = 0xFF
        F002 = 0x8A8B8C8D
        F003 = 0x8A8B8C8D
        F004 = 0x8A8B8C8D
        F005 = Buffer (0x05)
            {
                 0xFF, 0xFF, 0xFF, 0xFF, 0xFF                     // .....
            }
        F006 = Buffer (0x09)
            {
                /* 0000 */  0x58, 0x46, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // XF7.....
                /* 0008 */  0xFA                                             // .
            }
        F007 = Buffer (0x09)
            {
                /* 0000 */  0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0xFA                                             // .
            }
        F008 = Buffer (0x09)
            {
                /* 0000 */  0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0xFA                                             // .
            }
        F009 = Buffer (0x09)
            {
                /* 0000 */  0x82, 0x34, 0x56, 0x78, 0x90, 0xAB, 0xCD, 0xEF,  // .4Vx....
                /* 0008 */  0x55                                             // U
            }
        F00A = Buffer (0x09)
            {
                /* 0000 */  0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12, 0xCD, 0x52,  // .......R
                /* 0008 */  0x87                                             // .
            }
        BFZ0 = 0x918654AB
        BF01 = 0xFF
        BF02 = 0x8A8B8C8D
        BF03 = 0x8A8B8C8D
        BF04 = 0x8A8B8C8D
        BF05 = Buffer (0x05)
            {
                 0xFF, 0xFF, 0xFF, 0xFF, 0xFF                     // .....
            }
        BF06 = Buffer (0x09)
            {
                /* 0000 */  0x58, 0x46, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // XF7.....
                /* 0008 */  0xFA                                             // .
            }
        BF07 = Buffer (0x09)
            {
                /* 0000 */  0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0xFA                                             // .
            }
        BF08 = Buffer (0x09)
            {
                /* 0000 */  0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0xFA                                             // .
            }
        BF09 = Buffer (0x09)
            {
                /* 0000 */  0x82, 0x34, 0x56, 0x78, 0x90, 0xAB, 0xCD, 0xEF,  // .4Vx....
                /* 0008 */  0x55                                             // U
            }
        BF0A = Buffer (0x09)
            {
                /* 0000 */  0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12, 0xCD, 0x52,  // .......R
                /* 0008 */  0x87                                             // .
            }
        BF0B = 0xA2B3C4D5
        /*/////////////////////////////////////////////////////////////////// */

        Name (PP01, Package (0x01)
        {
            0x13
        })
        Device (DV01)
        {
        }

        Method (M001, 0, NotSerialized)
        {
            Return (0x00)
        }

        OperationRegion (R002, SystemMemory, 0x0100, 0x0100)
        PowerResource (PWR1, 0x01, 0x0000)
        {
            Method (M000, 0, NotSerialized)
            {
                Return (0x00)
            }
        }

        Processor (PR01, 0x00, 0xFFFFFFFF, 0x00){}
        Local7 = 0x00
        Switch (ToInteger (Arg0))
        {
            /* Uninitialized */
            /*
             * case (0x000) {
             * }
             */
            /* Integers */
            Case (0x0100)
            {
                Local7 = I000 /* \I000 */
            }
            Case (0x0101)
            {
                Local7 = I001 /* \I001 */
            }
            Case (0x0102)
            {
                Local7 = 0x12345678
            }
            Case (0x0103)
            {
                Local7 = 0xABEDF18942345678
            }
            Case (0x0104)
            {
                Local7 = Zero
            }
            Case (0x0105)
            {
                Local7 = One
            }
            Case (0x0106)
            {
                Local7 = Ones
            }
            Case (0x0107)
            {
                Local7 = Revision
            }
            Case (0x0108)
            {
                Local7 = 0x0123
            }
            Case (0x0109)
            {
                Local7 = 0x0B
            }
            Case            /* Strings */

 (0x0200)
            {
                Local7 = S000 /* \S000 */
            }
            Case (0x0201)
            {
                Local7 = SS01 /* \M484.SS01 */
            }
            Case (0x0202)
            {
                Local7 = SS02 /* \M484.SS02 */
            }
            Case (0x0203)
            {
                Local7 = SS03 /* \M484.SS03 */
            }
            Case (0x0204)
            {
                Local7 = SS04 /* \M484.SS04 */
            }
            Case (0x0205)
            {
                Local7 = SS05 /* \M484.SS05 */
            }
            Case (0x0206)
            {
                Local7 = SS06 /* \M484.SS06 */
            }
            Case (0x0207)
            {
                Local7 = SS07 /* \M484.SS07 */
            }
            Case (0x0208)
            {
                Local7 = SS08 /* \M484.SS08 */
            }
            Case (0x0209)
            {
                Local7 = SS09 /* \M484.SS09 */
            }
            Case (0x020A)
            {
                Local7 = SS0A /* \M484.SS0A */
            }
            Case (0x020B)
            {
                Local7 = SS0B /* \M484.SS0B */
            }
            Case (0x020C)
            {
                Local7 = SS0C /* \M484.SS0C */
            }
            Case (0x020D)
            {
                Local7 = SS0D /* \M484.SS0D */
            }
            Case (0x020E)
            {
                Local7 = SS0E /* \M484.SS0E */
            }
            Case (0x020F)
            {
                Local7 = SS0F /* \M484.SS0F */
            }
            Case (0x0210)
            {
                Local7 = SS10 /* \M484.SS10 */
            }
            Case (0x0211)
            {
                Local7 = SS11 /* \M484.SS11 */
            }
            Case            /* Buffers */

 (0x0300)
            {
                Local7 = B001 /* \B001 */
            }
            Case (0x0301)
            {
                Local7 = BB01 /* \M484.BB01 */
            }
            Case (0x0302)
            {
                Local7 = BB02 /* \M484.BB02 */
            }
            Case (0x0303)
            {
                Local7 = BB03 /* \M484.BB03 */
            }
            Case (0x0304)
            {
                Local7 = BB04 /* \M484.BB04 */
            }
            Case (0x0305)
            {
                Local7 = BB05 /* \M484.BB05 */
            }
            Case (0x0306)
            {
                Local7 = BB06 /* \M484.BB06 */
            }
            Case (0x0307)
            {
                Local7 = BB07 /* \M484.BB07 */
            }
            Case (0x0308)
            {
                Local7 = BB08 /* \M484.BB08 */
            }
            Case            /* Packages */

 (0x0400)
            {
                Local7 = P08B /* \P08B */
            }
            Case (0x0401)
            {
                Local7 = PP01 /* \M484.PP01 */
            }
            Case            /* Field Units */

 (0x0500)
            {
                Local7 = FR20 /* \FR20 */
            }
            Case (0x0501)
            {
                Local7 = F001 /* \M484.F001 */
            }
            Case (0x0502)
            {
                Local7 = F002 /* \M484.F002 */
            }
            Case (0x0503)
            {
                Local7 = F003 /* \M484.F003 */
            }
            Case (0x0504)
            {
                Local7 = F004 /* \M484.F004 */
            }
            Case (0x0505)
            {
                Local7 = F005 /* \M484.F005 */
            }
            Case (0x0506)
            {
                Local7 = F006 /* \M484.F006 */
            }
            Case (0x0507)
            {
                Local7 = F007 /* \M484.F007 */
            }
            Case (0x0508)
            {
                Local7 = F008 /* \M484.F008 */
            }
            Case (0x0509)
            {
                Local7 = F009 /* \M484.F009 */
            }
            Case (0x050A)
            {
                Local7 = F00A /* \M484.F00A */
            }
            Case            /*
             // Removed 09/2015: iASL now disallows these stores
             // Devices
             case (0x600) {
             Store(dv00, Local7)
             }
             case (0x601) {
             Store(dv01, Local7)
             }
             // Events
             case (0x700) {
             Store(e000, Local7)
             }
             case (0x701) {
             Store(e001, Local7)
             }
             // Methods
             case (0x800) {
             Store(m4a3, Local7)
             }
             case (0x801) {
             Store(m001, Local7)
             }
             // Mutexes
             case (0x900) {
             Store(mx00, Local7)
             }
             case (0x901) {
             Store(mx01, Local7)
             }
             // Operation Regions
             case (0xa00) {
             Store(rg00, Local7)
             }
             case (0xa01) {
             Store(r001, Local7)
             }
             case (0xa02) {
             Store(r002, Local7)
             }
             // Power Resources
             case (0xb00) {
             Store(pwr0, Local7)
             }
             case (0xb01) {
             Store(pwr1, Local7)
             }
             // Processor
             case (0xc00) {
             Store(prc0, Local7)
             }
             case (0xc01) {
             Store(pr01, Local7)
             }
             // Thermal Zones
             */
            /*
             * case (0xd00) {
             *		Store(Debug, Local7)
             * }
             */
            /* Buffer Field */
 (0x0E00)
            {
                Local7 = BFZ0 /* \BFZ0 */
            }
            Case (0x0E01)
            {
                Local7 = BF01 /* \M484.BF01 */
            }
            Case (0x0E02)
            {
                Local7 = BF02 /* \M484.BF02 */
            }
            Case (0x0E03)
            {
                Local7 = BF03 /* \M484.BF03 */
            }
            Case (0x0E04)
            {
                Local7 = BF04 /* \M484.BF04 */
            }
            Case (0x0E05)
            {
                Local7 = BF05 /* \M484.BF05 */
            }
            Case (0x0E06)
            {
                Local7 = BF06 /* \M484.BF06 */
            }
            Case (0x0E07)
            {
                Local7 = BF07 /* \M484.BF07 */
            }
            Case (0x0E08)
            {
                Local7 = BF08 /* \M484.BF08 */
            }
            Case (0x0E09)
            {
                Local7 = BF09 /* \M484.BF09 */
            }
            Case (0x0E0A)
            {
                Local7 = BF0A /* \M484.BF0A */
            }
            Case (0x0E0B)
            {
                Local7 = BF0B /* \M484.BF0B */
            }
            /* DDB Handle */
            /*
             * case (0xf00) {
             *		Store(Debug, Local7)
             * }
             */
            /* Debug Object */
            /*
             * case (0x1000) {
             *		Store(Debug, Local7)
             * }
             */
            Default
            {
                If ((Arg0 != 0x00))
                {
                    ERR ("----------- ERROR, m484: incorrect Arg0:", Z064, 0x023D, 0x00, 0x00, 0x00, 0x00)
                    Debug = Arg0
                }
            }

        }

        Return (Local7)
    }

    /* arg0 - opcode of operation */
    /* arg1 - type of 0-th argument */
    /* arg2 - type of 1-th argument */
    /* arg3 - type of 2-th argument */
    /* arg4 - type of 3-th argument */
    /* arg5 - type of 4-th argument */
    /* arg6 - {Ones - flag of exception, otherwise - index of result pair} */
    Method (M485, 7, Serialized)
    {
        If (0x00)
        {
            Debug = "##################################################################"
            Debug = Arg6
        }

        Name (TS, "m485")
        Name (EX00, 0x00)
        Name (TMP0, 0x00)
        If ((Arg6 == FLG0))
        {
            EX00 = 0x01
        }
        Else
        {
            Local5 = M48C (PKG1, Arg6)
            Local7 = ObjectType (Local5)
            If ((Local7 == 0x02))
            {
                If ((Local5 == "Exc"))
                {
                    EX00 = 0x01
                }
            }
        }

        Local7 = 0x00
        /* m482: */
        /* */
        /* arg0-arg4 - parameters of operators */
        /* arg5      - miscellaneous */
        /* arg6      - opcode of operation */
        /*
         * //// ?????????????????????????
         * Uninitialized data should be passed to the operators immediately
         * in the m480 but not here to these Store operations!!!!!!!!!!!!!!
         * But this will a few complicate m480 !!!!!!!!!!!!!!!!!!!!!!!!!!!!
         * //// ?????????????????????????
         */
        /* Parameters (if not to save them Uninitialized) */
        If ((Arg1 != 0x0FFF))
        {
            Local0 = M484 (Arg1)
        }

        If ((Arg2 != 0x0FFF))
        {
            Local1 = M484 (Arg2)
        }

        If ((Arg3 != 0x0FFF))
        {
            Local2 = M484 (Arg3)
        }

        If ((Arg4 != 0x0FFF))
        {
            Local3 = M484 (Arg4)
        }

        If ((Arg5 != 0x0FFF))
        {
            Local4 = M484 (Arg5)
        }

        If (EX00)
        {
            TMP0 = FLG2 /* \FLG2 */
            CH03 (TS, Z064, __LINE__, 0x00, 0x00)
        }

        Local7 = M482 (Local0, Local1, Local2, Local3, Local4, TMP0, Arg0)
        If (EX00)
        {
            CH04 (__METHOD__, 0x00, 0xFF, Z064, __LINE__, 0x00, 0x00)
        }
        ElseIf (FLG1)
        {
            /* Verify the first result */

            M489 (TS, Local7, Local5)
        }

        If (COM2)
        {
            /* The same operation but the first two arguments interchange */

            If ((Arg6 != FLG0))
            {
                If ((COM2 == 0x02))
                {
                    EX00 = 0x00
                    Local5 = M48C (PKG2, Arg6)
                    Local7 = ObjectType (Local5)
                    If ((Local7 == 0x02))
                    {
                        If ((Local5 == "Exc"))
                        {
                            EX00 = 0x01
                        }
                    }
                }
            }

            If (EX00)
            {
                CH03 (TS, Z064, __LINE__, 0x00, 0x00)
            }

            Local7 = M482 (Local1, Local0, Local2, Local3, Local4, TMP0, Arg0)
            If (EX00)
            {
                CH04 (__METHOD__, 0x00, 0xFF, Z064, __LINE__, 0x00, 0x00)
            }
            ElseIf (FLG1)
            {
                /* Verify the second result */

                M489 (TS, Local7, Local5)
            }
        }

        Return (Local7)
    }

    /* Init all parameters as non-usable */

    Method (M486, 0, NotSerialized)
    {
        DF00 = 0x00
        DF01 = 0x00
        DF02 = 0x00
        DF03 = 0x00
        DF04 = 0x00
    }

    /* Return the object of required type. */
    /* Allowed types are {1-12,14}, == 0x5fff. */
    /* Returned 0xfff is flag of "Uninitialized". */
    /* */
    /* These have to be implemented: */
    /* */
    /*	Method, Thermal Zone, DDB Handle */
    /* */
    Method (M487, 1, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                /* Uninitialized */

                Local7 = 0x0FFF
            }
            Case (0x01)
            {
                /* Integers */

                Local7 = 0x0100
            }
            Case (0x02)
            {
                /* Strings */

                Local7 = 0x0204
            }
            Case (0x03)
            {
                /* Buffers */

                Local7 = 0x0300
            }
            Case (0x04)
            {
                /* Packages */

                Local7 = 0x0400
            }
            Case (0x05)
            {
                /* Field Units */

                Local7 = 0x0500
            }
            Case (0x06)
            {
                /* Devices */

                Local7 = 0x0600
            }
            Case (0x07)
            {
                /* Events */

                Local7 = 0x0700
            }
            Case (0x08)
            {
                /* Methods */

                Local7 = 0x0800
            }
            Case (0x09)
            {
                /* Mutexes */

                Local7 = 0x0900
            }
            Case (0x0A)
            {
                /* Operation Regions */

                Local7 = 0x0A00
            }
            Case (0x0B)
            {
                /* Power Resources */

                Local7 = 0x0B00
            }
            Case (0x0C)
            {
                /* Processor */

                Local7 = 0x0C00
            }
            Case            /*
             * case (0xd00) {
             *	// Thermal Zones
             *	Store(Debug, Local7)
             * }
             */
 (0x0E)
            {
                /* Buffer Field */

                Local7 = 0x0E00
            }
            /*
             * case (0xf00) {
             *	// DDB Handle
             *	Store(Debug, Local7)
             * }
             *
             *
             * case (0x1000) {
             *	// Debug Object
             *	Store(Debug, Local7)
             * }
             */
            Default
            {
                If ((Arg0 != 0x00))
                {
                    ERR ("----------- ERROR, m487: incorrect Arg0:", Z064, 0x0319, 0x00, 0x00, 0x00, 0x00)
                    Debug = Arg0
                    Local7 = 0x00
                }
            }

        }

        Return (Local7)
    }

    /* Initiate exception by inappropriate operand */

    Method (M488, 6, Serialized)
    {
        Local7 = 0x00
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        If ((Arg1 & 0x5FFF))
        {
            LPN0 = 0x10
            LPC0 = 0x00
            While (LPN0)
            {
                Local6 = (0x01 << LPC0) /* \M488.LPC0 */
                If ((Arg1 & Local6))
                {
                    Local5 = M487 (LPC0)
                    Local7 = M485 (Arg0, Local5, DF01, DF02, DF03, DF04, FLG0)
                }

                LPN0--
                LPC0++
            }
        }

        If ((Arg2 & 0x5FFF))
        {
            LPN0 = 0x10
            LPC0 = 0x00
            While (LPN0)
            {
                Local6 = (0x01 << LPC0) /* \M488.LPC0 */
                If ((Arg2 & Local6))
                {
                    Local5 = M487 (LPC0)
                    Local7 = M485 (Arg0, DF00, Local5, DF02, DF03, DF04, FLG0)
                }

                LPN0--
                LPC0++
            }
        }

        If ((Arg3 & 0x5FFF))
        {
            LPN0 = 0x10
            LPC0 = 0x00
            While (LPN0)
            {
                Local6 = (0x01 << LPC0) /* \M488.LPC0 */
                If ((Arg3 & Local6))
                {
                    Local5 = M487 (LPC0)
                    Local7 = M485 (Arg0, DF00, DF01, Local5, DF03, DF04, FLG0)
                }

                LPN0--
                LPC0++
            }
        }

        If ((Arg4 & 0x5FFF))
        {
            LPN0 = 0x10
            LPC0 = 0x00
            While (LPN0)
            {
                Local6 = (0x01 << LPC0) /* \M488.LPC0 */
                If ((Arg4 & Local6))
                {
                    Local5 = M487 (LPC0)
                    Local7 = M485 (Arg0, DF00, DF01, DF02, Local5, DF04, FLG0)
                }

                LPN0--
                LPC0++
            }
        }

        If ((Arg5 & 0x5FFF))
        {
            LPN0 = 0x10
            LPC0 = 0x00
            While (LPN0)
            {
                Local6 = (0x01 << LPC0) /* \M488.LPC0 */
                If ((Arg5 & Local6))
                {
                    Local5 = M487 (LPC0)
                    Local7 = M485 (Arg0, DF00, DF01, DF02, DF03, Local5, FLG0)
                }

                LPN0--
                LPC0++
            }
        }

        Return (Local7)
    }

    Method (M489, 3, NotSerialized)
    {
        Local0 = ObjectType (Arg1)
        Local1 = ObjectType (Arg2)
        If ((Local0 != Local1))
        {
            ERR (Arg0, Z064, __LINE__, 0x00, 0x00, Local0, Local1)
        }
        ElseIf ((Arg1 != Arg2))
        {
            ERR (Arg0, Z064, __LINE__, 0x00, 0x00, Arg1, Arg2)
        }
    }

    /* Verify result */
    /* <name>,<results>,<result>,<index of result pair> */
    Method (M48A, 4, NotSerialized)
    {
        Local0 = (Arg3 * 0x02)
        Local7 = DerefOf (Arg1 [Local0])
        Local0++
        Local6 = DerefOf (Arg1 [Local0])
        If (F64)
        {
            If ((Arg2 != Local7))
            {
                ERR (Arg0, Z064, __LINE__, 0x00, 0x00, Arg2, Local7)
            }
        }
        ElseIf ((Arg2 != Local6))
        {
            ERR (Arg0, Z064, __LINE__, 0x00, 0x00, Arg2, Local6)
        }
    }

    /* Integer two operands operation */
    /* <operation>,<type of first operand> */
    /* */
    /* NOTE: now it work only by particular parts, */
    /*       all together produce crashes. Uncomment */
    /*       in future. */
    Method (M48B, 2, NotSerialized)
    {
        /* X - Integer */

        Local7 = M485 (Arg0, Arg1, 0x0100, 0x00, 0x00, 0x00, 0x00)
        /* X - String */

        Local7 = M485 (Arg0, Arg1, 0x0200, 0x00, 0x00, 0x00, 0x01)
        Local7 = M485 (Arg0, Arg1, 0x0201, 0x00, 0x00, 0x00, 0x02)
        Local7 = M485 (Arg0, Arg1, 0x0202, 0x00, 0x00, 0x00, 0x03)
        Local7 = M485 (Arg0, Arg1, 0x0203, 0x00, 0x00, 0x00, 0x04)
        Local7 = M485 (Arg0, Arg1, 0x0204, 0x00, 0x00, 0x00, 0x05)
        Local7 = M485 (Arg0, Arg1, 0x0205, 0x00, 0x00, 0x00, 0x06)
        Local7 = M485 (Arg0, Arg1, 0x0206, 0x00, 0x00, 0x00, 0x07)
        Local7 = M485 (Arg0, Arg1, 0x0207, 0x00, 0x00, 0x00, 0x08)
        Local7 = M485 (Arg0, Arg1, 0x0208, 0x00, 0x00, 0x00, 0x09)
        Local7 = M485 (Arg0, Arg1, 0x0209, 0x00, 0x00, 0x00, 0x0A)
        Local7 = M485 (Arg0, Arg1, 0x020A, 0x00, 0x00, 0x00, 0x0B)
        Local7 = M485 (Arg0, Arg1, 0x020B, 0x00, 0x00, 0x00, 0x0C)
        Local7 = M485 (Arg0, Arg1, 0x020C, 0x00, 0x00, 0x00, 0x0D)
        Local7 = M485 (Arg0, Arg1, 0x020D, 0x00, 0x00, 0x00, 0x0E)
        Local7 = M485 (Arg0, Arg1, 0x020E, 0x00, 0x00, 0x00, 0x0F)
        Local7 = M485 (Arg0, Arg1, 0x020F, 0x00, 0x00, 0x00, 0x10)
        Local7 = M485 (Arg0, Arg1, 0x0210, 0x00, 0x00, 0x00, 0x11)
        /* X - Buffer */

        Local7 = M485 (Arg0, Arg1, 0x0300, 0x00, 0x00, 0x00, 0x12)
        Local7 = M485 (Arg0, Arg1, 0x0301, 0x00, 0x00, 0x00, 0x13)
        Local7 = M485 (Arg0, Arg1, 0x0302, 0x00, 0x00, 0x00, 0x14)
        Local7 = M485 (Arg0, Arg1, 0x0303, 0x00, 0x00, 0x00, 0x15)
        Local7 = M485 (Arg0, Arg1, 0x0304, 0x00, 0x00, 0x00, 0x16)
        Local7 = M485 (Arg0, Arg1, 0x0305, 0x00, 0x00, 0x00, 0x17)
        Local7 = M485 (Arg0, Arg1, 0x0306, 0x00, 0x00, 0x00, 0x18)
        Local7 = M485 (Arg0, Arg1, 0x0307, 0x00, 0x00, 0x00, 0x19)
        Local7 = M485 (Arg0, Arg1, 0x0308, 0x00, 0x00, 0x00, 0x1A)
        /* X - Field Unit */

        Local7 = M485 (Arg0, Arg1, 0x0500, 0x00, 0x00, 0x00, 0x1B)
        Local7 = M485 (Arg0, Arg1, 0x0501, 0x00, 0x00, 0x00, 0x1C)
        Local7 = M485 (Arg0, Arg1, 0x0502, 0x00, 0x00, 0x00, 0x1D)
        Local7 = M485 (Arg0, Arg1, 0x0503, 0x00, 0x00, 0x00, 0x1E)
        Local7 = M485 (Arg0, Arg1, 0x0504, 0x00, 0x00, 0x00, 0x1F)
        Local7 = M485 (Arg0, Arg1, 0x0505, 0x00, 0x00, 0x00, 0x20)
        Local7 = M485 (Arg0, Arg1, 0x0506, 0x00, 0x00, 0x00, 0x21)
        Local7 = M485 (Arg0, Arg1, 0x0507, 0x00, 0x00, 0x00, 0x22)
        Local7 = M485 (Arg0, Arg1, 0x0508, 0x00, 0x00, 0x00, 0x23)
        Local7 = M485 (Arg0, Arg1, 0x0509, 0x00, 0x00, 0x00, 0x24)
        Local7 = M485 (Arg0, Arg1, 0x050A, 0x00, 0x00, 0x00, 0x25)
        /* X - Buffer Field */

        Local7 = M485 (Arg0, Arg1, 0x0E00, 0x00, 0x00, 0x00, 0x26)
        Local7 = M485 (Arg0, Arg1, 0x0E01, 0x00, 0x00, 0x00, 0x27)
        Local7 = M485 (Arg0, Arg1, 0x0E02, 0x00, 0x00, 0x00, 0x28)
        Local7 = M485 (Arg0, Arg1, 0x0E03, 0x00, 0x00, 0x00, 0x29)
        Local7 = M485 (Arg0, Arg1, 0x0E04, 0x00, 0x00, 0x00, 0x2A)
        Local7 = M485 (Arg0, Arg1, 0x0E05, 0x00, 0x00, 0x00, 0x2B)
        Local7 = M485 (Arg0, Arg1, 0x0E06, 0x00, 0x00, 0x00, 0x2C)
        Local7 = M485 (Arg0, Arg1, 0x0E07, 0x00, 0x00, 0x00, 0x2D)
        Local7 = M485 (Arg0, Arg1, 0x0E08, 0x00, 0x00, 0x00, 0x2E)
        Local7 = M485 (Arg0, Arg1, 0x0E09, 0x00, 0x00, 0x00, 0x2F)
        Local7 = M485 (Arg0, Arg1, 0x0E0A, 0x00, 0x00, 0x00, 0x30)
    }

    /* Return element of Package */
    /* <Package>,<index of elements-pair> */
    /* pair: {F64-element, F32-element} */
    Method (M48C, 2, NotSerialized)
    {
        Local0 = (Arg1 * 0x02)
        If (F64)
        {
            Local7 = DerefOf (Arg0 [Local0])
        }
        Else
        {
            Local0++
            Local7 = DerefOf (Arg0 [Local0])
        }

        Return (Local7)
    }

    /* arg0 - opcode of operation */
    /* */
    /* arg1 - type of 0-th argument */
    /* arg2 - type of 1-th argument */
    /* arg3 - type of 2-th argument */
    /* arg4 - type of 3-th argument */
    /* */
    /* arg5 - expected 64-bit result */
    /* arg6 - expected 32-bit result */
    Method (M48D, 7, Serialized)
    {
        Name (TS, "m48d")
        Name (TMP0, 0x00)
        If (0x00)
        {
            Debug = "##################################################################"
            Debug = Arg6
        }

        Name (EX00, 0x00)
        If (F64)
        {
            Local0 = ObjectType (Arg5)
            If ((Local0 == 0x02))
            {
                If ((Arg5 == "Exc"))
                {
                    EX00 = 0x01
                }
            }
        }
        Else
        {
            Local0 = ObjectType (Arg6)
            If ((Local0 == 0x02))
            {
                If ((Arg6 == "Exc"))
                {
                    EX00 = 0x01
                }
            }
        }

        Local7 = 0x00
        /* m482: */
        /* */
        /* arg0-arg4 - parameters of operators */
        /* arg5      - miscellaneous */
        /* arg6      - opcode of operation */
        Local0 = M484 (Arg1)
        Local1 = M484 (Arg2)
        Local2 = M484 (Arg3)
        Local3 = M484 (Arg4)
        If (EX00)
        {
            TMP0 = FLG2 /* \FLG2 */
            CH03 (TS, Z064, __LINE__, 0x00, 0x00)
        }

        Local7 = M482 (Local0, Local1, Local2, Local3, 0x00, TMP0, Arg0)
        If (EX00)
        {
            CH04 (__METHOD__, 0x00, 0xFF, Z064, __LINE__, 0x00, 0x00)
        }
        ElseIf        /* Verify the result */

 (F64)
        {
            M489 (TS, Local7, Arg5)
        }
        Else
        {
            M489 (TS, Local7, Arg6)
        }

        Return (Local7)
    }
