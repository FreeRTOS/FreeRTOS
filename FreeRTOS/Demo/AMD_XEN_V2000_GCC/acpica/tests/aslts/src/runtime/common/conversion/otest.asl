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
     SEE: LEqual (and LGreater ?) tests were mostly checked for 64-bit mode only.
     Do that after ACPICA bugs are fixed.
     SEE: what can be removed from m48b
     */
    /* */
    /* Implicit Source Operand Conversion, complex test */
    /* */
    Name (Z065, 0x41)
    /* Acquire (mux, wrd) => Boolean */
    /* */
    /* Total scale of unacceptable types: */
    /*    SyncObject: 0x5cff */
    /* Total scale of acceptable types: */
    /*    SyncObject: 0x0200 */
    Method (M400, 1, Serialized)
    {
        Name (OP, 0x00)
        Name (TS, "m400")
        TS00 (TS)
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0900
            Local7 = M488 (OP, 0x5CFF, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
            Local7 = M48D (OP, 0x0900, 0x00, 0x00, 0x00, Zero, Zero)
            Local7 = M48D (OP, 0x0901, 0x00, 0x00, 0x00, Zero, Zero)
        }
    }

    /* Add, check all unavailable non-hex symbols */

    Method (M4A2, 1, Serialized)
    {
        Name (TS, "m4a2")
        Name (S000, "`-=qwrtyuiop[]\\sghjkl;\'zxvnm,./~!@#$%^&*()_+QWRTYUIOP{}|SGHJKL:\"ZXVNM<>? ")
        Name (LPN0, 0x49)
        Name (LPC0, 0x00)
        While (LPN0)
        {
            Local0 = M4A1 (S000, LPC0)
            Local1 = ObjectType (Local0)
            If ((Local1 != 0x02))
            {
                ERR (Arg0, Z065, __LINE__, 0x00, 0x00, Local1, 0x02)
            }
            Else
            {
                Local1 = SizeOf (Local0)
                If ((Local1 != 0x01))
                {
                    ERR (Arg0, Z065, __LINE__, 0x00, 0x00, Local1, 0x01)
                }
                Else
                {
                    CH03 (TS, Z065, __LINE__, 0x00, 0x00)
                    Local7 = (Local0 + 0x00)
                    CH04 (Arg0, 0x00, 0x22, Z065, __LINE__, 0x00, 0x00) /* AE_BAD_HEX_CONSTANT */
                    CH03 (TS, Z065, __LINE__, 0x00, 0x00)
                    Local7 = (0x00 + Local0)
                    CH04 (Arg0, 0x00, 0x22, Z065, __LINE__, 0x00, 0x00) /* AE_BAD_HEX_CONSTANT */
                }
            }

            Debug = Local0
            LPN0--
            LPC0++
        }
    }

    /* Add, check all available hex symbols */

    Method (M4A4, 1, Serialized)
    {
        Name (TS, "m4a4")
        Name (S000, "0123456789abcdefABCDEF")
        Name (LPN0, 0x16)
        Name (LPC0, 0x00)
        While (LPN0)
        {
            Local0 = M4A1 (S000, LPC0)
            Local1 = ObjectType (Local0)
            If ((Local1 != 0x02))
            {
                ERR (Arg0, Z065, __LINE__, 0x00, 0x00, Local1, 0x02)
            }
            Else
            {
                Local1 = SizeOf (Local0)
                If ((Local1 != 0x01))
                {
                    ERR (Arg0, Z065, __LINE__, 0x00, 0x00, Local1, 0x01)
                }
                Else
                {
                    CH03 (TS, Z065, __LINE__, 0x00, 0x00)
                    Local7 = (Local0 + 0x00)
                    CH03 (TS, Z065, __LINE__, 0x00, 0x00)
                    CH03 (TS, Z065, __LINE__, 0x00, 0x00)
                    Local7 = (0x00 + Local0)
                    CH03 (TS, Z065, __LINE__, 0x00, 0x00)
                }
            }

            Debug = Local0
            LPN0--
            LPC0++
        }
    }

    /* Add, checkings in accordance with the Table 1 */

    Method (M4A0, 1, Serialized)
    {
        Name (TS, "m4a0")
        TS00 (TS)
        If (Arg0)
        {
            CH03 (TS, Z065, __LINE__, 0x00, 0x00)
            Local7 = ("fedcba98765432101" + 0x00)
            CH04 (__METHOD__, 0x00, 0x22, Z065, __LINE__, 0x00, 0x00)   /* AE_BAD_HEX_CONSTANT */
            CH03 (TS, Z065, __LINE__, 0x00, 0x00)
            Local7 = (0x00 + "fedcba98765432101")
            CH04 (__METHOD__, 0x00, 0x22, Z065, __LINE__, 0x00, 0x00)   /* AE_BAD_HEX_CONSTANT */
            CH03 (TS, Z065, __LINE__, 0x00, 0x00)
            Local7 = ("1234q" + 0x00)
            CH04 (__METHOD__, 0x00, 0x22, Z065, __LINE__, 0x00, 0x00)   /* AE_BAD_HEX_CONSTANT */
            CH03 (TS, Z065, __LINE__, 0x00, 0x00)
            Local7 = (0x00 + "1234q")
            CH04 (__METHOD__, 0x00, 0x22, Z065, __LINE__, 0x00, 0x00)   /* AE_BAD_HEX_CONSTANT */
            If (0x00)
            {
                CH03 (TS, Z065, __LINE__, 0x00, 0x00)
                Local7 = ("0xfedcba98765432" + 0x00)
                CH04 (__METHOD__, 0x00, 0x22, Z065, __LINE__, 0x00, 0x00)   /* AE_BAD_HEX_CONSTANT */
                CH03 (TS, Z065, __LINE__, 0x00, 0x00)
                Local7 = (0x00 + "0xfedcba98765432")
                CH04 (__METHOD__, 0x00, 0x22, Z065, __LINE__, 0x00, 0x00)   /* AE_BAD_HEX_CONSTANT */
                CH03 (TS, Z065, __LINE__, 0x00, 0x00)
                Local7 = ("" + 0x00)
                CH04 (__METHOD__, 0x00, 0x22, Z065, __LINE__, 0x00, 0x00)   /* AE_BAD_HEX_CONSTANT */
                CH03 (TS, Z065, __LINE__, 0x00, 0x00)
                Local7 = (0x00 + "")
                CH04 (__METHOD__, 0x00, 0x22, Z065, __LINE__, 0x00, 0x00)   /* AE_BAD_HEX_CONSTANT */
                CH03 (TS, Z065, __LINE__, 0x00, 0x00)
                Local7 = (" " + 0x00)
                CH04 (__METHOD__, 0x00, 0x22, Z065, __LINE__, 0x00, 0x00)   /* AE_BAD_HEX_CONSTANT */
                CH03 (TS, Z065, __LINE__, 0x00, 0x00)
                Local7 = (0x00 + " ")
                CH04 (__METHOD__, 0x00, 0x22, Z065, __LINE__, 0x00, 0x00)   /* AE_BAD_HEX_CONSTANT */
            }

            M4A2 (TS)
        }
        /* Buffers */
        /* Buffer Units */
        Else
        {
            /* Integers, directly */

            Local7 = (0xD1 + 0x00)
            M4C0 (TS, Local7, 0xD1, 0xD1)
            Local7 = (0x000000024CB016EA + 0x00)
            M4C0 (TS, Local7, 0x000000024CB016EA, 0x4CB016EA)
            Local7 = (0xFEDCBA9876543210 + 0x00)
            M4C0 (TS, Local7, 0xFEDCBA9876543210, 0x76543210)
            Local7 = (0x00 + 0x00)
            M4C0 (TS, Local7, 0x00, 0x00)
            Local7 = (0xFFFFFFFFFFFFFFFF + 0x00)
            M4C0 (TS, Local7, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFF)
            Local7 = (0x00 + 0xD1)
            M4C0 (TS, Local7, 0xD1, 0xD1)
            Local7 = (0x00 + 0x000000024CB016EA)
            M4C0 (TS, Local7, 0x000000024CB016EA, 0x4CB016EA)
            Local7 = (0x00 + 0xFEDCBA9876543210)
            M4C0 (TS, Local7, 0xFEDCBA9876543210, 0x76543210)
            Local7 = (0x00 + 0xFFFFFFFFFFFFFFFF)
            M4C0 (TS, Local7, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFF)
            /* Strings, directly */

            Local7 = ("0321" + 0x00)
            M4C0 (TS, Local7, 0x0321, 0x0321)
            Local7 = ("9876543210" + 0x00)
            M4C0 (TS, Local7, 0x0000009876543210, 0x76543210)
            Local7 = ("321" + 0x00)
            M4C0 (TS, Local7, 0x0321, 0x0321)
            Local7 = ("fedcba9876543210" + 0x00)
            M4C0 (TS, Local7, 0xFEDCBA9876543210, 0x76543210)
            M4A4 (TS)
        }

        /*
         Add(xxxxxx, 0, Local7)
         m4c0(ts, Local7, 0, 0)
         Add("xxxxxx", 0, Local7)
         m4c0(ts, Local7, 0, 0)
         */
        If (0x00)
        {
            Debug = 0x000000024CB016EA
        }
    }

    /* Add (int, int, Result) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Addend1: 0x1ed1 */
    /*    Addend2: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Addend1: 0x402e */
    /*    Addend1: 0x402e */
    Method (M401, 1, Serialized)
    {
        Name (OP, 0x01)
        TS00 ("m401")
        /* Expected results: 64-bit, 32-bit */

        Name (P000, Package (0x62)
        {
            /* X - Integer */

            0x58765432,
            0x58765432,
            /* X - String */

            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            0x9876,
            0x9876,
            0xABCD,
            0xABCD,
            0x1234567890987654,
            0x90987654,
            0xDAFECBAABBDDFFEE,
            0xBBDDFFEE,
            0x1234567890ABCDEF,
            0x90ABCDEF,
            0xFDEACB0132547698,
            0x32547698,
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            /* X - Buffer */

            0x00832291,
            0x00832291,
            0x80,
            0x80,
            0x8281,
            0x8281,
            0x86858483,
            0x86858483,
            0x0000009B9A999887,
            0x9A999887,
            0xA3A2A1A09F9E9D9C,
            0x9F9E9D9C,
            0xBBBAB9B8A7A6A5A4,
            0xA7A6A5A4,
            0x6261605F94939291,
            0x94939291,
            0x0807060504030201,
            0x04030201,
            /* X - Field Unit */

            0x7F,
            0x7F,
            0x07,
            0x07,
            0x8D,
            0x8D,
            0x8C8D,
            0x8C8D,
            0x8A8B8C8D,
            0x8A8B8C8D,
            0x00000001FFFFFFFF,
            0xFFFFFFFF,
            0x5CDEFA1988374658,
            0x88374658,
            0xDCDEFA1988379A58,
            0x88379A58,
            0xDCDEFA198837C758,
            0x8837C758,
            0xEFCDAB9078563482,
            0x78563482,
            0x52CD1299EFCDAB93,
            0xEFCDAB93,
            /* X - Buffer Field */

            0x918654AB,
            0x918654AB,
            0x07,
            0x07,
            0x8D,
            0x8D,
            0x8C8D,
            0x8C8D,
            0x8A8B8C8D,
            0x8A8B8C8D,
            0x00000001FFFFFFFF,
            0xFFFFFFFF,
            0x5CDEFA1988374658,
            0x88374658,
            0xDCDEFA1988379A58,
            0x88379A58,
            0xDCDEFA198837C758,
            0x8837C758,
            0xEFCDAB9078563482,
            0x78563482,
            0x52CD1299EFCDAB93,
            0xEFCDAB93
        })
        If (Arg0)
        {
            If (0x00)
            {
                M486 ()
                DF00 = 0x0100
                DF01 = 0x0100
                Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
            }

            M4A0 (0x01)
        }
        ElseIf (0x00)
        {
            FLG1 = 0x01
            COM2 = 0x01
            /*		Store(p000, PKG1) */
            /*		Store(PKG0, PKG2) */
            M48B (OP, 0x0104)
            /*		Store(PKG0, PKG1) */
            /*		Store(PKG0, PKG2) */
            COM2 = 0x00
            FLG1 = 0x00
        }
        Else
        {
            M4A0 (0x00)
        }
    }

    /* And (int, int, Result) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source1: 0x1ed1 */
    /*    Source2: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source1: 0x402e */
    /*    Source2: 0x402e */
    Method (M402, 1, Serialized)
    {
        Name (OP, 0x02)
        TS00 ("m402")
        /* Expected results: 64-bit, 32-bit */

        Name (P000, Package (0x62)
        {
            /* X - Integer */

            0x58765432,
            0x58765432,
            /* X - String */

            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            0x9876,
            0x9876,
            0xABCD,
            0xABCD,
            0x1234567890987654,
            0x90987654,
            0xDAFECBAABBDDFFEE,
            0xBBDDFFEE,
            0x1234567890ABCDEF,
            0x90ABCDEF,
            0xFDEACB0132547698,
            0x32547698,
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            /* X - Buffer */

            0x00832291,
            0x00832291,
            0x80,
            0x80,
            0x8281,
            0x8281,
            0x86858483,
            0x86858483,
            0x0000009B9A999887,
            0x9A999887,
            0xA3A2A1A09F9E9D9C,
            0x9F9E9D9C,
            0xBBBAB9B8A7A6A5A4,
            0xA7A6A5A4,
            0x6261605F94939291,
            0x94939291,
            0x0807060504030201,
            0x04030201,
            /* X - Field Unit */

            0x7F,
            0x7F,
            0x07,
            0x07,
            0x8D,
            0x8D,
            0x8C8D,
            0x8C8D,
            0x8A8B8C8D,
            0x8A8B8C8D,
            0x00000001FFFFFFFF,
            0xFFFFFFFF,
            0x5CDEFA1988374658,
            0x88374658,
            0xDCDEFA1988379A58,
            0x88379A58,
            0xDCDEFA198837C758,
            0x8837C758,
            0xEFCDAB9078563482,
            0x78563482,
            0x52CD1299EFCDAB93,
            0xEFCDAB93,
            /* X - Buffer Field */

            0x918654AB,
            0x918654AB,
            0x07,
            0x07,
            0x8D,
            0x8D,
            0x8C8D,
            0x8C8D,
            0x8A8B8C8D,
            0x8A8B8C8D,
            0x00000001FFFFFFFF,
            0xFFFFFFFF,
            0x5CDEFA1988374658,
            0x88374658,
            0xDCDEFA1988379A58,
            0x88379A58,
            0xDCDEFA198837C758,
            0x8837C758,
            0xEFCDAB9078563482,
            0x78563482,
            0x52CD1299EFCDAB93,
            0xEFCDAB93
        })
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
            FLG1 = 0x01
            COM2 = 0x01
            /*		Store(p000, PKG1) */
            /*		Store(PKG0, PKG2) */
            M48B (OP, 0x0106)
            /*		Store(PKG0, PKG1) */
            /*		Store(PKG0, PKG2) */
            COM2 = 0x00
            FLG1 = 0x00
        }
    }

    /* Concatenate({int|str|buf}, {int|str|buf}, Result) => ComputationalData */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source1: 0x1ed1 */
    /*    Source2: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source1: 0x402e */
    /*    Source2: 0x402e */
    Method (M403, 1, Serialized)
    {
        Name (OP, 0x03)
        TS00 ("m403")
        /* Expected results: 64-bit, 32-bit */

        Name (P000, Package (0x62)
        {
            /* X - Integer */

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x32, 0x54, 0x76, 0x58, 0x00, 0x00, 0x00, 0x00   // 2TvX....
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x32, 0x54, 0x76, 0x58   // xV4B2TvX
            },

            /* X - String */

            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x76, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x76, 0x98, 0x00, 0x00   // xV4Bv...
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0xCD, 0xAB, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0xCD, 0xAB, 0x00, 0x00   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x54, 0x76, 0x98, 0x90, 0x78, 0x56, 0x34, 0x12   // Tv..xV4.
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x54, 0x76, 0x98, 0x90   // xV4BTv..
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0xEE, 0xFF, 0xDD, 0xBB, 0xAA, 0xCB, 0xFE, 0xDA   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0xEE, 0xFF, 0xDD, 0xBB   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0xEF, 0xCD, 0xAB, 0x90, 0x78, 0x56, 0x34, 0x12   // ....xV4.
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0xEF, 0xCD, 0xAB, 0x90   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x98, 0x76, 0x54, 0x32, 0x01, 0xCB, 0xEA, 0xFD   // .vT2....
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x98, 0x76, 0x54, 0x32   // xV4B.vT2
            },

            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            /* X - Buffer */

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x91, 0x22, 0x83, 0x00, 0x00, 0x00, 0x00, 0x00   // ."......
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x91, 0x22, 0x83, 0x00   // xV4B."..
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x80, 0x00, 0x00, 0x00   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x81, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x81, 0x82, 0x00, 0x00   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x83, 0x84, 0x85, 0x86, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x83, 0x84, 0x85, 0x86   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x87, 0x98, 0x99, 0x9A, 0x9B, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x87, 0x98, 0x99, 0x9A   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x9C, 0x9D, 0x9E, 0x9F, 0xA0, 0xA1, 0xA2, 0xA3   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x9C, 0x9D, 0x9E, 0x9F   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0xA4, 0xA5, 0xA6, 0xA7, 0xB8, 0xB9, 0xBA, 0xBB   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0xA4, 0xA5, 0xA6, 0xA7   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x91, 0x92, 0x93, 0x94, 0x5F, 0x60, 0x61, 0x62   // ...._`ab
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x91, 0x92, 0x93, 0x94   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x01, 0x02, 0x03, 0x04   // xV4B....
            },

            /* X - Field Unit */

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x7F, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x7F, 0x00, 0x00, 0x00   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x07, 0x00, 0x00, 0x00   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x8D, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x8D, 0x00, 0x00, 0x00   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x8D, 0x8C, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x8D, 0x8C, 0x00, 0x00   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x8D, 0x8C, 0x8B, 0x8A, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x8D, 0x8C, 0x8B, 0x8A   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0xFF, 0xFF, 0xFF, 0xFF   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x58, 0x46, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0x5C   // XF7....\
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x58, 0x46, 0x37, 0x88   // xV4BXF7.
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC   // X.7.....
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x58, 0x9A, 0x37, 0x88   // xV4BX.7.
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC   // X.7.....
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x58, 0xC7, 0x37, 0x88   // xV4BX.7.
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x82, 0x34, 0x56, 0x78, 0x90, 0xAB, 0xCD, 0xEF   // .4Vx....
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x82, 0x34, 0x56, 0x78   // xV4B.4Vx
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12, 0xCD, 0x52   // .......R
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x93, 0xAB, 0xCD, 0xEF   // xV4B....
            },

            /* X - Buffer Field */

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0xAB, 0x54, 0x86, 0x91, 0x00, 0x00, 0x00, 0x00   // .T......
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0xAB, 0x54, 0x86, 0x91   // xV4B.T..
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x07, 0x00, 0x00, 0x00   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x8D, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x8D, 0x00, 0x00, 0x00   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x8D, 0x8C, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x8D, 0x8C, 0x00, 0x00   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x8D, 0x8C, 0x8B, 0x8A, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x8D, 0x8C, 0x8B, 0x8A   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0xFF, 0xFF, 0xFF, 0xFF   // xV4B....
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x58, 0x46, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0x5C   // XF7....\
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x58, 0x46, 0x37, 0x88   // xV4BXF7.
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC   // X.7.....
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x58, 0x9A, 0x37, 0x88   // xV4BX.7.
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC   // X.7.....
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x58, 0xC7, 0x37, 0x88   // xV4BX.7.
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x82, 0x34, 0x56, 0x78, 0x90, 0xAB, 0xCD, 0xEF   // .4Vx....
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x82, 0x34, 0x56, 0x78   // xV4B.4Vx
            },

            Buffer (0x10)
            {
                /* 0000 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB,  // xV4B....
                /* 0008 */  0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12, 0xCD, 0x52   // .......R
            },

            Buffer (0x08)
            {
                 0x78, 0x56, 0x34, 0x42, 0x93, 0xAB, 0xCD, 0xEF   // xV4B....
            }
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P001, Package (0x62)
        {
            /* X - Integer */

            Buffer (0x10)
            {
                /* 0000 */  0x32, 0x54, 0x76, 0x58, 0x00, 0x00, 0x00, 0x00,  // 2TvX....
                /* 0008 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x08)
            {
                 0x32, 0x54, 0x76, 0x58, 0x78, 0x56, 0x34, 0x42   // 2TvXxV4B
            },

            /* X - String */

            "qwrtABEDF18942345678",
            "qwrt42345678",
            "svnmjklABEDF18942345678",
            "svnmjkl42345678",
            "1234zyqABEDF18942345678",
            "1234zyq42345678",
            "abcdefzyqABEDF18942345678",
            "abcdefzyq42345678",
            "9876ABEDF18942345678",
            "987642345678",
            "aBcDABEDF18942345678",
            "aBcD42345678",
            "1234567890987654ABEDF18942345678",
            "123456789098765442345678",
            "daFeCBaabbddffeeABEDF18942345678",
            "daFeCBaabbddffee42345678",
            "1234567890abCdeFABEDF18942345678",
            "1234567890abCdeF42345678",
            "FdeAcb0132547698ABEDF18942345678",
            "FdeAcb013254769842345678",
            "12345678909876540ABEDF18942345678",
            "1234567890987654042345678",
            "fdeacb01325476980ABEDF18942345678",
            "fdeacb0132547698042345678",
            "123456789011223344556677889998765432199983337744ABEDF18942345678",
            "12345678901122334455667788999876543219998333774442345678",
            "abcdefaAbbccddeeffffeeddccaabbddeeffaaaabbbbeeefffddABEDF18942345678",
            "abcdefaAbbccddeeffffeeddccaabbddeeffaaaabbbbeeefffdd42345678",
            "1234567890abcdef9876543210fedbca1122334455667788fdeacbABEDF18942345678",
            "1234567890abcdef9876543210fedbca1122334455667788fdeacb42345678",
            "defa1234567890abcdef9876543210fedbca1122334455667788fdeacbABEDF18942345678",
            "defa1234567890abcdef9876543210fedbca1122334455667788fdeacb42345678",
            "123456789011223344556677889998765432199983337744zABEDF18942345678",
            "123456789011223344556677889998765432199983337744z42345678",
            /* X - Buffer */

            Buffer (0x0B)
            {
                /* 0000 */  0x91, 0x22, 0x83, 0x78, 0x56, 0x34, 0x42, 0x89,  // .".xV4B.
                /* 0008 */  0xF1, 0xED, 0xAB                                 // ...
            },

            Buffer (0x07)
            {
                 0x91, 0x22, 0x83, 0x78, 0x56, 0x34, 0x42         // .".xV4B
            },

            Buffer (0x09)
            {
                /* 0000 */  0x80, 0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED,  // .xV4B...
                /* 0008 */  0xAB                                             // .
            },

            Buffer (0x05)
            {
                 0x80, 0x78, 0x56, 0x34, 0x42                     // .xV4B
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x78, 0x56, 0x34, 0x42, 0x89, 0xF1,  // ..xV4B..
                /* 0008 */  0xED, 0xAB                                       // ..
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x78, 0x56, 0x34, 0x42               // ..xV4B
            },

            Buffer (0x0C)
            {
                /* 0000 */  0x83, 0x84, 0x85, 0x86, 0x78, 0x56, 0x34, 0x42,  // ....xV4B
                /* 0008 */  0x89, 0xF1, 0xED, 0xAB                           // ....
            },

            Buffer (0x08)
            {
                 0x83, 0x84, 0x85, 0x86, 0x78, 0x56, 0x34, 0x42   // ....xV4B
            },

            Buffer (0x0D)
            {
                /* 0000 */  0x87, 0x98, 0x99, 0x9A, 0x9B, 0x78, 0x56, 0x34,  // .....xV4
                /* 0008 */  0x42, 0x89, 0xF1, 0xED, 0xAB                     // B....
            },

            Buffer (0x09)
            {
                /* 0000 */  0x87, 0x98, 0x99, 0x9A, 0x9B, 0x78, 0x56, 0x34,  // .....xV4
                /* 0008 */  0x42                                             // B
            },

            Buffer (0x10)
            {
                /* 0000 */  0x9C, 0x9D, 0x9E, 0x9F, 0xA0, 0xA1, 0xA2, 0xA3,  // ........
                /* 0008 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x0C)
            {
                /* 0000 */  0x9C, 0x9D, 0x9E, 0x9F, 0xA0, 0xA1, 0xA2, 0xA3,  // ........
                /* 0008 */  0x78, 0x56, 0x34, 0x42                           // xV4B
            },

            Buffer (0x11)
            {
                /* 0000 */  0xA4, 0xA5, 0xA6, 0xA7, 0xB8, 0xB9, 0xBA, 0xBB,  // ........
                /* 0008 */  0xBC, 0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED,  // .xV4B...
                /* 0010 */  0xAB                                             // .
            },

            Buffer (0x0D)
            {
                /* 0000 */  0xA4, 0xA5, 0xA6, 0xA7, 0xB8, 0xB9, 0xBA, 0xBB,  // ........
                /* 0008 */  0xBC, 0x78, 0x56, 0x34, 0x42                     // .xV4B
            },

            Buffer (0xD0)
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
                /* 00C0 */  0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7, 0xC8,  // ........
                /* 00C8 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0xCC)
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
                /* 00C0 */  0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7, 0xC8,  // ........
                /* 00C8 */  0x78, 0x56, 0x34, 0x42                           // xV4B
            },

            Buffer (0x0109)
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
                /* 0100 */  0x01, 0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED,  // .xV4B...
                /* 0108 */  0xAB                                             // .
            },

            Buffer (0x0105)
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
                /* 0100 */  0x01, 0x78, 0x56, 0x34, 0x42                     // .xV4B
            },

            /* X - Field Unit */

            Buffer (0x10)
            {
                /* 0000 */  0x7F, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x08)
            {
                 0x7F, 0x00, 0x00, 0x00, 0x78, 0x56, 0x34, 0x42   // ....xV4B
            },

            Buffer (0x10)
            {
                /* 0000 */  0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x08)
            {
                 0x07, 0x00, 0x00, 0x00, 0x78, 0x56, 0x34, 0x42   // ....xV4B
            },

            Buffer (0x10)
            {
                /* 0000 */  0x8D, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x08)
            {
                 0x8D, 0x00, 0x00, 0x00, 0x78, 0x56, 0x34, 0x42   // ....xV4B
            },

            Buffer (0x10)
            {
                /* 0000 */  0x8D, 0x8C, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x08)
            {
                 0x8D, 0x8C, 0x00, 0x00, 0x78, 0x56, 0x34, 0x42   // ....xV4B
            },

            Buffer (0x10)
            {
                /* 0000 */  0x8D, 0x8C, 0x8B, 0x8A, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x08)
            {
                 0x8D, 0x8C, 0x8B, 0x8A, 0x78, 0x56, 0x34, 0x42   // ....xV4B
            },

            Buffer (0x10)
            {
                /* 0000 */  0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x09)
            {
                /* 0000 */  0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x78, 0x56, 0x34,  // .....xV4
                /* 0008 */  0x42                                             // B
            },

            Buffer (0x10)
            {
                /* 0000 */  0x58, 0x46, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0x5C,  // XF7....\
                /* 0008 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x0C)
            {
                /* 0000 */  0x58, 0x46, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0x5C,  // XF7....\
                /* 0008 */  0x78, 0x56, 0x34, 0x42                           // xV4B
            },

            Buffer (0x10)
            {
                /* 0000 */  0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x0C)
            {
                /* 0000 */  0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x78, 0x56, 0x34, 0x42                           // xV4B
            },

            Buffer (0x11)
            {
                /* 0000 */  0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x00, 0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED,  // .xV4B...
                /* 0010 */  0xAB                                             // .
            },

            Buffer (0x0D)
            {
                /* 0000 */  0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x00, 0x78, 0x56, 0x34, 0x42                     // .xV4B
            },

            Buffer (0x18)
            {
                /* 0000 */  0x82, 0x34, 0x56, 0x78, 0x90, 0xAB, 0xCD, 0xEF,  // .4Vx....
                /* 0008 */  0x55, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // U.......
                /* 0010 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x14)
            {
                /* 0000 */  0x82, 0x34, 0x56, 0x78, 0x90, 0xAB, 0xCD, 0xEF,  // .4Vx....
                /* 0008 */  0x55, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // U.......
                /* 0010 */  0x78, 0x56, 0x34, 0x42                           // xV4B
            },

            Buffer (0x29)
            {
                /* 0000 */  0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12, 0xCD, 0x52,  // .......R
                /* 0008 */  0x87, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0010 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0018 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0020 */  0x00, 0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED,  // .xV4B...
                /* 0028 */  0xAB                                             // .
            },

            Buffer (0x25)
            {
                /* 0000 */  0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12, 0xCD, 0x52,  // .......R
                /* 0008 */  0x87, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0010 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0018 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0020 */  0x00, 0x78, 0x56, 0x34, 0x42                     // .xV4B
            },

            /* X - Buffer Field */

            Buffer (0x10)
            {
                /* 0000 */  0xAB, 0x54, 0x86, 0x91, 0x00, 0x00, 0x00, 0x00,  // .T......
                /* 0008 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x08)
            {
                 0xAB, 0x54, 0x86, 0x91, 0x78, 0x56, 0x34, 0x42   // .T..xV4B
            },

            Buffer (0x10)
            {
                /* 0000 */  0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x08)
            {
                 0x07, 0x00, 0x00, 0x00, 0x78, 0x56, 0x34, 0x42   // ....xV4B
            },

            Buffer (0x10)
            {
                /* 0000 */  0x8D, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x08)
            {
                 0x8D, 0x00, 0x00, 0x00, 0x78, 0x56, 0x34, 0x42   // ....xV4B
            },

            Buffer (0x10)
            {
                /* 0000 */  0x8D, 0x8C, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x08)
            {
                 0x8D, 0x8C, 0x00, 0x00, 0x78, 0x56, 0x34, 0x42   // ....xV4B
            },

            Buffer (0x10)
            {
                /* 0000 */  0x8D, 0x8C, 0x8B, 0x8A, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x08)
            {
                 0x8D, 0x8C, 0x8B, 0x8A, 0x78, 0x56, 0x34, 0x42   // ....xV4B
            },

            Buffer (0x10)
            {
                /* 0000 */  0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x09)
            {
                /* 0000 */  0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x78, 0x56, 0x34,  // .....xV4
                /* 0008 */  0x42                                             // B
            },

            Buffer (0x10)
            {
                /* 0000 */  0x58, 0x46, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0x5C,  // XF7....\
                /* 0008 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x0C)
            {
                /* 0000 */  0x58, 0x46, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0x5C,  // XF7....\
                /* 0008 */  0x78, 0x56, 0x34, 0x42                           // xV4B
            },

            Buffer (0x10)
            {
                /* 0000 */  0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x0C)
            {
                /* 0000 */  0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x78, 0x56, 0x34, 0x42                           // xV4B
            },

            Buffer (0x11)
            {
                /* 0000 */  0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x00, 0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED,  // .xV4B...
                /* 0010 */  0xAB                                             // .
            },

            Buffer (0x0D)
            {
                /* 0000 */  0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x00, 0x78, 0x56, 0x34, 0x42                     // .xV4B
            },

            Buffer (0x18)
            {
                /* 0000 */  0x82, 0x34, 0x56, 0x78, 0x90, 0xAB, 0xCD, 0xEF,  // .4Vx....
                /* 0008 */  0x55, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // U.......
                /* 0010 */  0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED, 0xAB   // xV4B....
            },

            Buffer (0x14)
            {
                /* 0000 */  0x82, 0x34, 0x56, 0x78, 0x90, 0xAB, 0xCD, 0xEF,  // .4Vx....
                /* 0008 */  0x55, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // U.......
                /* 0010 */  0x78, 0x56, 0x34, 0x42                           // xV4B
            },

            Buffer (0x29)
            {
                /* 0000 */  0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12, 0xCD, 0x52,  // .......R
                /* 0008 */  0x87, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0010 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0018 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0020 */  0x00, 0x78, 0x56, 0x34, 0x42, 0x89, 0xF1, 0xED,  // .xV4B...
                /* 0028 */  0xAB                                             // .
            },

            Buffer (0x25)
            {
                /* 0000 */  0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12, 0xCD, 0x52,  // .......R
                /* 0008 */  0x87, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0010 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0018 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0020 */  0x00, 0x78, 0x56, 0x34, 0x42                     // .xV4B
            }
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P002, Package (0x62)
        {
            /* X - Integer */

            "98760000000058765432",
            "987658765432",
            /* X - String */

            "9876qwrt",
            "9876qwrt",
            "9876svnmjkl",
            "9876svnmjkl",
            "98761234zyq",
            "98761234zyq",
            "9876abcdefzyq",
            "9876abcdefzyq",
            "98769876",
            "98769876",
            "9876aBcD",
            "9876aBcD",
            "98761234567890987654",
            "98761234567890987654",
            "9876daFeCBaabbddffee",
            "9876daFeCBaabbddffee",
            "98761234567890abCdeF",
            "98761234567890abCdeF",
            "9876FdeAcb0132547698",
            "9876FdeAcb0132547698",
            "987612345678909876540",
            "987612345678909876540",
            "9876fdeacb01325476980",
            "9876fdeacb01325476980",
            "9876123456789011223344556677889998765432199983337744",
            "9876123456789011223344556677889998765432199983337744",
            "9876abcdefaAbbccddeeffffeeddccaabbddeeffaaaabbbbeeefffdd",
            "9876abcdefaAbbccddeeffffeeddccaabbddeeffaaaabbbbeeefffdd",
            "98761234567890abcdef9876543210fedbca1122334455667788fdeacb",
            "98761234567890abcdef9876543210fedbca1122334455667788fdeacb",
            "9876defa1234567890abcdef9876543210fedbca1122334455667788fdeacb",
            "9876defa1234567890abcdef9876543210fedbca1122334455667788fdeacb",
            "9876123456789011223344556677889998765432199983337744z",
            "9876123456789011223344556677889998765432199983337744z",
            /* X - Buffer */

            "987691 22 83",
            "987691 22 83",
            "987680",
            "987680",
            "987681 82",
            "987681 82",
            "987683 84 85 86",
            "987683 84 85 86",
            "987687 98 99 9A 9B",
            "987687 98 99 9A 9B",
            "98769C 9D 9E 9F A0 A1 A2 A3",
            "98769C 9D 9E 9F A0 A1 A2 A3",
            "9876A4 A5 A6 A7 B8 B9 BA BB BC",
            "9876A4 A5 A6 A7 B8 B9 BA BB BC",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            /* X - Field Unit */

            "9876000000000000007F",
            "98760000007F",
            "98760000000000000007",
            "987600000007",
            "9876000000000000008D",
            "98760000008D",
            "98760000000000008C8D",
            "987600008C8D",
            "9876000000008A8B8C8D",
            "98768A8B8C8D",
            "987600000001FFFFFFFF",
            "9876FF FF FF FF 01",
            "98765CDEFA1988374658",
            "987658 46 37 88 19 FA DE 5C",
            "9876DCDEFA1988379A58",
            "987658 9A 37 88 19 FA DE DC",
            "987658 C7 37 88 19 FA DE DC 00",
            "987658 C7 37 88 19 FA DE DC 00",
            "987682 34 56 78 90 AB CD EF 55 00 00 00 00 00 00 00",
            "987682 34 56 78 90 AB CD EF 55 00 00 00 00 00 00 00",
            "987693 AB CD EF 99 12 CD 52 87 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00",
            "987693 AB CD EF 99 12 CD 52 87 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00",
            /* X - Buffer Field */

            "987600000000918654AB",
            "9876918654AB",
            "98760000000000000007",
            "987600000007",
            "9876000000000000008D",
            "98760000008D",
            "98760000000000008C8D",
            "987600008C8D",
            "9876000000008A8B8C8D",
            "98768A8B8C8D",
            "987600000001FFFFFFFF",
            "9876FF FF FF FF 01",
            "98765CDEFA1988374658",
            "987658 46 37 88 19 FA DE 5C",
            "9876DCDEFA1988379A58",
            "987658 9A 37 88 19 FA DE DC",
            "987658 C7 37 88 19 FA DE DC 00",
            "987658 C7 37 88 19 FA DE DC 00",
            "987682 34 56 78 90 AB CD EF 55 00 00 00 00 00 00 00",
            "987682 34 56 78 90 AB CD EF 55 00 00 00 00 00 00 00",
            "987693 AB CD EF 99 12 CD 52 87 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00",
            "987693 AB CD EF 99 12 CD 52 87 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00"
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P003, Package (0x62)
        {
            /* X - Integer */

            Buffer (0x10)
            {
                /* 0000 */  0x32, 0x54, 0x76, 0x58, 0x00, 0x00, 0x00, 0x00,  // 2TvX....
                /* 0008 */  0x76, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x08)
            {
                 0x32, 0x54, 0x76, 0x58, 0x76, 0x98, 0x00, 0x00   // 2TvXv...
            },

            /* X - String */

            "qwrt9876",
            "qwrt9876",
            "svnmjkl9876",
            "svnmjkl9876",
            "1234zyq9876",
            "1234zyq9876",
            "abcdefzyq9876",
            "abcdefzyq9876",
            "98769876",
            "98769876",
            "aBcD9876",
            "aBcD9876",
            "12345678909876549876",
            "12345678909876549876",
            "daFeCBaabbddffee9876",
            "daFeCBaabbddffee9876",
            "1234567890abCdeF9876",
            "1234567890abCdeF9876",
            "FdeAcb01325476989876",
            "FdeAcb01325476989876",
            "123456789098765409876",
            "123456789098765409876",
            "fdeacb013254769809876",
            "fdeacb013254769809876",
            "1234567890112233445566778899987654321999833377449876",
            "1234567890112233445566778899987654321999833377449876",
            "abcdefaAbbccddeeffffeeddccaabbddeeffaaaabbbbeeefffdd9876",
            "abcdefaAbbccddeeffffeeddccaabbddeeffaaaabbbbeeefffdd9876",
            "1234567890abcdef9876543210fedbca1122334455667788fdeacb9876",
            "1234567890abcdef9876543210fedbca1122334455667788fdeacb9876",
            "defa1234567890abcdef9876543210fedbca1122334455667788fdeacb9876",
            "defa1234567890abcdef9876543210fedbca1122334455667788fdeacb9876",
            "123456789011223344556677889998765432199983337744z9876",
            "123456789011223344556677889998765432199983337744z9876",
            /* X - Buffer */

            Buffer (0x07)
            {
                 0x91, 0x22, 0x83, 0x39, 0x38, 0x37, 0x36         // .".9876
            },

            Buffer (0x07)
            {
                 0x91, 0x22, 0x83, 0x39, 0x38, 0x37, 0x36         // .".9876
            },

            Buffer (0x05)
            {
                 0x80, 0x39, 0x38, 0x37, 0x36                     // .9876
            },

            Buffer (0x05)
            {
                 0x80, 0x39, 0x38, 0x37, 0x36                     // .9876
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x39, 0x38, 0x37, 0x36               // ..9876
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x39, 0x38, 0x37, 0x36               // ..9876
            },

            Buffer (0x08)
            {
                 0x83, 0x84, 0x85, 0x86, 0x39, 0x38, 0x37, 0x36   // ....9876
            },

            Buffer (0x08)
            {
                 0x83, 0x84, 0x85, 0x86, 0x39, 0x38, 0x37, 0x36   // ....9876
            },

            Buffer (0x09)
            {
                /* 0000 */  0x87, 0x98, 0x99, 0x9A, 0x9B, 0x39, 0x38, 0x37,  // .....987
                /* 0008 */  0x36                                             // 6
            },

            Buffer (0x09)
            {
                /* 0000 */  0x87, 0x98, 0x99, 0x9A, 0x9B, 0x39, 0x38, 0x37,  // .....987
                /* 0008 */  0x36                                             // 6
            },

            Buffer (0x0C)
            {
                /* 0000 */  0x9C, 0x9D, 0x9E, 0x9F, 0xA0, 0xA1, 0xA2, 0xA3,  // ........
                /* 0008 */  0x39, 0x38, 0x37, 0x36                           // 9876
            },

            Buffer (0x0C)
            {
                /* 0000 */  0x9C, 0x9D, 0x9E, 0x9F, 0xA0, 0xA1, 0xA2, 0xA3,  // ........
                /* 0008 */  0x39, 0x38, 0x37, 0x36                           // 9876
            },

            Buffer (0x0D)
            {
                /* 0000 */  0xA4, 0xA5, 0xA6, 0xA7, 0xB8, 0xB9, 0xBA, 0xBB,  // ........
                /* 0008 */  0xBC, 0x39, 0x38, 0x37, 0x36                     // .9876
            },

            Buffer (0x0D)
            {
                /* 0000 */  0xA4, 0xA5, 0xA6, 0xA7, 0xB8, 0xB9, 0xBA, 0xBB,  // ........
                /* 0008 */  0xBC, 0x39, 0x38, 0x37, 0x36                     // .9876
            },

            Buffer (0xCC)
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
                /* 00C0 */  0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7, 0xC8,  // ........
                /* 00C8 */  0x39, 0x38, 0x37, 0x36                           // 9876
            },

            Buffer (0xCC)
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
                /* 00C0 */  0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7, 0xC8,  // ........
                /* 00C8 */  0x39, 0x38, 0x37, 0x36                           // 9876
            },

            Buffer (0x0105)
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
                /* 0100 */  0x01, 0x39, 0x38, 0x37, 0x36                     // .9876
            },

            Buffer (0x0105)
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
                /* 0100 */  0x01, 0x39, 0x38, 0x37, 0x36                     // .9876
            },

            /* X - Field Unit */

            Buffer (0x10)
            {
                /* 0000 */  0x7F, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x76, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x08)
            {
                 0x7F, 0x00, 0x00, 0x00, 0x76, 0x98, 0x00, 0x00   // ....v...
            },

            Buffer (0x10)
            {
                /* 0000 */  0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x76, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x08)
            {
                 0x07, 0x00, 0x00, 0x00, 0x76, 0x98, 0x00, 0x00   // ....v...
            },

            Buffer (0x10)
            {
                /* 0000 */  0x8D, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x76, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x08)
            {
                 0x8D, 0x00, 0x00, 0x00, 0x76, 0x98, 0x00, 0x00   // ....v...
            },

            Buffer (0x10)
            {
                /* 0000 */  0x8D, 0x8C, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x76, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x08)
            {
                 0x8D, 0x8C, 0x00, 0x00, 0x76, 0x98, 0x00, 0x00   // ....v...
            },

            Buffer (0x10)
            {
                /* 0000 */  0x8D, 0x8C, 0x8B, 0x8A, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x76, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x08)
            {
                 0x8D, 0x8C, 0x8B, 0x8A, 0x76, 0x98, 0x00, 0x00   // ....v...
            },

            Buffer (0x10)
            {
                /* 0000 */  0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x76, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x09)
            {
                /* 0000 */  0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x39, 0x38, 0x37,  // .....987
                /* 0008 */  0x36                                             // 6
            },

            Buffer (0x10)
            {
                /* 0000 */  0x58, 0x46, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0x5C,  // XF7....\
                /* 0008 */  0x76, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x0C)
            {
                /* 0000 */  0x58, 0x46, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0x5C,  // XF7....\
                /* 0008 */  0x39, 0x38, 0x37, 0x36                           // 9876
            },

            Buffer (0x10)
            {
                /* 0000 */  0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x76, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x0C)
            {
                /* 0000 */  0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x39, 0x38, 0x37, 0x36                           // 9876
            },

            Buffer (0x0D)
            {
                /* 0000 */  0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x00, 0x39, 0x38, 0x37, 0x36                     // .9876
            },

            Buffer (0x0D)
            {
                /* 0000 */  0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x00, 0x39, 0x38, 0x37, 0x36                     // .9876
            },

            Buffer (0x14)
            {
                /* 0000 */  0x82, 0x34, 0x56, 0x78, 0x90, 0xAB, 0xCD, 0xEF,  // .4Vx....
                /* 0008 */  0x55, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // U.......
                /* 0010 */  0x39, 0x38, 0x37, 0x36                           // 9876
            },

            Buffer (0x14)
            {
                /* 0000 */  0x82, 0x34, 0x56, 0x78, 0x90, 0xAB, 0xCD, 0xEF,  // .4Vx....
                /* 0008 */  0x55, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // U.......
                /* 0010 */  0x39, 0x38, 0x37, 0x36                           // 9876
            },

            Buffer (0x25)
            {
                /* 0000 */  0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12, 0xCD, 0x52,  // .......R
                /* 0008 */  0x87, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0010 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0018 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0020 */  0x00, 0x39, 0x38, 0x37, 0x36                     // .9876
            },

            Buffer (0x25)
            {
                /* 0000 */  0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12, 0xCD, 0x52,  // .......R
                /* 0008 */  0x87, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0010 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0018 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0020 */  0x00, 0x39, 0x38, 0x37, 0x36                     // .9876
            },

            /* X - Buffer Field */

            Buffer (0x10)
            {
                /* 0000 */  0xAB, 0x54, 0x86, 0x91, 0x00, 0x00, 0x00, 0x00,  // .T......
                /* 0008 */  0x76, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x08)
            {
                 0xAB, 0x54, 0x86, 0x91, 0x76, 0x98, 0x00, 0x00   // .T..v...
            },

            Buffer (0x10)
            {
                /* 0000 */  0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x76, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x08)
            {
                 0x07, 0x00, 0x00, 0x00, 0x76, 0x98, 0x00, 0x00   // ....v...
            },

            Buffer (0x10)
            {
                /* 0000 */  0x8D, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x76, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x08)
            {
                 0x8D, 0x00, 0x00, 0x00, 0x76, 0x98, 0x00, 0x00   // ....v...
            },

            Buffer (0x10)
            {
                /* 0000 */  0x8D, 0x8C, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x76, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x08)
            {
                 0x8D, 0x8C, 0x00, 0x00, 0x76, 0x98, 0x00, 0x00   // ....v...
            },

            Buffer (0x10)
            {
                /* 0000 */  0x8D, 0x8C, 0x8B, 0x8A, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x76, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x08)
            {
                 0x8D, 0x8C, 0x8B, 0x8A, 0x76, 0x98, 0x00, 0x00   // ....v...
            },

            Buffer (0x10)
            {
                /* 0000 */  0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x76, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x09)
            {
                /* 0000 */  0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x39, 0x38, 0x37,  // .....987
                /* 0008 */  0x36                                             // 6
            },

            Buffer (0x10)
            {
                /* 0000 */  0x58, 0x46, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0x5C,  // XF7....\
                /* 0008 */  0x76, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x0C)
            {
                /* 0000 */  0x58, 0x46, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0x5C,  // XF7....\
                /* 0008 */  0x39, 0x38, 0x37, 0x36                           // 9876
            },

            Buffer (0x10)
            {
                /* 0000 */  0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x76, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // v.......
            },

            Buffer (0x0C)
            {
                /* 0000 */  0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x39, 0x38, 0x37, 0x36                           // 9876
            },

            Buffer (0x0D)
            {
                /* 0000 */  0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x00, 0x39, 0x38, 0x37, 0x36                     // .9876
            },

            Buffer (0x0D)
            {
                /* 0000 */  0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x00, 0x39, 0x38, 0x37, 0x36                     // .9876
            },

            Buffer (0x14)
            {
                /* 0000 */  0x82, 0x34, 0x56, 0x78, 0x90, 0xAB, 0xCD, 0xEF,  // .4Vx....
                /* 0008 */  0x55, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // U.......
                /* 0010 */  0x39, 0x38, 0x37, 0x36                           // 9876
            },

            Buffer (0x14)
            {
                /* 0000 */  0x82, 0x34, 0x56, 0x78, 0x90, 0xAB, 0xCD, 0xEF,  // .4Vx....
                /* 0008 */  0x55, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // U.......
                /* 0010 */  0x39, 0x38, 0x37, 0x36                           // 9876
            },

            Buffer (0x25)
            {
                /* 0000 */  0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12, 0xCD, 0x52,  // .......R
                /* 0008 */  0x87, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0010 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0018 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0020 */  0x00, 0x39, 0x38, 0x37, 0x36                     // .9876
            },

            Buffer (0x25)
            {
                /* 0000 */  0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12, 0xCD, 0x52,  // .......R
                /* 0008 */  0x87, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0010 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0018 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0020 */  0x00, 0x39, 0x38, 0x37, 0x36                     // .9876
            }
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P004, Package (0x62)
        {
            /* X - Integer */

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x32, 0x54, 0x76, 0x58, 0x00, 0x00,  // ..2TvX..
                /* 0008 */  0x00, 0x00                                       // ..
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x32, 0x54, 0x76, 0x58               // ..2TvX
            },

            /* X - String */

            Buffer (0x06)
            {
                 0x81, 0x82, 0x71, 0x77, 0x72, 0x74               // ..qwrt
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x71, 0x77, 0x72, 0x74               // ..qwrt
            },

            Buffer (0x09)
            {
                /* 0000 */  0x81, 0x82, 0x73, 0x76, 0x6E, 0x6D, 0x6A, 0x6B,  // ..svnmjk
                /* 0008 */  0x6C                                             // l
            },

            Buffer (0x09)
            {
                /* 0000 */  0x81, 0x82, 0x73, 0x76, 0x6E, 0x6D, 0x6A, 0x6B,  // ..svnmjk
                /* 0008 */  0x6C                                             // l
            },

            Buffer (0x09)
            {
                /* 0000 */  0x81, 0x82, 0x31, 0x32, 0x33, 0x34, 0x7A, 0x79,  // ..1234zy
                /* 0008 */  0x71                                             // q
            },

            Buffer (0x09)
            {
                /* 0000 */  0x81, 0x82, 0x31, 0x32, 0x33, 0x34, 0x7A, 0x79,  // ..1234zy
                /* 0008 */  0x71                                             // q
            },

            Buffer (0x0B)
            {
                /* 0000 */  0x81, 0x82, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66,  // ..abcdef
                /* 0008 */  0x7A, 0x79, 0x71                                 // zyq
            },

            Buffer (0x0B)
            {
                /* 0000 */  0x81, 0x82, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66,  // ..abcdef
                /* 0008 */  0x7A, 0x79, 0x71                                 // zyq
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x39, 0x38, 0x37, 0x36               // ..9876
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x39, 0x38, 0x37, 0x36               // ..9876
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x61, 0x42, 0x63, 0x44               // ..aBcD
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x61, 0x42, 0x63, 0x44               // ..aBcD
            },

            Buffer (0x12)
            {
                /* 0000 */  0x81, 0x82, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,  // ..123456
                /* 0008 */  0x37, 0x38, 0x39, 0x30, 0x39, 0x38, 0x37, 0x36,  // 78909876
                /* 0010 */  0x35, 0x34                                       // 54
            },

            Buffer (0x12)
            {
                /* 0000 */  0x81, 0x82, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,  // ..123456
                /* 0008 */  0x37, 0x38, 0x39, 0x30, 0x39, 0x38, 0x37, 0x36,  // 78909876
                /* 0010 */  0x35, 0x34                                       // 54
            },

            Buffer (0x12)
            {
                /* 0000 */  0x81, 0x82, 0x64, 0x61, 0x46, 0x65, 0x43, 0x42,  // ..daFeCB
                /* 0008 */  0x61, 0x61, 0x62, 0x62, 0x64, 0x64, 0x66, 0x66,  // aabbddff
                /* 0010 */  0x65, 0x65                                       // ee
            },

            Buffer (0x12)
            {
                /* 0000 */  0x81, 0x82, 0x64, 0x61, 0x46, 0x65, 0x43, 0x42,  // ..daFeCB
                /* 0008 */  0x61, 0x61, 0x62, 0x62, 0x64, 0x64, 0x66, 0x66,  // aabbddff
                /* 0010 */  0x65, 0x65                                       // ee
            },

            Buffer (0x12)
            {
                /* 0000 */  0x81, 0x82, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,  // ..123456
                /* 0008 */  0x37, 0x38, 0x39, 0x30, 0x61, 0x62, 0x43, 0x64,  // 7890abCd
                /* 0010 */  0x65, 0x46                                       // eF
            },

            Buffer (0x12)
            {
                /* 0000 */  0x81, 0x82, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,  // ..123456
                /* 0008 */  0x37, 0x38, 0x39, 0x30, 0x61, 0x62, 0x43, 0x64,  // 7890abCd
                /* 0010 */  0x65, 0x46                                       // eF
            },

            Buffer (0x12)
            {
                /* 0000 */  0x81, 0x82, 0x46, 0x64, 0x65, 0x41, 0x63, 0x62,  // ..FdeAcb
                /* 0008 */  0x30, 0x31, 0x33, 0x32, 0x35, 0x34, 0x37, 0x36,  // 01325476
                /* 0010 */  0x39, 0x38                                       // 98
            },

            Buffer (0x12)
            {
                /* 0000 */  0x81, 0x82, 0x46, 0x64, 0x65, 0x41, 0x63, 0x62,  // ..FdeAcb
                /* 0008 */  0x30, 0x31, 0x33, 0x32, 0x35, 0x34, 0x37, 0x36,  // 01325476
                /* 0010 */  0x39, 0x38                                       // 98
            },

            Buffer (0x13)
            {
                /* 0000 */  0x81, 0x82, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,  // ..123456
                /* 0008 */  0x37, 0x38, 0x39, 0x30, 0x39, 0x38, 0x37, 0x36,  // 78909876
                /* 0010 */  0x35, 0x34, 0x30                                 // 540
            },

            Buffer (0x13)
            {
                /* 0000 */  0x81, 0x82, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,  // ..123456
                /* 0008 */  0x37, 0x38, 0x39, 0x30, 0x39, 0x38, 0x37, 0x36,  // 78909876
                /* 0010 */  0x35, 0x34, 0x30                                 // 540
            },

            Buffer (0x13)
            {
                /* 0000 */  0x81, 0x82, 0x66, 0x64, 0x65, 0x61, 0x63, 0x62,  // ..fdeacb
                /* 0008 */  0x30, 0x31, 0x33, 0x32, 0x35, 0x34, 0x37, 0x36,  // 01325476
                /* 0010 */  0x39, 0x38, 0x30                                 // 980
            },

            Buffer (0x13)
            {
                /* 0000 */  0x81, 0x82, 0x66, 0x64, 0x65, 0x61, 0x63, 0x62,  // ..fdeacb
                /* 0008 */  0x30, 0x31, 0x33, 0x32, 0x35, 0x34, 0x37, 0x36,  // 01325476
                /* 0010 */  0x39, 0x38, 0x30                                 // 980
            },

            Buffer (0x32)
            {
                /* 0000 */  0x81, 0x82, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,  // ..123456
                /* 0008 */  0x37, 0x38, 0x39, 0x30, 0x31, 0x31, 0x32, 0x32,  // 78901122
                /* 0010 */  0x33, 0x33, 0x34, 0x34, 0x35, 0x35, 0x36, 0x36,  // 33445566
                /* 0018 */  0x37, 0x37, 0x38, 0x38, 0x39, 0x39, 0x39, 0x38,  // 77889998
                /* 0020 */  0x37, 0x36, 0x35, 0x34, 0x33, 0x32, 0x31, 0x39,  // 76543219
                /* 0028 */  0x39, 0x39, 0x38, 0x33, 0x33, 0x33, 0x37, 0x37,  // 99833377
                /* 0030 */  0x34, 0x34                                       // 44
            },

            Buffer (0x32)
            {
                /* 0000 */  0x81, 0x82, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,  // ..123456
                /* 0008 */  0x37, 0x38, 0x39, 0x30, 0x31, 0x31, 0x32, 0x32,  // 78901122
                /* 0010 */  0x33, 0x33, 0x34, 0x34, 0x35, 0x35, 0x36, 0x36,  // 33445566
                /* 0018 */  0x37, 0x37, 0x38, 0x38, 0x39, 0x39, 0x39, 0x38,  // 77889998
                /* 0020 */  0x37, 0x36, 0x35, 0x34, 0x33, 0x32, 0x31, 0x39,  // 76543219
                /* 0028 */  0x39, 0x39, 0x38, 0x33, 0x33, 0x33, 0x37, 0x37,  // 99833377
                /* 0030 */  0x34, 0x34                                       // 44
            },

            Buffer (0x36)
            {
                /* 0000 */  0x81, 0x82, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66,  // ..abcdef
                /* 0008 */  0x61, 0x41, 0x62, 0x62, 0x63, 0x63, 0x64, 0x64,  // aAbbccdd
                /* 0010 */  0x65, 0x65, 0x66, 0x66, 0x66, 0x66, 0x65, 0x65,  // eeffffee
                /* 0018 */  0x64, 0x64, 0x63, 0x63, 0x61, 0x61, 0x62, 0x62,  // ddccaabb
                /* 0020 */  0x64, 0x64, 0x65, 0x65, 0x66, 0x66, 0x61, 0x61,  // ddeeffaa
                /* 0028 */  0x61, 0x61, 0x62, 0x62, 0x62, 0x62, 0x65, 0x65,  // aabbbbee
                /* 0030 */  0x65, 0x66, 0x66, 0x66, 0x64, 0x64               // efffdd
            },

            Buffer (0x36)
            {
                /* 0000 */  0x81, 0x82, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66,  // ..abcdef
                /* 0008 */  0x61, 0x41, 0x62, 0x62, 0x63, 0x63, 0x64, 0x64,  // aAbbccdd
                /* 0010 */  0x65, 0x65, 0x66, 0x66, 0x66, 0x66, 0x65, 0x65,  // eeffffee
                /* 0018 */  0x64, 0x64, 0x63, 0x63, 0x61, 0x61, 0x62, 0x62,  // ddccaabb
                /* 0020 */  0x64, 0x64, 0x65, 0x65, 0x66, 0x66, 0x61, 0x61,  // ddeeffaa
                /* 0028 */  0x61, 0x61, 0x62, 0x62, 0x62, 0x62, 0x65, 0x65,  // aabbbbee
                /* 0030 */  0x65, 0x66, 0x66, 0x66, 0x64, 0x64               // efffdd
            },

            Buffer (0x38)
            {
                /* 0000 */  0x81, 0x82, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,  // ..123456
                /* 0008 */  0x37, 0x38, 0x39, 0x30, 0x61, 0x62, 0x63, 0x64,  // 7890abcd
                /* 0010 */  0x65, 0x66, 0x39, 0x38, 0x37, 0x36, 0x35, 0x34,  // ef987654
                /* 0018 */  0x33, 0x32, 0x31, 0x30, 0x66, 0x65, 0x64, 0x62,  // 3210fedb
                /* 0020 */  0x63, 0x61, 0x31, 0x31, 0x32, 0x32, 0x33, 0x33,  // ca112233
                /* 0028 */  0x34, 0x34, 0x35, 0x35, 0x36, 0x36, 0x37, 0x37,  // 44556677
                /* 0030 */  0x38, 0x38, 0x66, 0x64, 0x65, 0x61, 0x63, 0x62   // 88fdeacb
            },

            Buffer (0x38)
            {
                /* 0000 */  0x81, 0x82, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,  // ..123456
                /* 0008 */  0x37, 0x38, 0x39, 0x30, 0x61, 0x62, 0x63, 0x64,  // 7890abcd
                /* 0010 */  0x65, 0x66, 0x39, 0x38, 0x37, 0x36, 0x35, 0x34,  // ef987654
                /* 0018 */  0x33, 0x32, 0x31, 0x30, 0x66, 0x65, 0x64, 0x62,  // 3210fedb
                /* 0020 */  0x63, 0x61, 0x31, 0x31, 0x32, 0x32, 0x33, 0x33,  // ca112233
                /* 0028 */  0x34, 0x34, 0x35, 0x35, 0x36, 0x36, 0x37, 0x37,  // 44556677
                /* 0030 */  0x38, 0x38, 0x66, 0x64, 0x65, 0x61, 0x63, 0x62   // 88fdeacb
            },

            Buffer (0x3C)
            {
                /* 0000 */  0x81, 0x82, 0x64, 0x65, 0x66, 0x61, 0x31, 0x32,  // ..defa12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x30,  // 34567890
                /* 0010 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x39, 0x38,  // abcdef98
                /* 0018 */  0x37, 0x36, 0x35, 0x34, 0x33, 0x32, 0x31, 0x30,  // 76543210
                /* 0020 */  0x66, 0x65, 0x64, 0x62, 0x63, 0x61, 0x31, 0x31,  // fedbca11
                /* 0028 */  0x32, 0x32, 0x33, 0x33, 0x34, 0x34, 0x35, 0x35,  // 22334455
                /* 0030 */  0x36, 0x36, 0x37, 0x37, 0x38, 0x38, 0x66, 0x64,  // 667788fd
                /* 0038 */  0x65, 0x61, 0x63, 0x62                           // eacb
            },

            Buffer (0x3C)
            {
                /* 0000 */  0x81, 0x82, 0x64, 0x65, 0x66, 0x61, 0x31, 0x32,  // ..defa12
                /* 0008 */  0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x30,  // 34567890
                /* 0010 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x39, 0x38,  // abcdef98
                /* 0018 */  0x37, 0x36, 0x35, 0x34, 0x33, 0x32, 0x31, 0x30,  // 76543210
                /* 0020 */  0x66, 0x65, 0x64, 0x62, 0x63, 0x61, 0x31, 0x31,  // fedbca11
                /* 0028 */  0x32, 0x32, 0x33, 0x33, 0x34, 0x34, 0x35, 0x35,  // 22334455
                /* 0030 */  0x36, 0x36, 0x37, 0x37, 0x38, 0x38, 0x66, 0x64,  // 667788fd
                /* 0038 */  0x65, 0x61, 0x63, 0x62                           // eacb
            },

            Buffer (0x33)
            {
                /* 0000 */  0x81, 0x82, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,  // ..123456
                /* 0008 */  0x37, 0x38, 0x39, 0x30, 0x31, 0x31, 0x32, 0x32,  // 78901122
                /* 0010 */  0x33, 0x33, 0x34, 0x34, 0x35, 0x35, 0x36, 0x36,  // 33445566
                /* 0018 */  0x37, 0x37, 0x38, 0x38, 0x39, 0x39, 0x39, 0x38,  // 77889998
                /* 0020 */  0x37, 0x36, 0x35, 0x34, 0x33, 0x32, 0x31, 0x39,  // 76543219
                /* 0028 */  0x39, 0x39, 0x38, 0x33, 0x33, 0x33, 0x37, 0x37,  // 99833377
                /* 0030 */  0x34, 0x34, 0x7A                                 // 44z
            },

            Buffer (0x33)
            {
                /* 0000 */  0x81, 0x82, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,  // ..123456
                /* 0008 */  0x37, 0x38, 0x39, 0x30, 0x31, 0x31, 0x32, 0x32,  // 78901122
                /* 0010 */  0x33, 0x33, 0x34, 0x34, 0x35, 0x35, 0x36, 0x36,  // 33445566
                /* 0018 */  0x37, 0x37, 0x38, 0x38, 0x39, 0x39, 0x39, 0x38,  // 77889998
                /* 0020 */  0x37, 0x36, 0x35, 0x34, 0x33, 0x32, 0x31, 0x39,  // 76543219
                /* 0028 */  0x39, 0x39, 0x38, 0x33, 0x33, 0x33, 0x37, 0x37,  // 99833377
                /* 0030 */  0x34, 0x34, 0x7A                                 // 44z
            },

            /* X - Buffer */

            Buffer (0x05)
            {
                 0x81, 0x82, 0x91, 0x22, 0x83                     // ...".
            },

            Buffer (0x05)
            {
                 0x81, 0x82, 0x91, 0x22, 0x83                     // ...".
            },

            Buffer (0x03)
            {
                 0x81, 0x82, 0x80                                 // ...
            },

            Buffer (0x03)
            {
                 0x81, 0x82, 0x80                                 // ...
            },

            Buffer (0x04)
            {
                 0x81, 0x82, 0x81, 0x82                           // ....
            },

            Buffer (0x04)
            {
                 0x81, 0x82, 0x81, 0x82                           // ....
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x83, 0x84, 0x85, 0x86               // ......
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x83, 0x84, 0x85, 0x86               // ......
            },

            Buffer (0x07)
            {
                 0x81, 0x82, 0x87, 0x98, 0x99, 0x9A, 0x9B         // .......
            },

            Buffer (0x07)
            {
                 0x81, 0x82, 0x87, 0x98, 0x99, 0x9A, 0x9B         // .......
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x9C, 0x9D, 0x9E, 0x9F, 0xA0, 0xA1,  // ........
                /* 0008 */  0xA2, 0xA3                                       // ..
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x9C, 0x9D, 0x9E, 0x9F, 0xA0, 0xA1,  // ........
                /* 0008 */  0xA2, 0xA3                                       // ..
            },

            Buffer (0x0B)
            {
                /* 0000 */  0x81, 0x82, 0xA4, 0xA5, 0xA6, 0xA7, 0xB8, 0xB9,  // ........
                /* 0008 */  0xBA, 0xBB, 0xBC                                 // ...
            },

            Buffer (0x0B)
            {
                /* 0000 */  0x81, 0x82, 0xA4, 0xA5, 0xA6, 0xA7, 0xB8, 0xB9,  // ........
                /* 0008 */  0xBA, 0xBB, 0xBC                                 // ...
            },

            Buffer (0xCA)
            {
                /* 0000 */  0x81, 0x82, 0x91, 0x92, 0x93, 0x94, 0x5F, 0x60,  // ......_`
                /* 0008 */  0x61, 0x62, 0x63, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E,  // abc.....
                /* 0010 */  0x0F, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16,  // ........
                /* 0018 */  0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E,  // ........
                /* 0020 */  0x1F, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26,  // . !"#$%&
                /* 0028 */  0x27, 0x28, 0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E,  // '()*+,-.
                /* 0030 */  0x2F, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,  // /0123456
                /* 0038 */  0x37, 0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E,  // 789:;<=>
                /* 0040 */  0x3F, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46,  // ?@ABCDEF
                /* 0048 */  0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E,  // GHIJKLMN
                /* 0050 */  0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56,  // OPQRSTUV
                /* 0058 */  0x57, 0x58, 0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E,  // WXYZ[\]^
                /* 0060 */  0x5F, 0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66,  // _`abcdef
                /* 0068 */  0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E,  // ghijklmn
                /* 0070 */  0x6F, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76,  // opqrstuv
                /* 0078 */  0x77, 0x78, 0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E,  // wxyz{|}~
                /* 0080 */  0x7F, 0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86,  // ........
                /* 0088 */  0x87, 0x88, 0x89, 0x8A, 0x8B, 0x8C, 0x8D, 0x8E,  // ........
                /* 0090 */  0x8F, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96,  // ........
                /* 0098 */  0x97, 0x98, 0x99, 0x9A, 0x9B, 0x9C, 0x9D, 0x9E,  // ........
                /* 00A0 */  0x9F, 0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6,  // ........
                /* 00A8 */  0xA7, 0xA8, 0xA9, 0xAA, 0xAB, 0xAC, 0xAD, 0xAE,  // ........
                /* 00B0 */  0xAF, 0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6,  // ........
                /* 00B8 */  0xB7, 0xB8, 0xB9, 0xBA, 0xBB, 0xBC, 0xBD, 0xBE,  // ........
                /* 00C0 */  0xBF, 0xC0, 0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6,  // ........
                /* 00C8 */  0xC7, 0xC8                                       // ..
            },

            Buffer (0xCA)
            {
                /* 0000 */  0x81, 0x82, 0x91, 0x92, 0x93, 0x94, 0x5F, 0x60,  // ......_`
                /* 0008 */  0x61, 0x62, 0x63, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E,  // abc.....
                /* 0010 */  0x0F, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16,  // ........
                /* 0018 */  0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E,  // ........
                /* 0020 */  0x1F, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26,  // . !"#$%&
                /* 0028 */  0x27, 0x28, 0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E,  // '()*+,-.
                /* 0030 */  0x2F, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,  // /0123456
                /* 0038 */  0x37, 0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E,  // 789:;<=>
                /* 0040 */  0x3F, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46,  // ?@ABCDEF
                /* 0048 */  0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E,  // GHIJKLMN
                /* 0050 */  0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56,  // OPQRSTUV
                /* 0058 */  0x57, 0x58, 0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E,  // WXYZ[\]^
                /* 0060 */  0x5F, 0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66,  // _`abcdef
                /* 0068 */  0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E,  // ghijklmn
                /* 0070 */  0x6F, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76,  // opqrstuv
                /* 0078 */  0x77, 0x78, 0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E,  // wxyz{|}~
                /* 0080 */  0x7F, 0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86,  // ........
                /* 0088 */  0x87, 0x88, 0x89, 0x8A, 0x8B, 0x8C, 0x8D, 0x8E,  // ........
                /* 0090 */  0x8F, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96,  // ........
                /* 0098 */  0x97, 0x98, 0x99, 0x9A, 0x9B, 0x9C, 0x9D, 0x9E,  // ........
                /* 00A0 */  0x9F, 0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6,  // ........
                /* 00A8 */  0xA7, 0xA8, 0xA9, 0xAA, 0xAB, 0xAC, 0xAD, 0xAE,  // ........
                /* 00B0 */  0xAF, 0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6,  // ........
                /* 00B8 */  0xB7, 0xB8, 0xB9, 0xBA, 0xBB, 0xBC, 0xBD, 0xBE,  // ........
                /* 00C0 */  0xBF, 0xC0, 0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6,  // ........
                /* 00C8 */  0xC7, 0xC8                                       // ..
            },

            Buffer (0x0103)
            {
                /* 0000 */  0x81, 0x82, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06,  // ........
                /* 0008 */  0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E,  // ........
                /* 0010 */  0x0F, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16,  // ........
                /* 0018 */  0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E,  // ........
                /* 0020 */  0x1F, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26,  // . !"#$%&
                /* 0028 */  0x27, 0x28, 0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E,  // '()*+,-.
                /* 0030 */  0x2F, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,  // /0123456
                /* 0038 */  0x37, 0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E,  // 789:;<=>
                /* 0040 */  0x3F, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46,  // ?@ABCDEF
                /* 0048 */  0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E,  // GHIJKLMN
                /* 0050 */  0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56,  // OPQRSTUV
                /* 0058 */  0x57, 0x58, 0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E,  // WXYZ[\]^
                /* 0060 */  0x5F, 0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66,  // _`abcdef
                /* 0068 */  0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E,  // ghijklmn
                /* 0070 */  0x6F, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76,  // opqrstuv
                /* 0078 */  0x77, 0x78, 0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E,  // wxyz{|}~
                /* 0080 */  0x7F, 0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86,  // ........
                /* 0088 */  0x87, 0x88, 0x89, 0x8A, 0x8B, 0x8C, 0x8D, 0x8E,  // ........
                /* 0090 */  0x8F, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96,  // ........
                /* 0098 */  0x97, 0x98, 0x99, 0x9A, 0x9B, 0x9C, 0x9D, 0x9E,  // ........
                /* 00A0 */  0x9F, 0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6,  // ........
                /* 00A8 */  0xA7, 0xA8, 0xA9, 0xAA, 0xAB, 0xAC, 0xAD, 0xAE,  // ........
                /* 00B0 */  0xAF, 0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6,  // ........
                /* 00B8 */  0xB7, 0xB8, 0xB9, 0xBA, 0xBB, 0xBC, 0xBD, 0xBE,  // ........
                /* 00C0 */  0xBF, 0xC0, 0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6,  // ........
                /* 00C8 */  0xC7, 0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE,  // ........
                /* 00D0 */  0xCF, 0xD0, 0xD1, 0xD2, 0xD3, 0xD4, 0xD5, 0xD6,  // ........
                /* 00D8 */  0xD7, 0xD8, 0xD9, 0xDA, 0xDB, 0xDC, 0xDD, 0xDE,  // ........
                /* 00E0 */  0xDF, 0xE0, 0xE1, 0xE2, 0xE3, 0xE4, 0xE5, 0xE6,  // ........
                /* 00E8 */  0xE7, 0xE8, 0xE9, 0xEA, 0xEB, 0xEC, 0xED, 0xEE,  // ........
                /* 00F0 */  0xEF, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                /* 00F8 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                /* 0100 */  0xFF, 0x00, 0x01                                 // ...
            },

            Buffer (0x0103)
            {
                /* 0000 */  0x81, 0x82, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06,  // ........
                /* 0008 */  0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E,  // ........
                /* 0010 */  0x0F, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16,  // ........
                /* 0018 */  0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E,  // ........
                /* 0020 */  0x1F, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26,  // . !"#$%&
                /* 0028 */  0x27, 0x28, 0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E,  // '()*+,-.
                /* 0030 */  0x2F, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36,  // /0123456
                /* 0038 */  0x37, 0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E,  // 789:;<=>
                /* 0040 */  0x3F, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46,  // ?@ABCDEF
                /* 0048 */  0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E,  // GHIJKLMN
                /* 0050 */  0x4F, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56,  // OPQRSTUV
                /* 0058 */  0x57, 0x58, 0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E,  // WXYZ[\]^
                /* 0060 */  0x5F, 0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66,  // _`abcdef
                /* 0068 */  0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E,  // ghijklmn
                /* 0070 */  0x6F, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76,  // opqrstuv
                /* 0078 */  0x77, 0x78, 0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E,  // wxyz{|}~
                /* 0080 */  0x7F, 0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86,  // ........
                /* 0088 */  0x87, 0x88, 0x89, 0x8A, 0x8B, 0x8C, 0x8D, 0x8E,  // ........
                /* 0090 */  0x8F, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96,  // ........
                /* 0098 */  0x97, 0x98, 0x99, 0x9A, 0x9B, 0x9C, 0x9D, 0x9E,  // ........
                /* 00A0 */  0x9F, 0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6,  // ........
                /* 00A8 */  0xA7, 0xA8, 0xA9, 0xAA, 0xAB, 0xAC, 0xAD, 0xAE,  // ........
                /* 00B0 */  0xAF, 0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6,  // ........
                /* 00B8 */  0xB7, 0xB8, 0xB9, 0xBA, 0xBB, 0xBC, 0xBD, 0xBE,  // ........
                /* 00C0 */  0xBF, 0xC0, 0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6,  // ........
                /* 00C8 */  0xC7, 0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE,  // ........
                /* 00D0 */  0xCF, 0xD0, 0xD1, 0xD2, 0xD3, 0xD4, 0xD5, 0xD6,  // ........
                /* 00D8 */  0xD7, 0xD8, 0xD9, 0xDA, 0xDB, 0xDC, 0xDD, 0xDE,  // ........
                /* 00E0 */  0xDF, 0xE0, 0xE1, 0xE2, 0xE3, 0xE4, 0xE5, 0xE6,  // ........
                /* 00E8 */  0xE7, 0xE8, 0xE9, 0xEA, 0xEB, 0xEC, 0xED, 0xEE,  // ........
                /* 00F0 */  0xEF, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                /* 00F8 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                /* 0100 */  0xFF, 0x00, 0x01                                 // ...
            },

            /* X - Field Unit */

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x7F, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00                                       // ..
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x7F, 0x00, 0x00, 0x00               // ......
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00                                       // ..
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x07, 0x00, 0x00, 0x00               // ......
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x8D, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00                                       // ..
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x8D, 0x00, 0x00, 0x00               // ......
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x8D, 0x8C, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00                                       // ..
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x8D, 0x8C, 0x00, 0x00               // ......
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x8D, 0x8C, 0x8B, 0x8A, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00                                       // ..
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x8D, 0x8C, 0x8B, 0x8A               // ......
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x00,  // ........
                /* 0008 */  0x00, 0x00                                       // ..
            },

            Buffer (0x07)
            {
                 0x81, 0x82, 0xFF, 0xFF, 0xFF, 0xFF, 0x01         // .......
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x58, 0x46, 0x37, 0x88, 0x19, 0xFA,  // ..XF7...
                /* 0008 */  0xDE, 0x5C                                       // .\
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x58, 0x46, 0x37, 0x88, 0x19, 0xFA,  // ..XF7...
                /* 0008 */  0xDE, 0x5C                                       // .\
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA,  // ..X.7...
                /* 0008 */  0xDE, 0xDC                                       // ..
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA,  // ..X.7...
                /* 0008 */  0xDE, 0xDC                                       // ..
            },

            Buffer (0x0B)
            {
                /* 0000 */  0x81, 0x82, 0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA,  // ..X.7...
                /* 0008 */  0xDE, 0xDC, 0x00                                 // ...
            },

            Buffer (0x0B)
            {
                /* 0000 */  0x81, 0x82, 0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA,  // ..X.7...
                /* 0008 */  0xDE, 0xDC, 0x00                                 // ...
            },

            Buffer (0x12)
            {
                /* 0000 */  0x81, 0x82, 0x82, 0x34, 0x56, 0x78, 0x90, 0xAB,  // ...4Vx..
                /* 0008 */  0xCD, 0xEF, 0x55, 0x00, 0x00, 0x00, 0x00, 0x00,  // ..U.....
                /* 0010 */  0x00, 0x00                                       // ..
            },

            Buffer (0x12)
            {
                /* 0000 */  0x81, 0x82, 0x82, 0x34, 0x56, 0x78, 0x90, 0xAB,  // ...4Vx..
                /* 0008 */  0xCD, 0xEF, 0x55, 0x00, 0x00, 0x00, 0x00, 0x00,  // ..U.....
                /* 0010 */  0x00, 0x00                                       // ..
            },

            Buffer (0x23)
            {
                /* 0000 */  0x81, 0x82, 0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12,  // ........
                /* 0008 */  0xCD, 0x52, 0x87, 0x00, 0x00, 0x00, 0x00, 0x00,  // .R......
                /* 0010 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0018 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0020 */  0x00, 0x00, 0x00                                 // ...
            },

            Buffer (0x23)
            {
                /* 0000 */  0x81, 0x82, 0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12,  // ........
                /* 0008 */  0xCD, 0x52, 0x87, 0x00, 0x00, 0x00, 0x00, 0x00,  // .R......
                /* 0010 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0018 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0020 */  0x00, 0x00, 0x00                                 // ...
            },

            /* X - Buffer Field */

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0xAB, 0x54, 0x86, 0x91, 0x00, 0x00,  // ...T....
                /* 0008 */  0x00, 0x00                                       // ..
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0xAB, 0x54, 0x86, 0x91               // ...T..
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00                                       // ..
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x07, 0x00, 0x00, 0x00               // ......
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x8D, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00                                       // ..
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x8D, 0x00, 0x00, 0x00               // ......
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x8D, 0x8C, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00                                       // ..
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x8D, 0x8C, 0x00, 0x00               // ......
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x8D, 0x8C, 0x8B, 0x8A, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00                                       // ..
            },

            Buffer (0x06)
            {
                 0x81, 0x82, 0x8D, 0x8C, 0x8B, 0x8A               // ......
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x00,  // ........
                /* 0008 */  0x00, 0x00                                       // ..
            },

            Buffer (0x07)
            {
                 0x81, 0x82, 0xFF, 0xFF, 0xFF, 0xFF, 0x01         // .......
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x58, 0x46, 0x37, 0x88, 0x19, 0xFA,  // ..XF7...
                /* 0008 */  0xDE, 0x5C                                       // .\
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x58, 0x46, 0x37, 0x88, 0x19, 0xFA,  // ..XF7...
                /* 0008 */  0xDE, 0x5C                                       // .\
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA,  // ..X.7...
                /* 0008 */  0xDE, 0xDC                                       // ..
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x81, 0x82, 0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA,  // ..X.7...
                /* 0008 */  0xDE, 0xDC                                       // ..
            },

            Buffer (0x0B)
            {
                /* 0000 */  0x81, 0x82, 0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA,  // ..X.7...
                /* 0008 */  0xDE, 0xDC, 0x00                                 // ...
            },

            Buffer (0x0B)
            {
                /* 0000 */  0x81, 0x82, 0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA,  // ..X.7...
                /* 0008 */  0xDE, 0xDC, 0x00                                 // ...
            },

            Buffer (0x12)
            {
                /* 0000 */  0x81, 0x82, 0x82, 0x34, 0x56, 0x78, 0x90, 0xAB,  // ...4Vx..
                /* 0008 */  0xCD, 0xEF, 0x55, 0x00, 0x00, 0x00, 0x00, 0x00,  // ..U.....
                /* 0010 */  0x00, 0x00                                       // ..
            },

            Buffer (0x12)
            {
                /* 0000 */  0x81, 0x82, 0x82, 0x34, 0x56, 0x78, 0x90, 0xAB,  // ...4Vx..
                /* 0008 */  0xCD, 0xEF, 0x55, 0x00, 0x00, 0x00, 0x00, 0x00,  // ..U.....
                /* 0010 */  0x00, 0x00                                       // ..
            },

            Buffer (0x23)
            {
                /* 0000 */  0x81, 0x82, 0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12,  // ........
                /* 0008 */  0xCD, 0x52, 0x87, 0x00, 0x00, 0x00, 0x00, 0x00,  // .R......
                /* 0010 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0018 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0020 */  0x00, 0x00, 0x00                                 // ...
            },

            Buffer (0x23)
            {
                /* 0000 */  0x81, 0x82, 0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12,  // ........
                /* 0008 */  0xCD, 0x52, 0x87, 0x00, 0x00, 0x00, 0x00, 0x00,  // .R......
                /* 0010 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0018 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0020 */  0x00, 0x00, 0x00                                 // ...
            }
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P005, Package (0x62)
        {
            /* X - Integer */

            Buffer (0x10)
            {
                /* 0000 */  0x32, 0x54, 0x76, 0x58, 0x00, 0x00, 0x00, 0x00,  // 2TvX....
                /* 0008 */  0x81, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x32, 0x54, 0x76, 0x58, 0x81, 0x82, 0x00, 0x00   // 2TvX....
            },

            /* X - String */

            "qwrt81 82",
            "qwrt81 82",
            "svnmjkl81 82",
            "svnmjkl81 82",
            "1234zyq81 82",
            "1234zyq81 82",
            "abcdefzyq81 82",
            "abcdefzyq81 82",
            "987681 82",
            "987681 82",
            "aBcD81 82",
            "aBcD81 82",
            "123456789098765481 82",
            "123456789098765481 82",
            "daFeCBaabbddffee81 82",
            "daFeCBaabbddffee81 82",
            "1234567890abCdeF81 82",
            "1234567890abCdeF81 82",
            "FdeAcb013254769881 82",
            "FdeAcb013254769881 82",
            "1234567890987654081 82",
            "1234567890987654081 82",
            "fdeacb0132547698081 82",
            "fdeacb0132547698081 82",
            "12345678901122334455667788999876543219998333774481 82",
            "12345678901122334455667788999876543219998333774481 82",
            "abcdefaAbbccddeeffffeeddccaabbddeeffaaaabbbbeeefffdd81 82",
            "abcdefaAbbccddeeffffeeddccaabbddeeffaaaabbbbeeefffdd81 82",
            "1234567890abcdef9876543210fedbca1122334455667788fdeacb81 82",
            "1234567890abcdef9876543210fedbca1122334455667788fdeacb81 82",
            "defa1234567890abcdef9876543210fedbca1122334455667788fdeacb81 82",
            "defa1234567890abcdef9876543210fedbca1122334455667788fdeacb81 82",
            "123456789011223344556677889998765432199983337744z81 82",
            "123456789011223344556677889998765432199983337744z81 82",
            /* X - Buffer */

            Buffer (0x05)
            {
                 0x91, 0x22, 0x83, 0x81, 0x82                     // ."...
            },

            Buffer (0x05)
            {
                 0x91, 0x22, 0x83, 0x81, 0x82                     // ."...
            },

            Buffer (0x03)
            {
                 0x80, 0x81, 0x82                                 // ...
            },

            Buffer (0x03)
            {
                 0x80, 0x81, 0x82                                 // ...
            },

            Buffer (0x04)
            {
                 0x81, 0x82, 0x81, 0x82                           // ....
            },

            Buffer (0x04)
            {
                 0x81, 0x82, 0x81, 0x82                           // ....
            },

            Buffer (0x06)
            {
                 0x83, 0x84, 0x85, 0x86, 0x81, 0x82               // ......
            },

            Buffer (0x06)
            {
                 0x83, 0x84, 0x85, 0x86, 0x81, 0x82               // ......
            },

            Buffer (0x07)
            {
                 0x87, 0x98, 0x99, 0x9A, 0x9B, 0x81, 0x82         // .......
            },

            Buffer (0x07)
            {
                 0x87, 0x98, 0x99, 0x9A, 0x9B, 0x81, 0x82         // .......
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x9C, 0x9D, 0x9E, 0x9F, 0xA0, 0xA1, 0xA2, 0xA3,  // ........
                /* 0008 */  0x81, 0x82                                       // ..
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x9C, 0x9D, 0x9E, 0x9F, 0xA0, 0xA1, 0xA2, 0xA3,  // ........
                /* 0008 */  0x81, 0x82                                       // ..
            },

            Buffer (0x0B)
            {
                /* 0000 */  0xA4, 0xA5, 0xA6, 0xA7, 0xB8, 0xB9, 0xBA, 0xBB,  // ........
                /* 0008 */  0xBC, 0x81, 0x82                                 // ...
            },

            Buffer (0x0B)
            {
                /* 0000 */  0xA4, 0xA5, 0xA6, 0xA7, 0xB8, 0xB9, 0xBA, 0xBB,  // ........
                /* 0008 */  0xBC, 0x81, 0x82                                 // ...
            },

            Buffer (0xCA)
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
                /* 00C0 */  0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7, 0xC8,  // ........
                /* 00C8 */  0x81, 0x82                                       // ..
            },

            Buffer (0xCA)
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
                /* 00C0 */  0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7, 0xC8,  // ........
                /* 00C8 */  0x81, 0x82                                       // ..
            },

            Buffer (0x0103)
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
                /* 0100 */  0x01, 0x81, 0x82                                 // ...
            },

            Buffer (0x0103)
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
                /* 0100 */  0x01, 0x81, 0x82                                 // ...
            },

            /* X - Field Unit */

            Buffer (0x10)
            {
                /* 0000 */  0x7F, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x81, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x7F, 0x00, 0x00, 0x00, 0x81, 0x82, 0x00, 0x00   // ........
            },

            Buffer (0x10)
            {
                /* 0000 */  0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x81, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x07, 0x00, 0x00, 0x00, 0x81, 0x82, 0x00, 0x00   // ........
            },

            Buffer (0x10)
            {
                /* 0000 */  0x8D, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x81, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x8D, 0x00, 0x00, 0x00, 0x81, 0x82, 0x00, 0x00   // ........
            },

            Buffer (0x10)
            {
                /* 0000 */  0x8D, 0x8C, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x81, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x8D, 0x8C, 0x00, 0x00, 0x81, 0x82, 0x00, 0x00   // ........
            },

            Buffer (0x10)
            {
                /* 0000 */  0x8D, 0x8C, 0x8B, 0x8A, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x81, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x8D, 0x8C, 0x8B, 0x8A, 0x81, 0x82, 0x00, 0x00   // ........
            },

            Buffer (0x10)
            {
                /* 0000 */  0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x81, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x07)
            {
                 0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x81, 0x82         // .......
            },

            ToUUID ("88374658-fa19-5cde-8182-000000000000"),
            Buffer (0x0A)
            {
                /* 0000 */  0x58, 0x46, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0x5C,  // XF7....\
                /* 0008 */  0x81, 0x82                                       // ..
            },

            Buffer (0x10)
            {
                /* 0000 */  0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x81, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x81, 0x82                                       // ..
            },

            Buffer (0x0B)
            {
                /* 0000 */  0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x00, 0x81, 0x82                                 // ...
            },

            Buffer (0x0B)
            {
                /* 0000 */  0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x00, 0x81, 0x82                                 // ...
            },

            Buffer (0x12)
            {
                /* 0000 */  0x82, 0x34, 0x56, 0x78, 0x90, 0xAB, 0xCD, 0xEF,  // .4Vx....
                /* 0008 */  0x55, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // U.......
                /* 0010 */  0x81, 0x82                                       // ..
            },

            Buffer (0x12)
            {
                /* 0000 */  0x82, 0x34, 0x56, 0x78, 0x90, 0xAB, 0xCD, 0xEF,  // .4Vx....
                /* 0008 */  0x55, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // U.......
                /* 0010 */  0x81, 0x82                                       // ..
            },

            Buffer (0x23)
            {
                /* 0000 */  0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12, 0xCD, 0x52,  // .......R
                /* 0008 */  0x87, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0010 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0018 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0020 */  0x00, 0x81, 0x82                                 // ...
            },

            Buffer (0x23)
            {
                /* 0000 */  0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12, 0xCD, 0x52,  // .......R
                /* 0008 */  0x87, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0010 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0018 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0020 */  0x00, 0x81, 0x82                                 // ...
            },

            /* X - Buffer Field */

            Buffer (0x10)
            {
                /* 0000 */  0xAB, 0x54, 0x86, 0x91, 0x00, 0x00, 0x00, 0x00,  // .T......
                /* 0008 */  0x81, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0xAB, 0x54, 0x86, 0x91, 0x81, 0x82, 0x00, 0x00   // .T......
            },

            Buffer (0x10)
            {
                /* 0000 */  0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x81, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x07, 0x00, 0x00, 0x00, 0x81, 0x82, 0x00, 0x00   // ........
            },

            Buffer (0x10)
            {
                /* 0000 */  0x8D, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x81, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x8D, 0x00, 0x00, 0x00, 0x81, 0x82, 0x00, 0x00   // ........
            },

            Buffer (0x10)
            {
                /* 0000 */  0x8D, 0x8C, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x81, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x8D, 0x8C, 0x00, 0x00, 0x81, 0x82, 0x00, 0x00   // ........
            },

            Buffer (0x10)
            {
                /* 0000 */  0x8D, 0x8C, 0x8B, 0x8A, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x81, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x08)
            {
                 0x8D, 0x8C, 0x8B, 0x8A, 0x81, 0x82, 0x00, 0x00   // ........
            },

            Buffer (0x10)
            {
                /* 0000 */  0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x81, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x07)
            {
                 0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x81, 0x82         // .......
            },

            ToUUID ("88374658-fa19-5cde-8182-000000000000"),
            Buffer (0x0A)
            {
                /* 0000 */  0x58, 0x46, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0x5C,  // XF7....\
                /* 0008 */  0x81, 0x82                                       // ..
            },

            Buffer (0x10)
            {
                /* 0000 */  0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x81, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            },

            Buffer (0x0A)
            {
                /* 0000 */  0x58, 0x9A, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x81, 0x82                                       // ..
            },

            Buffer (0x0B)
            {
                /* 0000 */  0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x00, 0x81, 0x82                                 // ...
            },

            Buffer (0x0B)
            {
                /* 0000 */  0x58, 0xC7, 0x37, 0x88, 0x19, 0xFA, 0xDE, 0xDC,  // X.7.....
                /* 0008 */  0x00, 0x81, 0x82                                 // ...
            },

            Buffer (0x12)
            {
                /* 0000 */  0x82, 0x34, 0x56, 0x78, 0x90, 0xAB, 0xCD, 0xEF,  // .4Vx....
                /* 0008 */  0x55, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // U.......
                /* 0010 */  0x81, 0x82                                       // ..
            },

            Buffer (0x12)
            {
                /* 0000 */  0x82, 0x34, 0x56, 0x78, 0x90, 0xAB, 0xCD, 0xEF,  // .4Vx....
                /* 0008 */  0x55, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // U.......
                /* 0010 */  0x81, 0x82                                       // ..
            },

            Buffer (0x23)
            {
                /* 0000 */  0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12, 0xCD, 0x52,  // .......R
                /* 0008 */  0x87, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0010 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0018 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0020 */  0x00, 0x81, 0x82                                 // ...
            },

            Buffer (0x23)
            {
                /* 0000 */  0x93, 0xAB, 0xCD, 0xEF, 0x99, 0x12, 0xCD, 0x52,  // .......R
                /* 0008 */  0x87, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0010 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0018 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0020 */  0x00, 0x81, 0x82                                 // ...
            }
        })
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
                /*		Store(0x200, df00) */
        /*		Store(m488(op, 0, 0x1ed1, 0, 0, 0), Local7) */
        /*		Store(0x300, df00) */
        /*		Store(m488(op, 0, 0x1ed1, 0, 0, 0), Local7) */
        }
        Else
        {
            FLG1 = 0x01
            /* (Integer ==> All other types) */
            /* (All other types ==> Integer) */
            COM2 = 0x02
            /*		Store(p000, PKG1) */
            /*		Store(p001, PKG2) */
            M48B (OP, 0x0103)
            /* (String ==> All other types) */
            /* (All other types ==> String) */
            COM2 = 0x02
            /*		Store(p002, PKG1) */
            /*		Store(p003, PKG2) */
            M48B (OP, 0x0204)
            /* (Buffer ==> All other types) */
            /* (All other types ==> Buffer) */
            COM2 = 0x02
            /*		Store(p004, PKG1) */
            /*		Store(p005, PKG2) */
            M48B (OP, 0x0302)
            /*		Store(PKG0, PKG1) */
            /*		Store(PKG0, PKG2) */
            COM2 = 0x00
            FLG1 = 0x00
        }
    }

    /* ConcatenateResTemplate (rtb, rtb, Result) => Buffer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source1: 0x5ef7 */
    /*    Source2: 0x5ef7 */
    /* Total scale of acceptable types: */
    /*    Source1: 0x0008 */
    /*    Source2: 0x0008 */
    Method (M404, 1, Serialized)
    {
        Name (OP, 0x04)
        TS00 ("m404")
        If (Arg0)
        {
            M486 ()
            DF00 = 0x030B
            DF01 = 0x030B
            Local7 = M488 (OP, 0x5FFF, 0x5FFF, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* CondRefOf (any, Result) => Boolean */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source: 0x0000 */
    /* Total scale of acceptable types: */
    /*    Source: 0x5eff */
    Method (M405, 1, Serialized)
    {
        Name (OP, 0x05)
        TS00 ("m405")
        If (Arg0)
        {
            M486 ()
            /* Error: CondRefOf fails with the Uninitialized type */

            Local7 = M488 (OP, 0x01, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* CopyObject (any, Destination) => DataRefObject */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source: 0x0000 */
    /* Total scale of acceptable types: */
    /*    Source: 0x5eff */
    Method (M406, 1, Serialized)
    {
        Name (OP, 0x06)
        TS00 ("m406")
        If (Arg0)
        {
            M486 ()
            /* Error: CopyObject fails with the Uninitialized type */

            Local7 = M488 (OP, 0x01, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* Decrement (int) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Minuend: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Minuend: 0x402e */
    Method (M407, 1, Serialized)
    {
        Name (OP, 0x07)
        Name (TS, "m407")
        TS00 (TS)
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x1ED1, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
            Local7 = M48D (OP, 0x0102, 0x00, 0x00, 0x00, 0x12345677, 0x12345677)
            Local7 = M48D (OP, 0x0204, 0x00, 0x00, 0x00, 0x9875, 0x9875)
            Local7 = M48D (OP, 0x0209, 0x00, 0x00, 0x00, 0xFDEACB0132547697, 0x32547697)
            Local7 = M48D (OP, 0x0302, 0x00, 0x00, 0x00, 0x8280, 0x8280)
            Local7 = M48D (OP, 0x0308, 0x00, 0x00, 0x00, 0x0807060504030200, 0x04030200)
            Local7 = M48D (OP, 0x0506, 0x00, 0x00, 0x00, 0x5CDEFA1988374657, 0x88374657)
            Local7 = M48D (OP, 0x0E06, 0x00, 0x00, 0x00, 0x5CDEFA1988374657, 0x88374657)
            /* Exceptions */

            Local7 = M48D (OP, 0x0202, 0x00, 0x00, 0x00, "Exc", "Exc")
            Local7 = M48D (OP, 0x020A, 0x00, 0x00, 0x00, "Exc", "Exc")
            Local7 = M48D (OP, 0x0210, 0x00, 0x00, 0x00, "Exc", "Exc")
        }
    }

    /* DerefOf ({ref|str}) => Object */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source: 0x5fff */
    /* Total scale of acceptable types: */
    /*    Source: 0x0000 */
    Method (M408, 1, Serialized)
    {
        Name (OP, 0x08)
        TS00 ("m408")
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x5FFF, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* Divide (int, int, Remainder, Result) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Dividend: 0x1ed1 */
    /*    Divisor: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Dividend: 0x402e */
    /*    Divisor: 0x402e */
    Method (M409, 1, Serialized)
    {
        Name (OP, 0x09)
        TS00 ("m409")
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
            Local7 = M48D (OP, 0x0102, 0x0102, 0x00, 0x00, 0x01, 0x01)
            Local7 = M48D (OP, 0x0103, 0x0102, 0x00, 0x00, 0x0000000971C214EA, 0x03)
            Local7 = M48D (OP, 0x0204, 0x0102, 0x00, 0x00, 0x00, 0x00)
            Local7 = M48D (OP, 0x0209, 0x0102, 0x00, 0x00, 0x0000000DF2B5C737, 0x02)
            Local7 = M48D (OP, 0x0302, 0x0102, 0x00, 0x00, 0x00, 0x00)
            Local7 = M48D (OP, 0x0308, 0x0102, 0x00, 0x00, 0x70E2C4AA, 0x00)
            Local7 = M48D (OP, 0x0506, 0x0102, 0x00, 0x00, 0x0000000519FF9D32, 0x07)
            Local7 = M48D (OP, 0x0E06, 0x0102, 0x00, 0x00, 0x0000000519FF9D32, 0x07)
            Local7 = M48D (OP, 0x0103, 0x0204, 0x00, 0x00, 0x000120B0A1E2C2D5, 0x6F2A)
            /* Exceptions */

            Local7 = M48D (OP, 0x0202, 0x0102, 0x00, 0x00, "Exc", "Exc")
            Local7 = M48D (OP, 0x020A, 0x0102, 0x00, 0x00, "Exc", "Exc")
            Local7 = M48D (OP, 0x0210, 0x0102, 0x00, 0x00, "Exc", "Exc")
            Local7 = M48D (OP, 0x0102, 0x0202, 0x00, 0x00, "Exc", "Exc")
            Local7 = M48D (OP, 0x0102, 0x020A, 0x00, 0x00, "Exc", "Exc")
            Local7 = M48D (OP, 0x0102, 0x0210, 0x00, 0x00, "Exc", "Exc")
        }
    }

    /* Fatal (byt, dwd, int) */
    /* */
    /* iasl: "Fatal operator requires [Integer|String|Buffer]" */
    /* Total scale of unacceptable types: */
    /*    Arg: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Arg: 0x402e */
    Method (M410, 1, Serialized)
    {
        Name (OP, 0x0A)
        TS00 ("m410")
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x1ED1, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* FindSetLeftBit (int, Result) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source: 0x402e */
    Method (M411, 1, Serialized)
    {
        Name (OP, 0x0B)
        TS00 ("m411")
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x1ED1, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
            Local7 = M48D (OP, 0x0102, 0x00, 0x00, 0x00, 0x1D, 0x1D)
            Local7 = M48D (OP, 0x0204, 0x00, 0x00, 0x00, 0x10, 0x10)
            Local7 = M48D (OP, 0x0206, 0x00, 0x00, 0x00, 0x3D, 0x20)
            /* Exceptions */

            Local7 = M48D (OP, 0x0202, 0x00, 0x00, 0x00, "Exc", "Exc")
            Local7 = M48D (OP, 0x020A, 0x00, 0x00, 0x00, "Exc", "Exc")
            Local7 = M48D (OP, 0x0210, 0x00, 0x00, 0x00, "Exc", "Exc")
        }
    }

    /* FindSetRightBit (int, Result) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source: 0x402e */
    Method (M412, 1, Serialized)
    {
        Name (OP, 0x0C)
        TS00 ("m412")
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x1ED1, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
            Local7 = M48D (OP, 0x0102, 0x00, 0x00, 0x00, 0x04, 0x04)
            Local7 = M48D (OP, 0x0204, 0x00, 0x00, 0x00, 0x02, 0x02)
            Local7 = M48D (OP, 0x0206, 0x00, 0x00, 0x00, 0x03, 0x03)
            /* Exceptions */

            Local7 = M48D (OP, 0x0202, 0x00, 0x00, 0x00, "Exc", "Exc")
            Local7 = M48D (OP, 0x020A, 0x00, 0x00, 0x00, "Exc", "Exc")
            Local7 = M48D (OP, 0x0210, 0x00, 0x00, 0x00, "Exc", "Exc")
        }
    }

    /* FromBCD (int, Result) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    BCDValue: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    BCDValue: 0x402e */
    Method (M413, 1, Serialized)
    {
        Name (OP, 0x0D)
        TS00 ("m413")
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x1ED1, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* Increment (int) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Addend: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Addend: 0x402e */
    Method (M414, 1, Serialized)
    {
        Name (OP, 0x0E)
        TS00 ("m414")
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x1ED1, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
            Local7 = M48D (OP, 0x0102, 0x00, 0x00, 0x00, 0x12345679, 0x12345679)
            Local7 = M48D (OP, 0x0204, 0x00, 0x00, 0x00, 0x9877, 0x9877)
            Local7 = M48D (OP, 0x0209, 0x00, 0x00, 0x00, 0xFDEACB0132547699, 0x32547699)
            Local7 = M48D (OP, 0x0302, 0x00, 0x00, 0x00, 0x8282, 0x8282)
            Local7 = M48D (OP, 0x0308, 0x00, 0x00, 0x00, 0x0807060504030202, 0x04030202)
            Local7 = M48D (OP, 0x0506, 0x00, 0x00, 0x00, 0x5CDEFA1988374659, 0x88374659)
            Local7 = M48D (OP, 0x0E06, 0x00, 0x00, 0x00, 0x5CDEFA1988374659, 0x88374659)
            /* Exceptions */

            Local7 = M48D (OP, 0x0202, 0x00, 0x00, 0x00, "Exc", "Exc")
            Local7 = M48D (OP, 0x020A, 0x00, 0x00, 0x00, "Exc", "Exc")
            Local7 = M48D (OP, 0x0210, 0x00, 0x00, 0x00, "Exc", "Exc")
        }
    }

    /* Index ({str|buf|pkg}, int, Destination) => ObjectReference */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source: 0x5fe3 */
    /*    Index: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source: 0x001c */
    /*    Index: 0x402e */
    Method (M415, 1, Serialized)
    {
        Name (OP, 0x0F)
        TS00 ("m415")
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0200
            DF01 = 0x0104  /* Zero */
            Local7 = M488 (OP, 0x5FE3, 0x1ED1, 0x00, 0x00, 0x00)
                /*
         // The action above together with those below generates exception
         Store(0x300, df00)
         Store(m488(op, 0, 0x1ed1, 0, 0, 0), Local7)
         Store(0x400, df00)
         Store(m488(op, 0, 0x1ed1, 0, 0, 0), Local7)
         */
        }
        Else
        {
        }
    }

    /* LAnd (int, int) => Boolean */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source1: 0x1ed1 */
    /*    Source2: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source1: 0x402e */
    /*    Source2: 0x402e */
    Method (M416, 1, Serialized)
    {
        Name (OP, 0x10)
        TS00 ("m416")
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* LEqual ({int|str|buf}, {int|str|buf}) => Boolean */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source1: 0x1ed1 */
    /*    Source2: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source1: 0x402e */
    /*    Source2: 0x402e */
    Method (M417, 1, Serialized)
    {
        Name (OP, 0x11)
        TS00 ("m417")
        /* Expected results: 64-bit, 32-bit */

        Name (P000, Package (0x62)
        {
            /* X - Integer */

            Zero,
            Zero,
            /* X - String */

            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            /* X - Buffer */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Field Unit */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer Field */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P001, Package (0x62)
        {
            /* X - Integer */

            Zero,
            Zero,
            /* X - String */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Field Unit */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer Field */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P002, Package (0x62)
        {
            /* X - Integer */

            Zero,
            Zero,
            /* X - String */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            /* X - Field Unit */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer Field */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P003, Package (0x62)
        {
            /* X - Integer */

            Zero,
            Zero,
            /* X - String */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Field Unit */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer Field */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P004, Package (0x62)
        {
            /* X - Integer */

            Zero,
            Zero,
            /* X - String */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer */

            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Field Unit */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer Field */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P005, Package (0x62)
        {
            /* X - Integer */

            Zero,
            Zero,
            /* X - String */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer */

            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Field Unit */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer Field */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero
        })
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
            FLG1 = 0x01
            /* (Integer ==> All other types) */
            /* (All other types ==> Integer)2556 */
            COM2 = 0x02
            /*		Store(p000, PKG1) */
            /*		Store(p001, PKG2) */
            M48B (OP, 0x0103)
            /* (String ==> All other types) */
            /* (All other types ==> String) */
            COM2 = 0x02
            /*		Store(p002, PKG1) */
            /*		Store(p003, PKG2) */
            M48B (OP, 0x0204)
            /* (Buffer ==> All other types) */
            /* (All other types ==> Buffer) */
            COM2 = 0x02
            /*		Store(p004, PKG1) */
            /*		Store(p005, PKG2) */
            M48B (OP, 0x0302)
            /*		Store(PKG0, PKG1) */
            /*		Store(PKG0, PKG2) */
            COM2 = 0x00
            FLG1 = 0x00
        }
    }

    /* LGreater ({int|str|buf}, {int|str|buf}) => Boolean */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source1: 0x1ed1 */
    /*    Source2: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source1: 0x402e */
    /*    Source2: 0x402e */
    Method (M418, 1, Serialized)
    {
        Name (OP, 0x12)
        TS00 ("m418")
        /* Expected results: 64-bit, 32-bit */

        Name (P000, Package (0x62)
        {
            /* X - Integer, (0) */

            Ones,
            Zero,
            /* X - String, (1) */

            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Zero,
            Ones,
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            /* X - Buffer, (18) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Ones,
            Ones,
            /* X - Field Unit, (27) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            /* X - Buffer Field, (38) */

            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P001, Package (0x62)
        {
            /* X - Integer, (0) */

            Zero,
            Ones,
            /* X - String, (1) */

            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            /* X - Buffer, (18) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            /* X - Field Unit, (27) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Ones,
            Zero,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer Field, (38) */

            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Ones,
            Zero,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P002, Package (0x62)
        {
            /* X - Integer, (0) */

            Ones,
            Ones,
            /* X - String, (1) */

            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            /* X - Buffer, (18) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            /* X - Field Unit, (27) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer Field, (38) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P003, Package (0x62)
        {
            /* X - Integer, (0) */

            Ones,
            Ones,
            /* X - String, (1) */

            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            /* X - Buffer, (18) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            /* X - Field Unit, (27) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer Field, (38) */

            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P004, Package (0x62)
        {
            /* X - Integer, (0) */

            Ones,
            Ones,
            /* X - String, (1) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer, (18) */

            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            /* X - Field Unit, (27) */

            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer Field, (38) */

            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P005, Package (0x62)
        {
            /* X - Integer, (0) */

            Ones,
            Ones,
            /* X - String, (1) */

            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            /* X - Buffer, (18) */

            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            /* X - Field Unit, (27) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer Field, (38) */

            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones
        })
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
            FLG1 = 0x01
            /* (Integer ==> All other types) */
            /* (All other types ==> Integer) */
            COM2 = 0x02
            /*		Store(p000, PKG1) */
            /*		Store(p001, PKG2) */
            M48B (OP, 0x0103)
            /* (String ==> All other types) */
            /* (All other types ==> String) */
            COM2 = 0x02
            /*		Store(p002, PKG1) */
            /*		Store(p003, PKG2) */
            M48B (OP, 0x0204)
            /* (Buffer ==> All other types) */
            /* (All other types ==> Buffer) */
            COM2 = 0x02
            /*		Store(p004, PKG1) */
            /*		Store(p005, PKG2) */
            M48B (OP, 0x0302)
            /*		Store(PKG0, PKG1) */
            /*		Store(PKG0, PKG2) */
            COM2 = 0x00
            FLG1 = 0x00
        }
    }

    /* LGreaterEqual ({int|str|buf}, {int|str|buf}) => Boolean */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source1: 0x1ed1 */
    /*    Source2: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source1: 0x402e */
    /*    Source2: 0x402e */
    Method (M419, 1, Serialized)
    {
        Name (OP, 0x13)
        TS00 ("m419")
        /* Expected results: 64-bit, 32-bit */

        Name (P000, Package (0x62)
        {
            /* X - Integer, (0) */

            Ones,
            Zero,
            /* X - String, (1) */

            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Zero,
            Ones,
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            /* X - Buffer, (18) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Ones,
            Ones,
            /* X - Field Unit, (27) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            /* X - Buffer Field, (38) */

            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P001, Package (0x62)
        {
            /* X - Integer, (0) */

            Zero,
            Ones,
            /* X - String, (1) */

            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            /* X - Buffer, (18) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            /* X - Field Unit, (27) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Ones,
            Zero,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer Field, (38) */

            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Ones,
            Zero,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P002, Package (0x62)
        {
            /* X - Integer, (0) */

            Ones,
            Ones,
            /* X - String, (1) */

            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            /* X - Buffer, (18) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            /* X - Field Unit, (27) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer Field, (38) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P003, Package (0x62)
        {
            /* X - Integer, (0) */

            Ones,
            Ones,
            /* X - String, (1) */

            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            /* X - Buffer, (18) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            /* X - Field Unit, (27) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer Field, (38) */

            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P004, Package (0x62)
        {
            /* X - Integer, (0) */

            Ones,
            Ones,
            /* X - String, (1) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer, (18) */

            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            /* X - Field Unit, (27) */

            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer Field, (38) */

            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P005, Package (0x62)
        {
            /* X - Integer, (0) */

            Ones,
            Ones,
            /* X - String, (1) */

            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            /* X - Buffer, (18) */

            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            /* X - Field Unit, (27) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer Field, (38) */

            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones
        })
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
            FLG1 = 0x01
            /* (Integer ==> All other types) */
            /* (All other types ==> Integer) */
            COM2 = 0x02
            /*		Store(p000, PKG1) */
            /*		Store(p001, PKG2) */
            M48B (OP, 0x0103)
            /* (String ==> All other types) */
            /* (All other types ==> String) */
            COM2 = 0x02
            /*		Store(p002, PKG1) */
            /*		Store(p003, PKG2) */
            M48B (OP, 0x0204)
            /* (Buffer ==> All other types) */
            /* (All other types ==> Buffer) */
            COM2 = 0x02
            /*		Store(p004, PKG1) */
            /*		Store(p005, PKG2) */
            M48B (OP, 0x0302)
            /*		Store(PKG0, PKG1) */
            /*		Store(PKG0, PKG2) */
            COM2 = 0x00
            FLG1 = 0x00
        }
    }

    /* LLess ({int|str|buf}, {int|str|buf}) => Boolean */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source1: 0x1ed1 */
    /*    Source2: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source1: 0x402e */
    /*    Source2: 0x402e */
    Method (M420, 1, Serialized)
    {
        Name (OP, 0x14)
        TS00 ("m420")
        /* Expected results: 64-bit, 32-bit */

        Name (P000, Package (0x62)
        {
            /* X - Integer, (0) */

            Zero,
            Ones,
            /* X - String, (1) */

            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Ones,
            Zero,
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            /* X - Buffer, (18) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Zero,
            Zero,
            /* X - Field Unit, (27) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            /* X - Buffer Field, (38) */

            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P001, Package (0x62)
        {
            /* X - Integer, (0) */

            Ones,
            Zero,
            /* X - String, (1) */

            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            /* X - Buffer, (18) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            /* X - Field Unit, (27) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Zero,
            Ones,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer Field, (38) */

            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Zero,
            Ones,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P002, Package (0x62)
        {
            /* X - Integer, (0) */

            Zero,
            Zero,
            /* X - String, (1) */

            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            /* X - Buffer, (18) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            /* X - Field Unit, (27) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer Field, (38) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P003, Package (0x62)
        {
            /* X - Integer, (0) */

            Zero,
            Zero,
            /* X - String, (1) */

            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            /* X - Buffer, (18) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            /* X - Field Unit, (27) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer Field, (38) */

            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P004, Package (0x62)
        {
            /* X - Integer, (0) */

            Zero,
            Zero,
            /* X - String, (1) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer, (18) */

            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            /* X - Field Unit, (27) */

            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer Field, (38) */

            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P005, Package (0x62)
        {
            /* X - Integer, (0) */

            Zero,
            Zero,
            /* X - String, (1) */

            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            /* X - Buffer, (18) */

            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            /* X - Field Unit, (27) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer Field, (38) */

            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero
        })
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
            FLG1 = 0x01
            /* (Integer ==> All other types) */
            /* (All other types ==> Integer) */
            COM2 = 0x02
            /*		Store(p000, PKG1) */
            /*		Store(p001, PKG2) */
            M48B (OP, 0x0103)
            /* (String ==> All other types) */
            /* (All other types ==> String) */
            COM2 = 0x02
            /*		Store(p002, PKG1) */
            /*		Store(p003, PKG2) */
            M48B (OP, 0x0204)
            /* (Buffer ==> All other types) */
            /* (All other types ==> Buffer) */
            COM2 = 0x02
            /*		Store(p004, PKG1) */
            /*		Store(p005, PKG2) */
            M48B (OP, 0x0302)
            /*		Store(PKG0, PKG1) */
            /*		Store(PKG0, PKG2) */
            COM2 = 0x00
            FLG1 = 0x00
        }
    }

    /* LLessEqual ({int|str|buf}, {int|str|buf}) => Boolean */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source1: 0x1ed1 */
    /*    Source2: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source1: 0x402e */
    /*    Source2: 0x402e */
    Method (M421, 1, Serialized)
    {
        Name (OP, 0x15)
        TS00 ("m421")
        /* Expected results: 64-bit, 32-bit */

        Name (P000, Package (0x62)
        {
            /* X - Integer, (0) */

            Zero,
            Ones,
            /* X - String, (1) */

            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Ones,
            Zero,
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            /* X - Buffer, (18) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Zero,
            Zero,
            /* X - Field Unit, (27) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            /* X - Buffer Field, (38) */

            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P001, Package (0x62)
        {
            /* X - Integer, (0) */

            Ones,
            Zero,
            /* X - String, (1) */

            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            /* X - Buffer, (18) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            /* X - Field Unit, (27) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Zero,
            Ones,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer Field, (38) */

            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Ones,
            Zero,
            Ones,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P002, Package (0x62)
        {
            /* X - Integer, (0) */

            Zero,
            Zero,
            /* X - String, (1) */

            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            /* X - Buffer, (18) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            /* X - Field Unit, (27) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer Field, (38) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Zero,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P003, Package (0x62)
        {
            /* X - Integer, (0) */

            Zero,
            Zero,
            /* X - String, (1) */

            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            /* X - Buffer, (18) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            /* X - Field Unit, (27) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer Field, (38) */

            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P004, Package (0x62)
        {
            /* X - Integer, (0) */

            Zero,
            Zero,
            /* X - String, (1) */

            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer, (18) */

            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            /* X - Field Unit, (27) */

            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer Field, (38) */

            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P005, Package (0x62)
        {
            /* X - Integer, (0) */

            Zero,
            Zero,
            /* X - String, (1) */

            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            /* X - Buffer, (18) */

            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Ones,
            /* X - Field Unit, (27) */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            /* X - Buffer Field, (38) */

            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Zero,
            Ones,
            Zero,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Zero,
            Zero
        })
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
            FLG1 = 0x01
            /* (Integer ==> All other types) */
            /* (All other types ==> Integer) */
            COM2 = 0x02
            /*		Store(p000, PKG1) */
            /*		Store(p001, PKG2) */
            M48B (OP, 0x0103)
            /* (String ==> All other types) */
            /* (All other types ==> String) */
            COM2 = 0x02
            /*		Store(p002, PKG1) */
            /*		Store(p003, PKG2) */
            M48B (OP, 0x0204)
            /* (Buffer ==> All other types) */
            /* (All other types ==> Buffer) */
            COM2 = 0x02
            /*		Store(p004, PKG1) */
            /*		Store(p005, PKG2) */
            M48B (OP, 0x0302)
            /*		Store(PKG0, PKG1) */
            /*		Store(PKG0, PKG2) */
            COM2 = 0x00
            FLG1 = 0x00
        }
    }

    /* LNot (int) => Boolean */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source: 0x402e */
    Method (M422, 1, Serialized)
    {
        Name (OP, 0x16)
        TS00 ("m422")
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x1ED1, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* LNotEqual ({int|str|buf}, {int|str|buf}) => Boolean */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source1: 0x1ed1 */
    /*    Source2: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source1: 0x402e */
    /*    Source2: 0x402e */
    Method (M423, 1, Serialized)
    {
        Name (OP, 0x17)
        TS00 ("m423")
        /* Expected results: 64-bit, 32-bit */

        Name (P000, Package (0x62)
        {
            /* X - Integer */

            Ones,
            Ones,
            /* X - String */

            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            /* X - Buffer */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Field Unit */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer Field */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P001, Package (0x62)
        {
            /* X - Integer */

            Ones,
            Ones,
            /* X - String */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Field Unit */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer Field */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P002, Package (0x62)
        {
            /* X - Integer */

            Ones,
            Ones,
            /* X - String */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            "Exc",
            "Exc",
            "Exc",
            "Exc",
            /* X - Field Unit */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer Field */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P003, Package (0x62)
        {
            /* X - Integer */

            Ones,
            Ones,
            /* X - String */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Field Unit */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer Field */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P004, Package (0x62)
        {
            /* X - Integer */

            Ones,
            Ones,
            /* X - String */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer */

            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Field Unit */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer Field */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones
        })
        /* Expected results: 64-bit, 32-bit */

        Name (P005, Package (0x62)
        {
            /* X - Integer */

            Ones,
            Ones,
            /* X - String */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer */

            Ones,
            Ones,
            Ones,
            Ones,
            Zero,
            Zero,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Field Unit */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            /* X - Buffer Field */

            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones,
            Ones
        })
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
            FLG1 = 0x01
            /* (Integer ==> All other types) */
            /* (All other types ==> Integer) */
            COM2 = 0x02
            /*		Store(p000, PKG1) */
            /*		Store(p001, PKG2) */
            M48B (OP, 0x0103)
            /* (String ==> All other types) */
            /* (All other types ==> String) */
            COM2 = 0x02
            /*		Store(p002, PKG1) */
            /*		Store(p003, PKG2) */
            M48B (OP, 0x0204)
            /* (Buffer ==> All other types) */
            /* (All other types ==> Buffer) */
            COM2 = 0x02
            /*		Store(p004, PKG1) */
            /*		Store(p005, PKG2) */
            M48B (OP, 0x0302)
            /*		Store(PKG0, PKG1) */
            /*		Store(PKG0, PKG2) */
            COM2 = 0x00
            FLG1 = 0x00
        }
    }

    /* LOr (int, int) => Boolean */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source1: 0x1ed1 */
    /*    Source2: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source1: 0x402e */
    /*    Source2: 0x402e */
    Method (M424, 1, Serialized)
    {
        Name (OP, 0x18)
        TS00 ("m424")
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* Match (pkg, byt, int, byt, int, int) => Ones | Integer */
    /* */
    /* Total scale of unacceptable types: */
    /* */
    /*                   Total  Currently excluded from it */
    /*    SearchPackage: 0x5eef */
    /*    MatchObject1:  0x1ed1 */
    /*    MatchObject2:  0x1ed1 0x1ed1 (causes error) */
    /*    StartIndex:    0x1ed1 0x1ed1 (causes error) */
    /* Total scale of acceptable types: */
    /*    SearchPackage: 0x0010 */
    /*    MatchObject1:  0x402e */
    /*    MatchObject2:  0x402e */
    /*    StartIndex:    0x402e */
    Method (M425, 1, Serialized)
    {
        Name (OP, 0x19)
        TS00 ("m425")
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0400
            DF01 = 0x0100
            DF02 = 0x0100
            DF03 = 0x0100
            DF04 = 0x0100
            Local7 = M488 (OP, 0x5EEF, 0x00, 0x1ED1, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* Mid ({str|buf}, int, int, Result) => Buffer or String */
    /* */
    /* Total scale of unacceptable types: */
    /* */
    /*            Total  Currently excluded from it */
    /*    Source: 0x1ed1 */
    /*    Index:  0x1ed1 0x0400 Op.Region (causes error) */
    /*    Length: 0x1ed1 0x0400 Op.Region (causes error) */
    /* Total scale of acceptable types: */
    /*    Source: 0x402e */
    /*    Index:  0x402e */
    /*    Length: 0x402e */
    Method (M426, 1, Serialized)
    {
        Name (OP, 0x1A)
        TS00 ("m426")
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0200
            DF01 = 0x0100
            DF02 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1AD1, 0x1AD1, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* Mod (int, int, Result) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Dividend: 0x1ed1 */
    /*    Divisor:  0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Dividend: 0x402e */
    /*    Divisor:  0x402e */
    Method (M427, 1, Serialized)
    {
        Name (OP, 0x1B)
        TS00 ("m427")
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* Multiply (int, int, Result) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Multiplicand: 0x1ed1 */
    /*    Multiplier:   0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Multiplicand: 0x402e */
    /*    Multiplier:   0x402e */
    Method (M428, 1, Serialized)
    {
        Name (OP, 0x1C)
        TS00 ("m428")
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* NAnd (int, int, Result) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source1: 0x1ed1 */
    /*    Source2: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source1: 0x402e */
    /*    Source2: 0x402e */
    Method (M429, 1, Serialized)
    {
        Name (OP, 0x1D)
        TS00 ("m429")
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* NOr (int, int, Result) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source1: 0x1ed1 */
    /*    Source2: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source1: 0x402e */
    /*    Source2: 0x402e */
    Method (M430, 1, Serialized)
    {
        Name (OP, 0x1E)
        TS00 ("m430")
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* Not (int, Result) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source: 0x402e */
    Method (M431, 1, Serialized)
    {
        Name (OP, 0x1F)
        TS00 ("m431")
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x1ED1, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* ObjectType (any) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Object: 0x0000 */
    /* Total scale of acceptable types: */
    /*    Object: 0x5eff */
    Method (M432, 1, Serialized)
    {
        Name (OP, 0x20)
        TS00 ("m432")
        If (Arg0)
        {
            M486 ()
            /* Error: ObjectType fails with the Uninitialized type */

            Local7 = M488 (OP, 0x01, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* Or (int, int, Result) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source1: 0x1ed1 */
    /*    Source2: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source1: 0x402e */
    /*    Source2: 0x402e */
    Method (M433, 1, Serialized)
    {
        Name (OP, 0x21)
        TS00 ("m433")
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* RefOf (any) => ObjectReference */
    /* */
    /* Total scale of unacceptable types: */
    /*    Object: 0x0000 */
    /* Total scale of acceptable types: */
    /*    Object: 0x5eff */
    Method (M434, 1, Serialized)
    {
        Name (OP, 0x22)
        TS00 ("m434")
        If (Arg0)
        {
            M486 ()
            /* Error: RefOf fails with the Uninitialized type */

            Local7 = M488 (OP, 0x01, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* Release (mux) */
    /* */
    /* Total scale of unacceptable types: */
    /*    SyncObject: 0x5cff */
    /* Total scale of acceptable types: */
    /*    SyncObject: 0x0200 */
    Method (M435, 1, Serialized)
    {
        Name (OP, 0x23)
        TS00 ("m435")
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x5CFF, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* Reset (evt) */
    /* */
    /* Total scale of unacceptable types: */
    /*    SyncObject: 0x5e7f */
    /* Total scale of acceptable types: */
    /*    SyncObject: 0x0080 */
    Method (M436, 1, Serialized)
    {
        Name (OP, 0x24)
        TS00 ("m436")
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x5E7F, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* Return ({any|ref}) */
    /* */
    /* Total scale of unacceptable types: */
    /*    Arg: 0x0000 */
    /* Total scale of acceptable types: */
    /*    Arg: 0x5eff */
    Method (M437, 1, Serialized)
    {
        Name (OP, 0x25)
        TS00 ("m437")
        If (Arg0)
        {
            M486 ()
            /* Error: Return fails with the Uninitialized type */

            Local7 = M488 (OP, 0x01, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* ShiftLeft (int, int, Result) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source:     0x1ed1 */
    /*    ShiftCount: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source:     0x402e */
    /*    ShiftCount: 0x402e */
    Method (M438, 1, Serialized)
    {
        Name (OP, 0x26)
        TS00 ("m438")
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* ShiftRight (int, int, Result) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source:     0x1ed1 */
    /*    ShiftCount: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source:     0x402e */
    /*    ShiftCount: 0x402e */
    Method (M439, 1, Serialized)
    {
        Name (OP, 0x27)
        TS00 ("m439")
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* Signal (evt) */
    /* */
    /* Total scale of unacceptable types: */
    /*    SyncObject: 0x5e7f */
    /* Total scale of acceptable types: */
    /*    SyncObject: 0x0080 */
    Method (M440, 1, Serialized)
    {
        Name (OP, 0x28)
        TS00 ("m440")
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x5E7F, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* SizeOf ({int|str|buf|pkg}) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    ObjectName: 0x5ee3 */
    /* Total scale of acceptable types: */
    /*    ObjectName: 0x004c */
    Method (M441, 1, Serialized)
    {
        Name (OP, 0x29)
        TS00 ("m441")
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x5EE3, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* Sleep (int) */
    /* */
    /* Total scale of unacceptable types: */
    /*    MilliSeconds: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    MilliSeconds: 0x402e */
    Method (M442, 1, Serialized)
    {
        Name (OP, 0x2A)
        TS00 ("m442")
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x1ED1, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* Stall (int) */
    /* */
    /* Total scale of unacceptable types: */
    /*    MicroSeconds: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    MicroSeconds: 0x402e */
    Method (M443, 1, Serialized)
    {
        Name (OP, 0x2B)
        TS00 ("m443")
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x1ED1, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* Store (any, Destination) => DataRefObject */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source: 0x0000 */
    /* Total scale of acceptable types: */
    /*    Source: 0x5eff */
    Method (M444, 1, Serialized)
    {
        Name (OP, 0x2C)
        TS00 ("m444")
        If (Arg0)
        {
            M486 ()
            /* Error: Store fails with the Uninitialized type */

            Local7 = M488 (OP, 0x01, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* Subtract (int, int, Result) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Minuend:    0x1ed1 */
    /*    Subtrahend: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Minuend:    0x402e */
    /*    Subtrahend: 0x402e */
    Method (M445, 1, Serialized)
    {
        Name (OP, 0x2D)
        TS00 ("m445")
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* ToBCD (int, Result) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Value: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Value: 0x402e */
    Method (M446, 1, Serialized)
    {
        Name (OP, 0x2E)
        TS00 ("m446")
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x1ED1, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* ToBuffer ({int|str|buf}, Result) => Buffer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Data: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Data: 0x402e */
    Method (M447, 1, Serialized)
    {
        Name (OP, 0x2F)
        TS00 ("m447")
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x1ED1, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* ToDecimalString ({int|str|buf}, Result) => String */
    /* */
    /* Total scale of unacceptable types: */
    /*    Data: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Data: 0x402e */
    Method (M448, 1, Serialized)
    {
        Name (OP, 0x30)
        TS00 ("m448")
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x1ED1, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
            Local7 = M48D (OP, 0x0102, 0x00, 0x00, 0x00, "305419896", "305419896")
            Local7 = M48D (OP, 0x0204, 0x00, 0x00, 0x00, "9876", "9876")
            Local7 = M48D (OP, 0x0209, 0x00, 0x00, 0x00, "FdeAcb0132547698", "FdeAcb0132547698")
            Local7 = M48D (OP, 0x0302, 0x00, 0x00, 0x00, "129,130", "129,130")
            Local7 = M48D (OP, 0x0303, 0x00, 0x00, 0x00, "131,132,133,134", "131,132,133,134")
            Local7 = M48D (OP, 0x0506, 0x00, 0x00, 0x00, "6692061083885586008", "88,70,55,136,25,250,198,82")
            Local7 = M48D (OP, 0x0E06, 0x00, 0x00, 0x00, "6692061083885586008", "88,70,55,136,25,250,198,82")
        }
    }

    /* ToHexString ({int|str|buf}, Result) => String */
    /* */
    /* Total scale of unacceptable types: */
    /*    Data: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Data: 0x402e */
    Method (M449, 1, Serialized)
    {
        Name (OP, 0x31)
        TS00 ("m449")
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x1ED1, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
            Local7 = M48D (OP, 0x0102, 0x00, 0x00, 0x00, "0000000012345678", "12345678")
            Local7 = M48D (OP, 0x0204, 0x00, 0x00, 0x00, "9876", "9876")
            Local7 = M48D (OP, 0x0209, 0x00, 0x00, 0x00, "FdeAcb0132547698", "FdeAcb0132547698")
            Local7 = M48D (OP, 0x0302, 0x00, 0x00, 0x00, "81,82", "81,82")
            Local7 = M48D (OP, 0x0303, 0x00, 0x00, 0x00, "83,84,85,86", "83,84,85,86")
            Local7 = M48D (OP, 0x0506, 0x00, 0x00, 0x00, "6692061083885586008", "58,46,37,88,19,FA,C6,52")
            Local7 = M48D (OP, 0x0E06, 0x00, 0x00, 0x00, "6692061083885586008", "58,46,37,88,19,FA,C6,52")
        }
    }

    /* ToInteger ({int|str|buf}, Result) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Data: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Data: 0x402e */
    Method (M450, 1, Serialized)
    {
        Name (OP, 0x32)
        TS00 ("m450")
        If (Arg0)
        {
            M486 ()
            Local7 = M488 (OP, 0x1ED1, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
            Local7 = M48D (OP, 0x0102, 0x00, 0x00, 0x00, 0x12345678, 0x12345678)
            Local7 = M48D (OP, 0x0204, 0x00, 0x00, 0x00, 0x9876, 0x9876)
            Local7 = M48D (OP, 0x0211, 0x00, 0x00, 0x00, 0xF1DAB98E0D794BC5, 0x0D794BC5)
            Local7 = M48D (OP, 0x0302, 0x00, 0x00, 0x00, 0x8281, 0x8281)
            Local7 = M48D (OP, 0x0303, 0x00, 0x00, 0x00, 0x86858483, 0x86858483)
            Local7 = M48D (OP, 0x0506, 0x00, 0x00, 0x00, 0x52C6FA1988374658, 0x88374658)
            Local7 = M48D (OP, 0x0E06, 0x00, 0x00, 0x00, 0x52C6FA1988374658, 0x88374658)
        }
    }

    /* ToString (buf, int, Result) => String */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source: 0x1ed1 */
    /*    Length: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source: 0x402e */
    /*    Length: 0x402e */
    Method (M451, 1, Serialized)
    {
        Name (OP, 0x33)
        TS00 ("m451")
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0300
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* Wait (evt, int) => Boolean */
    /* */
    /* Total scale of unacceptable types: */
    /*    SyncObject: 0x5e7f */
    /*    SyncObject: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    SyncObject: 0x0080 */
    /*    SyncObject: 0x402e */
    Method (M452, 1, Serialized)
    {
        Name (OP, 0x34)
        TS00 ("m452")
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0700
            DF01 = 0x0100
            Local7 = M488 (OP, 0x5E7F, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    /* XOr (int, int, Result) => Integer */
    /* */
    /* Total scale of unacceptable types: */
    /*    Source1: 0x1ed1 */
    /*    Source2: 0x1ed1 */
    /* Total scale of acceptable types: */
    /*    Source1: 0x402e */
    /*    Source2: 0x402e */
    Method (M453, 1, Serialized)
    {
        Name (OP, 0x35)
        TS00 ("m453")
        If (Arg0)
        {
            M486 ()
            DF00 = 0x0100
            DF01 = 0x0100
            Local7 = M488 (OP, 0x1ED1, 0x1ED1, 0x00, 0x00, 0x00)
        }
        Else
        {
        }
    }

    Method (M460, 1, Serialized)
    {
        If (0x01)
        {
            M400 (Arg0)
            M401 (Arg0)
            M402 (Arg0)
            M403 (Arg0)
            M404 (Arg0)
            M405 (Arg0)
            M406 (Arg0)
            M407 (Arg0)
            M408 (Arg0)
            M409 (Arg0)
            M410 (Arg0)
            M411 (Arg0)
            M412 (Arg0)
            M413 (Arg0)
            M414 (Arg0)
            M415 (Arg0)
            M416 (Arg0)
            M417 (Arg0)
            M418 (Arg0)
            M419 (Arg0)
            M420 (Arg0)
            M421 (Arg0)
            M422 (Arg0)
            M423 (Arg0)
            M424 (Arg0)
            M425 (Arg0)
            M426 (Arg0)
            M427 (Arg0)
            M428 (Arg0)
            M429 (Arg0)
            M430 (Arg0)
            M431 (Arg0)
            M432 (Arg0)
            M433 (Arg0)
            M434 (Arg0)
            M435 (Arg0)
            M436 (Arg0)
            M437 (Arg0)
            M438 (Arg0)
            M439 (Arg0)
            M440 (Arg0)
            M441 (Arg0)
            M442 (Arg0)
            M443 (Arg0)
            M444 (Arg0)
            M445 (Arg0)
            M446 (Arg0)
            M447 (Arg0)
            M448 (Arg0)
            M449 (Arg0)
            M450 (Arg0)
            M451 (Arg0)
            M452 (Arg0)
            M453 (Arg0)
        }
        Else
        {
            /*	m400(arg0) */
            /*	m401(arg0) */
            /*	m402(arg0) */
            /*	m403(arg0) */
            /*	m407(arg0) */
            /*	m409(arg0) */
            /*	m411(arg0) */
            /*	m412(arg0) */
            /*	m414(arg0) */
            /*	m417(arg0) */
            /*	m418(arg0) */
            /*	m448(arg0) */
            /*	m449(arg0) */
            /*	m450(arg0) */
            /*	m400(arg0) */
            M401 (Arg0)
        }

        If (0x00)
        {
            Name (XXXX, 0x00)
            Name (B000, Buffer (0x0A){})
            Name (S000, "000000000000000000000000000000")
            Debug = "-=-=-=-=-=-=-=-=-=-=-="
            Local0 = (0x0A > 0x05)
            Debug = Local0
            Local0 = (0x05 > 0x0A)
            Debug = Local0
            Local0 = ("11" > 0x11)
            Debug = Local0
            Local0 = ("11" == 0x11)
            Debug = Local0
            XXXX = "11"
            Debug = XXXX /* \M460.XXXX */
            Local0 = ("11" > 0x0FFFFFFF)
            Debug = Local0
            Local0 = (0x12 > "11")
            Debug = Local0
            XXXX = "1234567890abCdeF"
            Debug = XXXX /* \M460.XXXX */
            XXXX = "FdeAcb0132547698"
            Debug = XXXX /* \M460.XXXX */
            XXXX = "FdeAcb0132547698"
            Debug = XXXX /* \M460.XXXX */
            /* [ACPI Debug] Integer: 0x90ABCDEF */
            /* [ACPI Debug] Integer: 0x32547698 */
            B000 = "qwrt"
            Debug = B000 /* \M460.B000 */
            /* 71 77 72 74 00 00 00 00 00 00 */

            S000 = 0xABEDF18942345678
            Debug = S000 /* \M460.S000 */
            /* "ABEDF18942345678" */

            B000 = "ABEDF18942345678"
            Debug = B000 /* \M460.B000 */
                /* 41 42 45 44 46 31 38 39 34 32 */
        }
    }
