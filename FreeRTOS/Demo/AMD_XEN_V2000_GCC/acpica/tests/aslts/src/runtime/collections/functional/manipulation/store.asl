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
     */
    Name (Z042, 0x2A)
    Mutex (MT04, 0x00)
    /* Verifying 1-parameter, 1-result operator */

    Method (M302, 6, Serialized)
    {
        Local5 = 0x00
        Local3 = Arg1
        While (Local3)
        {
            /* Operand */

            Local0 = DerefOf (Arg3 [Local5])
            /* Expected result */

            Local1 = DerefOf (Arg4 [Local5])
            Switch (ToInteger (Arg5))
            {
                Case (0x00)
                {
                    ToInteger (Local0, Local2)
                    If ((Local2 != Local1))
                    {
                        ERR (Arg0, Z042, __LINE__, 0x00, 0x00, Local5, Arg2)
                        Return (0x01)
                    }
                }
                Case (0x01)
                {
                    ToBuffer (Local0, Local2)
                    If ((Local2 != Local1))
                    {
                        ERR (Arg0, Z042, __LINE__, 0x00, 0x00, Local5, Arg2)
                        Return (0x01)
                    }
                }
                Case (0x02)
                {
                    ToString (Local0, Ones, Local2)
                    If ((Local2 != Local1))
                    {
                        ERR (Arg0, Z042, __LINE__, 0x00, 0x00, Local5, Arg2)
                        Return (0x01)
                    }
                }
                Case (0x03)
                {
                    ToDecimalString (Local0, Local2)
                    If ((Local2 != Local1))
                    {
                        ERR (Arg0, Z042, __LINE__, 0x00, 0x00, Local5, Arg2)
                        Return (0x01)
                    }
                }
                Case (0x04)
                {
                    ToHexString (Local0, Local2)
                    If ((Local2 != Local1))
                    {
                        ERR (Arg0, Z042, __LINE__, 0x00, 0x00, Local5, Arg2)
                        Return (0x01)
                    }
                }
                Case (0x05)
                {
                    ToBCD (Local0, Local2)
                    If ((Local2 != Local1))
                    {
                        ERR (Arg0, Z042, __LINE__, 0x00, 0x00, Local5, Arg2)
                        Return (0x01)
                    }
                }
                Case (0x06)
                {
                    FromBCD (Local0, Local2)
                    If ((Local2 != Local1))
                    {
                        ERR (Arg0, Z042, __LINE__, 0x00, 0x00, Local5, Arg2)
                        Return (0x01)
                    }
                }
                Case (0x07)
                {
                    /* ToUUID macro */

                    Local2 = Local0
                    If ((Local2 != Local1))
                    {
                        ERR (Arg0, Z042, __LINE__, 0x00, 0x00, Local5, Arg2)
                        Return (0x01)
                    }
                }
                Case (0x08)
                {
                    /* Unicode macro */

                    Local2 = Local0
                    If ((Local2 != Local1))
                    {
                        ERR (Arg0, Z042, __LINE__, 0x00, 0x00, Local5, Arg2)
                        Return (0x01)
                    }
                }
                Case (0x09)
                {
                    /* EISAID macro */

                    Local2 = Local0
                    If ((Local2 != Local1))
                    {
                        ERR (Arg0, Z042, __LINE__, 0x00, 0x00, Local5, Arg2)
                        Return (0x01)
                    }
                }

            }

            Local5++
            Local3--
        }

        Return (0x00)
    }

    Method (ST00, 0, Serialized)
    {
        Debug = "TEST: ST00, Store object"
        /* Store */

        Local1 = Local0 = 0xABCDEF12
        If ((Local1 != 0xABCDEF12))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* Integer arithmetic */
        /* Add */
        Local1 = Local0 = (0x12345678 + 0x11111111)
        If ((Local1 != 0x23456789))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Store ((0x23456781 + 0x11111111), Local0)
        If ((Local0 != 0x34567892))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Local1 = Local0 = (0x12345678 + 0xF0000000)
        M4C0 (__METHOD__, Local1, 0x0000000102345678, 0x02345678)
        /* Subtract */

        Local1 = Local0 = (0x87654321 - 0x11111111)
        If ((Local1 != 0x76543210))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Store ((0x72387654 - 0x22221111), Local0)
        If ((Local0 != 0x50166543))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* Multiply */

        Local1 = Local0 = (0x00012345 * 0x7ABC)
        If ((Local1 != 0x8BA4C8AC))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Store ((0x000145AB * 0x3247), Local0)
        If ((Local0 != 0x3FF5B86D))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* Divide */

        Local2 = Divide (0x12345678, 0x1000, Local0, Local1)
        If ((Local2 != 0x00012345))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Store (Divide (0x7ABC56E8, 0x1000, Local0), Local1)
        If ((Local1 != 0x0007ABC5))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Store ((0x55667788 / 0x1000), Local0)
        If ((Local0 != 0x00055667))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* Increment */

        Local0 = 0x12345678
        Local1 = Local0++
        If ((Local1 != 0x12345679))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* Decrement */

        Local0 = 0x67812345
        Local1 = Local0--
        If ((Local1 != 0x67812344))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* And */

        Local1 = Local0 = (0x87654321 & 0xAAAAAAAA)
        If ((Local1 != 0x82200220))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Store ((0x88AABBCC & 0xAAAAAAAA), Local0)
        If ((Local0 != 0x88AAAA88))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* FindSetLeftBit */

        Local1 = FindSetLeftBit (0xF001, Local0)
        If ((Local1 != 0x10))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Local0 = FindSetLeftBit (0x09007001)
        If ((Local0 != 0x1C))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* FindSetRightBit */

        Local1 = FindSetRightBit (0x01080040, Local0)
        If ((Local1 != 0x07))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Local0 = FindSetRightBit (0x09800000)
        If ((Local0 != 0x18))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* Mod */

        Store ((0x1AFB3C4D % 0x00400000), Local0)
        If ((Local0 != 0x003B3C4D))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* ShiftLeft */

        Local1 = Local0 = (0x12345678 << 0x09)
        M4C0 (__METHOD__, Local1, 0x0000002468ACF000, 0x68ACF000)
        Store ((0x45678ABF << 0x0B), Local0)
        M4C0 (__METHOD__, Local0, 0x0000022B3C55F800, 0x3C55F800)
        /* ShiftRight */

        Local1 = Local0 = (0x87654321 >> 0x19)
        If ((Local1 != 0x43))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Store ((0x7654A0CB >> 0x15), Local0)
        If ((Local0 != 0x03B2))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* Nand */

        Local1 = NAnd (0xA33553AC, 0x9A9636CA, Local0)
        M4C0 (__METHOD__, Local1, 0xFFFFFFFF7DEBED77, 0x7DEBED77)
        Local0 = NAnd (0xA33553AC, 0x565C36C9)
        M4C0 (__METHOD__, Local0, 0xFFFFFFFFFDEBED77, 0xFDEBED77)
        /* Nor */

        Local1 = NOr (0x9A335A3C, 0x39A96C6A, Local0)
        M4C0 (__METHOD__, Local1, 0xFFFFFFFF44448181, 0x44448181)
        Local0 = NOr (0x9A353A3C, 0x39A69C6A)
        M4C0 (__METHOD__, Local0, 0xFFFFFFFF44484181, 0x44484181)
        /* Not */

        Local1 = Local0 = ~0x8A345678
        M4C0 (__METHOD__, Local1, 0xFFFFFFFF75CBA987, 0x75CBA987)
        Store (~0x8AF45678, Local0)
        M4C0 (__METHOD__, Local0, 0xFFFFFFFF750BA987, 0x750BA987)
        /* Or */

        Local1 = Local0 = (0x9A3533AC | 0x39A696CA)
        If ((Local1 != 0xBBB7B7EE))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Store ((0xCA3533A9 | 0xA9A696C3), Local0)
        If ((Local0 != 0xEBB7B7EB))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* Xor */

        Local1 = Local0 = (0x9A365AC3 ^ 0x39A96CA6)
        If ((Local1 != 0xA39F3665))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Store ((0xA9365AC3 ^ 0x93A96CA6), Local0)
        If ((Local0 != 0x3A9F3665))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* Logical operators */
        /* LAnd          (provided by LAN0) */
        /* LEqual        (provided by LEQ0) */
        /* LGreater      (provided by LGR0) */
        /* LGreaterEqual (provided by LGE0) */
        /* LLess         (provided by LL00) */
        /* LLessEqual    (provided by LLE0) */
        /* LNot          (provided by LN00) */
        /* LNotEqual     (provided by LNE0) */
        /* LOr           (provided by LOR0) */
        /* Synchronization */
        /* Acquire */
        Local0 = Acquire (MT04, 0x0005)
        If ((Local0 != Zero))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* Release (None) */
        /* ToInteger */
        Local1 = ToInteger ("0x89abcdef", Local0)
        If ((Local1 != 0x89ABCDEF))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Local0 = ToInteger ("0x89abcdef")
        If ((Local0 != 0x89ABCDEF))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* ToString */

        Local2 = Buffer (0x01)
            {
                 0x01                                             // .
            }
        Local1 = ToString (Local2, Ones, Local0)
        If ((Local1 != "\x01"))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Local0 = ToString (Local2, Ones)
        If ((Local0 != "\x01"))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Local1 = ToString (Local2, 0x01, Local0)
        If ((Local1 != "\x01"))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Local0 = ToString (Local2, 0x01)
        If ((Local0 != "\x01"))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* ToBuffer */

        Local2 = "\x01"
        Local1 = ToBuffer (Local2, Local0)
        If ((Local1 != Buffer (0x02)
                    {
                         0x01, 0x00                                       // ..
                    }))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Local0 = ToBuffer (Local2)
        If ((Local0 != Buffer (0x02)
                    {
                         0x01, 0x00                                       // ..
                    }))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* ToDecimalString */

        Local2 = 0x0C
        Local1 = ToDecimalString (Local2, Local0)
        If ((Local1 != "12"))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Local0 = ToDecimalString (Local2)
        If ((Local0 != "12"))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* ToHexString */

        Local2 = Buffer (0x01)
            {
                 0xEF                                             // .
            }
        Local1 = ToHexString (Local2, Local0)
        If ((Local1 != "EF"))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Local0 = ToHexString (Local2)
        If ((Local0 != "EF"))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* ToBCD */

        Local2 = 0x0A
        Local1 = ToBCD (Local2, Local0)
        If ((Local1 != 0x10))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Local0 = ToBCD (Local2)
        If ((Local0 != 0x10))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* FromBCD */

        Local2 = 0x10
        Local1 = FromBCD (Local2, Local0)
        If ((Local1 != 0x0A))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Local0 = FromBCD (Local2)
        If ((Local0 != 0x0A))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* Mid */

        Local2 = "0123"
        Local1 = Mid (Local2, 0x01, 0x02, Local0)
        If ((Local1 != "12"))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Local0 = Mid (Local2, 0x01, 0x02)
        If ((Local0 != "12"))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Local2 = Buffer (0x04)
            {
                 0x00, 0x01, 0x02, 0x03                           // ....
            }
        Local1 = Mid (Local2, 0x01, 0x02, Local0)
        If ((Local1 != Buffer (0x02)
                    {
                         0x01, 0x02                                       // ..
                    }))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Local0 = Mid (Local2, 0x01, 0x02)
        If ((Local0 != Buffer (0x02)
                    {
                         0x01, 0x02                                       // ..
                    }))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* Match */

        Local2 = Package (0x01)
            {
                0x01
            }
        Local0 = Match (Local2, MTR, 0x00, MTR, 0x00, 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* ConcatenateResTemplate */

        Local2 = Buffer (0x02)
            {
                 0x79, 0x00                                       // y.
            }
        Local3 = Buffer (0x02)
            {
                 0x79, 0x00                                       // y.
            }
        Local1 = ConcatenateResTemplate (Local2, Local3, Local0)
        /*
         * 20.12.2005: 0 instead of 0x87
         */
        If ((Local1 != Buffer (0x02)
                    {
                         0x79, 0x00                                       // y.
                    }))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /*
         * 20.12.2005: 0 instead of 0x87
         */
        Local0 = ConcatenateResTemplate (Local2, Local3)
        If ((Local0 != Buffer (0x02)
                    {
                         0x79, 0x00                                       // y.
                    }))
        {
            ERR (__METHOD__, Z042, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }
    }

    Method (M30D, 0, Serialized)
    {
        Name (STR0, "mnbvcxzlkjhgf")
        Name (STR1, "mnbvcxzlkjAgf")
        STR0 [0x0A] = "A"
        If ((STR0 != STR1))
        {
            ERR ("m30d", Z042, __LINE__, 0x00, 0x00, STR0, STR1)
        }
    }

    /* Run-method */

    Method (DCM0, 0, NotSerialized)
    {
        ST00 ()
        M30D ()
    }
