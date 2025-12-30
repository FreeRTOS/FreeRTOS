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
     *  Integer
     *
     * (verify exceptions caused by the imprope use of Integer type objects)
     */
    Name (Z093, 0x5D)
    Name (I100, 0xABCD1234)
    /* Expected exceptions: */
    /* */
    /* 47 - AE_AML_OPERAND_TYPE */
    /* Note: an object reference is defined by spec */
    /* to be an Integer, nevertheless it is supposed */
    /* that the product should distinguish Integer Data */
    /* from a reference. */
    /* */
    Method (M4B1, 1, Serialized)
    {
        Name (I000, 0x76543210)
        Event (E000)
        /* Local Named Object */

        Method (M000, 1, Serialized)
        {
            Name (I000, 0x89ABCDEF)
            /* DerefOf */

            If (Y083)
            {
                Local1 = DerefOf (I000)
                CH06 (Arg0, 0x00, 0x2F)
            }

            /* Index */

            Local1 = I000 [0x00]
            CH06 (Arg0, 0x02, 0x2F)
            /* ConcatenateResTemplate */

            ConcatenateResTemplate (I000, Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Local1)
            CH06 (Arg0, 0x05, 0x2F)
            ConcatenateResTemplate (Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, I000, Local1)
            CH06 (Arg0, 0x06, 0x2F)
        }

        /* Global Named Object */

        Method (M001, 1, NotSerialized)
        {
            /* DerefOf */

            If (Y083)
            {
                Local1 = DerefOf (I100)
                CH06 (Arg0, 0x07, 0x2F)
            }

            /* Index */

            Local1 = I100 [0x00]
            CH06 (Arg0, 0x09, 0x2F)
            /* ConcatenateResTemplate */

            ConcatenateResTemplate (I100, Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Local1)
            CH06 (Arg0, 0x0C, 0x2F)
            ConcatenateResTemplate (Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, I100, Local1)
            CH06 (Arg0, 0x0D, 0x2F)
        }

        /* Argument */

        Method (M002, 2, NotSerialized)
        {
            /* DerefOf */

            Local1 = DerefOf (Arg1)
            CH06 (Arg0, 0x0E, 0x2F)
            /* Release */

            Release (Arg1)
            CH06 (Arg0, 0x0F, 0x2F)
            /* Reset */

            Reset (Arg1)
            CH06 (Arg0, 0x10, 0x2F)
            /* Signal */

            Signal (Arg1)
            CH06 (Arg0, 0x11, 0x2F)
            /* Acquire */

            Local1 = Acquire (Arg1, 0x0000)
            CH06 (Arg0, 0x12, 0x2F)
            /* ConcatenateResTemplate */

            ConcatenateResTemplate (Arg1, Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Local1)
            CH06 (Arg0, 0x15, 0x2F)
            ConcatenateResTemplate (Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Arg1, Local1)
            CH06 (Arg0, 0x16, 0x2F)
            /* Index */

            Local1 = Arg1 [0x00]
            CH06 (Arg0, 0x18, 0x2F)
            /* Wait */

            Local1 = Wait (Arg1, 0x00)
            CH06 (Arg0, 0x19, 0x2F)
            /* Match */

            Local1 = Match (Arg1, MTR, 0x00, MTR, 0x00, 0x00)
            CH06 (Arg0, 0x1A, 0x2F)
        }

        /* Local */

        Method (M003, 1, NotSerialized)
        {
            Local0 = 0x89ABCDEF
            /* DerefOf */

            Local1 = DerefOf (Local0)
            CH06 (Arg0, 0x1B, 0x2F)
            /* Release */

            Release (Local0)
            CH06 (Arg0, 0x1C, 0x2F)
            /* Reset */

            Reset (Local0)
            CH06 (Arg0, 0x1D, 0x2F)
            /* Signal */

            Signal (Local0)
            CH06 (Arg0, 0x1E, 0x2F)
            /* Acquire */

            Local1 = Acquire (Local0, 0x0000)
            CH06 (Arg0, 0x1F, 0x2F)
            /* ConcatenateResTemplate */

            ConcatenateResTemplate (Local0, Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Local1)
            CH06 (Arg0, 0x22, 0x2F)
            ConcatenateResTemplate (Buffer (0x02)
                {
                     0x79, 0x00                                       // y.
                }, Local0, Local1)
            CH06 (Arg0, 0x23, 0x2F)
            /* Index */

            Local1 = Local0 [0x00]
            CH06 (Arg0, 0x25, 0x2F)
            /* Wait */

            Local1 = Wait (Local0, 0x00)
            CH06 (Arg0, 0x26, 0x2F)
            /* Match */

            Local1 = Match (Local0, MTR, 0x00, MTR, 0x00, 0x00)
            CH06 (Arg0, 0x27, 0x2F)
        }

        /* An element of Package */

        Method (M004, 1, Serialized)
        {
            Name (P000, Package (0x01)
            {
                0x89ABCDEF
            })
            /* DeRefOf(Index(Package, Ind)) */

            Local1 = DerefOf (DerefOf (P000 [0x00]))
            CH06 (Arg0, 0x28, 0x2F)
            Store (DerefOf (P000 [0x00]) [0x00], Local1)
            CH06 (Arg0, 0x29, 0x2F)
            Local1 = Match (DerefOf (P000 [0x00]), MTR, 0x00, MTR, 0x00,
                0x00)
            CH06 (Arg0, 0x2A, 0x2F)
            /* DeRefOf(Index(Package, Ind, Dest)) */

            Local1 = DerefOf (DerefOf (Local0 = P000 [0x00]))
            CH06 (Arg0, 0x2B, 0x2F)
            Store (DerefOf (Local0 = P000 [0x00]) [0x00], Local1)
            CH06 (Arg0, 0x2C, 0x2F)
            Local1 = Match (DerefOf (Local0 = P000 [0x00]), MTR, 0x00, MTR, 0x00,
                0x00)
            CH06 (Arg0, 0x2D, 0x2F)
        }

        /* Reference to Object */

        Method (M005, 2, NotSerialized)
        {
            Debug = Arg0
            Debug = Arg1
            Local0 = ObjectType (Arg1)
            If ((Local0 != 0x01))
            {
                ERR (Arg0, Z093, __LINE__, 0x00, 0x00, Local0, 0x01)
                Return (0x01)
            }

            Local1 = DerefOf (Arg1)
            CH03 (__METHOD__, Z093, __LINE__, 0x00, 0x00)
            Local1 = DerefOf (DerefOf (Arg1))
            CH06 (Arg0, 0x2F, 0x2F)
            Store (DerefOf (Arg1) [0x00], Local1)
            CH06 (Arg0, 0x30, 0x2F)
            Local1 = Match (DerefOf (Arg1), MTR, 0x00, MTR, 0x00, 0x00)
            CH06 (Arg0, 0x31, 0x2F)
            Return (0x00)
        }

        /* Result of Method invocation */

        Method (M006, 1, Serialized)
        {
            Name (I000, 0x00) /* Label to check m000 invocations */
            Method (M000, 1, NotSerialized)
            {
                I000 = Arg0
                Local0 = 0x89ABCDEF
                Return (Local0)
            }

            Method (CH00, 2, NotSerialized)
            {
                If ((I000 != Arg1))
                {
                    ERR (Arg0, Z093, __LINE__, 0x00, 0x00, I000, Arg1)
                }
            }

            Local1 = DerefOf (M000 (0x01))
            CH06 (Arg0, 0x33, 0x2F)
            CH00 (Arg0, 0x01)
            Release (M000 (0x02))
            CH06 (Arg0, 0x34, 0x2F)
            If (Y600)
            {
                CH00 (Arg0, 0x02)
            }

            Reset (M000 (0x03))
            CH06 (Arg0, 0x35, 0x2F)
            If (Y600)
            {
                CH00 (Arg0, 0x03)
            }

            Signal (M000 (0x04))
            CH06 (Arg0, 0x36, 0x2F)
            If (Y600)
            {
                CH00 (Arg0, 0x04)
            }

            Local1 = Acquire (M000 (0x05), 0x0000)
            CH06 (Arg0, 0x37, 0x2F)
            If (Y600)
            {
                CH00 (Arg0, 0x05)
            }

            Store (M000 (0x06) [0x00], Local1)
            CH06 (Arg0, 0x38, 0x2F)
            CH00 (Arg0, 0x06)
            Local1 = Wait (M000 (0x07), 0x00)
            CH06 (Arg0, 0x39, 0x2F)
            If (Y600)
            {
                CH00 (Arg0, 0x07)
            }

            Local1 = Match (M000 (0x08), MTR, 0x00, MTR, 0x00, 0x00)
            CH06 (Arg0, 0x3A, 0x2F)
            CH00 (Arg0, 0x08)
        }

        /* Reference to Object as Result of Method invocation */

        Method (M007, 1, Serialized)
        {
            Name (I000, 0x89ABCDEF)
            Name (I001, 0x00) /* Label to check m000 invocations */
            Method (M000, 2, NotSerialized)
            {
                I001 = Arg0
                If ((Arg1 == 0x00))
                {
                    Local0 = RefOf (I100)
                }
                ElseIf ((Arg1 == 0x01))
                {
                    Local0 = RefOf (I000)
                }

                Return (Local0)
            }

            Method (CH00, 2, NotSerialized)
            {
                If ((I001 != Arg1))
                {
                    ERR (Arg0, Z093, __LINE__, 0x00, 0x00, I000, Arg1)
                }
            }

            Name (LPN0, 0x02)
            Name (LPC0, 0x00)
            While (LPN0)
            {
                Local0 = (0x03 * LPC0) /* \M4B1.M007.LPC0 */
                I001 = 0x00
                Local1 = DerefOf (M000 (0x01, LPC0))
                CH03 (__METHOD__, Z093, __LINE__, 0x00, 0x00)
                CH00 (Arg0, 0x01)
                Local1 = DerefOf (DerefOf (M000 (0x02, LPC0)))
                CH06 (Arg0, (0x3C + Local0), 0x2F)
                CH00 (Arg0, 0x02)
                Store (DerefOf (M000 (0x03, LPC0)) [0x00], Local1)
                CH06 (Arg0, (0x3D + Local0), 0x2F)
                CH00 (Arg0, 0x03)
                Local1 = Match (DerefOf (M000 (0x04, LPC0)), MTR, 0x00, MTR, 0x00, 0x00)
                CH06 (Arg0, (0x3E + Local0), 0x2F)
                CH00 (Arg0, 0x04)
                LPN0--
                LPC0++
            }
        }

        CH03 (__METHOD__, Z093, __LINE__, 0x00, 0x00)
        /* Local Named Object */

        M000 (__METHOD__)
        /* Global Named Object */

        M001 (__METHOD__)
        /* Argument */

        M002 (__METHOD__, 0x76543210)
        /* Local */

        M003 (__METHOD__)
        /* An element of Package */

        M004 (__METHOD__)
        /* Reference to Local Named Object */

        M005 (Concatenate (__METHOD__, "-m005-RefLocName"), RefOf (I000))
        Local0 = RefOf (I000)
        M005 (Concatenate (__METHOD__, "-m005-RefLocName2"), Local0)
        CondRefOf (I000, Local0)
        M005 (Concatenate (__METHOD__, "-m005-CondRefLocName"), Local0)
        M005 (Concatenate (__METHOD__, "-m005-RefGlobName"), RefOf (I100))
        Local0 = RefOf (I100)
        M005 (Concatenate (__METHOD__, "-m005-RefGlobName2"), Local0)
        CondRefOf (I100, Local0)
        M005 (Concatenate (__METHOD__, "-m005-CondRefGlobName"), Local0)
        /* Reference to Local */

        Local0 = 0x89ABCDEF
        M005 (Concatenate (__METHOD__, "-m005-RefLocal"), RefOf (Local0))
        Local1 = RefOf (Local0)
        M005 (Concatenate (__METHOD__, "-m005-RefLocal2"), Local1)
        CondRefOf (Local0, Local1)
        M005 (Concatenate (__METHOD__, "-m005-CondRefLocal"), Local1)
        /* Reference to Arg */

        M005 (Concatenate (__METHOD__, "-m005-RefArg"), RefOf (Arg0))
        Local0 = RefOf (Arg0)
        M005 (Concatenate (__METHOD__, "-m005-RefArg2"), Local0)
        CondRefOf (Arg0, Local0)
        M005 (Concatenate (__METHOD__, "-m005-CondRefArg"), Local0)
        /* Index to Package */

        Name (P000, Package (0x01)
        {
            0x76543210
        })
        If (Y113)
        {
            M005 (Concatenate (__METHOD__, "-m005-Index"), P000 [0x00])
        }

        Store (P000 [0x00], Local0)
        M005 (Concatenate (__METHOD__, "-m005-Index2"), Local0)
        If (Y113)
        {
            M005 (Concatenate (__METHOD__, "-m005-Index3"), Local0 = P000 [0x00])
        }

        Local0 = P000 [0x00]
        M005 (Concatenate (__METHOD__, "-m005-Index4"), Local0)
        Local1 = Local0 = P000 [0x00]
        M005 (Concatenate (__METHOD__, "-m005-Index5"), Local1)
        /* Result of Method invocation */

        M006 (__METHOD__)
        /* Reference to Object as Result of Method invocation */

        If (Y500)
        {
            M007 (__METHOD__)
        }
    }
