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
     *  Field Unit
     *
     * (verify exceptions caused by the imprope use of Field Unit type objects)
     */
    Name (Z097, 0x61)
    OperationRegion (RG01, SystemMemory, 0x0100, 0x0100)
    Field (RG01, ByteAcc, NoLock, Preserve)
    {
        FU00,   31,
        FU01,   65
    }

    Name (II70, 0xABCD1234)
    Name (BI00, Buffer (0x09)
    {
        /* 0000 */  0xA4, 0xA5, 0xA6, 0xA7, 0xB8, 0xB9, 0xBA, 0xBB,  // ........
        /* 0008 */  0xBC                                             // .
    })
    /* Expected exceptions: */
    /* */
    /* 47 - AE_AML_OPERAND_TYPE */
    /* See notes to m4b1 and m4b3 */
    /* */
    Method (M4B5, 0, Serialized)
    {
        Field (RG01, ByteAcc, NoLock, Preserve)
        {
            Offset (0x0C),
            FU02,   31,
            FU03,   65
        }

        /* Local Named Object */

        Method (M000, 1, Serialized)
        {
            Field (RG01, ByteAcc, NoLock, Preserve)
            {
                Offset (0x18),
                FU02,   31,
                FU03,   65
            }

            FU02 = II70 /* \II70 */
            FU03 = BI00 /* \BI00 */
            /* Like Integer behaviour */

            If (Y083)
            {
                Local1 = DerefOf (FU02)
                CH06 (Arg0, 0x00, 0x2F)
            }

            Store (FU02 [0x00], Local1)
            CH06 (Arg0, 0x01, 0x2F)
            /* Like Buffer behaviour */

            If (Y083)
            {
                Local1 = DerefOf (FU03)
                CH06 (Arg0, 0x02, 0x2F)
            }

            Store (FU03 [0x00], Local1)
            If (Y900)
            {
                CH03 (__METHOD__, Z097, __LINE__, 0x00, 0x00)
            }
            Else
            {
                CH04 (__METHOD__, 0x00, 0x55, Z094, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
            }
        }

        /* Global Named Object */

        Method (M001, 1, NotSerialized)
        {
            FU00 = II70 /* \II70 */
            FU01 = BI00 /* \BI00 */
            /* Like Integer behaviour */

            If (Y083)
            {
                Local1 = DerefOf (FU00)
                CH06 (Arg0, 0x03, 0x2F)
            }

            Store (FU00 [0x00], Local1)
            CH06 (Arg0, 0x04, 0x2F)
            /* Like Buffer behaviour */

            If (Y083)
            {
                Local1 = DerefOf (FU01)
                CH06 (Arg0, 0x05, 0x2F)
            }

            Store (FU01 [0x00], Local1)
            If (Y900)
            {
                CH03 (__METHOD__, Z097, __LINE__, 0x00, 0x00)
            }
            Else
            {
                CH04 (__METHOD__, 0x00, 0x55, Z094, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
            }
        }

        /* Reference to Object */

        Method (M002, 3, NotSerialized)
        {
            Debug = Arg0
            Debug = Arg1
            Local0 = ObjectType (Arg1)
            If ((Local0 != 0x05))
            {
                ERR (Arg0, Z097, __LINE__, 0x00, 0x00, Local0, 0x05)
                Return (0x01)
            }

            Local1 = DerefOf (Arg1)
            CH03 (__METHOD__, Z097, __LINE__, 0x00, 0x00)
            Local1 = DerefOf (DerefOf (Arg1))
            CH06 (Arg0, 0x07, 0x2F)
            Store (DerefOf (Arg1) [0x00], Local1)
            If (Arg2)
            {
                /* Like Buffer behaviour */

                If (Y900)
                {
                    CH03 (__METHOD__, Z097, __LINE__, 0x00, 0x00)
                }
                Else
                {
                    CH04 (__METHOD__, 0x00, 0x55, Z097, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
                }
            }
            Else
            {
                /* Like Integer behaviour */

                CH06 (Arg0, 0x08, 0x2F)
            }

            Local1 = Match (DerefOf (Arg1), MTR, 0x00, MTR, 0x00, 0x00)
            CH06 (Arg0, 0x09, 0x2F)
            Return (0x00)
        }

        /* Reference to Object as Result of Method invocation */

        Method (M003, 1, Serialized)
        {
            Field (RG01, ByteAcc, NoLock, Preserve)
            {
                Offset (0x18),
                FU02,   31,
                FU03,   65
            }

            Name (I000, 0x00) /* Label to check m000 invocations */
            Method (M000, 2, NotSerialized)
            {
                I000 = Arg0
                If ((Arg1 == 0x00))
                {
                    Local0 = RefOf (FU00)
                }
                ElseIf ((Arg1 == 0x01))
                {
                    Local0 = RefOf (FU01)
                }
                ElseIf ((Arg1 == 0x02))
                {
                    Local0 = RefOf (FU02)
                }
                ElseIf ((Arg1 == 0x03))
                {
                    Local0 = RefOf (FU03)
                }

                Return (Local0)
            }

            Method (CH00, 2, NotSerialized)
            {
                If ((I000 != Arg1))
                {
                    ERR (Arg0, Z097, __LINE__, 0x00, 0x00, I000, Arg1)
                }
            }

            Name (LPN0, 0x04)
            Name (LPC0, 0x00)
            FU00 = II70 /* \II70 */
            FU01 = BI00 /* \BI00 */
            FU02 = II70 /* \II70 */
            FU03 = BI00 /* \BI00 */
            While (LPN0)
            {
                Local0 = (0x03 * LPC0) /* \M4B5.M003.LPC0 */
                I000 = 0x00
                Local1 = DerefOf (M000 (0x01, LPC0))
                CH03 (__METHOD__, Z097, __LINE__, 0x00, 0x00)
                CH00 (Arg0, 0x01)
                Local1 = DerefOf (DerefOf (M000 (0x02, LPC0)))
                CH06 (Arg0, (0x0B + Local0), 0x2F)
                CH00 (Arg0, 0x02)
                Store (DerefOf (M000 (0x03, LPC0)) [0x00], Local1)
                If ((LPC0 % 0x02))
                {
                    /* Like Buffer behaviour */

                    If (Y900)
                    {
                        CH03 (__METHOD__, Z097, __LINE__, 0x00, 0x00)
                    }
                    Else
                    {
                        CH04 (__METHOD__, 0x00, 0x55, Z097, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
                    }
                }
                Else
                {
                    /* Like Integer behaviour */

                    CH06 (Arg0, (0x0C + Local0), 0x2F)
                }

                CH00 (Arg0, 0x03)
                Local1 = Match (DerefOf (M000 (0x04, LPC0)), MTR, 0x00, MTR, 0x00, 0x00)
                CH06 (Arg0, (0x0D + Local0), 0x2F)
                CH00 (Arg0, 0x04)
                LPN0--
                LPC0++
            }
        }

        CH03 (__METHOD__, Z097, __LINE__, 0x00, 0x00)
        /* Local Named Object */

        M000 (__METHOD__)
        /* Global Named Object */

        M001 (__METHOD__)
        /* Reference to Local Named Object */

        FU02 = II70 /* \II70 */
        FU03 = BI00 /* \BI00 */
        M002 (Concatenate (__METHOD__, "-m002-RefLocNameI"), RefOf (FU02), 0x00)
        Local0 = RefOf (FU02)
        M002 (Concatenate (__METHOD__, "-m002-RefLocName2I"), Local0, 0x00)
        CondRefOf (FU02, Local0)
        M002 (Concatenate (__METHOD__, "-m002-CondRefLocNameI"), Local0, 0x00)
        M002 (Concatenate (__METHOD__, "-m002-RefLocNameB"), RefOf (FU03), 0x01)
        Local0 = RefOf (FU03)
        M002 (Concatenate (__METHOD__, "-m002-RefLocName2B"), Local0, 0x01)
        CondRefOf (FU03, Local0)
        M002 (Concatenate (__METHOD__, "-m002-CondRefLocNameB"), Local0, 0x01)
        FU00 = II70 /* \II70 */
        FU01 = BI00 /* \BI00 */
        M002 (Concatenate (__METHOD__, "-m002-RefGlobNameI"), RefOf (FU00), 0x00)
        Local0 = RefOf (FU00)
        M002 (Concatenate (__METHOD__, "-m002-RefGlobName2I"), Local0, 0x00)
        CondRefOf (FU00, Local0)
        M002 (Concatenate (__METHOD__, "-m002-CondRefGlobNameI"), Local0, 0x00)
        M002 (Concatenate (__METHOD__, "-m002-RefGlobNameB"), RefOf (FU01), 0x01)
        Local0 = RefOf (FU01)
        M002 (Concatenate (__METHOD__, "-m002-RefGlobName2B"), Local0, 0x01)
        CondRefOf (FU01, Local0)
        M002 (Concatenate (__METHOD__, "-m002-CondRefGlobNameB"), Local0, 0x01)
        /* Reference to Object as Result of Method invocation */

        M003 (__METHOD__)
    }
