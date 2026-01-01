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
     *  Buffer Field
     *
     * (verify exceptions caused by the imprope use of Buffer Field type objects)
     */
    Name (Z106, 0x6A)
    Name (B700, Buffer (0x14){})
    CreateField (B700, 0x0B, 0x1F, BF20)
    CreateField (B700, 0x3A, 0x41, BF21)
    Name (II71, 0xABCD1234)
    Name (BI01, Buffer (0x09)
    {
        /* 0000 */  0xA4, 0xA5, 0xA6, 0xA7, 0xB8, 0xB9, 0xBA, 0xBB,  // ........
        /* 0008 */  0xBC                                             // .
    })
    /* Expected exceptions: */
    /* */
    /* 47 - AE_AML_OPERAND_TYPE */
    /* See notes to m4b1 and m4b3 */
    /* */
    Method (M4BE, 0, Serialized)
    {
        Name (BBF1, Buffer (0x14){})
        CreateField (BBF1, 0x0B, 0x1F, BF02)
        CreateField (BBF1, 0x3A, 0x41, BF03)
        /* Local Named Object */

        Method (M000, 1, Serialized)
        {
            Name (BBF1, Buffer (0x14){})
            CreateField (BBF1, 0x0B, 0x1F, BF02)
            CreateField (BBF1, 0x3A, 0x41, BF03)
            BF02 = II71 /* \II71 */
            BF03 = BI01 /* \BI01 */
            /* Like Integer behaviour */

            If (Y083)
            {
                Local1 = DerefOf (BF02)
                CH06 (Arg0, 0x00, 0x2F)
            }

            Store (BF02 [0x00], Local1)
            CH03 (__METHOD__, Z106, __LINE__, 0x00, 0x00)
            /* Like Buffer behaviour */

            If (Y083)
            {
                Local1 = DerefOf (BF03)
                CH06 (Arg0, 0x02, 0x2F)
            }

            Store (BF03 [0x00], Local1)
            If (Y900)
            {
                CH03 (__METHOD__, Z106, __LINE__, 0x00, 0x00)
            }
            Else
            {
                CH04 (__METHOD__, 0x00, 0x55, Z106, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
            }
        }

        /* Global Named Object */

        Method (M001, 1, NotSerialized)
        {
            BF20 = II71 /* \II71 */
            BF21 = BI01 /* \BI01 */
            /* Like Integer behaviour */

            If (Y083)
            {
                Local1 = DerefOf (BF20)
                CH06 (Arg0, 0x03, 0x2F)
            }

            Store (BF20 [0x00], Local1)
            CH03 (__METHOD__, Z106, __LINE__, 0x00, 0x00)
            /* Like Buffer behaviour */

            If (Y083)
            {
                Local1 = DerefOf (BF21)
                CH06 (Arg0, 0x05, 0x2F)
            }

            Store (BF21 [0x00], Local1)
            If (Y900)
            {
                CH03 (__METHOD__, Z106, __LINE__, 0x00, 0x00)
            }
            Else
            {
                CH04 (__METHOD__, 0x00, 0x55, Z106, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
            }
        }

        /* Reference to Object */

        Method (M002, 3, NotSerialized)
        {
            Debug = Arg0
            Debug = Arg1
            Local0 = ObjectType (Arg1)
            If ((Local0 != 0x0E))
            {
                ERR (Arg0, Z106, __LINE__, 0x00, 0x00, Local0, 0x0E)
                Return (0x01)
            }

            Local1 = DerefOf (Arg1)
            CH03 (__METHOD__, Z106, __LINE__, 0x00, 0x00)
            Local1 = DerefOf (DerefOf (Arg1))
            CH06 (Arg0, 0x07, 0x2F)
            Store (DerefOf (Arg1) [0x00], Local1)
            If (Arg2)
            {
                /* Like Buffer behaviour */

                If (Y900)
                {
                    CH03 (__METHOD__, Z106, __LINE__, 0x00, 0x00)
                }
                Else
                {
                    CH04 (__METHOD__, 0x00, 0x55, Z106, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
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
            Name (BBF1, Buffer (0x14){})
            CreateField (BBF1, 0x0B, 0x1F, BF02)
            CreateField (BBF1, 0x3A, 0x41, BF03)
            Name (I000, 0x00) /* Label to check m000 invocations */
            Method (M000, 2, NotSerialized)
            {
                I000 = Arg0
                If ((Arg1 == 0x00))
                {
                    Local0 = RefOf (BF20)
                }
                ElseIf ((Arg1 == 0x01))
                {
                    Local0 = RefOf (BF21)
                }
                ElseIf ((Arg1 == 0x02))
                {
                    Local0 = RefOf (BF02)
                }
                ElseIf ((Arg1 == 0x03))
                {
                    Local0 = RefOf (BF03)
                }

                Return (Local0)
            }

            Method (CH00, 2, NotSerialized)
            {
                If ((I000 != Arg1))
                {
                    ERR (Arg0, Z106, __LINE__, 0x00, 0x00, I000, Arg1)
                }
            }

            Name (LPN0, 0x04)
            Name (LPC0, 0x00)
            BF20 = II71 /* \II71 */
            BF21 = BI01 /* \BI01 */
            BF02 = II71 /* \II71 */
            BF03 = BI01 /* \BI01 */
            While (LPN0)
            {
                Local0 = (0x03 * LPC0) /* \M4BE.M003.LPC0 */
                I000 = 0x00
                Local1 = DerefOf (M000 (0x01, LPC0))
                CH03 (__METHOD__, Z106, (0x04 + LPC0), 0x00, 0x00)
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
                        CH03 (__METHOD__, Z106, (0x08 + LPC0), 0x00, 0x00)
                    }
                    Else
                    {
                        CH04 (__METHOD__, 0x00, 0x55, Z106, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
                    }
                }

                CH00 (Arg0, 0x03)
                Local1 = Match (DerefOf (M000 (0x04, LPC0)), MTR, 0x00, MTR, 0x00, 0x00)
                CH06 (Arg0, (0x0D + Local0), 0x2F)
                CH00 (Arg0, 0x04)
                LPN0--
                LPC0++
            }
        }

        CH03 (__METHOD__, Z106, __LINE__, 0x00, 0x00)
        /* Local Named Object */

        M000 (__METHOD__)
        /* Global Named Object */

        M001 (__METHOD__)
        /* Reference to Local Named Object */

        BF02 = II71 /* \II71 */
        BF03 = BI01 /* \BI01 */
        M002 (Concatenate (__METHOD__, "-m002-RefLocNameI"), RefOf (BF02), 0x01)
        Local0 = RefOf (BF02)
        M002 (Concatenate (__METHOD__, "-m002-RefLocName2I"), Local0, 0x01)
        CondRefOf (BF02, Local0)
        M002 (Concatenate (__METHOD__, "-m002-CondRefLocNameI"), Local0, 0x01)
        M002 (Concatenate (__METHOD__, "-m002-RefLocNameB"), RefOf (BF03), 0x01)
        Local0 = RefOf (BF03)
        M002 (Concatenate (__METHOD__, "-m002-RefLocName2B"), Local0, 0x01)
        CondRefOf (BF03, Local0)
        M002 (Concatenate (__METHOD__, "-m002-CondRefLocNameB"), Local0, 0x01)
        BF20 = II71 /* \II71 */
        BF21 = BI01 /* \BI01 */
        M002 (Concatenate (__METHOD__, "-m002-RefGlobNameI"), RefOf (BF20), 0x01)
        Local0 = RefOf (BF20)
        M002 (Concatenate (__METHOD__, "-m002-RefGlobName2I"), Local0, 0x01)
        CondRefOf (BF20, Local0)
        M002 (Concatenate (__METHOD__, "-m002-CondRefGlobNameI"), Local0, 0x01)
        M002 (Concatenate (__METHOD__, "-m002-RefGlobNameB"), RefOf (BF21), 0x01)
        Local0 = RefOf (BF21)
        M002 (Concatenate (__METHOD__, "-m002-RefGlobName2B"), Local0, 0x01)
        CondRefOf (BF21, Local0)
        M002 (Concatenate (__METHOD__, "-m002-CondRefGlobNameB"), Local0, 0x01)
        /* Reference to Object as Result of Method invocation */

        M003 (__METHOD__)
    }
