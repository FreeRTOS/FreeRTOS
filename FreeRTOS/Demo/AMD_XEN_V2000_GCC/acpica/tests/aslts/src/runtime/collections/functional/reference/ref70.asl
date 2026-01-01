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
     * References
     *
     * Verify exceptions for different operators dealing with references
     */
    /*
     SEE: FILE BUG: hangs without printing error
     SEE: FILE BUG: CondRefOf doesn't cause an exception but only under some conditions
     */
    Name (Z081, 0x51)
    /* Run operator and expect ANY exception(s) */

    Method (M1A7, 7, Serialized)
    {
        FLG3 = 0x01
        FLG4 = 0x01
        /* flag, run test till the first error */

        If (C086)
        {
            /* Get current indicator of errors */

            If (GET2 ())
            {
                Return (Zero)
            }
        }

        CH03 (__METHOD__, Z081, __LINE__, 0x00, Arg6)
        /*
         // FILE BUG: hangs without printing error
         Store(CH03(ts, z081, 0x200, __LINE__, arg6), Local0)
         if (Local0) {
         Concatenate("Operation: 0x", arg6, Local0)
         Store(Local0, Debug)
         }
         */
        Switch (ToInteger (Arg6))
        {
            Case (0x07)
            {
                Local7 = Acquire (Arg0, 0x0064)
            }
            Default
            {
                M480 (Arg0, Arg1, Arg2, Arg3, Arg4, Arg5, Arg6)
            }

        }

        CH04 (C080, 0x00, 0xFF, Z081, __LINE__, Arg6, Arg6)
        /*
         // FILE BUG: hangs without printing error
         Store(CH04(c080, 0, 0xff, z081, __LINE__, arg6, arg6), Local0)
         if (Local0) {
         Concatenate("Operation: 0x", arg6, Local0)
         Store(Local0, Debug)
         }
         */
        FLG3 = 0x00
        FLG4 = 0x00
    }

    /*
     * Switch
     *
     * This sub-test causes break of exc_ref due to the bug 248
     * (lose path after exception or hang).
     * So, it is blocked, and in order to show 'Test is blocked'
     * it is run also additionally separately.
     */
    Method (M167, 1, Serialized)
    {
        CH03 ("m167", Z081, __LINE__, 0x00, 0x38)
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Local7 = 0x00
            }
            Default
            {
                Local7 = 0x01
            }

        }

        CH04 (C080, 0x00, 0xFF, Z081, __LINE__, 0x38, 0x38)
    }

    /* Check reaction on OPERAND-REFERENCE (exceptions are expected in most cases) */
    /* arg0 - reference to the value of arbitrary type */
    /* arg1 - absolute index of file initiating the checking */
    /* arg2 - index of checking (inside the file) */
    Method (M1A8, 3, Serialized)
    {
        /* Return */

        Method (M000, 1, NotSerialized)
        {
            Return (Arg0)
        }

        /* If */

        Method (M001, 1, NotSerialized)
        {
            CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x36)
            If (Arg0)
            {
                Local7 = 0x00
            }

            CH04 (C080, 0x00, 0xFF, Z081, __LINE__, 0x36, 0x36)
        }

        /* ElseIf */

        Method (M002, 1, NotSerialized)
        {
            CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x37)
            If (0x00)
            {
                Local7 = 0x00
            }
            ElseIf (Arg0)
            {
                Local7 = 0x01
            }

            CH04 (C080, 0x00, 0xFF, Z081, __LINE__, 0x37, 0x37)
        }

        /* While */

        Method (M004, 1, NotSerialized)
        {
            CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x3A)
            While (Arg0)
            {
                Local7 = 0x00
                Break
            }

            CH04 (C080, 0x00, 0xFF, Z081, __LINE__, 0x3A, 0x3A)
        }

        /* Set parameters of current checking */

        If (Arg1)
        {
            SET0 (Arg1, 0x00, Arg2)
        }

        /* flag, run test till the first error */

        If (C086)
        {
            /* Get current indicator of errors */

            If (GET2 ())
            {
                Return (Zero)
            }
        }

        /* Split into groups for debugging: some of them */
        /* were crashing the system. */
        Name (RN00, 0x01) /* CondRefOf */
        Name (RN01, 0x00) /* DerefOf */
        If (Y506)
        {
            /* Crash */

            RN01 = 0x01
        }

        Name (RN02, 0x01) /* ObjectType */
        Name (RN03, 0x01) /* RefOf */
        Name (RN04, 0x01) /* SizeOf */
        Name (RN05, 0x01) /* CopyObject */
        Name (RN06, 0x01) /* Return */
        Name (RN07, 0x01) /* If,ElseIf,Switch,While */
        Name (RN08, 0x01) /* All other operators */
        Name (B000, Buffer (0x0A){})
        Name (S000, "qwertyuiopasdfghjklz")
        Name (P000, Package (0x09)
        {
            0x01,
            0x02,
            0x03,
            0x04,
            0x05,
            0x06,
            0x07,
            0x08,
            0x09
        })
        FLG4 = 0x01
        If (RN00)
        {
            /* CondRefOf */

            CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x00)
            M480 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x05)
            CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x00)
        }

        If (RN01)
        {
            /* DerefOf */

            CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x00)
            M480 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x08)
            CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x00)
        }

        If (RN02)
        {
            /* ObjectType */

            CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x00)
            M480 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x20)
            CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x00)
        }

        If (RN03)
        {
            /* RefOf */

            CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x00)
            M480 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x22)
            CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x00)
        }

        If (RN04)
        {
            /* SizeOf */

            Local0 = 0x00
            Local1 = ObjectType (Arg0)
            Switch (ToInteger (Local1))
            {
                Case (0x01)
                {
                    /* Integer */

                    Local0 = 0x01
                }
                Case (0x02)
                {
                    /* String */

                    Local0 = 0x01
                }
                Case (0x03)
                {
                    /* Buffer */

                    Local0 = 0x01
                }
                Case (0x04)
                {
                    /* Package */

                    Local0 = 0x01
                }

            }

            If (Y505)
            {
                /* Buffer Field and Field Unit types should allow SizeOf() */

                Switch (ToInteger (Local1))
                {
                    Case (0x05)
                    {
                        /* Field Unit */

                        Local0 = 0x01
                    }
                    Case (0x0E)
                    {
                        /* Buffer Field */

                        Local0 = 0x01
                    }

                }
            }

            If (Local0)
            {
                CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x00)
                M480 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x29)
                CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x00)
            }
            Else
            {
                M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x29)
            }
        }

        /* if(rn04) */

        If (RN05)
        {
            /* CopyObject */

            CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x00)
            CopyObject (Arg0, Local7)
            CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x00)
        }

        If (RN06)
        {
            /* Return */

            CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x00)
            M000 (Arg0)
            CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x00)
        }

        If (RN07)
        {
            /* If */

            M001 (Arg0)
            /* ElseIf */

            M002 (Arg0)
            /* Switch */

            If (Y248)
            {
                M167 (Arg0)
            }
            Else
            {
                Debug = "WARNING: test m1a8:m1a8 blocked due to the bug 248!"
            }

            /* While */

            M004 (Arg0)
        }

        /* if(rn07) */

        If (RN08)
        {
            /* Acquire */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00)
            /* Add */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01)
            M1A7 (0x00, Arg0, 0x00, 0x00, 0x00, 0x00, 0x01)
            /* And */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02)
            M1A7 (0x00, Arg0, 0x00, 0x00, 0x00, 0x00, 0x02)
            /* Concatenate */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03)
            M1A7 (0x00, Arg0, 0x00, 0x00, 0x00, 0x00, 0x03)
            /* ConcatenateResTemplate */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04)
            M1A7 (0x00, Arg0, 0x00, 0x00, 0x00, 0x00, 0x04)
            /* Decrement */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x07)
            /* Divide */

            M1A7 (Arg0, 0x01, 0x00, 0x00, 0x00, 0x00, 0x09)
            M1A7 (0x01, Arg0, 0x00, 0x00, 0x00, 0x00, 0x09)
            /* Fatal */
            /* FindSetLeftBit */
            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0B)
            /* FindSetRightBit */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0C)
            /* FromBCD */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0D)
            /* Increment */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0E)
            /* Index */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0F)
            M1A7 (B000, Arg0, 0x00, 0x00, 0x00, 0x00, 0x0F)
            /* LAnd */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10)
            M1A7 (0x00, Arg0, 0x00, 0x00, 0x00, 0x00, 0x10)
            /* LEqual */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x11)
            M1A7 (0x00, Arg0, 0x00, 0x00, 0x00, 0x00, 0x11)
            /* LGreater */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x12)
            M1A7 (0x00, Arg0, 0x00, 0x00, 0x00, 0x00, 0x12)
            /* LGreaterEqual */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x13)
            M1A7 (0x00, Arg0, 0x00, 0x00, 0x00, 0x00, 0x13)
            /* LLess */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x14)
            M1A7 (0x00, Arg0, 0x00, 0x00, 0x00, 0x00, 0x14)
            /* LLessEqual */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x15)
            M1A7 (0x00, Arg0, 0x00, 0x00, 0x00, 0x00, 0x15)
            /* LNot */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x16)
            /* LNotEqual */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x17)
            M1A7 (0x00, Arg0, 0x00, 0x00, 0x00, 0x00, 0x17)
            /* LOr */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x18)
            M1A7 (0x00, Arg0, 0x00, 0x00, 0x00, 0x00, 0x18)
            /* Match */

            M1A7 (Arg0, 0x00, 0x01, 0x01, 0x01, 0x00, 0x19)
            M1A7 (P000, 0x00, Arg0, 0x01, 0x01, 0x00, 0x19)
            M1A7 (P000, 0x00, 0x01, Arg0, 0x01, 0x00, 0x19)
            M1A7 (P000, 0x00, 0x01, 0x01, Arg0, 0x00, 0x19)
            /* Mid */

            M1A7 (Arg0, 0x00, 0x05, 0x00, 0x00, 0x00, 0x1A)
            M1A7 (S000, Arg0, 0x05, 0x00, 0x00, 0x00, 0x1A)
            M1A7 (S000, 0x00, Arg0, 0x00, 0x00, 0x00, 0x1A)
            /* Mod */

            M1A7 (Arg0, 0x01, 0x00, 0x00, 0x00, 0x00, 0x1B)
            M1A7 (0x01, Arg0, 0x00, 0x00, 0x00, 0x00, 0x1B)
            /* Multiply */

            M1A7 (Arg0, 0x01, 0x00, 0x00, 0x00, 0x00, 0x1C)
            M1A7 (0x01, Arg0, 0x00, 0x00, 0x00, 0x00, 0x1C)
            /* NAnd */

            M1A7 (Arg0, 0x01, 0x00, 0x00, 0x00, 0x00, 0x1D)
            M1A7 (0x01, Arg0, 0x00, 0x00, 0x00, 0x00, 0x1D)
            /* NOr */

            M1A7 (Arg0, 0x01, 0x00, 0x00, 0x00, 0x00, 0x1E)
            M1A7 (0x01, Arg0, 0x00, 0x00, 0x00, 0x00, 0x1E)
            /* Not */

            M1A7 (Arg0, 0x01, 0x00, 0x00, 0x00, 0x00, 0x1F)
            /* Or */

            M1A7 (Arg0, 0x01, 0x00, 0x00, 0x00, 0x00, 0x21)
            M1A7 (0x01, Arg0, 0x00, 0x00, 0x00, 0x00, 0x21)
            /* Release */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x23)
            /* Reset */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x24)
            /* ShiftLeft */

            M1A7 (Arg0, 0x01, 0x00, 0x00, 0x00, 0x00, 0x26)
            M1A7 (0x01, Arg0, 0x00, 0x00, 0x00, 0x00, 0x26)
            /* ShiftRight */

            M1A7 (Arg0, 0x01, 0x00, 0x00, 0x00, 0x00, 0x27)
            M1A7 (0x01, Arg0, 0x00, 0x00, 0x00, 0x00, 0x27)
            /* Signal */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x28)
            /* Sleep */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2A)
            /* Stall */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2B)
            /* Store */

            CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x00)
            Local7 = Arg0
            CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x00)
            /* Subtract */

            M1A7 (Arg0, 0x01, 0x00, 0x00, 0x00, 0x00, 0x2D)
            M1A7 (0x01, Arg0, 0x00, 0x00, 0x00, 0x00, 0x2D)
            /* ToBCD */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2E)
            /* ToBuffer */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2F)
            /* ToDecimalString */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x30)
            /* ToHexString */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x31)
            /* ToInteger */

            M1A7 (Arg0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x32)
            /* ToString */

            M1A7 (Arg0, 0x01, 0x00, 0x00, 0x00, 0x00, 0x33)
            M1A7 (B000, Arg0, 0x00, 0x00, 0x00, 0x00, 0x33)
            /* Wait */

            M1A7 (Arg0, 0x01, 0x00, 0x00, 0x00, 0x00, 0x34)
            M1A7 (B000, Arg0, 0x00, 0x00, 0x00, 0x00, 0x34)
            /* XOr */

            M1A7 (Arg0, 0x01, 0x00, 0x00, 0x00, 0x00, 0x35)
            M1A7 (B000, Arg0, 0x00, 0x00, 0x00, 0x00, 0x35)
        } /* if(rn08) */

        FLG4 = 0x00
        RST0 ()
        Return (Zero)
    }

    /* Simple test, only some particular ways of obtaining references */

    Method (M1A9, 0, Serialized)
    {
        /* FILE BUG: CondRefOf doesn't cause an exception but only under some conditions, */
        /* namely for rn00 == 2. */
        Name (RN00, 0x02) /* Simplest modes, for debugging */
        Name (RN01, 0x01) /* Crash */
        If ((RN00 == 0x00))
        {
            /* Simplest mode, ONE-TWO operations of those below */

            Local0 = RefOf (I900)
            M1A8 (Local0, Z081, 0x0F)
            Local1 = CondRefOf (I900, Local0)
            If (M1A4 (Local1, 0x22))
            {
                M1A8 (Local0, Z081, 0x23)
            }
        }
        ElseIf ((RN00 == 0x01))
        {
            /* Simplest mode, SOME of operations below */

            Store (S900 [0x00], Local0)
            M1A8 (Local0, Z081, 0x00)
            Store (B900 [0x03], Local0)
            M1A8 (Local0, Z081, 0x01)
            Store (P901 [0x00], Local0)
            M1A8 (Local0, Z081, 0x02)
            Store (P91E [0x00], Local0)
            M1A8 (Local0, Z081, 0x04)
            Local0 = Local1 = P901 [0x00]
            M1A8 (Local1, Z081, 0x0A)
            Local0 = Local1 = P91E [0x00]
            M1A8 (Local1, Z081, 0x0E)
            Local0 = RefOf (I900)
            M1A8 (Local0, Z081, 0x0F)
            Local0 = RefOf (F900)
            M1A8 (Local0, Z081, 0x12)
            Local0 = RefOf (BN90)
            M1A8 (Local0, Z081, 0x13)
            Local0 = RefOf (IF90)
            M1A8 (Local0, Z081, 0x14)
            Local0 = RefOf (BF90)
            M1A8 (Local0, Z081, 0x15)
            Local1 = CondRefOf (I900, Local0)
            If (M1A4 (Local1, 0x22))
            {
                M1A8 (Local0, Z081, 0x23)
            }
        }
        Else
        {
            /* Index */

            Store (S900 [0x00], Local0)
            M1A8 (Local0, Z081, 0x00)
            Store (B900 [0x03], Local0)
            M1A8 (Local0, Z081, 0x01)
            Store (P901 [0x00], Local0)
            M1A8 (Local0, Z081, 0x02)
            If (RN01)
            {
                Store (P916 [0x00], Local0)
                M1A8 (Local0, Z081, 0x03)
            }

            Store (P91E [0x00], Local0)
            M1A8 (Local0, Z081, 0x04)
            Local0 = Local1 = S900 [0x00]
            M1A8 (Local0, Z081, 0x05)
            M1A8 (Local1, Z081, 0x06)
            Local0 = Local1 = B900 [0x03]
            M1A8 (Local0, Z081, 0x07)
            M1A8 (Local1, Z081, 0x08)
            Local0 = Local1 = P901 [0x00]
            M1A8 (Local0, Z081, 0x09)
            M1A8 (Local1, Z081, 0x0A)
            If (RN01)
            {
                Local0 = Local1 = P916 [0x00]
                M1A8 (Local0, Z081, 0x0B)
                M1A8 (Local1, Z081, 0x0C)
            }

            Local0 = Local1 = P91E [0x00]
            M1A8 (Local0, Z081, 0x0D)
            M1A8 (Local1, Z081, 0x0E)
            /* RefOf */

            Local0 = RefOf (I900)
            M1A8 (Local0, Z081, 0x0F)
            Local0 = RefOf (S900)
            M1A8 (Local0, Z081, 0x10)
            Local0 = RefOf (B900)
            M1A8 (Local0, Z081, 0x11)
            Local0 = RefOf (F900)
            M1A8 (Local0, Z081, 0x12)
            Local0 = RefOf (BN90)
            M1A8 (Local0, Z081, 0x13)
            Local0 = RefOf (IF90)
            M1A8 (Local0, Z081, 0x14)
            Local0 = RefOf (BF90)
            M1A8 (Local0, Z081, 0x15)
            Local0 = RefOf (E900)
            M1A8 (Local0, Z081, 0x16)
            Local0 = RefOf (MX90)
            M1A8 (Local0, Z081, 0x17)
            Local0 = RefOf (D900)
            M1A8 (Local0, Z081, 0x18)
            Local0 = RefOf (TZ90)
            M1A8 (Local0, Z081, 0x19)
            Local0 = RefOf (PR90)
            M1A8 (Local0, Z081, 0x1A)
            Local0 = RefOf (R900)
            M1A8 (Local0, Z081, 0x1B)
            Local0 = RefOf (PW90)
            M1A8 (Local0, Z081, 0x1C)
            Local0 = RefOf (P900)
            M1A8 (Local0, Z081, 0x1D)
            Local0 = RefOf (P901)
            M1A8 (Local0, Z081, 0x1E)
            Local0 = RefOf (P916)
            M1A8 (Local0, Z081, 0x1F)
            Local0 = RefOf (P91D)
            M1A8 (Local0, Z081, 0x20)
            Local0 = RefOf (P91E)
            M1A8 (Local0, Z081, 0x21)
            /* CondRefOf */

            Local1 = CondRefOf (I900, Local0)
            If (M1A4 (Local1, 0x22))
            {
                M1A8 (Local0, Z081, 0x23)
            }

            Local1 = CondRefOf (S900, Local0)
            If (M1A4 (Local1, 0x24))
            {
                M1A8 (Local0, Z081, 0x25)
            }

            Local1 = CondRefOf (B900, Local0)
            If (M1A4 (Local1, 0x26))
            {
                M1A8 (Local0, Z081, 0x27)
            }

            Local1 = CondRefOf (F900, Local0)
            If (M1A4 (Local1, 0x28))
            {
                M1A8 (Local0, Z081, 0x29)
            }

            Local1 = CondRefOf (BN90, Local0)
            If (M1A4 (Local1, 0x2A))
            {
                M1A8 (Local0, Z081, 0x2B)
            }

            Local1 = CondRefOf (IF90, Local0)
            If (M1A4 (Local1, 0x2C))
            {
                M1A8 (Local0, Z081, 0x2D)
            }

            Local1 = CondRefOf (BF90, Local0)
            If (M1A4 (Local1, 0x2E))
            {
                M1A8 (Local0, Z081, 0x2F)
            }

            Local1 = CondRefOf (E900, Local0)
            If (M1A4 (Local1, 0x30))
            {
                M1A8 (Local0, Z081, 0x31)
            }

            Local1 = CondRefOf (MX90, Local0)
            If (M1A4 (Local1, 0x32))
            {
                M1A8 (Local0, Z081, 0x33)
            }

            Local1 = CondRefOf (D900, Local0)
            If (M1A4 (Local1, 0x34))
            {
                M1A8 (Local0, Z081, 0x35)
            }

            Local1 = CondRefOf (TZ90, Local0)
            If (M1A4 (Local1, 0x36))
            {
                M1A8 (Local0, Z081, 0x37)
            }

            Local1 = CondRefOf (PR90, Local0)
            If (M1A4 (Local1, 0x38))
            {
                M1A8 (Local0, Z081, 0x39)
            }

            Local1 = CondRefOf (R900, Local0)
            If (M1A4 (Local1, 0x3A))
            {
                M1A8 (Local0, Z081, 0x3B)
            }

            Local1 = CondRefOf (PW90, Local0)
            If (M1A4 (Local1, 0x3C))
            {
                M1A8 (Local0, Z081, 0x3D)
            }

            Local1 = CondRefOf (P900, Local0)
            If (M1A4 (Local1, 0x3E))
            {
                M1A8 (Local0, Z081, 0x3F)
            }

            Local1 = CondRefOf (P901, Local0)
            If (M1A4 (Local1, 0x40))
            {
                M1A8 (Local0, Z081, 0x41)
            }

            Local1 = CondRefOf (P916, Local0)
            If (M1A4 (Local1, 0x42))
            {
                M1A8 (Local0, Z081, 0x43)
            }

            Local1 = CondRefOf (P91D, Local0)
            If (M1A4 (Local1, 0x44))
            {
                M1A8 (Local0, Z081, 0x45)
            }

            Local1 = CondRefOf (P91E, Local0)
            If (M1A4 (Local1, 0x46))
            {
                M1A8 (Local0, Z081, 0x47)
            }
        }
    }

    Method (M106, 0, Serialized)
    {
        Name (I000, 0xABCD0000)
        Method (M000, 1, NotSerialized)
        {
            CH03 (__METHOD__, Z081, __LINE__, 0x00, 0x00)
            Debug = DerefOf (RefOf (DerefOf (RefOf (Arg0))))
            CH04 (C080, 0x00, 0xFF, Z081, __LINE__, 0x00, 0x00)
        }

        M000 (I000)
    }

    /* Run-method */

    Method (REF5, 0, Serialized)
    {
        Name (P91E, Package (0x01)
        {
            0xABCD0000
        })
        Debug = "TEST: REF5, References, check exceptions"
        C080 = "REF5" /* name of test */
        C081 = Z081       /* absolute index of file initiating the checking */ /* \Z081 */
        C082 = 0x01      /* flag of test of exceptions */
        C083 = 0x00      /* run verification of references (write/read) */
        C084 = 0x00      /* run verification of references (reading) */
        C085 = 0x00      /* create the chain of references to LocalX, then dereference them */
        C086 = 0x00      /* flag, run test till the first error */
        C087 = 0x01      /* apply DeRefOf to ArgX-ObjectReference */
        C089 = 0x01      /* flag of Reference, object otherwise */
        If (0x00)
        {
            /* This mode of test run takes much time, moreover, */
            /* due to the bug 95 of ACPICA it fails to complete. */
            /* So, if run it then do it with the flag c086 set up */
            /* - run test till the first error. */
            C086 = 0x01 /* flag, run test till the first error */
            /* For local data (methods of ref1.asl) */
            /* Reset current indicator of errors */
            RST2 ()
            C081 = Z077 /* absolute index of file initiating the checking */ /* \Z077 */
            SRMT ("m168")
            M168 ()
            SRMT ("m169")
            M169 ()
            SRMT ("m16a")
            M16A (0x00)
            SRMT ("m16b")
            M16B ()
            SRMT ("m16c")
            M16C (0x00)
            SRMT ("m16d")
            M16D ()
            SRMT ("m16e")
            M16E ()
            /* For global data (methods of ref4.asl) */

            C081 = Z080 /* absolute index of file initiating the checking */ /* \Z080 */
            SRMT ("m190")
            M190 ()
            SRMT ("m191")
            M191 (0x00)
            SRMT ("m192")
            M192 ()
            SRMT ("m193")
            M193 (0x00)
            SRMT ("m194")
            M194 ()
        }
        Else
        {
            /* Run simple test only for some particular ways of */
            /* obtaining references. */
            C086 = 0x00 /* don't break testing on error appearance */
            SRMT ("m1a9")
            M1A9 ()
        }

        /* Particular tests */

        SRMT ("m106")
        M106 ()
        SRMT ("m167")
        If (Y248)
        {
            /* This code here only to not forget to run m1a8:m167 */

            Local0 = Local1 = P91E [0x00]
            M167 (Local0)
        }
        Else
        {
            BLCK ()
        }
    }
