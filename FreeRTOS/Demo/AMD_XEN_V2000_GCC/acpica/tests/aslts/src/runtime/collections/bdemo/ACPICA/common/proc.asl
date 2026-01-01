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
     * Common use Methods
     */
    /*
     * Verification of Package
     *
     * arg0 - Package
     * arg1 - size of Package
     * arg2 - size of pre-initialized area
     * arg3 - index of area to be written
     * arg4 - size of area to be written
     * arg5 - maximal number of pre-initialized elements to be verified
     * arg6 - maximal number of written elements to be verified
     */
    Method (MD6A, 7, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        /* Writing */

        If (Arg4)
        {
            LPN0 = Arg4
            LPC0 = Arg3
            While (LPN0)
            {
                TRC0 (Arg0, LPC0, LPC0)
                Arg0 [LPC0] = LPC0 /* \MD6A.LPC0 */
                LPN0--
                LPC0++
            }
        }

        /* Verifying pre-initialized area */

        If ((Arg2 && Arg5))
        {
            If ((Arg2 < Arg5))
            {
                Arg5 = Arg2
            }

            LPN0 = Arg5
            LPC0 = 0x00
            While (LPN0)
            {
                Local0 = DerefOf (Arg0 [LPC0])
                TRC1 (Arg0, LPC0, Local0)
                If ((Local0 != LPC0))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, LPC0)
                }

                LPN0--
                LPC0++
            }
        }

        If (Arg2)
        {
            /* First pre-initialized element */

            Local0 = DerefOf (Arg0 [0x00])
            TRC1 (Arg0, 0x00, Local0)
            If ((Local0 != 0x00))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
            }

            /* Last pre-initialized element */

            Local0 = (Arg2 - 0x01)
            Local1 = DerefOf (Arg0 [Local0])
            TRC1 (Arg0, Local0, Local1)
            If ((Local1 != Local0))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, Local0)
            }

            /* Middle pre-initialized element */

            Divide (Arg2, 0x02, Local1, Local0)
            Local1 = DerefOf (Arg0 [Local0])
            TRC1 (Arg0, Local0, Local1)
            If ((Local1 != Local0))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, Local0)
            }
        }

        /* Verifying written area */

        If ((Arg4 && Arg6))
        {
            If ((Arg4 < Arg6))
            {
                Arg6 = Arg4
            }

            LPN0 = Arg6
            LPC0 = Arg3
            While (LPN0)
            {
                Local0 = DerefOf (Arg0 [LPC0])
                TRC1 (Arg0, LPC0, Local0)
                If ((Local0 != LPC0))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, LPC0)
                }

                LPN0--
                LPC0++
            }
        }

        If (Arg4)
        {
            /* First written element */

            Local0 = DerefOf (Arg0 [Arg3])
            TRC1 (Arg0, Arg3, Local0)
            If ((Local0 != Arg3))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Arg3)
            }

            /* Last written element */

            Local0 = (Arg3 + Arg4)
            Local0--
            Local1 = DerefOf (Arg0 [Local0])
            TRC1 (Arg0, Local0, Local1)
            If ((Local1 != Local0))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, Local0)
            }

            /* Middle written element */

            Divide (Arg4, 0x02, Local0, Local1)
            Local0 = (Arg3 + Local1)
            Local1 = DerefOf (Arg0 [Local0])
            TRC1 (Arg0, Local0, Local1)
            If ((Local1 != Local0))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, Local0)
            }
        }

        /* Check exception on access to the uninitialized element */

        If ((Arg2 < Arg1))
        {
            If (Arg4)
            {
                If ((Arg3 > Arg2))
                {
                    /* Just after pre-initialized area */

                    TRC1 (Arg0, Arg2, 0xF0F0F0F0)
                    Store (Arg0 [Arg2], Local0)
                    CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
                    Local1 = DerefOf (Local0)
                    CH04 (__METHOD__, 0x01, 0x33, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_UNINITIALIZED_ELEMENT */
                    /* Just before written area */

                    Local1 = (Arg3 - 0x01)
                    TRC1 (Arg0, Local1, 0xF0F0F0F0)
                    Store (Arg0 [Local1], Local0)
                    CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
                    Local1 = DerefOf (Local0)
                    CH04 (__METHOD__, 0x01, 0x33, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_UNINITIALIZED_ELEMENT */
                }

                /* Just after pre-initialized and written areas */

                Local7 = (Arg3 + Arg4)
                If ((Arg2 > Local7))
                {
                    Local7 = Arg2
                }

                If ((Local7 < Arg1))
                {
                    TRC1 (Arg0, Local7, 0xF0F0F0F0)
                    Store (Arg0 [Local7], Local0)
                    CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
                    Local1 = DerefOf (Local0)
                    CH04 (__METHOD__, 0x01, 0x33, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_UNINITIALIZED_ELEMENT */
                    /* Last element of Package */

                    Local1 = (Arg1 - 0x01)
                    TRC1 (Arg0, Local1, 0xF0F0F0F0)
                    Store (Arg0 [Local1], Local0)
                    CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
                    Local1 = DerefOf (Local0)
                    CH04 (__METHOD__, 0x01, 0x33, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_UNINITIALIZED_ELEMENT */
                }
            }
            Else
            {
                /* Just after pre-initialized area */

                TRC1 (Arg0, Arg2, 0xF0F0F0F0)
                Store (Arg0 [Arg2], Local0)
                CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
                Local1 = DerefOf (Local0)
                CH04 (__METHOD__, 0x01, 0x33, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_UNINITIALIZED_ELEMENT */
                /* Last element of Package */

                Local1 = (Arg1 - 0x01)
                TRC1 (Arg0, Local1, 0xF0F0F0F0)
                Store (Arg0 [Local1], Local0)
                CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
                Local1 = DerefOf (Local0)
                CH04 (__METHOD__, 0x01, 0x33, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_UNINITIALIZED_ELEMENT */
            }
        }

        /* Check exception on out of Package access */

        TRC1 (Arg0, Arg1, 0xF0F0F0F0)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = Arg0 [Arg1]
        CH04 (__METHOD__, 0x00, 0x37, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_PACKAGE_LIMIT */
        Local7 = (Arg1 + 0x01)
        If ((Local7 >= Arg1))
        {
            TRC1 (Arg0, Local7, 0xF0F0F0F0)
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = Arg0 [Local7]
            CH04 (__METHOD__, 0x00, 0x37, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_PACKAGE_LIMIT */
        }

        If ((0xFFFFFFFFFFFFFFFF >= Arg1))
        {
            TRC1 (Arg0, 0xFFFFFFFFFFFFFFFF, 0xF0F0F0F0)
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = Arg0 [0xFFFFFFFFFFFFFFFF]
            CH04 (__METHOD__, 0x00, 0x37, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_PACKAGE_LIMIT */
        }

        /* Check near the maximal bound of a simple Package */
        /* (not VarPackage) - 254, 255, 256, 257 elements: */
        MD6B (Arg0, Arg1, Arg2, Arg3, Arg4, 0xFE)
        MD6B (Arg0, Arg1, Arg2, Arg3, Arg4, 0xFF)
        MD6B (Arg0, Arg1, Arg2, Arg3, Arg4, 0x0100)
        MD6B (Arg0, Arg1, Arg2, Arg3, Arg4, 0x0101)
        TRC2 ("The test run up to the end")
    }

    /*
     * Verification of Package
     *
     * arg0 - Package
     * arg1 - size of Package
     * arg2 - size of pre-initialized area
     * arg3 - index of area to be written
     * arg4 - size of area to be written
     * arg5 - index of element of Package to be verified
     */
    Method (MD6B, 6, NotSerialized)
    {
        Local7 = 0x00
        If ((Arg5 < Arg2))
        {
            Local7 = 0x01
        }
        ElseIf ((Arg5 >= Arg3))
        {
            Local0 = (Arg3 + Arg4)
            If ((Arg5 < Local0))
            {
                Local7 = 0x01
            }
        }

        If (Local7)
        {
            /* Was initialized */

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = DerefOf (Arg0 [Arg5])
            TRC1 (Arg0, Arg5, Local0)
            If ((Local0 != Arg5))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Arg5)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        }
        ElseIf ((Arg5 < Arg1))
        {
            /* Check exception on access to the uninitialized element */

            TRC1 (Arg0, Arg5, 0xF0F0F0F0)
            Store (Arg0 [Arg5], Local0)
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local1 = DerefOf (Local0)
            CH04 (__METHOD__, 0x01, 0x33, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_UNINITIALIZED_ELEMENT */
        }
        Else
        {
            /* Check exception on out of Package access */

            TRC1 (Arg0, Arg5, 0xF0F0F0F0)
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = Arg0 [Arg5]
            CH04 (__METHOD__, 0x00, 0x37, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_PACKAGE_LIMIT */
        }
    }

    /*
     * Check, register errors and reset the global level
     * execution exception AE_AML_DIVIDE_BY_ZERO caused in
     * demo-test of bug 162.
     */
    Method (MD7D, 0, NotSerialized)
    {
        ID01 = 0x00
        Local0 = ERRS /* \ERRS */
        /*
         * Slacken expectations:
         *
         * - check opcode of the FIRST exception
         * - number of exceptions NOT GREATER than two
         */
        /* Check opcode of the first exception */
        CH04 (__METHOD__, 0x01, 0x38, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_DIVIDE_BY_ZERO */
        /* Number of exceptions not greater than two */

        If ((EXC1 > 0x02))
        {
            ID01 = 0x01
        }

        /* Reset the number of exceptions */

        EXC1 = 0x00
        If ((ERRS != Local0))
        {
            ID01 = 0x01
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Return (0x01)
    }

    /*
     * Check result
     * arg0 - result
     * arg1 - expected type of result
     * arg2 - expected result
     * arg3 - index of checking
     * arg4 - index of checking
     * arg5 - tag, to check the value of object
     */
    Method (MF88, 6, NotSerialized)
    {
        Local0 = ObjectType (Arg0)
        If ((Local0 != Arg1))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Arg1)
        }

        If (Arg5)
        {
            If ((Arg0 != Arg2))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg0, Arg2)
            }
        }
    }

    Method (M02A, 0, NotSerialized)
    {
        Debug = "Check the error manually and remove call to m02a() when the bug is fixed."
        ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
    }
