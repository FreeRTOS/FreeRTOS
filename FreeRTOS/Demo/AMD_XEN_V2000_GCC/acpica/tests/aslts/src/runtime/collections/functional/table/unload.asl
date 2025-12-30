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
     * UnLoad ASL operator functionality
     */
    /*
     * This sub-test is intended to comprehensively verify
     * the Unload ASL operator functionality.
     *
     * Performs a run-time unload of a Definition Block that was
     * loaded using a Load (and LoadTable) term.
     *
     * The overall functionality of the Unload Objects is indirectly
     * verified by other Table management tests as far as Unload is
     * needed to perform cleanup and check effectiveness of Load and
     * LoadTable operators.
     *
     *    17.5.126   Unload (Unload Definition Block)
     *    Syntax
     * Unload (Handle)
     *
     * On testing the following issues should be covered (actually in the tests
     * of loading except for the exceptional conditions ones):
     *
     * - successful execution of the Unload operator for the specified DDBHandle
     *   obtained through loading of a SSDT from a proper location,
     *
     * - successful execution of the Unload operator for the specified DDBHandle
     *   obtained through LoadTable operator,
     *
     * - the Handle parameter of the Unload can be specified as Named Object,
     *   LocalX, ArgX, Derefof (to Index or RefOf reference), and Method call,
     *
     * - all namespace objects created as a result of the corresponding Load
     *   operation are removed from the namespace,
     *
     * - unloading a number of different SSDTs,
     *
     * - Load/UnLoad processing can be done with the same table many times,
     *
     * - exceptional conditions caused by inappropriate data:
     *   = the parameter of the UnLoad operator is not of DDBHandle type,
     *   = execute UnLoad operator with the same DDBHandle repeatedly,
     *   = the operand of UnLoad operator is absent.
     *
     * Can not be tested following issues:
     * - unloading a SSDT to be a synchronous operation ("the control methods
     *   defined in the Definition Block are not executed during load time")
     */
    Name (Z175, 0xAF)
    Device (DTM1)
    {
        /* Different Sources to specify DDBHandle for UnLoad. */
        /* Most of them (Named Object, LocalX, ArgX, Derefof) */
        /* are checked in load.asl */
        /* DDBHandle returned by Method call */
        Method (TST0, 1, Serialized)
        {
            Name (HI0, 0x00)
            Method (M000, 0, NotSerialized)
            {
                Return (HI0) /* \DTM1.TST0.HI0_ */
            }

            Concatenate (Arg0, "-tst0", Arg0)
            \DTM0.RFU0 = \DTM0.BUF0
            If (CondRefOf (\SSS0, Local0))
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                Return (Zero)
            }

            /* Modify Revision field of SSDT */

            Store ((\DTM0.CREV + 0x01), \DTM0.CREV)
            /* Recalculate and save CheckSum */

            Local0 = \DTM0.RFU0
            Store ((\DTM0.SUM + \DTM0.CHSM (Local0, SizeOf (Local0))), \DTM0.SUM)
            If (CH03 (Arg0, Z175, __LINE__, 0x00, 0x00))
            {
                Return (Zero)
            }

            Load (\DTM0.RFU0, HI0) /* \DTM1.TST0.HI0_ */
            If (CH03 (Arg0, Z175, __LINE__, 0x00, 0x00))
            {
                Return (Zero)
            }

            Debug = "Table Loaded"
            Local1 = ObjectType (HI0)
            If ((Local1 != C017))
            {
                /* DDB Handle */

                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, Local1, C017)
            }

            /* Check the new Object appears */

            If (CondRefOf (\SSS0, Local0)){}
            Else
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\SSS0", 0x00)
            }

            Local1 = ObjectType (Local0)
            If ((Local1 != C010))
            {
                /* Method */

                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, Local1, C010)
            }
            Else
            {
                Local0 = \SSS0 ()
                If (CH03 (Arg0, Z175, __LINE__, 0x00, 0x01))
                {
                    Return (Zero)
                }

                If (("\\SSS0" != Local0))
                {
                    ERR (Arg0, Z175, __LINE__, 0x00, 0x00, Local0, "\\SSS0")
                }
            }

            /* UnLoad operator execution */

            Unload (M000 ())
            If (CH03 (Arg0, Z175, __LINE__, 0x00, 0x00))
            {
                Return (Zero)
            }

            Debug = "Table Unloaded"
            If (CondRefOf (\SSS0, Local0))
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
            }

            Return (Zero)
        }

        /* All namespace objects created as a result of the corresponding */
        /* Load operation are absent in the namespace after UnLoad */
        Method (TST1, 1, Serialized)
        {
            Name (DDB0, 0x00)
            Name (DDB1, 0x00)
            Method (M000, 4, NotSerialized)
            {
                Concatenate (Arg0, "-m000.", Arg0)
                Concatenate (Arg0, Arg1, Arg0)
                Local0 = ObjectType (Arg2)
                If ((Arg3 != Local0))
                {
                    ERR (Arg0, Z175, __LINE__, 0x00, 0x00, Local0, Arg3)
                    Return (0x01)
                }

                Return (0x00)
            }

            Method (M001, 1, NotSerialized)
            {
                Concatenate (Arg0, "-m001", Arg0)
                /* Integer */

                If (CondRefOf (\AUXD.INT0, Local0))
                {
                    ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.INT0", 0x01)
                    Return (0x01)
                }

                /* String */

                If (CondRefOf (\AUXD.STR0, Local0))
                {
                    ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.STR0", 0x01)
                    Return (0x01)
                }

                /* Buffer */

                If (CondRefOf (\AUXD.BUF0, Local0))
                {
                    ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.BUF0", 0x01)
                    Return (0x01)
                }

                /* Package */

                If (CondRefOf (\AUXD.PAC0, Local0))
                {
                    ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.PAC0", 0x01)
                    Return (0x01)
                }

                /* Field Unit */

                If (CondRefOf (\AUXD.FLU0, Local0))
                {
                    ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.FLU0", 0x01)
                    Return (0x01)
                }

                /* Device */

                If (CondRefOf (\AUXD.DEV0, Local0))
                {
                    ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.DEV0", 0x01)
                    Return (0x01)
                }

                /* Event */

                If (CondRefOf (\AUXD.EVE0, Local0))
                {
                    ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.EVE0", 0x01)
                    Return (0x01)
                }

                /* Method */

                If (CondRefOf (\AUXD.MMM0, Local0))
                {
                    ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.MMM0", 0x01)
                    Return (0x01)
                }

                /* Mutex */

                If (CondRefOf (\AUXD.MTX0, Local0))
                {
                    ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.MTX0", 0x01)
                    Return (0x01)
                }

                /* OpRegion */

                If (CondRefOf (\AUXD.OPR0, Local0))
                {
                    ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.OPR0", 0x01)
                    Return (0x01)
                }

                /* Power Resource */

                If (CondRefOf (\AUXD.PWR0, Local0))
                {
                    ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.PWR0", 0x01)
                    Return (0x01)
                }

                /* Processor */

                If (CondRefOf (\AUXD.CPU0, Local0))
                {
                    ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.CPU0", 0x01)
                    Return (0x01)
                }

                /* Thermal Zone */

                If (CondRefOf (\AUXD.TZN0, Local0))
                {
                    ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.TZN0", 0x01)
                    Return (0x01)
                }

                /* Buffer Field */

                If (CondRefOf (\AUXD.BFL0, Local0))
                {
                    ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.BFL0", 0x01)
                    Return (0x01)
                }

                Return (0x00)
            }

            Concatenate (Arg0, "-tst1", Arg0)
            /* Check absence of the auxiliary table Objects before Load */

            If (M001 (Concatenate (Arg0, ".before")))
            {
                Return (0x01)
            }

            /* Load auxiliary table */

            \DTM0.RFU3 = \DTM0.BUF3
            Load (\DTM0.RFU3, DDB0) /* \DTM1.TST1.DDB0 */
            If (CH03 (Arg0, Z175, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            /* Integer */

            If (CondRefOf (\AUXD.INT0, Local0))
            {
                M000 (Arg0, "int", Local0, C009)
            }
            Else
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.INT0", 0x00)
            }

            /* String */

            If (CondRefOf (\AUXD.STR0, Local0))
            {
                M000 (Arg0, "str", Local0, C00A)
            }
            Else
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.STR0", 0x00)
            }

            /* Buffer */

            If (CondRefOf (\AUXD.BUF0, Local0))
            {
                M000 (Arg0, "buf", Local0, C00B)
            }
            Else
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.BUF0", 0x00)
            }

            /* Package */

            If (Y286)
            {
                If (CondRefOf (\AUXD.PAC0, Local0))
                {
                    M000 (Arg0, "pac", Local0, C00C)
                }
                Else
                {
                    ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.PAC0", 0x00)
                }
            }

            /* Field Unit */

            If (CondRefOf (\AUXD.FLU0, Local0))
            {
                M000 (Arg0, "flu", Local0, C00D)
            }
            Else
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.FLU0", 0x00)
            }

            /* Device */

            If (CondRefOf (\AUXD.DEV0, Local0))
            {
                M000 (Arg0, "dev", Local0, C00E)
            }
            Else
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.DEV0", 0x00)
            }

            /* Event */

            If (CondRefOf (\AUXD.EVE0, Local0))
            {
                M000 (Arg0, "evt", Local0, C00F)
            }
            Else
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.EVE0", 0x00)
            }

            /* Method */

            If (CondRefOf (\AUXD.MMM0, Local0))
            {
                M000 (Arg0, "met", Local0, C010)
            }
            Else
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.MMM0", 0x00)
            }

            /* Mutex */

            If (CondRefOf (\AUXD.MTX0, Local0))
            {
                M000 (Arg0, "mtx", Local0, C011)
            }
            Else
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.MTX0", 0x00)
            }

            /* OpRegion */

            If (CondRefOf (\AUXD.OPR0, Local0))
            {
                M000 (Arg0, "opr", Local0, C012)
            }
            Else
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.OPR0", 0x00)
            }

            /* Power Resource */

            If (CondRefOf (\AUXD.PWR0, Local0))
            {
                M000 (Arg0, "pwr", Local0, C013)
            }
            Else
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.PWR0", 0x00)
            }

            /* Processor */

            If (CondRefOf (\AUXD.CPU0, Local0))
            {
                M000 (Arg0, "cpu", Local0, C014)
            }
            Else
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.CPU0", 0x00)
            }

            /* Thermal Zone */

            If (CondRefOf (\AUXD.TZN0, Local0))
            {
                M000 (Arg0, "cpu", Local0, C015)
            }
            Else
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.TZN0", 0x00)
            }

            /* Buffer Field */

            If (CondRefOf (\AUXD.BFL0, Local0))
            {
                M000 (Arg0, "bfl", Local0, C016)
            }
            Else
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, "\\AUXD.BFL0", 0x00)
            }

            Unload (DDB0)
            CH03 (Arg0, Z175, __LINE__, 0x00, 0x00)
            /* Check absence of the auxiliary table Objects after UnLoad */

            If (M001 (Concatenate (Arg0, ".after")))
            {
                Return (0x01)
            }

            Return (0x00)
        }

        /* Load/UnLoad processing can be done with the same table many times */

        Method (TST2, 1, NotSerialized)
        {
            Concatenate (Arg0, "tst2.", Arg0)
            Local0 = 0x05
            While (Local0)
            {
                If (TST1 (Concatenate (Arg0, Mid ("0123456789", Local0, 0x01))))
                {
                    Return (0x01)
                }

                Local0--
            }

            Return (0x00)
        }

        /* Exceptions when the parameter of the UnLoad operator */
        /* is not of DDBHandle type */
        Method (TST3, 1, Serialized)
        {
            Name (DDB0, 0x00)
            Name (DDB1, 0x00)
            Method (M000, 4, NotSerialized)
            {
                Concatenate (Arg0, "-m000.", Arg0)
                Concatenate (Arg0, Arg1, Arg0)
                Local0 = ObjectType (Arg2)
                If ((Arg3 != Local0))
                {
                    ERR (Arg0, Z175, __LINE__, 0x00, 0x00, Local0, Arg3)
                    Return (0x01)
                }

                Unload (DerefOf (Arg2))
                CH04 (Arg0, 0x00, 0x2F, Z175, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
                Return (0x00)
            }

            Concatenate (Arg0, "-tst3", Arg0)
            /* Load auxiliary table */

            \DTM0.RFU3 = \DTM0.BUF3
            Load (\DTM0.RFU3, DDB0) /* \DTM1.TST3.DDB0 */
            If (CH03 (Arg0, Z175, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            /* Uninitialized */

            If (0x00)
            {
                Local1 = 0x00
            }

            Local0 = ObjectType (Local1)
            If ((C008 != Local0))
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, Local0, C008)
            }
            Else
            {
                Unload (Local1)
                If (SLCK)
                {
                    CH04 (Arg0, 0x00, 0x2F, Z175, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
                }
                Else
                {
                    CH04 (Arg0, 0x00, 0x31, Z175, __LINE__, 0x00, 0x00) /* AE_AML_UNINITIALIZED_LOCAL */
                }
            }

            /* Integer */

            M000 (Arg0, "int", RefOf (\AUXD.INT0), C009)
            /* String */

            M000 (Arg0, "str", RefOf (\AUXD.STR0), C00A)
            /* Buffer */

            M000 (Arg0, "buf", RefOf (\AUXD.BUF0), C00B)
            /* Package */

            If (Y286)
            {
                M000 (Arg0, "pac", RefOf (\AUXD.PAC0), C00C)
            }

            Local0 = ObjectType (\AUXD.PAC0)
            If ((C00C != Local0))
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, Local0, C00C)
            }
            Else
            {
                Unload (\AUXD.PAC0)
                CH04 (Arg0, 0x00, 0x2F, Z175, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            }

            /* Field Unit */

            M000 (Arg0, "flu", RefOf (\AUXD.FLU0), C00D)
            /* Device */

            Local0 = ObjectType (\AUXD.DEV0)
            If ((C00E != Local0))
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, Local0, C00E)
            }
            Else
            {
                Unload (\AUXD.DEV0)
                CH04 (Arg0, 0x00, 0x2F, Z175, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            }

            /* Event */

            M000 (Arg0, "evt", RefOf (\AUXD.EVE0), C00F)
            /* Method */

            M000 (Arg0, "met", RefOf (\AUXD.MMM0), C010)
            /* Mutex */

            M000 (Arg0, "mtx", RefOf (\AUXD.MTX0), C011)
            /* OpRegion */

            M000 (Arg0, "opr", RefOf (\AUXD.OPR0), C012)
            /* Power Resource */

            M000 (Arg0, "pwr", RefOf (\AUXD.PWR0), C013)
            /* Processor */

            M000 (Arg0, "cpu", RefOf (\AUXD.CPU0), C014)
            /* Thermal Zone */

            Local0 = ObjectType (\AUXD.TZN0)
            If ((C015 != Local0))
            {
                ERR (Arg0, Z175, __LINE__, 0x00, 0x00, Local0, C015)
            }
            Else
            {
                Unload (\AUXD.TZN0)
                CH04 (Arg0, 0x00, 0x2F, Z175, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            }

            /* Buffer Field */

            M000 (Arg0, "bfl", RefOf (\AUXD.BFL0), C016)
            Unload (DDB0)
            CH03 (Arg0, Z175, __LINE__, 0x00, 0x00)
            Return (0x00)
        }

        /* Exceptions when UnLoad is executed with the same DDBHandle repeatedly */

        Method (TST4, 1, Serialized)
        {
            Name (DDB0, 0x00)
            Name (DDB1, 0x00)
            Concatenate (Arg0, "-tst4", Arg0)
            /* Load auxiliary table */

            \DTM0.RFU3 = \DTM0.BUF3
            Load (\DTM0.RFU3, DDB0) /* \DTM1.TST4.DDB0 */
            If (CH03 (Arg0, Z175, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            /* First Unload */

            Unload (DDB0)
            If (CH03 (Arg0, Z175, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local0 = 0x05
            While (Local0)
            {
                /* Any next */

                Unload (DDB0)
                CH04 (Arg0, 0x00, 0x1C, Z175, __LINE__, 0x05, Local0) /* AE_BAD_PARAMETER */
                Local0--
            }

            /* Second DDBHandle */

            \DTM0.RFU3 = \DTM0.BUF3
            Load (\DTM0.RFU3, DDB1) /* \DTM1.TST4.DDB1 */
            If (CH03 (Arg0, Z175, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local0 = 0x05
            While (Local0)
            {
                /* Any next */

                Unload (DDB0)
                CH04 (Arg0, 0x00, 0x1C, Z175, __LINE__, 0x05, Local0) /* AE_BAD_PARAMETER */
                Local0--
            }

            Unload (DDB1)
            If (CH03 (Arg0, Z175, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Return (0x00)
        }

        /* Exceptions when the operand of UnLoad operator is absent */

        Method (TST5, 1, Serialized)
        {
            Name (DDB0, 0x00)
            Method (M000, 0, NotSerialized)
            {
                Return (0x00)
            }

            Method (M001, 0, NotSerialized)
            {
                Return (DDB0) /* \DTM1.TST5.DDB0 */
            }

            Concatenate (Arg0, "-tst5", Arg0)
            /* Load auxiliary table */

            \DTM0.RFU3 = \DTM0.BUF3
            Load (\DTM0.RFU3, DDB0) /* \DTM1.TST5.DDB0 */
            If (CH03 (Arg0, Z175, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            /* Device */

            Unload (DerefOf (RefOf (\AUXD.DEV0)))
            CH04 (Arg0, 0x00, 0x3E, Z175, __LINE__, 0x00, 0x00) /* AE_AML_NO_RETURN_VALUE */
            /* Thermal Zone */

            Unload (DerefOf (RefOf (\AUXD.TZN0)))
            CH04 (Arg0, 0x00, 0x3E, Z175, __LINE__, 0x00, 0x00) /* AE_AML_NO_RETURN_VALUE */
            /* Method execution */

            CopyObject (M000 (), M001) /* \DTM1.TST5.M001 */
            Unload (M001 ())
            If (SLCK)
            {
                CH04 (Arg0, 0x00, 0x2F, Z175, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            }
            Else
            {
                CH04 (Arg0, 0x00, 0x2F, Z175, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            }

            Unload (DDB0)
            If (CH03 (Arg0, Z175, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Return (0x00)
        }
    }

    Method (TUL0, 0, Serialized)
    {
        CH03 (__METHOD__, Z175, __LINE__, 0x00, 0x00)
        /* Different Sources to specify DDBHandle for UnLoad. */
        /* Most of them (Named Object, LocalX, ArgX, Derefof) */
        /* are checked in load.asl */
        /* DDBHandle returned by Method call */
        SRMT ("TUL0.tst0")
        \DTM1.TST0 (__METHOD__)
        CH03 (__METHOD__, Z175, __LINE__, 0x00, 0x00)
        /* All namespace objects created as a result of the corresponding */
        /* Load operation are absent in the namespace after UnLoad */
        SRMT ("TUL0.tst1")
        \DTM1.TST1 (__METHOD__)
        CH03 (__METHOD__, Z175, __LINE__, 0x00, 0x00)
        /* Load/UnLoad processing can be done with the same table many times */

        SRMT ("TUL0.tst2")
        \DTM1.TST2 (__METHOD__)
        CH03 (__METHOD__, Z175, __LINE__, 0x00, 0x00)
    }

    /* Exceptional conditions */

    Method (TUL1, 0, Serialized)
    {
        /* Exceptions when the parameter of the UnLoad operator */
        /* is not of DDBHandle type */
        SRMT ("TUL1.tst3")
        \DTM1.TST3 (__METHOD__)
        /* Exceptions when UnLoad is executed with the same DDBHandle repeatedly */

        SRMT ("TUL1.tst4")
        If (Y292)
        {
            \DTM1.TST4 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }

        /* Exceptions when the operand of UnLoad operator is absent */

        SRMT ("TUL1.tst5")
        \DTM1.TST5 (__METHOD__)
    }
