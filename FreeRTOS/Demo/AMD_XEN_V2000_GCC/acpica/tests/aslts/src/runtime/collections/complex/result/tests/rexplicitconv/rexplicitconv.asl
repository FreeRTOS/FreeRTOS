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
     * Check Result Object processing on optional storing
     * in the explicit conversion operators
     */
    Name (Z126, 0x7E)
    /* m693(<store op>, <exc. conditions>, */
    /*      <Target scale>, <Result scale>, <kind of Source-Target pair>) */
    Method (M693, 5, Serialized)
    {
        Name (TS, "m693")
        /*
         - choose a type of the Object to store into:
         = Uninitialized
         = Integer
         = String
         = Buffer
         = Package
         ...
         - choose a value of the Object to store into
         - choose kind of the Object to store into:
         = Named Object
         = Method LocalX Object
         - determine the destination Object to store into: it should exist
         and be initialized with the chosen value (Dst0)
         - choose a way to obtain some result object (Expr ~ Result Object
         returned by any Explicit conversion Operator (Op)):
         = ToInteger
         = ToBCD
         = FromBCD
         = ToString
         = ToHexString
         = ToDecimalString
         = ToBuffer
         - choose storing expression:
         = Store(Op(Src0, ...), Dst0)
         = CopyObject(Op(Src0, ...), Dst0)
         = Op(Src0, ..., Dst0)
         - the type of the result Object depend on the Operator
         - choose specific source objects to obtain the result Object of
         the specified type: it should exist and be initialized (Src0, ...)
         - choose a benchmark value according to a storing expression,
         chosen source objects, the value of the target object and
         relevant result conversion rule (if any) - Bval
         - check that the destination Object Dst0 is properly initialized
         - perform storing expression:
         Store(Expr(Src0, ...), Dst0)
         CopyObject(Expr(Src0, ...), Dst0)
         Op(Expr(Src0, ...), Dst0)
         - check that the benchmark value Bval is equal to the updated
         destination Object Dst0:
         - check that the source objects are not updated:
         - update the destination Object again and check that the source
         objects are not updated
         */
        /* Object-initializers are used either with Source or Target */
        /* (names ended by 0 and 1 respectively) */
        /* Integer */
        Name (INT0, 0xFEDCBA9876543210)
        Name (INT1, 0xFEDCBA9876543211)
        /* String */

        Name (STR0, "source string")
        Name (STR1, "target string")
        /* Buffer */

        Name (BUF0, Buffer (0x09)
        {
            /* 0000 */  0x09, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02,  // ........
            /* 0008 */  0x01                                             // .
        })
        Name (BUF1, Buffer (0x11)
        {
             0xC3                                             // .
        })
        /* Base of Buffer Fields */

        Name (BUFZ, Buffer (0x14){})
        Name (PAC1, Package (0x01)
        {
            "target package"
        })
        /* Device */

        Device (DEV1)
        {
            Name (S000, "DEV1")
        }

        /* Event */

        Event (EVE1)
        /* Method */

        Name (MM01, "ff1Y")  /* Value, returned from MMMY */
        Name (MMM1, 0x00)   /* Method as Target Object */
        Method (MMMY, 0, NotSerialized)
        {
            Return (MM01) /* \M693.MM01 */
        }

        /* Mutex */

        Mutex (MTX1, 0x00)
        If (Y361)
        {
            /* Operation Region */

            OperationRegion (OPR0, SystemMemory, 0x00, 0x14)
            OperationRegion (OPR1, SystemMemory, 0x00, 0x14)
        }

        /* Power Resource */

        PowerResource (PWR1, 0x00, 0x0000)
        {
            Name (S000, "PWR1")
        }

        /* Processor */

        Processor (CPU1, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (S000, "CPU1")
        }

        /* Thermal Zone */

        ThermalZone (TZN1)
        {
            Name (S000, "TZN1")
        }

        /* Reference */

        Name (REF0, Package (0x01){})
        Name (REF1, Package (0x01){})
        /* Data to gather statistics */

        Name (STCS, 0x00)
        Name (INDM, 0xFF)
        Name (PAC2, Package (0x01){})
        Name (IND2, 0x00)
        Name (PAC3, Package (0x01){})
        Name (IND3, 0x00)
        Name (PAC4, Package (0x03)
        {
            "Store",
            "Copyobject",
            "Optional"
        })
        Name (TERR, "-test error")
        /* Update statistics */
        /* m000(<type>, <shift>, <low>, <up>) */
        Method (M000, 4, NotSerialized)
        {
            If ((Arg0 == 0x02))
            {
                If ((IND2 < INDM))
                {
                    Store (((Arg3 * Arg1) + Arg2), PAC2 [IND2])
                    IND2++
                }
            }
            ElseIf ((Arg0 == 0x03))
            {
                If ((IND3 < INDM))
                {
                    Store (((Arg3 * Arg1) + Arg2), PAC3 [IND3])
                    IND3++
                }
            }
        }

        /* Initialize statistics */

        Method (M001, 0, NotSerialized)
        {
            If (STCS)
            {
                PAC2 = Package (0xFF){}
                IND2 = 0x00
                PAC3 = Package (0xFF){}
                IND3 = 0x00
            }
        }

        /* Output statistics */

        Method (M002, 1, Serialized)
        {
            Name (LPN0, 0x00)
            Name (LPC0, 0x00)
            If (STCS)
            {
                Debug = Arg0
                If (IND2)
                {
                    Debug = "Run-time exceptions:"
                    Debug = IND2 /* \M693.IND2 */
                    Debug = "Types:"
                    LPN0 = IND2 /* \M693.IND2 */
                    LPC0 = 0x00
                    While (LPN0)
                    {
                        Debug = DerefOf (PAC2 [LPC0])
                        LPN0--
                        LPC0++
                    }
                }

                If (IND3)
                {
                    Debug = "Type mismatch:"
                    Debug = IND3 /* \M693.IND3 */
                    LPN0 = IND3 /* \M693.IND3 */
                    LPC0 = 0x00
                    While (LPN0)
                    {
                        Debug = DerefOf (PAC3 [LPC0])
                        LPN0--
                        LPC0++
                    }
                }
            }
        }

        /* Prepare Target of specified type */

        Method (M003, 4, Serialized)
        {
            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                                /* Only check */
                }
                Case (0x01)
                {
                    CopyObject (DerefOf (Arg3), INT1) /* \M693.INT1 */
                    CopyObject (INT1, Arg2)
                }
                Case (0x02)
                {
                    CopyObject (DerefOf (Arg3), STR1) /* \M693.STR1 */
                    CopyObject (STR1, Arg2)
                }
                Case (0x03)
                {
                    CopyObject (DerefOf (Arg3), BUF1) /* \M693.BUF1 */
                    Local0 = SizeOf (BUF1)
                    If ((Local0 != 0x11))
                    {
                        ERR (Concatenate (Arg0, TERR), Z126, __LINE__, 0x00, 0x00, Local0, 0x11)
                        Return (0x01)
                    }

                    CopyObject (BUF1, Arg2)
                }
                Case (0x04)
                {
                    CopyObject (DerefOf (Arg3), PAC1) /* \M693.PAC1 */
                    CopyObject (PAC1, Arg2)
                }
                Case (0x05)
                {
                                /* Check only */
                }
                Case (0x06)
                {
                    CopyObject (DEV1, Arg2)
                }
                Case (0x07)
                {
                    CopyObject (EVE1, Arg2)
                }
                Case (0x08)
                {
                    CopyObject (DerefOf (RefOf (MMMY)), MMM1) /* \M693.MMM1 */
                    CopyObject (DerefOf (RefOf (MMM1)), Arg2)
                }
                Case (0x09)
                {
                    CopyObject (MTX1, Arg2)
                }
                Case (0x0A)
                {
                    CopyObject (OPR1, Arg2)
                }
                Case (0x0B)
                {
                    CopyObject (PWR1, Arg2)
                }
                Case (0x0C)
                {
                    CopyObject (CPU1, Arg2)
                }
                Case (0x0D)
                {
                    CopyObject (TZN1, Arg2)
                }
                Case (0x0E)
                {
                                /* Check only */
                }
                Case (0x11)
                {
                    CopyObject (RefOf (REF0), REF1) /* \M693.REF1 */
                    /*if (y522) { */

                    CopyObject (REF1, Arg2)
                                /*} else { */
                /*	CopyObject(DeRefof(REF1), arg2) */
                /*} */
                }
                /* Unexpected Target Type */

                Default
                {
                    ERR (Concatenate (Arg0, TERR), Z126, __LINE__, 0x00, 0x00, Arg1, 0x00)
                    Return (0x01)
                }

            }

            If (CH03 (Arg0, Z126, __LINE__, 0x00, 0x00))
            {
                /*Exception during preparing of Target Object */

                Return (0x01)
            }

            Local0 = ObjectType (Arg2)
            If ((Local0 != Arg1))
            {
                /* ObjectType of Target can not be set up */

                ERR (Arg0, Z126, __LINE__, 0x00, 0x00, Local0, Arg1)
                Return (0x01)
            }

            Return (0x00)
        }

        /* Prepare Source of specified type */

        Method (M004, 4, Serialized)
        {
            Switch (ToInteger (Arg1))
            {
                Case (0x01)
                {
                    CopyObject (DerefOf (Arg3), INT0) /* \M693.INT0 */
                    CopyObject (INT0, Arg2)
                }
                Case (0x02)
                {
                    CopyObject (DerefOf (Arg3), STR0) /* \M693.STR0 */
                    CopyObject (STR0, Arg2)
                }
                Case (0x03)
                {
                    If (Y136)
                    {
                        CopyObject (DerefOf (Arg3), BUF0) /* \M693.BUF0 */
                    }
                    Else
                    {
                        M687 (DerefOf (Arg3), RefOf (BUF0))
                    }

                    CopyObject (BUF0, Arg2)
                }
                /* Unexpected Source Type */

                Default
                {
                    ERR (Concatenate (Arg0, TERR), Z126, __LINE__, 0x00, 0x00, Arg1, 0x00)
                    Return (0x01)
                }

            }

            If (CH03 (Arg0, Z126, __LINE__, 0x00, 0x00))
            {
                /* Exception during preparing of Source Object */

                Return (0x01)
            }

            Local0 = ObjectType (Arg2)
            If ((Local0 != Arg1))
            {
                /* ObjectType of Source can not be set up */

                ERR (Arg0, Z126, __LINE__, 0x00, 0x00, Local0, Arg1)
                Return (0x01)
            }

            Return (0x00)
        }

        /* Check Source Object type is not corrupted after storing, */
        /* for the computational data types verify its value against */
        /* the Object-initializer value */
        Method (M005, 4, Serialized)
        {
            Local0 = ObjectType (Arg2)
            If ((Local0 != Arg1))
            {
                /* ObjectType of Source object is corrupted */

                ERR (Arg0, Z126, __LINE__, 0x00, 0x00, Local0, Arg1)
                Return (0x01)
            }

            Switch (ToInteger (Arg1))
            {
                Case (0x01)
                {
                    Local0 = ObjectType (INT0)
                }
                Case (0x02)
                {
                    Local0 = ObjectType (STR0)
                }
                Case (0x03)
                {
                    Local0 = ObjectType (BUF0)
                }
                /* Unexpected Result Type */

                Default
                {
                    ERR (Arg0, Z126, __LINE__, 0x00, 0x00, Arg1, 0x00)
                    Return (0x01)
                }

            }

            If ((Local0 != Arg1))
            {
                /* Mismatch of Source Type against specified one */

                ERR (Arg0, Z126, __LINE__, 0x00, 0x00, Local0, Arg1)
                If (STCS)
                {
                    M000 (0x03, 0x01000000, Local0, Arg0)
                }

                Return (0x01)
            }
            Else
            {
                /* Check equality of the Source value to the Object-initializer one */

                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        If ((INT0 != DerefOf (Arg3)))
                        {
                            ERR (Arg0, Z126, __LINE__, 0x00, 0x00, INT0, DerefOf (Arg3))
                            Return (0x01)
                        }

                        If ((DerefOf (Arg2) != INT0))
                        {
                            ERR (Arg0, Z126, __LINE__, 0x00, 0x00, DerefOf (Arg2), INT0)
                            Return (0x01)
                        }
                    }
                    Case (0x02)
                    {
                        If ((STR0 != DerefOf (Arg3)))
                        {
                            ERR (Arg0, Z126, __LINE__, 0x00, 0x00, STR0, DerefOf (Arg3))
                            Return (0x01)
                        }

                        If ((DerefOf (Arg2) != STR0))
                        {
                            ERR (Arg0, Z126, __LINE__, 0x00, 0x00, DerefOf (Arg2), STR0)
                            Return (0x01)
                        }
                    }
                    Case (0x03)
                    {
                        If ((BUF0 != DerefOf (Arg3)))
                        {
                            ERR (Arg0, Z126, __LINE__, 0x00, 0x00, BUF0, DerefOf (Arg3))
                            Return (0x01)
                        }

                        If ((DerefOf (Arg2) != BUF0))
                        {
                            ERR (Arg0, Z126, __LINE__, 0x00, 0x00, DerefOf (Arg2), BUF0)
                            Return (0x01)
                        }
                    }

                }
            }

            Return (0x00)
        }

        /* Check Target Object to have the expected type and value */
        /* m006(<msg>, <ref to target>, <target type>, <source type>, */
        /*      <op>, <target save type>, <test data package>) */
        Method (M006, 7, Serialized)
        {
            Name (MMM2, 0x00) /* The auxiliary Object to invoke Method */
            Local2 = ObjectType (Arg1)
            If ((Local2 != Arg2))
            {
                If (STCS)
                {
                    M000 (0x03, 0x00010000, Arg2, Local2)
                }
            }

            If (M686 (Arg5, Arg2, Arg3))
            {
                /* Target must save type */

                If ((Local2 != Arg2))
                {
                    /* Types mismatch Target/Target on storing */

                    If ((Arg2 == C016))
                    {
                        If (X170)
                        {
                            ERR (Arg0, Z126, __LINE__, 0x00, 0x00, Local2, Arg2)
                        }
                    }
                    Else
                    {
                        ERR (Arg0, Z126, __LINE__, 0x00, 0x00, Local2, Arg2)
                    }

                    If (STCS)
                    {
                        M000 (0x03, 0x0100, Arg2, Local2)
                    }

                    Return (0x01)
                }
            }
            ElseIf            /* Target must accept type of the Result Object */

 ((Local2 != Arg3))
            {
                If ((M684 (Arg3) != 0x01))
                {
                    /* Types mismatch Result/Target on storing */

                    ERR (Arg0, Z126, __LINE__, 0x00, 0x00, Local2, Arg3)
                    Return (0x01)
                }
                ElseIf ((Local2 != 0x03))
                {
                    /* Types mismatch Result/Target on storing */
                    /* Test fixed type Objects are converted to Buffer */
                    ERR (Arg0, Z126, __LINE__, 0x00, 0x00, Local2, 0x03)
                    Return (0x01)
                }

                If (STCS)
                {
                    M000 (0x03, 0x0100, Arg3, Local2)
                }
            }

            /* Retrieve the benchmark value */

            If (M686 (Arg5, Arg2, Arg3))
            {
                /* Save type of Target */
                /* Retrieve the benchmark value */
                Local7 = DerefOf (DerefOf (Arg6 [0x04]) [Arg2])
            }
            Else
            {
                Local7 = DerefOf (Arg6 [0x03])
            }

            If ((DerefOf (Arg1) != Local7))
            {
                If (((Arg2 == C00B) && (Arg3 == C00B)))
                {
                    If (X194)
                    {
                        ERR (Arg0, Z126, __LINE__, 0x00, 0x00, DerefOf (Arg1), Local7)
                    }
                }
                Else
                {
                    ERR (Arg0, Z126, __LINE__, 0x00, 0x00, DerefOf (Arg1), Local7)
                }

                Return (0x01)
            }

            Return (0x00)
        }

        /* Check processing of an Source Named Object of the specified type */
        /* on immediate storing to a Target Named Object of the specified type */
        /* m008(<msg>, <aux>, <target type>, <source type>, */
        /*      <op>, <exc. condition>, <test data package>) */
        Method (M008, 7, Serialized)
        {
            /* Source Named Object */

            Name (SRC0, 0x00)
            /* Target Named Object */

            Name (DST0, 0x00)
            /* Retrieve index of the verified Explicit conversion Operator */

            Local6 = DerefOf (Arg6 [0x00])
            Concatenate (Arg0, "-", Arg0)
            Concatenate (Arg0, Concatenate (Mid (Local6, 0x00, 0x02), Concatenate (Mid (Arg4, 0x00,
                0x02), Concatenate (Mid (Arg2, 0x00, 0x02), Mid (Arg3, 0x00, 0x02)
                ))), Arg0)
            If (STCS)
            {
                Debug = Arg0
            }

            /* Prepare Source of specified type and value */

            Store (Arg6 [0x01], Local7)
            If (M004 (Concatenate (Arg0, "-m004"), Arg3, RefOf (SRC0), Local7))
            {
                /* Source Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z126, __LINE__, 0x00, 0x00, Arg3, 0x00)
                Return (0x01)
            }

            /* Prepare Target of specified type */

            Store (DerefOf (Arg6 [0x02]) [Arg2], Local7)
            If ((Arg2 == 0x05))
            {
                /* Field Unit Target */

                Field (OPR0, ByteAcc, NoLock, Preserve)
                {
                    FLUX,   69,
                    FLU1,   69
                }

                Local1 = RefOf (FLU1)
            }
            ElseIf ((Arg2 == 0x0E))
            {
                /* Buffer Field Target */

                CreateField (BUFZ, 0x50, 0x45, BFL1)
                Local1 = RefOf (BFL1)
            }
            Else
            {
                Local1 = RefOf (DST0)
            }

            If (M003 (Concatenate (Arg0, "-m003"), Arg2, Local1, Local7))
            {
                /* Target Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z126, __LINE__, 0x00, 0x00, Arg2, 0x00)
                Return (0x01)
            }

            /* Use a Source Object to immediately store into the Target */

            If ((Arg2 == 0x05))
            {
                /* Field Unit Target */

                If ((Arg4 == 0x00))
                {
                    /* Store */

                    Switch (ToInteger (Local6))
                    {
                        Case (0x00)
                        {
                            FLU1 = ToInteger (SRC0)
                        }
                        Case (0x01)
                        {
                            FLU1 = ToBCD (SRC0)
                        }
                        Case (0x02)
                        {
                            FLU1 = FromBCD (SRC0)
                        }
                        Case (0x03)
                        {
                            FLU1 = ToString (SRC0, Ones)
                        }
                        Case (0x04)
                        {
                            FLU1 = ToHexString (SRC0)
                        }
                        Case (0x05)
                        {
                            FLU1 = ToDecimalString (SRC0)
                        }
                        Case (0x06)
                        {
                            FLU1 = ToBuffer (SRC0)
                        }

                    }
                }
                ElseIf ((Arg4 == 0x01))
                {
                    /* CopyObject */

                    Switch (ToInteger (Local6))
                    {
                        Case (0x00)
                        {
                            CopyObject (ToInteger (SRC0), FLU1) /* \M693.M008.FLU1 */
                        }
                        Case (0x01)
                        {
                            CopyObject (ToBCD (SRC0), FLU1) /* \M693.M008.FLU1 */
                        }
                        Case (0x02)
                        {
                            CopyObject (FromBCD (SRC0), FLU1) /* \M693.M008.FLU1 */
                        }
                        Case (0x03)
                        {
                            CopyObject (ToString (SRC0, Ones), FLU1) /* \M693.M008.FLU1 */
                        }
                        Case (0x04)
                        {
                            CopyObject (ToHexString (SRC0), FLU1) /* \M693.M008.FLU1 */
                        }
                        Case (0x05)
                        {
                            CopyObject (ToDecimalString (SRC0), FLU1) /* \M693.M008.FLU1 */
                        }
                        Case (0x06)
                        {
                            CopyObject (ToBuffer (SRC0), FLU1) /* \M693.M008.FLU1 */
                        }

                    }
                }
                ElseIf ((Arg4 == 0x02))
                {
                    /* Optional storing */

                    Switch (ToInteger (Local6))
                    {
                        Case (0x00)
                        {
                            ToInteger (SRC0, FLU1) /* \M693.M008.FLU1 */
                        }
                        Case (0x01)
                        {
                            ToBCD (SRC0, FLU1) /* \M693.M008.FLU1 */
                        }
                        Case (0x02)
                        {
                            FromBCD (SRC0, FLU1) /* \M693.M008.FLU1 */
                        }
                        Case (0x03)
                        {
                            ToString (SRC0, Ones, FLU1) /* \M693.M008.FLU1 */
                        }
                        Case (0x04)
                        {
                            ToHexString (SRC0, FLU1) /* \M693.M008.FLU1 */
                        }
                        Case (0x05)
                        {
                            ToDecimalString (SRC0, FLU1) /* \M693.M008.FLU1 */
                        }
                        Case (0x06)
                        {
                            ToBuffer (SRC0, FLU1) /* \M693.M008.FLU1 */
                        }

                    }
                }
                Else
                {
                    /* Unexpected Kind of Op (0 - Store, ...) */

                    ERR (Concatenate (Arg0, TERR), Z126, __LINE__, 0x00, 0x00, Arg4, 0x00)
                    Return (0x01)
                }
            }
            ElseIf ((Arg2 == 0x0E))
            {
                /* Buffer Field Target */

                If ((Arg4 == 0x00))
                {
                    /* Store */

                    Switch (ToInteger (Local6))
                    {
                        Case (0x00)
                        {
                            BFL1 = ToInteger (SRC0)
                        }
                        Case (0x01)
                        {
                            BFL1 = ToBCD (SRC0)
                        }
                        Case (0x02)
                        {
                            BFL1 = FromBCD (SRC0)
                        }
                        Case (0x03)
                        {
                            BFL1 = ToString (SRC0, Ones)
                        }
                        Case (0x04)
                        {
                            BFL1 = ToHexString (SRC0)
                        }
                        Case (0x05)
                        {
                            BFL1 = ToDecimalString (SRC0)
                        }
                        Case (0x06)
                        {
                            BFL1 = ToBuffer (SRC0)
                        }

                    }
                }
                ElseIf ((Arg4 == 0x01))
                {
                    /* CopyObject */

                    Switch (ToInteger (Local6))
                    {
                        Case (0x00)
                        {
                            CopyObject (ToInteger (SRC0), BFL1) /* \M693.M008.BFL1 */
                        }
                        Case (0x01)
                        {
                            CopyObject (ToBCD (SRC0), BFL1) /* \M693.M008.BFL1 */
                        }
                        Case (0x02)
                        {
                            CopyObject (FromBCD (SRC0), BFL1) /* \M693.M008.BFL1 */
                        }
                        Case (0x03)
                        {
                            CopyObject (ToString (SRC0, Ones), BFL1) /* \M693.M008.BFL1 */
                        }
                        Case (0x04)
                        {
                            CopyObject (ToHexString (SRC0), BFL1) /* \M693.M008.BFL1 */
                        }
                        Case (0x05)
                        {
                            CopyObject (ToDecimalString (SRC0), BFL1) /* \M693.M008.BFL1 */
                        }
                        Case (0x06)
                        {
                            CopyObject (ToBuffer (SRC0), BFL1) /* \M693.M008.BFL1 */
                        }

                    }
                }
                ElseIf ((Arg4 == 0x02))
                {
                    /* Optional storing */

                    Switch (ToInteger (Local6))
                    {
                        Case (0x00)
                        {
                            ToInteger (SRC0, BFL1) /* \M693.M008.BFL1 */
                        }
                        Case (0x01)
                        {
                            ToBCD (SRC0, BFL1) /* \M693.M008.BFL1 */
                        }
                        Case (0x02)
                        {
                            FromBCD (SRC0, BFL1) /* \M693.M008.BFL1 */
                        }
                        Case (0x03)
                        {
                            ToString (SRC0, Ones, BFL1) /* \M693.M008.BFL1 */
                        }
                        Case (0x04)
                        {
                            ToHexString (SRC0, BFL1) /* \M693.M008.BFL1 */
                        }
                        Case (0x05)
                        {
                            ToDecimalString (SRC0, BFL1) /* \M693.M008.BFL1 */
                        }
                        Case (0x06)
                        {
                            ToBuffer (SRC0, BFL1) /* \M693.M008.BFL1 */
                        }

                    }
                }
                Else
                {
                    /* Unexpected Kind of Op (0 - Store, ...) */

                    ERR (Concatenate (Arg0, TERR), Z126, __LINE__, 0x00, 0x00, Arg4, 0x00)
                    Return (0x01)
                }
            }
            ElseIf ((Arg4 == 0x00))
            {
                /* Store */

                Switch (ToInteger (Local6))
                {
                    Case (0x00)
                    {
                        DST0 = ToInteger (SRC0)
                    }
                    Case (0x01)
                    {
                        DST0 = ToBCD (SRC0)
                    }
                    Case (0x02)
                    {
                        DST0 = FromBCD (SRC0)
                    }
                    Case (0x03)
                    {
                        DST0 = ToString (SRC0, Ones)
                    }
                    Case (0x04)
                    {
                        DST0 = ToHexString (SRC0)
                    }
                    Case (0x05)
                    {
                        DST0 = ToDecimalString (SRC0)
                    }
                    Case (0x06)
                    {
                        DST0 = ToBuffer (SRC0)
                    }

                }
            }
            ElseIf ((Arg4 == 0x01))
            {
                /* CopyObject */

                Switch (ToInteger (Local6))
                {
                    Case (0x00)
                    {
                        CopyObject (ToInteger (SRC0), DST0) /* \M693.M008.DST0 */
                    }
                    Case (0x01)
                    {
                        CopyObject (ToBCD (SRC0), DST0) /* \M693.M008.DST0 */
                    }
                    Case (0x02)
                    {
                        CopyObject (FromBCD (SRC0), DST0) /* \M693.M008.DST0 */
                    }
                    Case (0x03)
                    {
                        CopyObject (ToString (SRC0, Ones), DST0) /* \M693.M008.DST0 */
                    }
                    Case (0x04)
                    {
                        CopyObject (ToHexString (SRC0), DST0) /* \M693.M008.DST0 */
                    }
                    Case (0x05)
                    {
                        CopyObject (ToDecimalString (SRC0), DST0) /* \M693.M008.DST0 */
                    }
                    Case (0x06)
                    {
                        CopyObject (ToBuffer (SRC0), DST0) /* \M693.M008.DST0 */
                    }

                }
            }
            ElseIf ((Arg4 == 0x02))
            {
                /* Optional storing */

                Switch (ToInteger (Local6))
                {
                    Case (0x00)
                    {
                        ToInteger (SRC0, DST0) /* \M693.M008.DST0 */
                    }
                    Case (0x01)
                    {
                        ToBCD (SRC0, DST0) /* \M693.M008.DST0 */
                    }
                    Case (0x02)
                    {
                        FromBCD (SRC0, DST0) /* \M693.M008.DST0 */
                    }
                    Case (0x03)
                    {
                        ToString (SRC0, Ones, DST0) /* \M693.M008.DST0 */
                    }
                    Case (0x04)
                    {
                        ToHexString (SRC0, DST0) /* \M693.M008.DST0 */
                    }
                    Case (0x05)
                    {
                        ToDecimalString (SRC0, DST0) /* \M693.M008.DST0 */
                    }
                    Case (0x06)
                    {
                        ToBuffer (SRC0, DST0) /* \M693.M008.DST0 */
                    }

                }
            }
            Else
            {
                /* Unexpected Kind of Op (0 - Store, ...) */

                ERR (Concatenate (Arg0, TERR), Z126, __LINE__, 0x00, 0x00, Arg4, 0x00)
                Return (0x01)
            }

            If (Arg5)
            {
                /* Exception is expected */

                If (!CH06 (Arg0, 0x1A, 0xFF))
                {
                    If (STCS)
                    {
                        M000 (0x02, 0x0100, Arg2, Arg3)
                    }
                }
            }
            ElseIf (CH03 (Arg0, Z126, __LINE__, 0x00, Arg2))
            {
                /* Storing caused unexpected exception */

                If (STCS)
                {
                    M000 (0x02, 0x0100, Arg2, Arg3)
                }
            }
            Else
            {
                /* Check Target Object to have the expected type and value */
                /* Target accept type on storing to Named of Store operator is 0 */
                If ((Arg4 == 0x00))
                {
                    Local0 = 0x00
                }
                Else
                {
                    Local0 = 0x02
                }

                M006 (Concatenate (Arg0, "-m006"), Local1, Arg2, Arg3, Arg4, Local0, Arg6)
            }

            /* Check Source Object type is not corrupted after storing */

            Store (Arg6 [0x01], Local7)
            If (M005 (Concatenate (Arg0, "-m005"), Arg3, RefOf (SRC0), Local7))
            {
                If (STCS)
                {
                    Debug = "m008, Source Object has been corrupted during storing"
                }
            }

            Return (0x00)
        }

        /* Check processing of an Source Named Object of the specified type */
        /* on immediate storing to a Target LocalX Object of the specified type */
        /* m009(<msg>, <aux>, <target type>, <source type>, */
        /*      <op>, <exc. condition>, <test data package>) */
        Method (M009, 7, Serialized)
        {
            /* Source Named Object */

            Name (SRC0, 0x00)
            /* Target Named Object: Local4 */
            /* Retrieve index of the verified Explicit conversion Operator */
            Local6 = DerefOf (Arg6 [0x00])
            Concatenate (Arg0, "-", Arg0)
            Concatenate (Arg0, Concatenate (Mid (Local6, 0x00, 0x02), Concatenate (Mid (Arg4, 0x00,
                0x02), Concatenate (Mid (Arg2, 0x00, 0x02), Mid (Arg3, 0x00, 0x02)
                ))), Arg0)
            If (STCS)
            {
                Debug = Arg0
            }

            /* Prepare Source of specified type and value */

            Store (Arg6 [0x01], Local7)
            If (M004 (Concatenate (Arg0, "-m004"), Arg3, RefOf (SRC0), Local7))
            {
                /* Source Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z126, __LINE__, 0x00, 0x00, Arg3, 0x00)
                Return (0x01)
            }

            /* Prepare Target of specified type */

            Store (DerefOf (Arg6 [0x02]) [Arg2], Local7)
            If (M003 (Concatenate (Arg0, "-m003"), Arg2, RefOf (Local4), Local7))
            {
                /* Target Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z126, __LINE__, 0x00, 0x00, Arg2, 0x00)
                Return (0x01)
            }

            /* Use a Source Object to immediately store into the Target */

            If ((Arg4 == 0x00))
            {
                /* Store */

                Switch (ToInteger (Local6))
                {
                    Case (0x00)
                    {
                        Local4 = ToInteger (SRC0)
                    }
                    Case (0x01)
                    {
                        Local4 = ToBCD (SRC0)
                    }
                    Case (0x02)
                    {
                        Local4 = FromBCD (SRC0)
                    }
                    Case (0x03)
                    {
                        Local4 = ToString (SRC0, Ones)
                    }
                    Case (0x04)
                    {
                        Local4 = ToHexString (SRC0)
                    }
                    Case (0x05)
                    {
                        Local4 = ToDecimalString (SRC0)
                    }
                    Case (0x06)
                    {
                        Local4 = ToBuffer (SRC0)
                    }

                }
            }
            ElseIf ((Arg4 == 0x01))
            {
                /* CopyObject */

                Switch (ToInteger (Local6))
                {
                    Case (0x00)
                    {
                        CopyObject (ToInteger (SRC0), Local4)
                    }
                    Case (0x01)
                    {
                        CopyObject (ToBCD (SRC0), Local4)
                    }
                    Case (0x02)
                    {
                        CopyObject (FromBCD (SRC0), Local4)
                    }
                    Case (0x03)
                    {
                        CopyObject (ToString (SRC0, Ones), Local4)
                    }
                    Case (0x04)
                    {
                        CopyObject (ToHexString (SRC0), Local4)
                    }
                    Case (0x05)
                    {
                        CopyObject (ToDecimalString (SRC0), Local4)
                    }
                    Case (0x06)
                    {
                        CopyObject (ToBuffer (SRC0), Local4)
                    }

                }
            }
            ElseIf ((Arg4 == 0x02))
            {
                /* Optional storing */

                Switch (ToInteger (Local6))
                {
                    Case (0x00)
                    {
                        ToInteger (SRC0, Local4)
                    }
                    Case (0x01)
                    {
                        ToBCD (SRC0, Local4)
                    }
                    Case (0x02)
                    {
                        FromBCD (SRC0, Local4)
                    }
                    Case (0x03)
                    {
                        ToString (SRC0, Ones, Local4)
                    }
                    Case (0x04)
                    {
                        ToHexString (SRC0, Local4)
                    }
                    Case (0x05)
                    {
                        ToDecimalString (SRC0, Local4)
                    }
                    Case (0x06)
                    {
                        ToBuffer (SRC0, Local4)
                    }

                }
            }
            Else
            {
                /* Unexpected Kind of Op (0 - Store, ...) */

                ERR (Concatenate (Arg0, TERR), Z126, __LINE__, 0x00, 0x00, Arg4, 0x00)
                Return (0x01)
            }

            If (Arg5)
            {
                /* Exception is expected */

                If (!CH06 (Arg0, 0x1F, 0xFF))
                {
                    If (STCS)
                    {
                        M000 (0x02, 0x0100, Arg2, Arg3)
                    }
                }
            }
            ElseIf (CH03 (Arg0, Z126, __LINE__, 0x00, Arg2))
            {
                /* Storing caused unexpected exception */

                If (STCS)
                {
                    M000 (0x02, 0x0100, Arg2, Arg3)
                }
            }
            Else
            {
                /* Check Target Object to have the expected type and value */
                /* Target accept type on storing to LocalX is 1 */
                Local0 = 0x01
                M006 (Concatenate (Arg0, "-m006"), RefOf (Local4), Arg2, Arg3, Arg4, Local0, Arg6)
            }

            /* Check Source Object type is not corrupted after storing */

            Store (Arg6 [0x01], Local7)
            If (M005 (Concatenate (Arg0, "-m005"), Arg3, RefOf (SRC0), Local7))
            {
                If (STCS)
                {
                    Debug = "m009, Source Object has been corrupted during storing"
                }
            }

            Return (0x00)
        }

        /* Test data packages */
        /* ToInteger */
        Name (P032, Package (0x11)
        {
            /* index of the Operator */

            0x00,
            /* SRC0 initial value */

            0xFEDCBA9876543210,
            /* Target Objects initial values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA9876543211,
                "target string",
                Buffer (0x11)
                {
                     0xC3                                             // .
                },

                Package (0x01)
                {
                    "target package"
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00
            },

            /* Benchmark Result object value */

            0xFEDCBA9876543210,
            /* Benchmark Result object converted to Target type values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA9876543210,
                "76543210",
                Buffer (0x11)
                {
                     0x10, 0x32, 0x54, 0x76                           // .2Tv
                },

                0x00,
                Buffer (0x09)
                {
                     0x10, 0x32, 0x54, 0x76                           // .2Tv
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                     0x10, 0x32, 0x54, 0x76                           // .2Tv
                },

                0x00,
                0x00
            }
        })
        Name (P064, Package (0x11)
        {
            /* index of the Operator */

            0x00,
            /* SRC0 initial value */

            0xFEDCBA9876543210,
            /* Target Objects initial values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA9876543211,
                "target string",
                Buffer (0x11)
                {
                     0xC3                                             // .
                },

                Package (0x01)
                {
                    "target package"
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00
            },

            /* Benchmark Result object value */

            0xFEDCBA9876543210,
            /* Benchmark Result object converted to Target type values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA9876543210,
                "FEDCBA9876543210",
                Buffer (0x11)
                {
                     0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE   // .2Tv....
                },

                0x00,
                Buffer (0x09)
                {
                     0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE   // .2Tv....
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                     0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE   // .2Tv....
                },

                0x00,
                0x00
            }
        })
        /* ToBCD */

        Name (P132, Package (0x11)
        {
            /* index of the Operator */

            0x01,
            /* SRC0 initial value */

            0x055F2CC0,
            /* Target Objects initial values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA9876543211,
                "target string",
                Buffer (0x11)
                {
                     0xC3                                             // .
                },

                Package (0x01)
                {
                    "target package"
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00
            },

            /* Benchmark Result object value */

            0x90123456,
            /* Benchmark Result object converted to Target type values */

            Package (0x11)
            {
                0x00,
                0x90123456,
                "90123456",
                Buffer (0x11)
                {
                     0x56, 0x34, 0x12, 0x90                           // V4..
                },

                0x00,
                Buffer (0x09)
                {
                     0x56, 0x34, 0x12, 0x90                           // V4..
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                     0x56, 0x34, 0x12, 0x90                           // V4..
                },

                0x00,
                0x00
            }
        })
        Name (P164, Package (0x11)
        {
            /* index of the Operator */

            0x01,
            /* SRC0 initial value */

            0x000D76162EE9EC35,
            /* Target Objects initial values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA9876543211,
                "target string",
                Buffer (0x11)
                {
                     0xC3                                             // .
                },

                Package (0x01)
                {
                    "target package"
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00
            },

            /* Benchmark Result object value */

            0x3789012345678901,
            /* Benchmark Result object converted to Target type values */

            Package (0x11)
            {
                0x00,
                0x3789012345678901,
                "3789012345678901",
                Buffer (0x11)
                {
                     0x01, 0x89, 0x67, 0x45, 0x23, 0x01, 0x89, 0x37   // ..gE#..7
                },

                0x00,
                Buffer (0x09)
                {
                     0x01, 0x89, 0x67, 0x45, 0x23, 0x01, 0x89, 0x37   // ..gE#..7
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                     0x01, 0x89, 0x67, 0x45, 0x23, 0x01, 0x89, 0x37   // ..gE#..7
                },

                0x00,
                0x00
            }
        })
        /* FromBCD */

        Name (P232, Package (0x11)
        {
            /* index of the Operator */

            0x02,
            /* SRC0 initial value */

            0x90123456,
            /* Target Objects initial values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA9876543211,
                "target string",
                Buffer (0x11)
                {
                     0xC3                                             // .
                },

                Package (0x01)
                {
                    "target package"
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00
            },

            /* Benchmark Result object value */

            0x055F2CC0,
            /* Benchmark Result object converted to Target type values */

            Package (0x11)
            {
                0x00,
                0x055F2CC0,
                "055F2CC0",
                Buffer (0x11)
                {
                     0xC0, 0x2C, 0x5F, 0x05                           // .,_.
                },

                0x00,
                Buffer (0x09)
                {
                     0xC0, 0x2C, 0x5F, 0x05                           // .,_.
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                     0xC0, 0x2C, 0x5F, 0x05                           // .,_.
                },

                0x00,
                0x00
            }
        })
        Name (P264, Package (0x11)
        {
            /* index of the Operator */

            0x02,
            /* SRC0 initial value */

            0x3789012345678901,
            /* Target Objects initial values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA9876543211,
                "target string",
                Buffer (0x11)
                {
                     0xC3                                             // .
                },

                Package (0x01)
                {
                    "target package"
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00
            },

            /* Benchmark Result object value */

            0x000D76162EE9EC35,
            /* Benchmark Result object converted to Target type values */

            Package (0x11)
            {
                0x00,
                0x000D76162EE9EC35,
                "000D76162EE9EC35",
                Buffer (0x11)
                {
                     0x35, 0xEC, 0xE9, 0x2E, 0x16, 0x76, 0x0D         // 5....v.
                },

                0x00,
                Buffer (0x09)
                {
                     0x35, 0xEC, 0xE9, 0x2E, 0x16, 0x76, 0x0D         // 5....v.
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                     0x35, 0xEC, 0xE9, 0x2E, 0x16, 0x76, 0x0D         // 5....v.
                },

                0x00,
                0x00
            }
        })
        /* ToString */

        Name (P332, Package (0x11)
        {
            /* index of the Operator */

            0x03,
            /* SRC0 initial value */

            "fedcba98 string",
            /* Target Objects initial values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA9876543211,
                "target string",
                Buffer (0x11)
                {
                     0xC3                                             // .
                },

                Package (0x01)
                {
                    "target package"
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00
            },

            /* Benchmark Result object value */

            "fedcba98 string",
            /* Benchmark Result object converted to Target type values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA98,
                "fedcba98 string",
                Buffer (0x11)
                {
                    /* 0000 */  0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38,  // fedcba98
                    /* 0008 */  0x20, 0x73, 0x74, 0x72, 0x69, 0x6E, 0x67         //  string
                },

                0x00,
                Buffer (0x09)
                {
                     0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38   // fedcba98
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                     0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38   // fedcba98
                },

                0x00,
                0x00
            }
        })
        Name (P364, Package (0x11)
        {
            /* index of the Operator */

            0x03,
            /* SRC0 initial value */

            "fedcba9876543210 string",
            /* Target Objects initial values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA9876543211,
                "target string",
                Buffer (0x11)
                {
                     0xC3                                             // .
                },

                Package (0x01)
                {
                    "target package"
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00
            },

            /* Benchmark Result object value */

            "fedcba9876543210 string",
            /* Benchmark Result object converted to Target type values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA9876543210,
                "fedcba9876543210 string",
                Buffer (0x11)
                {
                    /* 0000 */  0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38,  // fedcba98
                    /* 0008 */  0x37, 0x36, 0x35, 0x34, 0x33, 0x32, 0x31, 0x30,  // 76543210
                    /* 0010 */  0x20                                             //
                },

                0x00,
                Buffer (0x09)
                {
                    /* 0000 */  0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38,  // fedcba98
                    /* 0008 */  0x17                                             // .
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                    /* 0000 */  0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38,  // fedcba98
                    /* 0008 */  0x17                                             // .
                },

                0x00,
                0x00
            }
        })
        /* ToHexString */

        Name (P432, Package (0x11)
        {
            /* index of the Operator */

            0x04,
            /* SRC0 initial value */

            "fedcba98 string",
            /* Target Objects initial values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA9876543211,
                "target string",
                Buffer (0x11)
                {
                     0xC3                                             // .
                },

                Package (0x01)
                {
                    "target package"
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00
            },

            /* Benchmark Result object value */

            "fedcba98 string",
            /* Benchmark Result object converted to Target type values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA98,
                "fedcba98 string",
                Buffer (0x11)
                {
                    /* 0000 */  0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38,  // fedcba98
                    /* 0008 */  0x20, 0x73, 0x74, 0x72, 0x69, 0x6E, 0x67         //  string
                },

                0x00,
                Buffer (0x09)
                {
                     0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38   // fedcba98
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                     0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38   // fedcba98
                },

                0x00,
                0x00
            }
        })
        Name (P464, Package (0x11)
        {
            /* index of the Operator */

            0x04,
            /* SRC0 initial value */

            "fedcba9876543210 string",
            /* Target Objects initial values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA9876543211,
                "target string",
                Buffer (0x11)
                {
                     0xC3                                             // .
                },

                Package (0x01)
                {
                    "target package"
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00
            },

            /* Benchmark Result object value */

            "fedcba9876543210 string",
            /* Benchmark Result object converted to Target type values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA9876543210,
                "fedcba9876543210 string",
                Buffer (0x11)
                {
                    /* 0000 */  0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38,  // fedcba98
                    /* 0008 */  0x37, 0x36, 0x35, 0x34, 0x33, 0x32, 0x31, 0x30,  // 76543210
                    /* 0010 */  0x20                                             //
                },

                0x00,
                Buffer (0x09)
                {
                    /* 0000 */  0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38,  // fedcba98
                    /* 0008 */  0x17                                             // .
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                    /* 0000 */  0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38,  // fedcba98
                    /* 0008 */  0x17                                             // .
                },

                0x00,
                0x00
            }
        })
        /* ToDecimalString */

        Name (P532, Package (0x11)
        {
            /* index of the Operator */

            0x05,
            /* SRC0 initial value */

            "fedcba98 string",
            /* Target Objects initial values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA9876543211,
                "target string",
                Buffer (0x11)
                {
                     0xC3                                             // .
                },

                Package (0x01)
                {
                    "target package"
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00
            },

            /* Benchmark Result object value */

            "fedcba98 string",
            /* Benchmark Result object converted to Target type values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA98,
                "fedcba98 string",
                Buffer (0x11)
                {
                    /* 0000 */  0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38,  // fedcba98
                    /* 0008 */  0x20, 0x73, 0x74, 0x72, 0x69, 0x6E, 0x67         //  string
                },

                0x00,
                Buffer (0x09)
                {
                     0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38   // fedcba98
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                     0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38   // fedcba98
                },

                0x00,
                0x00
            }
        })
        Name (P564, Package (0x11)
        {
            /* index of the Operator */

            0x05,
            /* SRC0 initial value */

            "fedcba9876543210 string",
            /* Target Objects initial values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA9876543211,
                "target string",
                Buffer (0x11)
                {
                     0xC3                                             // .
                },

                Package (0x01)
                {
                    "target package"
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00
            },

            /* Benchmark Result object value */

            "fedcba9876543210 string",
            /* Benchmark Result object converted to Target type values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA9876543210,
                "fedcba9876543210 string",
                Buffer (0x11)
                {
                    /* 0000 */  0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38,  // fedcba98
                    /* 0008 */  0x37, 0x36, 0x35, 0x34, 0x33, 0x32, 0x31, 0x30,  // 76543210
                    /* 0010 */  0x20                                             //
                },

                0x00,
                Buffer (0x09)
                {
                    /* 0000 */  0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38,  // fedcba98
                    /* 0008 */  0x17                                             // .
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                    /* 0000 */  0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38,  // fedcba98
                    /* 0008 */  0x17                                             // .
                },

                0x00,
                0x00
            }
        })
        /* ToBuffer */

        Name (P632, Package (0x11)
        {
            /* index of the Operator */

            0x06,
            /* SRC0 initial value */

            Buffer (0x07)
            {
                 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01         // .......
            },

            /* Target Objects initial values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA9876543211,
                "target string",
                Buffer (0x11)
                {
                     0xC3                                             // .
                },

                Package (0x01)
                {
                    "target package"
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00
            },

            /* Benchmark Result object value */

            Buffer (0x07)
            {
                 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01         // .......
            },

            /* Benchmark Result object converted to Target type values */

            Package (0x11)
            {
                0x00,
                0x04050607,
                "07 06 05 04 03 02 01",
                Buffer (0x11)
                {
                     0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01         // .......
                },

                0x00,
                Buffer (0x09)
                {
                     0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01         // .......
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                     0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01         // .......
                },

                0x00,
                0x00
            }
        })
        Name (P664, Package (0x11)
        {
            /* index of the Operator */

            0x06,
            /* SRC0 initial value */

            Buffer (0x07)
            {
                 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01         // .......
            },

            /* Target Objects initial values */

            Package (0x11)
            {
                0x00,
                0xFEDCBA9876543211,
                "target string",
                Buffer (0x11)
                {
                     0xC3                                             // .
                },

                Package (0x01)
                {
                    "target package"
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00
            },

            /* Benchmark Result object value */

            Buffer (0x07)
            {
                 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01         // .......
            },

            /* Benchmark Result object converted to Target type values */

            Package (0x11)
            {
                0x00,
                0x0001020304050607,
                "07 06 05 04 03 02 01",
                Buffer (0x11)
                {
                     0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01         // .......
                },

                0x00,
                Buffer (0x09)
                {
                     0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01         // .......
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                     0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01         // .......
                },

                0x00,
                0x00
            }
        })
        Name (P320, Package (0x07)
        {
            P032,
            P132,
            P232,
            P332,
            P432,
            P532,
            P632
        })
        Name (P640, Package (0x07)
        {
            P064,
            P164,
            P264,
            P364,
            P464,
            P564,
            P664
        })
        Name (SCL0, Buffer (0x07)
        {
             0x01, 0x01, 0x01, 0x02, 0x02, 0x02, 0x03         // .......
        })
        Name (LPN0, 0x11)
        Name (LPC0, 0x00)
        Name (LPN1, 0x00)
        Name (LPC1, 0x00)
        If ((Arg0 == 0x00))
        {
            Concatenate (TS, "-S", TS) /* \M693.TS__ */
        }
        ElseIf ((Arg0 == 0x01))
        {
            Concatenate (TS, "-C", TS) /* \M693.TS__ */
        }
        ElseIf ((Arg0 == 0x02))
        {
            Concatenate (TS, "-O", TS) /* \M693.TS__ */
        }

        If ((Arg4 == 0x00))
        {
            Concatenate (TS, "-N", TS) /* \M693.TS__ */
        }
        Else
        {
            Concatenate (TS, "-L", TS) /* \M693.TS__ */
        }

        If (Arg1)
        {
            Concatenate (TS, "-Exc", TS) /* \M693.TS__ */
        }

        SRMT (TS)
        /* Initialize statistics */

        M001 ()
        If ((Arg0 > 0x02))
        {
            /* Unexpected Kind of Op (0 - Store, ...) */

            ERR (Concatenate (TS, TERR), Z126, __LINE__, 0x00, 0x00, Arg0, 0x00)
            Return (0x01)
        }

        If ((Arg4 > 0x01))
        {
            /* Unexpected Kind of Source-Target pair */

            ERR (Concatenate (TS, TERR), Z126, __LINE__, 0x00, 0x00, Arg4, 0x00)
            Return (0x01)
        }

        /* Flags of Store from and to Named to check */
        /* exceptional conditions on storing */
        If ((Arg0 != 0x00))
        {
            Local0 = 0x00
            Local1 = 0x00
        }
        Else
        {
            Local0 = 0x01
            Local1 = (Arg4 == 0x00)
        }

        /* Enumerate Target types */

        While (LPN0)
        {
            If ((DerefOf (B670 [LPC0]) && DerefOf (Arg2 [LPC0])))
            {
                /* Not invalid type of the Target Object to store in */

                LPN1 = 0x07
                LPC1 = 0x00
                /* Enumerate the Explicit conversion operators */
                /* which determine expected Result types */
                While (LPN1)
                {
                    /* Choose expected Result type */

                    If (Y900)
                    {
                        Local2 = DerefOf (Index (Buffer (0x07)
                                    {
                                         0x01, 0x01, 0x01, 0x02, 0x02, 0x02, 0x03         // .......
                                    }, LPC1))
                    }
                    Else
                    {
                        Local2 = DerefOf (SCL0 [LPC1])
                    }

                    If ((DerefOf (B671 [Local2]) && DerefOf (Arg3 [Local2])))
                    {
                        /* Not invalid type of the result Object to be stored */

                        If (F64)
                        {
                            Local3 = DerefOf (P640 [LPC1])
                        }
                        Else
                        {
                            Local3 = DerefOf (P320 [LPC1])
                        }

                        If (Arg1)
                        {
                            /* Skip cases without exceptional conditions */

                            If (!M685 ((Arg0 != 0x00), LPC0, Local2, Local0, Local1))
                            {
                                LPN1--
                                LPC1++
                                Continue
                            }
                        }
                        ElseIf                        /* Skip cases with exceptional conditions */

 (M685 ((Arg0 != 0x00), LPC0, Local2, Local0, Local1))
                        {
                            LPN1--
                            LPC1++
                            Continue
                        }

                        If ((Arg4 == 0x00))
                        {
                            /* Named Source and Target */

                            M008 (Concatenate (TS, "-m008"), 0x00, LPC0, Local2, Arg0, Arg1, Local3)
                        }
                        ElseIf ((Arg4 == 0x01))
                        {
                            /* LocalX Target */

                            M009 (Concatenate (TS, "-m009"), 0x00, LPC0, Local2, Arg0, Arg1, Local3)
                        }
                    }

                    LPN1--
                    LPC1++
                }
            }

            LPN0--
            LPC0++
        }

        /* Output statistics */

        M002 (Concatenate ("Storing of the result of Explicit conversion to Named Object with ", DerefOf (PAC4 [Arg0])))
        Return (0x00)
    }

    /* Run-method */

    Method (RES3, 0, NotSerialized)
    {
        Debug = "TEST: RES3, Result Object optional storing in the explicit conversion operators"
        /* Named Source and Target */
        /* Store the result of the explicit conversion operators */
        M693 (0x00, 0x00, B676, B676, 0x00)
        /* CopyObject the result of the explicit conversion operators */

        M693 (0x01, 0x00, B676, B676, 0x00)
        /* Optional storing of the result of the explicit conversion operators */

        M693 (0x02, 0x00, B676, B676, 0x00)
        /* LocalX Target */
        /* Store the result of the explicit conversion operators */
        M693 (0x00, 0x00, B677, B676, 0x01)
        /* CopyObject the result of the explicit conversion operators */

        M693 (0x01, 0x00, B677, B676, 0x01)
        /* Optional storing of the result of the explicit conversion operators */

        M693 (0x02, 0x00, B677, B676, 0x01)
    }
