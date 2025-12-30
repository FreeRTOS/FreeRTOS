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
     * Check Result Object processing on Increment/Decrement
     */
    Name (Z125, 0x7D)
    /* Test verifying Result Object processing on storing of the resilt */
    /* into different kinds of Target Objects by means of the specified */
    /* either Increment or Decrement operator */
    /* m692(<op (Increment/Decrement)>, <exc. conditions>) */
    Method (M692, 2, Serialized)
    {
        Name (TS, "m692")
        /*
         - choose a type of the destination operand Object (Dst0):
         = Uninitialized
         = Integer
         = String
         = Buffer
         = Package
         ...
         - choose kind of the operand Object:
         = Named Object
         = Method ArgX Object
         = Method LocalX Object
         - choose a value to initialize Dst0,
         - choose a benchmark value according to the initialized value - Bval
         - check that the Dst0 is properly initialized
         - perform storing expression:
         Increment(Expr(Dst0))
         Decrement(Expr(Dst0))
         - check that the benchmark value Bval is equal to the updated
         destination operand Object Dst0
         */
        /* Object-initializers are used with Source~Target */
        /* Integer */
        Name (INT0, 0xFEDCBA9876543210)
        /* String */

        Name (STR0, "76543210")
        Name (STR1, "76543210")
        /* Buffer */

        Name (BUF0, Buffer (0x09)
        {
            /* 0000 */  0x09, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02,  // ........
            /* 0008 */  0x01                                             // .
        })
        Name (BUF1, Buffer (0x09)
        {
            /* 0000 */  0x09, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02,  // ........
            /* 0008 */  0x01                                             // .
        })
        /* Initializer of Fields */

        Name (BUF2, Buffer (0x09)
        {
            /* 0000 */  0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25,  // ..ueUE5%
            /* 0008 */  0x15                                             // .
        })
        /* Base of Buffer Fields */

        Name (BUFZ, Buffer (0x14){})
        /* Package */

        Name (PAC0, Package (0x03)
        {
            0xFEDCBA987654321F,
            "test package",
            Buffer (0x09)
            {
                /* 0000 */  0x13, 0x12, 0x11, 0x10, 0x0F, 0x0E, 0x0D, 0x0C,  // ........
                /* 0008 */  0x0B                                             // .
            }
        })
        If (Y361)
        {
            /* Field Unit */

            Field (OPR0, ByteAcc, NoLock, Preserve)
            {
                FLU0,   69,
                FLU1,   69
            }
        }

        /* Device */

        Device (DEV0)
        {
            Name (S000, "DEV0")
        }

        /* Event */

        Event (EVE0)
        /* Method */

        Name (MMM0, 0x00)   /* Method as Source Object */
        Method (MMMX, 0, NotSerialized)
        {
            Return ("abcd")
        }

        /* Mutex */

        Mutex (MTX0, 0x00)
        If (Y361)
        {
            /* Operation Region */

            OperationRegion (OPR0, SystemMemory, 0x00, 0x14)
        }

        /* Power Resource */

        PowerResource (PWR0, 0x00, 0x0000)
        {
            Name (S000, "PWR0")
        }

        /* Processor */

        Processor (CPU0, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (S000, "CPU0")
        }

        /* Thermal Zone */

        ThermalZone (TZN0)
        {
            Name (S000, "TZN0")
        }

        /* Buffer Field */

        CreateField (BUFZ, 0x00, 0x45, BFL0)
        CreateField (BUFZ, 0x00, 0x45, BFL1)
        /* Data to gather statistics */

        Name (STCS, 0x00)
        Name (INDM, 0xFF)
        Name (PAC2, Package (0x01){})
        Name (IND2, 0x00)
        Name (PAC3, Package (0x01){})
        Name (IND3, 0x00)
        Name (PAC4, Package (0x02)
        {
            "Increment",
            "Decrement"
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
                    Debug = IND2 /* \M692.IND2 */
                    Debug = "Types:"
                    LPN0 = IND2 /* \M692.IND2 */
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
                    Debug = IND3 /* \M692.IND3 */
                    LPN0 = IND3 /* \M692.IND3 */
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

        /* Prepare Source of specified type */

        Method (M004, 3, Serialized)
        {
            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                }
                Case (0x01)
                {
                    CopyObject (INT0, Arg2)
                }
                Case (0x02)
                {
                    CopyObject (STR0, Arg2)
                }
                Case (0x03)
                {
                    CopyObject (BUF0, Arg2)
                }
                Case (0x04)
                {
                    CopyObject (PAC0, Arg2)
                }
                Case (0x05)
                {
                    FLU0 = BUF2 /* \M692.BUF2 */
                }
                Case (0x06)
                {
                    CopyObject (DEV0, Arg2)
                }
                Case (0x07)
                {
                    CopyObject (EVE0, Arg2)
                }
                Case (0x08)
                {
                    CopyObject (DerefOf (RefOf (MMMX)), MMM0) /* \M692.MMM0 */
                    CopyObject (DerefOf (RefOf (MMM0)), Arg2)
                }
                Case (0x09)
                {
                    CopyObject (MTX0, Arg2)
                }
                Case (0x0A)
                {
                    CopyObject (OPR0, Arg2)
                }
                Case (0x0B)
                {
                    CopyObject (PWR0, Arg2)
                }
                Case (0x0C)
                {
                    CopyObject (CPU0, Arg2)
                }
                Case (0x0D)
                {
                    CopyObject (TZN0, Arg2)
                }
                Case (0x0E)
                {
                    BFL0 = BUF2 /* \M692.BUF2 */
                }
                /* Unexpected Source Type */

                Default
                {
                    ERR (Concatenate (Arg0, TERR), Z125, __LINE__, 0x00, 0x00, Arg1, 0x00)
                    Return (0x01)
                }

            }

            If (CH03 (Arg0, Z125, __LINE__, 0x00, 0x00))
            {
                /* Exception during preparing of Source Object */

                Return (0x01)
            }

            Local0 = ObjectType (Arg2)
            If ((Local0 != Arg1))
            {
                /* ObjectType of Source can not be set up */

                ERR (Arg0, Z125, __LINE__, 0x00, 0x00, Local0, Arg1)
                Return (0x01)
            }

            Return (0x00)
        }

        /* Check Target Object to have the expected type and value */
        /* m006(<msg>, <ref to target>, <target type>, <source type>, */
        /*      <op>, <target save type>) */
        Method (M006, 6, Serialized)
        {
            Name (MMM2, 0x00) /* The auxiliary Object to invoke Method */
            Local2 = ObjectType (Arg1)
            /* Target must save type */

            If ((Local2 != Arg2))
            {
                /* Types mismatch Target/Target on storing */
                /* Target (Result) type should keep the original type */
                If (((Arg3 == C00A) || (Arg3 == C00B)))
                {
                    If (X195)
                    {
                        ERR (Arg0, Z125, __LINE__, 0x00, 0x00, Local2, Arg2)
                    }
                }
                Else
                {
                    ERR (Arg0, Z125, __LINE__, 0x00, 0x00, Local2, Arg2)
                }

                If (STCS)
                {
                    M000 (0x03, 0x0100, Arg2, Local2)
                }

                Return (0x01)
            }

            Switch (ToInteger (Arg2))
            {
                Case (0x01)
                {
                    Switch (ToInteger (Arg3))
                    {
                        Case (0x01)
                        {
                            If ((Arg4 == 0x00))
                            {
                                /* Increment */

                                Local0 = (INT0 + 0x01)
                            }
                            ElseIf ((Arg4 == 0x01))
                            {
                                Local0 = (INT0 - 0x01)
                            }
                            Else
                            {
                                Local0 = INT0 /* \M692.INT0 */
                            }

                            If ((DerefOf (Arg1) != Local0))
                            {
                                ERR (Arg0, Z125, __LINE__, 0x00, 0x00, DerefOf (Arg1), Local0)
                                Return (0x01)
                            }
                        }
                        Case (0x02)
                        {
                            If ((Arg4 == 0x00))
                            {
                                /* Increment */

                                Local0 = (STR0 + 0x01)
                            }
                            ElseIf ((Arg4 == 0x01))
                            {
                                Local0 = (STR0 - 0x01)
                            }
                            Else
                            {
                                Local0 = STR0 /* \M692.STR0 */
                            }

                            If ((DerefOf (Arg1) != Local0))
                            {
                                ERR (Arg0, Z125, __LINE__, 0x00, 0x00, DerefOf (Arg1), Local0)
                                Return (0x01)
                            }
                        }
                        Case (0x03)
                        {
                            If ((Arg4 == 0x00))
                            {
                                /* Increment */

                                Local0 = (BUF0 + 0x01)
                            }
                            ElseIf ((Arg4 == 0x01))
                            {
                                Local0 = (BUF0 - 0x01)
                            }
                            Else
                            {
                                Local0 = BUF0 /* \M692.BUF0 */
                            }

                            If ((DerefOf (Arg1) != Local0))
                            {
                                ERR (Arg0, Z125, __LINE__, 0x00, 0x00, DerefOf (Arg1), Local0)
                                Return (0x01)
                            }
                        }
                        Default
                        {
                            ERR (Concatenate (Arg0, TERR), Z125, __LINE__, 0x00, 0x00, Arg1, Arg3)
                            Return (0x01)
                        }

                    }
                }
                Case (0x02)
                {
                    Switch (ToInteger (Arg3))
                    {
                        Case (0x02)
                        {
                            If ((Arg4 == 0x00))
                            {
                                /* Increment */

                                STR1 = (STR0 + 0x01)
                            }
                            ElseIf ((Arg4 == 0x01))
                            {
                                STR1 = (STR0 - 0x01)
                            }
                            Else
                            {
                                STR1 = STR0 /* \M692.STR0 */
                            }

                            If ((DerefOf (Arg1) != STR1))
                            {
                                ERR (Arg0, Z125, __LINE__, 0x00, 0x00, DerefOf (Arg1), STR1)
                                Return (0x01)
                            }
                        }
                        Default
                        {
                            ERR (Concatenate (Arg0, TERR), Z125, __LINE__, 0x00, 0x00, Arg1, Arg3)
                            Return (0x01)
                        }

                    }
                }
                Case (0x03)
                {
                    Switch (ToInteger (Arg3))
                    {
                        Case (0x03)
                        {
                            If ((Arg4 == 0x00))
                            {
                                /* Increment */

                                BUF1 = (BUF0 + 0x01)
                            }
                            ElseIf ((Arg4 == 0x01))
                            {
                                BUF1 = (BUF0 - 0x01)
                            }
                            Else
                            {
                                BUF1 = BUF0 /* \M692.BUF0 */
                            }

                            If ((DerefOf (Arg1) != BUF1))
                            {
                                ERR (Arg0, Z125, __LINE__, 0x00, 0x00, DerefOf (Arg1), BUF1)
                                Return (0x01)
                            }
                        }
                        Default
                        {
                            ERR (Concatenate (Arg0, TERR), Z125, __LINE__, 0x00, 0x00, Arg1, Arg3)
                            Return (0x01)
                        }

                    }
                }
                Case (0x05)
                {
                    Switch (ToInteger (Arg3))
                    {
                        Case (0x05)
                        {
                            If ((Arg4 == 0x00))
                            {
                                /* Increment */

                                FLU1 = (FLU0 + 0x01)
                            }
                            ElseIf ((Arg4 == 0x01))
                            {
                                FLU1 = (FLU0 - 0x01)
                            }
                            Else
                            {
                                FLU1 = FLU0 /* \M692.FLU0 */
                            }

                            If ((DerefOf (Arg1) != FLU1))
                            {
                                ERR (Arg0, Z125, __LINE__, 0x00, 0x00, DerefOf (Arg1), FLU1)
                                Return (0x01)
                            }
                        }
                        Default
                        {
                            ERR (Concatenate (Arg0, TERR), Z125, __LINE__, 0x00, 0x00, Arg1, Arg3)
                            Return (0x01)
                        }

                    }
                }
                Case (0x0E)
                {
                    Switch (ToInteger (Arg3))
                    {
                        Case (0x0E)
                        {
                            If ((Arg4 == 0x00))
                            {
                                /* Increment */

                                BFL1 = (BFL0 + 0x01)
                            }
                            ElseIf ((Arg4 == 0x01))
                            {
                                BFL1 = (BFL0 - 0x01)
                            }
                            Else
                            {
                                BFL1 = BFL0 /* \M692.BFL0 */
                            }

                            If ((DerefOf (Arg1) != BFL1))
                            {
                                ERR (Arg0, Z125, __LINE__, 0x00, 0x00, DerefOf (Arg1), BFL1)
                                Return (0x01)
                            }
                        }
                        Default
                        {
                            ERR (Concatenate (Arg0, TERR), Z125, __LINE__, 0x00, 0x00, Arg1, Arg3)
                            Return (0x01)
                        }

                    }
                }
                Default
                {
                    ERR (Concatenate (Arg0, TERR), Z125, __LINE__, 0x00, 0x00, Arg1, Arg3)
                    Return (0x01)
                }

            }

            Return (0x00)
        }

        /* Check processing of an Source Named Object of the specified type */
        /* as an immediate operand in Increment/Decrement operators */
        /* m008(<msg>, <aux>, <target type>, <source type>, */
        /*      <op>, <exc. condition>) */
        Method (M008, 6, Serialized)
        {
            /* Source Named Object */

            Name (SRC0, 0x00)
            Concatenate (Arg0, "-", Arg0)
            Concatenate (Arg0, Concatenate (Mid (Arg4, 0x00, 0x02), Concatenate (Mid (Arg2, 0x00,
                0x02), Mid (Arg3, 0x00, 0x02))), Arg0)
            If (STCS)
            {
                Debug = Arg0
            }

            /* Target save type of Increment/Decrement operators is 0 */
            /* (Target should take a type of Integer) */
            Local0 = 0x00
            If ((Arg3 == 0x05))
            {
                /* Field Unit Source/Target */

                Local3 = RefOf (FLU0)
            }
            ElseIf ((Arg3 == 0x0E))
            {
                /* Buffer Field Source/Target */

                Local3 = RefOf (BFL0)
            }
            Else
            {
                Local3 = RefOf (SRC0)
            }

            /* Prepare Source of specified type */

            If (M004 (Concatenate (Arg0, "-m004"), Arg3, Local3))
            {
                /* Source Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z125, __LINE__, 0x00, 0x00, Arg3, 0x00)
                Return (0x01)
            }

            /* Use a Source Object immediately in the Operator */

            If ((Arg3 == 0x05))
            {
                /* Field Unit Source/Target */

                If ((Arg4 == 0x00))
                {
                    /* Increment */

                    FLU0++
                }
                ElseIf ((Arg4 == 0x01))
                {
                    /* Decrement */

                    FLU0--
                }
                Else
                {
                    /* Unexpected Kind of Op (0 - Increment, 1 - Decrement) */

                    ERR (Concatenate (Arg0, TERR), Z125, __LINE__, 0x00, 0x00, Arg4, 0x00)
                    Return (0x01)
                }
            }
            ElseIf ((Arg3 == 0x0E))
            {
                /* Buffer Source/Field Target */

                If ((Arg4 == 0x00))
                {
                    /* Increment */

                    BFL0++
                }
                ElseIf ((Arg4 == 0x01))
                {
                    /* Decrement */

                    BFL0--
                }
                Else
                {
                    /* Unexpected Kind of Op (0 - Increment, 1 - Decrement) */

                    ERR (Concatenate (Arg0, TERR), Z125, __LINE__, 0x00, 0x00, Arg4, 0x00)
                    Return (0x01)
                }
            }
            ElseIf ((Arg4 == 0x00))
            {
                /* Increment */

                SRC0++
            }
            ElseIf ((Arg4 == 0x01))
            {
                /* Decrement */

                SRC0--
            }
            Else
            {
                /* Unexpected Kind of Op (0 - Increment, 1 - Decrement) */

                ERR (Concatenate (Arg0, TERR), Z125, __LINE__, 0x00, 0x00, Arg4, 0x00)
                Return (0x01)
            }

            If (Arg5)
            {
                /* Exception is expected */

                If (!CH06 (Arg0, 0x16, 0xFF))
                {
                    If (STCS)
                    {
                        M000 (0x02, 0x0100, Arg2, Arg3)
                    }
                }
            }
            ElseIf (CH03 (Arg0, Z125, __LINE__, 0x00, Arg2))
            {
                /* Processing caused unexpected exception */

                If (STCS)
                {
                    M000 (0x02, 0x0100, Arg2, Arg3)
                }
            }
            Else
            {
                /* Check Target Object to have the expected type and value */

                M006 (Concatenate (Arg0, "-m006"), Local3, Arg2, Arg3, Arg4, Local0)
            }

            Return (0x00)
        }

        /* Check processing of an Source LocalX Object of the specified type */
        /* as an immediate operand in Increment/Decrement operators */
        /* m009(<msg>, <aux>, <target type>, <source type>, */
        /*      <op>, <exc. condition>) */
        Method (M009, 6, NotSerialized)
        {
            /* Source LocalX Object: Local1 */

            Concatenate (Arg0, "-", Arg0)
            Concatenate (Arg0, Concatenate (Mid (Arg4, 0x00, 0x02), Concatenate (Mid (Arg2, 0x00,
                0x02), Mid (Arg3, 0x00, 0x02))), Arg0)
            If (STCS)
            {
                Debug = Arg0
            }

            /* Target save type of Increment/Decrement operators is 0 */
            /* (Target should take a type of Integer) */
            Local0 = 0x00
            If (M004 (Concatenate (Arg0, "-m004"), Arg3, RefOf (Local1)))
            {
                /* Source Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z125, __LINE__, 0x00, 0x00, Arg3, 0x00)
                Return (0x01)
            }

            If ((Arg4 == 0x00))
            {
                /* Increment */

                Local1++
            }
            ElseIf ((Arg4 == 0x01))
            {
                /* Decrement */

                Local1--
            }
            Else
            {
                /* Unexpected Kind of Op (0 - Increment, 1 - Decrement) */

                ERR (Concatenate (Arg0, TERR), Z125, __LINE__, 0x00, 0x00, Arg4, 0x00)
                Return (0x01)
            }

            If (Arg5)
            {
                If ((SLCK && ((ToInteger (Arg3) == 0x00) && (ToInteger (Arg2
                    ) == 0x01))))
                {
                    /* In slack mode, [Uninitialized] object */
                    /* will be converted to Integer 0, thus no */
                    /* exception caused by implicit source */
                    /* conversion. */
                    If (CH03 (Arg0, Z125, __LINE__, 0x00, Arg2))
                    {
                        If (STCS)
                        {
                            M000 (0x02, 0x0100, Arg2, Arg3)
                        }
                    }
                }
                ElseIf                /* Exception is expected */

 (!CH06 (Arg0, 0x1A, 0xFF))
                {
                    If (STCS)
                    {
                        M000 (0x02, 0x0100, Arg2, Arg3)
                    }
                }
            }
            ElseIf (CH03 (Arg0, Z125, __LINE__, 0x00, Arg2))
            {
                /* Processing caused unexpected exception */

                If (STCS)
                {
                    M000 (0x02, 0x0100, Arg2, Arg3)
                }
            }
            Else
            {
                /* Check Target Object to have the expected type and value */

                M006 (Concatenate (Arg0, "-m006"), RefOf (Local1), Arg2, Arg3, Arg4, Local0)
            }

            Return (0x00)
        }

        /* Check processing of an Source LocalX Object of the specified type */
        /* as an immediate argument of the Method in which it is used */
        /* as an immediate operand in Increment/Decrement operators */
        /* m00a(<msg>, <aux>, <target type>, <source type>, */
        /*      <op>, <exc. condition>) */
        Method (M00A, 6, NotSerialized)
        {
            /* Source LocalX Object: Local1 */

            Method (M100, 1, NotSerialized)
            {
                Arg0++
                Return (Arg0)
            }

            Method (M101, 1, NotSerialized)
            {
                Arg0--
                Return (Arg0)
            }

            Concatenate (Arg0, "-", Arg0)
            Concatenate (Arg0, Concatenate (Mid (Arg4, 0x00, 0x02), Concatenate (Mid (Arg2, 0x00,
                0x02), Mid (Arg3, 0x00, 0x02))), Arg0)
            If (STCS)
            {
                Debug = Arg0
            }

            /* Target save type of Increment/Decrement operators is 0 */
            /* (Target should take a type of Integer) */
            Local0 = 0x00
            If (M004 (Concatenate (Arg0, "-m004"), Arg3, RefOf (Local1)))
            {
                /* Source Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z125, __LINE__, 0x00, 0x00, Arg3, 0x00)
                Return (0x01)
            }

            If ((Arg4 == 0x00))
            {
                /* Increment */

                Local2 = M100 (Local1)
            }
            ElseIf ((Arg4 == 0x01))
            {
                /* Decrement */

                Local2 = M101 (Local1)
            }
            Else
            {
                /* Unexpected Kind of Op (0 - Increment, 1 - Decrement) */

                ERR (Concatenate (Arg0, TERR), Z125, __LINE__, 0x00, 0x00, Arg4, 0x00)
                Return (0x01)
            }

            If (Arg5)
            {
                If ((SLCK && ((ToInteger (Arg3) == 0x00) && (ToInteger (Arg2
                    ) == 0x01))))
                {
                    /* In slack mode, [Uninitialized] object */
                    /* will be converted to Integer 0, thus no */
                    /* exception caused by implicit source */
                    /* conversion. */
                    If (CH03 (Arg0, Z125, __LINE__, 0x00, Arg2))
                    {
                        If (STCS)
                        {
                            M000 (0x02, 0x0100, Arg2, Arg3)
                        }
                    }
                }
                ElseIf                /* Exception is expected */

 (!CH06 (Arg0, 0x1E, 0xFF))
                {
                    If (STCS)
                    {
                        M000 (0x02, 0x0100, Arg2, Arg3)
                    }
                }
            }
            ElseIf (CH03 (Arg0, Z125, __LINE__, 0x00, Arg2))
            {
                /* Processing caused unexpected exception */

                If (STCS)
                {
                    M000 (0x02, 0x0100, Arg2, Arg3)
                }
            }
            Else
            {
                /* Check Target Object to have the expected type and value */

                M006 (Concatenate (Arg0, "-m006"), RefOf (Local2), Arg2, Arg3, Arg4, Local0)
                M006 (Concatenate (Arg0, "-m006"), RefOf (Local1), Arg2, Arg3, 0x02, Local0)
            }

            Return (0x00)
        }

        /* Check processing of an Source Named Object of the specified type */
        /* passed by a reference as an argument of the Method in which it is used */
        /* as an immediate operand in Increment/Decrement operators */
        /* m00b(<msg>, <aux>, <target type>, <source type>, */
        /*      <op>, <exc. condition>) */
        Method (M00B, 6, Serialized)
        {
            /* Source Named Object */

            Name (SRC0, 0x00)
            Method (M100, 1, NotSerialized)
            {
                Arg0++
            }

            Method (M101, 1, NotSerialized)
            {
                Arg0--
            }

            Concatenate (Arg0, "-", Arg0)
            Concatenate (Arg0, Concatenate (Mid (Arg4, 0x00, 0x02), Concatenate (Mid (Arg2, 0x00,
                0x02), Mid (Arg3, 0x00, 0x02))), Arg0)
            If (STCS)
            {
                Debug = Arg0
            }

            /* Target save type of Increment/Decrement operators is 0 */
            /* (Target should take a type of Integer) */
            Local0 = 0x00
            If ((Arg3 == 0x05))
            {
                /* Field Unit Source/Target */

                Local3 = RefOf (FLU0)
            }
            ElseIf ((Arg3 == 0x0E))
            {
                /* Buffer Field Source/Target */

                Local3 = RefOf (BFL0)
            }
            Else
            {
                Local3 = RefOf (SRC0)
            }

            /* Prepare Source of specified type */

            If (M004 (Concatenate (Arg0, "-m004"), Arg3, Local3))
            {
                /* Source Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z125, __LINE__, 0x00, 0x00, Arg3, 0x00)
                Return (0x01)
            }

            /* Use a reference to Source Object in the Operator */

            If ((Arg4 == 0x00))
            {
                /* Increment */

                M100 (Local3)
            }
            ElseIf ((Arg4 == 0x01))
            {
                /* Decrement */

                M101 (Local3)
            }
            Else
            {
                /* Unexpected Kind of Op (0 - Increment, 1 - Decrement) */

                ERR (Concatenate (Arg0, TERR), Z125, __LINE__, 0x00, 0x00, Arg4, 0x00)
                Return (0x01)
            }

            If (Arg5)
            {
                /* Exception is expected */

                If (!CH06 (Arg0, 0x22, 0xFF))
                {
                    If (STCS)
                    {
                        M000 (0x02, 0x0100, Arg2, Arg3)
                    }
                }
            }
            ElseIf (CH03 (Arg0, Z125, __LINE__, 0x00, Arg2))
            {
                /* Processing caused unexpected exception */

                If (STCS)
                {
                    M000 (0x02, 0x0100, Arg2, Arg3)
                }
            }
            Else
            {
                /* Check Target Object to have the expected type and value */

                M006 (Concatenate (Arg0, "-m006"), Local3, Arg2, Arg3, Arg4, Local0)
            }

            Return (0x00)
        }

        Name (LPC0, 0x01)
        Name (LPN1, 0x11)
        Name (LPC1, 0x00)
        If ((Arg0 == 0x00))
        {
            Concatenate (TS, "-Inc", TS) /* \M692.TS__ */
        }
        Else
        {
            Concatenate (TS, "-Dec", TS) /* \M692.TS__ */
        }

        If (Arg1)
        {
            Concatenate (TS, "-Exc", TS) /* \M692.TS__ */
        }

        SRMT (TS)
        /* Initialize statistics */

        M001 ()
        If ((Arg0 > 0x01))
        {
            /* Unexpected Kind of Op (0 - Increment, 1 - Decrement) */

            ERR (Concatenate (TS, TERR), Z125, __LINE__, 0x00, 0x00, Arg0, 0x00)
            Return (0x01)
        }

        /* Enumerate Result types */

        While (LPN1)
        {
            If ((DerefOf (B677 [LPC1]) && DerefOf (B671 [LPC1])))
            {
                /* Not invalid type of the result Object */
                /* Determine Target type */
                LPC0 = LPC1 /* \M692.LPC1 */
                If (!Y501)
                {
                    /* The question: should Increment/Decrement save the Target type? */

                    If (!DerefOf (B678 [LPC0]))
                    {
                        /* Not fixed type, Target type is Integer */

                        LPC0 = 0x01
                    }
                }

                If (Arg1)
                {
                    /* Skip cases without exceptional conditions */

                    If (DerefOf (B67B [LPC1]))
                    {
                        LPN1--
                        LPC1++
                        Continue
                    }
                }
                ElseIf                /* Skip cases with exceptional conditions */

 (!DerefOf (B67B [LPC1]))
                {
                    LPN1--
                    LPC1++
                    Continue
                }

                /* Named Source */

                If ((LPC1 != C008))
                {
                    /* Named can not be set up to Uninitialized */

                    M008 (Concatenate (TS, "-m008"), 0x00, LPC0, LPC1, Arg0, Arg1)
                }

                /* LocalX Source */

                If (!DerefOf (B678 [LPC1]))
                {
                    /* LocalX can not be set up to Fixed types */

                    M009 (Concatenate (TS, "-m009"), 0x00, LPC0, LPC1, Arg0, Arg1)
                    M00A (Concatenate (TS, "-m00a"), 0x00, LPC0, LPC1, Arg0, Arg1)
                }

                /* Reference to Named */

                If (Y367)
                {
                    If ((LPC1 != C008))
                    {
                        /* Named can not be set up to Uninitialized */

                        M00B (Concatenate (TS, "-m00b"), 0x00, LPC0, LPC1, Arg0, Arg1)
                    }
                }
            }

            LPN1--
            LPC1++
        }

        /* Output statistics */

        M002 (Concatenate ("Result Object processing with ", DerefOf (PAC4 [Arg0])))
        Return (0x00)
    }

    /* Run-method */

    Method (RES2, 0, NotSerialized)
    {
        Debug = "TEST: RES2, Result Object processing on Increment/Decrement"
        /* Increment */

        M692 (0x00, 0x00)
        /* Decrement */

        M692 (0x01, 0x00)
    }
