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
     * Check Result Object processing (simultaneously verifying
     * the Implicit Result Object Conversion Rules) in the Store operator
     */
    Name (Z123, 0x7B)
    /* Store to Global Named Objects, Constant and LocalX */

    Method (M690, 0, Serialized)
    {
        Name (TERR, "test error")
        Name (I000, 0x00)
        /* Common testing control */

        Method (M100, 3, Serialized)
        {
            Name (LPN0, 0x00)
            Name (LPC0, 0x00)
            Name (LPN1, 0x00)
            Name (LPC1, 0x00)
            SRMT (Arg0)
            LPN0 = 0x09
            LPC0 = 0x00
            /* Enumerate ways to obtain some result object */

            While (LPN0)
            {
                LPN1 = 0x03
                LPC1 = 0x01
                /* Enumerate types of the result Object */

                While (LPN1)
                {
                    /* Choose a type and a value of the Object to store into */

                    Switch (ToInteger (Arg1))
                    {
                        Case (0x00)
                        {
                                                /* Uninitialized */
                        /* Store(Src0, Local0) */
                        }
                        Case (0x01)
                        {
                            /* Integer */
                            /* Choose kind of the Object to store into: */
                            If ((Arg2 == 0x00))
                            {
                                /* Constant (like Store(Src0, Zero)) */

                                M010 (Concatenate (__METHOD__, "-m010"), LPC0, LPC1)
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                /* Named Object */

                                M011 (Concatenate (__METHOD__, "-m011"), LPC0, LPC1)
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                /* ArgX Object */
                                /* Store(Src0, arg3) */
                                Debug = "Not implemented"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                            ElseIf ((Arg2 == 0x03))
                            {
                                /* LocalX Object */

                                M013 (Concatenate (__METHOD__, "-m013"), LPC0, LPC1)
                            }
                            ElseIf ((Arg2 == 0x04))
                            {
                                /* Reference in ArgX Object */
                                /* Store(Src0, arg4) */
                                Debug = "Not implemented"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                            ElseIf ((Arg2 == 0x05))
                            {
                                /* Elemenf of a Package */
                                /* Store(Src0, Index(p680, 0)) */
                                Debug = "Not implemented"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                            Else
                            {
                                Debug = "Unexpected Kind of the Object to store into"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                        }
                        Case (0x02)
                        {
                            /* String */
                            /* choose kind of the Object to store into: */
                            If ((Arg2 == 0x00))
                            {
                                /* Constant */
                                /* Store(Src0, "") */
                                Debug = "Not implemented"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                /* Named Object */

                                M021 (Concatenate (__METHOD__, "-m021"), LPC0, LPC1)
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                /* ArgX Object */
                                /* Store(Src0, arg3) */
                                Debug = "Not implemented"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                            ElseIf ((Arg2 == 0x03))
                            {
                                /* LocalX Object */

                                M023 (Concatenate (__METHOD__, "-m023"), LPC0, LPC1)
                            }
                            ElseIf ((Arg2 == 0x04))
                            {
                                /* Reference in ArgX Object */
                                /* Store(Src0, arg4) */
                                Debug = "Not implemented"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                            ElseIf ((Arg2 == 0x05))
                            {
                                /* Elemenf of a Package */
                                /* Store(Src0, Index(p680, 0)) */
                                Debug = "Not implemented"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                            Else
                            {
                                Debug = "Unexpected Kind of the Object to store into"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                        }
                        Case (0x03)
                        {
                            /* Buffer */
                            /* choose kind of the Object to store into: */
                            If ((Arg2 == 0x00))
                            {
                                /* Constant */
                                /* Store(Src0, Buffer(1){}) */
                                Debug = "Not implemented"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                /* Named Object */

                                M031 (Concatenate (__METHOD__, "-m031"), LPC0, LPC1)
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                /* ArgX Object */
                                /* Store(Src0, arg3) */
                                Debug = "Not implemented"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                            ElseIf ((Arg2 == 0x03))
                            {
                                /* LocalX Object */
                                /* Store(Src0, Local2) */
                                Debug = "Not implemented"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                            ElseIf ((Arg2 == 0x04))
                            {
                                /* Reference in ArgX Object */
                                /* Store(Src0, arg4) */
                                Debug = "Not implemented"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                            ElseIf ((Arg2 == 0x05))
                            {
                                /* Elemenf of a Package */
                                /* Store(Src0, Index(p680, 0)) */
                                Debug = "Not implemented"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                            Else
                            {
                                Debug = "Unexpected Kind of the Object to store into"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                        }
                        Case (0x04)
                        {
                            /* Package */
                            /* Store(Src0, p680) */
                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer field */
                            /* Choose kind of the Object to store into: */
                            If ((Arg2 == 0x00))
                            {
                                /* Constant (like Store(Src0, Zero)) */

                                Debug = "Not implemented"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                /* Named Object */

                                M0E0 (Concatenate (__METHOD__, "-m0e0"), LPC0, LPC1)
                                M0E1 (Concatenate (__METHOD__, "-m0e1"), LPC0, LPC1)
                                M0E2 (Concatenate (__METHOD__, "-m0e2"), LPC0, LPC1)
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                /* ArgX Object */
                                /* Store(Src0, arg3) */
                                Debug = "Not implemented"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                            ElseIf ((Arg2 == 0x03))
                            {
                                /* LocalX Object */
                                /* Store(Src0, Local2) */
                                Debug = "Not implemented"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                            ElseIf ((Arg2 == 0x04))
                            {
                                /* Reference in ArgX Object */
                                /* Store(Src0, arg4) */
                                Debug = "Not implemented"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                            ElseIf ((Arg2 == 0x05))
                            {
                                /* Elemenf of a Package */
                                /* Store(Src0, Index(p680, 0)) */
                                Debug = "Not implemented"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                            Else
                            {
                                Debug = "Unexpected Kind of the Object to store into"
                                ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                                Return (0x01)
                            }
                        }
                        Default
                        {
                            Debug = "Unexpected type of the Object to store into"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }

                    LPN1--
                    LPC1++
                }

                LPN0--
                LPC0++
            }

            Return (0x00)
        }

        /* Store() Result Object to Integer Constant */

        Method (M010, 3, Serialized)
        {
            Name (P000, Package (0x04)
            {
                Zero,
                One,
                Ones,
                0xFE7CB391D650A284
            })
            /* Return Indexed reference to ASL constant specified */
            /* by Name as an element of the Package for next applying */
            /* through Derefof operator as Destination in Store operator */
            Method (M200, 1, NotSerialized)
            {
                If (Y900)
                {
                    Return (Index (Package (0x04)
                        {
                            Zero,
                            One,
                            Ones,
                            0xFE7CB391D650A284
                        }, Arg0))
                }

                Return (P000 [Arg0])
            }

            /* ArgX as a way to obtain some result object */

            Method (M000, 5, Serialized)
            {
                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        DerefOf (M200 (0x01)) = Arg2
                        M680 (Arg0, 0x18, 0x00, DerefOf (M200 (0x01)), 0x01)
                        M680 (Arg0, 0x19, 0x00, Arg2, 0xFE7CB391D650A284)
                    }
                    Case (0x02)
                    {
                        /* String */

                        DerefOf (M200 (0x01)) = Arg3
                        M680 (Arg0, 0x1A, 0x00, DerefOf (M200 (0x01)), 0x01)
                        M680 (Arg0, 0x1B, 0x00, Arg3, "FE7CB391D650A284")
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        DerefOf (M200 (0x01)) = Arg4
                        M680 (Arg0, 0x1C, 0x00, DerefOf (M200 (0x01)), 0x01)
                        M680 (Arg0, 0x1D, 0x00, Arg4, Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                    }
                    Case (0x05)
                    {
                        /* Field Unit */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }
                    Case (0x0E)
                    {
                        /* Buffer Field */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }

                }

                Return (0x00)
            }

            /* Reference in ArgX as a way to obtain some result object */

            Method (M001, 5, Serialized)
            {
                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        DerefOf (M200 (0x01)) = DerefOf (Arg2)
                        M680 (Arg0, 0x20, 0x00, DerefOf (M200 (0x01)), 0x01)
                        M680 (Arg0, 0x21, 0x00, DerefOf (Arg2), 0xFE7CB391D650A284)
                    }
                    Case (0x02)
                    {
                        /* String */

                        DerefOf (M200 (0x01)) = DerefOf (Arg3)
                        M680 (Arg0, 0x22, 0x00, DerefOf (M200 (0x01)), 0x01)
                        M680 (Arg0, 0x23, 0x00, DerefOf (Arg3), "FE7CB391D650A284")
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        DerefOf (M200 (0x01)) = DerefOf (Arg4)
                        M680 (Arg0, 0x24, 0x00, DerefOf (M200 (0x01)), 0x01)
                        M680 (Arg0, 0x25, 0x00, DerefOf (Arg4), Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                    }
                    Case (0x05)
                    {
                        /* Field Unit */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }
                    Case (0x0E)
                    {
                        /* Buffer Field */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }

                }

                Return (0x00)
            }

            M680 (Arg0, 0x28, 0x00, DerefOf (M200 (0x01)), 0x01)
            /* Choose a way to obtain some result object */

            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    /* Data Image */
                    /* Choose a type of the result Object and specific source */
                    /* objects to obtain the result Object of the specified type. */
                    /* Check that the destination Object is properly initialized. */
                    /* Perform storing expression and check result. */
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            DerefOf (M200 (0x01)) = 0xFE7CB391D650A284
                            M680 (Arg0, 0x29, 0x00, DerefOf (M200 (0x01)), 0x01)
                        }
                        Case (0x02)
                        {
                            /* String */

                            DerefOf (M200 (0x01)) = "FE7CB391D650A284"
                            M680 (Arg0, 0x2A, 0x00, DerefOf (M200 (0x01)), 0x01)
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            DerefOf (M200 (0x01)) = Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                }
                            M680 (Arg0, 0x2B, 0x00, DerefOf (M200 (0x01)), 0x01)
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x01)
                {
                    /* Named Object */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            DerefOf (M200 (0x01)) = I6E0 /* \I6E0 */
                            M680 (Arg0, 0x2E, 0x00, DerefOf (M200 (0x01)), 0x01)
                            M680 (Arg0, 0x2F, 0x00, I6E0, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            DerefOf (M200 (0x01)) = S6E0 /* \S6E0 */
                            M680 (Arg0, 0x30, 0x00, DerefOf (M200 (0x01)), 0x01)
                            M680 (Arg0, 0x31, 0x00, S6E0, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            DerefOf (M200 (0x01)) = B6E0 /* \B6E0 */
                            M680 (Arg0, 0x32, 0x00, DerefOf (M200 (0x01)), 0x01)
                            M680 (Arg0, 0x33, 0x00, B6E0, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x02)
                {
                    /* Method ArgX Object */

                    M000 (Concatenate (Arg0, "-m000"), Arg2, 0xFE7CB391D650A284, "FE7CB391D650A284", Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                        })
                }
                Case (0x03)
                {
                    /* Method LocalX Object */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            Local0 = 0xFE7CB391D650A284
                        }
                        Case (0x02)
                        {
                            /* String */

                            Local0 = "FE7CB391D650A284"
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            Local0 = Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                }
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            DerefOf (M200 (0x01)) = Local0
                            M680 (Arg0, 0x38, 0x00, DerefOf (M200 (0x01)), 0x01)
                            M680 (Arg0, 0x39, 0x00, Local0, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            DerefOf (M200 (0x01)) = Local0
                            M680 (Arg0, 0x3A, 0x00, DerefOf (M200 (0x01)), 0x01)
                            M680 (Arg0, 0x3B, 0x00, Local0, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            DerefOf (M200 (0x01)) = Local0
                            M680 (Arg0, 0x3C, 0x00, DerefOf (M200 (0x01)), 0x01)
                            M680 (Arg0, 0x3D, 0x00, Local0, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x04)
                {
                    /* Derefof of intermediate Object (Method ArgX Object) */

                    M001 (Concatenate (Arg0, "-m001"), Arg2, RefOf (I6E1), RefOf (S6E1), RefOf (B6E1))
                }
                Case (0x05)
                {
                    /* Derefof of immediate Index(...) */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            DerefOf (M200 (0x01)) = DerefOf (P690 [0x00])
                            M680 (Arg0, 0x40, 0x00, DerefOf (M200 (0x01)), 0x01)
                            M680 (Arg0, 0x41, 0x00, DerefOf (P690 [0x00]), 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            DerefOf (M200 (0x01)) = DerefOf (P690 [0x01])
                            M680 (Arg0, 0x42, 0x00, DerefOf (M200 (0x01)), 0x01)
                            M680 (Arg0, 0x43, 0x00, DerefOf (P690 [0x01]), "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            DerefOf (M200 (0x01)) = DerefOf (P690 [0x02])
                            M680 (Arg0, 0x44, 0x00, DerefOf (M200 (0x01)), 0x01)
                            M680 (Arg0, 0x45, 0x00, DerefOf (P690 [0x02]), Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x06)
                {
                    /* Derefof of Indexed Reference returned by called Method */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            DerefOf (M200 (0x01)) = DerefOf (M681 (P690, 0x03))
                            M680 (Arg0, 0x48, 0x00, DerefOf (M200 (0x01)), 0x01)
                            M680 (Arg0, 0x49, 0x00, DerefOf (P690 [0x03]), 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            DerefOf (M200 (0x01)) = DerefOf (M681 (P690, 0x04))
                            M680 (Arg0, 0x4A, 0x00, DerefOf (M200 (0x01)), 0x01)
                            M680 (Arg0, 0x4B, 0x00, DerefOf (P690 [0x04]), "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            DerefOf (M200 (0x01)) = DerefOf (M681 (P690, 0x05))
                            M680 (Arg0, 0x4C, 0x00, DerefOf (M200 (0x01)), 0x01)
                            M680 (Arg0, 0x4D, 0x00, DerefOf (P690 [0x05]), Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x07)
                {
                    /* Result Object returned by called Method */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            DerefOf (M200 (0x01)) = M682 (Arg2, 0x02)
                            M680 (Arg0, 0x50, 0x00, DerefOf (M200 (0x01)), 0x01)
                            M680 (Arg0, 0x51, 0x00, I6E2, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            DerefOf (M200 (0x01)) = M682 (Arg2, 0x02)
                            M680 (Arg0, 0x52, 0x00, DerefOf (M200 (0x01)), 0x01)
                            M680 (Arg0, 0x53, 0x00, S6E2, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            DerefOf (M200 (0x01)) = M682 (Arg2, 0x02)
                            M680 (Arg0, 0x54, 0x00, DerefOf (M200 (0x01)), 0x01)
                            M680 (Arg0, 0x55, 0x00, B6E2, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x08)
                {
                    /* Result Object returned by any Operator (Op) */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            Store ((I6E3 + 0x00), DerefOf (M200 (0x01)))
                            M680 (Arg0, 0x58, 0x00, DerefOf (M200 (0x01)), 0x01)
                            M680 (Arg0, 0x59, 0x00, I6E3, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            DerefOf (M200 (0x01)) = Mid (S6E3, 0x02, 0x0E)
                            M680 (Arg0, 0x5A, 0x00, DerefOf (M200 (0x01)), 0x01)
                            M680 (Arg0, 0x5B, 0x00, S6E3, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            DerefOf (M200 (0x01)) = Mid (B6E3, 0x01, 0x07)
                            M680 (Arg0, 0x5C, 0x00, DerefOf (M200 (0x01)), 0x01)
                            M680 (Arg0, 0x5D, 0x00, B6E3, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                /* Additionally can be implemented cases: */
                /* Derefof of immediate Refof */
                /* Derefof of intermediate Object */
                /* Derefof of Reference returned by called Method */
                Default
                {
                    Debug = "Unexpected way to obtain some result Object"
                    ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                    Return (0x01)
                }

            }

            Return (0x00)
        }

        /* Store() Result Object to Integer Named Object */

        Method (M011, 3, Serialized)
        {
            /* ArgX as a way to obtain some result object */

            Method (M000, 5, Serialized)
            {
                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        M680 (Arg0, 0x61, 0x00, I680, 0xA0A1A2A35F5E5D80)
                        I680 = Arg2
                        M680 (Arg0, 0x62, 0x00, I680, 0xFE7CB391D650A284)
                        I680 = 0xC179B3FE
                        M680 (Arg0, 0x63, 0x00, I680, 0xC179B3FE)
                        M680 (Arg0, 0x64, 0x00, Arg2, 0xFE7CB391D650A284)
                    }
                    Case (0x02)
                    {
                        /* String */

                        M680 (Arg0, 0x65, 0x00, I681, 0xA0A1A2A35F5E5D81)
                        I681 = Arg3
                        If (Y602)
                        {
                            If (F64)
                            {
                                I000 = 0xFE7CB391D650A284
                            }
                            Else
                            {
                                I000 = 0xFE7CB391
                            }
                        }
                        Else
                        {
                            I000 = 0xFE7CB391D650A284
                        }

                        M680 (Arg0, 0x66, 0x00, I681, I000)
                        I681 = "C179B3FE"
                        M680 (Arg0, 0x67, 0x00, I681, 0xC179B3FE)
                        M680 (Arg0, 0x68, 0x00, Arg3, "FE7CB391D650A284")
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        M680 (Arg0, 0x69, 0x00, I682, 0xA0A1A2A35F5E5D82)
                        I682 = Arg4
                        M680 (Arg0, 0x6A, 0x00, I682, 0xFE7CB391D650A284)
                        I682 = Buffer (0x04)
                            {
                                 0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                            }
                        M680 (Arg0, 0x6B, 0x00, I682, 0xC179B3FE)
                        M680 (Arg0, 0x6C, 0x00, Arg4, Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                    }
                    Case (0x05)
                    {
                        /* Field Unit */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }
                    Case (0x0E)
                    {
                        /* Buffer Field */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }

                }

                Return (0x00)
            }

            /* Reference in ArgX as a way to obtain some result object */

            Method (M001, 5, Serialized)
            {
                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        M680 (Arg0, 0x6F, 0x00, I683, 0xA0A1A2A35F5E5D83)
                        I683 = DerefOf (Arg2)
                        M680 (Arg0, 0x70, 0x00, I683, 0xFE7CB391D650A284)
                        I683 = 0xC179B3FE
                        M680 (Arg0, 0x71, 0x00, I683, 0xC179B3FE)
                        M680 (Arg0, 0x72, 0x00, DerefOf (Arg2), 0xFE7CB391D650A284)
                    }
                    Case (0x02)
                    {
                        /* String */

                        M680 (Arg0, 0x73, 0x00, I684, 0xA0A1A2A35F5E5D84)
                        I684 = DerefOf (Arg3)
                        If (Y602)
                        {
                            If (F64)
                            {
                                I000 = 0xFE7CB391D650A284
                            }
                            Else
                            {
                                I000 = 0xFE7CB391
                            }
                        }
                        Else
                        {
                            I000 = 0xFE7CB391D650A284
                        }

                        M680 (Arg0, 0x74, 0x00, I684, I000)
                        I684 = "C179B3FE"
                        M680 (Arg0, 0x75, 0x00, I684, 0xC179B3FE)
                        M680 (Arg0, 0x76, 0x00, DerefOf (Arg3), "FE7CB391D650A284")
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        M680 (Arg0, 0x77, 0x00, I685, 0xA0A1A2A35F5E5D85)
                        I685 = DerefOf (Arg4)
                        M680 (Arg0, 0x78, 0x00, I685, 0xFE7CB391D650A284)
                        I685 = Buffer (0x04)
                            {
                                 0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                            }
                        M680 (Arg0, 0x79, 0x00, I685, 0xC179B3FE)
                        M680 (Arg0, 0x7A, 0x00, DerefOf (Arg4), Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                    }
                    Case (0x05)
                    {
                        /* Field Unit */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }
                    Case (0x0E)
                    {
                        /* Buffer Field */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }

                }

                Return (0x00)
            }

            /* Choose a way to obtain some result object */

            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    /* Data Image */
                    /* Choose a type of the result Object and specific source */
                    /* objects to obtain the result Object of the specified type. */
                    /* Check that the destination Object is properly initialized. */
                    /* Perform storing expression and check result. */
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x7D, 0x00, I686, 0xA0A1A2A35F5E5D86)
                            I686 = 0xFE7CB391D650A284
                            M680 (Arg0, 0x7E, 0x00, I686, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x7F, 0x00, I687, 0xA0A1A2A35F5E5D87)
                            I687 = "FE7CB391D650A284"
                            If (Y602)
                            {
                                If (F64)
                                {
                                    I000 = 0xFE7CB391D650A284
                                }
                                Else
                                {
                                    I000 = 0xFE7CB391
                                }
                            }
                            Else
                            {
                                I000 = 0xFE7CB391D650A284
                            }

                            M680 (Arg0, 0x80, 0x00, I687, I000)
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x81, 0x00, I688, 0xA0A1A2A35F5E5D88)
                            I688 = Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                }
                            M680 (Arg0, 0x82, 0x00, I688, 0xFE7CB391D650A284)
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x01)
                {
                    /* Named Object */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x85, 0x00, I689, 0xA0A1A2A35F5E5D89)
                            I689 = I6E0 /* \I6E0 */
                            M680 (Arg0, 0x86, 0x00, I689, 0xFE7CB391D650A284)
                            I689 = 0xC179B3FE
                            M680 (Arg0, 0x87, 0x00, I689, 0xC179B3FE)
                            M680 (Arg0, 0x88, 0x00, I6E0, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x89, 0x00, I68A, 0xA0A1A2A35F5E5D8A)
                            I68A = S6E0 /* \S6E0 */
                            If (Y602)
                            {
                                If (F64)
                                {
                                    I000 = 0xFE7CB391D650A284
                                }
                                Else
                                {
                                    I000 = 0xFE7CB391
                                }
                            }
                            Else
                            {
                                I000 = 0xFE7CB391D650A284
                            }

                            M680 (Arg0, 0x8A, 0x00, I68A, I000)
                            I68A = "C179B3FE"
                            M680 (Arg0, 0x8B, 0x00, I68A, 0xC179B3FE)
                            M680 (Arg0, 0x8C, 0x00, S6E0, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x8D, 0x00, I68B, 0xA0A1A2A35F5E5D8B)
                            I68B = B6E0 /* \B6E0 */
                            M680 (Arg0, 0x8E, 0x00, I68B, 0xFE7CB391D650A284)
                            I68B = Buffer (0x04)
                                {
                                     0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                                }
                            M680 (Arg0, 0x8F, 0x00, I68B, 0xC179B3FE)
                            M680 (Arg0, 0x90, 0x00, B6E0, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case                        /*
                         // Removed 09/2015: iASL now disallows store of package to integer
                         Case(4) {	// Package
                         Store(Package(){0xfe7cb391d650a284}, i684)
                         }
                         */
 (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x02)
                {
                    /* Method ArgX Object */

                    M000 (Concatenate (Arg0, "-m000"), Arg2, 0xFE7CB391D650A284, "FE7CB391D650A284", Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                        })
                }
                Case (0x03)
                {
                    /* Method LocalX Object */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            Local0 = 0xFE7CB391D650A284
                        }
                        Case (0x02)
                        {
                            /* String */

                            Local0 = "FE7CB391D650A284"
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            Local0 = Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                }
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x95, 0x00, I68C, 0xA0A1A2A35F5E5D8C)
                            I68C = Local0
                            M680 (Arg0, 0x96, 0x00, I68C, 0xFE7CB391D650A284)
                            I68C = 0xC179B3FE
                            M680 (Arg0, 0x97, 0x00, I68C, 0xC179B3FE)
                            M680 (Arg0, 0x98, 0x00, Local0, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x99, 0x00, I68D, 0xA0A1A2A35F5E5D8D)
                            I68D = Local0
                            If (Y602)
                            {
                                If (F64)
                                {
                                    I000 = 0xFE7CB391D650A284
                                }
                                Else
                                {
                                    I000 = 0xFE7CB391
                                }
                            }
                            Else
                            {
                                I000 = 0xFE7CB391D650A284
                            }

                            M680 (Arg0, 0x9A, 0x00, I68D, I000)
                            I68D = "C179B3FE"
                            M680 (Arg0, 0x9B, 0x00, I68D, 0xC179B3FE)
                            M680 (Arg0, 0x9C, 0x00, Local0, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x9D, 0x00, I68E, 0xA0A1A2A35F5E5D8E)
                            I68E = Local0
                            M680 (Arg0, 0x9E, 0x00, I68E, 0xFE7CB391D650A284)
                            I68E = Buffer (0x04)
                                {
                                     0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                                }
                            M680 (Arg0, 0x9F, 0x00, I68E, 0xC179B3FE)
                            M680 (Arg0, 0xA0, 0x00, Local0, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }

                    }
                }
                Case (0x04)
                {
                    /* Derefof of intermediate Object (Method ArgX Object) */

                    M001 (Concatenate (Arg0, "-m001"), Arg2, RefOf (I6E1), RefOf (S6E1), RefOf (B6E1))
                }
                Case (0x05)
                {
                    /* Derefof of immediate Index(...) */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0xA1, 0x00, I68F, 0xA0A1A2A35F5E5D8F)
                            I68F = DerefOf (P690 [0x00])
                            M680 (Arg0, 0xA2, 0x00, I68F, 0xFE7CB391D650A284)
                            I68F = 0xC179B3FE
                            M680 (Arg0, 0xA3, 0x00, I68F, 0xC179B3FE)
                            M680 (Arg0, 0xA4, 0x00, DerefOf (P690 [0x00]), 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0xA5, 0x00, I690, 0xA0A1A2A35F5E5D90)
                            I690 = DerefOf (P690 [0x01])
                            If (Y602)
                            {
                                If (F64)
                                {
                                    I000 = 0xFE7CB391D650A284
                                }
                                Else
                                {
                                    I000 = 0xFE7CB391
                                }
                            }
                            Else
                            {
                                I000 = 0xFE7CB391D650A284
                            }

                            M680 (Arg0, 0xA6, 0x00, I690, I000)
                            I690 = "C179B3FE"
                            M680 (Arg0, 0xA7, 0x00, I690, 0xC179B3FE)
                            M680 (Arg0, 0xA8, 0x00, DerefOf (P690 [0x01]), "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0xA9, 0x00, I691, 0xA0A1A2A35F5E5D91)
                            I691 = DerefOf (P690 [0x02])
                            M680 (Arg0, 0xAA, 0x00, I691, 0xFE7CB391D650A284)
                            I691 = Buffer (0x04)
                                {
                                     0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                                }
                            M680 (Arg0, 0xAB, 0x00, I691, 0xC179B3FE)
                            M680 (Arg0, 0xAC, 0x00, DerefOf (P690 [0x02]), Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x06)
                {
                    /* Derefof of Indexed Reference returned by called Method */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0xAF, 0x00, I692, 0xA0A1A2A35F5E5D92)
                            I692 = DerefOf (M681 (P690, 0x03))
                            M680 (Arg0, 0xB0, 0x00, I692, 0xFE7CB391D650A284)
                            I692 = 0xC179B3FE
                            M680 (Arg0, 0xB1, 0x00, I692, 0xC179B3FE)
                            M680 (Arg0, 0xB2, 0x00, DerefOf (P690 [0x03]), 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0xB3, 0x00, I693, 0xA0A1A2A35F5E5D93)
                            I693 = DerefOf (M681 (P690, 0x04))
                            If (Y602)
                            {
                                If (F64)
                                {
                                    I000 = 0xFE7CB391D650A284
                                }
                                Else
                                {
                                    I000 = 0xFE7CB391
                                }
                            }
                            Else
                            {
                                I000 = 0xFE7CB391D650A284
                            }

                            M680 (Arg0, 0xB4, 0x00, I693, I000)
                            I693 = "C179B3FE"
                            M680 (Arg0, 0xB5, 0x00, I693, 0xC179B3FE)
                            M680 (Arg0, 0xB6, 0x00, DerefOf (P690 [0x04]), "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0xB7, 0x00, I694, 0xA0A1A2A35F5E5D94)
                            I694 = DerefOf (M681 (P690, 0x05))
                            M680 (Arg0, 0xB8, 0x00, I694, 0xFE7CB391D650A284)
                            I694 = Buffer (0x04)
                                {
                                     0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                                }
                            M680 (Arg0, 0xB9, 0x00, I694, 0xC179B3FE)
                            M680 (Arg0, 0xBA, 0x00, DerefOf (P690 [0x05]), Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x07)
                {
                    /* Result Object returned by called Method */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0xBD, 0x00, I695, 0xA0A1A2A35F5E5D95)
                            I695 = M682 (Arg2, 0x02)
                            M680 (Arg0, 0xBE, 0x00, I695, 0xFE7CB391D650A284)
                            I695 = 0xC179B3FE
                            M680 (Arg0, 0xBF, 0x00, I695, 0xC179B3FE)
                            M680 (Arg0, 0xC0, 0x00, I6E2, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0xC1, 0x00, I696, 0xA0A1A2A35F5E5D96)
                            I696 = M682 (Arg2, 0x02)
                            If (Y602)
                            {
                                If (F64)
                                {
                                    I000 = 0xFE7CB391D650A284
                                }
                                Else
                                {
                                    I000 = 0xFE7CB391
                                }
                            }
                            Else
                            {
                                I000 = 0xFE7CB391D650A284
                            }

                            M680 (Arg0, 0xC2, 0x00, I696, I000)
                            I696 = "C179B3FE"
                            M680 (Arg0, 0xC3, 0x00, I696, 0xC179B3FE)
                            M680 (Arg0, 0xC4, 0x00, S6E2, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0xC5, 0x00, I697, 0xA0A1A2A35F5E5D97)
                            I697 = M682 (Arg2, 0x02)
                            M680 (Arg0, 0xC6, 0x00, I697, 0xFE7CB391D650A284)
                            I697 = Buffer (0x04)
                                {
                                     0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                                }
                            M680 (Arg0, 0xC7, 0x00, I697, 0xC179B3FE)
                            M680 (Arg0, 0xC8, 0x00, B6E2, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x08)
                {
                    /* Result Object returned by any Operator (Op) */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0xCB, 0x00, I698, 0xA0A1A2A35F5E5D98)
                            Store ((I6E3 + 0x00), I698) /* \I698 */
                            M680 (Arg0, 0xCC, 0x00, I698, 0xFE7CB391D650A284)
                            I698 = 0xC179B3FE
                            M680 (Arg0, 0xCD, 0x00, I698, 0xC179B3FE)
                            M680 (Arg0, 0xCE, 0x00, I6E3, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0xCF, 0x00, I699, 0xA0A1A2A35F5E5D99)
                            I699 = Mid (S6E3, 0x02, 0x0E)
                            If (Y602)
                            {
                                If (F64)
                                {
                                    I000 = 0x007CB391D650A284
                                }
                                Else
                                {
                                    I000 = 0x7CB391D6
                                }
                            }
                            Else
                            {
                                I000 = 0x007CB391D650A284
                            }

                            M680 (Arg0, 0xD0, 0x00, I699, I000)
                            I699 = "C179B3FE"
                            M680 (Arg0, 0xD1, 0x00, I699, 0xC179B3FE)
                            M680 (Arg0, 0xD2, 0x00, S6E3, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0xD3, 0x00, I69A, 0xA0A1A2A35F5E5D9A)
                            I69A = Mid (B6E3, 0x01, 0x07)
                            M680 (Arg0, 0xD4, 0x00, I69A, 0x00FE7CB391D650A2)
                            I69A = Buffer (0x04)
                                {
                                     0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                                }
                            M680 (Arg0, 0xD5, 0x00, I69A, 0xC179B3FE)
                            M680 (Arg0, 0xD6, 0x00, B6E3, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                /* Additionally can be implemented cases: */
                /* Derefof of immediate Refof */
                /* Derefof of intermediate Object */
                /* Derefof of Reference returned by called Method */
                Default
                {
                    Debug = "Unexpected way to obtain some result Object"
                    ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                    Return (0x01)
                }

            }

            Return (0x00)
        }

        /* Store() Result Object to Integer Method LocalX Object */

        Method (M013, 3, Serialized)
        {
            /* ArgX as a way to obtain some result object */

            Method (M000, 5, Serialized)
            {
                Local1 = 0xA0A1A2A35F5E5D5C
                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        M680 (Arg0, 0xDA, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                        Local1 = Arg2
                        If (F64)
                        {
                            M680 (Arg0, 0xDB, 0x00, Local1, 0xFE7CB391D650A284)
                        }
                        Else
                        {
                            M680 (Arg0, 0xDC, 0x00, Local1, 0xD650A284)
                        }

                        Local1 = 0xC179B3FE
                        M680 (Arg0, 0xDD, 0x00, Local1, 0xC179B3FE)
                        M680 (Arg0, 0xDE, 0x00, Arg2, 0xFE7CB391D650A284)
                    }
                    Case (0x02)
                    {
                        /* String */

                        M680 (Arg0, 0xDF, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                        Local1 = Arg3
                        M680 (Arg0, 0xE0, 0x00, Local1, "FE7CB391D650A284")
                        Local1 [0x03] = 0x0B
                        M680 (Arg0, 0xE1, 0x00, Local1, "FE7\vB391D650A284")
                        M680 (Arg0, 0xE2, 0x00, Arg3, "FE7CB391D650A284")
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        M680 (Arg0, 0xE3, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                        Local1 = Arg4
                        M680 (Arg0, 0xE4, 0x00, Local1, Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                        Local1 [0x03] = 0x0B
                        M680 (Arg0, 0xE5, 0x00, Local1, Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                        M680 (Arg0, 0xE6, 0x00, Arg4, Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                    }
                    Case (0x05)
                    {
                        /* Field Unit */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }
                    Case (0x0E)
                    {
                        /* Buffer Field */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }

                }

                Return (0x00)
            }

            /* Reference in ArgX as a way to obtain some result object */

            Method (M001, 5, Serialized)
            {
                Local1 = 0xA0A1A2A35F5E5D5C
                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        M680 (Arg0, 0xE9, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                        Local1 = DerefOf (Arg2)
                        If (F64)
                        {
                            M680 (Arg0, 0xEA, 0x00, Local1, 0xFE7CB391D650A284)
                        }
                        Else
                        {
                            M680 (Arg0, 0xEB, 0x00, Local1, 0xD650A284)
                        }

                        Local1 = 0xC179B3FE
                        M680 (Arg0, 0xEC, 0x00, Local1, 0xC179B3FE)
                        M680 (Arg0, 0xED, 0x00, DerefOf (Arg2), 0xFE7CB391D650A284)
                    }
                    Case (0x02)
                    {
                        /* String */

                        M680 (Arg0, 0xEE, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                        Local1 = DerefOf (Arg3)
                        M680 (Arg0, 0xEF, 0x00, Local1, "FE7CB391D650A284")
                        Local1 [0x03] = 0x0B
                        M680 (Arg0, 0xF0, 0x00, Local1, "FE7\vB391D650A284")
                        M680 (Arg0, 0xF1, 0x00, DerefOf (Arg3), "FE7CB391D650A284")
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        M680 (Arg0, 0xF2, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                        Local1 = DerefOf (Arg4)
                        M680 (Arg0, 0xF3, 0x00, Local1, Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                        Local1 [0x03] = 0x0B
                        M680 (Arg0, 0xF4, 0x00, Local1, Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                        M680 (Arg0, 0xF5, 0x00, DerefOf (Arg4), Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                    }
                    Case (0x05)
                    {
                        /* Field Unit */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }
                    Case (0x0E)
                    {
                        /* Buffer Field */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }

                }

                Return (0x00)
            }

            Local1 = 0xA0A1A2A35F5E5D5C
            /* Choose a way to obtain some result object */

            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    /* Data Image */
                    /* Choose a type of the result Object and specific source */
                    /* objects to obtain the result Object of the specified type. */
                    /* Check that the destination Object is properly initialized. */
                    /* Perform storing expression and check result. */
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0xF8, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = 0xFE7CB391D650A284
                            If (F64)
                            {
                                M680 (Arg0, 0xF9, 0x00, Local1, 0xFE7CB391D650A284)
                            }
                            Else
                            {
                                M680 (Arg0, 0xFA, 0x00, Local1, 0xD650A284)
                            }
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0xFB, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = "FE7CB391D650A284"
                            M680 (Arg0, 0xFC, 0x00, Local1, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0xFD, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                }
                            M680 (Arg0, 0xFE, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x01)
                {
                    /* Named Object */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x0101, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = I6E4 /* \I6E4 */
                            If (F64)
                            {
                                M680 (Arg0, 0x0102, 0x00, Local1, 0xFE7CB391D650A284)
                            }
                            Else
                            {
                                M680 (Arg0, 0x0103, 0x00, Local1, 0xD650A284)
                            }

                            Local1 = 0xC179B3FE
                            M680 (Arg0, 0x0104, 0x00, Local1, 0xC179B3FE)
                            M680 (Arg0, 0x0105, 0x00, I6E4, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x0106, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = S6E4 /* \S6E4 */
                            M680 (Arg0, 0x0107, 0x00, Local1, "FE7CB391D650A284")
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0108, 0x00, Local1, "FE7\vB391D650A284")
                            M680 (Arg0, 0x0109, 0x00, S6E4, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x010A, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = B6E4 /* \B6E4 */
                            M680 (Arg0, 0x010B, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x010C, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            M680 (Arg0, 0x010D, 0x00, B6E4, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Default
                        {
                            Debug = "Unexpected type of the result Object to be stored"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x02)
                {
                    /* Method ArgX Object */

                    M000 (Concatenate (Arg0, "-m000"), Arg2, 0xFE7CB391D650A284, "FE7CB391D650A284", Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                        })
                }
                Case (0x03)
                {
                    /* Method LocalX Object */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x00)
                        {
                            /* Stuff */

                            Return (0x00)
                        }
                        Case (0x01)
                        {
                            /* Integer */

                            Local0 = 0xFE7CB391D650A284
                        }
                        Case (0x02)
                        {
                            /* String */

                            Local0 = "FE7CB391D650A284"
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            Local0 = Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                }
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x0111, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = Local0
                            If (F64)
                            {
                                M680 (Arg0, 0x0112, 0x00, Local1, 0xFE7CB391D650A284)
                            }
                            Else
                            {
                                M680 (Arg0, 0x0113, 0x00, Local1, 0xD650A284)
                            }

                            Local1 = 0xC179B3FE
                            M680 (Arg0, 0x0114, 0x00, Local1, 0xC179B3FE)
                            M680 (Arg0, 0x0115, 0x00, Local0, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x0116, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = Local0
                            M680 (Arg0, 0x0117, 0x00, Local1, "FE7CB391D650A284")
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0118, 0x00, Local1, "FE7\vB391D650A284")
                            M680 (Arg0, 0x0119, 0x00, Local0, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x011A, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = Local0
                            M680 (Arg0, 0x011B, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x011C, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            M680 (Arg0, 0x011D, 0x00, Local0, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }

                    }
                }
                Case (0x04)
                {
                    /* Derefof of intermediate Object (Method ArgX Object) */

                    M001 (Concatenate (Arg0, "-m001"), Arg2, RefOf (I6E5), RefOf (S6E5), RefOf (B6E5))
                }
                Case (0x05)
                {
                    /* Derefof of immediate Index(...) */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x011E, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = DerefOf (P690 [0x06])
                            If (F64)
                            {
                                M680 (Arg0, 0x011F, 0x00, Local1, 0xFE7CB391D650A284)
                            }
                            Else
                            {
                                M680 (Arg0, 0x0120, 0x00, Local1, 0xD650A284)
                            }

                            Local1 = 0xC179B3FE
                            M680 (Arg0, 0x0121, 0x00, Local1, 0xC179B3FE)
                            M680 (Arg0, 0x0122, 0x00, DerefOf (P690 [0x06]), 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x0123, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = DerefOf (P690 [0x07])
                            M680 (Arg0, 0x0124, 0x00, Local1, "FE7CB391D650A284")
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0125, 0x00, Local1, "FE7\vB391D650A284")
                            M680 (Arg0, 0x0126, 0x00, DerefOf (P690 [0x07]), "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x0127, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = DerefOf (P690 [0x08])
                            M680 (Arg0, 0x0128, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0129, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            M680 (Arg0, 0x012A, 0x00, DerefOf (P690 [0x08]), Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x06)
                {
                    /* Derefof of Indexed Reference returned by called Method */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x012D, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = DerefOf (M681 (P690, 0x09))
                            If (F64)
                            {
                                M680 (Arg0, 0x012E, 0x00, Local1, 0xFE7CB391D650A284)
                            }
                            Else
                            {
                                M680 (Arg0, 0x012F, 0x00, Local1, 0xD650A284)
                            }

                            Local1 = 0xC179B3FE
                            M680 (Arg0, 0x0130, 0x00, Local1, 0xC179B3FE)
                            M680 (Arg0, 0x0131, 0x00, DerefOf (P690 [0x09]), 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x0132, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = DerefOf (M681 (P690, 0x0A))
                            M680 (Arg0, 0x0133, 0x00, Local1, "FE7CB391D650A284")
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0134, 0x00, Local1, "FE7\vB391D650A284")
                            M680 (Arg0, 0x0135, 0x00, DerefOf (P690 [0x0A]), "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x0136, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = DerefOf (M681 (P690, 0x0B))
                            M680 (Arg0, 0x0137, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0138, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            M680 (Arg0, 0x0139, 0x00, DerefOf (P690 [0x0B]), Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }

                    }
                }
                Case (0x07)
                {
                    /* Result Object returned by called Method */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x013A, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = M682 (Arg2, 0x06)
                            If (F64)
                            {
                                M680 (Arg0, 0x013B, 0x00, Local1, 0xFE7CB391D650A284)
                            }
                            Else
                            {
                                M680 (Arg0, 0x013C, 0x00, Local1, 0xD650A284)
                            }

                            Local1 = 0xC179B3FE
                            M680 (Arg0, 0x013D, 0x00, Local1, 0xC179B3FE)
                            M680 (Arg0, 0x013E, 0x00, I6E6, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x013F, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = M682 (Arg2, 0x06)
                            M680 (Arg0, 0x0140, 0x00, Local1, "FE7CB391D650A284")
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0141, 0x00, Local1, "FE7\vB391D650A284")
                            M680 (Arg0, 0x0142, 0x00, S6E6, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x0143, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = M682 (Arg2, 0x06)
                            M680 (Arg0, 0x0144, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0145, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            M680 (Arg0, 0x0146, 0x00, B6E6, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x08)
                {
                    /* Result Object returned by any Operator (Op): */
                    /* Add, Mid */
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x0149, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Store ((I6E7 + 0x00), Local1)
                            If (F64)
                            {
                                M680 (Arg0, 0x014A, 0x00, Local1, 0xFE7CB391D650A284)
                            }
                            Else
                            {
                                M680 (Arg0, 0x014B, 0x00, Local1, 0xD650A284)
                            }

                            Local1 = 0xC179B3FE
                            M680 (Arg0, 0x014C, 0x00, Local1, 0xC179B3FE)
                            M680 (Arg0, 0x014D, 0x00, I6E7, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x014E, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = Mid (S6E7, 0x02, 0x0E)
                            M680 (Arg0, 0x014F, 0x00, Local1, "7CB391D650A284")
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0150, 0x00, Local1, "7CB\v91D650A284")
                            M680 (Arg0, 0x0151, 0x00, S6E7, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x0152, 0x00, Local1, 0xA0A1A2A35F5E5D5C)
                            Local1 = Mid (B6E7, 0x01, 0x07)
                            M680 (Arg0, 0x0153, 0x00, Local1, Buffer (0x07)
                                {
                                     0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE         // .P...|.
                                })
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0154, 0x00, Local1, Buffer (0x07)
                                {
                                     0xA2, 0x50, 0xD6, 0x0B, 0xB3, 0x7C, 0xFE         // .P...|.
                                })
                            M680 (Arg0, 0x0155, 0x00, B6E7, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                /* Additionally can be implemented cases: */
                /* Derefof of immediate Refof */
                /* Derefof of intermediate Object */
                /* Derefof of Reference returned by called Method */
                Default
                {
                    Debug = "Unexpected way to obtain some result Object"
                    ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                    Return (0x01)
                }

            }

            Return (0x00)
        }

        /* Store() Result Object to String Named Object */

        Method (M021, 3, Serialized)
        {
            /* ArgX as a way to obtain some result object */

            Method (M000, 5, Serialized)
            {
                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        M680 (Arg0, 0x0159, 0x00, S680, "initial named string80")
                        S680 = Arg2
                        If (F64)
                        {
                            M680 (Arg0, 0x015A, 0x00, S680, "FE7CB391D650A284")
                        }
                        Else
                        {
                            M680 (Arg0, 0x015B, 0x00, S680, "D650A284")
                        }

                        S680 [0x03] = 0x0B
                        If (F64)
                        {
                            M680 (Arg0, 0x015C, 0x00, S680, "FE7\vB391D650A284")
                        }
                        Else
                        {
                            M680 (Arg0, 0x015D, 0x00, S680, "D65\vA284")
                        }

                        M680 (Arg0, 0x015E, 0x00, Arg2, 0xFE7CB391D650A284)
                    }
                    Case (0x02)
                    {
                        /* String */

                        M680 (Arg0, 0x015F, 0x00, S681, "initial named string81")
                        S681 = Arg3
                        M680 (Arg0, 0x0160, 0x00, S681, "FE7CB391D650A284")
                        S681 [0x03] = 0x0B
                        M680 (Arg0, 0x0161, 0x00, S681, "FE7\vB391D650A284")
                        M680 (Arg0, 0x0162, 0x00, Arg3, "FE7CB391D650A284")
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        M680 (Arg0, 0x0163, 0x00, S682, "initial named string82")
                        S682 = Arg4
                        M680 (Arg0, 0x0164, 0x00, S682, "84 A2 50 D6 91 B3 7C FE")
                        S682 [0x03] = 0x0B
                        M680 (Arg0, 0x0165, 0x00, S682, "84 \v2 50 D6 91 B3 7C FE")
                        M680 (Arg0, 0x0166, 0x00, Arg4, Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                    }
                    Case (0x05)
                    {
                        /* Field Unit */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }
                    Case (0x0E)
                    {
                        /* Buffer Field */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }

                }

                Return (0x00)
            }

            /* Reference in ArgX as a way to obtain some result object */

            Method (M001, 5, Serialized)
            {
                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        M680 (Arg0, 0x0169, 0x00, S683, "initial named string83")
                        S683 = DerefOf (Arg2)
                        If (F64)
                        {
                            M680 (Arg0, 0x016A, 0x00, S683, "FE7CB391D650A284")
                        }
                        Else
                        {
                            M680 (Arg0, 0x016B, 0x00, S683, "D650A284")
                        }

                        S683 [0x03] = 0x0B
                        If (F64)
                        {
                            M680 (Arg0, 0x016C, 0x00, S683, "FE7\vB391D650A284")
                        }
                        Else
                        {
                            M680 (Arg0, 0x016D, 0x00, S683, "D65\vA284")
                        }

                        M680 (Arg0, 0x016E, 0x00, DerefOf (Arg2), 0xFE7CB391D650A284)
                    }
                    Case (0x02)
                    {
                        /* String */

                        M680 (Arg0, 0x016F, 0x00, S684, "initial named string84")
                        S684 = DerefOf (Arg3)
                        M680 (Arg0, 0x0170, 0x00, S684, "FE7CB391D650A284")
                        S684 [0x03] = 0x0B
                        M680 (Arg0, 0x0171, 0x00, S684, "FE7\vB391D650A284")
                        M680 (Arg0, 0x0172, 0x00, DerefOf (Arg3), "FE7CB391D650A284")
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        M680 (Arg0, 0x0173, 0x00, S685, "initial named string85")
                        S685 = DerefOf (Arg4)
                        M680 (Arg0, 0x0174, 0x00, S685, "84 A2 50 D6 91 B3 7C FE")
                        S685 [0x03] = 0x0B
                        M680 (Arg0, 0x0175, 0x00, S685, "84 \v2 50 D6 91 B3 7C FE")
                        M680 (Arg0, 0x0176, 0x00, DerefOf (Arg4), Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                    }
                    Case (0x05)
                    {
                        /* Field Unit */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }
                    Case (0x0E)
                    {
                        /* Buffer Field */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }

                }

                Return (0x00)
            }

            /* Choose a way to obtain some result object */

            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    /* Data Image */
                    /* Choose a type of the result Object and specific source */
                    /* objects to obtain the result Object of the specified type. */
                    /* Check that the destination Object is properly initialized. */
                    /* Perform storing expression and check result. */
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x0179, 0x00, S686, "initial named string86")
                            S686 = 0xFE7CB391D650A284
                            If (F64)
                            {
                                M680 (Arg0, 0x017A, 0x00, S686, "FE7CB391D650A284")
                            }
                            Else
                            {
                                M680 (Arg0, 0x017B, 0x00, S686, "D650A284")
                            }
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x017C, 0x00, S687, "initial named string87")
                            S687 = "FE7CB391D650A284"
                            M680 (Arg0, 0x017D, 0x00, S687, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x017E, 0x00, S688, "initial named string88")
                            S688 = Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                }
                            M680 (Arg0, 0x017F, 0x00, S688, "84 A2 50 D6 91 B3 7C FE")
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x01)
                {
                    /* Named Object */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x0182, 0x00, S689, "initial named string89")
                            S689 = I6E4 /* \I6E4 */
                            If (F64)
                            {
                                M680 (Arg0, 0x0183, 0x00, S689, "FE7CB391D650A284")
                            }
                            Else
                            {
                                M680 (Arg0, 0x0184, 0x00, S689, "D650A284")
                            }

                            S689 [0x03] = 0x0B
                            If (F64)
                            {
                                M680 (Arg0, 0x0185, 0x00, S689, "FE7\vB391D650A284")
                            }
                            Else
                            {
                                M680 (Arg0, 0x0186, 0x00, S689, "D65\vA284")
                            }

                            M680 (Arg0, 0x0187, 0x00, I6E4, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x0188, 0x00, S68A, "initial named string8a")
                            S68A = S6E4 /* \S6E4 */
                            M680 (Arg0, 0x0189, 0x00, S68A, "FE7CB391D650A284")
                            S68A [0x03] = 0x0B
                            M680 (Arg0, 0x018A, 0x00, S68A, "FE7\vB391D650A284")
                            M680 (Arg0, 0x018B, 0x00, S6E4, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x018C, 0x00, S68B, "initial named string8b")
                            S68B = B6E4 /* \B6E4 */
                            M680 (Arg0, 0x018D, 0x00, S68B, "84 A2 50 D6 91 B3 7C FE")
                            S68B [0x03] = 0x0B
                            M680 (Arg0, 0x018E, 0x00, S68B, "84 \v2 50 D6 91 B3 7C FE")
                            M680 (Arg0, 0x018F, 0x00, B6E4, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x02)
                {
                    /* Method ArgX Object */

                    M000 (Concatenate (Arg0, "-m000"), Arg2, 0xFE7CB391D650A284, "FE7CB391D650A284", Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                        })
                }
                Case (0x03)
                {
                    /* Method LocalX Object */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            Local0 = 0xFE7CB391D650A284
                        }
                        Case (0x02)
                        {
                            /* String */

                            Local0 = "FE7CB391D650A284"
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            Local0 = Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                }
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x0194, 0x00, S68C, "initial named string8c")
                            S68C = Local0
                            If (F64)
                            {
                                M680 (Arg0, 0x0195, 0x00, S68C, "FE7CB391D650A284")
                            }
                            Else
                            {
                                M680 (Arg0, 0x0196, 0x00, S68C, "D650A284")
                            }

                            S68C [0x03] = 0x0B
                            If (F64)
                            {
                                M680 (Arg0, 0x0197, 0x00, S68C, "FE7\vB391D650A284")
                            }
                            Else
                            {
                                M680 (Arg0, 0x0198, 0x00, S68C, "D65\vA284")
                            }

                            M680 (Arg0, 0x0199, 0x00, Local0, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x019A, 0x00, S68D, "initial named string8d")
                            S68D = Local0
                            M680 (Arg0, 0x019B, 0x00, S68D, "FE7CB391D650A284")
                            S68D [0x03] = 0x0B
                            M680 (Arg0, 0x019C, 0x00, S68D, "FE7\vB391D650A284")
                            M680 (Arg0, 0x019D, 0x00, Local0, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x019E, 0x00, S68E, "initial named string8e")
                            S68E = Local0
                            M680 (Arg0, 0x019F, 0x00, S68E, "84 A2 50 D6 91 B3 7C FE")
                            S68E [0x03] = 0x0B
                            M680 (Arg0, 0x01A0, 0x00, S68E, "84 \v2 50 D6 91 B3 7C FE")
                            M680 (Arg0, 0x01A1, 0x00, Local0, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }

                    }
                }
                Case (0x04)
                {
                    /* Derefof of intermediate Object (Method ArgX Object) */

                    M001 (Concatenate (Arg0, "-m001"), Arg2, RefOf (I6E5), RefOf (S6E5), RefOf (B6E5))
                }
                Case (0x05)
                {
                    /* Derefof of immediate Index(...) */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x01A2, 0x00, S68F, "initial named string8f")
                            S68F = DerefOf (P690 [0x06])
                            If (F64)
                            {
                                M680 (Arg0, 0x01A3, 0x00, S68F, "FE7CB391D650A284")
                            }
                            Else
                            {
                                M680 (Arg0, 0x01A4, 0x00, S68F, "D650A284")
                            }

                            S68F [0x03] = 0x0B
                            If (F64)
                            {
                                M680 (Arg0, 0x01A5, 0x00, S68F, "FE7\vB391D650A284")
                            }
                            Else
                            {
                                M680 (Arg0, 0x01A6, 0x00, S68F, "D65\vA284")
                            }

                            M680 (Arg0, 0x01A7, 0x00, DerefOf (P690 [0x06]), 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x01A8, 0x00, S690, "initial named string90")
                            S690 = DerefOf (P690 [0x07])
                            M680 (Arg0, 0x01A9, 0x00, S690, "FE7CB391D650A284")
                            S690 [0x03] = 0x0B
                            M680 (Arg0, 0x01AA, 0x00, S690, "FE7\vB391D650A284")
                            M680 (Arg0, 0x01AB, 0x00, DerefOf (P690 [0x07]), "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x01AC, 0x00, S691, "initial named string91")
                            S691 = DerefOf (P690 [0x08])
                            M680 (Arg0, 0x01AD, 0x00, S691, "84 A2 50 D6 91 B3 7C FE")
                            S691 [0x03] = 0x0B
                            M680 (Arg0, 0x01AE, 0x00, S691, "84 \v2 50 D6 91 B3 7C FE")
                            M680 (Arg0, 0x01AF, 0x00, DerefOf (P690 [0x08]), Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x06)
                {
                    /* Derefof of Indexed Reference returned by called Method */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x01B2, 0x00, S692, "initial named string92")
                            S692 = DerefOf (M681 (P690, 0x09))
                            If (F64)
                            {
                                M680 (Arg0, 0x01B3, 0x00, S692, "FE7CB391D650A284")
                            }
                            Else
                            {
                                M680 (Arg0, 0x01B4, 0x00, S692, "D650A284")
                            }

                            S692 [0x03] = 0x0B
                            If (F64)
                            {
                                M680 (Arg0, 0x01B5, 0x00, S692, "FE7\vB391D650A284")
                            }
                            Else
                            {
                                M680 (Arg0, 0x01B6, 0x00, S692, "D65\vA284")
                            }

                            M680 (Arg0, 0x01B7, 0x00, DerefOf (P690 [0x09]), 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x01B8, 0x00, S693, "initial named string93")
                            S693 = DerefOf (M681 (P690, 0x0A))
                            M680 (Arg0, 0x01B9, 0x00, S693, "FE7CB391D650A284")
                            S693 [0x03] = 0x0B
                            M680 (Arg0, 0x01BA, 0x00, S693, "FE7\vB391D650A284")
                            M680 (Arg0, 0x01BB, 0x00, DerefOf (P690 [0x0A]), "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x01BC, 0x00, S694, "initial named string94")
                            S694 = DerefOf (M681 (P690, 0x0B))
                            M680 (Arg0, 0x01BD, 0x00, S694, "84 A2 50 D6 91 B3 7C FE")
                            S694 [0x03] = 0x0B
                            M680 (Arg0, 0x01BE, 0x00, S694, "84 \v2 50 D6 91 B3 7C FE")
                            M680 (Arg0, 0x01BF, 0x00, DerefOf (P690 [0x0B]), Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x07)
                {
                    /* Result Object returned by called Method */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x01C2, 0x00, S695, "initial named string95")
                            S695 = M682 (Arg2, 0x06)
                            If (F64)
                            {
                                M680 (Arg0, 0x01C3, 0x00, S695, "FE7CB391D650A284")
                            }
                            Else
                            {
                                M680 (Arg0, 0x01C4, 0x00, S695, "D650A284")
                            }

                            S695 [0x03] = 0x0B
                            If (F64)
                            {
                                M680 (Arg0, 0x01C5, 0x00, S695, "FE7\vB391D650A284")
                            }
                            Else
                            {
                                M680 (Arg0, 0x01C6, 0x00, S695, "D65\vA284")
                            }

                            M680 (Arg0, 0x01C7, 0x00, I6E6, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x01C8, 0x00, S696, "initial named string96")
                            S696 = M682 (Arg2, 0x06)
                            M680 (Arg0, 0x01C9, 0x00, S696, "FE7CB391D650A284")
                            S696 [0x03] = 0x0B
                            M680 (Arg0, 0x01CA, 0x00, S696, "FE7\vB391D650A284")
                            M680 (Arg0, 0x01CB, 0x00, S6E6, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x01CC, 0x00, S697, "initial named string97")
                            S697 = M682 (Arg2, 0x06)
                            M680 (Arg0, 0x01CD, 0x00, S697, "84 A2 50 D6 91 B3 7C FE")
                            S697 [0x03] = 0x0B
                            M680 (Arg0, 0x01CE, 0x00, S697, "84 \v2 50 D6 91 B3 7C FE")
                            M680 (Arg0, 0x01CF, 0x00, B6E6, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x08)
                {
                    /* Result Object returned by any Operator (Op): */
                    /* Add, Mid */
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x01D2, 0x00, S698, "initial named string98")
                            Store ((I6E7 + 0x00), S698) /* \S698 */
                            If (F64)
                            {
                                M680 (Arg0, 0x01D3, 0x00, S698, "FE7CB391D650A284")
                            }
                            Else
                            {
                                M680 (Arg0, 0x01D4, 0x00, S698, "D650A284")
                            }

                            S698 [0x03] = 0x0B
                            If (F64)
                            {
                                M680 (Arg0, 0x01D5, 0x00, S698, "FE7\vB391D650A284")
                            }
                            Else
                            {
                                M680 (Arg0, 0x01D6, 0x00, S698, "D65\vA284")
                            }

                            M680 (Arg0, 0x01D7, 0x00, I6E7, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x01D8, 0x00, S699, "initial named string99")
                            S699 = Mid (S6E7, 0x02, 0x0E)
                            M680 (Arg0, 0x01D9, 0x00, S699, "7CB391D650A284")
                            S699 [0x03] = 0x0B
                            M680 (Arg0, 0x01DA, 0x00, S699, "7CB\v91D650A284")
                            M680 (Arg0, 0x01DB, 0x00, S6E7, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x01DC, 0x00, S69A, "initial named string9a")
                            S69A = Mid (B6E7, 0x01, 0x07)
                            M680 (Arg0, 0x01DD, 0x00, S69A, "A2 50 D6 91 B3 7C FE")
                            S69A [0x03] = 0x0B
                            M680 (Arg0, 0x01DE, 0x00, S69A, "A2 \v0 D6 91 B3 7C FE")
                            M680 (Arg0, 0x01DF, 0x00, B6E7, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                /* Additionally can be implemented cases: */
                /* Derefof of immediate Refof */
                /* Derefof of intermediate Object */
                /* Derefof of Reference returned by called Method */
                Default
                {
                    Debug = "Unexpected way to obtain some result Object"
                    ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                    Return (0x01)
                }

            }

            Return (0x00)
        }

        /* Store() Result Object to Buffer Named Object */

        Method (M031, 3, Serialized)
        {
            /* ArgX as a way to obtain some result object */

            Method (M000, 5, Serialized)
            {
                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        M680 (Arg0, 0x01E3, 0x00, B680, Buffer (0x09)
                            {
                                /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                /* 0008 */  0x80                                             // .
                            })
                        B680 = Arg2
                        If (F64)
                        {
                            M680 (Arg0, 0x01E4, 0x00, B680, Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                    /* 0008 */  0x00                                             // .
                                })
                        }
                        Else
                        {
                            M680 (Arg0, 0x01E5, 0x00, B680, Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x00, 0x00, 0x00, 0x00,  // ..P.....
                                    /* 0008 */  0x00                                             // .
                                })
                        }

                        B680 [0x03] = 0x0B
                        If (F64)
                        {
                            M680 (Arg0, 0x01E6, 0x00, B680, Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                    /* 0008 */  0x00                                             // .
                                })
                        }
                        Else
                        {
                            M680 (Arg0, 0x01E7, 0x00, B680, Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x00, 0x00, 0x00, 0x00,  // ..P.....
                                    /* 0008 */  0x00                                             // .
                                })
                        }

                        M680 (Arg0, 0x01E8, 0x00, Arg2, 0xFE7CB391D650A284)
                    }
                    Case (0x02)
                    {
                        /* String */

                        M680 (Arg0, 0x01E9, 0x00, B681, Buffer (0x09)
                            {
                                /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                /* 0008 */  0x81                                             // .
                            })
                        B681 = Arg3
                        M680 (Arg0, 0x01EA, 0x00, B681, Buffer (0x09)
                            {
                                /* 0000 */  0x46, 0x45, 0x37, 0x43, 0x42, 0x33, 0x39, 0x31,  // FE7CB391
                                /* 0008 */  0x44                                             // D
                            })
                        B681 [0x03] = 0x0B
                        M680 (Arg0, 0x01EB, 0x00, B681, Buffer (0x09)
                            {
                                /* 0000 */  0x46, 0x45, 0x37, 0x0B, 0x42, 0x33, 0x39, 0x31,  // FE7.B391
                                /* 0008 */  0x44                                             // D
                            })
                        M680 (Arg0, 0x01EC, 0x00, Arg3, "FE7CB391D650A284")
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        M680 (Arg0, 0x01ED, 0x00, B682, Buffer (0x09)
                            {
                                /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                /* 0008 */  0x82                                             // .
                            })
                        B682 = Arg4
                        M680 (Arg0, 0x01EE, 0x00, B682, Buffer (0x09)
                            {
                                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                /* 0008 */  0x00                                             // .
                            })
                        B682 [0x03] = 0x0B
                        M680 (Arg0, 0x01EF, 0x00, B682, Buffer (0x09)
                            {
                                /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                /* 0008 */  0x00                                             // .
                            })
                        M680 (Arg0, 0x01F0, 0x00, Arg4, Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                    }
                    Case (0x05)
                    {
                        /* Field Unit */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }
                    Case (0x0E)
                    {
                        /* Buffer Field */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }

                }

                Return (0x00)
            }

            /* Reference in ArgX as a way to obtain some result object */

            Method (M001, 5, Serialized)
            {
                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        M680 (Arg0, 0x01F3, 0x00, B683, Buffer (0x09)
                            {
                                /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                /* 0008 */  0x83                                             // .
                            })
                        B683 = DerefOf (Arg2)
                        If (F64)
                        {
                            M680 (Arg0, 0x01F4, 0x00, B683, Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                    /* 0008 */  0x00                                             // .
                                })
                        }
                        Else
                        {
                            M680 (Arg0, 0x01F5, 0x00, B683, Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x00, 0x00, 0x00, 0x00,  // ..P.....
                                    /* 0008 */  0x00                                             // .
                                })
                        }

                        B683 [0x03] = 0x0B
                        If (F64)
                        {
                            M680 (Arg0, 0x01F6, 0x00, B683, Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                    /* 0008 */  0x00                                             // .
                                })
                        }
                        Else
                        {
                            M680 (Arg0, 0x01F7, 0x00, B683, Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x00, 0x00, 0x00, 0x00,  // ..P.....
                                    /* 0008 */  0x00                                             // .
                                })
                        }

                        M680 (Arg0, 0x01F8, 0x00, DerefOf (Arg2), 0xFE7CB391D650A284)
                    }
                    Case (0x02)
                    {
                        /* String */

                        M680 (Arg0, 0x01F9, 0x00, B684, Buffer (0x09)
                            {
                                /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                /* 0008 */  0x84                                             // .
                            })
                        B684 = DerefOf (Arg3)
                        M680 (Arg0, 0x01FA, 0x00, B684, Buffer (0x09)
                            {
                                /* 0000 */  0x46, 0x45, 0x37, 0x43, 0x42, 0x33, 0x39, 0x31,  // FE7CB391
                                /* 0008 */  0x44                                             // D
                            })
                        B684 [0x03] = 0x0B
                        M680 (Arg0, 0x01FB, 0x00, B684, Buffer (0x09)
                            {
                                /* 0000 */  0x46, 0x45, 0x37, 0x0B, 0x42, 0x33, 0x39, 0x31,  // FE7.B391
                                /* 0008 */  0x44                                             // D
                            })
                        M680 (Arg0, 0x01FC, 0x00, DerefOf (Arg3), "FE7CB391D650A284")
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        M680 (Arg0, 0x01FD, 0x00, B685, Buffer (0x09)
                            {
                                /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                /* 0008 */  0x85                                             // .
                            })
                        B685 = DerefOf (Arg4)
                        M680 (Arg0, 0x01FE, 0x00, B685, Buffer (0x09)
                            {
                                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                /* 0008 */  0x00                                             // .
                            })
                        B685 [0x03] = 0x0B
                        M680 (Arg0, 0x01FF, 0x00, B685, Buffer (0x09)
                            {
                                /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                /* 0008 */  0x00                                             // .
                            })
                        M680 (Arg0, 0x0200, 0x00, DerefOf (Arg4), Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                    }
                    Case (0x05)
                    {
                        /* Field Unit */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }
                    Case (0x0E)
                    {
                        /* Buffer Field */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }

                }

                Return (0x00)
            }

            /* Store(Concatenate(Concatenate(arg0, arg1), arg2), Debug) */
            /* Choose a way to obtain some result object */
            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    /* Data Image */
                    /* Choose a type of the result Object and specific source */
                    /* objects to obtain the result Object of the specified type. */
                    /* Check that the destination Object is properly initialized. */
                    /* Perform storing expression and check result. */
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x0203, 0x00, B686, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x86                                             // .
                                })
                            B686 = 0xFE7CB391D650A284
                            If (F64)
                            {
                                M680 (Arg0, 0x0204, 0x00, B686, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                        /* 0008 */  0x00                                             // .
                                    })
                            }
                            Else
                            {
                                M680 (Arg0, 0x0205, 0x00, B686, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x00, 0x00, 0x00, 0x00,  // ..P.....
                                        /* 0008 */  0x00                                             // .
                                    })
                            }
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x0206, 0x00, B687, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x87                                             // .
                                })
                            B687 = "FE7CB391D650A284"
                            M680 (Arg0, 0x0207, 0x00, B687, Buffer (0x09)
                                {
                                    /* 0000 */  0x46, 0x45, 0x37, 0x43, 0x42, 0x33, 0x39, 0x31,  // FE7CB391
                                    /* 0008 */  0x44                                             // D
                                })
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x0208, 0x00, B688, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x88                                             // .
                                })
                            B688 = Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                }
                            M680 (Arg0, 0x0209, 0x00, B688, Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                    /* 0008 */  0x00                                             // .
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x01)
                {
                    /* Named Object */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x020C, 0x00, B689, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x89                                             // .
                                })
                            B689 = I6E4 /* \I6E4 */
                            If (F64)
                            {
                                M680 (Arg0, 0x020D, 0x00, B689, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                        /* 0008 */  0x00                                             // .
                                    })
                            }
                            Else
                            {
                                M680 (Arg0, 0x020E, 0x00, B689, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x00, 0x00, 0x00, 0x00,  // ..P.....
                                        /* 0008 */  0x00                                             // .
                                    })
                            }

                            B689 [0x03] = 0x0B
                            If (F64)
                            {
                                M680 (Arg0, 0x020F, 0x00, B689, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                        /* 0008 */  0x00                                             // .
                                    })
                            }
                            Else
                            {
                                M680 (Arg0, 0x0210, 0x00, B689, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x00, 0x00, 0x00, 0x00,  // ..P.....
                                        /* 0008 */  0x00                                             // .
                                    })
                            }

                            M680 (Arg0, 0x0211, 0x00, I6E4, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x0212, 0x00, B68A, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x8A                                             // .
                                })
                            B68A = S6E4 /* \S6E4 */
                            M680 (Arg0, 0x0213, 0x00, B68A, Buffer (0x09)
                                {
                                    /* 0000 */  0x46, 0x45, 0x37, 0x43, 0x42, 0x33, 0x39, 0x31,  // FE7CB391
                                    /* 0008 */  0x44                                             // D
                                })
                            B68A [0x03] = 0x0B
                            M680 (Arg0, 0x0214, 0x00, B68A, Buffer (0x09)
                                {
                                    /* 0000 */  0x46, 0x45, 0x37, 0x0B, 0x42, 0x33, 0x39, 0x31,  // FE7.B391
                                    /* 0008 */  0x44                                             // D
                                })
                            M680 (Arg0, 0x0215, 0x00, S6E4, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x0216, 0x00, B68B, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x8B                                             // .
                                })
                            B68B = B6E4 /* \B6E4 */
                            M680 (Arg0, 0x0217, 0x00, B68B, Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                    /* 0008 */  0x00                                             // .
                                })
                            B68B [0x03] = 0x0B
                            M680 (Arg0, 0x0218, 0x00, B68B, Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                    /* 0008 */  0x00                                             // .
                                })
                            M680 (Arg0, 0x0219, 0x00, B6E4, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x02)
                {
                    /* Method ArgX Object */

                    M000 (Concatenate (Arg0, "-m000"), Arg2, 0xFE7CB391D650A284, "FE7CB391D650A284", Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                        })
                }
                Case (0x03)
                {
                    /* Method LocalX Object */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            Local0 = 0xFE7CB391D650A284
                        }
                        Case (0x02)
                        {
                            /* String */

                            Local0 = "FE7CB391D650A284"
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            Local0 = Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                }
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x021E, 0x00, B68C, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x8C                                             // .
                                })
                            B68C = Local0
                            If (F64)
                            {
                                M680 (Arg0, 0x021F, 0x00, B68C, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                        /* 0008 */  0x00                                             // .
                                    })
                            }
                            Else
                            {
                                M680 (Arg0, 0x0220, 0x00, B68C, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x00, 0x00, 0x00, 0x00,  // ..P.....
                                        /* 0008 */  0x00                                             // .
                                    })
                            }

                            B68C [0x03] = 0x0B
                            If (F64)
                            {
                                M680 (Arg0, 0x0221, 0x00, B68C, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                        /* 0008 */  0x00                                             // .
                                    })
                            }
                            Else
                            {
                                M680 (Arg0, 0x0222, 0x00, B68C, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x00, 0x00, 0x00, 0x00,  // ..P.....
                                        /* 0008 */  0x00                                             // .
                                    })
                            }

                            M680 (Arg0, 0x0223, 0x00, Local0, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x0224, 0x00, B68D, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x8D                                             // .
                                })
                            B68D = Local0
                            M680 (Arg0, 0x0225, 0x00, B68D, Buffer (0x09)
                                {
                                    /* 0000 */  0x46, 0x45, 0x37, 0x43, 0x42, 0x33, 0x39, 0x31,  // FE7CB391
                                    /* 0008 */  0x44                                             // D
                                })
                            B68D [0x03] = 0x0B
                            M680 (Arg0, 0x0226, 0x00, B68D, Buffer (0x09)
                                {
                                    /* 0000 */  0x46, 0x45, 0x37, 0x0B, 0x42, 0x33, 0x39, 0x31,  // FE7.B391
                                    /* 0008 */  0x44                                             // D
                                })
                            M680 (Arg0, 0x0227, 0x00, Local0, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x0228, 0x00, B68E, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x8E                                             // .
                                })
                            B68E = Local0
                            M680 (Arg0, 0x0229, 0x00, B68E, Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                    /* 0008 */  0x00                                             // .
                                })
                            B68E [0x03] = 0x0B
                            M680 (Arg0, 0x022A, 0x00, B68E, Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                    /* 0008 */  0x00                                             // .
                                })
                            M680 (Arg0, 0x022B, 0x00, Local0, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }

                    }
                }
                Case (0x04)
                {
                    /* Derefof of intermediate Object (Method ArgX Object) */

                    M001 (Concatenate (Arg0, "-m001"), Arg2, RefOf (I6E5), RefOf (S6E5), RefOf (B6E5))
                }
                Case (0x05)
                {
                    /* Derefof of immediate Index(...) */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x022C, 0x00, B68F, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x8F                                             // .
                                })
                            B68F = DerefOf (P690 [0x06])
                            If (F64)
                            {
                                M680 (Arg0, 0x022D, 0x00, B68F, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                        /* 0008 */  0x00                                             // .
                                    })
                            }
                            Else
                            {
                                M680 (Arg0, 0x022E, 0x00, B68F, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x00, 0x00, 0x00, 0x00,  // ..P.....
                                        /* 0008 */  0x00                                             // .
                                    })
                            }

                            B68F [0x03] = 0x0B
                            If (F64)
                            {
                                M680 (Arg0, 0x022F, 0x00, B68F, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                        /* 0008 */  0x00                                             // .
                                    })
                            }
                            Else
                            {
                                M680 (Arg0, 0x0230, 0x00, B68F, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x00, 0x00, 0x00, 0x00,  // ..P.....
                                        /* 0008 */  0x00                                             // .
                                    })
                            }

                            M680 (Arg0, 0x0231, 0x00, DerefOf (P690 [0x06]), 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x0232, 0x00, B690, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x90                                             // .
                                })
                            B690 = DerefOf (P690 [0x07])
                            M680 (Arg0, 0x0233, 0x00, B690, Buffer (0x09)
                                {
                                    /* 0000 */  0x46, 0x45, 0x37, 0x43, 0x42, 0x33, 0x39, 0x31,  // FE7CB391
                                    /* 0008 */  0x44                                             // D
                                })
                            B690 [0x03] = 0x0B
                            M680 (Arg0, 0x0234, 0x00, B690, Buffer (0x09)
                                {
                                    /* 0000 */  0x46, 0x45, 0x37, 0x0B, 0x42, 0x33, 0x39, 0x31,  // FE7.B391
                                    /* 0008 */  0x44                                             // D
                                })
                            M680 (Arg0, 0x0235, 0x00, DerefOf (P690 [0x07]), "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x0236, 0x00, B691, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x91                                             // .
                                })
                            B691 = DerefOf (P690 [0x08])
                            M680 (Arg0, 0x0237, 0x00, B691, Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                    /* 0008 */  0x00                                             // .
                                })
                            B691 [0x03] = 0x0B
                            M680 (Arg0, 0x0238, 0x00, B691, Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                    /* 0008 */  0x00                                             // .
                                })
                            M680 (Arg0, 0x0239, 0x00, DerefOf (P690 [0x08]), Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x06)
                {
                    /* Derefof of Indexed Reference returned by called Method */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x023C, 0x00, B692, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x92                                             // .
                                })
                            B692 = DerefOf (M681 (P690, 0x09))
                            If (F64)
                            {
                                M680 (Arg0, 0x023D, 0x00, B692, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                        /* 0008 */  0x00                                             // .
                                    })
                            }
                            Else
                            {
                                M680 (Arg0, 0x023E, 0x00, B692, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x00, 0x00, 0x00, 0x00,  // ..P.....
                                        /* 0008 */  0x00                                             // .
                                    })
                            }

                            B692 [0x03] = 0x0B
                            If (F64)
                            {
                                M680 (Arg0, 0x023F, 0x00, B692, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                        /* 0008 */  0x00                                             // .
                                    })
                            }
                            Else
                            {
                                M680 (Arg0, 0x0240, 0x00, B692, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x00, 0x00, 0x00, 0x00,  // ..P.....
                                        /* 0008 */  0x00                                             // .
                                    })
                            }

                            M680 (Arg0, 0x0241, 0x00, DerefOf (P690 [0x09]), 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x0242, 0x00, B693, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x93                                             // .
                                })
                            B693 = DerefOf (M681 (P690, 0x0A))
                            M680 (Arg0, 0x0243, 0x00, B693, Buffer (0x09)
                                {
                                    /* 0000 */  0x46, 0x45, 0x37, 0x43, 0x42, 0x33, 0x39, 0x31,  // FE7CB391
                                    /* 0008 */  0x44                                             // D
                                })
                            B693 [0x03] = 0x0B
                            M680 (Arg0, 0x0244, 0x00, B693, Buffer (0x09)
                                {
                                    /* 0000 */  0x46, 0x45, 0x37, 0x0B, 0x42, 0x33, 0x39, 0x31,  // FE7.B391
                                    /* 0008 */  0x44                                             // D
                                })
                            M680 (Arg0, 0x0245, 0x00, DerefOf (P690 [0x0A]), "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x0246, 0x00, B694, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x94                                             // .
                                })
                            B694 = DerefOf (M681 (P690, 0x0B))
                            M680 (Arg0, 0x0247, 0x00, B694, Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                    /* 0008 */  0x00                                             // .
                                })
                            B694 [0x03] = 0x0B
                            M680 (Arg0, 0x0248, 0x00, B694, Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                    /* 0008 */  0x00                                             // .
                                })
                            M680 (Arg0, 0x0249, 0x00, DerefOf (P690 [0x0B]), Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x07)
                {
                    /* Result Object returned by called Method */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x024C, 0x00, B695, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x95                                             // .
                                })
                            B695 = M682 (Arg2, 0x06)
                            If (F64)
                            {
                                M680 (Arg0, 0x024D, 0x00, B695, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                        /* 0008 */  0x00                                             // .
                                    })
                            }
                            Else
                            {
                                M680 (Arg0, 0x024E, 0x00, B695, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x00, 0x00, 0x00, 0x00,  // ..P.....
                                        /* 0008 */  0x00                                             // .
                                    })
                            }

                            B695 [0x03] = 0x0B
                            If (F64)
                            {
                                M680 (Arg0, 0x024F, 0x00, B695, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                        /* 0008 */  0x00                                             // .
                                    })
                            }
                            Else
                            {
                                M680 (Arg0, 0x0250, 0x00, B695, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x00, 0x00, 0x00, 0x00,  // ..P.....
                                        /* 0008 */  0x00                                             // .
                                    })
                            }

                            M680 (Arg0, 0x0251, 0x00, I6E6, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x0252, 0x00, B696, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x96                                             // .
                                })
                            B696 = M682 (Arg2, 0x06)
                            M680 (Arg0, 0x0253, 0x00, B696, Buffer (0x09)
                                {
                                    /* 0000 */  0x46, 0x45, 0x37, 0x43, 0x42, 0x33, 0x39, 0x31,  // FE7CB391
                                    /* 0008 */  0x44                                             // D
                                })
                            B696 [0x03] = 0x0B
                            M680 (Arg0, 0x0254, 0x00, B696, Buffer (0x09)
                                {
                                    /* 0000 */  0x46, 0x45, 0x37, 0x0B, 0x42, 0x33, 0x39, 0x31,  // FE7.B391
                                    /* 0008 */  0x44                                             // D
                                })
                            M680 (Arg0, 0x0255, 0x00, S6E6, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x0256, 0x00, B697, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x97                                             // .
                                })
                            B697 = M682 (Arg2, 0x06)
                            M680 (Arg0, 0x0257, 0x00, B697, Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                    /* 0008 */  0x00                                             // .
                                })
                            B697 [0x03] = 0x0B
                            M680 (Arg0, 0x0258, 0x00, B697, Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                    /* 0008 */  0x00                                             // .
                                })
                            M680 (Arg0, 0x0259, 0x00, B6E6, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x08)
                {
                    /* Result Object returned by any Operator (Op): */
                    /* Add, Mid */
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x025C, 0x00, B698, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x98                                             // .
                                })
                            Store ((I6E7 + 0x00), B698) /* \B698 */
                            If (F64)
                            {
                                M680 (Arg0, 0x025D, 0x00, B698, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                        /* 0008 */  0x00                                             // .
                                    })
                            }
                            Else
                            {
                                M680 (Arg0, 0x025E, 0x00, B698, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x00, 0x00, 0x00, 0x00,  // ..P.....
                                        /* 0008 */  0x00                                             // .
                                    })
                            }

                            B698 [0x03] = 0x0B
                            If (F64)
                            {
                                M680 (Arg0, 0x025F, 0x00, B698, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                        /* 0008 */  0x00                                             // .
                                    })
                            }
                            Else
                            {
                                M680 (Arg0, 0x0260, 0x00, B698, Buffer (0x09)
                                    {
                                        /* 0000 */  0x84, 0xA2, 0x50, 0x0B, 0x00, 0x00, 0x00, 0x00,  // ..P.....
                                        /* 0008 */  0x00                                             // .
                                    })
                            }

                            M680 (Arg0, 0x0261, 0x00, I6E7, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x0262, 0x00, B699, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x99                                             // .
                                })
                            B699 = Mid (S6E7, 0x02, 0x0E)
                            M680 (Arg0, 0x0263, 0x00, B699, Buffer (0x09)
                                {
                                    /* 0000 */  0x37, 0x43, 0x42, 0x33, 0x39, 0x31, 0x44, 0x36,  // 7CB391D6
                                    /* 0008 */  0x35                                             // 5
                                })
                            B699 [0x03] = 0x0B
                            M680 (Arg0, 0x0264, 0x00, B699, Buffer (0x09)
                                {
                                    /* 0000 */  0x37, 0x43, 0x42, 0x0B, 0x39, 0x31, 0x44, 0x36,  // 7CB.91D6
                                    /* 0008 */  0x35                                             // 5
                                })
                            M680 (Arg0, 0x0265, 0x00, S6E7, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x0266, 0x00, B69A, Buffer (0x09)
                                {
                                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                                    /* 0008 */  0x9A                                             // .
                                })
                            B69A = Mid (B6E7, 0x01, 0x07)
                            M680 (Arg0, 0x0267, 0x00, B69A, Buffer (0x09)
                                {
                                    /* 0000 */  0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE, 0x00,  // .P...|..
                                    /* 0008 */  0x00                                             // .
                                })
                            B69A [0x03] = 0x0B
                            M680 (Arg0, 0x0268, 0x00, B69A, Buffer (0x09)
                                {
                                    /* 0000 */  0xA2, 0x50, 0xD6, 0x0B, 0xB3, 0x7C, 0xFE, 0x00,  // .P...|..
                                    /* 0008 */  0x00                                             // .
                                })
                            M680 (Arg0, 0x0269, 0x00, B6E7, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                /* Additionally can be implemented cases: */
                /* Derefof of immediate Refof */
                /* Derefof of intermediate Object */
                /* Derefof of Reference returned by called Method */
                Default
                {
                    Debug = "Unexpected way to obtain some result Object"
                    ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                    Return (0x01)
                }

            }

            Return (0x00)
        }

        /* Store() Result Object to Buffer Field Named Object, */
        /* case of the field, which is 31-bit long (bf80) */
        Method (M0E0, 3, Serialized)
        {
            /* ArgX as a way to obtain some result object */

            Method (M000, 5, Serialized)
            {
                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        BF80 = Arg2
                        M010 (Arg0, 0x82, 0x01)
                        M680 (Arg0, 0x026D, 0x00, Arg2, 0xFE7CB391D650A284)
                    }
                    Case (0x02)
                    {
                        /* String */

                        BF80 = Arg3
                        M020 (Arg0, 0x89, 0x01)
                        M680 (Arg0, 0x026E, 0x00, Arg3, "FE7CB391D650A284")
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        BF80 = Arg4
                        M030 (Arg0, 0x90, 0x01)
                        M680 (Arg0, 0x026F, 0x00, Arg4, Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                    }
                    Case (0x05)
                    {
                        /* Field Unit */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }
                    Case (0x0E)
                    {
                        /* Buffer Field */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }

                }

                Return (0x00)
            }

            /* Reference in ArgX as a way to obtain some result object */

            Method (M001, 5, Serialized)
            {
                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        BF80 = DerefOf (Arg2)
                        M010 (Arg0, 0x99, 0x01)
                        M680 (Arg0, 0x0272, 0x00, DerefOf (Arg2), 0xFE7CB391D650A284)
                    }
                    Case (0x02)
                    {
                        /* String */

                        BF80 = DerefOf (Arg3)
                        M020 (Arg0, 0xA0, 0x01)
                        M680 (Arg0, 0x0273, 0x00, DerefOf (Arg3), "FE7CB391D650A284")
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        BF80 = DerefOf (Arg4)
                        M030 (Arg0, 0xA7, 0x01)
                        M680 (Arg0, 0x0274, 0x00, DerefOf (Arg4), Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                    }
                    Case (0x05)
                    {
                        /* Field Unit */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }
                    Case (0x0E)
                    {
                        /* Buffer Field */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }

                }

                Return (0x00)
            }

            /* Check storing of 0xfe7cb391d650a284 to bf80, */
            /* optionally perform an additional update and check */
            /* m010(<errmsg>, <errnum>, <flag>) */
            Method (M010, 3, NotSerialized)
            {
                M680 (Arg0, Arg1, 0x00, ObjectType (BF80), 0x0E)
                M680 (Arg0, Arg1, 0x01, BF80, Buffer(){0x84, 0xA2, 0x50, 0x56})
                BF80 = 0xC179B3FE
                M680 (Arg0, Arg1, 0x02, ObjectType (BF80), 0x0E)
                M680 (Arg0, Arg1, 0x03, BF80, Buffer(){0xFE, 0xB3, 0x79, 0x41})
            }

            /* Check storing of "FE7CB391D650A284" to bf80, */
            /* optionally perform an additional update and check */
            /* m020(<errmsg>, <errnum>, <flag>) */
            Method (M020, 3, NotSerialized)
            {
                M680 (Arg0, Arg1, 0x00, ObjectType (BF80), 0x0E)
                M680 (Arg0, Arg1, 0x01, BF80, Buffer(){0x46, 0x45, 0x37, 0x43})
                BF80 = "C179B3FE"
                M680 (Arg0, Arg1, 0x02, ObjectType (BF80), 0x0E)
                M680 (Arg0, Arg1, 0x03, BF80, Buffer(){0x43, 0x31, 0x37, 0x39})
            }

            /* Check storing of Buffer(){0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE} */
            /* to bf80, optionally perform an additional update and check */
            /* m030(<errmsg>, <errnum>, <flag>) */
            Method (M030, 3, NotSerialized)
            {
                M680 (Arg0, Arg1, 0x00, ObjectType (BF80), 0x0E)
                M680 (Arg0, Arg1, 0x01, BF80, Buffer(){0x84, 0xA2, 0x50, 0x56})
                BF80 = Buffer (0x04)
                    {
                         0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                    }
                M680 (Arg0, Arg1, 0x02, ObjectType (BF80), 0x0E)
                M680 (Arg0, Arg1, 0x03, BF80, Buffer(){0xFE, 0xB3, 0x79, 0x41})
            }

            /* Fill the bytes range of the Buffer Field in the SourceBuffer */

            M683 (B675, 0x23, 0x3F, 0xA5)
            /* Choose a way to obtain some result object */

            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    /* Data Image */
                    /* Choose a type of the result Object and specific source */
                    /* objects to obtain the result Object of the specified type. */
                    /* Check that the destination Object is properly initialized. */
                    /* Perform storing expression and check result. */
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            BF80 = 0xFE7CB391D650A284
                            M010 (Arg0, 0xB0, 0x00)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF80 = "FE7CB391D650A284"
                            M020 (Arg0, 0xB6, 0x00)
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF80 = Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                }
                            M030 (Arg0, 0xBC, 0x00)
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x01)
                {
                    /* Named Object */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            BF80 = I6E4 /* \I6E4 */
                            M010 (Arg0, 0xC4, 0x01)
                            M680 (Arg0, 0x0279, 0x00, I6E4, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF80 = S6E4 /* \S6E4 */
                            M020 (Arg0, 0xCB, 0x01)
                            M680 (Arg0, 0x027A, 0x00, S6E4, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF80 = B6E4 /* \B6E4 */
                            M030 (Arg0, 0xD2, 0x01)
                            M680 (Arg0, 0x027B, 0x00, B6E4, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x02)
                {
                    /* Method ArgX Object */

                    M000 (Concatenate (Arg0, "-m000"), Arg2, 0xFE7CB391D650A284, "FE7CB391D650A284", Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                        })
                }
                Case (0x03)
                {
                    /* Method LocalX Object */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            Local0 = 0xFE7CB391D650A284
                        }
                        Case (0x02)
                        {
                            /* String */

                            Local0 = "FE7CB391D650A284"
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            Local0 = Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                }
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            BF80 = Local0
                            M010 (Arg0, 0xDD, 0x01)
                            M680 (Arg0, 0x0280, 0x00, Local0, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF80 = Local0
                            M020 (Arg0, 0xE4, 0x01)
                            M680 (Arg0, 0x0281, 0x00, Local0, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF80 = Local0
                            M030 (Arg0, 0xEB, 0x01)
                            M680 (Arg0, 0x0282, 0x00, Local0, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }

                    }
                }
                Case (0x04)
                {
                    /* Derefof of intermediate Object (Method ArgX Object) */

                    M001 (Concatenate (Arg0, "-m001"), Arg2, RefOf (I6E5), RefOf (S6E5), RefOf (B6E5))
                }
                Case (0x05)
                {
                    /* Derefof of immediate Index(...) */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            BF80 = DerefOf (P690 [0x06])
                            M010 (Arg0, 0xF2, 0x01)
                            M680 (Arg0, 0x0283, 0x00, DerefOf (P690 [0x06]), 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF80 = DerefOf (P690 [0x07])
                            M020 (Arg0, 0xF9, 0x01)
                            M680 (Arg0, 0x0284, 0x00, DerefOf (P690 [0x07]), "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF80 = DerefOf (P690 [0x08])
                            M030 (Arg0, 0x0100, 0x01)
                            M680 (Arg0, 0x0285, 0x00, DerefOf (P690 [0x08]), Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x06)
                {
                    /* Derefof of Indexed Reference returned by called Method */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            BF80 = DerefOf (M681 (P690, 0x09))
                            M010 (Arg0, 0x0109, 0x01)
                            M680 (Arg0, 0x0288, 0x00, DerefOf (P690 [0x09]), 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF80 = DerefOf (M681 (P690, 0x0A))
                            M020 (Arg0, 0x0110, 0x01)
                            M680 (Arg0, 0x0289, 0x00, DerefOf (P690 [0x0A]), "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF80 = DerefOf (M681 (P690, 0x0B))
                            M030 (Arg0, 0x011C, 0x01)
                            M680 (Arg0, 0x028A, 0x00, DerefOf (P690 [0x0B]), Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x07)
                {
                    /* Result Object returned by called Method */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            BF80 = M682 (Arg2, 0x06)
                            M010 (Arg0, 0x0125, 0x01)
                            M680 (Arg0, 0x028D, 0x00, I6E6, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF80 = M682 (Arg2, 0x06)
                            M020 (Arg0, 0x0131, 0x01)
                            M680 (Arg0, 0x028E, 0x00, S6E6, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF80 = M682 (Arg2, 0x06)
                            M030 (Arg0, 0x0138, 0x01)
                            M680 (Arg0, 0x028F, 0x00, B6E6, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x08)
                {
                    /* Result Object returned by any Operator (Op): */
                    /* Add, Mid */
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            Store ((I6E7 + 0x00), BF80) /* \BF80 */
                            M010 (Arg0, 0x013C, 0x01)
                            M680 (Arg0, 0x0292, 0x00, I6E7, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF80 = Mid (S6E7, 0x02, 0x0E)
                            M680 (Arg0, 0x0293, 0x00, ObjectType (BF80), 0x0E)
                            M680 (Arg0, 0x0294, 0x00, BF80, Buffer() {0x37, 0x43, 0x42, 0x33})
                            BF80 = "C179B3FE"
                            M680 (Arg0, 0x0295, 0x00, ObjectType (BF80), 0x0E)
                            M680 (Arg0, 0x0296, 0x00, BF80, Buffer() {0x43, 0x31, 0x37, 0x39})
                            M680 (Arg0, 0x0297, 0x00, S6E7, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF80 = Mid (B6E7, 0x01, 0x07)
                            M680 (Arg0, 0x0298, 0x00, ObjectType (BF80), 0x0E)
                            M680 (Arg0, 0x0299, 0x00, BF80, Buffer() {0xA2, 0x50, 0xD6, 0x11})
                            BF80 = Buffer (0x04)
                                {
                                     0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                                }
                            M680 (Arg0, 0x029A, 0x00, ObjectType (BF80), 0x0E)
                            M680 (Arg0, 0x029B, 0x00, BF80, Buffer() {0xFE, 0xB3, 0x79, 0x41})
                            M680 (Arg0, 0x029C, 0x00, B6E7, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                /* Additionally can be implemented cases: */
                /* Derefof of immediate Refof */
                /* Derefof of intermediate Object */
                /* Derefof of Reference returned by called Method */
                Default
                {
                    Debug = "Unexpected way to obtain some result Object"
                    ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                    Return (0x01)
                }

            }

            Return (0x00)
        }

        /* Store() Result Object to Buffer Field Named Object */
        /* case of the field, which is 63-bit long (bf81) */
        Method (M0E1, 3, Serialized)
        {
            /* ArgX as a way to obtain some result object */

            Method (M000, 5, Serialized)
            {
                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        BF81 = Arg2
                        M010 (Arg0, 0x82, 0x01)
                        M680 (Arg0, 0x02A0, 0x00, Arg2, 0xFE7CB391D650A284)
                    }
                    Case (0x02)
                    {
                        /* String */

                        BF81 = Arg3
                        M020 (Arg0, 0x89, 0x01)
                        M680 (Arg0, 0x02A1, 0x00, Arg3, "FE7CB391D650A284")
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        BF81 = Arg4
                        M030 (Arg0, 0x90, 0x01)
                        M680 (Arg0, 0x02A2, 0x00, Arg4, Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                    }
                    Case (0x05)
                    {
                        /* Field Unit */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }
                    Case (0x0E)
                    {
                        /* Buffer Field */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }

                }

                Return (0x00)
            }

            /* Reference in ArgX as a way to obtain some result object */

            Method (M001, 5, Serialized)
            {
                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        BF81 = DerefOf (Arg2)
                        M010 (Arg0, 0x99, 0x01)
                        M680 (Arg0, 0x02A5, 0x00, DerefOf (Arg2), 0xFE7CB391D650A284)
                    }
                    Case (0x02)
                    {
                        /* String */

                        BF81 = DerefOf (Arg3)
                        M020 (Arg0, 0xA0, 0x01)
                        M680 (Arg0, 0x02A6, 0x00, DerefOf (Arg3), "FE7CB391D650A284")
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        BF81 = DerefOf (Arg4)
                        M030 (Arg0, 0xA7, 0x01)
                        M680 (Arg0, 0x02A7, 0x00, DerefOf (Arg4), Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                    }
                    Case (0x05)
                    {
                        /* Field Unit */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }
                    Case (0x0E)
                    {
                        /* Buffer Field */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }

                }

                Return (0x00)
            }

            /* Check storing of 0xfe7cb391d650a284 to bf81, */
            /* optionally perform an additional update and check */
            /* m010(<errmsg>, <errnum>, <flag>) */
            Method (M010, 3, NotSerialized)
            {
                M680 (Arg0, Arg1, 0x00, ObjectType (BF81), 0x0E)
                If (F64)
                {
                    M680 (Arg0, Arg1, 0x02, BF81, Buffer (0x08)
                        {
                            0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0x7E   // ..P.....
                        })
                }
                else
                {
                    M680 (Arg0, Arg1, 0x02, BF81, Buffer (0x08)
                        {
                            0x84, 0xA2, 0x50, 0xD6, 0x00, 0x00, 0x00, 0x00   // ..P.....
                        })
                }

                If (Arg2)
                {
                    BF81 = 0xC179B3FE
                    M680 (Arg0, Arg1, 0x03, ObjectType (BF81), 0x0E)
                    M680 (Arg0, Arg1, 0x05, BF81, Buffer (0x08)
                        {
                            0xFE, 0xB3, 0x79, 0xC1, 0x00, 0x00, 0x00, 0x00   // ..y.....
                        })
                }
            }

            /* Check storing of "FE7CB391D650A284" to bf81, */
            /* optionally perform an additional update and check */
            /* m020(<errmsg>, <errnum>, <flag>) */
            Method (M020, 3, NotSerialized)
            {
                M680 (Arg0, Arg1, 0x00, ObjectType (BF81), 0x0E)
                M680 (Arg0, Arg1, 0x02, BF81, Buffer (0x08)
                    {
                        0x46, 0x45, 0x37, 0x43, 0x42, 0x33, 0x39, 0x31   // FE7CB391
                    })

                If (Arg2)
                {
                    BF81 = "C179B3FE"
                    M680 (Arg0, Arg1, 0x03, ObjectType (BF81), 0x0E)
                    M680 (Arg0, Arg1, 0x05, BF81, Buffer (0x08)
                        {
                            0x43, 0x31, 0x37, 0x39, 0x42, 0x33, 0x46, 0x45   // C179B3FE
                        })
                }
            }

            /* Check storing of Buffer(){0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE} */
            /* to bf81, optionally perform an additional update and check */
            /* m030(<errmsg>, <errnum>, <flag>) */
            Method (M030, 3, NotSerialized)
            {
                M680 (Arg0, Arg1, 0x00, ObjectType (BF81), 0x0E)
                M680 (Arg0, Arg1, 0x02, BF81, Buffer (0x08)
                    {
                        0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0x7E   // ..P...|~
                    })

                If (Arg2)
                {
                    BF81 = Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                        }
                    M680 (Arg0, Arg1, 0x03, ObjectType (BF81), 0x0E)
                    M680 (Arg0, Arg1, 0x05, BF81, Buffer (0x08)
                        {
                            0xFE, 0xB3, 0x79, 0xC1, 0x00, 0x00, 0x00, 0x00   // ..y.....
                        })
                }
            }

            /* Fill the bytes range of the Buffer Field in the SourceBuffer */

            M683 (B675, 0x23, 0x3F, 0xA5)
            /* Choose a way to obtain some result object */

            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    /* Data Image */
                    /* Choose a type of the result Object and specific source */
                    /* objects to obtain the result Object of the specified type. */
                    /* Check that the destination Object is properly initialized. */
                    /* Perform storing expression and check result. */
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            BF81 = 0xFE7CB391D650A284
                            M010 (Arg0, 0xB0, 0x00)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF81 = "FE7CB391D650A284"
                            M020 (Arg0, 0xB6, 0x00)
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF81 = Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                }
                            M030 (Arg0, 0xBC, 0x00)
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x01)
                {
                    /* Named Object */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            BF81 = I6E4 /* \I6E4 */
                            M010 (Arg0, 0xC4, 0x01)
                            M680 (Arg0, 0x02AC, 0x00, I6E4, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF81 = S6E4 /* \S6E4 */
                            M020 (Arg0, 0xCB, 0x01)
                            M680 (Arg0, 0x02AD, 0x00, S6E4, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF81 = B6E4 /* \B6E4 */
                            M030 (Arg0, 0xD2, 0x01)
                            M680 (Arg0, 0x02AE, 0x00, B6E4, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x02)
                {
                    /* Method ArgX Object */

                    M000 (Concatenate (Arg0, "-m000"), Arg2, 0xFE7CB391D650A284, "FE7CB391D650A284", Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                        })
                }
                Case (0x03)
                {
                    /* Method LocalX Object */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            Local0 = 0xFE7CB391D650A284
                        }
                        Case (0x02)
                        {
                            /* String */

                            Local0 = "FE7CB391D650A284"
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            Local0 = Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                }
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            BF81 = Local0
                            M010 (Arg0, 0xDD, 0x01)
                            M680 (Arg0, 0x02B3, 0x00, Local0, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF81 = Local0
                            M020 (Arg0, 0xE4, 0x01)
                            M680 (Arg0, 0x02B4, 0x00, Local0, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF81 = Local0
                            M030 (Arg0, 0xEB, 0x01)
                            M680 (Arg0, 0x02B5, 0x00, Local0, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }

                    }
                }
                Case (0x04)
                {
                    /* Derefof of intermediate Object (Method ArgX Object) */

                    M001 (Concatenate (Arg0, "-m001"), Arg2, RefOf (I6E5), RefOf (S6E5), RefOf (B6E5))
                }
                Case (0x05)
                {
                    /* Derefof of immediate Index(...) */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            BF81 = DerefOf (P690 [0x06])
                            M010 (Arg0, 0xF2, 0x01)
                            M680 (Arg0, 0x02B6, 0x00, DerefOf (P690 [0x06]), 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF81 = DerefOf (P690 [0x07])
                            M020 (Arg0, 0xF9, 0x01)
                            M680 (Arg0, 0x02B7, 0x00, DerefOf (P690 [0x07]), "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF81 = DerefOf (P690 [0x08])
                            M030 (Arg0, 0x0100, 0x01)
                            M680 (Arg0, 0x02B8, 0x00, DerefOf (P690 [0x08]), Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x06)
                {
                    /* Derefof of Indexed Reference returned by called Method */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            BF81 = DerefOf (M681 (P690, 0x09))
                            M010 (Arg0, 0x0109, 0x01)
                            M680 (Arg0, 0x02BB, 0x00, DerefOf (P690 [0x09]), 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF81 = DerefOf (M681 (P690, 0x0A))
                            M020 (Arg0, 0x0110, 0x01)
                            M680 (Arg0, 0x02BC, 0x00, DerefOf (P690 [0x0A]), "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF81 = DerefOf (M681 (P690, 0x0B))
                            M030 (Arg0, 0x011C, 0x01)
                            M680 (Arg0, 0x02BD, 0x00, DerefOf (P690 [0x0B]), Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x07)
                {
                    /* Result Object returned by called Method */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            BF81 = M682 (Arg2, 0x06)
                            M010 (Arg0, 0x0125, 0x01)
                            M680 (Arg0, 0x02C0, 0x00, I6E6, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF81 = M682 (Arg2, 0x06)
                            M020 (Arg0, 0x0131, 0x01)
                            M680 (Arg0, 0x02C1, 0x00, S6E6, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF81 = M682 (Arg2, 0x06)
                            M030 (Arg0, 0x0138, 0x01)
                            M680 (Arg0, 0x02C2, 0x00, B6E6, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x08)
                {
                    /* Result Object returned by any Operator (Op): */
                    /* Add, Mid */
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            Store ((I6E7 + 0x00), BF81) /* \BF81 */
                            M010 (Arg0, 0x013C, 0x01)
                            M680 (Arg0, 0x02C5, 0x00, I6E7, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF81 = Mid (S6E7, 0x02, 0x0E)
                            M680 (Arg0, 0x02C6, 0x00, ObjectType (BF81), 0x0E)
                            M680 (Arg0, 0x02C8, 0x00, BF81, Buffer (0x08)
                                {
                                     0x37, 0x43, 0x42, 0x33, 0x39, 0x31, 0x44, 0x36   // 7CB391D6
                                })

                            BF81 = "C179B3FE"
                            M680 (Arg0, 0x02C9, 0x00, ObjectType (BF81), 0x0E)
                            M680 (Arg0, 0x02CB, 0x00, BF81, Buffer (0x08)
                                {
                                     0x43, 0x31, 0x37, 0x39, 0x42, 0x33, 0x46, 0x45   // C179B3FE
                                })

                            M680 (Arg0, 0x02CC, 0x00, S6E7, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF81 = Mid (B6E7, 0x01, 0x07)
                            M680 (Arg0, 0x02CD, 0x00, ObjectType (BF81), 0x0E)
                            M680 (Arg0, 0x02CF, 0x00, BF81, Buffer (0x08)
                                {
                                     0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE, 0x00   // .P...|..
                                })

                            BF81 = Buffer (0x04)
                                {
                                     0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                                }
                            M680 (Arg0, 0x02D0, 0x00, ObjectType (BF81), 0x0E)
                            M680 (Arg0, 0x02D2, 0x00, BF81, Buffer (0x08)
                                {
                                     0xFE, 0xB3, 0x79, 0xC1, 0x00, 0x00, 0x00, 0x00   // ..y.....
                                })

                            M680 (Arg0, 0x02D3, 0x00, B6E7, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                /* Additionally can be implemented cases: */
                /* Derefof of immediate Refof */
                /* Derefof of intermediate Object */
                /* Derefof of Reference returned by called Method */
                Default
                {
                    Debug = "Unexpected way to obtain some result Object"
                    ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                    Return (0x01)
                }

            }

            Return (0x00)
        }

        /* Store() Result Object to Buffer Field Named Object */
        /* case of the field, which is 69-bit long (bf82) */
        Method (M0E2, 3, Serialized)
        {
            /* ArgX as a way to obtain some result object */

            Method (M000, 5, Serialized)
            {
                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        BF82 = Arg2
                        M010 (Arg0, 0x82, 0x01)
                        M680 (Arg0, 0x02D7, 0x00, Arg2, 0xFE7CB391D650A284)
                    }
                    Case (0x02)
                    {
                        /* String */

                        BF82 = Arg3
                        M020 (Arg0, 0x89, 0x01)
                        M680 (Arg0, 0x02D8, 0x00, Arg3, "FE7CB391D650A284")
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        BF82 = Arg4
                        M030 (Arg0, 0x90, 0x01)
                        M680 (Arg0, 0x02D9, 0x00, Arg4, Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                    }
                    Case (0x05)
                    {
                        /* Field Unit */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }
                    Case (0x0E)
                    {
                        /* Buffer Field */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }

                }

                Return (0x00)
            }

            /* Reference in ArgX as a way to obtain some result object */

            Method (M001, 5, Serialized)
            {
                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        BF82 = DerefOf (Arg2)
                        M010 (Arg0, 0x99, 0x01)
                        M680 (Arg0, 0x02DC, 0x00, DerefOf (Arg2), 0xFE7CB391D650A284)
                    }
                    Case (0x02)
                    {
                        /* String */

                        BF82 = DerefOf (Arg3)
                        M020 (Arg0, 0xA0, 0x01)
                        M680 (Arg0, 0x02DD, 0x00, DerefOf (Arg3), "FE7CB391D650A284")
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        BF82 = DerefOf (Arg4)
                        M030 (Arg0, 0xA7, 0x01)
                        M680 (Arg0, 0x02DE, 0x00, DerefOf (Arg4), Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                    }
                    Case (0x05)
                    {
                        /* Field Unit */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }
                    Case (0x0E)
                    {
                        /* Buffer Field */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }

                }

                Return (0x00)
            }

            /* Check storing of 0xfe7cb391d650a284 to bf82, */
            /* optionally perform an additional update and check */
            /* m010(<errmsg>, <errnum>, <flag>) */
            Method (M010, 3, NotSerialized)
            {
                If (F64)
                {
                    M680 (Arg0, Arg1, 0x00, ObjectType (BF82), 0x0E)
                    M680 (Arg0, Arg1, 0x01, BF82, Buffer (0x09)
                        {
                            /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                            /* 0008 */  0x00                                             // .
                        })
                }
                Else
                {
                    M680 (Arg0, Arg1, 0x02, BF82, Buffer (0x09)
                        {
                            /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x00, 0x00, 0x00, 0x00,  // ..P.....
                            /* 0008 */  0x00                                             // .
                        })
                }


                If (Arg2)
                {
                    BF82 = 0xC179B3FE
                    M680 (Arg0, Arg1, 0x03, ObjectType (BF82), 0x0E)
                    M680 (Arg0, Arg1, 0x04, BF82, Buffer (0x09)
                        {
                            /* 0000 */  0xFE, 0xB3, 0x79, 0xC1, 0x00, 0x00, 0x00, 0x00,  // ..y.....
                            /* 0008 */  0x00                                             // .
                        })
                }
            }

            /* Check storing of "FE7CB391D650A284" to bf82, */
            /* optionally perform an additional update and check */
            /* m020(<errmsg>, <errnum>, <flag>) */
            Method (M020, 3, NotSerialized)
            {
                M680 (Arg0, Arg1, 0x00, ObjectType (BF82), 0x0E)
                M680 (Arg0, Arg1, 0x01, BF82, Buffer (0x09)
                    {
                        /* 0000 */  0x46, 0x45, 0x37, 0x43, 0x42, 0x33, 0x39, 0x31,  // FE7CB391
                        /* 0008 */  0x04                                             // .
                    })
                If (Arg2)
                {
                    BF82 = "C179B3FE"
                    M680 (Arg0, Arg1, 0x02, ObjectType (BF82), 0x0E)
                    M680 (Arg0, Arg1, 0x03, BF82, Buffer (0x09)
                        {
                            "C179B3FE"
                        })
                }
            }

            /* Check storing of Buffer(){0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE} */
            /* to bf82, optionally perform an additional update and check */
            /* m030(<errmsg>, <errnum>, <flag>) */
            Method (M030, 3, NotSerialized)
            {
                M680 (Arg0, Arg1, 0x00, ObjectType (BF82), 0x0E)
                M680 (Arg0, Arg1, 0x01, BF82, Buffer (0x09)
                    {
                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                        /* 0008 */  0x00                                             // .
                    })
                If (Arg2)
                {
                    BF82 = Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                        }
                    M680 (Arg0, Arg1, 0x02, ObjectType (BF82), 0x0E)
                    M680 (Arg0, Arg1, 0x03, BF82, Buffer (0x09)
                        {
                            /* 0000 */  0xFE, 0xB3, 0x79, 0xC1, 0x00, 0x00, 0x00, 0x00,  // ..y.....
                            /* 0008 */  0x00                                             // .
                        })
                }
            }

            /* Fill the bytes range of the Buffer Field in the SourceBuffer */

            M683 (B675, 0x6E, 0x45, 0xA5)
            /* Choose a way to obtain some result object */

            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    /* Data Image */
                    /* Choose a type of the result Object and specific source */
                    /* objects to obtain the result Object of the specified type. */
                    /* Check that the destination Object is properly initialized. */
                    /* Perform storing expression and check result. */
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            BF82 = 0xFE7CB391D650A284
                            M010 (Arg0, 0xB0, 0x00)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF82 = "FE7CB391D650A284"
                            M020 (Arg0, 0xB6, 0x00)
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF82 = Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                }
                            M030 (Arg0, 0xBC, 0x00)
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x01)
                {
                    /* Named Object */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            BF82 = I6E4 /* \I6E4 */
                            M010 (Arg0, 0xC4, 0x01)
                            M680 (Arg0, 0x02E3, 0x00, I6E4, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF82 = S6E4 /* \S6E4 */
                            M020 (Arg0, 0xCB, 0x01)
                            M680 (Arg0, 0x02E4, 0x00, S6E4, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF82 = B6E4 /* \B6E4 */
                            M030 (Arg0, 0xD2, 0x01)
                            M680 (Arg0, 0x02E5, 0x00, B6E4, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x02)
                {
                    /* Method ArgX Object */

                    M000 (Concatenate (Arg0, "-m000"), Arg2, 0xFE7CB391D650A284, "FE7CB391D650A284", Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                        })
                }
                Case (0x03)
                {
                    /* Method LocalX Object */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            Local0 = 0xFE7CB391D650A284
                        }
                        Case (0x02)
                        {
                            /* String */

                            Local0 = "FE7CB391D650A284"
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            Local0 = Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                }
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            BF82 = Local0
                            M010 (Arg0, 0xDD, 0x01)
                            M680 (Arg0, 0x02EA, 0x00, Local0, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF82 = Local0
                            M020 (Arg0, 0xE4, 0x01)
                            M680 (Arg0, 0x02EB, 0x00, Local0, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF82 = Local0
                            M030 (Arg0, 0xEB, 0x01)
                            M680 (Arg0, 0x02EC, 0x00, Local0, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }

                    }
                }
                Case (0x04)
                {
                    /* Derefof of intermediate Object (Method ArgX Object) */

                    M001 (Concatenate (Arg0, "-m001"), Arg2, RefOf (I6E5), RefOf (S6E5), RefOf (B6E5))
                }
                Case (0x05)
                {
                    /* Derefof of immediate Index(...) */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            BF82 = DerefOf (P690 [0x06])
                            M010 (Arg0, 0xF2, 0x01)
                            M680 (Arg0, 0x02ED, 0x00, DerefOf (P690 [0x06]), 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF82 = DerefOf (P690 [0x07])
                            M020 (Arg0, 0xF9, 0x01)
                            M680 (Arg0, 0x02EE, 0x00, DerefOf (P690 [0x07]), "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF82 = DerefOf (P690 [0x08])
                            M030 (Arg0, 0x0100, 0x01)
                            M680 (Arg0, 0x02EF, 0x00, DerefOf (P690 [0x08]), Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x06)
                {
                    /* Derefof of Indexed Reference returned by called Method */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            BF82 = DerefOf (M681 (P690, 0x09))
                            M010 (Arg0, 0x0109, 0x01)
                            M680 (Arg0, 0x02F2, 0x00, DerefOf (P690 [0x09]), 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF82 = DerefOf (M681 (P690, 0x0A))
                            M020 (Arg0, 0x0110, 0x01)
                            M680 (Arg0, 0x02F3, 0x00, DerefOf (P690 [0x0A]), "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF82 = DerefOf (M681 (P690, 0x0B))
                            M030 (Arg0, 0x011C, 0x01)
                            M680 (Arg0, 0x02F4, 0x00, DerefOf (P690 [0x0B]), Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x07)
                {
                    /* Result Object returned by called Method */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            BF82 = M682 (Arg2, 0x06)
                            M010 (Arg0, 0x0125, 0x01)
                            M680 (Arg0, 0x02F7, 0x00, I6E6, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF82 = M682 (Arg2, 0x06)
                            M020 (Arg0, 0x0131, 0x01)
                            M680 (Arg0, 0x02F8, 0x00, S6E6, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF82 = M682 (Arg2, 0x06)
                            M030 (Arg0, 0x0138, 0x01)
                            M680 (Arg0, 0x02F9, 0x00, B6E6, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x08)
                {
                    /* Result Object returned by any Operator (Op): */
                    /* Add, Mid */
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            Store ((I6E7 + 0x00), BF82) /* \BF82 */
                            M010 (Arg0, 0x013C, 0x01)
                            M680 (Arg0, 0x02FC, 0x00, I6E7, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            BF82 = Mid (S6E7, 0x02, 0x0E)
                            M680 (Arg0, 0x02FD, 0x00, ObjectType (BF82), 0x0E)
                            M680 (Arg0, 0x02FE, 0x00, BF82, Buffer (0x09)
                                {
                                    /* 0000 */  0x37, 0x43, 0x42, 0x33, 0x39, 0x31, 0x44, 0x36,  // 7CB391D6
                                    /* 0008 */  0x15                                             // .
                                })
                            BF82 = "C179B3FE"
                            M680 (Arg0, 0x02FF, 0x00, ObjectType (BF82), 0x0E)
                            M680 (Arg0, 0x0300, 0x00, BF82, Buffer (0x09)
                                {
                                    "C179B3FE"
                                })
                            M680 (Arg0, 0x0301, 0x00, S6E7, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            BF82 = Mid (B6E7, 0x01, 0x07)
                            M680 (Arg0, 0x0302, 0x00, ObjectType (BF82), 0x0E)
                            M680 (Arg0, 0x0303, 0x00, BF82, Buffer (0x09)
                                {
                                    /* 0000 */  0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE, 0x00,  // .P...|..
                                    /* 0008 */  0x00                                             // .
                                })
                            BF82 = Buffer (0x04)
                                {
                                     0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                                }
                            M680 (Arg0, 0x0304, 0x00, ObjectType (BF82), 0x0E)
                            M680 (Arg0, 0x0305, 0x00, BF82, Buffer (0x09)
                                {
                                    /* 0000 */  0xFE, 0xB3, 0x79, 0xC1, 0x00, 0x00, 0x00, 0x00,  // ..y.....
                                    /* 0008 */  0x00                                             // .
                                })
                            M680 (Arg0, 0x0306, 0x00, B6E7, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                /* Additionally can be implemented cases: */
                /* Derefof of immediate Refof */
                /* Derefof of intermediate Object */
                /* Derefof of Reference returned by called Method */
                Default
                {
                    Debug = "Unexpected way to obtain some result Object"
                    ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                    Return (0x01)
                }

            }

            Return (0x00)
        }

        /* Store() Result Object to String Method LocalX Object */

        Method (M023, 3, Serialized)
        {
            /* ArgX as a way to obtain some result object */

            Method (M000, 5, Serialized)
            {
                Local1 = "initial named string"
                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        M680 (Arg0, 0x030A, 0x00, Local1, "initial named string")
                        Local1 = Arg2
                        If (F64)
                        {
                            M680 (Arg0, 0x030B, 0x00, Local1, 0xFE7CB391D650A284)
                        }
                        Else
                        {
                            M680 (Arg0, 0x030C, 0x00, Local1, 0xD650A284)
                        }

                        Local1 = 0xC179B3FE
                        M680 (Arg0, 0x030D, 0x00, Local1, 0xC179B3FE)
                        M680 (Arg0, 0x030E, 0x00, Arg2, 0xFE7CB391D650A284)
                    }
                    Case (0x02)
                    {
                        /* String */

                        M680 (Arg0, 0x030F, 0x00, Local1, "initial named string")
                        Local1 = Arg3
                        M680 (Arg0, 0x0310, 0x00, Local1, "FE7CB391D650A284")
                        Local1 [0x03] = 0x0B
                        M680 (Arg0, 0x0311, 0x00, Local1, "FE7\vB391D650A284")
                        M680 (Arg0, 0x0312, 0x00, Arg3, "FE7CB391D650A284")
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        M680 (Arg0, 0x0313, 0x00, Local1, "initial named string")
                        Local1 = Arg4
                        M680 (Arg0, 0x0314, 0x00, Local1, Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                        Local1 [0x03] = 0x0B
                        M680 (Arg0, 0x0315, 0x00, Local1, Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                        M680 (Arg0, 0x0316, 0x00, Arg4, Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                    }
                    Case (0x05)
                    {
                        /* Field Unit */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }
                    Case (0x0E)
                    {
                        /* Buffer Field */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }

                }

                Return (0x00)
            }

            /* Reference in ArgX as a way to obtain some result object */

            Method (M001, 5, Serialized)
            {
                Local1 = "initial named string"
                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        M680 (Arg0, 0x0319, 0x00, Local1, "initial named string")
                        Local1 = DerefOf (Arg2)
                        If (F64)
                        {
                            M680 (Arg0, 0x031A, 0x00, Local1, 0xFE7CB391D650A284)
                        }
                        Else
                        {
                            M680 (Arg0, 0x031B, 0x00, Local1, 0xD650A284)
                        }

                        Local1 = 0xC179B3FE
                        M680 (Arg0, 0x031C, 0x00, Local1, 0xC179B3FE)
                        M680 (Arg0, 0x031D, 0x00, DerefOf (Arg2), 0xFE7CB391D650A284)
                    }
                    Case (0x02)
                    {
                        /* String */

                        M680 (Arg0, 0x031E, 0x00, Local1, "initial named string")
                        Local1 = DerefOf (Arg3)
                        M680 (Arg0, 0x031F, 0x00, Local1, "FE7CB391D650A284")
                        Local1 [0x03] = 0x0B
                        M680 (Arg0, 0x0320, 0x00, Local1, "FE7\vB391D650A284")
                        M680 (Arg0, 0x0321, 0x00, DerefOf (Arg3), "FE7CB391D650A284")
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        M680 (Arg0, 0x0322, 0x00, Local1, "initial named string")
                        Local1 = DerefOf (Arg4)
                        M680 (Arg0, 0x0323, 0x00, Local1, Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                        Local1 [0x03] = 0x0B
                        M680 (Arg0, 0x0324, 0x00, Local1, Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                        M680 (Arg0, 0x0325, 0x00, DerefOf (Arg4), Buffer (0x08)
                            {
                                 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                            })
                    }
                    Case (0x05)
                    {
                        /* Field Unit */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }
                    Case (0x0E)
                    {
                        /* Buffer Field */

                        Debug = "Not implemented"
                        ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        Return (0x01)
                    }

                }

                Return (0x00)
            }

            Local1 = "initial named string"
            /* Choose a way to obtain some result object */

            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    /* Data Image */
                    /* Choose a type of the result Object and specific source */
                    /* objects to obtain the result Object of the specified type. */
                    /* Check that the destination Object is properly initialized. */
                    /* Perform storing expression and check result. */
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x0328, 0x00, Local1, "initial named string")
                            Local1 = 0xFE7CB391D650A284
                            If (F64)
                            {
                                M680 (Arg0, 0x0329, 0x00, Local1, 0xFE7CB391D650A284)
                            }
                            Else
                            {
                                M680 (Arg0, 0x032A, 0x00, Local1, 0xD650A284)
                            }
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x032B, 0x00, Local1, "initial named string")
                            Local1 = "FE7CB391D650A284"
                            M680 (Arg0, 0x032C, 0x00, Local1, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x032D, 0x00, Local1, "initial named string")
                            Local1 = Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                }
                            M680 (Arg0, 0x032E, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x01)
                {
                    /* Named Object */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x0331, 0x00, Local1, "initial named string")
                            Local1 = I6E4 /* \I6E4 */
                            If (F64)
                            {
                                M680 (Arg0, 0x0332, 0x00, Local1, 0xFE7CB391D650A284)
                            }
                            Else
                            {
                                M680 (Arg0, 0x0333, 0x00, Local1, 0xD650A284)
                            }

                            Local1 = 0xC179B3FE
                            M680 (Arg0, 0x0334, 0x00, Local1, 0xC179B3FE)
                            M680 (Arg0, 0x0335, 0x00, I6E4, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x0336, 0x00, Local1, "initial named string")
                            Local1 = S6E4 /* \S6E4 */
                            M680 (Arg0, 0x0337, 0x00, Local1, "FE7CB391D650A284")
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0338, 0x00, Local1, "FE7\vB391D650A284")
                            M680 (Arg0, 0x0339, 0x00, S6E4, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x033A, 0x00, Local1, "initial named string")
                            Local1 = B6E4 /* \B6E4 */
                            M680 (Arg0, 0x033B, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x033C, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            M680 (Arg0, 0x033D, 0x00, B6E4, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Default
                        {
                            Debug = "Unexpected type of the result Object to be stored"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x02)
                {
                    /* Method ArgX Object */

                    M000 (Concatenate (Arg0, "-m000"), Arg2, 0xFE7CB391D650A284, "FE7CB391D650A284", Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                        })
                }
                Case (0x03)
                {
                    /* Method LocalX Object */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x00)
                        {
                            /* Stuff */

                            Return (0x00)
                        }
                        Case (0x01)
                        {
                            /* Integer */

                            Local0 = 0xFE7CB391D650A284
                        }
                        Case (0x02)
                        {
                            /* String */

                            Local0 = "FE7CB391D650A284"
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            Local0 = Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                }
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x0341, 0x00, Local1, "initial named string")
                            Local1 = Local0
                            If (F64)
                            {
                                M680 (Arg0, 0x0342, 0x00, Local1, 0xFE7CB391D650A284)
                            }
                            Else
                            {
                                M680 (Arg0, 0x0343, 0x00, Local1, 0xD650A284)
                            }

                            Local1 = 0xC179B3FE
                            M680 (Arg0, 0x0344, 0x00, Local1, 0xC179B3FE)
                            M680 (Arg0, 0x0345, 0x00, Local0, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x0346, 0x00, Local1, "initial named string")
                            Local1 = Local0
                            M680 (Arg0, 0x0347, 0x00, Local1, "FE7CB391D650A284")
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0348, 0x00, Local1, "FE7\vB391D650A284")
                            M680 (Arg0, 0x0349, 0x00, Local0, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x034A, 0x00, Local1, "initial named string")
                            Local1 = Local0
                            M680 (Arg0, 0x034B, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x034C, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            M680 (Arg0, 0x034D, 0x00, Local0, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }

                    }
                }
                Case (0x04)
                {
                    /* Derefof of intermediate Object (Method ArgX Object) */

                    M001 (Concatenate (Arg0, "-m001"), Arg2, RefOf (I6E5), RefOf (S6E5), RefOf (B6E5))
                }
                Case (0x05)
                {
                    /* Derefof of immediate Index(...) */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x034E, 0x00, Local1, "initial named string")
                            Local1 = DerefOf (P690 [0x06])
                            If (F64)
                            {
                                M680 (Arg0, 0x034F, 0x00, Local1, 0xFE7CB391D650A284)
                            }
                            Else
                            {
                                M680 (Arg0, 0x0350, 0x00, Local1, 0xD650A284)
                            }

                            Local1 = 0xC179B3FE
                            M680 (Arg0, 0x0351, 0x00, Local1, 0xC179B3FE)
                            M680 (Arg0, 0x0352, 0x00, DerefOf (P690 [0x06]), 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x0353, 0x00, Local1, "initial named string")
                            Local1 = DerefOf (P690 [0x07])
                            M680 (Arg0, 0x0354, 0x00, Local1, "FE7CB391D650A284")
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0355, 0x00, Local1, "FE7\vB391D650A284")
                            M680 (Arg0, 0x0356, 0x00, DerefOf (P690 [0x07]), "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x0357, 0x00, Local1, "initial named string")
                            Local1 = DerefOf (P690 [0x08])
                            M680 (Arg0, 0x0358, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0359, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            M680 (Arg0, 0x035A, 0x00, DerefOf (P690 [0x08]), Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x06)
                {
                    /* Derefof of Indexed Reference returned by called Method */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x035D, 0x00, Local1, "initial named string")
                            Local1 = DerefOf (M681 (P690, 0x09))
                            If (F64)
                            {
                                M680 (Arg0, 0x035E, 0x00, Local1, 0xFE7CB391D650A284)
                            }
                            Else
                            {
                                M680 (Arg0, 0x035F, 0x00, Local1, 0xD650A284)
                            }

                            Local1 = 0xC179B3FE
                            M680 (Arg0, 0x0360, 0x00, Local1, 0xC179B3FE)
                            M680 (Arg0, 0x0361, 0x00, DerefOf (P690 [0x09]), 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x0362, 0x00, Local1, "initial named string")
                            Local1 = DerefOf (M681 (P690, 0x0A))
                            M680 (Arg0, 0x0363, 0x00, Local1, "FE7CB391D650A284")
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0364, 0x00, Local1, "FE7\vB391D650A284")
                            M680 (Arg0, 0x0365, 0x00, DerefOf (P690 [0x0A]), "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x0366, 0x00, Local1, "initial named string")
                            Local1 = DerefOf (M681 (P690, 0x0B))
                            M680 (Arg0, 0x0367, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0368, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            M680 (Arg0, 0x0369, 0x00, DerefOf (P690 [0x0B]), Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }

                    }
                }
                Case (0x07)
                {
                    /* Result Object returned by called Method */

                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x036A, 0x00, Local1, "initial named string")
                            Local1 = M682 (Arg2, 0x06)
                            If (F64)
                            {
                                M680 (Arg0, 0x036B, 0x00, Local1, 0xFE7CB391D650A284)
                            }
                            Else
                            {
                                M680 (Arg0, 0x036C, 0x00, Local1, 0xD650A284)
                            }

                            Local1 = 0xC179B3FE
                            M680 (Arg0, 0x036D, 0x00, Local1, 0xC179B3FE)
                            M680 (Arg0, 0x036E, 0x00, I6E6, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x036F, 0x00, Local1, "initial named string")
                            Local1 = M682 (Arg2, 0x06)
                            M680 (Arg0, 0x0370, 0x00, Local1, "FE7CB391D650A284")
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0371, 0x00, Local1, "FE7\vB391D650A284")
                            M680 (Arg0, 0x0372, 0x00, S6E6, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x0373, 0x00, Local1, "initial named string")
                            Local1 = M682 (Arg2, 0x06)
                            M680 (Arg0, 0x0374, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0375, 0x00, Local1, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0x0B, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                            M680 (Arg0, 0x0376, 0x00, B6E6, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                Case (0x08)
                {
                    /* Result Object returned by any Operator (Op): */
                    /* Add, Mid */
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x01)
                        {
                            /* Integer */

                            M680 (Arg0, 0x0379, 0x00, Local1, "initial named string")
                            Store ((I6E7 + 0x00), Local1)
                            If (F64)
                            {
                                M680 (Arg0, 0x037A, 0x00, Local1, 0xFE7CB391D650A284)
                            }
                            Else
                            {
                                M680 (Arg0, 0x037B, 0x00, Local1, 0xD650A284)
                            }

                            Local1 = 0xC179B3FE
                            M680 (Arg0, 0x037C, 0x00, Local1, 0xC179B3FE)
                            M680 (Arg0, 0x037D, 0x00, I6E7, 0xFE7CB391D650A284)
                        }
                        Case (0x02)
                        {
                            /* String */

                            M680 (Arg0, 0x037E, 0x00, Local1, "initial named string")
                            Local1 = Mid (S6E7, 0x02, 0x0E)
                            M680 (Arg0, 0x037F, 0x00, Local1, "7CB391D650A284")
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0380, 0x00, Local1, "7CB\v91D650A284")
                            M680 (Arg0, 0x0381, 0x00, S6E7, "FE7CB391D650A284")
                        }
                        Case (0x03)
                        {
                            /* Buffer */

                            M680 (Arg0, 0x0382, 0x00, Local1, "initial named string")
                            Local1 = Mid (B6E7, 0x01, 0x07)
                            M680 (Arg0, 0x0383, 0x00, Local1, Buffer (0x07)
                                {
                                     0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE         // .P...|.
                                })
                            Local1 [0x03] = 0x0B
                            M680 (Arg0, 0x0384, 0x00, Local1, Buffer (0x07)
                                {
                                     0xA2, 0x50, 0xD6, 0x0B, 0xB3, 0x7C, 0xFE         // .P...|.
                                })
                            M680 (Arg0, 0x0385, 0x00, B6E7, Buffer (0x08)
                                {
                                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                                })
                        }
                        Case (0x05)
                        {
                            /* Field Unit */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }
                        Case (0x0E)
                        {
                            /* Buffer Field */

                            Debug = "Not implemented"
                            ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            Return (0x01)
                        }

                    }
                }
                /* Additionally can be implemented cases: */
                /* Derefof of immediate Refof */
                /* Derefof of intermediate Object */
                /* Derefof of Reference returned by called Method */
                Default
                {
                    Debug = "Unexpected way to obtain some result Object"
                    ERR (TERR, Z123, __LINE__, 0x00, 0x00, Arg1, Arg2)
                    Return (0x01)
                }

            }

            Return (0x00)
        }

        M100 (Concatenate (__METHOD__, "-m100-S-IntC"), 0x01, 0x00)
        M100 (Concatenate (__METHOD__, "-m100-S-IntN"), 0x01, 0x01)
        M100 (Concatenate (__METHOD__, "-m100-S-IntL"), 0x01, 0x03)
        M100 (Concatenate (__METHOD__, "-m100-S-StrN"), 0x02, 0x01)
        M100 (Concatenate (__METHOD__, "-m100-S-StrL"), 0x02, 0x03)
        M100 (Concatenate (__METHOD__, "-m100-S-BufN"), 0x03, 0x01)
        M100 (Concatenate (__METHOD__, "-m100-S-BFldN"), 0x0E, 0x01)
    }

    /* Run-method */

    Method (RES0, 0, NotSerialized)
    {
        Debug = "TEST: RES0, Result Object processing in Store operator"
        /* Check storing of immediate Source Objects by Store() */

        M689 ("RES0-m689", 0x00, 0x00)
        /* Store() to Global Named Objects, Constant and LocalX */

        M690 ()
    }
