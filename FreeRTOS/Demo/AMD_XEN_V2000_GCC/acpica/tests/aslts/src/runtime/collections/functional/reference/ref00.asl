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
     * The common methods of the Reference tests
     *
     *
     * Methods used for to verify particular References:
     *
     *    m1a0, m1a1, m1a2
     */
    /*
     SEE: Investigate and report all y<XXX>.
     SEE: see everywhere "index of checking" and z0XX - through all ref files: corresponds?!!!!!!!!!
     SEE: add into m1a6 and all m000 the checking like these:
     Store(\i900, Debug)
     Store(\d900.i900, Debug)
     */
    Name (Z076, 0x4C)
    /* Check Boolean (CondRefOf) and the type of value */
    /* arg0 - reference to the value of arbitrary type */
    /* arg1 - expected type of value */
    /* arg2 - returned Boolean */
    /* arg3 - index of checking (inside the file) */
    Method (M1A0, 4, NotSerialized)
    {
        Local7 = M1A4 (Arg2, Arg3)
        SET0 (C081, 0x00, Arg3)
        If (Local7)
        {
            Local0 = ObjectType (Arg0)
            If ((Local0 != Arg1))
            {
                ERR (C080, Z076, __LINE__, 0x00, 0x00, Local0, Arg1)
            }
            /* if (c08b) */
            /* ATTENTION: exactly the same in m1a0 and m1a2 */
            Else
            {
                If (C089)
                {
                    /* Flag of Reference, object otherwise */

                    If (C082)
                    {
                        /* Test of exceptions */

                        M1A8 (Arg0, 0x00, 0x00)
                    }

                    If (C085)
                    {
                        /* Create the chain of references to LocalX, */
                        /* then dereference them. */
                        Local0 = RefOf (Arg0)
                        Local1 = RefOf (Local0)
                        Local2 = RefOf (Local1)
                        Local3 = RefOf (Local2)
                        Local4 = RefOf (Local3)
                        Local5 = RefOf (Local4)
                        Local6 = RefOf (Local5)
                        Local7 = RefOf (Local6)
                        Local6 = DerefOf (Local7)
                        Local5 = DerefOf (Local6)
                        Local4 = DerefOf (Local5)
                        Local3 = DerefOf (Local4)
                        Local2 = DerefOf (Local3)
                        Local1 = DerefOf (Local2)
                        Local0 = DerefOf (Local1)
                        Local7 = DerefOf (Local0)
                        /* Create the chain of references to LocalX, */
                        /* then dereference them. */
                        Local0 = M1A5 (Local7)
                    }
                }

                /* if(c089) */
                /* ATTENTION: exactly the same in m1a0 and m1a2 */
                /* (but, don't replace it by call to Method) */
                Method (M002, 1, NotSerialized)
                {
                    Arg0 = 0xABCD001A
                }

                /* Run verification of references (write/read) */

                If ((C083 == 0x01))
                {
                    C08A = 0xABCD001A
                    Arg0 = C08A /* \C08A */
                }
                ElseIf ((C083 == 0x02))
                {
                    C08A = 0xABCD001B
                    CopyObject (C08A, Arg0)
                }
                ElseIf ((C083 == 0x03))
                {
                    C08A = 0xABCD001C
                    Arg0 = C08A /* \C08A */
                    C08A = 0xABCD001D
                    CopyObject (C08A, Arg0)
                }

                Local7 = 0x00
                If ((C08B == 0x01))
                {
                    Local0 = RefOf (Arg0)
                    Local1 = ObjectType (Local0)
                    If ((Local1 != Arg1))
                    {
                        ERR (C080, Z076, __LINE__, 0x00, 0x00, Local1, Arg1)
                    }
                    Else
                    {
                        Local7 = 0x01
                    }
                }
                ElseIf ((C08B == 0x02))
                {
                    Local1 = CondRefOf (Arg0, Local0)
                    If ((Local1 != Ones))
                    {
                        ERR (C080, Z076, __LINE__, 0x00, 0x00, Local1, Arg1)
                    }
                    Else
                    {
                        Local1 = ObjectType (Local0)
                        If ((Local1 != Arg1))
                        {
                            ERR (C080, Z076, __LINE__, 0x00, 0x00, Local1, Arg1)
                        }
                        Else
                        {
                            Local7 = 0x01
                        }
                    }
                }

                If (Local7)
                {
                    /* Obtain RefOf_Reference to ArgX */

                    Local0 = RefOf (Arg0)
                    Local1 = ObjectType (Local0)
                    If ((Local1 != Arg1))
                    {
                        ERR (C080, Z076, __LINE__, 0x00, 0x00, Local1, Arg1)
                    }
                    Else
                    {
                        /* Check DerefOf */

                        Local1 = ObjectType (DerefOf (Local0))
                        If ((Local1 != Arg1))
                        {
                            ERR (C080, Z076, __LINE__, 0x00, 0x00, Local1, Arg1)
                        }

                        /* Check that writing into M2-ArgX-RefOf_Reference */
                        /* changes the original object (M1-ArgX): */
                        M002 (Local0)
                        Local1 = ObjectType (Arg0)
                        If ((Local1 != C009))
                        {
                            ERR (C080, Z076, __LINE__, 0x00, 0x00, Local1, C009)
                        }
                        ElseIf ((Arg0 != 0xABCD001A))
                        {
                            ERR (C080, Z076, __LINE__, 0x00, 0x00, Arg0, 0xABCD001A)
                        }
                        Else
                        {
                            /* Check that M1-LocalX-RefOf_Reference remains */
                            /* up to date after writing into M2-ArgX in M2 and */
                            /* thus updating the contents of the object */
                            /* referenced by M1-LocalX. */
                            Local1 = ObjectType (Local0)
                            If ((Local1 != C009))
                            {
                                ERR (C080, Z076, __LINE__, 0x00, 0x00, Local1, C009)
                            }
                            Else
                            {
                                Local1 = SizeOf (Local0)
                                If ((Local1 != ISZ0))
                                {
                                    ERR (C080, Z076, __LINE__, 0x00, 0x00, Local1, ISZ0)
                                }
                            }
                        }
                    }
                }
            }
        }

        /* if(Local7) */

        RST0 ()
    }

    /* Verifying reference to the Object nested inside Packages */
    /* arg0 - reference to the Object (may be to Package) */
    /* arg1 - type of the value referred by arg0 */
    /* arg2 - nesting level of the Packages */
    /*        (Package always is a 0-th element */
    /*         of previous Package) */
    /* arg3 - index of the Object inside the last Package */
    /* arg4 - type of the Object */
    /* arg5 - the benchmark value of Object for verification */
    /* arg6 - index of checking (inside the file) */
    Method (M1A2, 7, Serialized)
    {
        SET0 (C081, 0x00, Arg6)
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Local0 = ObjectType (Arg0)
        If ((Local0 != Arg1))
        {
            ERR (C080, Z076, __LINE__, 0x00, 0x00, Local0, Arg1)
        }
        /* if (c08b) */
        /* ATTENTION: exactly the same in m1a0 and m1a2 */
        Else
        {
            If (C089)
            {
                /* Flag of Reference, object otherwise */

                If (C082)
                {
                    /* Test of exceptions */

                    M1A8 (Arg0, 0x00, 0x00)
                }

                If (C085)
                {
                    /* Create the chain of references to LocalX, */
                    /* then dereference them. */
                    Local0 = RefOf (Arg0)
                    Local1 = RefOf (Local0)
                    Local2 = RefOf (Local1)
                    Local3 = RefOf (Local2)
                    Local4 = RefOf (Local3)
                    Local5 = RefOf (Local4)
                    Local6 = RefOf (Local5)
                    Local7 = RefOf (Local6)
                    Local6 = DerefOf (Local7)
                    Local5 = DerefOf (Local6)
                    Local4 = DerefOf (Local5)
                    Local3 = DerefOf (Local4)
                    Local2 = DerefOf (Local3)
                    Local1 = DerefOf (Local2)
                    Local0 = DerefOf (Local1)
                    Local7 = DerefOf (Local0)
                    /* Create the chain of references to LocalX, */
                    /* then dereference them. */
                    Local0 = M1A5 (Local7)
                }
                Else
                {
                    Local0 = Arg0
                }
            }
            Else
            {
                Local0 = Arg0
            }

            /* if(c089) */

            If (C084)
            {
                /* run verification of references (reading) */

                If (C089)
                {
                    /* Flag of Reference, object otherwise */
                    /*
                     * 17.2.5.9.1   ArgX Objects
                     *
                     * 1) Read from ArgX parameters
                     *    ObjectReference - Automatic dereference, return
                     *                      the target of the reference.
                     *                      Use of DeRefOf returns the same.
                     */
                    If (C087)
                    {
                        /* "Use of DeRefOf returns the same" */

                        Local2 = DerefOf (Local0)
                    }
                    Else
                    {
                        /* Automatic dereference */

                        Local2 = Local0
                    }
                }
                Else
                {
                    Local2 = Local0
                }

                /* if(c089) */

                LPN0 = Arg2
                While (LPN0)
                {
                    If ((LPN0 == 0x01))
                    {
                        Store (Local2 [Arg3], Local1)
                    }
                    Else
                    {
                        Store (Local2 [0x00], Local1)
                    }

                    Local2 = DerefOf (Local1)
                    LPN0--
                    LPC0++
                }

                Local0 = ObjectType (Local2)
                If ((Local0 != Arg4))
                {
                    ERR (C080, Z076, __LINE__, 0x00, 0x00, Local0, Arg4)
                }
                ElseIf ((Local2 != Arg5))
                {
                    ERR (C080, Z076, __LINE__, 0x00, 0x00, Local2, Arg5)
                }
            }

            /* if(c084) */
            /* ATTENTION: exactly the same in m1a0 and m1a2 */
            /* (but, don't replace it by call to Method) */
            Method (M002, 1, NotSerialized)
            {
                Arg0 = 0xABCD001A
            }

            /* Run verification of references (write/read) */

            If ((C083 == 0x01))
            {
                C08A = 0xABCD001A
                Arg0 = C08A /* \C08A */
            }
            ElseIf ((C083 == 0x02))
            {
                C08A = 0xABCD001B
                CopyObject (C08A, Arg0)
            }
            ElseIf ((C083 == 0x03))
            {
                C08A = 0xABCD001C
                Arg0 = C08A /* \C08A */
                C08A = 0xABCD001D
                CopyObject (C08A, Arg0)
            }

            Local7 = 0x00
            If ((C08B == 0x01))
            {
                Local0 = RefOf (Arg0)
                Local1 = ObjectType (Local0)
                If ((Local1 != Arg1))
                {
                    ERR (C080, Z076, __LINE__, 0x00, 0x00, Local1, Arg1)
                }
                Else
                {
                    Local7 = 0x01
                }
            }
            ElseIf ((C08B == 0x02))
            {
                Local1 = CondRefOf (Arg0, Local0)
                If ((Local1 != Ones))
                {
                    ERR (C080, Z076, __LINE__, 0x00, 0x00, Local1, Arg1)
                }
                Else
                {
                    Local1 = ObjectType (Local0)
                    If ((Local1 != Arg1))
                    {
                        ERR (C080, Z076, __LINE__, 0x00, 0x00, Local1, Arg1)
                    }
                    Else
                    {
                        Local7 = 0x01
                    }
                }
            }

            If (Local7)
            {
                /* Obtain RefOf_Reference to ArgX */

                Local0 = RefOf (Arg0)
                Local1 = ObjectType (Local0)
                If ((Local1 != Arg1))
                {
                    ERR (C080, Z076, __LINE__, 0x00, 0x00, Local1, Arg1)
                }
                Else
                {
                    /* Check DerefOf */

                    Local1 = ObjectType (DerefOf (Local0))
                    If ((Local1 != Arg1))
                    {
                        ERR (C080, Z076, __LINE__, 0x00, 0x00, Local1, Arg1)
                    }

                    /* Check that writing into M2-ArgX-RefOf_Reference */
                    /* changes the original object (M1-ArgX): */
                    M002 (Local0)
                    Local1 = ObjectType (Arg0)
                    If ((Local1 != C009))
                    {
                        ERR (C080, Z076, __LINE__, 0x00, 0x00, Local1, C009)
                    }
                    ElseIf ((Arg0 != 0xABCD001A))
                    {
                        ERR (C080, Z076, __LINE__, 0x00, 0x00, Arg0, 0xABCD001A)
                    }
                    Else
                    {
                        /* Check that M1-LocalX-RefOf_Reference remains */
                        /* up to date after writing into M2-ArgX in M2 and */
                        /* thus updating the contents of the object */
                        /* referenced by M1-LocalX. */
                        Local1 = ObjectType (Local0)
                        If ((Local1 != C009))
                        {
                            ERR (C080, Z076, __LINE__, 0x00, 0x00, Local1, C009)
                        }
                        Else
                        {
                            Local1 = SizeOf (Local0)
                            If ((Local1 != ISZ0))
                            {
                                ERR (C080, Z076, __LINE__, 0x00, 0x00, Local1, ISZ0)
                            }
                        }
                    }
                }
            }
        }

        RST0 ()
    }

    /* Check only Boolean (CondRefOf) */
    /* arg0 - returned Boolean */
    /* arg1 - index of checking (inside the file) */
    Method (M1A4, 2, NotSerialized)
    {
        SET0 (C081, 0x00, Arg1)
        Local7 = 0x01
        Local0 = ObjectType (Arg0)
        If ((Local0 != C009))
        {
            ERR (C080, Z076, __LINE__, 0x00, 0x00, Local0, C009)
            Local7 = 0x00
        }
        ElseIf ((Arg0 != Ones))
        {
            ERR (C080, Z076, __LINE__, 0x00, 0x00, Arg0, Ones)
            Local7 = 0x00
        }

        RST0 ()
        Return (Local7)
    }

    /* Create the chain of references to LocalX, then dereference them */

    Method (M1A5, 1, NotSerialized)
    {
        Local0 = RefOf (Arg0)
        Local1 = RefOf (Local0)
        Local2 = RefOf (Local1)
        Local3 = RefOf (Local2)
        Local4 = RefOf (Local3)
        Local5 = RefOf (Local4)
        Local6 = RefOf (Local5)
        Local7 = RefOf (Local6)
        Local6 = DerefOf (Local7)
        Local5 = DerefOf (Local6)
        Local4 = DerefOf (Local5)
        Local3 = DerefOf (Local4)
        Local2 = DerefOf (Local3)
        Local1 = DerefOf (Local2)
        Local0 = DerefOf (Local1)
        Local7 = DerefOf (Local0)
        Return (Local7)
    }

    /*
     * Set Global variables assignment applied in the tests
     *
     * arg0 - c080 - name of test
     * arg1 - c083 - run verification of references (write/read)
     * arg2 - c084 - run verification of references (reading)
     * arg3 - c085 - create the chain of references to LocalX, then dereference them
     * arg4 - c087 - apply DeRefOf to ArgX-ObjectReference
     * arg5 - c081 - absolute index of file initiating the checking
     */
    Method (M1AD, 6, NotSerialized)
    {
        Local0 = ObjectType (Arg0)
        If ((Local0 == C00A))
        {
            C080 = Arg0
        }

        C083 = Arg1
        C084 = Arg2
        C085 = Arg3
        C087 = Arg4
        If (Arg5)
        {
            C081 = Arg5
        }
    }

    /* Test skipped message */

    Method (M1AE, 3, NotSerialized)
    {
        Concatenate ("Test ", Arg0, Local0)
        Concatenate (Local0, " skipped due to the following issue:", Debug)
        Concatenate ("   ", Arg1, Debug)
        Local0 = ObjectType (Arg2)
        If ((Local0 == C00A))
        {
            Concatenate ("   ", Arg2, Debug)
        }
    }
