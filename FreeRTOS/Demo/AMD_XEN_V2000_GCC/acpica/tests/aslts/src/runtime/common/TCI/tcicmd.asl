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
     * The Test Command Interface with the ACPICA (_TCI)
     *
     * Note: _TCI and TCI mean the same in comments below.
     *       But, actually the name of the relevant predefined
     *       Method is _TCI.
     */
    Name (Z128, 0x80)
    Name (DE00, 0x00) /* Disable reporting errors from m3a4, needed in m3aa (not enough params) */
    Name (FOPT, 0x00) /* Flag of optimization */
    /*
     * Constants
     */
    /* Opcodes of the Test Commands provided by _TCI */
    Name (C200, 0x00CD0000)    /* _TCI-end statistics */
    Name (C201, 0x00CD0001)    /* _TCI-begin statistics */
    Name (C202, 0x00CD0002)    /* TCI_CMD_CHECK_SUPPORTED */
    Name (C203, 0x00CD0003)    /* TCI_CMD_GET_ID_OF_THREADS */
    /* Tags of commands (to be filled into TCI Package by aslts) */

    Name (C208, 0xEEEE0596)  /* TCI_TAG_GET_MC_STAT_AFTER_TCI_TERM */
    Name (C209, 0xBBBB063A)  /* TCI_TAG_GET_MC_STAT_BEFORE_TCI_RUN */
    Name (C20A, 0xCCCC07B9)  /* TCI_TAG_CHECK_SUPPORTED */
    Name (C20B, 0xDDDD01F5)  /* TCI_TAG_GET_ID_OF_THREADS */
    /*
     * The layout of the Package for Memory Consumption Statistics
     * applied for TCI commands:
     *   _TCI-end statistics (command TCI_CMD_GET_MC_STAT_AFTER_TCI_TERM)
     *   _TCI-begin statistics (command TCI_CMD_GET_MC_STAT_BEFORE_TCI_RUN)
     */
    Name (C210, 0x00) /* Title */
    Name (C211, 0x04) /* acq0 */
    Name (C212, 0x09) /* acq1 (-) */
    Name (C213, 0x0E) /* acq2 (-) */
    Name (C214, 0x13) /* acq3 */
    Name (C215, 0x18) /* acq4 (-) */
    Name (C216, 0x1D) /* acq5 */
    Name (C217, 0x22) /* rel0 */
    Name (C218, 0x27) /* rel1 */
    Name (C219, 0x2C) /* rel2 (-) */
    Name (C21A, 0x31) /* rel3 */
    Name (C21B, 0x36) /* Created Objects */
    Name (C21C, 0x54) /* Deleted Objects */
    Name (C21D, 0x72) /* Miscellaneous Stat */
    Name (C220, 0x79) /* the length of the Package for */
    /* Memory Consumption Statistics. */
    /* The layout of header of the common _TCI Package */
    /* Input, data of header passed to ACPICA */
    Name (C222, 0x00)   /* Tag of command (to be set up by aslts) */
    /* Output, data of header returned to aslts from ACPICA */

    Name (C223, 0x01)   /* Size (number of elements actually packed into TCI package, */
    /* to be filled by ACPICA) */

    Name (C224, 0x02)   /* Cmd (command has been executed, to be filled by ACPICA) */
    Name (C225, 0x03)   /* CACHE_ENABLED (object cache is enabled info flag, */
    /* to be filled by ACPICA) */

    Name (C22B, 0x04)   /* length of the common _TCI Package header */
    /* The layout of header of TCI_CMD_GET_ID_OF_THREADS command */
    /* (returned to aslts from ACPICA) */
    Name (C22C, 0x04)   /* TCI_PACKAGE_THR_NUM */
    Name (C22D, 0x05)   /* TCI_PACKAGE_THR_NUM_REAL */
    Name (C22E, 0x06)   /* TCI_PACKAGE_THR_ID */
    Name (C22F, 0x07)   /* length TCI_PACKAGE_THR_HEADER_SIZE */
    Name (C221, 0x05)   /* CACHE_LISTS_NUMBER (Object Caches): */
    /*   CLIST_ID_NAMESPACE     0 -- Acpi-Namespace */
    /*   CLIST_ID_STATE         1 -- Acpi-State */
    /*   CLIST_ID_OPERAND       2 -- Acpi-Operand */
    /*   CLIST_ID_PSNODE        3 -- Acpi-Parse */
    /*   CLIST_ID_PSNODE_EXT    4 -- Acpi-ParseExt */
    Name (C226, 0x00)   /* CLIST_ID_NAMESPACE */
    Name (C227, 0x01)   /* CLIST_ID_STATE */
    Name (C228, 0x02)   /* CLIST_ID_OPERAND */
    Name (C229, 0x03)   /* CLIST_ID_PSNODE */
    Name (C22A, 0x04)   /* CLIST_ID_PSNODE_EXT */
    /*
     * The main Test Command interface with the ACPICA
     *
     * arg0 - opcode of the Test Command
     * arg1 - Package for different needs depending on the command.
     *        So, in case of the Memory Consumption Statistics commands it
     *        is filled by ACPICA with the Memory Consumption Statistics.
     *        The length of package in this case should be not less than c220,
     *        otherwise, no any failure arises but not all data are returned
     *        by Package just only the relevant part of it. It is true for all
     *        commands.
     * Note: use m3a0 or m165 to prepare the arg1-package.
     */
    Method (_TCI, 2, NotSerialized)
    {
        /*
         * Before to run this method reset location
         * of Command which is to be filled by ACPICA
         * to acknowledge the interconnection.
         * It is performed in m3a0 and m3a4.
         */
        Return (Arg1)
    }

    /*
     * Create and initialize the Package for _TCI
     *
     * arg0 - opcode of the Test Command.
     *        Use 0 for allocation without initialization.
     * arg1 - number of element of Package (for some of commands)
     *
     * Return the resulting Package:
     *
     *   - if arg0 is zero - the Package of c220 length
     *   - otherwise - the Package of length depending on
     *     the command is additionally initialized
     */
    Method (M165, 2, Serialized)
    {
        Name (NUM, 0x00)
        Name (TAG, 0x00)
        If (Arg0)
        {
            Switch (ToInteger (Arg0))
            {
                Case (0x00CD0000)
                {
                    /* _TCI-end statistics */

                    TAG = C208 /* \C208 */
                    NUM = C220 /* \C220 */
                }
                Case (0x00CD0001)
                {
                    /* _TCI-begin statistics */

                    TAG = C209 /* \C209 */
                    NUM = C220 /* \C220 */
                }
                Case (0x00CD0002)
                {
                    /* TCI_CMD_CHECK_SUPPORTED */

                    TAG = C20A /* \C20A */
                    NUM = C22B /* \C22B */
                }
                Case (0x00CD0003)
                {
                    /* TCI_CMD_GET_ID_OF_THREADS */

                    TAG = C20B /* \C20B */
                    NUM = Arg1
                }
                Default
                {
                    ERR ("m165", Z128, __LINE__, 0x00, 0x00, Arg0, 0x00)
                }

            }

            If ((NUM < C22B))
            {
                ERR ("m165", Z128, __LINE__, 0x00, 0x00, NUM, C22B)
            }
            Else
            {
                Name (P000, Package (NUM){})
                Name (LPN0, 0x00)
                Name (LPC0, 0x00)
                LPN0 = NUM /* \M165.NUM_ */
                LPC0 = 0x00
                While (LPN0)
                {
                    P000 [LPC0] = 0x00
                    LPN0--
                    LPC0++
                }

                P000 [0x00] = TAG /* \M165.TAG_ */
                Return (P000) /* \M165.P000 */
            }
        }
        Else
        {
            Name (P001, Package (C220){})
            Return (P001) /* \M165.P001 */
        }

        Return (0x00)
    }

    /*
     * Create and initialize the Package for simple cases
     * entirely specified by the opcode of command.
     *
     * a. for Memory Consumption Statistics
     *    (_TCI-begin or _TCI-end statistics).
     *
     * b. TCI_CMD_CHECK_SUPPORTED
     *
     * arg0 - opcode of the Test Command.
     *        Use 0 for allocation without initialization.
     *
     * Returns the TCI Package
     */
    Method (M3A0, 1, NotSerialized)
    {
        Local0 = M165 (Arg0, 0x00)
        Return (Local0)
    }

    Method (M3A1, 2, NotSerialized)
    {
        Local0 = DerefOf (NMTP [Arg1])
        Concatenate ("", Arg0, Local2)
        Concatenate (Local2, " ", Local1)
        Concatenate (Local1, Local0, Debug)
    }

    /*
     * Print out the Memory Consumption Statistics Package
     *
     * arg0 - Memory Consumption Statistics Package
     * arg1 - opcode of the title message
     */
    Method (M3A2, 2, Serialized)
    {
        If ((Arg1 == 0x00))
        {
            Debug = "==== _TCI-end statistics"
        }
        ElseIf ((Arg1 == 0x01))
        {
            Debug = "==== _TCI-begin statistics"
        }
        ElseIf ((Arg1 == 0x02))
        {
            Debug = "==== _TCI-end-begin difference"
        }
        Else
        {
            Debug = "???"
        }

        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        LPN0 = C220 /* \C220 */
        LPC0 = 0x00
        Local1 = 0x00
        Local2 = 0x00
        While (LPN0)
        {
            If ((LPC0 == C210))
            {
                Debug = "Title:"
            }
            ElseIf ((LPC0 == C211))
            {
                Debug = "acq0:  all calls to AcpiUtAcquireFromCache"
            }
            ElseIf ((LPC0 == C212))
            {
                Debug = "acq1: +AcpiUtAcquireMutex"
            }
            ElseIf ((LPC0 == C213))
            {
                Debug = "acq2: +there is a cache object available"
            }
            ElseIf ((LPC0 == C214))
            {
                Debug = "acq3: +AcpiUtReleaseMutex"
            }
            ElseIf ((LPC0 == C215))
            {
                Debug = "acq4: +otherwise, the cache is empty, create a new object"
            }
            ElseIf ((LPC0 == C216))
            {
                Debug = "acq5: +AcpiUtReleaseMutex"
            }
            ElseIf ((LPC0 == C217))
            {
                Debug = "rel0:  all calls to AcpiUtReleaseToCache"
            }
            ElseIf ((LPC0 == C218))
            {
                Debug = "rel1: +walk cache is full, just free this object"
            }
            ElseIf ((LPC0 == C219))
            {
                Debug = "rel2: +otherwise, put this object back into the cache"
            }
            ElseIf ((LPC0 == C21A))
            {
                Debug = "rel3: +AcpiUtAcquireMutex"
            }
            ElseIf ((LPC0 == C21B))
            {
                Debug = "Created Objects:"
            }
            ElseIf ((LPC0 == C21C))
            {
                Debug = "Deleted Objects:"
            }
            ElseIf ((LPC0 == C21D))
            {
                Debug = "Miscellaneous Stat:"
            }

            If ((LPC0 >= C21D))
            {
                Debug = DerefOf (Arg0 [LPC0])
            }
            ElseIf ((LPC0 >= C21C))
            {
                Local0 = DerefOf (Arg0 [LPC0])
                M3A1 (Local0, Local1)
                Local1++
            }
            ElseIf ((LPC0 >= C21B))
            {
                Local0 = DerefOf (Arg0 [LPC0])
                M3A1 (Local0, Local2)
                Local2++
            }
            Else
            {
                Debug = DerefOf (Arg0 [LPC0])
            }

            LPN0--
            LPC0++
        }
    }

    /*
     * Calculate the difference between the two
     * Memory Consumption Statistics Packages.
     *
     * arg0 - Package of _TCI-end statistics
     * arg1 - Package of _TCI-begin statistics
     * arg2 - Package for _TCI-end-begin difference
     */
    Method (M3A3, 3, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        LPN0 = C220 /* \C220 */
        LPC0 = 0x00
        While (LPN0)
        {
            Local0 = DerefOf (Arg0 [LPC0])
            Local1 = DerefOf (Arg1 [LPC0])
            Local2 = (Local1 - Local0)
            Arg2 [LPC0] = Local2
            LPN0--
            LPC0++
        }
    }

    /*
     * Verify difference of Memory Consumption Statistics between
     * two points: _TCI-end statistics and _TCI-begin statistics
     * (and reset locations of Command of arg0 and arg1 Packages
     * for the following run).
     *
     * Check that the Memory Consumption Statistics measured at the first point
     * as '_TCI-end statistics' was then changed as expected to the second point
     * where statistics was measured as '_TCI-begin statistics'. Between these
     * two points we initiate some AML activity which involves the memory
     * consumption acquire/release to be then analyzed and verified.
     *
     *
     * arg0 - Package of _TCI-end statistics
     * arg1 - Package of _TCI-begin statistics
     * arg2 - Package for _TCI-end-begin difference
     * arg3 - Package with the benchmark information on Created Objects
     * arg4 - Package with the benchmark information on Deleted Objects
     *        (if non-Package, then arg3 is used)
     * arg5 - Package with the benchmark information on memory acq0 and rel0
     *        (if non-Package, then compare acq0 and rel0 of arg2,
     *         otherwise, arg5 is a Package with the expected per-memory
     *         type differences, expected: acq0[i] - rel0[i] = arg5[i])
     * arg6 - index of checking (inside the file)
     *
     * Return:
     *           0 - success
     *           1 - incorrect Memory Consumption Statistics encountered
     *   otherwise - failed to determine the Memory Consumption Statistics
     *
     * See: the time of execution can be reduced (design and use additional flags):
     * - exclude initialization before each operation
     *   (ACPICA writes all elements, benchmarks for the
     *   following sub-test mostly differ previous ones)
     * - restrict checkings (use flag) by the acq0 & rel0,
     *   and add & del.
     */
    Method (M3A4, 7, Serialized)
    {
        /* Flag of printing */

        Name (PR1, 0x00)
        Name (PR2, 0x00)
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        If (PR1)
        {
            M3A2 (Arg0, 0x00)
            M3A2 (Arg1, 0x01)
        }

        If (PR2)
        {
            M3A2 (Arg2, 0x02)
        }

        Local7 = 0x00
        /* Check headers of Packages */

        If (M3A6 (Arg0, 0x00, Arg6))
        {
            Local7 = 0x02
        }

        If (M3A6 (Arg1, 0x01, Arg6))
        {
            Local7 = 0x02
        }

        /* Check statistics specified by index */

        If (M3A7 (Arg0, 0x00, Arg6))
        {
            Local7 = 0x02
        }

        If (M3A7 (Arg1, 0x00, Arg6))
        {
            Local7 = 0x02
        }

        If (M3A7 (Arg2, 0x01, Arg6))
        {
            Local7 = 0x02
        }

        /*
         * acq0 and rel0 of arg2-difference
         * are to be equal each to another
         * (or correspond to arg5):
         */
        If ((ObjectType (Arg5) == C00C))
        {
            Local0 = C211 /* \C211 */
            Local1 = C217 /* \C217 */
            Local4 = 0x00
            LPN0 = C221 /* \C221 */
            LPC0 = 0x00
            While (LPN0)
            {
                Local2 = DerefOf (Arg2 [Local0])
                Local3 = DerefOf (Arg2 [Local1])
                Local5 = DerefOf (Arg5 [Local4])
                Local6 = (Local2 - Local3)
                If ((Local6 != Local5))
                {
                    If (!DE00)
                    {
                        ERR ("m3a4", Z128, __LINE__, 0x00, Arg6, Local6, Local5)
                        Debug = LPC0 /* \M3A4.LPC0 */
                        Debug = Local0
                        Debug = Local1
                        Debug = Local4
                        Debug = Local2
                        Debug = Local3
                        Debug = Local5
                        Debug = Local6
                    }

                    Local7 = 0x01
                }

                Local0++
                Local1++
                Local4++
                LPN0--
                LPC0++
            }
        }
        Else
        {
            Local0 = C211 /* \C211 */
            Local1 = C217 /* \C217 */
            LPN0 = C221 /* \C221 */
            LPC0 = 0x00
            While (LPN0)
            {
                Local2 = DerefOf (Arg2 [Local0])
                Local3 = DerefOf (Arg2 [Local1])
                If ((Local2 != Local3))
                {
                    If (!DE00)
                    {
                        ERR ("m3a4", Z128, __LINE__, 0x00, Arg6, Local2, Local3)
                    }

                    Local7 = 0x01
                }

                Local0++
                Local1++
                LPN0--
                LPC0++
            }
        }

        /* arg2-difference: acq0 == acq3 + acq5 */

        Local0 = C211 /* \C211 */
        Local1 = C214 /* \C214 */
        Local2 = C216 /* \C216 */
        LPN0 = C221 /* \C221 */
        LPC0 = 0x00
        While (LPN0)
        {
            Local3 = DerefOf (Arg2 [Local0])
            Local4 = DerefOf (Arg2 [Local1])
            Local5 = DerefOf (Arg2 [Local2])
            Local6 = (Local4 + Local5)
            If ((Local3 != Local6))
            {
                If (!DE00)
                {
                    ERR ("m3a4", Z128, __LINE__, 0x00, Arg6, Local3, Local6)
                }

                Local7 = 0x01
            }

            Local0++
            Local1++
            Local2++
            LPN0--
            LPC0++
        }

        /* arg2-difference: rel0 == rel1 + rel3 */

        Local0 = C217 /* \C217 */
        Local1 = C218 /* \C218 */
        Local2 = C21A /* \C21A */
        LPN0 = C221 /* \C221 */
        LPC0 = 0x00
        While (LPN0)
        {
            Local3 = DerefOf (Arg2 [Local0])
            Local4 = DerefOf (Arg2 [Local1])
            Local5 = DerefOf (Arg2 [Local2])
            Local6 = (Local4 + Local5)
            If ((Local3 != Local6))
            {
                If (!DE00)
                {
                    ERR ("m3a4", Z128, __LINE__, 0x00, Arg6, Local3, Local6)
                }

                Local7 = 0x01
            }

            Local0++
            Local1++
            Local2++
            LPN0--
            LPC0++
        }

        /* Check, created Objects are identical to the benchmark ones */

        If ((ObjectType (Arg3) == C00C))
        {
            LPN0 = C027 /* \C027 */
            Local0 = C21B /* \C21B */
            Local1 = 0x00
            While (LPN0)
            {
                Local2 = DerefOf (Arg2 [Local0])
                Local3 = DerefOf (Arg3 [Local1])
                If ((Local2 != Local3))
                {
                    If (!DE00)
                    {
                        ERR ("m3a4", Z128, __LINE__, 0x00, Arg6, Local2, Local3)
                    }

                    Local7 = 0x01
                }

                Local0++
                Local1++
                LPN0--
            }
        }

        /* Check, deleted Objects are identical to the benchmark ones */

        LPN0 = C027 /* \C027 */
        Local0 = C21C /* \C21C */
        Local1 = 0x00
        Local4 = 0x00
        If ((ObjectType (Arg4) == C00C))
        {
            Local4 = Arg4
        }
        ElseIf ((ObjectType (Arg3) == C00C))
        {
            Local4 = Arg3
        }

        If ((ObjectType (Local4) == C00C))
        {
            While (LPN0)
            {
                Local2 = DerefOf (Arg2 [Local0])
                Local3 = DerefOf (Local4 [Local1])
                If ((Local2 != Local3))
                {
                    If (!DE00)
                    {
                        ERR ("m3a4", Z128, __LINE__, 0x00, Arg6, Local2, Local3)
                    }

                    Local7 = 0x01
                }

                Local0++
                Local1++
                LPN0--
            }
        }

        /*
         * Reset locations of Command of arg0 and arg1
         * Packages for the following run.
         * Store(0, Index(arg0, c224))
         * Store(0, Index(arg1, c224))
         */
        Return (Local7)
    }

    /*
     * Return non-zero in case the Test Command interface
     * with the ACPICA (_TCI) is supported.
     */
    Method (M3A5, 0, NotSerialized)
    {
        Local0 = M3A0 (C202)   /* TCI_CMD_CHECK_SUPPORTED */
        _TCI (C202, Local0)
        Local1 = DerefOf (Local0 [C224])
        If ((Local1 != C202))
        {
            Return (0x00)
        }

        Return (0x01)
    }

    /*
     * Check header of Memory Consumption Statistics Package
     * arg0 - Memory Consumption Statistics Package
     * arg1 - Means:
     *        0         - _TCI-end statistics
     *        otherwise - _TCI-begin statistics
     * arg2 - index of checking (inside the file)
     */
    Method (M3A6, 3, NotSerialized)
    {
        Local7 = 0x00
        /* Tag of command */

        If (Arg1)
        {
            Local0 = C209 /* \C209 */
        }
        Else
        {
            Local0 = C208 /* \C208 */
        }

        Local1 = DerefOf (Arg0 [0x00])
        If ((Local1 != Local0))
        {
            ERR ("m3a6", Z128, __LINE__, 0x00, Arg2, Local1, Local0)
            Local7 = 0x01
        }

        /* Number of elements actually packed */

        Local1 = DerefOf (Arg0 [0x01])
        If ((Local1 != C220))
        {
            ERR ("m3a6", Z128, __LINE__, 0x00, Arg2, Local1, C220)
            Local7 = 0x01
        }

        /* Command has been executed */

        If (Arg1)
        {
            Local0 = C201 /* \C201 */
        }
        Else
        {
            Local0 = C200 /* \C200 */
        }

        Local1 = DerefOf (Arg0 [0x02])
        If ((Local1 != Local0))
        {
            ERR ("m3a6", Z128, __LINE__, 0x00, Arg2, Local1, Local0)
            Local7 = 0x01
        }

        /* Object cache is enabled */

        Local1 = DerefOf (Arg0 [0x03])
        If (!Local1)
        {
            ERR ("m3a6", Z128, __LINE__, 0x00, Arg2, Local1, 0x01)
            Local7 = 0x01
        }

        Return (Local7)
    }

    /*
     * Check statistics specified by index
     *
     * arg0 - Memory Consumption Statistics Package
     * arg1 - Means:
     *        non-zero  - _TCI-end-begin difference Package
     *        otherwise - usual Memory Consumption Statistics Package
     * arg2 - index of checking (inside the file)
     */
    Method (M3A7, 3, NotSerialized)
    {
        Local7 = 0x00
        If (Arg1){        /*
         // ACPI_STAT_SUCCESS_FREE == ACPI_STAT_SUCCESS_ALLOC
         Add(c21d, 5, Local0)
         Store(DerefOf(Index(arg0, Local0)), Local1)
         Increment(Local0)
         Store(DerefOf(Index(arg0, Local0)), Local2)
         if (LNotEqual(Local2, Local1)) {
         err("m3a7", z128, __LINE__, 0, arg2, Local2, Local1)
         Store(1, Local7)
         }
         */
        }
        Else
        {
            /* ACPI_STAT_INVALID_EXBUF */

            Local0 = C21D /* \C21D */
            Local1 = DerefOf (Arg0 [Local0])
            If (Local1)
            {
                ERR ("m3a7", Z128, __LINE__, 0x00, Arg2, Local1, 0x00)
                Local7 = 0x01
            }

            /* ACPI_STAT_ZONE0_CORRUPTED */

            Local0++
            Local1 = DerefOf (Arg0 [Local0])
            If (Local1)
            {
                ERR ("m3a7", Z128, __LINE__, 0x00, Arg2, Local1, 0x00)
                Local7 = 0x01
            }

            /* ACPI_STAT_ZONE1_CORRUPTED */

            Local0++
            Local1 = DerefOf (Arg0 [Local0])
            If (Local1)
            {
                ERR ("m3a7", Z128, __LINE__, 0x00, Arg2, Local1, 0x00)
                Local7 = 0x01
            }

            /* ACPI_STAT_FAILED_ALLOC */

            Local0++
            Local1 = DerefOf (Arg0 [Local0])
            If (Local1)
            {
                ERR ("m3a7", Z128, __LINE__, 0x00, Arg2, Local1, 0x00)
                Local7 = 0x01
            }

            /* ACPI_STAT_NULL_FREE */

            Local0++
            Local1 = DerefOf (Arg0 [Local0])
            If (Local1)
            {
                ERR ("m3a7", Z128, __LINE__, 0x00, Arg2, Local1, 0x00)
                Local7 = 0x01
            }
        }

        Return (Local7)
    }

    /*
     * Create and initialize the sample Package for the
     * per-object type benchmark Memory Consumption Statistics
     */
    Method (M3A8, 0, Serialized)
    {
        Name (P000, Package (0x20)
        {
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
        })
        Return (P000) /* \M3A8.P000 */
    }

    /*
     * Create and initialize the sample Package for the
     * per-memory type benchmark Memory Consumption Statistics
     */
    Method (M3A9, 0, Serialized)
    {
        Name (P000, Package (0x07)
        {
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00
        })
        Return (P000) /* \M3A9.P000 */
    }

    /*
     * Determine the flag of optimization: check that
     * processing of the Add operation corresponds to
     * the expectation: optimized/non-optimized.
     *
     * Mode of run, optimized/non-optimized, is essential
     * for this kind tests (memory consumption).
     *
     * arg0 - Means:
     *           0 - check for Optimization is tuned off
     *   otherwise - check for Optimization is tuned on
     */
    Method (M3AA, 0, Serialized)
    {
        Name (I000, 0x00)
        Name (P000, Package (0x01){})
        Name (P00B, Package (0x01){})
        FOPT = 0xFF
        Local0 = M3A0 (C200)   /* _TCI-end statistics */
        P00B = M3A0 (C201)     /* _TCI-begin statistics */
        Local1 = M3A0 (0x00)      /* difference */
        _TCI (C200, Local0)
        Store ((0x03 + 0x04), I000) /* \M3AA.I000 */
        _TCI (C201, P00B)
        M3A3 (Local0, P00B, Local1)
        /* Statistics expected in case Optimization is tuned off */

        P000 = M3A8 ()
        P000 [C009] = 0x04 /* Integer */
        DE00 = 0x01
        Local6 = M3A4 (Local0, P00B, Local1, P000, 0x00, 0x00, 0x00)
        DE00 = 0x00
        If ((Local6 == 0x02))
        {
            Debug = "Failed to determine the flag of optimization"
            Return (Zero)
        }
        Else
        {
            /* Statistics expected in case Optimization is tuned on */

            P000 = M3A8 ()
            P000 [C009] = 0x01 /* Integer */
            DE00 = 0x01
            Local7 = M3A4 (Local0, P00B, Local1, P000, 0x00, 0x00, 0x01)
            DE00 = 0x00
            If ((Local7 == 0x02))
            {
                Debug = "Failed to determine the flag of optimization"
                Return (Zero)
            }
        }

        If ((Local6 == Local7))
        {
            Debug = "Internal error 0"
            ERR ("m3aa", Z128, __LINE__, 0x00, 0x00, Local6, Local7)
        }
        ElseIf (Local6)
        {
            FOPT = 0x01
        }
        Else
        {
            FOPT = 0x00
        }
    }

    /*
     * Return Package with the array of thread indexes
     * otherwise Integer 0.
     *
     * arg0 - number of threads
     */
    Method (M163, 1, Serialized)
    {
        Name (SIZE, 0x00)
        SIZE = (C22F + Arg0)
        Local0 = M165 (C203, SIZE) /* TCI_CMD_GET_ID_OF_THREADS */
        _TCI (C203, Local0)
        Local1 = DerefOf (Local0 [C224])
        If ((Local1 != C203))
        {
            Return (0x00)
        }

        Return (Local0)
    }
