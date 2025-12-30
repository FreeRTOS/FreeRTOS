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
     * Objects of common use to provide the common control of test run,
     * provide the uniform structure of all run-time tests.
     *
     * The full applied hierarchy of test-concepts follows:
     * - test suite       (aslts)
     * - test collection  (functional, complex, exceptions,...)
     * - test case        (arithmetic, bfield, exc, opackageel,..)
     * - test (or root method) simplest test unit supplied with the
     *         status line and evaluated as [PASS|FAIL|BLOCKED|SKIPPED].
     */
    Name (Z062, 0x3E)
    Name (FF32, 0xFFFFFFFF)          /* -1, 32-bit */
    Name (FF64, Ones)                /* -1, 64-bit */
    /* Test execution trace */

    Name (TRCF, 0x00)            /* Trace enabling flag */
    Name (TRCH, "ASLTS")      /* Head of trace message */
    Name (STST, "STST")   /* Head of summary status message of test run */
    Name (CTST, "CTST")   /* Head of current status message of test run */
    Name (PR01, 0x01)            /* Printing starts of sub-tests */
    Name (PR02, 0x01)            /* More detailed printing */
    /* Start time (Timer-time) of running test */

    Name (TMT0, 0x00)
    /* Flag of multi-threading mode */

    Name (MTHR, 0x00)
    /* Set the multi-threading mode flag */

    Method (SET3, 1, NotSerialized)
    {
        MTHR = Arg0
    }

    /* From Integer arithmetic */

    Name (C000, 0x0A)
    Name (C001, 0x05)
    /* From Logical operators */

    Name (C002, 0x0D)
    Name (C003, 0x0C)
    Name (C004, 0x06)
    Name (C005, 0x04)
    Name (C006, 0x1F)
    Name (C007, 0x33)
    /* Types, as returned by ObjectType */

    Name (C008, 0x00)   /* Uninitialized */
    Name (C009, 0x01)   /* Integer */
    Name (C00A, 0x02)   /* String */
    Name (C00B, 0x03)   /* Buffer */
    Name (C00C, 0x04)   /* Package */
    Name (C00D, 0x05)   /* Field Unit */
    Name (C00E, 0x06)   /* Device */
    Name (C00F, 0x07)   /* Event */
    Name (C010, 0x08)   /* Method */
    Name (C011, 0x09)   /* Mutex */
    Name (C012, 0x0A)  /* Operation Region */
    Name (C013, 0x0B)  /* Power Resource */
    Name (C014, 0x0C)  /* Processor */
    Name (C015, 0x0D)  /* Thermal Zone */
    Name (C016, 0x0E)  /* Buffer Field */
    Name (C017, 0x0F)  /* DDB Handle */
    Name (C018, 0x10)  /* Debug Object */
    Name (C019, 0x11)  /* LOCAL_REGION_FIELD */
    Name (C01A, 0x12)  /* LOCAL_BANK_FIELD */
    Name (C01B, 0x13)  /* LOCAL_INDEX_FIELD */
    Name (C01C, 0x14)  /* LOCAL_REFERENCE */
    Name (C01D, 0x15)  /* LOCAL_ALIAS */
    Name (C01E, 0x16)  /* LOCAL_METHOD_ALIAS */
    Name (C01F, 0x17)  /* LOCAL_NOTIFY */
    Name (C020, 0x18)  /* LOCAL_ADDRESS_HANDLER */
    Name (C021, 0x19)  /* LOCAL_RESOURCE */
    Name (C022, 0x1A)  /* LOCAL_RESOURCE_FIELD */
    Name (C023, 0x1B)  /* LOCAL_SCOPE */
    Name (C024, 0x1C)  /* LOCAL_EXTRA */
    Name (C025, 0x1D)  /* LOCAL_DATA */
    Name (C027, 0x1E)  /* Number of different types */
    Name (C028, 0x00)   /* Reserved (first) */
    /* The name of type Package */

    Name (NMTP, Package (0x20)
    {
        "Uninitialized",
        "Integer",
        "String",
        "Buffer",
        "Package",
        "Field Unit",
        "Device",
        "Event",
        "Method",
        "Mutex",
        "Operation Region",
        "Power Resource",
        "Processor",
        "Thermal Zone",
        "Buffer Field",
        "DDB Handle",
        "Debug Object",
        "LOCAL_REGION_FIELD",
        "LOCAL_BANK_FIELD",
        "LOCAL_INDEX_FIELD",
        "LOCAL_REFERENCE",
        "LOCAL_ALIAS",
        "LOCAL_METHOD_ALIAS",
        "LOCAL_NOTIFY",
        "LOCAL_ADDRESS_HANDLER",
        "LOCAL_RESOURCE",
        "LOCAL_RESOURCE_FIELD",
        "LOCAL_SCOPE",
        "LOCAL_EXTRA",
        "LOCAL_DATA",
        "--",
        "--"
    })
    /* Global variables for an arbitrary use inside the particular Run-methods */

    Name (C080, 0x00)
    Name (C081, 0x00)
    Name (C082, 0x00)
    Name (C083, 0x00)
    Name (C084, 0x00)
    Name (C085, 0x00)
    Name (C086, 0x00)
    Name (C087, 0x00)
    Name (C088, 0x00)
    Name (C089, 0x00)
    Name (C08A, 0x00)
    Name (C08B, 0x00)
    Name (C08C, 0x00788B60) /* used in operand tests (801 - 2 msec) */
    /*
     * Flag:
     *    non-zero - prohibits non-precise opcode exceptions
     *               (one particular opcode of exception is verified).
     *    0 - only presence of some exception(s) is verified.
     */
    Name (EXCV, 0x00)
    /*
     * An "absolute index of file reporting error" used for reporting errors
     * from the bug-demo files (only!). It is the same for all the bug-demo files
     * (files of TCLD type tests). It is not even an index of file as such in this
     * case but only designation of reporting error from some bug-demo file. The
     * actual number of bug (NNN) in this case is taken from TIND and the same file
     * name like this "*NNN.asl" is reported for all the bug-demo files corresponding
     * to the same bug where NNN is the number of bug. So, "indexes of errors
     * (inside the file)" corresponding to the same bug should differ through
     * all files of that bug.
     */
    Name (ZFFF, 0x07FF)
    /*
     * Flag: 0 - 32, 1 - 64
     */
    Name (F64, 0x00)
    /*
     * Byte and character size of Integer
     */
    Name (ISZ0, 0x00)
    Name (ISZC, 0x00)
    /*
     * The tests execution trace.
     *
     * ETR0 - the size of trace Packages
     * ETR1 - the number of units (ETR0/3) in trace Packages
     * ERRP - Package for summary information about the first ETR1 errors
     * RP0P - Package to store the first ETR0 status lines of the
     *        root Methods run results.
     * RMRC - current number of root Methods runs
     */
    Name (ETR0, 0x04B0)
    Name (ETR1, 0x0190)
    Name (ERRP, Package (ETR0){})
    Name (RP0P, Package (ETR0){})
    Name (RMRC, 0x00)
    /*
     * Errors handling
     * (ERR0 & ERR2) overwrite (arg3 & arg4) of err()
     * (but there is no remained ArgX for ERR1 in err()).
     */
    Name (ERRS, 0x00)   /* Errors counter */
    Name (ERRB, 0x00)   /* Error opcode base */
    Name (ERR0, 0x00)   /* Absolute index of file initiating the checking */
    Name (ERR1, 0x00)   /* Name of Method initiating the checking */
    Name (ERR2, 0x00)   /* Index of checking */
    Name (ERR3, 0x00)   /* Current indicator of errors */
    Name (ERR4, 0x00)   /* Full print out of ERRORS SUMMARY */
    Name (ERR5, 0x00)   /* Used to calculate the number of errors of root Method */
    Name (ERR6, 0x00)   /* The number of failed root Methods (tests) */
    Name (ERR7, 0x00)   /* The number of errors detected during the loading stage */
    Name (FNAM, 0x00)   /* Test filename */
    /*
     * Set parameters of current checking
     *
     * arg0 - absolute index of file initiating the checking
     * arg1 - name of Method initiating the checking
     * arg2 - index of checking (inside the file)
     *
     * ATTENTION:
     * These globals are introduced due to the lack of
     * parameters of ASL-Method (7).
     * Sometimes these parameters may mislead, because
     * may be redirected by the following more deeper
     * calls. We don't restore the previous values - it
     * would be too complicated.
     *
     * Apply it when the common Methods are used and
     * the initial Method which initialized the checking
     * is somewhere in another file and there is no remained
     * ArgX to pass that information.
     *
     * Apply it also when there are many entries with the
     * "index of checking" in the same file. It is more
     * convenient to arrange them inside the particular
     * Methods than to update all them inside the entire
     * file each time when it is needed to change any
     * or add some new.
     *
     * Note:
     * Due to the lack of ArgX the direct call to err()
     * doesn't allow to print the "Name of Method initiating
     * the checking". This is possible due to SET0 as well.
     *
     * Note:
     * Don't attempt to set up the zero "index of checking"
     * by this Method. It will be ignored and overwritten
     * by arg4 of err().
     *
     * Note:
     * Nevertheless, in any case, the err() provides
     * not exact address of error but only hints where
     * to seek the actual source Method of error.
     */
    Method (SET0, 3, NotSerialized)
    {
        If (ERR0)
        {
            ERR ("SET0", Z062, __LINE__, 0x00, 0x00, ERR0, 0x00)
        }
        Else
        {
            CopyObject (Arg0, ERR0) /* \ERR0 */
            CopyObject (Arg1, ERR1) /* \ERR1 */
            CopyObject (Arg2, ERR2) /* \ERR2 */
        }
    }

    /* Reset parameters of current checking */

    Method (RST0, 0, NotSerialized)
    {
        CopyObject (0x00, ERR0) /* \ERR0 */
        CopyObject (0x00, ERR1) /* \ERR1 */
        CopyObject (0x00, ERR2) /* \ERR2 */
        CopyObject (0x00, FNAM) /* \FNAM */
    }

    /* Reset current indicator of errors */

    Method (RST2, 0, NotSerialized)
    {
        ERR3 = 0x00
    }

    /* Get current indicator of errors */

    Method (GET2, 0, NotSerialized)
    {
        Return (ERR3) /* \ERR3 */
    }

    /* Collections of tests */

    Name (TCLA, 0x00)   /* compilation */
    Name (TCLF, 0x01)   /* functional */
    Name (TCLC, 0x02)   /* complex */
    Name (TCLE, 0x03)   /* exceptions */
    Name (TCLD, 0x04)   /* bug-demo (bdemo) */
    Name (TCLS, 0x05)   /* service */
    Name (TCLM, 0x06)   /* mt */
    Name (TCLT, 0x07)   /* Identity2MS */
    Name (TCLI, 0x08)   /* implementation dependent */
    Name (MAXC, 0x08)   /* equal to last maximal */
    /* Current index of tests collection */

    Name (TCLL, 0x00)
    /* Index of current test inside the collection */

    Name (TIND, 0x12345678)
    /* Name of test */

    Name (TSNM, "NAME_OF_TEST")
    /* Name of root method */

    Name (NRMT, "")
    /*
     * Flag, execution of root-method was skipped.
     *
     * It means that there where no conditions to run the test,
     * the test was not run and the reported status is 'skipped'.
     * The relevant assertion specified by the test is not to be
     * verified under the particular conditions at all.
     *
     * For example, the test can be run only in 64-bit mode, in
     * 32-bit mode the result of the test is undefined, so in
     * 32-bit mode, don't run it but only report the status of
     * test as skipped.
     */
    Name (FLG5, 0x00)
    /*
     * Flag, execution of root-method was blocked.
     *
     * It means that for some reason the test at present can not be run.
     * The tests was not run and the relevant assertion was not verified.
     * The test will be run when the conditions are changed. Up to that
     * moment, the status of such test is reported as 'blocked'.
     *
     * For example, some tests temporarily cause abort of testing,
     * thus preventing normal completion of all the tests of aslts
     * and generating the summary status of run of aslts.
     * To provide the normal conditions for other tests of aslts
     * we block the tests which prevent normal work
     * until the relevant causes are fixed in ACPICA.
     */
    Name (FLG6, 0x00)
    /*
     * Flag, compiler the test in the abbu layout
     */
    Name (ABUU, 0x00)
    /* Set global test filename */

    Method (SETF, 1, NotSerialized)
    {
        CopyObject (Arg0, FNAM) /* \FNAM */
    }

    /*
     * Test Header - Display common test header
     *
     * Arg0 - Name of test (RT25, etc)
     * Arg1 - Full Name of test ("Resource Descriptor Macro", etc.)
     * Arg2 - Test filename (via __FILE__ macro)
     */
    Method (THDR, 3, NotSerialized)
    {
        /* Save the test filename in the FNAM global */

        SETF (Arg2)
        /* Build output string and store to debug object */

        Concatenate ("TEST: ", Arg0, Local1)
        Concatenate (Local1, ", ", Local2)
        Concatenate (Local2, Arg1, Local3)
        Concatenate (Local3, " (", Local4)
        Concatenate (Local4, Arg2, Local5)
        Concatenate (Local5, ")", Local6)
        Debug = Local6
    }

    /* Report completion of root Method */

    Method (RPT0, 0, NotSerialized)
    {
        /* To get the same view in both 32-bit and 64-bit modes */

        Name (B000, Buffer (0x04){})
        If (SizeOf (NRMT))
        {
            /* Analyze previous run of root Method */

            Concatenate (":", TCN0 (TCLL), Local1)
            Concatenate (Local1, ":", Local0)
            Concatenate (Local0, TNIC (TCLL, TIND), Local1)
            Concatenate (Local1, ":", Local0)
            Concatenate (Local0, NRMT, Local1)
            Concatenate (Local1, ":", Local0)
            Local7 = (ERRS - ERR5) /* \ERR5 */
            If (FLG5)
            {
                Concatenate (Local0, "SKIPPED:", Local1)
            }
            ElseIf (FLG6)
            {
                Concatenate (Local0, "BLOCKED:", Local1)
            }
            ElseIf (Local7)
            {
                Concatenate (Local0, "FAIL:Errors # ", Local2)
                B000 = Local7
                Concatenate (Local2, B000, Local0)
                Concatenate (Local0, ":", Local1)
                ERR6++
            }
            Else
            {
                Concatenate (Local0, "PASS:", Local1)
            }

            Concatenate (":", CTST, Local0)
            Concatenate (Local0, Local1, Local2)
            Debug = Local2
            If ((RMRC < ETR0))
            {
                Concatenate (":", STST, Local2)
                Concatenate (Local2, Local1, Local0)
                RP0P [RMRC] = Local0
            }

            RMRC++
        }

        ERR5 = 0x00
        FLG5 = 0x00
        FLG6 = 0x00
    }

    /* Set the name of current root method */

    Method (SRMT, 1, NotSerialized)
    {
        /* Report completion of previous root Method */

        RPT0 ()
        /* Current number of errors */

        ERR5 = ERRS /* \ERRS */
        If (0x01)
        {
            Concatenate (Arg0, " test started", Debug)
        }

        CopyObject(Arg0, NRMT)
    }

    /*
     * Set 'skipped' status of execution of root method.
     * Used only to report that the root-method was not
     * run but skipped.
     */
    Method (SKIP, 0, NotSerialized)
    {
        FLG5 = 0x01
    }

    /*
     * Set 'blocked' status of execution of root method.
     * Used only to report that the root-method was not
     * run, it was blocked.
     */
    Method (BLCK, 0, NotSerialized)
    {
        FLG6 = 0x01
    }

    /*
     * Open sub-test
     *
     * arg0 - absolute index of file initiating the checking
     * arg1 - the name of Method initiating the checking
     */
    Method (BEG0, 2, NotSerialized)
    {
        SET0 (Arg0, Arg1, 0x00)
    }

    /* Close sub-test */

    Method (END0, 0, NotSerialized)
    {
        RST0 ()
    }

    /*
     * Current test start
     * arg0 - name of test
     * arg1 - index of tests collection
     * arg2 - index of test inside the collection
     * arg3 - run mode parameter of test
     */
    Method (STTT, 4, NotSerialized)
    {
        TSNM = Arg0
        TCLL = Arg1
        TIND = Arg2
        NRMT = ""
        FLG5 = 0x00
        FLG6 = 0x00
        ERR5 = 0x00
        /* Pack up ID of test case to use it in err() */

        ERRB = PK00 (Arg1, Arg2)
        /* Initial work for any test */

        Concatenate ("TEST (", TCN0 (TCLL), Local1)
        Concatenate (Local1, "), ", Local0)
        Concatenate (Local0, TSNM, Local1)
        If (RTPT)
        {
            /* Run Tests Parameters Technique (RTPT) */
            /* When running a group of tests (collections), full* */
            Local7 = 0x00
            If ((RUN0 == 0x00))
            {
                Local7 = 0x01
            }
            ElseIf ((RUN0 == 0x01))
            {
                If (Arg3)
                {
                    Local7 = 0x01
                }
            }
            ElseIf ((RUN0 == 0x02))
            {
                If ((Arg3 == 0x00))
                {
                    Local7 = 0x01
                }
            }
            ElseIf ((RUN0 == 0x03))
            {
                If ((Arg3 == RUN1))
                {
                    Local7 = 0x01
                }
            }
            ElseIf ((RUN0 == 0x04))
            {
                If ((Arg1 == RUN2))
                {
                    If ((Arg2 == RUN3))
                    {
                        Local7 = 0x01
                    }
                }
            }
        }
        Else
        {
            Local7 = 0x01
        }

        If (!Local7)
        {
            Concatenate (Local1, ", SKIPPED", Local0)
            Local1 = Local0
        }

        Debug = Local1
        Return (Local7)
    }

    /* Current test finish */

    Method (FTTT, 0, NotSerialized)
    {
        CH03 ("FTTT", 0x00, __LINE__, 0x00, 0x00)
        /* Report completion of previous root Method */

        RPT0 ()
        TSNM = "NAME_OF_TEST"
        TCLL = 0x00
        TIND = 0x12345678
        NRMT = ""
        FLG5 = 0x00
        FLG6 = 0x00
        ERR5 = 0x00
    }

    /*
     * Pack up ID of test case
     *
     * arg0 - index of tests collection
     * arg1 - index of test inside the collection
     */
    Method (PK00, 2, NotSerialized)
    {
        Local0 = (Arg0 & 0x0F)
        Local1 = (Arg1 & 0x1F)
        Local2 = (Local0 << 0x05)
        Local0 = (Local2 | Local1)
        Local7 = (Local0 << 0x17)
        Return (Local7)
    }

    /*
     * Pack up information of checking
     *
     * arg0 - absolute index of file initiating the checking
     * arg1 - index of checking (inside the file)
     */
    Method (PK01, 2, NotSerialized)
    {
        Local0 = (Arg0 & 0x07FF)
        Local1 = (Arg1 & 0x0FFF)
        Local2 = (Local0 << 0x0C)
        Local7 = (Local2 | Local1)
        Return (Local7)
    }

    /*
     * Pack up index of bug
     *
     * arg0 - index of bug
     */
    Method (PK02, 1, NotSerialized)
    {
        Local0 = (Arg0 & 0x01FF)
        Local7 = (Local0 << 0x17)
        Return (Local7)
    }

    /*
     * Pack up information of error
     *
     * arg0 - absolute index of file reporting the error
     * arg1 - index of error (inside the file)
     */
    Method (PK03, 2, NotSerialized)
    {
        Local0 = (Arg0 & 0x07FF)
        Local1 = (Arg1 & 0x0FFF)
        Local2 = (Local0 << 0x0C)
        Local7 = (Local2 | Local1)
        Return (Local7)
    }

    /*
     * Errors processing
     *
     * NOTE: looks we have exceeded some of the fields below
     *       but don't actually use them though pack them up.
     *
     * The layout of opcode of error (three 32-bit words)
     *
     * Word 0) 0xctfffeee (information of error)
     *
     * [31:28,4]   - c   0xf0000000
     * [27:23,5]   - t   0x0f800000
     * [22:12,11]  - fff 0x007ff000
     * [11:0,12]   - eee 0x00000fff
     *
     * Word 1) 0xmmzzzuuu (information of checking)
     *
     * [31:23,9]   - m   0xff800000
     * [22:12,11]  - zzz 0x007ff000
     * [11:0,12]   - uuu 0x00000fff
     *
     * Word 2) 0xnnnnnnnn (name of method)
     *
     *   c - index of tests collection
     *   t - index of test inside the collection
     *   f - absolute index of file reporting the error
     *   e - index of error (inside the file)
     *
     *   z - absolute index of file initiating the checking
     *   u - index of checking
     *   m - miscellaneous:
     *       1) in case of TCLD tests there is an index of bug
     *
     *   n - name of Method initiating the checking
     *
     * arg0 - diagnostic message (usually, the name of method conglomeration of tests)
     * arg1 - absolute index of file reporting the error
     * arg2 - line number of error (inside the file)
     * arg3 - absolute index of file initiating the checking
     * arg4 - line number of of checking (inside the file)
     * arg5 - first value (usually, received value)
     * arg6 - second value (usually, expected value)
     */
    Method (ERR, 7, NotSerialized)
    {
        Local3 = 0x00
        Local6 = 0x00
        If (ERR0)
        {
            /* ERR0 (Local4) - absolute index of file initiating the checking */
            /* ERR1 (Local3) - name of Method initiating the checking */
            /* ERR2 (Local5) - index of checking */
            Local4 = ERR0 /* \ERR0 */
            Local3 = ERR1 /* \ERR1 */
            /* Don't attempt to set up the zero "index of checking" */
            /* by SET0. It will be ignored and overwritten by arg4 */
            /* of err(). */
            If (ERR2)
            {
                Local5 = ERR2 /* \ERR2 */
            }
            Else
            {
                Local5 = Arg4
            }
        }
        Else
        {
            Local4 = 0x00
            Local5 = Arg4
            If ((TCLL == TCLD))
            {
                If (Local5)
                {
                    Local4 = ZFFF /* \ZFFF */
                }
            }
            Else
            {
                Local4 = Arg3
            }

            If ((ObjectType (Arg0) == C00A))
            {
                Local3 = Arg0
            }
        }

        If (Local4)
        {
            /* Pack up information of checking */

            Local6 = PK01 (Local4, Local5)
        }

        If ((TCLL == TCLD))
        {
            /* Pack up index of bug */

            Local0 = PK02 (TIND)
            Local6 |= Local0
        }

        /* Pack up information of error */

        Local0 = PK03 (Arg1, Arg2)
        /* Add ID of test case being executed */

        Local7 = (ERRB | Local0)
        Local1 = "---------- ERROR    : "
        Concatenate (Local1, Arg0, Local0)
        Debug = Local0
        ERP0 (Arg1, Arg2, Local4, Local3, Local5)
        If ((ObjectType (Arg5) == 0x01)) /* Check for Integer */
        {
            /* Format/print the Expected result value */

            ToHexString (Arg6, Local0)
            ToDecimalString (Arg6, Local1)
            Concatenate ("**** Expected Result: 0x", Local0, Local0)
            Concatenate (Local0, ", (", Local0)
            Concatenate (Local0, Local1, Local0)
            Concatenate (Local0, ")", Local0)
            Debug = Local0
            /* Format/print the Actual result value */

            ToHexString (Arg5, Local0)
            ToDecimalString (Arg5, Local1)
            Concatenate ("**** Actual Result  : 0x", Local0, Local0)
            Concatenate (Local0, ", (", Local0)
            Concatenate (Local0, Local1, Local0)
            Concatenate (Local0, ")", Local0)
            Debug = Local0
        }
        Else
        {
            Debug = "**** Actual Result:"
            Debug = Arg5
            Debug = "**** Expected Result:"
            Debug = Arg6
        }

        Debug = "---------- END\n"
        /* Pack the summary information about the first N errors */

        If ((ERRS < ETR1))
        {
            Local0 = (ERRS * 0x03)
            ERRP [Local0] = Local7 /* information of error */
            Local0++
            ERRP [Local0] = Local6 /* information of checking */
            Local0++
            ERRP [Local0] = Local3 /* name of method */
        }

        ERRS++
        /* Set current indicator of errors */

        ERR3 = 0x01
    }

    /*
     * Report parameters of error
     * arg0 - absolute index of file reporting the error
     * arg1 - index of error
     * arg2 - absolute index of file initiating the checking
     * arg3 - name of Method initiating the checking
     * arg4 - index of checking
     */
    Method (ERP0, 5, NotSerialized)
    {
        Concatenate ("TITLE               : ", TSNM, Local0)
        Debug = Local0
        Concatenate ("COLLECTION          : ", TCN0 (TCLL), Local0)
        Local1 = TNIC (TCLL, TIND)
        Debug = Local0
        Concatenate ("TEST CASE           : ", Local1, Local0)
        Debug = Local0
        Concatenate ("TEST                : ", NRMT, Local0)
        Debug = Local0
        /* Error */

        If ((FNAM != 0x00))
        {
            /* Use global filename, set via SETF */

            Local1 = FNAM /* \FNAM */
        }
        ElseIf ((Arg0 == ZFFF))
        {
            /* ATTENTION: don't use zFFF in tests other than TCLD */

            Local1 = SB00 (TIND, 0x00)
        }
        Else
        {
            Local1 = DerefOf (TFN0 [Arg0])
        }

        Concatenate ("ERROR,    File      : ", Local1, Local0)
        Debug = Local0
        Concatenate ("          Line      : ", ToDecimalString(Arg1), Local0)
        Debug = Local0
        /* Checking */

        If (Arg2)
        {
            If ((Arg2 == ZFFF))
            {
                /* ATTENTION: don't use zFFF in tests other than TCLD */

                Local1 = SB00 (TIND, 0x00)
            }
            Else
            {
                Local1 = DerefOf (TFN0 [Arg2])
            }

            Concatenate ("CHECKING, File      : ", Local1, Local0)
            Debug = Local0
            If ((ObjectType (Arg3) == C00A))
            {
                Concatenate ("             Method : ", Arg3, Local0)
                Debug = Local0
            }

            Concatenate ("             Line   : ", ToDecimalString(Arg4), Local0)
            Debug = Local0
        }
    }

    /*
     * Service for bug-demo.
     *
     * arg0 - index of bug
     * arg1 - type of work:
     *          0 - return the name of test corresponding to bug-demo
     *          1 - return the name of file ..
     */
    Method (SB00, 2, NotSerialized)
    {
        Local7 = "?"
        If ((Arg1 == 0x00))
        {
            ToDecimalString (Arg0, Local0)
            Concatenate ("*", Local0, Local1)
            Concatenate (Local1, ".asl", Local7)
        }
        ElseIf ((Arg1 == 0x01))
        {
            ToDecimalString (Arg0, Local0)
            Concatenate ("Demo of bug ", Local0, Local7)
        }

        Return (Local7)
    }

    /* Print out the whole contents, not only 32 bytes as debugger does */

    Method (PRN0, 1, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        LPN0 = SizeOf (Arg0)
        LPC0 = 0x00
        While (LPN0)
        {
            Local0 = DerefOf (Arg0 [LPC0])
            Debug = Local0
            LPN0--
            LPC0++
        }
    }

    /*
     * Check result of operation on equal to Zero
     * arg0 - message of error
     * arg1 - arg5 of err, "received value"
     * arg2 - arg6 of err, "expected value"
     * arg3 - value
     */
    Method (CH00, 4, NotSerialized)
    {
        If ((Arg3 != Zero))
        {
            ERR (Arg0, Z062, __LINE__, 0x00, 0x00, Arg1, Arg2)
        }
    }

    /*
     * Check result of operation on equal to Non-Zero (Ones)
     * arg0 - message of error
     * arg1 - arg5 of err, "received value"
     * arg2 - arg6 of err, "expected value"
     * arg3 - value
     */
    Method (CH01, 4, NotSerialized)
    {
        If ((Arg3 != Ones))
        {
            ERR (Arg0, Z062, __LINE__, 0x00, 0x00, Arg1, Arg2)
        }
    }

    /*
     * True, when the value is in range
     *
     * arg0 - Value
     * arg1 - RangeMin
     * arg2 - RangeMax
     */
    Method (RNG0, 3, NotSerialized)
    {
        If ((Arg1 > Arg2))
        {
            Debug = "RNG0: RangeMin greater than RangeMax"
            Fatal (0x00, 0x00000000, 0x00) /* Type, Code, Arg */
        }

        If ((Arg1 > Arg0))
        {
            Return (Zero)
        }
        ElseIf ((Arg0 > Arg2))
        {
            Return (Zero)
        }

        Return (Ones)
    }

    /* 200 symbols (without '\0') */

    Name (BIG0, "qwertyuiopasdfghjklzxcvbnm1234567890QWERTYUIOPASDFGHJKLZXCVBNMqwertyuiopasdfghjklzxcvbnm1234567890QWERTYUIOPASDFGHJKLZXCVBNMqwertyuiopasdfghjklzxcvbnm1234567890QWERTYUIOPASDFGHJKLZXCVBNMqwertyuiopasdf")
    /* All symbols */

    Name (ALL0, "`1234567890-=qwertyuiop[]\\asdfghjkl;\'zxcvbnm,./~!@#$%^&*()_+QWERTYUIOP{}|ASDFGHJKL:\"ZXCVBNM<>?")
    /* Check all the constants are not corrupted */

    Method (CST0, 0, NotSerialized)
    {
        If ((C000 != 0x0A))
        {
            ERR ("c000 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C001 != 0x05))
        {
            ERR ("c001 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C002 != 0x0D))
        {
            ERR ("c002 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C003 != 0x0C))
        {
            ERR ("c003 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C004 != 0x06))
        {
            ERR ("c004 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C005 != 0x04))
        {
            ERR ("c005 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C006 != 0x1F))
        {
            ERR ("c006 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C007 != 0x33))
        {
            ERR ("c007 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C008 != 0x00))
        {
            ERR ("c008 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C009 != 0x01))
        {
            ERR ("c009 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C00A != 0x02))
        {
            ERR ("c00a corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C00B != 0x03))
        {
            ERR ("c00b corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C00C != 0x04))
        {
            ERR ("c00c corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C00D != 0x05))
        {
            ERR ("c00d corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C00E != 0x06))
        {
            ERR ("c00e corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C00F != 0x07))
        {
            ERR ("c00f corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C010 != 0x08))
        {
            ERR ("c010 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C011 != 0x09))
        {
            ERR ("c011 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C012 != 0x0A))
        {
            ERR ("c012 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C013 != 0x0B))
        {
            ERR ("c013 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C014 != 0x0C))
        {
            ERR ("c014 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C015 != 0x0D))
        {
            ERR ("c015 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C016 != 0x0E))
        {
            ERR ("c016 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C017 != 0x0F))
        {
            ERR ("c017 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C018 != 0x10))
        {
            ERR ("c018 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If ((C019 != 0x11))
        {
            ERR ("c019 corrupted", Z062, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }
    }

    /*
     * Shift elements of buffer
     * <buf>,
     * <byte size of buf>,
     * <cmd: 0 - left, 1 - right>
     * <n shift: {1-7}>
     */
    Method (SFT0, 4, Serialized)
    {
        Name (N000, 0x00)
        Name (NCUR, 0x00)
        N000 = Arg1
        NCUR = 0x00
        Local6 = 0x00
        If (Arg2)
        {
            Local3 = Arg3
            Local5 = (0x08 - Local3)
        }
        Else
        {
            Local5 = Arg3
            Local3 = (0x08 - Local5)
        }

        Local0 = Arg1
        Local0++
        Name (B000, Buffer (Local0){})
        While (N000)
        {
            Local0 = DerefOf (Arg0 [NCUR])
            Local1 = (Local0 >> Local3)
            Local2 = (Local1 & 0xFF)
            Local1 = (Local2 | Local6)
            Local4 = (Local0 << Local5)
            Local6 = (Local4 & 0xFF)
            B000 [NCUR] = Local1
            N000--
            NCUR++
        }

        B000 [NCUR] = Local6
        /* Store(arg0, Debug) */
        /* Store(b000, Debug) */
        Return (B000) /* \SFT0.B000 */
    }

    /*
     * The entire byte size of buffer (starting with the
     * first byte of buffer, not field) affected by field.
     *
     * <index of bit>,
     * <num of bits>,
     */
    Method (MBS0, 2, NotSerialized)
    {
        Local0 = (Arg0 + Arg1)
        Local1 = (Local0 + 0x07)
        Divide (Local1, 0x08, Local2, Local0)
        Return (Local0)
    }

    /*
     * Bit-shift (0-7) elements of buffer
     *
     * <buf>,
     * <n shift: {0-7}>
     * <bit size of shift area>,
     * <source value of first byte>,
     * <source value of last byte>,
     */
    Method (SFT1, 5, Serialized)
    {
        Name (PREV, 0x00)
        Name (MS00, 0x00)
        Name (MS01, 0x00)
        Name (MS02, 0x00)
        Name (MS03, 0x00)
        Name (TAIL, 0x00)
        Name (LBT0, 0x00)
        /* Loop 0 */

        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        /* Byte size of result buffer */

        Name (NB01, 0x00)
        /* Reqular processed bytes number */

        Name (NREG, 0x00)
        /* Bit-size of low part of byte */

        Name (NB08, 0x00)
        /* Bit-size of high part of byte */

        Name (NB09, 0x00)
        /* Bit-size of last byte */

        Name (REST, 0x00)
        If ((Arg2 < 0x01))
        {
            ERR ("sft", Z062, __LINE__, 0x00, 0x00, Arg2, 0x01)
            Return (Ones)
        }

        If ((Arg1 > 0x07))
        {
            ERR ("sft", Z062, __LINE__, 0x00, 0x00, Arg1, 0x07)
            Return (Ones)
        }

        NB01 = MBS0 (Arg1, Arg2)
        Name (B000, Buffer (NB01){})
        /* Layout of regulsr bytes */

        NB08 = Arg1
        NB09 = (0x08 - NB08) /* \SFT1.NB08 */
        /* Produce masks of regulsr byte */

        Local0 = (0xFF >> NB08) /* \SFT1.NB08 */
        MS01 = (Local0 << NB08) /* \SFT1.NB08 */
        MS00 = ~MS01 /* \SFT1.MS01 */
        /* Last byte size */

        Local7 = (Arg1 + Arg2)
        REST = (Local7 % 0x08)
        If ((REST == 0x00))
        {
            REST = 0x08
        }

        /* Substitute field usually determined on previous step */

        PREV = (Arg3 & MS00) /* \SFT1.MS00 */
        /* Reqular processing repetition number */

        If ((Arg2 >= NB09))
        {
            NREG = 0x01
            Local7 = (Arg2 - NB09) /* \SFT1.NB09 */
            Divide (Local7, 0x08, Local1, Local0)
            NREG += Local0
        }

        /* Regular processing */

        LPN0 = NREG /* \SFT1.NREG */
        LPC0 = 0x00
        While (LPN0)
        {
            Local7 = DerefOf (Arg0 [LPC0])
            Local0 = (Local7 << NB08) /* \SFT1.NB08 */
            Local1 = (Local0 | PREV) /* \SFT1.PREV */
            B000 [LPC0] = Local1
            PREV = (Local7 >> NB09) /* \SFT1.NB09 */
            LPN0--
            LPC0++
        }

        If ((REST == 0x08))
        {
            TAIL = 0x00
        }
        ElseIf ((REST <= NB08))
        {
            TAIL = 0x01
        }
        Else
        {
            TAIL = 0x02
            LBT0 = DerefOf (Arg0 [LPC0])
        }

        /* =================== */
        /* Processing the tail */
        /* =================== */
        If ((TAIL == 0x01))
        {
            /* Produce masks */

            Local0 = (0xFF >> REST) /* \SFT1.REST */
            MS03 = (Local0 << REST) /* \SFT1.REST */
            MS02 = ~MS03 /* \SFT1.MS03 */
            Local0 = (PREV & MS02) /* \SFT1.MS02 */
            Local1 = (Arg4 & MS03) /* \SFT1.MS03 */
            Local2 = (Local0 | Local1)
            B000 [LPC0] = Local2
        }
        ElseIf ((TAIL == 0x02))
        {
            Local0 = (PREV & MS00) /* \SFT1.MS00 */
            Local1 = (LBT0 << NB08) /* \SFT1.NB08 */
            Local7 = (Local0 | Local1)
            /*
             * Byte layout:
             * 000011112222
             * rem sz  nb08
             * 33333333
             * nb09
             *     44444444
             *     rest
             */
            /* Produce masks of rem field */
            Local2 = (0xFF >> REST) /* \SFT1.REST */
            Local0 = (Local2 << REST) /* \SFT1.REST */
            Local1 = ~Local0
            /* Determine contents of field */

            Local2 = (Local7 & Local1)
            /* Remained of original last (first) byte */

            Local3 = (Arg4 & Local0)
            /* Result */

            Local0 = (Local2 | Local3)
            B000 [LPC0] = Local0
        }

        Return (B000) /* \SFT1.B000 */
    }

    /*
     * Verify result
     *
     * arg0 - name of test
     * arg1 - result
     * arg2 - expected value (64-bit mode)
     * arg3 - expected value (32-bit mode)
     * DISADVANTAGE: information about the actual place
     *               in errors reports is lost, should be
     *               resolved in the future.
     */
    Method (M4C0, 4, Serialized)
    {
        Name (TMP0, 0x00)
        Name (TMP1, 0x00)
        Local7 = 0x00
        TMP0 = ObjectType (Arg1)
        If (F64)
        {
            TMP1 = ObjectType (Arg2)
            If ((TMP0 != TMP1))
            {
                ERR (Arg0, Z062, __LINE__, 0x00, 0x00, TMP0, TMP1)
                Local7 = 0x01
            }
            ElseIf ((Arg1 != Arg2))
            {
                ERR (Arg0, Z062, __LINE__, 0x00, 0x00, Arg1, Arg2)
                Local7 = 0x01
            }
        }
        Else
        {
            TMP1 = ObjectType (Arg3)
            If ((TMP0 != TMP1))
            {
                ERR (Arg0, Z062, __LINE__, 0x00, 0x00, TMP0, TMP1)
                Local7 = 0x01
            }
            ElseIf ((Arg1 != Arg3))
            {
                ERR (Arg0, Z062, __LINE__, 0x00, 0x00, Arg1, Arg3)
                Local7 = 0x01
            }
        }

        Return (Local7)
    }

    /*
     * Return one-symbol string
     *
     * arg0 - source string contains desirable symbols
     * srg1 - index inside the source string
     */
    Method (M4A1, 2, Serialized)
    {
        Name (S000, " ")
        Local0 = DerefOf (Arg0 [Arg1])
        S000 [0x00] = Local0
        Return (S000) /* \M4A1.S000 */
    }

    /* Initialization */

    Method (STRT, 1, Serialized)
    {
        Method (M555, 0, NotSerialized)
        {
        }

        /* Data to determine 32/64 mode, global because of mt-tests */

        DataTableRegion (HDR, "DSDT", "", "")
        Field (HDR, AnyAcc, NoLock, Preserve)
        {
            SIG,    32,
            LENG,   32,
            REV,    8,
            SUM,    8,
            OID,    48,
            OTID,   64,
            OREV,   32,
            CID,    32,
            CREV,   32
        }

        /*
         * The first fictitious Method execution which statistics
         * is then used for to estimate all other Methods executions.
         */
        M555 ()
        TMT0 = Timer
        If ((REV < 0x02))
        {
            F64 = 0x00
            ISZ0 = 0x04
            ISZC = 0x08
            Debug = "32-bit mode"
        }
        Else
        {
            F64 = 0x01
            ISZ0 = 0x08
            ISZC = 0x10
            Debug = "64-bit mode"
        }

        /*
         * Check that the total number of exceptions is zero here.
         * The internal data about the exceptions initiated by some
         * bdemo tests on a global level should be reset by them to
         * this point as they didn't take place. Otherwise, an error
         * will be below registered.
         */
        If (CH02 ())
        {
            ERR7++
            /* Reset internal information about exceptions */

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            EXC0 = 0x00
            EXC1 = 0x00
        }

        SRTP (Arg0)
        RTPI ()
        RST0 ()
        RST2 ()
        /* Adjust some skippings of tests for different ACPICA releases */

        SET2 (SETN)
    }

    Name (TCNP, Package (0x09)
    {
        "compilation",
        "functional",
        "complex",
        "exceptions",
        "bdemo",
        "service",
        "mt",
        "Identity2MS",
        "IMPL"
    })
    /*
     * Test collection name
     * arg0 - index of test collection
     */
    Method (TCN0, 1, NotSerialized)
    {
        Local7 = "?"
        If ((Arg0 <= MAXC))
        {
            Local7 = DerefOf (TCNP [Arg0])
        }

        Return (Local7)
    }

    /*
     * Name of test inside collection
     * arg0 - index of test collection
     * arg1 - index of test inside the collection
     */
    Method (TNIC, 2, Serialized)
    {
        Local7 = "?"
        Switch (ToInteger (Arg0))
        {
            Case (0x01)
            {
                Local7 = DerefOf (TNF0 [Arg1])
            }
            Case (0x02)
            {
                Local7 = DerefOf (TNC0 [Arg1])
            }
            Case (0x03)
            {
                Local7 = DerefOf (TNE0 [Arg1])
            }
            Case (0x04)
            {
                Local7 = SB00 (Arg1, 0x01)
            }
            Case (0x05)
            {
                Local7 = DerefOf (TNS0 [Arg1])
            }
            Case (0x06)
            {
                Local7 = DerefOf (TNM0 [Arg1])
            }
            Case (0x07)
            {
                Local7 = DerefOf (TNT0 [Arg1])
            }
            Case (0x08)
            {
                Local7 = DerefOf (TNI0 [Arg1])
            }

        }

        Return (Local7)
    }

    /* Names of functional tests */

    Name (TNF0, Package (0x0F)
    {
        "arithmetic",
        "bfield",
        "constant",
        "control",
        "descriptor",
        "external",
        "local",
        "logic",
        "manipulation",
        "name",
        "reference",
        "region",
        "synchronization",
        "table",
        "module"
    })
    /* Names of complex tests */

    Name (TNC0, Package (0x14)
    {
        "misc",
        "provoke",
        "oarg",
        "oconst",
        "olocal",
        "oreturn",
        "onamedloc",
        "onamedglob",
        "opackageel",
        "oreftonamed",
        "oconversion",
        "oreftopackageel",
        "rstore",
        "roptional",
        "rconversion",
        "rcopyobject",
        "rindecrement",
        "rexplicitconv",
        "badasl",
        "namespace"
    })
    /* Names of exceptions tests */

    Name (TNE0, Package (0x07)
    {
        "exc",
        "exc_operand1",
        "exc_operand2",
        "exc_result1",
        "exc_result2",
        "exc_ref",
        "exc_tbl"
    })
    /* Names of service tests */

    Name (TNS0, Package (0x01)
    {
        "condbranches"
    })
    /* Names of mt tests */

    Name (TNM0, Package (0x01)
    {
        "mt-mutex"
    })
    /* Names of Identity2MS tests */

    Name (TNT0, Package (0x01)
    {
        "abbu"
    })
    /* Names of IMPL tests */

    Name (TNI0, Package (0x01)
    {
        "dynobj"
    })
    /* Names of test files */

    Name (TFN0, Package (0xCD)
    {
        "UNDEF",         /* 0 */
        "crbuffield.asl",
        "constants.asl",
        "ctl0.asl",
        "ctl1.asl",
        "ctl2.asl",
        "timing.asl",
        "concatenaterestemplate.asl",
        "dependentfn.asl",
        "dma.asl",
        "dwordio.asl",
        "dwordmemory.asl",
        "dwordspace.asl",
        "extendedio.asl",
        "extendedmemory.asl",
        "extendedspace.asl",
        "fixedio.asl",
        "interrupt.asl",
        "io.asl",
        "irq.asl",
        "irqnoflags.asl",
        "memory24.asl",
        "memory32.asl",
        "memory32fixed.asl",
        "qwordio.asl",
        "qwordmemory.asl",   /* 25 */
        "qwordspace.asl",
        "register.asl",
        "resourcetemplate.asl",
        "rtemplate.asl",
        "vendorlong.asl",
        "vendorshort.asl",
        "wordbusnumber.asl",
        "wordio.asl",
        "wordspace.asl",
        "logical.asl",
        "concatenate.asl",
        "eisaid.asl",
        "match1.asl",
        "mid.asl",
        "objecttype.asl",
        "sizeof.asl",
        "store.asl",
        "tobuffer.asl",
        "todecimalstring.asl",
        "tofrombcd.asl",
        "tohexstring.asl",
        "tointeger.asl",
        "tostring.asl",
        "touuid.asl",
        "unicode.asl",   /* 50 */
        "package.asl",
        "event.asl",
        "mutex.asl",
        "misc.asl",
        "provoke.asl",
        "oconversion.asl",
        "rconversion.asl",
        "exc.asl",
        "exc_operand1.asl",
        "exc_result.asl",
        "XXXXXX.asl",    /* 61 - RESERVED, not in use */
        "common.asl",
        "ehandle.asl",
        "oproc.asl",
        "otest.asl",
        "rproc.asl",
        "rtest.asl",
        "switch1.asl",
        "switch2.asl",
        "switch3.asl",
        "switch4.asl",
        "switch5.asl",
        "switch6.asl",
        "while.asl",
        "match2.asl",
        "ref00.asl",
        "ref01.asl",
        "ref02.asl",
        "ref03.asl",
        "ref04.asl",
        "ref70.asl",
        "operations.asl",
        "arithmetic.asl",
        "ocommon.asl",
        "oconst.asl",
        "onamedglob1.asl",
        "onamedglob2.asl",
        "onamedloc1.asl",
        "onamedloc2.asl",
        "opackageel.asl",
        "oreftonamed1.asl",
        "exc_00_undef.asl",
        "exc_01_int.asl",
        "exc_02_str.asl",
        "exc_03_buf.asl",
        "exc_04_pckg.asl",
        "exc_05_funit.asl",
        "exc_06_dev.asl",
        "exc_07_event.asl",
        "exc_08_method.asl",     /* 100 */
        "exc_09_mux.asl",
        "exc_10_oreg.asl",
        "exc_11_pwr.asl",
        "exc_12_proc.asl",
        "exc_13_tzone.asl",
        "exc_14_bfield.asl",
        "exc_operand2.asl",
        "ref05.asl",
        "ref71.asl",
        "ref06.asl",
        "ref50.asl",
        "name.asl",
        "data.asl",
        "dataproc.asl",
        "datastproc.asl",
        "ref07.asl",         /* 116 */
        "olocal.asl",
        "oreturn.asl",
        "oreftopackageel.asl",
        "oreftonamed2.asl",  /* 120 */
        "oarg.asl",
        "rcommon.asl",
        "rstore.asl",
        "rcopyobject.asl",
        "rindecrement.asl",
        "rexplicitconv.asl",
        "roptional.asl",
        "tcicmd.asl",
        "dobexec.asl",
        "dobdecl.asl",   /* 130 */
        "dobctl.asl",
        "dobexceptions.asl",
        "method.asl",
        "function.asl",
        "condbranches.asl",
        "add.asl",
        "standaloneRet.asl",
        "store.asl",
        "return.asl",
        "dobmisc.asl",   /* 140 */
        "opregions.asl",
        "dtregions.asl",
        "regionfield.asl",
        "indexfield.asl",
        "bankfield.asl",
        "badasl.asl",
        "mt-common.asl",
        "mt-mutex.asl",
        "mt-mxs.asl",
        "mutex2.asl",    /* 150 */
        "mutex_proc.asl",
        "mt-tests.asl",
        "mt-service.asl",
        "ns0.asl",
        "ns1.asl",
        "ns2.asl",
        "ns3.asl",
        "ns4.asl",
        "ns5.asl",
        "ns6.asl",           /* 160 */
        "I2MS_msfail0.asl",
        "I2MS_st0.asl",
        "I2MS_ns_in00.asl",
        "I2MS_ns_in10.asl",
        "I2MS_ns_in20.asl",
        "I2MS_ns_in30.asl",
        "I2MS_ns_in40.asl",
        "I2MS_ns_in50.asl",
        "I2MS_mt0_abbu.asl",
        "I2MS_mt0_aslts.asl",    /* 170 */
        "I2MS_recursion_abbu.asl",
        "I2MS_recursion_aslts.asl",
        "serialized.asl",
        "load.asl",          /* 174 */
        "unload.asl",
        "loadtable.asl",
        "recursion.asl",
        "ns-scope.asl",      /* 178 */
        "ns-fullpath.asl",
        "scope.asl",     /* 180 */
        "object.asl",
        "order.asl",
        /* below are incorrect yet: */

        "I2MS_ns_dv00.asl",
        "I2MS_ns_dv10.asl",
        "I2MS_ns_dv20.asl",
        "I2MS_ns_dv30.asl",
        "I2MS_ns_device.asl",
        "I2MS_ns_device_abbu.asl",
        "I2MS_ns_device_aslts.asl",
        /* see these files can be not used at all: */

        "I2MS_ns4.asl",  /* 190 */
        "I2MS_ns5.asl",
        "I2MS_ns6.asl",
        /* ACPI 5.0 */

        "fixeddma.asl",
        "gpioint.asl",
        "gpioio.asl",
        "i2cserialbus.asl",
        "spiserialbus.asl",
        "uartserialbus.asl",
        /* ACPI 6.2 */

        "pinfunction.asl",
        "pinconfig.asl",     /* 200 */
        "pingroup.asl",
        "pingroupfunction.asl",
        "pingroupconfig.asl",
        /* External Op tests */

        "external.asl"  /* 204 */
    })
    /*
     * Unpack error
     *
     * arg0 - information of error (Word 0)
     * arg1 - information of checking (Word 1)
     * arg2 - name of Method initiating the checking (Word 2)
     */
    Method (UNP0, 3, Serialized)
    {
        /* c - index of tests collection */

        Local7 = (Arg0 >> 0x1C)
        Local0 = (Local7 & 0x0F)
        /* t - index of test inside the collection */

        Local7 = (Arg0 >> 0x17)
        Local1 = (Local7 & 0x1F)
        /* f - absolute index of file reporting the error */

        Local7 = (Arg0 >> 0x0C)
        Local2 = (Local7 & 0x07FF)
        /* e - index of error (inside the file) */

        Local3 = (Arg0 & 0x0FFF)
        Local6 = ""
        Local7 = ""
        Switch (ToInteger (Local0))
        {
            Case (0x01)
            {
                Local6 = DerefOf (TNF0 [Local1])
                If (ERR4)
                {
                    Local7 = ", functional, "
                }
            }
            Case (0x02)
            {
                Local6 = DerefOf (TNC0 [Local1])
                If (ERR4)
                {
                    Local7 = ", complex, "
                }
            }
            Case (0x03)
            {
                Local6 = DerefOf (TNE0 [Local1])
                If (ERR4)
                {
                    Local7 = ", exceptions, "
                }
            }
            Case (0x04)
            {
                /* m - in case of TCLD tests there is an index of bug */

                Local0 = (Arg1 >> 0x17)
                Local1 = (Local0 & 0x01FF)
                Local6 = SB00 (Local1, 0x01)
                If (ERR4)
                {
                    Local7 = ", bug-demo, "
                }
            }
            Case (0x05)
            {
                Local6 = DerefOf (TNS0 [Local1])
                If (ERR4)
                {
                    Local7 = ", service, "
                }
            }
            Case (0x06)
            {
                Local6 = DerefOf (TNM0 [Local1])
                If (ERR4)
                {
                    Local7 = ", mt, "
                }
            }
            Case (0x07)
            {
                Local6 = DerefOf (TNT0 [Local1])
                If (ERR4)
                {
                    Local7 = ", Identity2MS, "
                }
            }
            Case (0x08)
            {
                Local6 = DerefOf (TNI0 [Local1])
                If (ERR4)
                {
                    Local7 = ", IMPL, "
                }
            }

        }

        Concatenate (Local7, Local6, Local5)
        Concatenate (Local5, ", ", Local1)
        /* Error */

        If ((Local2 == ZFFF))
        {
            /* ATTENTION: don't use zFFF in tests other than TCLD */
            /* m - in case of TCLD tests there is an index of bug */
            Local0 = (Arg1 >> 0x17)
            Local2 = (Local0 & 0x01FF)
            Local6 = SB00 (Local2, 0x00)
        }
        Else
        {
            Local6 = DerefOf (TFN0 [Local2])
        }

        Concatenate (Local1, Local6, Local7)
        Concatenate (Local7, ", ", Local1)
        Concatenate (Local1, Local3, Local7)
        /* (z+u) - entire field of checking */

        Local5 = (Arg1 & 0x007FFFFF)
        If (Local5)
        {
            /* z - absolute index of file initiating the checking */

            Local5 = (Arg1 >> 0x0C)
            Local2 = (Local5 & 0x07FF)
            /* u - index of checking */

            Local3 = (Arg1 & 0x0FFF)
            If ((Local2 == ZFFF))
            {
                /* ATTENTION: don't use zFFF in tests other than TCLD */
                /* m - in case of TCLD tests there is an index of bug */
                Local0 = (Arg1 >> 0x17)
                Local2 = (Local0 & 0x01FF)
                Local6 = SB00 (Local2, 0x00)
            }
            Else
            {
                Local6 = DerefOf (TFN0 [Local2])
            }

            Concatenate (Local7, ", ", Local1)
            Concatenate (Local1, Local6, Local5)
            Concatenate (Local5, ", ", Local1)
            Concatenate (Local1, Local3, Local7)
            If ((ObjectType (Arg2) == C00A))
            {
                Concatenate (Local7, ", ", Local1)
                Concatenate (Local1, Arg2, Local7)
            }
        }

        Return (Local7)
    }

    /* Report errors */

    Method (RERR, 0, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        LPN0 = ETR1 /* \ETR1 */
        If ((ERRS < LPN0))
        {
            LPN0 = ERRS /* \ERRS */
        }

        Local0 = 0x00
        Debug = "========= ERRORS SUMMARY (max 400):"
        While (LPN0)
        {
            Local7 = DerefOf (ERRP [Local0])
            Local0++
            Local6 = DerefOf (ERRP [Local0])
            Local0++
            Local4 = DerefOf (ERRP [Local0])
            Local0++
            Local1 = UNP0 (Local7, Local6, Local4)
            If (ERR4)
            {
                Concatenate ("", Local7, Local2)
                Concatenate (Local2, ", ", Local5)
                Concatenate (Local5, Local6, Local2)
                Concatenate (Local2, Local1, Local7)
            }
            Else
            {
                Concatenate ("", Local1, Local7)
            }

            Debug = Local7
            LPN0--
            LPC0++
        }

        If ((ERRS > ETR1))
        {
            Debug = "********* Not all errors were traced, maximum exceeded!"
        }

        Debug = "========= END."
    }

    /* Report root Methods run results */

    Method (RRM0, 0, Serialized, 3)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        LPN0 = ETR0 /* \ETR0 */
        If ((RMRC < LPN0))
        {
            LPN0 = RMRC /* \RMRC */
        }

        Debug = "========= ROOT METHODS SUMMARY (max 600):"
        While (LPN0)
        {
            Local7 = DerefOf (RP0P [LPC0])
            Debug = Local7
            LPN0--
            LPC0++
        }

        If ((RMRC > ETR0))
        {
            Debug = "********* Not all root Methods were traced, maximum exceeded!"
        }

        Debug = "========= END."
    }

    /* Final actions */

    Method (FNSH, 0, NotSerialized)
    {
        /* Check, the current number of exceptions is zero */

        CH03 ("FNSH", 0x00, __LINE__, 0x00, 0x00)
        /* Check all the constants are not corrupted */

        CST0 ()
        /* Run time */

        Local7 = Timer
        Local6 = (Local7 - TMT0) /* \TMT0 */
        Divide (Local6, 0x0A, Local1, Local2)
        Divide (Local2, 0x000F4240, Local1, Local0)
        Debug = Concatenate ("Run time (in seconds): 0x", Local0)
        /* Exceptions total */

        Debug = Concatenate ("The total number of exceptions handled: 0x", EXC1)
        /* Status of test run */

        If (ERRS)
        {
            RERR ()
        }

        /* Report root Methods run results */

        RRM0 ()
        If (F64)
        {
            Concatenate ("TEST ACPICA: ", "64-bit :", Local0)
        }
        Else
        {
            Concatenate ("TEST ACPICA: ", "32-bit :", Local0)
        }

        If (ERR7)
        {
            Concatenate ("!!!! ERRORS were detected during the loading stage, # 0x", ERR7, Debug)
        }

        EXC1 = 0x00
        If ((ERRS || ERR7))
        {
            Concatenate (Local0, " FAIL : Errors # 0x", Local1)
            Concatenate (Local1, ERRS, Local2)
            Concatenate (Local2, ", Failed tests # 0x", Local1)
            Debug = Concatenate (Local1, ERR6)
            Return (0x01)
        }

        Debug = Concatenate (Local0, " PASS")
        Return (0x00)
    }

    /* Trace execution */
    /*
     * Report write operation
     * arg0 - object where writing
     * arg1 - index where writing
     * arg2 - value
     */
    Method (TRC0, 3, NotSerialized)
    {
        If (TRCF)
        {
            Concatenate (TRCH, ", WRITE: where ", Local0)
            Concatenate (Local0, Arg1, Local1)
            Concatenate (Local1, ", ", Local0)
            Concatenate (Local0, Arg2, Local1)
            Debug = Local1
        }
    }

    /*
     * Report read operation
     * arg0 - object from where reading
     * arg1 - index from where reading
     * arg2 - obtained value
     */
    Method (TRC1, 3, NotSerialized)
    {
        If (TRCF)
        {
            Concatenate (TRCH, ", READ: where ", Local0)
            Concatenate (Local0, Arg1, Local1)
            Concatenate (Local1, ", ", Local0)
            Concatenate (Local0, Arg2, Local1)
            Debug = Local1
        }
    }

    /*
     * Report string
     * arg0 - string
     */
    Method (TRC2, 1, NotSerialized)
    {
        If (TRCF)
        {
            Concatenate (TRCH, ", ", Local0)
            Concatenate (Local0, Arg0, Local1)
            Debug = Local1
        }
    }

    /* Switch on trace */

    Method (TRC8, 0, NotSerialized)
    {
        TRCF = 0x01
    }

    /* Switch off trace */

    Method (TRC9, 0, NotSerialized)
    {
        TRCF = 0x00
    }

    /* Start of test */

    Method (TS00, 1, NotSerialized)
    {
        If (PR01)
        {
            Concatenate ("Test ", Arg0, Local0)
            Concatenate (Local0, " started", Local1)
            Debug = Local1
        }
    }

    /*
     * Convert the Timer units (one unit - 100 nsecs) to Seconds
     * arg0 - interval in Timer units
     */
    Method (TMR0, 1, NotSerialized)
    {
        /* Convert to microseconds */

        Divide (Arg0, 0x0A, Local0, Local1)
        /* Convert to seconds */

        Divide (Local1, 0x000F4240, Local0, Local2)
        Return (Local2)
    }
