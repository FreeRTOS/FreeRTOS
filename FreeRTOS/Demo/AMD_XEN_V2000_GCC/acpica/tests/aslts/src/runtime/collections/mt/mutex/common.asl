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
     * SEE:
     * ??????????? Multi-threading common definitions
     * see: see structure and the name of this file also later !!!!!!!!!!!!!!
     * ??????????????????????????????????????????????????????????????????????
     *
     *
     * NOTIONS and NOTATIONS:
     *
     * ID and Index of thread:
     *
     *   each thread is identified by its ID (delivered from the underlying system)
     *   and its calculated unique index between all the threads participating in
     *   the test.
     *
     * Control Thread - the thread with index equal to 0
     * Worker Threads  - all other threads with the non-zero index
     *
     * Number of threads (total) -
     *    the value passed to AcpiExec Threads command
     *    as a number of threads parameter.
     *
     * Number of threads actually in work -
     *    number of threads actually participating the relevant test.
     *    Note: this value includes the Control Thread too.
     */
    Name (Z147, 0x93)
    /*
     * Common data of threads
     *
     * Usage:
     *
     *   command line: Threads 6 1 MAIN
     *     6 - number of threads, it can be greater or less than 6
     *
     *   redm      - set it to zero to reduce the run time
     *   vb00-vb06 - use them to suppress the output
     *
     *   FLG1      - the _TCI-based Initialization of multithreading interconnection
     *               (run command TCI_CMD_GET_ID_OF_THREADS to determine indexes of threads)
     */
    /*
     * Flags
     */
    Name (CTL0, 0x00) /* the Control thread is ready */
    Name (REDM, 0x01) /* run tests in reduced mode */
    Name (GLDI, 0x00) /* global data initialized */
    /*
     * Simple switch of the verbal mode
     *
     * 0 - silent
     * otherwise - allow
     *
     * s-flags (defaults are given in comment (0/1))
     */
    Name (VB00, 0x00) /* (0) common messages */
    Name (VB02, 0x01) /* (1) trace Control thread */
    Name (VB03, 0x00) /* (0) trace Worker threads */
    Name (VB04, 0x01) /* (1) report statistics */
    Name (VB05, 0x00) /* (0) report warnings by worker-threads */
    Name (VB06, 0x01) /* (1) report errors by worker-threads */
    /*
     * Multi-conditional switches of the verbal mode
     *
     * 0 - silent
     * 1 - allow only for Control Thread to report
     * 2 - allow only for Worker Threads to report
     * 3 - allow for all threads to report
     *
     * mc-flags
     */
    Name (VB01, 0x01) /* header of test */
    /* Sleep mode */

    Name (SL00, 0x32) /* Default milliseconds to sleep for Control thread */
    Name (SL01, 0x32) /* Default milliseconds to sleep for Worker threads */
    /*
     * Default milliseconds to sleep for Control thread
     * before to check hang status of worker threads on
     * operations.
     */
    Name (SL02, 0x01F4)
    /* How many times maximum to repeat sl02 sleeping */

    Name (SL03, 0x01)
    Name (SLM0, 0x00)   /* Sleeping mode for worker threads */
    /* Milliseconds to sleep for non-zero slm0 */

    Name (I100, 0x32)
    Name (I101, 0x64)
    Name (I102, 0xC8)
    Name (I103, 0x0190)
    Name (I104, 0x01F4)
    Name (I105, 0x4B)
    Name (I106, 0x96)
    Name (I107, 0xFA)
    Name (I108, 0x012C)
    /* Commands for workers */

    Name (C100, 0xF0) /* Idle thread */
    Name (C101, 0xF1) /* Exit the infinite loop */
    Name (C102, 0xF2) /* Sleep for the specified number of Milliseconds */
    Name (C103, 0xF3) /* Acquire/Sleep/Release */
    Name (C104, 0xF4) /* <Acquire/Sleep>(0-15 levels)/Release(15-0 levels) */
    Name (C105, 0xF5) /* Example 0 */
    Name (C106, 0xF6) /* Acquire specified set of mutexes */
    Name (C107, 0xF7) /* Release specified set of mutexes */
    Name (C108, 0xF8) /* Terminate thread */
    Name (C109, 0xF9) /* Invoke Serialized method */
    Name (C10A, 0xFA) /* Invoke non-Serialized method, use Mutex for exclusive access to critical section */
    Name (C10B, 0xFB) /* Non-serialized method is grabbed simultaneously */
    /* Responds of worker threads (not intersect with 'Commands for workers') */

    Name (RS00, 0x97) /* "I see zero do00" */
    /* Common use strategies provided by the Control thread */

    Name (CM01, 0x01) /* all workers to exit the infinite loop */
    Name (CM02, 0x02) /* all workers to sleep for the specified period */
    /*
     * This buffer is to be filled by the control thread.
     * It is filed with the commands to be fulfilled by the
     * worker threads.
     *
     * The thread of i-th index takes the command from the
     * i-th element of Buffer.
     *
     * It is read-only for worker threads.
     */
    Name (BS00, Buffer (0x01)
    {
         0x00                                             // .
    })
    /*
     * This buffer is zeroed by the control thread and then to be
     * filled by the worker threads with the commands they have been
     * fulfilled.
     */
    Name (BS01, Buffer (0x01)
    {
         0x00                                             // .
    })
    /*
     * This buffer is zeroed by the control thread and then to be
     * filled by the worker threads when they see that do00 is zero.
     *
     * The control thread uses it to check that all the worker threads
     * saw zero do00 (are idle) before to start the next command.
     */
    Name (BS02, Buffer (0x01)
    {
         0x00                                             // .
    })
    /*
     * This buffer is zeroed by the control thread and then to
     * be filled by the idle worker threads.
     */
    Name (BS03, Buffer (0x01)
    {
         0x00                                             // .
    })
    /*
     * This buffer is zeroed by the control thread and then to be
     * set up by the worker threads when they complete.
     */
    Name (BS04, Buffer (0x01)
    {
         0x00                                             // .
    })
    /*
     * p10X - statistics
     */
    /*
     * These package are zeroed by the control thread,
     * the worker threads accumulate there:
     * - errors
     * - number of errors
     * - warnings
     * - number of warnings
     */
    Name (P100, Package (0x01)
    {
        0x00
    }) /* scale of errors */
    Name (P101, Package (0x01)
    {
        0x00
    }) /* number of errors */
    Name (P102, Package (0x01)
    {
        0x00
    }) /* scale of warnings */
    Name (P103, Package (0x01)
    {
        0x00
    }) /* number of warnings */
    /* Command statistics */

    Name (P104, Package (0x01)
    {
        0x00
    }) /* number of Sleep */
    Name (P105, Package (0x01)
    {
        0x00
    }) /* number of Acquire */
    Name (P106, Package (0x01)
    {
        0x00
    }) /* number of Release */
    /*
     * To be filled by the control thread,
     * non-zero enables to fulfill the commands specified by bs00.
     */
    Name (DO00, 0x00)
    /* Opcodes of errors reported by worker threads */

    Name (ER00, 0x01) /* Acquire failed */
    Name (ER01, 0x02) /* Flag of mutex is already non-zero (set up by some thread(s)) */
    Name (ER02, 0x04) /* Invalid flag of mutex (changed by other thread while this one owned that mutex) */
    Name (ER03, 0x08) /* Unexpected exception */
    Name (ER04, 0x10) /* Improper exception (no exception, or unexpected opcode, or more than one exception) */
    Name (ER05, 0x20) /* Invalid command */
    Name (ER06, 0x40) /* Invalid Index of current thread */
    Name (ER07, 0x80) /* Too big Index of current thread */
    Name (ER08, 0x0100) /* Invalid counter of mutex owning */
    Name (ER09, 0x0200) /* Acquire returned zero but FAIL expected */
    Name (ER10, 0x0400) /* Serialized method doesn't provide exclusive call */
    Name (ER11, 0x0800) /* Serialized method doesn't provide exclusive call */
    Name (ER12, 0x1000) /* Non-serialized method thr-1 didn't get into method */
    Name (ER13, 0x2000) /* Non-serialized method thr-N didn't get into method */
    /* Opcodes of warnings reported by worker threads */

    Name (WN00, 0x01) /* Acquire repeatedly the same mutex by thread which already owns it */
    /*
     * These packages are to be filled by the control thread.
     * They are filed with the arguments of commands specified
     * for the worker threads.
     *
     * The thread of i-th index takes the arguments from the
     * i-th elements of Packages.
     *
     * These are read-only for worker threads.
     *
     * For Acquire/Release:
     *
     * p200 - starting level of mutex
     * p201 - number of Levels of mutexes
     * p202 - starting index of mutex (on the specified level)
     * p203 - number of mutexes of the same level
     * p204 - exceptional conditions
     * p205 - opcode of TimeOutValue (see comment to ma00)
     */
    Name (P200, Package (0x01)
    {
        0x00
    })
    Name (P201, Package (0x01)
    {
        0x00
    })
    Name (P202, Package (0x01)
    {
        0x00
    })
    Name (P203, Package (0x01)
    {
        0x00
    })
    Name (P204, Package (0x01)
    {
        0x00
    })
    Name (P205, Package (0x01)
    {
        0x00
    })
    /* Exceptions total number */

    Name (EX10, 0x00)
    /*
     * p30X - Current state
     */
    Name (P300, Package (0x01)
    {
        0x00
    }) /* scale of errors */
    Name (P301, Package (0x01)
    {
        0x00
    }) /* scale of warnings */
    /*
     * Non-zero means to check absence of exception
     * before and after each operation additionally
     * to the checking (if any) specified per-operation.
     */
    Name (FLG0, 0x00)
    /*
     * Handle exceptions
     *
     * Exceptional condition flag:
     *
     * EX0D      - FAIL expected
     * EX0E      - check for "no exception"
     * otherwise - opcode of exception expected
     */
    /*
     * The _TCI-based Initialization of multithreading interconnection
     * (run command TCI_CMD_GET_ID_OF_THREADS to determine indexes of threads).
     *
     * Note: now when arguments (arg0, arg1, arg2) are determined
     *       by Threads command of AcpiExec and passed to test, it
     *       is unnecessary to do "The _TCI-based Initialization of
     *       multithreading interconnection" below. Used temporary.
     */
    Name (FLG1, 0x00)
    /*
     * Variables used by particular tests
     *
     * FLG2,
     * FLG3
     *   1) To show that Serialized method is grabbed exclusively
     *   2) To show that non-Serialized method is grabbed by two threads simultaneously
     */
    Name (FLG2, 0x00)
    Name (FLG3, 0x00)
    /*
     * The Control Thread manages and controls the specified testing strategy
     * to be fulfilled by the Worker Threads.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread (0, can be used for control only)
     * arg2 - Index of current thread
     * arg3 - cammand - index of the test strategy to be
     *        managed and controlled by the Control Thread
     *        and fulfilled by the Worker Threads (Workers).
     *
     * Arguments of the command arg3:
     *
     * arg4
     * arg5
     * arg6
     */
    Method (M100, 7, Serialized)
    {
        /* Prohibits activity of all the worker threads */

        Switch (Arg3)
        {
            Case (0x01)
            {
                /* CM01: All workers to exit the infinite loop */

                M10C (Arg0)
            }
            Case (0x02)
            {
                /* CM02: All workers to sleep for the specified period */

                M10D (Arg0)
            }

        }
    }

    /*
     * Open testing - init interaction data
     *
     * arg0 - number of threads
     */
    Method (M102, 1, Serialized)
    {
        Name (B000, Buffer (Arg0){})
        Name (P000, Package (Arg0){})
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        DO00 = 0x00
        CopyObject (B000, BS00) /* \BS00 */
        CopyObject (B000, BS01) /* \BS01 */
        CopyObject (B000, BS02) /* \BS02 */
        CopyObject (B000, BS03) /* \BS03 */
        CopyObject (P000, P200) /* \P200 */
        CopyObject (P000, P201) /* \P201 */
        CopyObject (P000, P202) /* \P202 */
        CopyObject (P000, P203) /* \P203 */
        CopyObject (P000, P204) /* \P204 */
        CopyObject (P000, P205) /* \P205 */
        CopyObject (P000, P300) /* \P300 */
        CopyObject (P000, P301) /* \P301 */
        LPN0 = Arg0
        LPC0 = 0x00
        While (LPN0)
        {
            P300 [LPC0] = 0x00
            P301 [LPC0] = 0x00
            LPN0--
            LPC0++
        }

        /*
         * Initialization to be done once
         */
        If (!GLDI)
        {
            /* Statistics */

            CopyObject (P000, P100) /* \P100 */
            CopyObject (P000, P101) /* \P101 */
            CopyObject (P000, P102) /* \P102 */
            CopyObject (P000, P103) /* \P103 */
            CopyObject (P000, P104) /* \P104 */
            CopyObject (P000, P105) /* \P105 */
            CopyObject (P000, P106) /* \P106 */
            CopyObject (B000, BS04) /* \BS04 */
            LPN0 = Arg0
            LPC0 = 0x00
            While (LPN0)
            {
                P100 [LPC0] = 0x00
                P101 [LPC0] = 0x00
                P102 [LPC0] = 0x00
                P103 [LPC0] = 0x00
                P104 [LPC0] = 0x00
                P105 [LPC0] = 0x00
                P106 [LPC0] = 0x00
                LPN0--
                LPC0++
            }
        }

        /* Init fl01 */

        M339 ()
        /*
         * Reset all counters (cnt0) and flags (fl00)
         * corresponding to all Mutexes.
         */
        M330 ()
        /* Report that the Control thread is ready */

        CTL0 = 0x01
        GLDI = 0x01
    }

    /*
     * Control thread waits for all the worker threads to
     * fulfill the specified for them buffer of commands.
     *
     * arg0 - number of threads
     */
    Method (M103, 1, Serialized)
    {
        /* Wait for all Worker threads and check their statuses */

        Name (B000, Buffer (Arg0){})
        Name (B001, Buffer (Arg0){})
        Name (B002, Buffer (Arg0){})
        CopyObject (BS00, B000) /* \M103.B000 */
        M110 (Arg0, B000, B001, B002)
    }

    /*
     * The _TCI-based initialization of multithreading interconnection
     *
     * In result each thread knows its ID and calculated its index
     * between all threads participating in the test.
     *
     * arg0 - number of threads
     *
     * Return:
     *   success   - II-Package
     *   otherwise - 0
     */
    Method (M104, 1, NotSerialized)
    {
        /*
         * Local0 - array of thread IDs
         * Local1 - auxiliary
         * Local2 - auxiliary
         * Local7 - II-Package
         */
        If (VB00)
        {
            Debug = "Checking for the Test Command Interface with the ACPICA (_TCI) support"
        }

        If (!M3A5 ())
        {
            Debug = "The Test Command Interface with the ACPICA (_TCI) is not supported"
            Return (0x00)
        }

        If (VB00)
        {
            Debug = "Getting array of thread IDs"
        }

        Local0 = M163 (Arg0)
        Local1 = ObjectType (Local0)
        If ((Local1 != C00C))
        {
            Debug = "Failed to get array of thread indexes"
            Return (0x00)
        }

        If (VB00)
        {
            Debug = "Calculating index of thread"
        }

        Local7 = M105 (Local0, Arg0)
        Local2 = ObjectType (Local7)
        If ((Local2 != C00C))
        {
            Debug = "Invalid contents of Package of threads"
            Return (0x00)
        }

        Return (Local7)
    }

    /*
     * Calculate and return II-Package with Index of current thread between
     * all threads participating in the test and ID of that thread.
     *
     * arg0 - the Package of thread IDs returned by m163 which
     *        executes the command TCI_CMD_GET_ID_OF_THREADS.
     * arg1 - number of threads
     *
     * Return:
     * II-Package in success:
     *	0-th element - ID of that current thread
     *	1-th element - Index of current thread between all threads participating in test
     * Integer otherwise:
     *    0
     */
    Method (M105, 2, NotSerialized)
    {
        /*
         * Local0 - auxiliary
         * Local1 - auxiliary
         * Local2 - lpN0
         * Local3 - lpC0
         * Local4 - TCI_PACKAGE_THR_NUM
         * Local5 - TCI_PACKAGE_THR_NUM_REAL
         * Local6 - TCI_PACKAGE_THR_ID (ID of thread)
         * Local7 - Index of thread
         */
        Local7 = FF32 /* \FF32 */
        /* Store(arg0, Debug) */

        Local4 = DerefOf (Arg0 [C22C]) /* TCI_PACKAGE_THR_NUM */
        If (!Local4)
        {
            Debug = "TCI_PACKAGE_THR_NUM is zero"
            Return (0x00)
        }

        Local5 = DerefOf (Arg0 [C22D]) /* TCI_PACKAGE_THR_NUM_REAL */
        If (!Local5)
        {
            Debug = "TCI_PACKAGE_THR_NUM_REAL is zero"
            Return (0x00)
        }

        Local6 = DerefOf (Arg0 [C22E]) /* TCI_PACKAGE_THR_ID */
        If (!Local6)
        {
            Debug = "TCI_PACKAGE_THR_ID is zero"
            Return (0x00)
        }

        If ((Local4 != Local5))
        {
            Debug = "TCI_PACKAGE_THR_NUM != TCI_PACKAGE_THR_NUM_REAL"
            Debug = Local4
            Debug = Local5
            Return (0x00)
        }

        If ((Local4 != Arg1))
        {
            Debug = "TCI_PACKAGE_THR_NUM != Number of threads"
            Debug = Local4
            Debug = Arg1
            Return (0x00)
        }

        /* Calculate index of thread */

        Local2 = Arg1
        Local3 = 0x00
        Local0 = C22F /* \C22F */
        While (Local2)
        {
            Local1 = DerefOf (Arg0 [Local0])
            If (!Local1)
            {
                Debug = "thread ID is zero"
                Return (0x00)
            }
            ElseIf ((Local1 == Local6))
            {
                If ((Local7 != FF32))
                {
                    Debug = "thread ID encountered twice"
                    Return (0x00)
                }

                Local7 = Local3
            }

            Local0++
            Local2--
            Local3++
        }

        /* Return Package: Index of current thread, ID of current thread */

        Local0 = Package (0x02){}
        Local0 [0x00] = Local6
        Local0 [0x01] = Local7
        Return (Local0)
    }

    /*
     * Report errors detected by the worker threads
     *
     * arg0 - name of test
     * arg1 - number of threads
     */
    Method (M106, 2, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        LPN0 = Arg1
        LPC0 = 0x00
        While (LPN0)
        {
            Local0 = DerefOf (P300 [LPC0])
            If (Local0)
            {
                /*
                 * Reports:
                 * lpC0   - Index of thread
                 * Local0 - the scale of its errors
                 */
                ERR (Arg0, Z147, __LINE__, 0x00, 0x00, LPC0, Local0)
            }

            LPN0--
            LPC0++
        }
    }

    /*
     * Initialization of multithreading interconnection
     *
     * Note: now when arguments (arg0, arg1, arg2) are determined
     *       by Threads command of AcpiExec and passed to test, it
     *       is unnecessary to do "The _TCI-based Initialization of
     *       multithreading interconnection" below. Used temporary.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     * arg3 - minimal number of threads needed for test
     */
    Method (M107, 4, NotSerialized)
    {
        /* Set the multi-threading mode flag */

        SET3 (0x01)
        /*
         * Local0 - auxiliary
         * Local1 - auxiliary
         * Local6 - ID of thread
         * Local7 - Index of thread
         */
        /* The _TCI-based Initialization of multithreading interconnection */
        If (FLG1)
        {
            Local0 = M104 (Arg0)
            Local1 = ObjectType (Local0)
            If ((Local1 != C00C))
            {
                ERR ("m107", Z147, __LINE__, 0x00, 0x00, Local1, C00C)
                Return (0x00)
            }

            /* Get ID and Index of current thread */

            Local6 = DerefOf (Local0 [0x00])
            Local7 = DerefOf (Local0 [0x01])
            If ((Local6 != Arg1))
            {
                ERR ("m107", Z147, __LINE__, 0x00, 0x00, Local6, Arg1)
                Return (0x00)
            }

            If ((Local7 != Arg2))
            {
                ERR ("m107", Z147, __LINE__, 0x00, 0x00, Local7, Arg2)
                Return (0x00)
            }
        }

        If (((Arg0 < 0x02) || (Arg0 < Arg3)))
        {
            Debug = "Insufficient number of threads for Test!"
            Return (0x00)
        }

        Return (0x01)
    }

    /*
     * Close testing
     *
     * arg0 - name of test
     * arg1 - number of threads
     * arg2 - ID of current thread
     * arg3 - Index of current thread
     */
    Method (M108, 4, NotSerialized)
    {
        /* all workers to exit the infinite loop */

        M100 (Arg1, Arg2, Arg3, CM01, 0x00, 0x00, 0x00)
        /* Report errors detected by the worker threads */

        M106 (Arg0, Arg1)
    }

    /*
     * CM01: all workers to exit the infinite loop
     *
     * arg0 - number of threads
     */
    Method (M10C, 1, Serialized)
    {
        /* All workers to exit the infinite loop */

        M200 (BS00, Arg0, C101) /* cmd: Exit the infinite loop */
        M114 (Arg0)
        /* Wait for all Worker threads */

        Name (B000, Buffer (Arg0){})
        Name (B001, Buffer (Arg0){})
        Name (B002, Buffer (Arg0){})
        CopyObject (BS00, B000) /* \M10C.B000 */
        M110 (Arg0, B000, B001, B002)
    }

    /*
     * CM02: all workers to sleep for the specified period
     *
     * arg0 - number of threads
     */
    Method (M10D, 1, NotSerialized)
    {
        /* All workers to sleep for the specified period */

        M200 (BS00, Arg0, C102) /* cmd: Sleep for the specified number of Milliseconds */
        M114 (Arg0)
        /* Wait for all Worker threads */

        M103 (Arg0)
    }

    /*
     * Control thread checks that the specified set of worker threads
     * hang on the specified operations or completed the operations.
     *
     * arg0 - number of threads
     * arg1 - buffer of arg0 length
     *        1 - check completion of operation
     *        2 - check hang
     *
     * Return:
     *   These mean unexpected behaviour:
     *     0x01 - some threads has not completed operation
     *     0x02 - some threads are not hang on operation
     *   These report the contents of buffer:
     *     0x10 - has checkings of completed operation
     *     0x20 - has checkings of hang on operation
     */
    Method (M10E, 2, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (RVAL, 0x00)
        LPN0 = Arg0
        LPC0 = 0x00
        While (LPN0)
        {
            /* For not a Control thread only */

            If ((LPC0 != 0x00))
            {
                Local0 = DerefOf (Arg1 [LPC0])
                Local1 = DerefOf (BS01 [LPC0])
                If ((Local0 == 0x01))
                {
                    /* check completion of operation */

                    RVAL |= 0x10
                    If (!Local1)
                    {
                        RVAL |= 0x01
                    }
                }
                ElseIf ((Local0 == 0x02))
                {
                    /* check hang */

                    RVAL |= 0x20
                    If (Local1)
                    {
                        RVAL |= 0x02
                    }
                }
            }

            LPN0--
            LPC0++
        }

        Return (RVAL) /* \M10E.RVAL */
    }

    /*
     * Run and analyze result of m10e()
     *
     * arg0,
     * arg1 - see m10e
     */
    Method (M10F, 2, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (RVAL, 0x00)
        LPN0 = SL03 /* \SL03 */
        LPC0 = 0x00
        While (LPN0)
        {
            Sleep (SL02)
            RVAL = M10E (Arg0, Arg1)
            If (!(RVAL & 0x20))
            {
                /* doesn't have checkings of hang */

                If (!(RVAL & 0x01))
                {
                    /* all examined have completed */

                    Break
                }
            }

            LPN0--
            LPC0++
        }

        Return (RVAL) /* \M10F.RVAL */
    }

    /*
     * Control thread waits for all the worker threads to
     * fulfill the specified for them buffer of commands.
     *
     * arg0 - number of threads (total)
     * arg1 - the per-thread expectations of completion status mapping buffer
     * arg2 - the per-thread expectations of hang       status mapping buffer
     * arg3 - the per-thread expectations of idle       status mapping buffer
     */
    Method (M110, 4, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (FIND, 0x00)
        Name (SL80, 0x00)
        Name (SL81, 0x00)
        Name (CMD0, 0x00)
        Name (HNG0, 0x00)
        Name (IDL0, 0x00)
        Name (QUIT, 0x00)
        /*
         * Check that all the worker threads saw my
         * non-zero do00 and fulfilled the proper command.
         */
        While (0x01)
        {
            FIND = 0x00
            LPN0 = Arg0
            LPC0 = 0x00
            While (LPN0)
            {
                /* For not a Control thread only */

                If ((LPC0 != 0x00))
                {
                    CMD0 = DerefOf (Arg1 [LPC0])
                    HNG0 = DerefOf (Arg2 [LPC0])
                    IDL0 = DerefOf (Arg3 [LPC0])
                    Local0 = DerefOf (BS00 [LPC0])
                    Local1 = DerefOf (BS01 [LPC0])
                    Local2 = DerefOf (BS03 [LPC0])
                    Local3 = DerefOf (BS04 [LPC0]) /* terminated threads */
                    If (Local3){                    /* Thread already completed by c108 */
                    }
                    ElseIf (CMD0)
                    {
                        If ((Local0 != CMD0))
                        {
                            ERR ("m110", Z147, __LINE__, 0x00, 0x00, Local0, CMD0)
                            Debug = LPC0 /* \M110.LPC0 */
                        }

                        If (!Local1)
                        {
                            /* Not completed yet */

                            FIND = 0x01
                            Break
                        }
                        ElseIf ((Local1 != Local0))
                        {
                            /* Has executed unexpected command */

                            ERR ("m110", Z147, __LINE__, 0x00, 0x00, Local1, Local0)
                            Debug = LPC0 /* \M110.LPC0 */
                        }
                    }
                    ElseIf (HNG0)
                    {
                        SL81 = 0x01
                        If ((SL80 < SL03))
                        {
                            /*
                             * Delay here is some pure attempt to be objective -
                             * it can look like hang now but go just after this
                             * checking.
                             */
                            SL80++
                            Sleep (SL02)
                        }

                        Local4 = DerefOf (BS01 [LPC0])
                        If (Local4)
                        {
                            /* Doesn't hang */

                            If ((Local4 != Local0))
                            {
                                /* Has executed unexpected command */

                                ERR ("m110", Z147, __LINE__, 0x00, 0x00, Local1, Local0)
                                Debug = LPC0 /* \M110.LPC0 */
                            }

                            ERR ("m110", Z147, __LINE__, 0x00, 0x00, Local0, Local4)
                            Debug = LPC0 /* \M110.LPC0 */
                        }
                    }
                    ElseIf (IDL0)
                    {
                        If ((Local0 != C100))
                        {
                            ERR ("m110", Z147, __LINE__, 0x00, 0x00, Local0, CMD0)
                            Debug = LPC0 /* \M110.LPC0 */
                        }

                        If (!Local2)
                        {
                            /* Not completed yet */

                            FIND = 0x01
                            Break
                        }
                        ElseIf ((Local2 != C100))
                        {
                            /* Has executed unexpected command */

                            ERR ("m110", Z147, __LINE__, 0x00, 0x00, Local0, CMD0)
                            Debug = LPC0 /* \M110.LPC0 */
                        }
                    }
                    Else
                    {
                        ERR ("m110", Z147, __LINE__, 0x00, 0x00, LPC0, Local0)
                        Debug = LPC0 /* \M110.LPC0 */
                    }
                }

                LPN0--
                LPC0++
            }

            QUIT = 0x00
            If (!FIND)
            {
                QUIT = 0x01
                /*
                 * All threads except those being checked for hang status
                 * have completed their commands.
                 */
                If (SL81)
                {
                    /* Has threads to check hang status */

                    If ((SL80 < SL03))
                    {
                        /* Not completed yet the specified delay */

                        QUIT = 0x00
                    }
                }
            }

            If (QUIT)
            {
                Break
            }

            /*
             * Don't report about Control thread sleeping -
             * don't use m206(0, sl00).
             */
            Sleep (SL00)
        }

        /*
         * Set do00 to zero and check that all the worker threads
         * saw my zero do00 (if only it is not the EXIT command).
         */
        M200 (BS02, Arg0, 0x00)
        DO00 = 0x00
        While (0x01)
        {
            FIND = 0x00
            LPN0 = Arg0
            LPC0 = 0x00
            While (LPN0)
            {
                /* For not a Control thread only */

                If ((LPC0 != 0x00))
                {
                    /*
                     * Reset the specified command for each thread
                     * which in fact doesn't hang.
                     */
                    Local0 = DerefOf (BS02 [LPC0])
                    If (Local0)
                    {
                        /* Alive, doesn't hang, so reset its command */

                        BS00 [LPC0] = C100 /* \C100 */
                        BS01 [LPC0] = 0x00
                    }

                    /*
                     * For all threads except those being checked for
                     * hang status and completed already.
                     */
                    HNG0 = DerefOf (Arg2 [LPC0])
                    Local0 = DerefOf (BS04 [LPC0])
                    If ((!HNG0 && !Local0))
                    {
                        Local0 = DerefOf (BS02 [LPC0])
                        If (!Local0)
                        {
                            FIND = 0x01
                            Break
                        }
                    }
                }

                LPN0--
                LPC0++
            }

            /*
             * All threads except those being checked for hang status
             * have zeroed do00.
             */
            If (!FIND)
            {
                Break
            }

            /*
             * Don't report about Control thread sleeping -
             * don't use m206(0, sl00).
             */
            Sleep (SL00)
        }
        /* All the worker threads are ready for any next command */
    }

    /*
     * Check absence of exception
     *
     * arg0 - ID of current thread
     * arg1 - Index of current thread
     * arg2 - exceptional condition flag
     * arg3 - the name of operation
     *
     * Return opcode of exception to be generated or zero
     */
    Method (M111, 4, Serialized)
    {
        If ((FLG0 || Arg2))
        {
            Local0 = CH08 ("m111", Arg0, Z147, 0x0C, 0x00, 0x00)
            If (Local0)
            {
                SE00 (Arg1, ER03, "Error er03")
            }
        }

        /* Analyze opcode of exception to be generated */

        Switch (Arg2)
        {
            Case (0x00)
            {
                Local0 = 0x00
            }
            Case (0xFE)
            {
                /* EX0E - check "no exception" */

                Local0 = 0x00
            }
            Case (0xFD)
            {
                /* EX0D - FAIL expected */

                Local0 = Arg2
                Concatenate (Arg3, ", generating FAIL condition ", Local1)
                M201 (Arg1, VB03, Local1)
            }
            Default
            {
                Local0 = Arg2
                Concatenate (Arg3, ", generating exceptional condition ", Local1)
                Concatenate (Local1, Local0, Local1)
                M201 (Arg1, VB03, Local1)
            }

        }

        Return (Local0)
    }

    /*
     * Check exception
     *
     * arg0 - ID of current thread
     * arg1 - Index of current thread
     * arg2 - exceptional condition flag
     * arg3 - return code of operation
     */
    Method (M112, 4, NotSerialized)
    {
        Local2 = 0x00
        If ((Arg2 == EX0E))
        {
            /* check "no exception" */

            Local0 = CH08 ("m112", Arg0, Z147, 0x0D, 0x00, 0x00)
            If (Local0)
            {
                SE00 (Arg1, ER03, "Error er03")
            }
        }
        ElseIf ((Arg2 == EX0D))
        {
            /* FAIL of operation expected */

            If (!Arg3)
            {
                ERR ("m112", Z147, __LINE__, 0x00, 0x00, Arg3, 0x01)
            }
        }
        ElseIf (Arg2)
        {
            /* check presence of particular exception */

            Local0 = CH09 (0x00, Arg0, Arg2, Z147, 0x0F, RefOf (Local2))
            If (Local0)
            {
                SE00 (Arg1, ER04, "Error er04")
            }
        }

        If (FLG0)
        {
            Local0 = CH08 ("m112", Arg0, Z147, 0x10, 0x00, 0x00)
            If (Local0)
            {
                SE00 (Arg1, ER03, "Error er03")
            }
        }
    }

    /*
     * Control thread initiates execution of commands by the worker threads
     *
     * arg0 - number of threads (total)
     */
    Method (M114, 1, NotSerialized)
    {
        M200 (BS01, Arg0, 0x00)
        M200 (BS03, Arg0, 0x00)
        DO00 = 0x01
    }

    /*
     * Return index of the greatest alive non-terminated yet thread
     *
     * arg0 - number of threads
     */
    Method (M115, 1, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        /* Means 'not found' */

        Local7 = Arg0
        /* Inverse order, excluding a Control thread */

        LPN0 = (Arg0 - 0x01)
        LPC0 = (Arg0 - 0x01)
        While (LPN0)
        {
            Local0 = DerefOf (BS04 [LPC0])
            If (!Local0)
            {
                Local7 = LPC0 /* \M115.LPC0 */
                Break
            }

            LPN0--
            LPC0--
        }

        Return (Local7)
    }

    /*
     * Add error-bit relative to arg0-th thread
     *
     * arg0 - Index of thread
     * arg1 - error-bit
     * arg2 - message
     */
    Method (SE00, 3, NotSerialized)
    {
        Local0 = DerefOf (P300 [Arg0])
        Local1 = (Arg1 | Local0)
        P300 [Arg0] = Local1
        If (VB04)
        {
            /* Add scale of Errors */

            Local0 = DerefOf (P100 [Arg0])
            Local1 = (Arg1 | Local0)
            P100 [Arg0] = Local1
            /* Increment statistics of Errors (number) */

            M212 (RefOf (P101), Arg0)
        }

        If (VB06)
        {
            Concatenate ("ERROR: ", Arg2, Local0)
            M201 (Arg0, 0x01, Local0)
        }
    }

    /*
     * Add warning-bit relative to arg0-th thread
     *
     * arg0 - Index of thread
     * arg1 - warning-bit
     * arg2 - message
     */
    Method (WRN0, 3, NotSerialized)
    {
        Local0 = DerefOf (P301 [Arg0])
        Local1 = (Arg1 | Local0)
        P301 [Arg0] = Local1
        If (VB04)
        {
            /* Add scale of Warnings */

            Local0 = DerefOf (P102 [Arg0])
            Local1 = (Arg1 | Local0)
            P102 [Arg0] = Local1
            /* Increment statistics of Warnings (number) */

            M212 (RefOf (P103), Arg0)
        }

        If (VB05)
        {
            Concatenate ("WARNING: ", Arg2, Local0)
            M201 (Arg0, 0x01, Local0)
        }
    }
