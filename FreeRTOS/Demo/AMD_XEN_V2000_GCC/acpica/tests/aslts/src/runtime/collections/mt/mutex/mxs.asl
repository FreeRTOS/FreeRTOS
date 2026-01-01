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
     * Access to mutexes routines
     */
    Name (Z149, 0x95)
    /*
     * Opcodes of initialization of set of mutexes
     *
     * c300 - usual
     * c301 - one mutex of Index equal to ((Index of current thread) - 1)
     */
    Name (C300, 0x00)
    Name (C301, 0x01)
    /*
     * Flags corresponding to Mutexes
     */
    Name (FL00, Package (MAX0)
    {
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){}
    })
    /*
     * Counters (current) corresponding to Mutexes
     * (how many times the relevant mutex has been
     * successfully Acquired (may be repeatedly)
     * (by the same thread))
     *
     * - incremented on Acquire
     * - decremented on Release
     */
    Name (FL01, Package (MAX0)
    {
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){}
    })
    /*
     * Counters corresponding to Mutexes
     *
     * how many times the mutex has successfully Acquired
     * by different threads.
     *
     * - incremented on Acquire
     * - reset to zero by the Control thread
     */
    Name (CNT0, Package (MAX0)
    {
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){},
        Package (MAX1){}
    })
    /*
     * Acquire mutex
     *
     * arg0 - ID of current thread
     * arg1 - Index of thread
     * arg2 - Level of mutex
     * arg3 - Index of mutex
     * arg4 - opcode of exception to be generated or zero
     * arg5 - opcode of TimeOutValue (see comment to ma00)
     * arg6 - if fall into sleep
     */
    Method (M310, 7, Serialized)
    {
        Local0 = M21E ("Acquire mutex, ", Arg2, Arg3)
        M201 (Arg1, VB03, Local0)
        /* Increment statistics of Acquire */

        If (VB04)
        {
            M212 (RefOf (P105), Arg1)
        }

        If ((Arg4 == EX0D))
        {
            /* FAIL expected */

            Local6 = 0x00
        }
        Else
        {
            Local6 = Arg4
        }

        Local7 = 0x01 /* Init with FAIL */
        Switch (Arg2)
        {
            Case (0x00)
            {
                Local7 = MA00 (Arg3, Local6, Arg5)
            }
            Case (0x01)
            {
                Local7 = MA01 (Arg3, Local6, Arg5)
            }
            Case (0x02)
            {
                Local7 = MA02 (Arg3, Local6, Arg5)
            }
            Case (0x03)
            {
                Local7 = MA03 (Arg3, Local6, Arg5)
            }
            Case (0x04)
            {
                Local7 = MA04 (Arg3, Local6, Arg5)
            }
            Case (0x05)
            {
                Local7 = MA05 (Arg3, Local6, Arg5)
            }
            Case (0x06)
            {
                Local7 = MA06 (Arg3, Local6, Arg5)
            }
            Case (0x07)
            {
                Local7 = MA07 (Arg3, Local6, Arg5)
            }
            Case (0x08)
            {
                Local7 = MA08 (Arg3, Local6, Arg5)
            }
            Case (0x09)
            {
                Local7 = MA09 (Arg3, Local6, Arg5)
            }
            Case (0x0A)
            {
                Local7 = MA0A (Arg3, Local6, Arg5)
            }
            Case (0x0B)
            {
                Local7 = MA0B (Arg3, Local6, Arg5)
            }
            Case (0x0C)
            {
                Local7 = MA0C (Arg3, Local6, Arg5)
            }
            Case (0x0D)
            {
                Local7 = MA0D (Arg3, Local6, Arg5)
            }
            Case (0x0E)
            {
                Local7 = MA0E (Arg3, Local6, Arg5)
            }
            Case (0x0F)
            {
                Local7 = MA0F (Arg3, Local6, Arg5)
            }

        }

        If ((Arg4 == EX0D))
        {
            /* FAIL expected */

            If (Local7)
            {
                M201 (Arg1, VB03, "Acquire returned non-zero, it was expected")
            }
            Else
            {
                M201 (Arg1, VB03, "Error 9: Acquire returned zero but FAIL expected!")
                SE00 (Arg1, ER09, "Error er09")
            }

            Return (Local7)
        }
        ElseIf (Arg4)
        {
            Return (0x01)
        }
        ElseIf (Local7)
        {
            M201 (Arg1, VB03, "Error 0: Acquire returned non-zero!")
            SE00 (Arg1, ER00, "Error er00")
            Return (0x01)
        }
        Else
        {
            /*
             * Increment counter (cnt0) and set up flag (fl00)
             * corresponding to mutex. Report error in case the
             * flag is non-zero.
             */
            Local7 = M21E ("Incrementing count of mutex, ", Arg2, Arg3)
            Concatenate (Local7, " and set up its flag", Local1)
            M201 (Arg1, VB03, Local1)
            M331 (Arg1, Arg2, Arg3)
            If (Arg6)
            {
                M201 (Arg1, VB03, "Fall into sleep")
                If (SLM0)
                {
                    Divide (Arg1, 0x05, Local1)
                    Local2 = 0x64
                    Switch (Local1)
                    {
                        Case (0x00)
                        {
                            Local2 = I100 /* \I100 */
                        }
                        Case (0x01)
                        {
                            Local2 = I101 /* \I101 */
                        }
                        Case (0x02)
                        {
                            Local2 = I102 /* \I102 */
                        }
                        Case (0x03)
                        {
                            Local2 = I103 /* \I103 */
                        }
                        Case (0x04)
                        {
                            Local2 = I104 /* \I104 */
                        }
                        Case (0x05)
                        {
                            Local2 = I105 /* \I105 */
                        }
                        Case (0x06)
                        {
                            Local2 = I106 /* \I106 */
                        }
                        Case (0x07)
                        {
                            Local2 = I107 /* \I107 */
                        }
                        Case (0x08)
                        {
                            Local2 = I108 /* \I108 */
                        }

                    }

                    M206 (Arg1, Local2)
                }
                Else
                {
                    M206 (Arg1, SL01)
                }
            }
        }

        Return (0x00)
    }

    /*
     * Release mutex
     *
     * arg0 - ID of current thread
     * arg1 - Index of thread
     * arg2 - Level of mutex
     * arg3 - Index of mutex
     * arg4 - opcode of exception to be generated or zero
     * arg5 - if fall into sleep
     */
    Method (M311, 6, Serialized)
    {
        Local0 = M21E ("Release mutex, ", Arg2, Arg3)
        M201 (Arg1, VB03, Local0)
        /* Increment statistics of Release */

        If (VB04)
        {
            M212 (RefOf (P106), Arg1)
        }

        /*
         * Check up and reset flag (fl00) corresponding to this Mutex
         * (check that it was not changed by other threads while this
         * one was sleeping).
         */
        If (!Arg4)
        {
            M332 (Arg1, Arg2, Arg3)
        }

        Switch (Arg2)
        {
            Case (0x00)
            {
                MA10 (Arg3)
            }
            Case (0x01)
            {
                MA11 (Arg3)
            }
            Case (0x02)
            {
                MA12 (Arg3)
            }
            Case (0x03)
            {
                MA13 (Arg3)
            }
            Case (0x04)
            {
                MA14 (Arg3)
            }
            Case (0x05)
            {
                MA15 (Arg3)
            }
            Case (0x06)
            {
                MA16 (Arg3)
            }
            Case (0x07)
            {
                MA17 (Arg3)
            }
            Case (0x08)
            {
                MA18 (Arg3)
            }
            Case (0x09)
            {
                MA19 (Arg3)
            }
            Case (0x0A)
            {
                MA1A (Arg3)
            }
            Case (0x0B)
            {
                MA1B (Arg3)
            }
            Case (0x0C)
            {
                MA1C (Arg3)
            }
            Case (0x0D)
            {
                MA1D (Arg3)
            }
            Case (0x0E)
            {
                MA1E (Arg3)
            }
            Case (0x0F)
            {
                MA1F (Arg3)
            }

        }

        If (Arg5)
        {
            M206 (Arg1, SL01)
        }
    }

    /*
     * Reset all counters (cnt0) and flags (fl00)
     * corresponding to all Mutexes.
     */
    Method (M330, 0, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (LPN1, 0x00)
        Name (LPC1, 0x00)
        LPN0 = MAX0 /* \MAX0 */
        LPC0 = 0x00
        While (LPN0)
        {
            LPN1 = MAX1 /* \MAX1 */
            LPC1 = 0x00
            While (LPN1)
            {
                DerefOf (CNT0 [LPC0]) [LPC1] = 0x00
                DerefOf (FL00 [LPC0]) [LPC1] = 0x00
                LPN1--
                LPC1++
            }

            LPN0--
            LPC0++
        }
    }

    /*
     * For Acquire
     *
     * Increment counter (cnt0) and set up flag (fl00)
     * corresponding to the mutex of arg1-Level and
     * arg2-Index. Report error in case the flag is non-zero.
     *
     * arg0 - Index of thread
     * arg1 - Level of mutex
     * arg2 - Index of mutex
     */
    Method (M331, 3, NotSerialized)
    {
        /* Local1 - the value of flag (index of thread owning the mutex) */

        Local0 = DerefOf (FL00 [Arg1])
        Local1 = DerefOf (Local0 [Arg2])
        If (Local1)
        {
            If ((Local1 == Arg0))
            {
                Local7 = M21E ("Mutex ", Arg1, Arg2)
                Concatenate (Local7, " is already owned by thr ", Local7)
                Concatenate (Local7, Arg0, Local7)
                WRN0 (Arg0, WN00, Local7)
            }
            Else
            {
                SE00 (Arg0, ER01, "Error er01")
            }
        }

        /* Set up flag */

        DerefOf (FL00 [Arg1]) [Arg2] = Arg0
        /* Increment counter cnt0 (owning by all threads) */

        Local0 = DerefOf (CNT0 [Arg1])
        Local1 = DerefOf (Local0 [Arg2])
        Local1++
        DerefOf (CNT0 [Arg1]) [Arg2] = Local1
        /* Increment counter fl01 (owning by one thread) */

        Local0 = DerefOf (FL01 [Arg1])
        Local1 = DerefOf (Local0 [Arg2])
        Local1++
        DerefOf (FL01 [Arg1]) [Arg2] = Local1
    }

    /*
     * For Release
     *
     * Check up and reset flag (fl00) corresponding to this Mutex
     * (check that it was not changed by other threads while this
     * one was sleeping).
     *
     * arg0 - Index of thread
     * arg1 - Level of mutex
     * arg2 - Index of mutex
     */
    Method (M332, 3, NotSerialized)
    {
        /* Local1 - the value of flag (index of thread owning the mutex) */

        Local0 = DerefOf (FL00 [Arg1])
        Local1 = DerefOf (Local0 [Arg2])
        If ((Local1 != Arg0))
        {
            SE00 (Arg0, ER02, "Error er02")
        }
        Else
        {
            /* Reset flag */
            /* Local1 - counter of owning the mutex by the same thread */
            Local0 = DerefOf (FL01 [Arg1])
            Local1 = DerefOf (Local0 [Arg2])
            If ((Local1 == 0x00))
            {
                SE00 (Arg0, ER08, "Error er08")
            }
            Else
            {
                Local1--
                If ((Local1 == 0x00))
                {
                    /*
                     * May be greater than one when owning mutex by the
                     * same thread several times (allowed for ACPI mutex).
                     */
                    DerefOf (FL00 [Arg1]) [Arg2] = 0x00
                }

                DerefOf (FL01 [Arg1]) [Arg2] = Local1
            }
        }
    }

    /*
     * Check up the value of counter corresponding to this Mutex
     *
     * arg0 - Level of mutex
     * arg1 - Index of mutex
     * arg2 - expected value of counter
     */
    Method (M333, 3, NotSerialized)
    {
        Local0 = DerefOf (CNT0 [Arg0])
        Local1 = DerefOf (Local0 [Arg1])
        If ((Local1 != Arg2))
        {
            ERR ("m333", Z149, __LINE__, 0x00, 0x00, Local1, Arg2)
            Debug = Arg0
            Debug = Arg1
        }
    }

    /*
     * Specify the per-thread set of mutexes to deal with in operation
     *
     * arg0 - number of threads (threads actually in work)
     * arg1 - opcode of initialization
     * arg2 - Level of mutex (initial)
     * arg3 - Number of levels of mutexes
     * arg4 - Index of mutex (inside the level)
     * arg5 - Number of mutexes of the same level
     */
    Method (M334, 6, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        LPN0 = Arg0
        LPC0 = 0x00
        While (LPN0)
        {
            /* For not a Control thread only */

            If ((LPC0 != 0x00))
            {
                Switch (Arg1)
                {
                    Case (0x01)
                    {
                        /* c301 */
                        /*
                         * One mutex of Index equal to
                         * ((Index of current thread) - 1)
                         */
                        P200 [LPC0] = Arg2
                        P201 [LPC0] = Arg3
                        Local0 = (LPC0 - 0x01)
                        P202 [LPC0] = Local0
                        P203 [LPC0] = 0x01
                    }
                    /* c300 */

                    Default
                    {
                        P200 [LPC0] = Arg2
                        P201 [LPC0] = Arg3
                        P202 [LPC0] = Arg4
                        P203 [LPC0] = Arg5
                    }

                }
                        /* Switch() */
            }

            /* if() */

            LPN0--
            LPC0++
        }
    }

    /*
     * Control thread initiates workers to Acquire
     * specified set of mutexes - on each specified
     * level - one mutex of Index which is equal to
     * ((Index of thread) - 1).
     *
     * When all workers complete that operation checks up
     * the state of execution of operation provided by
     * workers.
     *
     * arg0 - number of threads (total)
     * arg1 - number of threads (threads actually in work)
     *
     * ====== as for m334:
     * arg2 - Level of mutex (initial)
     * arg3 - Number of levels of mutexes
     *
     * arg4 - expected value of counter
     * arg5 - exceptional conditions flags (buffer/Integer)
     */
    Method (M337, 6, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        /* Acquire specified set of mutexes */
        /* Set up per-thread set of mutexes */
        M334 (Arg1, C301, Arg2, Arg3, 0x00, 0x00)
        /* Init the exceptional conditions flags */

        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
        M20F (Arg1, Arg5, 0x00)
        /* c106 for all first arg1 threads */

        M210 (BS00, Arg0, C106, 0x00, Arg1, 0x01, C102) /* cmd: Acquire specified set of mutexes */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
        /* Check up the values of counters of all Mutexes */

        LPN0 = Arg3
        LPC0 = Arg2
        While (LPN0)
        {
            M333 (LPC0, 0x00, Arg4)
            LPN0--
            LPC0++
        }
    }

    /*
     * Control thread initiates workers to Release
     * specified set of mutexes - on each specified
     * level - one mutex of Index which is equal to
     * ((Index of thread) - 1).
     *
     * Control thread initiates workers to Release
     * specified set of mutexes.
     *
     * arg0 - number of threads (total)
     * arg1 - number of threads (threads actually in work)
     *
     * ====== as for m334:
     * arg2 - Level of mutex (initial)
     * arg3 - Number of levels of mutexes
     */
    Method (M338, 4, NotSerialized)
    {
        /* Set up per-thread set of mutexes */

        M334 (Arg1, C301, Arg2, Arg3, 0x00, 0x00)
        /* c107 for all first arg1 threads */

        M210 (BS00, Arg0, C107, 0x00, Arg1, 0x01, C102) /* cmd: Release specified set of mutexes */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
    }

    /*
     * Control thread checks that the specified set of worker threads
     * hang on the specified operations or completed the operations.
     *
     * See m10e for args:
     * arg0 - number of threads
     * arg1 - buffer
     */
    Method (M33D, 2, NotSerialized)
    {
        Local0 = M10F (Arg0, Arg1)
        If ((Local0 & 0x01))
        {
            ERR ("m33d", Z149, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        If ((Local0 & 0x02))
        {
            ERR ("m33d", Z149, __LINE__, 0x00, 0x00, Local0, 0x00)
        }
    }

    /*
     * Run command for the specified set of workers
     *
     * arg0 - number of threads
     * arg1 - specificator of elements (see m20a)
     * arg2 - command
     */
    Method (M33E, 3, NotSerialized)
    {
        M20A (BS00, Arg0, Arg2, Arg1) /* cmd */
        M114 (Arg0)
        /* Wait for Worker threads */

        M103 (Arg0)
    }

    /*
     * Control thread initiates commands for workers to be fulfilled.
     * After commands execution checks the statuses of all threads.
     *
     * It should be one of the following:
     *   - thread completed the specified command
     *   - thread hangs (on the specified command)
     *   - all other idle threads completed the 'idle-command'
     *     (for all those threads not enumerated in either 'Expected
     *     completion statuses' or 'Expected hang statuses' lists).
     *
     * Note: because of the restricted number of ACPI arguments available,
     *       the input data are combined.
     *
     * arg0 - numbers of threads (buffer/Integer).
     *        Integer:
     *          number of threads both total and 'actually in work'
     *        Buffer (elements of buffer):
     *          0-th element - number of threads (total)
     *          1-th element - number of threads (threads actually in work, not extra idle ones)
     *
     * arg1 - Commands (buffer/Integer).
     *
     *        buffer/Integer, per-thread commands to be fulfilled
     *        Integer:
     *          0        - undefined
     *          non-zero - the same command for all worker threads
     *        Buffer (elements of buffer):
     *          0        - undefined
     *          non-zero - command for the relevant worker thread
     *
     * arg2 - Exceptional conditions flags (buffer/Integer)
     *
     *        buffer/Integer, per-thread flags of exceptional conditions
     *        Integer:
     *          - non-zero means that we generate the same
     *            exceptional condition for all worker threads
     *        Buffer (elements of buffer):
     *          0        - exception is not expected
     *          non-zero - means that we generate exceptional condition
     *                     for the relevant thread
     *
     *        The particular value (X0) of the exceptional condition flag
     *        corresponding to the particular thread means the following:
     *
     *        0: do nothing
     *        non-zero:
     *
     *          1) before to run operation:
     *
     *             check absence of any exception occurred on this thread
     *
     *          2) after the operation is completed depending on X0:
     *
     *             EX0E (particular undefined opcode of exception):
     *
     *               check that no any exception occurred on this thread
     *
     *             otherwise:
     *
     *               check that exception with opcode equal to X0
     *               has occurred on this thread
     *
     * arg3 - Levels of mutexes (buffer/Integer).
     *
     *        buffer/Integer, per-thread levels of mutexes
     *        Integer:
     *          - the same level of mutex for all worker threads
     *            (number of levels is 1)
     *        Buffer (elements of buffer):
     *        Pairs:
     *          - start level of mutex for the relevant thread
     *          - number of levels
     *
     * arg4 - Indexes of mutexes (buffer/Integer).
     *
     *        buffer/Integer, per-thread indexes of mutexes
     *        Integer:
     *          - the same index of mutex for all worker threads
     *            (number of mutexes of the same level is 1)
     *        Buffer (elements of buffer):
     *        Pairs:
     *          - start index of mutex for the relevant thread
     *          - number of mutexes of the same level
     *
     * arg5 - Expected completion statuses (the same semantics as Commands) (buffer/Integer).
     *
     *        buffer/Integer, per-thread commands to check for completion
     *        Integer:
     *          0        - do nothing
     *          non-zero - the same command for all worker threads
     *        Buffer (elements of buffer):
     *          0        - do nothing
     *          non-zero - command for the relevant worker thread
     *
     * arg6 - Expected hang statuses (the same semantics as Commands) (buffer/Integer).
     *
     *        buffer/Integer, per-thread commands to check for hang
     *        Integer:
     *          0        - do nothing
     *          non-zero - the same command for all worker threads
     *        Buffer (elements of buffer):
     *          0        - do nothing
     *          non-zero - command for the relevant worker thread
     *
     *        Note: non-zero 0-th element of the buffer means the
     *              number of hanging threads expected to wake up
     *              after some command of arg1 will be executed.
     */
    Method (M33F, 7, Serialized)
    {
        Name (NTH0, 0x00) /* total */
        Name (NTH1, 0x00) /* actually in work */
        Name (HAS1, 0x00) /* has non-zero exception expectations */
        /* Check params */

        Local0 = M344 (Arg5, Arg6)
        If (Local0)
        {
            ERR ("m33f: incorrect parameters", Z149, __LINE__, 0x00, 0x00, Arg5, Arg6)
            Debug = Local0
            Return (Zero)
        }

        /* Parse number of threads */

        If ((ObjectType (Arg0) == C009))
        {
            NTH0 = Arg0
            NTH1 = Arg0
        }
        Else
        {
            NTH0 = DerefOf (Arg0 [0x00])
            NTH1 = DerefOf (Arg0 [0x01])
        }

        /* 1) Command execution */
        /*
         * Prepare buffers of per-thread commands and arguments
         *
         * Resulting data: bs00, p200, p201, p202, p203, p204
         *
         * Note: not specified elements of buffers are not touched.
         */
        HAS1 = M340 (NTH1, Arg1, Arg2, Arg3, Arg4)
        /* Allow workers to execute their commands */

        M114 (NTH0)
        /* 2) Check status of execution of commands */
        /* Calculate the per-thread expectations of completion statuses */
        Local0 = M342 (NTH0, NTH1, Arg5)
        /* Calculate the per-thread expectations of hang statuses */

        Local1 = M342 (NTH0, NTH1, Arg6)
        /* Calculate the idle-threads mapping buffer */

        Local2 = M343 (NTH0, NTH1, Local0, Local1)
        /*
         * So, each thread is represented in one and only one of sets:
         *
         * Local0 - expectations of completion
         * Local1 - expectations of hang
         * Local2 - idle
         */
        /* Wait for all Worker threads and check their statuses */
        M110 (NTH0, Local0, Local1, Local2)
        /* Reset exception expectation */

        M336 (NTH0, HAS1)
    }

    /*
     * Prepare buffers of per-thread commands and arguments
     *
     * Resulting data: bs00, p200, p201, p202, p203
     *
     * Note: don't touch not specified elements of buffer.
     *
     * arg0 - number of threads (threads actually in work)
     * arg1 - Commands (see m33f)
     * arg2 - Exceptional conditions flags (see m33f)
     * arg3 - Levels of mutexes (see m33f)
     * arg4 - Indexes of mutexes (see m33f)
     */
    Method (M340, 5, Serialized)
    {
        Name (HAS0, 0x00)
        Name (HAS1, 0x00) /* has non-zero exception expectations */
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (SLCT, 0x00)
        Name (CMD0, 0x00)
        Name (B000, Buffer (Arg0){})
        Name (B200, Buffer (Arg0){})
        Name (B201, Buffer (Arg0){})
        Name (B202, Buffer (Arg0){})
        Name (B203, Buffer (Arg0){})
        Local0 = ObjectType (Arg1)
        If ((Local0 == C009))
        {
            /* Integer */

            CMD0 = Arg1
            If (!CMD0)
            {
                Return (Zero)
            }
        }
        Else
        {
            /* Buffer/Package */

            SLCT = 0x01
        }

        LPN0 = Arg0
        LPC0 = 0x00
        While (LPN0)
        {
            /* For not a Control thread only */

            If ((LPC0 != 0x00))
            {
                If (SLCT)
                {
                    CMD0 = DerefOf (Arg1 [LPC0])
                }

                If (CMD0)
                {
                    HAS0 = 0x01
                    B000 [LPC0] = CMD0 /* \M340.CMD0 */
                    /* Prepare arguments of command */

                    Local0 = M341 (CMD0, LPC0, Arg3, Arg4)
                    If ((ObjectType (Local0) == C00C))
                    {
                        Local1 = DerefOf (Local0 [0x00])
                        B200 [LPC0] = Local1
                        Local1 = DerefOf (Local0 [0x01])
                        B201 [LPC0] = Local1
                        Local1 = DerefOf (Local0 [0x02])
                        B202 [LPC0] = Local1
                        Local1 = DerefOf (Local0 [0x03])
                        B203 [LPC0] = Local1
                    }
                }
            }

            LPN0--
            LPC0++
        }

        /* Prepare the exceptional conditions flags buffer */

        Local1 = M20E (Arg0, Arg2)
        /*
         * Prepare all the commands and arguments and then re-write
         * them into the target buffers looks there useful for debugging.
         */
        If (HAS0)
        {
            LPN0 = Arg0
            LPC0 = 0x00
            While (LPN0)
            {
                CMD0 = DerefOf (B000 [LPC0])
                If (CMD0)
                {
                    BS00 [LPC0] = CMD0 /* \M340.CMD0 */
                    Local0 = DerefOf (B200 [LPC0])
                    P200 [LPC0] = Local0
                    Local0 = DerefOf (B201 [LPC0])
                    P201 [LPC0] = Local0
                    Local0 = DerefOf (B202 [LPC0])
                    P202 [LPC0] = Local0
                    Local0 = DerefOf (B203 [LPC0])
                    P203 [LPC0] = Local0
                    Local0 = DerefOf (Local1 [LPC0])
                    If (Local0)
                    {
                        HAS1 = 0x01
                    }

                    P204 [LPC0] = Local0
                    P205 [LPC0] = TOVF /* \TOVF */
                }

                LPN0--
                LPC0++
            }
        }

        Return (HAS1) /* \M340.HAS1 */
    }

    /*
     * Prepare arguments of command
     *
     * arg0 - command
     * arg1 - index of thread
     * arg2 - Levels of mutexes (see m33f)
     * arg3 - Indexes of mutexes (see m33f)
     *
     * Return (no free ArgX to pass references to target Packages there,
     *         so using Return):
     *   - Package with elements to be filled
     *     into p200, p201, p202, p203.
     *   - Integer if no arguments.
     */
    Method (M341, 4, Serialized)
    {
        Name (HAS0, 0x00)
        Name (P000, Package (0x04)
        {
            0x00,
            0x00,
            0x00,
            0x00
        })
        Name (I000, 0x00)
        Name (I001, 0x00)
        Name (I002, 0x00)
        Name (I003, 0x00)
        Switch (Arg0)
        {
            Case (Package (0x03)
                {
                    0xF6,
                    0xF7,
                    0xF3
                }

)
            {
                /* 0xf6, c106 - Acquire specified set of mutexes */
                /* 0xf7, c107 - Release specified set of mutexes */
                /* 0xf3, c103 - Acquire/Sleep/Release */
                /*
                 * To calculate:
                 *
                 * i000 - starting level of mutex
                 * i001 - number of levels
                 * i002 - starting index of mutex (of the same level)
                 * i003 - number of mutexes (of the same level)
                 */
                /* Levels */
                Local0 = ObjectType (Arg2)
                If ((Local0 == C009))
                {
                    /* Integer */

                    I000 = Arg2
                    I001 = 0x01
                }
                Else
                {
                    /* Buffer/Package */

                    Local0 = (Arg1 * 0x02)
                    I000 = DerefOf (Arg2 [Local0])
                    Local0++
                    I001 = DerefOf (Arg2 [Local0])
                }

                /* Indexes */

                Local0 = ObjectType (Arg3)
                If ((Local0 == C009))
                {
                    /* Integer */

                    I002 = Arg3
                    I003 = 0x01
                }
                Else
                {
                    /* Buffer/Package */

                    Local0 = (Arg1 * 0x02)
                    I002 = DerefOf (Arg3 [Local0])
                    Local0++
                    I003 = DerefOf (Arg3 [Local0])
                }

                HAS0 = 0x01
            }
            Default
            {
                ERR ("m341: unexpected command:", Z149, __LINE__, 0x00, 0x00, 0x00, Arg0)
            }

        }

        If (HAS0)
        {
            P000 [0x00] = I000 /* \M341.I000 */
            P000 [0x01] = I001 /* \M341.I001 */
            P000 [0x02] = I002 /* \M341.I002 */
            P000 [0x03] = I003 /* \M341.I003 */
            Return (P000) /* \M341.P000 */
        }

        Return (0x00)
    }

    /*
     * Prepare the per-thread status expectations mapping buffer
     *
     * arg0 - number of threads (total)
     * arg1 - number of threads (threads actually in work)
     * arg2 - Expected completion/hang statuses (see m33f)
     *
     * Return:
     *
     * Buffer (elements of buffer):
     *   0        - nothing to do for the relevant thread
     *   non-zero - element of buffer means the last command
     *              specified for the relevant thread.
     */
    Method (M342, 3, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (SLCT, 0x00)
        Name (CMD0, 0x00)
        Name (B000, Buffer (Arg0){})
        Local0 = ObjectType (Arg2)
        If ((Local0 == C009))
        {
            /* Integer */

            CMD0 = Arg2
            If (!CMD0)
            {
                Return (B000) /* \M342.B000 */
            }
        }
        Else
        {
            /* Buffer/Package */

            SLCT = 0x01
        }

        LPN0 = Arg1
        LPC0 = 0x00
        While (LPN0)
        {
            If (SLCT)
            {
                CMD0 = DerefOf (Arg2 [LPC0])
            }

            If (CMD0)
            {
                B000 [LPC0] = CMD0 /* \M342.CMD0 */
            }

            LPN0--
            LPC0++
        }

        Return (B000) /* \M342.B000 */
    }

    /*
     * Prepare the idle-threads mapping buffer
     *
     * arg0 - number of threads (total)
     * arg1 - number of threads (threads actually in work, not extra idle ones)
     * arg2 - Buffer, expected completion statuses (see m33f)
     * arg3 - Buffer, Expected hang statuses (see m33f)
     *
     * Return:
     *
     * Buffer (elements of buffer):
     *   0        - the relevant thread is non-idle
     *   non-zero - the relevant thread is idle
     */
    Method (M343, 4, Serialized)
    {
        Name (ERR0, 0x00)
        Name (IDLE, 0x00)
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (B000, Buffer (Arg0){})
        LPN0 = Arg0
        LPC0 = 0x00
        While (LPN0)
        {
            IDLE = 0x00
            If ((LPC0 >= Arg1))
            {
                IDLE = 0x01
            }
            Else
            {
                Local0 = DerefOf (Arg2 [LPC0])
                Local1 = DerefOf (Arg3 [LPC0])
                If ((Local0 && Local1))
                {
                    /* Expects both completion and hang simultaneously */

                    ERR0 = 0x01
                }
                ElseIf ((!Local0 && !Local1))
                {
                    IDLE = 0x01
                }
            }

            B000 [LPC0] = IDLE /* \M343.IDLE */
            LPN0--
            LPC0++
        }

        If (ERR0)
        {
            ERR ("m333", Z149, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        Return (B000) /* \M343.B000 */
    }

    /*
     * Check pair of parameters
     *
     * arg0 - Expected completion statuses (see m33f).
     * arg1 - Expected hang       statuses (see m33f).
     */
    Method (M344, 2, Serialized)
    {
        Name (INT0, 0x00)
        Name (INT1, 0x00)
        Name (ALL0, 0x00)
        Name (ALL1, 0x00)
        If ((ObjectType (Arg0) == C009))
        {
            INT0 = 0x01
            If (Arg0)
            {
                ALL0 = 0x01
            }
        }

        If ((ObjectType (Arg1) == C009))
        {
            INT1 = 0x01
            If (Arg1)
            {
                ALL1 = 0x01
            }
        }

        If ((ALL0 || ALL1))
        {
            If ((INT0 && INT0))
            {
                If ((ALL0 && ALL1))
                {
                    Return (0x01)
                }
            }
            Else
            {
                Return (0x02)
            }
        }

        Return (0x00)
    }

    /*
     * Reset exception expectation
     *
     * arg0 - number of threads (total)
     * arg1 - non-zero -- has non-zero exception expectations
     */
    Method (M336, 2, NotSerialized)
    {
        /* Add statistics of exceptions (total) */

        EX10 += EXC0 /* \EXC0 */
        If (Arg1)
        {
            If (!EXC0)
            {
                /* Expected exceptions but have none */

                ERR ("m333", Z149, __LINE__, 0x00, 0x00, EXC0, 0x00)
            }
        }
        ElseIf (EXC0)
        {
            /* Unexpected exceptions */

            ERR ("m333", Z149, __LINE__, 0x00, 0x00, EXC0, 0x00)
        }

        /*Reset EXC0 (the current number of exceptions handled) */

        CH0A ()
        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
    }

    /* Init fl01 */

    Method (M339, 0, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (LPN1, 0x00)
        Name (LPC1, 0x00)
        LPN0 = MAX0 /* \MAX0 */
        LPC0 = 0x00
        While (LPN0)
        {
            LPN1 = MAX1 /* \MAX1 */
            LPC1 = 0x00
            While (LPN1)
            {
                DerefOf (FL01 [LPC0]) [LPC1] = 0x00
                LPN1--
                LPC1++
            }

            LPN0--
            LPC0++
        }
    }
