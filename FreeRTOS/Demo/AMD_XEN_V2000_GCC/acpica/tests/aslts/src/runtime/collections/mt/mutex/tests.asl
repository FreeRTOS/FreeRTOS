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
     * The test strategies to be managed and controlled by the
     * Control Thread and fulfilled by the Worker Threads (Workers).
     */
    Name (Z152, 0x98)
    /*
     * Acquire/Sleep/Release
     *
     * All workers:
     * - Acquire the same mutex
     * - increment global counter
     * - set up another global to its Index
     * - sleep for the specified period
     * - check that the global contains just its Index
     * - Release mutex
     * Control thread:
     * - check after all threads complete that counter is correct
     *
     * arg0 - number of threads
     * arg1 - Level of mutex
     * arg2 - Index of mutex
     * arg3 - Number of mutexes of the same level
     */
    Method (M801, 4, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (NUMW, 0x00) /* number of threads in work */
        /* Number of threads to be actually in work */

        NUMW = M213 (Arg0, 0x05, 0x04)
        /* Set up per-thread set of mutexes */

        M334 (NUMW, C300, Arg1, 0x00, Arg2, Arg3)
        /* c103 for all first num threads */

        M210 (BS00, Arg0, C103, 0x00, NUMW, 0x01, C102) /* cmd: Acquire/Sleep/Release */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
        /* Check up the values of counters of all Mutexes */
        /* lpC0 - Index of mutex */
        Local0 = (NUMW - 0x01) /* exclude the Control thread */
        LPN0 = Arg3
        LPC0 = Arg2
        While (LPN0)
        {
            M333 (Arg1, LPC0, Local0)
            LPN0--
            LPC0++
        }
    }

    /*
     * <Acquire/Sleep>(0-15 levels)/Release(15-0 levels)
     *
     * arg0 - number of threads
     * arg1 - Index of mutex
     * arg2 - Number of mutexes of the same level
     */
    Method (M802, 3, Serialized)
    {
        Name (NUMW, 0x00) /* number of threads in work */
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (LPN1, 0x00)
        Name (LPC1, 0x00)
        /* Number of threads to be actually in work */

        NUMW = M213 (Arg0, 0x05, 0x05)
        /* Set up per-thread set of mutexes */

        M334 (NUMW, C300, 0x00, 0x00, Arg1, Arg2)
        /* c104 for all first num threads */

        M210 (BS00, Arg0, C104, 0x00, NUMW, 0x01, C102) /* cmd: <Acquire/Sleep>(0-15 levels)/Release(15-0 levels) */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
        /* Check up the values of counters of all Mutexes */

        Local0 = (NUMW - 0x01)
        LPN0 = MAX0 /* \MAX0 */
        LPC0 = 0x00
        While (LPN0)
        {
            /* lpC0 - Level */

            LPN1 = Arg2
            LPC1 = Arg1
            While (LPN1)
            {
                /* lpC1 - Index of mutex */

                M333 (LPC0, LPC1, Local0)
                LPN1--
                LPC1++
            }

            LPN0--
            LPC0++
        }
    }

    /*
     * Example 0
     *
     * arg0 - number of threads
     * arg1 - Index of mutex
     * arg2 - Number of mutexes of the same level
     */
    Method (M803, 1, Serialized)
    {
        Name (NUMW, 0x00) /* number of threads in work */
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        /* Number of threads to be actually in work */

        NUMW = M213 (Arg0, 0x06, 0x06)
        /* c105 for all first num threads */

        M210 (BS00, Arg0, C105, 0x00, NUMW, 0x01, C102) /* cmd: Example 0 */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
    }

    /*
     * Manage the test m804
     *
     * arg0 - number of threads
     * arg1 - 0        - thread_2 Releases than thread_1 Releases
     *        non-zero - thread_1 Releases than thread_2 Releases
     * Thread_1:
     * arg2 - Level of mutex (initial)
     * arg3 - Number of levels of mutexes
     * Thread_2:
     * arg4 - Level of mutex (initial)
     * arg5 - Number of levels of mutexes
     */
    Method (M8FF, 6, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (THR, 0x00)
        /* ACQUIRING */
        /* === Thread 1 === */
        THR = 0x01
        /* Set up per-thread set of mutexes */

        M334 (Arg0, C300, Arg2, Arg3, 0x00, 0x01)
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR, C106)  /* cmd: Acquire specified set of mutexes */
        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
        M114 (Arg0)
        /* Wait for all Worker threads */

        M103 (Arg0)
        /* Check up the values of counters of all Mutexes */

        LPN0 = Arg3
        LPC0 = Arg2
        While (LPN0)
        {
            M333 (LPC0, 0x00, 0x01)
            LPN0--
            LPC0++
        }

        /* === Thread 2 === */

        THR = 0x02
        /* Set up per-thread set of mutexes */

        M334 (Arg0, C300, Arg4, Arg5, 0x01, 0x01)
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR, C106)  /* cmd: Acquire specified set of mutexes */
        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
        M114 (Arg0)
        /* Wait for all Worker threads */

        M103 (Arg0)
        /* Check up the values of counters of all Mutexes */

        LPN0 = Arg5
        LPC0 = Arg4
        While (LPN0)
        {
            M333 (LPC0, 0x01, 0x01)
            LPN0--
            LPC0++
        }

        /* RELEASING */

        If (!Arg1)
        {
            /* === Thread 2 === */

            THR = 0x02
            /* Set up per-thread set of mutexes */

            M334 (Arg0, C300, Arg4, Arg5, 0x01, 0x01)
            M200 (BS00, Arg0, C102) /* cmd: Sleep */
            M208 (BS00, THR, C107)  /* cmd: Release specified set of mutexes */
            M114 (Arg0)
            /* Wait for all Worker threads */

            M103 (Arg0)
        }

        /* === Thread 1 === */

        THR = 0x01
        /* Set up per-thread set of mutexes */

        M334 (Arg0, C300, Arg2, Arg3, 0x00, 0x01)
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR, C107)  /* cmd: Release specified set of mutexes */
        M114 (Arg0)
        /* Wait for all Worker threads */

        M103 (Arg0)
        If (Arg1)
        {
            /* === Thread 2 === */

            THR = 0x02
            /* Set up per-thread set of mutexes */

            M334 (Arg0, C300, Arg4, Arg5, 0x01, 0x01)
            M200 (BS00, Arg0, C102) /* cmd: Sleep */
            M208 (BS00, THR, C107)  /* cmd: Release specified set of mutexes */
            M114 (Arg0)
            /* Wait for all Worker threads */

            M103 (Arg0)
        }
    }

    /*
     * arg0 - number of threads
     */
    Method (M804, 1, NotSerialized)
    {
        /* I */

        M8FF (Arg0, 0x00, 0x00, MAX0, 0x00, MAX0)
        /* Reset all counters (cnt0) and flags (fl00) corresponding to all Mutexes */

        M330 ()
        /* II */

        M8FF (Arg0, 0x01, 0x00, MAX0, 0x00, MAX0)
        /* Reset all counters (cnt0) and flags (fl00) corresponding to all Mutexes */

        M330 ()
        /* III */

        M8FF (Arg0, 0x01, 0x07, 0x01, 0x00, MAX0)
    }

    /*
     * arg0 - number of threads
     */
    Method (M805, 1, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (THR, 0x00)
        Name (EE01, Buffer (Arg0)
        {
             0x00, 0x3F, 0x00                                 // .?.
        }) /* AE_AML_NOT_OWNER */
        Name (EE02, Buffer (Arg0)
        {
             0x00, 0x00, 0x3F                                 // ..?
        }) /* AE_AML_NOT_OWNER */
        /* 1. Thread_1 owns its set of all-level mutexes and falls into sleeping */

        THR = 0x01
        /* Set up per-thread set of mutexes */

        M334 (Arg0, C300, 0x00, MAX0, 0x00, 0x01)
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR, C106)  /* cmd: Acquire specified set of mutexes */
        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
        M114 (Arg0)
        /* Wait for all Worker threads */

        M103 (Arg0)
        /* Check up the values of counters of all Mutexes */

        LPN0 = MAX0 /* \MAX0 */
        LPC0 = 0x00
        While (LPN0)
        {
            M333 (LPC0, 0x00, 0x01)
            LPN0--
            LPC0++
        }

        /* 2,3. Thread_2 tries to Release all those mutexes owned by Thread_1 */

        THR = 0x02
        /* Set up exception expectation on Release operation */

        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
        M20F (Arg0, EE02, 0x00)    /* Init the exceptional conditions flags (AE_AML_NOT_OWNER) */
        /* Set up per-thread set of mutexes */

        M334 (Arg0, C300, 0x00, MAX0, 0x00, 0x01)
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR, C107)  /* cmd: Release specified set of mutexes */
        M114 (Arg0)
        /* Wait for all Worker threads */

        M103 (Arg0)
        /* Reset exception expectation */

        M336 (Arg0, 0x01)
        /* 4. Thread_2 owns its set of all-level mutexes (not intersecting with Thread_1) */

        THR = 0x02
        /* Set up per-thread set of mutexes */

        M334 (Arg0, C300, 0x00, MAX0, 0x01, 0x01)
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR, C106)  /* cmd: Acquire specified set of mutexes */
        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
        M114 (Arg0)
        /* Wait for all Worker threads */

        M103 (Arg0)
        /* Check up the values of counters of all Mutexes */

        LPN0 = MAX0 /* \MAX0 */
        LPC0 = 0x00
        While (LPN0)
        {
            M333 (LPC0, 0x00, 0x01)
            LPN0--
            LPC0++
        }

        /* 5,6. Thread_2 tries again to Release mutexes owned by Thread_1 */

        THR = 0x02
        /* Set up exception expectation on Release operation */

        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
        M20F (Arg0, EE02, 0x00)    /* Init the exceptional conditions flags (AE_AML_NOT_OWNER) */
        /* Set up per-thread set of mutexes */

        M334 (Arg0, C300, 0x00, MAX0, 0x00, 0x01)
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR, C107)  /* cmd: Release specified set of mutexes */
        M114 (Arg0)
        /* Wait for all Worker threads */

        M103 (Arg0)
        /* Reset exception expectation */

        M336 (Arg0, 0x01)
        /* 7,8. Thread_1 tries to Release mutexes owned by Thread_2 */

        THR = 0x01
        /* Set up exception expectation on Release operation */

        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
        M20F (Arg0, EE01, 0x00)    /* Init the exceptional conditions flags (AE_AML_NOT_OWNER) */
        /* Set up per-thread set of mutexes */

        M334 (Arg0, C300, 0x00, MAX0, 0x01, 0x01)
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR, C107)  /* cmd: Release specified set of mutexes */
        M114 (Arg0)
        /* Wait for all Worker threads */

        M103 (Arg0)
        /* Reset exception expectation */

        M336 (Arg0, 0x01)
        /* 9. Thread_1 Releases its mutexes */

        THR = 0x01
        /* Set up per-thread set of mutexes */

        M334 (Arg0, C300, 0x00, MAX0, 0x00, 0x01)
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR, C107)  /* cmd: Release specified set of mutexes */
        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
        M114 (Arg0)
        /* Wait for all Worker threads */

        M103 (Arg0)
        /* 10. Thread_2 Releases its mutexes */

        THR = 0x02
        /* Set up per-thread set of mutexes */

        M334 (Arg0, C300, 0x00, MAX0, 0x01, 0x01)
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR, C107)  /* cmd: Release specified set of mutexes */
        M114 (Arg0)
        /* Wait for all Worker threads */

        M103 (Arg0)
    }

    /*
     * arg0 - number of threads (total)
     */
    Method (M806, 1, Serialized)
    {
        Name (NUMW, 0x00) /* number of threads in work */
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (NTH0, Buffer (0x02){})
        Name (IX00, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x00, 0x01, 0x01, 0x01, 0x02, 0x01,  // ........
            /* 0008 */  0x03, 0x01                                       // ..
        })
        /*
         * arg0-arg5 - same as m33f
         * arg6 - index of thread according to the test scenario
         */
        Method (M000, 7, Serialized)
        {
            Name (NTH1, 0x00) /* actually in work */
            NTH1 = DerefOf (Arg0 [0x01])
            If ((Arg6 < NTH1))
            {
                M33F (Arg0, Arg1, Arg2, Arg3, Arg4, Arg5, 0x00)
            }
        }

        /* Number of threads to be actually in work */

        NUMW = M213 (Arg0, MIN1, 0x04)
        /* Pack numbers of threads */

        NTH0 = M20D (Arg0, NUMW)
        /* Data */

        Name (B001, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x01,  // ........
            /* 0008 */  0x00, 0x01                                       // ..
        })
        Name (B002, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x01, 0x01, 0x00, 0x00, 0x01, 0x01,  // ........
            /* 0008 */  0x01, 0x01                                       // ..
        })
        Name (B003, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x02, 0x01, 0x02, 0x01, 0x00, 0x00,  // ........
            /* 0008 */  0x02, 0x01                                       // ..
        })
        Name (B004, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x03, 0x01, 0x03, 0x01, 0x03, 0x01,  // ........
            /* 0008 */  0x00, 0x00                                       // ..
        })
        Name (CM01, Package (MIN1)
        {
            0x00,
            C107,
            0x00,
            0x00,
            0x00
        })
        Name (EE01, Buffer (MIN1)
        {
             0x00, 0x3F, 0x00, 0x00, 0x00                     // .?...
        }) /* AE_AML_NOT_OWNER */
        Name (CM02, Package (MIN1)
        {
            0x00,
            0x00,
            C107,
            0x00,
            0x00
        })
        Name (EE02, Buffer (MIN1)
        {
             0x00, 0x00, 0x3F, 0x00, 0x00                     // ..?..
        }) /* AE_AML_NOT_OWNER */
        Name (CM03, Package (MIN1)
        {
            0x00,
            0x00,
            0x00,
            C107,
            0x00
        })
        Name (EE03, Buffer (MIN1)
        {
             0x00, 0x00, 0x00, 0x3F, 0x00                     // ...?.
        }) /* AE_AML_NOT_OWNER */
        Name (CM04, Package (MIN1)
        {
            0x00,
            0x00,
            0x00,
            0x00,
            C107
        })
        Name (EE04, Buffer (MIN1)
        {
             0x00, 0x00, 0x00, 0x00, 0x3F                     // ....?
        }) /* AE_AML_NOT_OWNER */
        /* Acquire */

        LPN0 = MAX0 /* \MAX0 */
        LPC0 = 0x00
        While (LPN0)
        {
            /* All threads Acquire their mutexes */

            M33F (NTH0, C106, 0x00, LPC0, IX00, C106, 0x00)    /* Expected hang statuses       (buffer/Integer) */
            /* 2. Threads thr-2, thr-3, thr-4 attempt to Release mutex of thr-1 */

            If ((NUMW > 0x01))
            {
                M000 (NTH0, CM02, EE02, LPC0, B001, CM02, 0x02)
                M000 (NTH0, CM03, EE03, LPC0, B001, CM03, 0x03)
                M000 (NTH0, CM04, EE04, LPC0, B001, CM04, 0x04)
            }

            /* 3. Threads thr-1, thr-3, thr-4 attempt to Release mutex of thr-2 */

            If ((NUMW > 0x02))
            {
                M000 (NTH0, CM01, EE01, LPC0, B002, CM01, 0x01)
                M000 (NTH0, CM03, EE03, LPC0, B002, CM03, 0x03)
                M000 (NTH0, CM04, EE04, LPC0, B002, CM04, 0x04)
            }

            /* 4. Threads thr-1, thr-2, thr-4 attempt to Release mutex of thr-3 */

            If ((NUMW > 0x03))
            {
                M000 (NTH0, CM01, EE01, LPC0, B003, CM01, 0x01)
                M000 (NTH0, CM02, EE02, LPC0, B003, CM02, 0x02)
                M000 (NTH0, CM04, EE04, LPC0, B003, CM04, 0x04)
            }

            /* 5. Threads thr-1, thr-2, thr-3 attempt to Release mutex of thr-4 */

            If ((NUMW > 0x04))
            {
                M000 (NTH0, CM01, EE01, LPC0, B004, CM01, 0x01)
                M000 (NTH0, CM02, EE02, LPC0, B004, CM02, 0x02)
                M000 (NTH0, CM03, EE03, LPC0, B004, CM03, 0x03)
            }

            /* All threads Release their mutexes */

            M33F (NTH0, C107, 0x00, LPC0, IX00, C107, 0x00)    /* Expected hang statuses       (buffer/Integer) */
            LPN0--
            LPC0++
        }
    }

    /*
     * arg0 - number of threads
     */
    Method (M807, 1, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (LPN1, 0x00)
        Name (LPC1, 0x00)
        Name (IX00, 0x00)
        Name (NUMW, 0x00) /* number of threads in work */
        /* Number of threads to be actually in work */

        NUMW = M213 (Arg0, MIN1, 0x03)
        /* From 15 to 0 */

        LPN0 = MAX0 /* \MAX0 */
        IX00 = MAX0 /* \MAX0 */
        IX00--
        LPC0 = IX00 /* \M807.IX00 */
        While (LPN0)
        {
            If ((LPC0 != 0x00))
            {
                /*
                 * 3. Acquire mutexes from 0 to (N-1) levels:
                 *	- Set up per-thread set of mutexes
                 *	- Acquire specified set of mutexes
                 *	- Wait for all Worker threads
                 *	- Check up the values of counters of all Mutexes
                 */
                M337 (Arg0, NUMW, 0x00, LPC0, 0x01, 0x00)
                /*
                 * 4. Release mutexes from 0 to (N-1) levels:
                 *	- Set up per-thread set of mutexes
                 *	- Release specified set of mutexes
                 *	- Wait for all Worker threads
                 */
                M338 (Arg0, NUMW, 0x00, LPC0)
                /* Reset all counters (cnt0) and flags (fl00) corresponding to all Mutexes */

                M330 ()
            }

            /* 5. Acquire mutex of level N */

            M337 (Arg0, NUMW, LPC0, 0x01, 0x01, 0x00)
            If ((LPC0 != 0x00))
            {
                /*
                 * 6. Attempt to Acquire mutexes from 0 to (N-1) levels
                 * 7. Exception is expected
                 */
                M337 (Arg0, NUMW, 0x00, LPC0, 0x00, 0x40) /* With exceptional conditions flags (AE_AML_MUTEX_ORDER) */
                /* Reset exception expectation */

                M336 (Arg0, 0x01)
            }

            If ((LPC0 != IX00))
            {
                /*
                 * 8. Acquire mutexes from (N+1) to 15 levels
                 *	- Set up per-thread set of mutexes
                 *	- Acquire specified set of mutexes
                 *	- Wait for all Worker threads
                 *	- Check up the values of counters of all Mutexes
                 */
                Local0 = (LPC0 + 0x01)
                Local1 = (IX00 - LPC0) /* \M807.LPC0 */
                M337 (Arg0, NUMW, Local0, Local1, 0x01, 0x00)
            }

            /*
             * 9. Release all mutexes (starting with lpC0 up to 15 level):
             *	- Set up per-thread set of mutexes
             *	- Release specified set of mutexes
             *	- Wait for all Worker threads
             */
            Local1 = (MAX0 - LPC0) /* \M807.LPC0 */
            M338 (Arg0, NUMW, LPC0, Local1)
            /* Reset all counters (cnt0) and flags (fl00) corresponding to all Mutexes */

            M330 ()
            If ((LPC0 != 0x00))
            {
                /*
                 * 10. Acquire mutexes from 0 to (N-1) levels:
                 *	- Set up per-thread set of mutexes
                 *	- Acquire specified set of mutexes
                 *	- Wait for all Worker threads
                 *	- Check up the values of counters of all Mutexes
                 */
                M337 (Arg0, NUMW, 0x00, LPC0, 0x01, 0x00)
                /*
                 * 11. Release mutexes (from 0 to (N-1) levels):
                 *	- Set up per-thread set of mutexes
                 *	- Release specified set of mutexes
                 *	- Wait for all Worker threads
                 */
                M338 (Arg0, NUMW, 0x00, LPC0)
                /* Reset all counters (cnt0) and flags (fl00) corresponding to all Mutexes */

                M330 ()
            }

            LPN0--
            LPC0--
        }
    }

    /*
     * arg0 - number of threads (total)
     */
    Method (M808, 1, Serialized)
    {
        Name (PR, 0x00)
        Name (L000, 0x00)
        Name (NTH0, Buffer (0x02){})
        /*
         * Per-thread indexes of mutexes
         *
         * Ctl-thr,   thr-1, thr-2, thr-3, thr-4
         */
        Name (B000, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x00, 0x01, 0x01, 0x01, 0x02, 0x01,  // ........
            /* 0008 */  0x03, 0x01                                       // ..
        })
        Name (B001, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x01, 0x01, 0x02, 0x01, 0x03, 0x01,  // ........
            /* 0008 */  0x00, 0x01                                       // ..
        })
        Name (B002, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x02, 0x01, 0x03, 0x01, 0x00, 0x01,  // ........
            /* 0008 */  0x01, 0x01                                       // ..
        })
        Name (B003, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x03, 0x01, 0x00, 0x01, 0x01, 0x01,  // ........
            /* 0008 */  0x02, 0x01                                       // ..
        })
        /* Pack numbers of threads */

        NTH0 = M20D (Arg0, MIN1)
        /* x-0-123 */
        /*
         * Acquire all x-0-123 and check owning
         *
         * Threads thr-1, thr-2, thr-3, thr-4
         * acquire respectively all x-0-123 mutexes
         * and check owning of all those mutexes.
         */
        M33F (NTH0, C106, 0x00, L000, B000, C106, 0x00)    /* Expected hang statuses       (buffer/Integer) */
        If (PR)
        {
            M20B (0x00, "Acquire all x-0-123")
        }

        /* At this point threads have Acquired: x-0-123 */

        M8FE (NTH0, L000, B000, B001, PR)
        M8FE (NTH0, L000, B001, B002, PR)
        M8FE (NTH0, L000, B002, B003, PR)
        M8FE (NTH0, L000, B003, B000, PR)
        /* At this point threads have Acquired: x-0-123 */
        /* Release mutexes on all threads */
        Name (CM00, Package (MIN1)
        {
            0x00,
            C107,
            C107,
            C107,
            C107
        })
        Name (CP00, Package (MIN1)
        {
            0x00,
            C107,
            C107,
            C107,
            C107
        })
        M33F (NTH0, CM00, 0x00, L000, B000, CP00, 0x00)    /* Expected hang statuses       (buffer/Integer) */
        If (PR)
        {
            M20B (0x00, "Release all")
        }
    }

    /*
     * Manage the test m808
     *
     * agr0 - numbers of threads (buffer/Integer)
     * arg1 - levels of mutexes  (buffer/Integer)
     * arg2 - indexes of mutexes (buffer/Integer) - start point
     * arg3 - indexes of mutexes (buffer/Integer) - target point
     * arg4 - printing flag
     */
    Method (M8FE, 5, Serialized)
    {
        /*
         * Comments are for one particular transfer step from
         * x-0-123 to x-1-230, other steps are identical.
         */
        /* At this point threads have Acquired: x-0-123 */
        /* x-1-230 */
        /* Acquire x-x-230 and check that all -230- hang */
        Name (CM00, Package (MIN1)
        {
            0x00,
            0x00,
            C106,
            C106,
            C106
        })
        M33F (Arg0, CM00, 0x00, Arg1, Arg3, 0x00, CM00) /* Expected hang statuses       (buffer/Integer) */
        If (Arg4)
        {
            M20B (0x00, "Acquire x-x-230")
        }

        /* Release x-0-xxx, this frees mux for thr-4 */

        Name (CM01, Package (MIN1)
        {
            0x00,
            C107,
            0x00,
            0x00,
            0x00
        })
        Name (CP01, Package (MIN1)
        {
            0x00,
            C107,
            0x00,
            0x00,
            C106
        })
        Name (HG01, Package (MIN1)
        {
            0x00,
            0x00,
            C106,
            C106,
            0x00
        })
        M33F (Arg0, CM01, 0x00, Arg1, Arg2, CP01, HG01) /* Expected hang statuses       (buffer/Integer) */
        If (Arg4)
        {
            M20B (0x00, "Release x-0-xxx")
        }

        /* Acquire x-1-xxx and check that it hangs too */

        Name (CM02, Package (MIN1)
        {
            0x00,
            C106,
            0x00,
            0x00,
            0x00
        })
        Name (HG02, Package (MIN1)
        {
            0x00,
            C106,
            C106,
            C106,
            0x00
        })
        M33F (Arg0, CM02, 0x00, Arg1, Arg3, 0x00, HG02) /* Expected hang statuses       (buffer/Integer) */
        If (Arg4)
        {
            M20B (0x00, "Acquire x-1-xxx")
        }

        /* Release x-x-xx3, this frees mux for thr-3 */

        Name (CM03, Package (MIN1)
        {
            0x00,
            0x00,
            0x00,
            0x00,
            C107
        })
        Name (CP03, Package (MIN1)
        {
            0x00,
            0x00,
            0x00,
            C106,
            C107
        })
        Name (HG03, Package (MIN1)
        {
            0x00,
            C106,
            C106,
            0x00,
            0x00
        })
        M33F (Arg0, CM03, 0x00, Arg1, Arg2, CP03, HG03) /* Expected hang statuses       (buffer/Integer) */
        If (Arg4)
        {
            M20B (0x00, "Release x-x-xx3")
        }

        /* Release x-x-x2x, this frees mux for thr-2 */

        Name (CM04, Package (MIN1)
        {
            0x00,
            0x00,
            0x00,
            C107,
            0x00
        })
        Name (CP04, Package (MIN1)
        {
            0x00,
            0x00,
            C106,
            C107,
            0x00
        })
        Name (HG04, Package (MIN1)
        {
            0x00,
            C106,
            0x00,
            0x00,
            0x00
        })
        M33F (Arg0, CM04, 0x00, Arg1, Arg2, CP04, HG04) /* Expected hang statuses       (buffer/Integer) */
        If (Arg4)
        {
            M20B (0x00, "Release x-x-x2x")
        }

        /* Release x-x-1xx, this frees mux for thr-1 */

        Name (CM05, Package (MIN1)
        {
            0x00,
            0x00,
            C107,
            0x00,
            0x00
        })
        Name (CP05, Package (MIN1)
        {
            0x00,
            C106,
            C107,
            0x00,
            0x00
        })
        M33F (Arg0, CM05, 0x00, Arg1, Arg2, CP05, 0x00)    /* Expected hang statuses       (buffer/Integer) */
        If (Arg4)
        {
            M20B (0x00, "Release x-x-1xx")
        }
        /* At this point threads have Acquired: x-1-230 */
    }

    /*
     * arg0 - number of threads (total)
     */
    Method (M809, 1, NotSerialized)
    {
        M80C (Arg0, 0x01)
    }

    /*
     * arg0 - number of threads (total)
     * arg1 - variant (of parameters passed to m8fd):
     *        0:
     *           arg1 - indexes of mutexes (buffer/Integer)
     *           arg2 - levels of mutexes  (buffer/Integer) - start point
     *           arg3 - levels of mutexes  (buffer/Integer) - target point
     *        1:
     *           arg1 - levels of mutexes  (buffer/Integer)
     *           arg2 - indexes of mutexes (buffer/Integer) - start point
     *           arg3 - indexes of mutexes (buffer/Integer) - target point
     */
    Method (M80C, 2, Serialized)
    {
        Name (PR, 0x00)
        Name (IXLL, 0x00)
        Name (NTH0, Buffer (0x02){})
        /*
         * Per-thread indexes/levels (depending on arg1) of mutexes
         *
         * Ctl-thr,   thr-1, thr-2, thr-3, thr-4
         */
        Name (B000, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x00, 0x01, 0x01, 0x01, 0x02, 0x01,  // ........
            /* 0008 */  0x03, 0x01                                       // ..
        })
        Name (B001, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x01, 0x01, 0x02, 0x01, 0x03, 0x01,  // ........
            /* 0008 */  0x04, 0x01                                       // ..
        })
        Name (B002, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x02, 0x01, 0x03, 0x01, 0x04, 0x01,  // ........
            /* 0008 */  0x05, 0x01                                       // ..
        })
        Name (B003, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x03, 0x01, 0x04, 0x01, 0x05, 0x01,  // ........
            /* 0008 */  0x06, 0x01                                       // ..
        })
        Name (B004, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x04, 0x01, 0x05, 0x01, 0x06, 0x01,  // ........
            /* 0008 */  0x07, 0x01                                       // ..
        })
        Name (B005, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x05, 0x01, 0x06, 0x01, 0x07, 0x01,  // ........
            /* 0008 */  0x08, 0x01                                       // ..
        })
        Name (B006, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x06, 0x01, 0x07, 0x01, 0x08, 0x01,  // ........
            /* 0008 */  0x09, 0x01                                       // ..
        })
        Name (B007, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x07, 0x01, 0x08, 0x01, 0x09, 0x01,  // ........
            /* 0008 */  0x0A, 0x01                                       // ..
        })
        Name (B008, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x08, 0x01, 0x09, 0x01, 0x0A, 0x01,  // ........
            /* 0008 */  0x0B, 0x01                                       // ..
        })
        Name (B009, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x09, 0x01, 0x0A, 0x01, 0x0B, 0x01,  // ........
            /* 0008 */  0x0C, 0x01                                       // ..
        })
        Name (B00A, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x0A, 0x01, 0x0B, 0x01, 0x0C, 0x01,  // ........
            /* 0008 */  0x0D, 0x01                                       // ..
        })
        Name (B00B, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x0B, 0x01, 0x0C, 0x01, 0x0D, 0x01,  // ........
            /* 0008 */  0x0E, 0x01                                       // ..
        })
        Name (B00C, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x0C, 0x01, 0x0D, 0x01, 0x0E, 0x01,  // ........
            /* 0008 */  0x0F, 0x01                                       // ..
        })
        If (Arg1)
        {
            /* The same level of mutexes */

            IXLL = 0x00
        }
        Else
        {
            /* The same index of mutexes */

            IXLL = 0x00
        }

        /* Pack numbers of threads */

        NTH0 = M20D (Arg0, MIN1)
        /* x-0123 */
        /*
         * x-0-1-2-3
         * Acquire all x-0123 and check owning
         *
         * Threads thr-1, thr-2, thr-3, thr-4
         * acquire respectively all x-0123 mutexes
         * and check owning of all those mutexes.
         */
        If (Arg1)
        {
            Local6 = IXLL /* \M80C.IXLL */
            Local7 = B000 /* \M80C.B000 */
        }
        Else
        {
            Local6 = B000 /* \M80C.B000 */
            Local7 = IXLL /* \M80C.IXLL */
        }

        M33F (NTH0, C106, 0x00, Local6, Local7, C106, 0x00)      /* Expected hang statuses       (buffer/Integer) */
        If (PR)
        {
            M20B (0x00, "Acquire all x-0123")
        }

        M8FD (NTH0, IXLL, B000, B001, PR, Arg1)
        M8FD (NTH0, IXLL, B001, B002, PR, Arg1)
        M8FD (NTH0, IXLL, B002, B003, PR, Arg1)
        M8FD (NTH0, IXLL, B003, B004, PR, Arg1)
        M8FD (NTH0, IXLL, B004, B005, PR, Arg1)
        M8FD (NTH0, IXLL, B005, B006, PR, Arg1)
        M8FD (NTH0, IXLL, B006, B007, PR, Arg1)
        M8FD (NTH0, IXLL, B007, B008, PR, Arg1)
        M8FD (NTH0, IXLL, B008, B009, PR, Arg1)
        M8FD (NTH0, IXLL, B009, B00A, PR, Arg1)
        M8FD (NTH0, IXLL, B00A, B00B, PR, Arg1)
        M8FD (NTH0, IXLL, B00B, B00C, PR, Arg1)
        /* x-(12)-(13)-(14)-(15), Release=x-(12)(13)(14)(15), hang=x-xxxx, success=x-(12)(13)(14)(15) */

        If (Arg1)
        {
            Local6 = IXLL /* \M80C.IXLL */
            Local7 = B00C /* \M80C.B00C */
        }
        Else
        {
            Local6 = B00C /* \M80C.B00C */
            Local7 = IXLL /* \M80C.IXLL */
        }

        M33F (NTH0, C107, 0x00, Local6, Local7, C107, 0x00)    /* Expected hang statuses       (buffer/Integer) */
        If (PR)
        {
            M20B (0x00, "Release x-(12)(13)(14)(15)")
        }
    }

    /*
     * arg0 - numbers of threads (buffer/Integer)
     * arg1 - indexes/levels of mutexes (buffer/Integer)
     * arg2 - levels/indexes of mutexes (buffer/Integer) - start point
     * arg3 - levels/indexes of mutexes (buffer/Integer) - target point
     * arg4 - printing flag
     * arg5 - variant (see m80c)
     */
    Method (M8FD, 6, Serialized)
    {
        /* At this point threads have Acquired: x-0123 */
        /*
         * Comments are given for one particular transfer step
         * from x-0-123 to x-1-230, other steps are identical.
         */
        /* x-01-12-23-34, Acquire=x-1234, hang=x-123x, success=x-xxx4 */
        Name (CM00, Package (MIN1)
        {
            0x00,
            C106,
            C106,
            C106,
            C106
        })
        Name (CP00, Package (MIN1)
        {
            0x00,
            0x00,
            0x00,
            0x00,
            C106
        })
        Name (HG00, Package (MIN1)
        {
            0x00,
            C106,
            C106,
            C106,
            0x00
        })
        If (Arg5)
        {
            Local6 = Arg1
            Local7 = Arg3
        }
        Else
        {
            Local6 = Arg3
            Local7 = Arg1
        }

        M33F (Arg0, CM00, 0x00, Local6, Local7, CP00, HG00)   /* Expected hang statuses       (buffer/Integer) */
        If (Arg4)
        {
            M20B (0x00, "Acquire x-1234")
        }

        /* x-01-12-23-3, Release=x-xxx4, hang=x-123x, success=x-xxx4 */

        Name (CM01, Package (MIN1)
        {
            0x00,
            0x00,
            0x00,
            0x00,
            C107
        })
        Name (CP01, Package (MIN1)
        {
            0x00,
            0x00,
            0x00,
            0x00,
            C107
        })
        Name (HG01, Package (MIN1)
        {
            0x00,
            C106,
            C106,
            C106,
            0x00
        })
        If (Arg5)
        {
            Local6 = Arg1
            Local7 = Arg3
        }
        Else
        {
            Local6 = Arg3
            Local7 = Arg1
        }

        M33F (Arg0, CM01, 0x00, Local6, Local7, CP01, HG01)   /* Expected hang statuses       (buffer/Integer) */
        If (Arg4)
        {
            M20B (0x00, "Release x-xxx4")
        }

        /* x-01-12-23-x, Release=x-xxx3, hang=x-12xx, success=x-xx33 */

        Name (CM02, Package (MIN1)
        {
            0x00,
            0x00,
            0x00,
            0x00,
            C107
        })
        Name (CP02, Package (MIN1)
        {
            0x00,
            0x00,
            0x00,
            C106,
            C107
        })
        Name (HG02, Package (MIN1)
        {
            0x00,
            C106,
            C106,
            0x00,
            0x00
        })
        If (Arg5)
        {
            Local6 = Arg1
            Local7 = Arg2
        }
        Else
        {
            Local6 = Arg2
            Local7 = Arg1
        }

        M33F (Arg0, CM02, 0x00, Local6, Local7, CP02, HG02)   /* Expected hang statuses       (buffer/Integer) */
        If (Arg4)
        {
            M20B (0x00, "Release x-xxx3")
        }

        /* x-01-12-23-4, Acquire=x-xxx4, hang=x-12xx, success=x-xxx4 */

        Name (CM03, Package (MIN1)
        {
            0x00,
            0x00,
            0x00,
            0x00,
            C106
        })
        Name (CP03, Package (MIN1)
        {
            0x00,
            0x00,
            0x00,
            0x00,
            C106
        })
        Name (HG03, Package (MIN1)
        {
            0x00,
            C106,
            C106,
            0x00,
            0x00
        })
        If (Arg5)
        {
            Local6 = Arg1
            Local7 = Arg3
        }
        Else
        {
            Local6 = Arg3
            Local7 = Arg1
        }

        M33F (Arg0, CM03, 0x00, Local6, Local7, CP03, HG03)   /* Expected hang statuses       (buffer/Integer) */
        If (Arg4)
        {
            M20B (0x00, "Acquire x-xxx4")
        }

        /* x-01-12-2-4, Release=x-xx3x, hang=x-12xx, success=x-xx3x */

        Name (CM05, Package (MIN1)
        {
            0x00,
            0x00,
            0x00,
            C107,
            0x00
        })
        Name (CP05, Package (MIN1)
        {
            0x00,
            0x00,
            0x00,
            C107,
            0x00
        })
        Name (HG05, Package (MIN1)
        {
            0x00,
            C106,
            C106,
            0x00,
            0x00
        })
        If (Arg5)
        {
            Local6 = Arg1
            Local7 = Arg3
        }
        Else
        {
            Local6 = Arg3
            Local7 = Arg1
        }

        M33F (Arg0, CM05, 0x00, Local6, Local7, CP05, HG05)   /* Expected hang statuses       (buffer/Integer) */
        If (Arg4)
        {
            M20B (0x00, "Release x-xx3x")
        }

        /* x-01-12-x-4, Release=x-xx2x, hang=x-1xxx, success=x-x22x */

        Name (CM06, Package (MIN1)
        {
            0x00,
            0x00,
            0x00,
            C107,
            0x00
        })
        Name (CP06, Package (MIN1)
        {
            0x00,
            0x00,
            C106,
            C107,
            0x00
        })
        Name (HG06, Package (MIN1)
        {
            0x00,
            C106,
            0x00,
            0x00,
            0x00
        })
        If (Arg5)
        {
            Local6 = Arg1
            Local7 = Arg2
        }
        Else
        {
            Local6 = Arg2
            Local7 = Arg1
        }

        M33F (Arg0, CM06, 0x00, Local6, Local7, CP06, HG06)   /* Expected hang statuses       (buffer/Integer) */
        If (Arg4)
        {
            M20B (0x00, "Release x-xx2x")
        }

        /* x-01-12-3-4, Acquire=x-xx3x, hang=x-1xxx, success=x-xx3x */

        Name (CM07, Package (MIN1)
        {
            0x00,
            0x00,
            0x00,
            C106,
            0x00
        })
        Name (CP07, Package (MIN1)
        {
            0x00,
            0x00,
            0x00,
            C106,
            0x00
        })
        Name (HG07, Package (MIN1)
        {
            0x00,
            C106,
            0x00,
            0x00,
            0x00
        })
        If (Arg5)
        {
            Local6 = Arg1
            Local7 = Arg3
        }
        Else
        {
            Local6 = Arg3
            Local7 = Arg1
        }

        M33F (Arg0, CM07, 0x00, Local6, Local7, CP07, HG07)   /* Expected hang statuses       (buffer/Integer) */
        If (Arg4)
        {
            M20B (0x00, "Acquire x-xx3x")
        }

        /* x-01-1-3-4, Release=x-x2xx, hang=x-1xxx, success=x-x2xx */

        Name (CM08, Package (MIN1)
        {
            0x00,
            0x00,
            C107,
            0x00,
            0x00
        })
        Name (CP08, Package (MIN1)
        {
            0x00,
            0x00,
            C107,
            0x00,
            0x00
        })
        Name (HG08, Package (MIN1)
        {
            0x00,
            C106,
            0x00,
            0x00,
            0x00
        })
        If (Arg5)
        {
            Local6 = Arg1
            Local7 = Arg3
        }
        Else
        {
            Local6 = Arg3
            Local7 = Arg1
        }

        M33F (Arg0, CM08, 0x00, Local6, Local7, CP08, HG08)   /* Expected hang statuses       (buffer/Integer) */
        If (Arg4)
        {
            M20B (0x00, "Release x-x2xx")
        }

        /* x-01-x-3-4, Release=x-x1xx, hang=x-xxxx, success=x-11xx */

        Name (CM09, Package (MIN1)
        {
            0x00,
            0x00,
            C107,
            0x00,
            0x00
        })
        Name (CP09, Package (MIN1)
        {
            0x00,
            C106,
            C107,
            0x00,
            0x00
        })
        If (Arg5)
        {
            Local6 = Arg1
            Local7 = Arg2
        }
        Else
        {
            Local6 = Arg2
            Local7 = Arg1
        }

        M33F (Arg0, CM09, 0x00, Local6, Local7, CP09, 0x00)      /* Expected hang statuses       (buffer/Integer) */
        If (Arg4)
        {
            M20B (0x00, "Release x-x1xx")
        }

        /* x-01-2-3-4, Acquire=x-x2xx, hang=x-xxxx, success=x-x2xx */

        Name (CM0A, Package (MIN1)
        {
            0x00,
            0x00,
            C106,
            0x00,
            0x00
        })
        Name (CP0A, Package (MIN1)
        {
            0x00,
            0x00,
            C106,
            0x00,
            0x00
        })
        If (Arg5)
        {
            Local6 = Arg1
            Local7 = Arg3
        }
        Else
        {
            Local6 = Arg3
            Local7 = Arg1
        }

        M33F (Arg0, CM0A, 0x00, Local6, Local7, CP0A, 0x00)      /* Expected hang statuses       (buffer/Integer) */
        If (Arg4)
        {
            M20B (0x00, "Acquire x-x2xx")
        }

        /* x-0-2-3-4, Release=x-1xxx, hang=x-xxxx, success=x-1xxx */

        Name (CM0B, Package (MIN1)
        {
            0x00,
            C107,
            0x00,
            0x00,
            0x00
        })
        Name (CP0B, Package (MIN1)
        {
            0x00,
            C107,
            0x00,
            0x00,
            0x00
        })
        If (Arg5)
        {
            Local6 = Arg1
            Local7 = Arg3
        }
        Else
        {
            Local6 = Arg3
            Local7 = Arg1
        }

        M33F (Arg0, CM0B, 0x00, Local6, Local7, CP0B, 0x00)      /* Expected hang statuses       (buffer/Integer) */
        If (Arg4)
        {
            M20B (0x00, "Release x-1xxx")
        }

        /* x-x-2-3-4, Release=x-0xxx, hang=x-xxxx, success=x-0xxx */

        Name (CM0C, Package (MIN1)
        {
            0x00,
            C107,
            0x00,
            0x00,
            0x00
        })
        Name (CP0C, Package (MIN1)
        {
            0x00,
            C107,
            0x00,
            0x00,
            0x00
        })
        If (Arg5)
        {
            Local6 = Arg1
            Local7 = Arg2
        }
        Else
        {
            Local6 = Arg2
            Local7 = Arg1
        }

        M33F (Arg0, CM0C, 0x00, Local6, Local7, CP0C, 0x00)      /* Expected hang statuses       (buffer/Integer) */
        If (Arg4)
        {
            M20B (0x00, "Release x-0xxx")
        }

        /* x-1-2-3-4, Acquire=x-1xxx, hang=x-xxxx, success=x-1xxx */

        Name (CM0D, Package (MIN1)
        {
            0x00,
            C106,
            0x00,
            0x00,
            0x00
        })
        Name (CP0D, Package (MIN1)
        {
            0x00,
            C106,
            0x00,
            0x00,
            0x00
        })
        If (Arg5)
        {
            Local6 = Arg1
            Local7 = Arg3
        }
        Else
        {
            Local6 = Arg3
            Local7 = Arg1
        }

        M33F (Arg0, CM0D, 0x00, Local6, Local7, CP0D, 0x00)      /* Expected hang statuses       (buffer/Integer) */
        If (Arg4)
        {
            M20B (0x00, "Acquire x-1xxx")
        }
        /* At this point threads have Acquired: x-1234 */
    }

    /*
     * arg0 - number of threads (total)
     */
    Method (M810, 1, NotSerialized)
    {
        M80C (Arg0, 0x00)
    }

    /*
     * arg0 - number of threads (total)
     */
    Method (M811, 1, Serialized)
    {
        Name (RPT, 0x04)
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Name (LPN1, 0x00)
        Name (LPC1, 0x00)
        Name (NTH0, Buffer (0x02){})
        Name (IX00, Buffer ((MIN1 * 0x02))
        {
            /* 0000 */  0x00, 0x00, 0x00, 0x01, 0x01, 0x01, 0x02, 0x01,  // ........
            /* 0008 */  0x03, 0x01                                       // ..
        })
        Name (NUMW, 0x00) /* number of threads in work */
        /* Number of threads to be actually in work */

        NUMW = M213 (Arg0, MIN1, 0x04)
        /* Pack numbers of threads */

        NTH0 = M20D (Arg0, NUMW)
        /* Each thread Acquires successfully its mutex N times */

        LPN0 = MAX0 /* \MAX0 */
        LPC0 = 0x00
        While (LPN0)
        {
            LPN1 = RPT /* \M811.RPT_ */
            LPC1 = 0x00
            /* Repetition */

            While (LPN1)
            {
                M33F (NTH0, C106, 0x00, LPC0, IX00, C106, 0x00)    /* Expected hang statuses       (buffer/Integer) */
                LPN1--
                LPC1++
            }

            LPN0--
            LPC0++
        }

        /* Each thread Releases successfully its mutex N times */

        LPN0 = MAX0 /* \MAX0 */
        LPC0 = (MAX0 - 0x01)
        While (LPN0)
        {
            LPN1 = RPT /* \M811.RPT_ */
            LPC1 = 0x00
            /* Repetition */

            While (LPN1)
            {
                M33F (NTH0, C107, 0x00, LPC0, IX00, C107, 0x00)    /* Expected hang statuses       (buffer/Integer) */
                LPN1--
                LPC1++
            }

            LPN0--
            LPC0--
        }

        /*
         * Each thread gets exception AE_AML_MUTEX_NOT_ACQUIRED (65)
         * on additional Release.
         */
        LPN0 = MAX0 /* \MAX0 */
        LPC0 = (MAX0 - 0x01)
        While (LPN0)
        {
            M33F (NTH0, C107, 0x41, LPC0, IX00, C107, 0x00)    /* Expected hang statuses       (buffer/Integer) */
            LPN0--
            LPC0--
        }
    }

    /*
     * arg0 - number of threads (total)
     */
    Method (M812, 1, Serialized)
    {
        Name (RPT, 0x03)  /* number of repetition */
        Name (LPN0, 0x00) /* level */
        Name (LPC0, 0x00)
        Name (LPN1, 0x00) /* index-thread */
        Name (LPC1, 0x00)
        Name (INDT, 0x00) /* index of thread */
        Name (LPN2, 0x00) /* repetition */
        Name (LPC2, 0x00)
        Name (LLS0, 0x00)
        Name (NUM2, 0x00)
        Name (IXSZ, 0x00)
        Name (NUMW, 0x00) /* number of threads in work */
        Store ((MIN1 * 0x02), IXSZ) /* \M812.IXSZ */
        Name (NTH0, Buffer (0x02){})
        /* Buffers of indexes of mutexes */

        Name (PIXS, Package (MIN1)
        {
            0x00,
            Buffer (IXSZ)
            {
                /* 0000 */  0x00, 0x00, 0x00, 0x01, 0x00, 0x01, 0x00, 0x01,  // ........
                /* 0008 */  0x00, 0x01                                       // ..
            },

            Buffer (IXSZ)
            {
                /* 0000 */  0x00, 0x00, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
                /* 0008 */  0x01, 0x01                                       // ..
            },

            Buffer (IXSZ)
            {
                /* 0000 */  0x00, 0x00, 0x02, 0x01, 0x02, 0x01, 0x02, 0x01,  // ........
                /* 0008 */  0x02, 0x01                                       // ..
            },

            Buffer (IXSZ)
            {
                /* 0000 */  0x00, 0x00, 0x03, 0x01, 0x03, 0x01, 0x03, 0x01,  // ........
                /* 0008 */  0x03, 0x01                                       // ..
            }
        })
        Name (BIXS, Buffer (IXSZ){})
        Name (CM00, Buffer (MIN1){})
        Name (CP00, Buffer (MIN1){})
        Name (HG00, Buffer (MIN1){})
        /*
         * Determine num - number of threads actually in work
         *
         * Note: maximum for num is min1 here but it can be diminished
         * to reduce the time of execution.
         */
        NUMW = M213 (Arg0, MIN1, 0x03)
        NUM2 = (NUMW - 0x01) /* except the control thread */
        /* Pack numbers of threads */

        NTH0 = M20D (Arg0, NUMW)
        /*
         * Determine lls0 - number of levels to be in work
         *
         * Note: maximum for lls0 is max0 here but it can be diminished
         * to reduce the time of execution.
         */
        If (REDM)
        {
            LLS0 = 0x03
        }
        Else
        {
            LLS0 = MAX0 /* \MAX0 */
        }

        /* 9. Do 1-8 for all Levels of mutex one by one */

        LPN0 = LLS0 /* \M812.LLS0 */
        LPC0 = 0x00
        While (LPN0)
        {
            /*
             * 8. Do 1-7 for all threads one by one (so, for 0-3 Indexes of mutex as well)
             */
            LPN1 = NUM2 /* \M812.NUM2 */
            LPC1 = 0x00
            While (LPN1)
            {
                INDT = (LPC1 + 0x01)
                BIXS = DerefOf (PIXS [INDT])
                /* 1. Thread thr-i Acquires successfully mutex M0 of (i-1)-th index for N times */
                /* c106 for indt-th thread */
                M210 (CM00, NUMW, C106, INDT, 0x01, 0x01, 0x00)
                /* Repetition */

                LPN2 = RPT /* \M812.RPT_ */
                LPC2 = 0x00
                While (LPN2)
                {
                    M33F (NTH0, CM00, 0x00, LPC0, BIXS, CM00, 0x00)    /* Expected hang statuses       (buffer/Integer) */
                    LPN2--
                    LPC2++
                }

                /* 2. Other threads Acquire M0 too and hang */
                /*
                 * c103 for all except indt-th thread
                 * (and except 0-th thread naturally,
                 * not mentioned more below)
                 */
                M200 (CM00, NUMW, C103)
                M208 (CM00, INDT, 0x00)
                M33F (NTH0, CM00, 0x00, LPC0, BIXS, 0x00, CM00)
                /* 3. Thread thr-i Acquires successfully mutex M0 for N times again */
                /* c106 for indt-th thread */
                M210 (CM00, NUMW, C106, INDT, 0x01, 0x01, 0x00)
                /* c103 for all except indt-th thread */

                M200 (HG00, NUMW, C103)
                M208 (HG00, INDT, 0x00)
                /* Repetition */

                LPN2 = RPT /* \M812.RPT_ */
                LPC2 = 0x00
                While (LPN2)
                {
                    M33F (NTH0, CM00, 0x00, LPC0, BIXS, CM00, HG00)
                    LPN2--
                    LPC2++
                }

                /* 4. Thread thr-i Releases mutex M0 for 2*N times */
                /* c107 for indt-th thread */
                M210 (CM00, NUMW, C107, INDT, 0x01, 0x01, 0x00)
                /* c103 for all except indt-th thread */

                M200 (HG00, NUMW, C103)
                M208 (HG00, INDT, 0x00)
                /* Repetition */

                LPN2 = (RPT * 0x02)
                LPN2--
                LPC2 = 0x00
                While (LPN2)
                {
                    M33F (NTH0, CM00, 0x00, LPC0, BIXS, CM00, HG00)
                    LPN2--
                    LPC2++
                }

                /*
                 * 5. One of other threads (thr-j) owns M0
                 * 6. Thread thr-j Release M0
                 * 7. Do 5-6 items for all 'other' threads
                 */
                /* c107 for indt-th thread */
                M210 (CM00, NUMW, C107, INDT, 0x01, 0x01, 0x00)
                /* c103 for all except indt-th thread, and c107 for indt-th thread */

                M200 (CP00, NUMW, C103)
                M208 (CP00, INDT, C107)
                M33F (NTH0, CM00, 0x00, LPC0, BIXS, CP00, 0x00)
                LPN1--
                LPC1++
            }

            LPN0--
            LPC0++
        }
    }

    /*
     * arg0 - number of threads (total)
     */
    Method (M813, 1, Serialized)
    {
        Name (RPT, 0x0100) /* number of repetition */
        Name (LPN0, 0x00) /* level */
        Name (LPC0, 0x00)
        Name (LPN1, 0x00) /* index-thread */
        Name (LPC1, 0x00)
        Name (INDT, 0x00) /* index of thread */
        Name (LPN2, 0x00) /* repetition */
        Name (LPC2, 0x00)
        Name (LLS0, 0x00) /* number of levels */
        Name (NUM2, 0x00)
        Name (IXSZ, 0x00)
        Name (NUMW, 0x00) /* number of threads in work */
        Store ((MIN1 * 0x02), IXSZ) /* \M813.IXSZ */
        Name (NTH0, Buffer (0x02){})
        /* Buffer of per-thread indexes of mutexes */

        Name (IX00, Buffer (IXSZ)
        {
            /* 0000 */  0x00, 0x00, 0x00, 0x01, 0x01, 0x01, 0x02, 0x01,  // ........
            /* 0008 */  0x03, 0x01                                       // ..
        })
        Name (CM00, Buffer (MIN1){})
        /*
         * Determine num - number of threads actually in work
         * See input control on arg0 (before m813)
         *
         * Note: maximum for num is min1 here but it can be diminished
         * to reduce the time of execution.
         */
        NUMW = M213 (Arg0, 0x03, 0x02)
        NUM2 = (NUMW - 0x01) /* except the control thread */
        /* Pack numbers of threads */

        NTH0 = M20D (Arg0, NUMW)
        /*
         * Determine lls0 - number of levels to be in work
         *
         * Note: maximum for lls0 is max0 here but it can be diminished
         * to reduce the time of execution.
         */
        If (REDM)
        {
            LLS0 = 0x01
        }
        Else
        {
            LLS0 = MAX0 /* \MAX0 */
        }

        /* For all Levels of mutex one by one */

        LPN0 = LLS0 /* \M813.LLS0 */
        LPC0 = 0x00
        While (LPN0)
        {
            /* For different indexes-threads one by one */

            LPN1 = NUM2 /* \M813.NUM2 */
            LPC1 = 0x00
            While (LPN1)
            {
                INDT = (LPC1 + 0x01)
                /* Thread thr-i Acquires successfully mutex M0 of (i-1)-th index for N times */
                /* c106 for indt-th thread */
                M210 (CM00, NUMW, C106, INDT, 0x01, 0x01, 0x00)
                /* Repetition */

                LPN2 = RPT /* \M813.RPT_ */
                LPC2 = 0x00
                While (LPN2)
                {
                    M33F (NTH0, CM00, 0x00, LPC0, IX00, CM00, 0x00)    /* Expected hang statuses       (buffer/Integer) */
                    LPN2--
                    LPC2++
                }

                /* Thread thr-i Releases mutex M0 for N times */
                /* c107 for indt-th thread */
                M210 (CM00, NUMW, C107, INDT, 0x01, 0x01, 0x00)
                /* Repetition */

                LPN2 = RPT /* \M813.RPT_ */
                LPC2 = 0x00
                While (LPN2)
                {
                    M33F (NTH0, CM00, 0x00, LPC0, IX00, CM00, 0x00)
                    LPN2--
                    LPC2++
                }

                LPN1--
                LPC1++
            }

            LPN0--
            LPC0++
        }
    }

    /*
     * arg0 - number of threads (total)
     */
    Method (M814, 1, Serialized)
    {
        Name (LPN0, 0x00) /* level */
        Name (LPC0, 0x00)
        Name (LPN1, 0x00) /* index */
        Name (LPC1, 0x00)
        Name (THR1, 0x00)
        Name (THR2, 0x00)
        THR1 = 0x01
        THR2 = M115 (Arg0) /* thread with the greatest index */
        If ((THR2 >= Arg0))
        {
            Debug = "No alive threads for Test!"
            Debug = "Test mf14 skipped!"
            SKIP ()
            Return (Zero)
        }

        If ((THR2 <= THR1))
        {
            Debug = "Insufficient number of threads for Test!"
            Debug = "Test mf14 skipped!"
            SKIP ()
            Return (Zero)
        }

        /* 1. Thread thr-N Acquires all the mutexes on all levels */
        /* Set up per-thread set of mutexes */
        M334 (Arg0, C300, 0x00, MAX0, 0x00, MIN0)
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR2, C106) /* cmd: Acquire specified set of mutexes */
        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
        /* Check up the values of counters of all Mutexes */

        LPN0 = MAX0 /* \MAX0 */
        LPC0 = 0x00
        While (LPN0)
        {
            LPN1 = MIN0 /* \MIN0 */
            LPC1 = 0x00
            While (LPN1)
            {
                M333 (LPC0, LPC1, 0x01)
                LPN1--
                LPC1++
            }

            LPN0--
            LPC0++
        }

        /*
         * 2. Thread thr-1 tries to Acquire all the same mutexes
         *    and gets FAIL (TimeOutValue is not 0xFFFF).
         */
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR1, C106) /* cmd: Acquire specified set of mutexes */
        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
        M214 (Arg0, Arg0, TOV1) /* TimeOutValue equal to 1 msec */
        M20F (Arg0, EX0D, 0x00)    /* Init the exceptional conditions flags (FAIL) */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
        /* 3. Thread thr-N terminates */

        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR2, C108) /* cmd: Terminate thread */
        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
        /*
         * 4. Thread thr-1 Acquire all those mutexes again
         *    and gets success (TimeOutValue is 0xFFFF)
         */
        /* Sleep, to ensure the thread thr-N terminates */
        M206 (0x00, 0xC8)
        /*
         * Reset all counters (cnt0) and flags (fl00) corresponding
         * to all Mutexes which were set up by thread thr-N.
         */
        M330 ()
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR1, C106) /* cmd: Acquire specified set of mutexes */
        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
        /* 5. Thread thr-1 Releases all mutexes */

        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR1, C107) /* cmd: Release specified set of mutexes */
        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
    }

    /*
     * arg0 - number of threads (total)
     */
    Method (M815, 1, Serialized)
    {
        Name (LPN0, 0x00) /* level */
        Name (LPC0, 0x00)
        Name (LPN1, 0x00) /* index */
        Name (LPC1, 0x00)
        Name (THR1, 0x00)
        Name (THR2, 0x00)
        THR1 = 0x01
        THR2 = M115 (Arg0) /* thread with the greatest index */
        If ((THR2 >= Arg0))
        {
            Debug = "No alive threads for Test!"
            Debug = "Test mf14 skipped!"
            SKIP ()
            Return (Zero)
        }

        If ((THR2 <= THR1))
        {
            Debug = "Insufficient number of threads for Test!"
            Debug = "Test mf15 skipped!"
            SKIP ()
            Return (Zero)
        }

        /* 1. Thread thr-N Acquires all the mutexes on all levels */
        /* Set up per-thread set of mutexes */
        M334 (Arg0, C300, 0x00, MAX0, 0x00, MIN0)
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR2, C106) /* cmd: Acquire specified set of mutexes */
        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
        /* Check up the values of counters of all Mutexes */

        LPN0 = MAX0 /* \MAX0 */
        LPC0 = 0x00
        While (LPN0)
        {
            LPN1 = MIN0 /* \MIN0 */
            LPC1 = 0x00
            While (LPN1)
            {
                M333 (LPC0, LPC1, 0x01)
                LPN1--
                LPC1++
            }

            LPN0--
            LPC0++
        }

        /*
         * 2. Thread thr-1 tries to Acquire all the same mutexes
         *    and gets FAIL (TimeOutValue is not 0xFFFF).
         */
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR1, C106) /* cmd: Acquire specified set of mutexes */
        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
        M214 (Arg0, Arg0, TOV1) /* TimeOutValue equal to 1 msec */
        M20F (Arg0, EX0D, 0x00)    /* Init the exceptional conditions flags (FAIL) */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
        /*
         * 3. Thread thr-1 tries to Acquire all the same mutexes
         * and hang (TimeOutValue is 0xFFFF).
         */
        /*
         * Reset all counters (cnt0) and flags (fl00) corresponding
         * to all Mutexes which were set up by thread thr-N.
         */
        M330 ()
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR1, C106) /* cmd: Acquire specified set of mutexes */
        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        Name (CP00, Buffer (Arg0){})
        Name (HG00, Buffer (Arg0){})
        Name (ID00, Buffer (Arg0){})
        CopyObject (BS00, CP00) /* \M815.CP00 */
        CP00 [THR1] = 0x00
        HG00 [THR1] = C106 /* \C106 */
        M110 (Arg0, CP00, HG00, ID00)
        /*
         * 4. Thread thr-N terminates
         * 5. Thread thr-1 owns all those mutexes
         */
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR2, C108) /* cmd: Terminate thread */
        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        Name (CP01, Buffer (Arg0){})
        Name (HG01, Buffer (Arg0){})
        Name (ID01, Buffer (Arg0){})
        BS00 [THR1] = C106 /* thr-1 hangs on c106 */ /* \C106 */
        CopyObject (BS00, CP01) /* \M815.CP01 */
        M110 (Arg0, CP01, HG01, ID01)
        /* 6. Thread thr-1 Releases all mutexes */

        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR1, C107) /* cmd: Release specified set of mutexes */
        M215 (Arg0)             /* Reset TimeOutValue and exceptional condition flags */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
    }

    /*
     * Serialized method to be executed by Worker thread
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (M8FC, 3, Serialized)
    {
        If (FLG2)
        {
            SE00 (Arg2, ER10, "Error er10")
        }

        FLG2 = Arg1
        M201 (Arg2, VB03, "Execution of Serialized method started")
        M206 (Arg2, SL01) /* Sleep */
        /*
         * NOTE: it is a recurcive second call to m101:
         *
         *       MAIN
         *         mf00
         *           mf16
         *             m101
         *               m8fc
         *                 m101
         *
         * So, additional command c101 is needed for it to exit that second call to m101.
         */
        M201 (Arg2, VB03, "Call recursively m101")
        M101 (Arg0, Arg1, Arg2, 0x01)
        M206 (Arg2, SL01) /* Sleep */
        M201 (Arg2, VB03, "Execution of Serialized method completed")
        If ((FLG2 != Arg1))
        {
            SE00 (Arg2, ER11, "Error er11")
        }

        FLG2 = 0x00
    }

    /*
     * Non-serialized method to be executed by Worker thread,
     * use mutex for exclusive access to critical section.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (M8FA, 3, NotSerialized)
    {
        Local0 = MA00 (0x00, 0x00, 0xFFFF)
        If (Local0)
        {
            SE00 (Arg2, ER00, "Error er00")
        }

        If (FLG2)
        {
            SE00 (Arg2, ER10, "Error er10")
        }

        FLG2 = Arg1
        M201 (Arg2, VB03, "Execution of critical section started")
        M206 (Arg2, SL01) /* Sleep */
        /*
         * NOTE: it is a recurcive second call to m101:
         *
         *       MAIN
         *         mf00
         *           mf16
         *             m101
         *               m8fc
         *                 m101
         *
         * So, additional command c101 is needed for it to exit that second call to m101.
         */
        M201 (Arg2, VB03, "Call recursively m101")
        M101 (Arg0, Arg1, Arg2, 0x01)
        M206 (Arg2, SL01) /* Sleep */
        M201 (Arg2, VB03, "Execution of critical section completed")
        If ((FLG2 != Arg1))
        {
            SE00 (Arg2, ER11, "Error er11")
        }

        FLG2 = 0x00
        If (!Local0)
        {
            MA10 (0x00)
        }
    }

    /*
     * Non-serialized method to be executed by Worker thread
     *
     * non-serialized method is grabbed simultaneously by several threads
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (M8F9, 3, NotSerialized)
    {
        /*
         * Index of one of two threads participating in test is 1
         */
        If ((Arg2 == 0x01))
        {
            If (FLG2)
            {
                SE00 (Arg2, ER12, "Error er12")
            }
            Else
            {
                FLG2 = Arg2
            }
        }
        ElseIf (FLG3)
        {
            SE00 (Arg2, ER12, "Error er12")
        }
        Else
        {
            FLG3 = Arg2
        }

        M201 (Arg2, VB03, "Execution of non-serialized method started")
        M206 (Arg2, SL01) /* Sleep */
        /*
         * NOTE: it is a recurcive second call to m101:
         *
         *       MAIN
         *         mf00
         *           mf16
         *             m101
         *               m8fc
         *                 m101
         *
         * So, additional command c101 is needed for it to exit that second call to m101.
         */
        M201 (Arg2, VB03, "Call recursively m101")
        M101 (Arg0, Arg1, Arg2, 0x01)
        M206 (Arg2, SL01) /* Sleep */
        M201 (Arg2, VB03, "Execution of non-serialized method completed")
        If (!FLG2)
        {
            SE00 (Arg2, ER12, "Error er12")
        }

        If (!FLG3)
        {
            SE00 (Arg2, ER13, "Error er13")
        }
    }

    /*
     * arg0 - number of threads (total)
     * arg1 - main command for worker thread
     */
    Method (M8FB, 2, Serialized)
    {
        Name (LPN0, 0x00) /* level */
        Name (LPC0, 0x00)
        Name (LPN1, 0x00) /* index */
        Name (LPC1, 0x00)
        Name (THR1, 0x00)
        Name (THR2, 0x00)
        THR1 = 0x01
        THR2 = M115 (Arg0) /* thread with the greatest index */
        If ((THR2 >= Arg0))
        {
            Debug = "No alive threads for Test!"
            Debug = "Test mf14 skipped!"
            SKIP ()
            Return (Zero)
        }

        If ((THR2 <= THR1))
        {
            Debug = "Insufficient number of threads for Test!"
            Debug = "Test mf15 skipped!"
            SKIP ()
            Return (Zero)
        }

        /*
         * 1. Thread thr-1 invokes method MXXX (by c109/c10a) which allows
         *    exclusive access to the critical section.
         *    Then it calls recursively m101 (infinite loop of worker threads)
         *    so becomes identical to other threads for managing it.
         */
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR1, Arg1) /* cmd: c109/c10a */
        M20F (Arg0, 0x00, 0x00)       /* Init (Reset) the exceptional conditions flags (SUCCESS) */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
        /*
         * 2. Thread thr-2 invokes the same method MXXX (by c109/c10a) and hangs
         *    because method MXXX provides exclusive access and is already grabbed by thr-1.
         */
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR2, Arg1) /* cmd: c109/c10a */
        M20F (Arg0, 0x00, 0x00)       /* Init (Reset) the exceptional conditions flags (SUCCESS) */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        Name (CP00, Buffer (Arg0){})
        Name (HG00, Buffer (Arg0){})
        Name (ID00, Buffer (Arg0){})
        CopyObject (BS00, CP00) /* \M8FB.CP00 */
        CP00 [THR2] = 0x00
        HG00 [THR2] = Arg1
        M110 (Arg0, CP00, HG00, ID00)
        /*
         * 3. Sleep for all
         */
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        Name (CP01, Buffer (Arg0){})
        Name (HG01, Buffer (Arg0){})
        Name (ID01, Buffer (Arg0){})
        CopyObject (BS00, CP01) /* \M8FB.CP01 */
        CP01 [THR2] = 0x00
        HG01 [THR2] = Arg1
        M110 (Arg0, CP01, HG01, ID01)
        /*
         * 4. Thread thr-1 is directed to exit recursive (second) call to m101
         *    (infinite loop of worker threads).
         */
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR1, C101) /* cmd: Exit the infinite loop */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        Name (CP02, Buffer (Arg0){})
        Name (HG02, Buffer (Arg0){})
        Name (ID02, Buffer (Arg0){})
        CopyObject (BS00, CP02) /* \M8FB.CP02 */
        CP02 [THR2] = 0x00
        HG02 [THR2] = Arg1
        M110 (Arg0, CP02, HG02, ID02)
        /*
         * 5. Thread thr-2 is directed to exit recursive (second) call to m101
         *    (infinite loop of worker threads).
         */
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR2, C101) /* cmd: Exit the infinite loop */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
    }

    /*
     * Use Serialized method for exclusive access to critical section
     *
     * arg0 - number of threads (total)
     */
    Method (M816, 1, NotSerialized)
    {
        M8FB (Arg0, C109)
    }

    /*
     * Use Mutex for exclusive access to critical section, invoke non-Serialized method
     *
     * arg0 - number of threads (total)
     */
    Method (M817, 1, NotSerialized)
    {
        M8FB (Arg0, C10A)
    }

    /*
     * Non-serialized method is grabbed simultaneously
     *
     * arg0 - number of threads (total)
     */
    Method (M818, 1, Serialized)
    {
        Name (LPN0, 0x00) /* level */
        Name (LPC0, 0x00)
        Name (LPN1, 0x00) /* index */
        Name (LPC1, 0x00)
        Name (THR1, 0x00)
        Name (THR2, 0x00)
        FLG2 = 0x00
        FLG3 = 0x00
        THR1 = 0x01
        THR2 = M115 (Arg0) /* thread with the greatest index */
        If ((THR2 >= Arg0))
        {
            Debug = "No alive threads for Test!"
            Debug = "Test mf14 skipped!"
            SKIP ()
            Return (Zero)
        }

        If ((THR2 <= THR1))
        {
            Debug = "Insufficient number of threads for Test!"
            Debug = "Test mf15 skipped!"
            SKIP ()
            Return (Zero)
        }

        /*
         * 1. Thread thr-1 invokes non-Serialized method MXXX.
         *    Then it calls recursively m101 (infinite loop of worker threads)
         *    so becomes identical to other threads for managing it.
         */
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR1, C10B) /* cmd: Invoke non-Serialized method */
        M20F (Arg0, 0x00, 0x00)       /* Init (Reset) the exceptional conditions flags (SUCCESS) */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
        /*
         * 2. Sleep for all
         */
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M20F (Arg0, 0x00, 0x00)       /* Init (Reset) the exceptional conditions flags (SUCCESS) */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
        /*
         * 3. Thread thr-N invokes non-Serialized method MXXX.
         *    Then it calls recursively m101 (infinite loop of worker threads)
         *    so becomes identical to other threads for managing it.
         */
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR2, C10B) /* cmd: Invoke non-Serialized method */
        M20F (Arg0, 0x00, 0x00)       /* Init (Reset) the exceptional conditions flags (SUCCESS) */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
        /*
         * 4. Sleep for all
         */
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M20F (Arg0, 0x00, 0x00)       /* Init (Reset) the exceptional conditions flags (SUCCESS) */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
        /*
         * 5. Both threads thr-1 and thr-N are directed to exit recursive (second) calls to m101
         *    (infinite loops of worker threads).
         */
        M200 (BS00, Arg0, C102) /* cmd: Sleep */
        M208 (BS00, THR1, C101) /* cmd: Exit the infinite loop */
        M208 (BS00, THR2, C101) /* cmd: Exit the infinite loop */
        M20F (Arg0, 0x00, 0x00)       /* Init (Reset) the exceptional conditions flags (SUCCESS) */
        M114 (Arg0) /* run */
        /* Wait for all Worker threads */

        M103 (Arg0)
        If ((FLG2 != THR1))
        {
            ERR (Arg0, Z152, __LINE__, 0x00, 0x00, FLG2, THR1)
        }

        If ((FLG3 != THR2))
        {
            ERR (Arg0, Z152, __LINE__, 0x00, 0x00, FLG3, THR2)
        }
    }
