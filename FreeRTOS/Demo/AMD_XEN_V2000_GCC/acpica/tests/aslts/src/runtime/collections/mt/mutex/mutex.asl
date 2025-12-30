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
     * Check mutex related interfaces in a real multi-threading mode
     */
    Name (Z148, 0x94)
    /*
     in progress
     SEE:
     ??????????????????????????????????????????
     1) See sleeping mode ... and m209
     3) remove all mf0X - workers only once go into
     } else { // Worker Threads
     m101(arg0, arg1, arg2, 0)
     }
     and Ctl Thread do mf00()
     4) do the same number of mutexes (indexes) for all mutex levels
     then uni0 will work in cm06/cm07... properly
     5) actually properly split methods among files and files among directories
     6) groups of methods - m340-m344 and m20d-m20e in the same group and name
     6) some methods are not used?
     7) m33f - does it have "Check up the values of counters of all Mutexes"?
     8) allow tests to run for 3 and 2 threads (excluding some) without SKIPPED
     */
    /*
     * Test mf01.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (MF01, 3, Serialized)
    {
        /* Initialization of multithreading interconnection */

        If (!M107 (Arg0, Arg1, Arg2, 0x00))
        {
            If (!Arg2)
            {
                Debug = "Test mf01 skipped!"
                SKIP ()
            }

            Return (Zero)
        }

        /* Report start of test: depending on vb01 can be reported by each thread */

        M204 ("mf01", Arg0, Arg1, Arg2)
        /*
         * The Worker Threads loop forever executing strategies
         * specified and controlled by the Control Thread.
         */
        If ((Arg2 == 0x00))
        {
            /* Control Thread */
            /*
             * These variables are to be actually used
             * by the Control Thread only
             */
            Name (LPN0, 0x00)
            Name (LPC0, 0x00)
            /* Open testing */

            M102 (Arg0)
            /* All workers to sleep */

            M100 (Arg0, Arg1, Arg2, CM02, 0x00, 0x00, 0x00)
            /* Acquire/Sleep/Release for all 0-15 levels and GL */

            LPN0 = MAX0 /* \MAX0 */
            LPC0 = 0x00
            While (LPN0)
            {
                /*
                 * Reset all counters (cnt0) and flags (fl00)
                 * corresponding to all Mutexes.
                 */
                M330 ()
                /*
                 * Acquire/Sleep/Release
                 *
                 * - Number of threads
                 * - Level of mutex
                 * - Index of mutex
                 * - Number of mutexes of the same level
                 */
                M801 (Arg0, LPC0, 0x00, MIN0)
                LPN0--
                LPC0++
            }

            /* Close testing */

            M108 ("mf01", Arg0, Arg1, Arg2)
        }
        Else
        {
            /* Worker Threads */

            M101 (Arg0, Arg1, Arg2, 0x00)
        }
    }

    /*
     * Test mf02.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (MF02, 3, NotSerialized)
    {
        /* Initialization of multithreading interconnection */

        If (!M107 (Arg0, Arg1, Arg2, 0x00))
        {
            If (!Arg2)
            {
                Debug = "Test mf02 skipped!"
                SKIP ()
            }

            Return (Zero)
        }

        /* Report start of test: depending on vb01 can be reported by each thread */

        M204 ("mf02", Arg0, Arg1, Arg2)
        /*
         * The Worker Threads loop forever executing strategies
         * specified and controlled by the Control Thread.
         */
        If ((Arg2 == 0x00))
        {
            /* Control Thread */
            /* Open testing */
            M102 (Arg0)
            /* All workers to sleep */

            M100 (Arg0, Arg1, Arg2, CM02, 0x00, 0x00, 0x00)
            /*
             * <Acquire/Sleep>(0-15 levels) and GL/Release(15-0 levels) and GL
             * - Number of threads
             * - Index of mutex
             * - Number of mutexes of the same level
             */
            M802 (Arg0, 0x00, 0x02)
            /* Close testing */

            M108 ("mf02", Arg0, Arg1, Arg2)
        }
        Else
        {
            /* Worker Threads */

            M101 (Arg0, Arg1, Arg2, 0x00)
        }
    }

    /*
     * Test mf03.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (MF03, 3, NotSerialized)
    {
        /* Initialization of multithreading interconnection */

        If (!M107 (Arg0, Arg1, Arg2, 0x00))
        {
            If (!Arg2)
            {
                Debug = "Test mf03 skipped!"
                SKIP ()
            }

            Return (Zero)
        }

        /* Report start of test: depending on vb01 can be reported by each thread */

        M204 ("mf03", Arg0, Arg1, Arg2)
        /*
         * The Worker Threads loop forever executing strategies
         * specified and controlled by the Control Thread.
         */
        If ((Arg2 == 0x00))
        {
            /* Control Thread */
            /* Open testing */
            M102 (Arg0)
            /* All workers to sleep */

            M100 (Arg0, Arg1, Arg2, CM02, 0x00, 0x00, 0x00)
            /*
             * Example 0
             * - Number of threads
             */
            M803 (Arg0)
            /* Close testing */

            M108 ("mf03", Arg0, Arg1, Arg2)
        }
        Else
        {
            /* Worker Threads */

            M101 (Arg0, Arg1, Arg2, 0x00)
        }
    }

    /*
     * Test mf04.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (MF04, 3, NotSerialized)
    {
        /* Initialization of multithreading interconnection */

        If (!M107 (Arg0, Arg1, Arg2, 0x03))
        {
            If (!Arg2)
            {
                Debug = "Test mf04 skipped!"
                SKIP ()
            }

            Return (Zero)
        }

        /* Report start of test: depending on vb01 can be reported by each thread */

        M204 ("mf04", Arg0, Arg1, Arg2)
        /*
         * The Worker Threads loop forever executing strategies
         * specified and controlled by the Control Thread.
         */
        If ((Arg2 == 0x00))
        {
            /* Control Thread */
            /* Open testing */
            M102 (Arg0)
            /* All workers to sleep */

            M100 (Arg0, Arg1, Arg2, CM02, 0x00, 0x00, 0x00)
            /* Test (see SPEC for mf04) */

            M804 (Arg0)
            /* Close testing */

            M108 ("mf04", Arg0, Arg1, Arg2)
        }
        Else
        {
            /* Worker Threads */

            M101 (Arg0, Arg1, Arg2, 0x00)
        }
    }

    /*
     * Test mf05.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (MF05, 3, NotSerialized)
    {
        /* Initialization of multithreading interconnection */

        If (!M107 (Arg0, Arg1, Arg2, 0x03))
        {
            If (!Arg2)
            {
                Debug = "Test mf05 skipped!"
                SKIP ()
            }

            Return (Zero)
        }

        /* Report start of test: depending on vb01 can be reported by each thread */

        M204 ("mf05", Arg0, Arg1, Arg2)
        /*
         * The Worker Threads loop forever executing strategies
         * specified and controlled by the Control Thread.
         */
        If ((Arg2 == 0x00))
        {
            /* Control Thread */
            /* Open testing */
            M102 (Arg0)
            /* All workers to sleep */

            M100 (Arg0, Arg1, Arg2, CM02, 0x00, 0x00, 0x00)
            /* Test (see SPEC for mf05) */

            M805 (Arg0)
            /* Close testing */

            M108 ("mf05", Arg0, Arg1, Arg2)
        }
        Else
        {
            /* Worker Threads */

            M101 (Arg0, Arg1, Arg2, 0x00)
        }
    }

    /*
     * Test mf06.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (MF06, 3, NotSerialized)
    {
        /* Initialization of multithreading interconnection */

        If (!M107 (Arg0, Arg1, Arg2, 0x03))
        {
            If (!Arg2)
            {
                Debug = "Test mf06 skipped!"
                SKIP ()
            }

            Return (Zero)
        }

        /* Report start of test: depending on vb01 can be reported by each thread */

        M204 ("mf06", Arg0, Arg1, Arg2)
        /*
         * The Worker Threads loop forever executing strategies
         * specified and controlled by the Control Thread.
         */
        If ((Arg2 == 0x00))
        {
            /* Control Thread */
            /* Open testing */
            M102 (Arg0)
            /* All workers to sleep */

            M100 (Arg0, Arg1, Arg2, CM02, 0x00, 0x00, 0x00)
            /* Test (see SPEC for mf06) */

            M806 (Arg0)
            /* Close testing */

            M108 ("mf06", Arg0, Arg1, Arg2)
        }
        Else
        {
            /* Worker Threads */

            M101 (Arg0, Arg1, Arg2, 0x00)
        }
    }

    /*
     * Test mf07.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (MF07, 3, NotSerialized)
    {
        /* Initialization of multithreading interconnection */

        If (!M107 (Arg0, Arg1, Arg2, 0x00))
        {
            If (!Arg2)
            {
                Debug = "Test mf07 skipped!"
                SKIP ()
            }

            Return (Zero)
        }

        /* Report start of test: depending on vb01 can be reported by each thread */

        M204 ("mf07", Arg0, Arg1, Arg2)
        /*
         * The Worker Threads loop forever executing strategies
         * specified and controlled by the Control Thread.
         */
        If ((Arg2 == 0x00))
        {
            /* Control Thread */
            /* Open testing */
            M102 (Arg0)
            /* All workers to sleep */

            M100 (Arg0, Arg1, Arg2, CM02, 0x00, 0x00, 0x00)
            /* Test (see SPEC for mf07) */

            M807 (Arg0)
            /* Close testing */

            M108 ("mf07", Arg0, Arg1, Arg2)
        }
        Else
        {
            /* Worker Threads */

            M101 (Arg0, Arg1, Arg2, 0x00)
        }
    }

    /*
     * Test mf08.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (MF08, 3, NotSerialized)
    {
        /* Initialization of multithreading interconnection */

        If (!M107 (Arg0, Arg1, Arg2, MIN1))
        {
            If (!Arg2)
            {
                Debug = "Test mf08 skipped!"
                SKIP ()
            }

            Return (Zero)
        }

        /* Report start of test: depending on vb01 can be reported by each thread */

        M204 ("mf08", Arg0, Arg1, Arg2)
        /*
         * The Worker Threads loop forever executing strategies
         * specified and controlled by the Control Thread.
         */
        If ((Arg2 == 0x00))
        {
            /* Control Thread */
            /* Open testing */
            M102 (Arg0)
            /* All workers to sleep */

            M100 (Arg0, Arg1, Arg2, CM02, 0x00, 0x00, 0x00)
            /* Test (see SPEC for mf08) */

            M808 (Arg0)
            /* Close testing */

            M108 ("mf08", Arg0, Arg1, Arg2)
        }
        Else
        {
            /* Worker Threads */

            M101 (Arg0, Arg1, Arg2, 0x00)
        }
    }

    /*
     * Test mf09.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (MF09, 3, NotSerialized)
    {
        /* Initialization of multithreading interconnection */

        If (!M107 (Arg0, Arg1, Arg2, MIN1))
        {
            If (!Arg2)
            {
                Debug = "Test mf09 skipped!"
                SKIP ()
            }

            Return (Zero)
        }

        /* Report start of test: depending on vb01 can be reported by each thread */

        M204 ("mf09", Arg0, Arg1, Arg2)
        /*
         * The Worker Threads loop forever executing strategies
         * specified and controlled by the Control Thread.
         */
        If ((Arg2 == 0x00))
        {
            /* Control Thread */
            /* Open testing */
            M102 (Arg0)
            /* All workers to sleep */

            M100 (Arg0, Arg1, Arg2, CM02, 0x00, 0x00, 0x00)
            /* Test (see SPEC for mf09) */

            M809 (Arg0)
            /* Close testing */

            M108 ("mf09", Arg0, Arg1, Arg2)
        }
        Else
        {
            /* Worker Threads */

            M101 (Arg0, Arg1, Arg2, 0x00)
        }
    }

    /*
     * Test mf10.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (MF10, 3, NotSerialized)
    {
        /* Initialization of multithreading interconnection */

        If (!M107 (Arg0, Arg1, Arg2, MIN1))
        {
            If (!Arg2)
            {
                Debug = "Test mf10 skipped!"
                SKIP ()
            }

            Return (Zero)
        }

        /* Report start of test: depending on vb01 can be reported by each thread */

        M204 ("mf10", Arg0, Arg1, Arg2)
        /*
         * The Worker Threads loop forever executing strategies
         * specified and controlled by the Control Thread.
         */
        If ((Arg2 == 0x00))
        {
            /* Control Thread */
            /* Open testing */
            M102 (Arg0)
            /* All workers to sleep */

            M100 (Arg0, Arg1, Arg2, CM02, 0x00, 0x00, 0x00)
            /* Test (see SPEC for mf10) */

            M810 (Arg0)
            /* Close testing */

            M108 ("mf10", Arg0, Arg1, Arg2)
        }
        Else
        {
            /* Worker Threads */

            M101 (Arg0, Arg1, Arg2, 0x00)
        }
    }

    /*
     * Test mf11.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (MF11, 3, NotSerialized)
    {
        /* Initialization of multithreading interconnection */

        If (!M107 (Arg0, Arg1, Arg2, 0x00))
        {
            If (!Arg2)
            {
                Debug = "Test mf11 skipped!"
                SKIP ()
            }

            Return (Zero)
        }

        /* Report start of test: depending on vb01 can be reported by each thread */

        M204 ("mf11", Arg0, Arg1, Arg2)
        /*
         * The Worker Threads loop forever executing strategies
         * specified and controlled by the Control Thread.
         */
        If ((Arg2 == 0x00))
        {
            /* Control Thread */
            /* Open testing */
            M102 (Arg0)
            /* All workers to sleep */

            M100 (Arg0, Arg1, Arg2, CM02, 0x00, 0x00, 0x00)
            /* Test (see SPEC for mf11) */

            M811 (Arg0)
            /* Close testing */

            M108 ("mf11", Arg0, Arg1, Arg2)
        }
        Else
        {
            /* Worker Threads */

            M101 (Arg0, Arg1, Arg2, 0x00)
        }
    }

    /*
     * Test mf12.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (MF12, 3, NotSerialized)
    {
        /* Initialization of multithreading interconnection */

        If (!M107 (Arg0, Arg1, Arg2, 0x03))
        {
            If (!Arg2)
            {
                Debug = "Test mf12 skipped!"
                SKIP ()
            }

            Return (Zero)
        }

        /* Report start of test: depending on vb01 can be reported by each thread */

        M204 ("mf12", Arg0, Arg1, Arg2)
        /*
         * The Worker Threads loop forever executing strategies
         * specified and controlled by the Control Thread.
         */
        If ((Arg2 == 0x00))
        {
            /* Control Thread */
            /* Open testing */
            M102 (Arg0)
            /* All workers to sleep */

            M100 (Arg0, Arg1, Arg2, CM02, 0x00, 0x00, 0x00)
            /* Test (see SPEC for mf12) */

            M812 (Arg0)
            /* Close testing */

            M108 ("mf12", Arg0, Arg1, Arg2)
        }
        Else
        {
            /* Worker Threads */

            M101 (Arg0, Arg1, Arg2, 0x00)
        }
    }

    /*
     * Test mf13.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (MF13, 3, NotSerialized)
    {
        /* Initialization of multithreading interconnection */

        If (!M107 (Arg0, Arg1, Arg2, 0x00))
        {
            If (!Arg2)
            {
                Debug = "Test mf13 skipped!"
                SKIP ()
            }

            Return (Zero)
        }

        /* Report start of test: depending on vb01 can be reported by each thread */

        M204 ("mf13", Arg0, Arg1, Arg2)
        /*
         * The Worker Threads loop forever executing strategies
         * specified and controlled by the Control Thread.
         */
        If ((Arg2 == 0x00))
        {
            /* Control Thread */
            /* Open testing */
            M102 (Arg0)
            /* All workers to sleep */

            M100 (Arg0, Arg1, Arg2, CM02, 0x00, 0x00, 0x00)
            /* Test (see SPEC for mf13) */

            M813 (Arg0)
            /* Close testing */

            M108 ("mf13", Arg0, Arg1, Arg2)
        }
        Else
        {
            /* Worker Threads */

            M101 (Arg0, Arg1, Arg2, 0x00)
        }
    }

    /*
     * Test mf14.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (MF14, 3, NotSerialized)
    {
        /* Initialization of multithreading interconnection */

        If (!M107 (Arg0, Arg1, Arg2, 0x00))
        {
            If (!Arg2)
            {
                Debug = "Test mf14 skipped!"
                SKIP ()
            }

            Return (Zero)
        }

        /* Report start of test: depending on vb01 can be reported by each thread */

        M204 ("mf14", Arg0, Arg1, Arg2)
        /*
         * The Worker Threads loop forever executing strategies
         * specified and controlled by the Control Thread.
         */
        If ((Arg2 == 0x00))
        {
            /* Control Thread */
            /* Open testing */
            M102 (Arg0)
            /* All workers to sleep */

            M100 (Arg0, Arg1, Arg2, CM02, 0x00, 0x00, 0x00)
            /* Test (see SPEC for mf14) */

            M814 (Arg0)
            /* Close testing */

            M108 ("mf14", Arg0, Arg1, Arg2)
        }
        Else
        {
            /* Worker Threads */

            M101 (Arg0, Arg1, Arg2, 0x00)
        }
    }

    /*
     * Test mf15.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (MF15, 3, NotSerialized)
    {
        /* Initialization of multithreading interconnection */

        If (!M107 (Arg0, Arg1, Arg2, 0x00))
        {
            If (!Arg2)
            {
                Debug = "Test mf15 skipped!"
                SKIP ()
            }

            Return (Zero)
        }

        /* Report start of test: depending on vb01 can be reported by each thread */

        M204 ("mf15", Arg0, Arg1, Arg2)
        /*
         * The Worker Threads loop forever executing strategies
         * specified and controlled by the Control Thread.
         */
        If ((Arg2 == 0x00))
        {
            /* Control Thread */
            /* Open testing */
            M102 (Arg0)
            /* All workers to sleep */

            M100 (Arg0, Arg1, Arg2, CM02, 0x00, 0x00, 0x00)
            /* Test (see SPEC for mf15) */

            M815 (Arg0)
            /* Close testing */

            M108 ("mf15", Arg0, Arg1, Arg2)
        }
        Else
        {
            /* Worker Threads */

            M101 (Arg0, Arg1, Arg2, 0x00)
        }
    }

    /*
     * Test mf16.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (MF16, 3, NotSerialized)
    {
        /* Initialization of multithreading interconnection */

        If (!M107 (Arg0, Arg1, Arg2, 0x00))
        {
            If (!Arg2)
            {
                Debug = "Test mf16 skipped!"
                SKIP ()
            }

            Return (Zero)
        }

        /* Report start of test: depending on vb01 can be reported by each thread */

        M204 ("mf16", Arg0, Arg1, Arg2)
        /*
         * The Worker Threads loop forever executing strategies
         * specified and controlled by the Control Thread.
         */
        If ((Arg2 == 0x00))
        {
            /* Control Thread */
            /* Open testing */
            M102 (Arg0)
            /* All workers to sleep */

            M100 (Arg0, Arg1, Arg2, CM02, 0x00, 0x00, 0x00)
            /* Test (see SPEC for mf16) */

            M816 (Arg0)
            /* Close testing */

            M108 ("mf16", Arg0, Arg1, Arg2)
        }
        Else
        {
            /* Worker Threads */

            M101 (Arg0, Arg1, Arg2, 0x00)
        }
    }

    /*
     * Test mf17.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (MF17, 3, NotSerialized)
    {
        /* Initialization of multithreading interconnection */

        If (!M107 (Arg0, Arg1, Arg2, 0x00))
        {
            If (!Arg2)
            {
                Debug = "Test mf17 skipped!"
                SKIP ()
            }

            Return (Zero)
        }

        /* Report start of test: depending on vb01 can be reported by each thread */

        M204 ("mf17", Arg0, Arg1, Arg2)
        /*
         * The Worker Threads loop forever executing strategies
         * specified and controlled by the Control Thread.
         */
        If ((Arg2 == 0x00))
        {
            /* Control Thread */
            /* Open testing */
            M102 (Arg0)
            /* All workers to sleep */

            M100 (Arg0, Arg1, Arg2, CM02, 0x00, 0x00, 0x00)
            /* Test (see SPEC for mf17) */

            M817 (Arg0)
            /* Close testing */

            M108 ("mf17", Arg0, Arg1, Arg2)
        }
        Else
        {
            /* Worker Threads */

            M101 (Arg0, Arg1, Arg2, 0x00)
        }
    }

    /*
     * Test mf18.
     *
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (MF18, 3, NotSerialized)
    {
        /* Initialization of multithreading interconnection */

        If (!M107 (Arg0, Arg1, Arg2, 0x00))
        {
            If (!Arg2)
            {
                Debug = "Test mf18 skipped!"
                SKIP ()
            }

            Return (Zero)
        }

        /* Report start of test: depending on vb01 can be reported by each thread */

        M204 ("mf18", Arg0, Arg1, Arg2)
        /*
         * The Worker Threads loop forever executing strategies
         * specified and controlled by the Control Thread.
         */
        If ((Arg2 == 0x00))
        {
            /* Control Thread */
            /* Open testing */
            M102 (Arg0)
            /* All workers to sleep */

            M100 (Arg0, Arg1, Arg2, CM02, 0x00, 0x00, 0x00)
            /* Test (see SPEC for mf18) */

            M818 (Arg0)
            /* Close testing */

            M108 ("mf18", Arg0, Arg1, Arg2)
        }
        Else
        {
            /* Worker Threads */

            M101 (Arg0, Arg1, Arg2, 0x00)
        }
    }

    /*
     * arg0 - number of threads
     * arg1 - ID of current thread
     * arg2 - Index of current thread
     */
    Method (MF00, 3, NotSerialized)
    {
        If (!Arg2)
        {
            /* Sleeping mode */

            SL00 = 0x0A /* default milliseconds to sleep for Control thread */
            SL01 = 0x0A /* default milliseconds to sleep for Worker threads */
            SLM0 = 0x00  /* sleeping mode for worker threads */
        }

        If (!Y251)
        {
            If (!Arg2)
            {
                /*
                 * Initialization of multithreading interconnection:
                 * only to check that mt-technique itself works.
                 */
                If (!M107 (Arg0, Arg1, Arg2, 0x00))
                {
                    Debug = "Mt-technique doesn\'t work!"
                }
                Else
                {
                    Debug = "Mt-technique works"
                }

                VB04 = 0x00 /* don't print statistics */
                CTL0 = 0x01 /* Worker threads - go! */
                SRMT ("mt_mutex_tests")
            }

            Return (Zero)
        }

        If (0x01)
        {
            /* Tests */

            If (!Arg2)
            {
                SRMT ("mf01")
            }

            MF01 (Arg0, Arg1, Arg2)
            If (!Arg2)
            {
                SRMT ("mf02")
            }

            MF02 (Arg0, Arg1, Arg2)
            If (!Arg2)
            {
                SRMT ("mf03")
            }

            MF03 (Arg0, Arg1, Arg2)
            If (!Arg2)
            {
                SRMT ("mf04")
            }

            MF04 (Arg0, Arg1, Arg2)
            If (!Arg2)
            {
                SRMT ("mf05")
            }

            MF05 (Arg0, Arg1, Arg2)
            If (!Arg2)
            {
                SRMT ("mf06")
            }

            MF06 (Arg0, Arg1, Arg2)
            If (0x01)
            {
                If (!Arg2)
                {
                    SRMT ("mf07")
                }

                MF07 (Arg0, Arg1, Arg2)
            }
            ElseIf (!Arg2)
            {
                SRMT ("mf07")
                BLCK ()
            }

            If (!Arg2)
            {
                SRMT ("mf08")
            }

            MF08 (Arg0, Arg1, Arg2)
            If (!Arg2)
            {
                SRMT ("mf09")
            }

            MF09 (Arg0, Arg1, Arg2)
            If (!Arg2)
            {
                SRMT ("mf10")
            }

            MF10 (Arg0, Arg1, Arg2)
            If (!Arg2)
            {
                SRMT ("mf11")
            }

            MF11 (Arg0, Arg1, Arg2)
            If (!Arg2)
            {
                SRMT ("mf12")
            }

            MF12 (Arg0, Arg1, Arg2)
            If (!Arg2)
            {
                SRMT ("mf13")
            }

            MF13 (Arg0, Arg1, Arg2)
            If (!Arg2)
            {
                SRMT ("mf14")
            }

            MF14 (Arg0, Arg1, Arg2)
            If (!Arg2)
            {
                SRMT ("mf15")
            }

            MF15 (Arg0, Arg1, Arg2)
            If (!Arg2)
            {
                SRMT ("mf16")
            }

            MF16 (Arg0, Arg1, Arg2)
            If (!Arg2)
            {
                SRMT ("mf17")
            }

            MF17 (Arg0, Arg1, Arg2)
            If (!Arg2)
            {
                SRMT ("mf18")
            }

            MF18 (Arg0, Arg1, Arg2)
        }
        Else
        {
            If (!Arg2)
            {
                SRMT ("mf01")
            }

            MF01 (Arg0, Arg1, Arg2)
        }

        /* Report statistics */

        If ((Arg2 == 0x00))
        {
            /* Control Thread */

            If (VB04)
            {
                M211 (Arg0)
            }
        }
    }
