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
     * Synchronization (mutexes)
     *
     * The test for ASL-Mutexes to be run on a single invocation only
     */
    /*
     * Mutex + Acquire + Release
     *
     * The test actions exercise the (Mutex + Acquire + Release)
     * operators adhering to the following ACPI-specified rules
     * (some of them are verified):
     *
     * - creates a data mutex synchronization object,
     *   with level from 0 to 15 specified by SyncLevel,
     * - a Mutex is not owned by a different invocation so it is owned
     *   immediately,
     * - acquiring ownership of a Mutex can be nested,
     * - a Mutex can be acquired more than once by the same invocation,
     * - Acquire returns False if a timeout not occurred and the mutex
     *   ownership was successfully acquired,
     * - to prevent deadlocks, wherever more than one synchronization
     *   object must be owned, the synchronization objects must always
     *   be released in the order opposite the order in which they were
     *   acquired,
     * - all Acquire terms must refer to a synchronization object with
     *   an equal or greater SyncLevel to current level,
     * - all Release terms must refer to a synchronization object with
     *   equal or lower SyncLevel to the current level,
     * - after all the acquired mutexes of the current level are released
     *   the top occupied levels declines to the nearest occupied level,
     * - Acquire increases the counter of mutex by one,
     * - Release decreases the counter of mutex by one.
     */
    /* Acquire methods */
    /* m01X(<method name>, <mux0>,  <mux1>,  <mux2>, <mux3>) */
    /* Release methods */
    /* m02X(<method name>, <mux0>,  <mux1>,  <mux2>, <mux3>) */
    /* ================================================= Acquire methods */
    Method (M010, 5, NotSerialized)
    {
        If (Arg1)
        {
            CH00 (Arg0, 0x00, 0x00, Acquire (T000, 0x0000))
        }

        If (Arg2)
        {
            CH00 (Arg0, 0x00, 0x01, Acquire (T001, 0xFFFF))
        }

        If (Arg3)
        {
            CH00 (Arg0, 0x00, 0x02, Acquire (T002, 0x8000))
        }

        If (Arg4)
        {
            CH00 (Arg0, 0x00, 0x03, Acquire (T003, 0x1000))
        }
    }

    Method (M011, 5, NotSerialized)
    {
        If (Arg1)
        {
            CH00 (Arg0, 0x01, 0x00, Acquire (T100, 0x0000))
        }

        If (Arg2)
        {
            CH00 (Arg0, 0x01, 0x01, Acquire (T101, 0xFFFF))
        }

        If (Arg3)
        {
            CH00 (Arg0, 0x01, 0x02, Acquire (T102, 0x8000))
        }

        If (Arg4)
        {
            CH00 (Arg0, 0x01, 0x03, Acquire (T103, 0x1000))
        }
    }

    Method (M012, 5, NotSerialized)
    {
        If (Arg1)
        {
            CH00 (Arg0, 0x02, 0x00, Acquire (T200, 0x0000))
        }

        If (Arg2)
        {
            CH00 (Arg0, 0x02, 0x01, Acquire (T201, 0xFFFF))
        }

        If (Arg3)
        {
            CH00 (Arg0, 0x02, 0x02, Acquire (T202, 0x8000))
        }

        If (Arg4)
        {
            CH00 (Arg0, 0x02, 0x03, Acquire (T203, 0x1000))
        }
    }

    Method (M013, 5, NotSerialized)
    {
        If (Arg1)
        {
            CH00 (Arg0, 0x03, 0x00, Acquire (T300, 0x0000))
        }

        If (Arg2)
        {
            CH00 (Arg0, 0x03, 0x01, Acquire (T301, 0xFFFF))
        }

        If (Arg3)
        {
            CH00 (Arg0, 0x03, 0x02, Acquire (T302, 0x8000))
        }

        If (Arg4)
        {
            CH00 (Arg0, 0x03, 0x03, Acquire (T303, 0x1000))
        }
    }

    Method (M014, 5, NotSerialized)
    {
        If (Arg1)
        {
            CH00 (Arg0, 0x04, 0x00, Acquire (T400, 0x0000))
        }

        If (Arg2)
        {
            CH00 (Arg0, 0x04, 0x01, Acquire (T401, 0xFFFF))
        }

        If (Arg3)
        {
            CH00 (Arg0, 0x04, 0x02, Acquire (T402, 0x8000))
        }

        If (Arg4)
        {
            CH00 (Arg0, 0x04, 0x03, Acquire (T403, 0x1000))
        }
    }

    Method (M015, 5, NotSerialized)
    {
        If (Arg1)
        {
            CH00 (Arg0, 0x05, 0x00, Acquire (T500, 0x0000))
        }

        If (Arg2)
        {
            CH00 (Arg0, 0x05, 0x01, Acquire (T501, 0xFFFF))
        }

        If (Arg3)
        {
            CH00 (Arg0, 0x05, 0x02, Acquire (T502, 0x8000))
        }

        If (Arg4)
        {
            CH00 (Arg0, 0x05, 0x03, Acquire (T503, 0x1000))
        }
    }

    Method (M016, 5, NotSerialized)
    {
        If (Arg1)
        {
            CH00 (Arg0, 0x06, 0x00, Acquire (T600, 0x0000))
        }

        If (Arg2)
        {
            CH00 (Arg0, 0x06, 0x01, Acquire (T601, 0xFFFF))
        }

        If (Arg3)
        {
            CH00 (Arg0, 0x06, 0x02, Acquire (T602, 0x8000))
        }

        If (Arg4)
        {
            CH00 (Arg0, 0x06, 0x03, Acquire (T603, 0x1000))
        }
    }

    Method (M017, 5, NotSerialized)
    {
        If (Arg1)
        {
            CH00 (Arg0, 0x07, 0x00, Acquire (T700, 0x0000))
        }

        If (Arg2)
        {
            CH00 (Arg0, 0x07, 0x01, Acquire (T701, 0xFFFF))
        }

        If (Arg3)
        {
            CH00 (Arg0, 0x07, 0x02, Acquire (T702, 0x8000))
        }

        If (Arg4)
        {
            CH00 (Arg0, 0x07, 0x03, Acquire (T703, 0x1000))
        }
    }

    Method (M018, 5, NotSerialized)
    {
        If (Arg1)
        {
            CH00 (Arg0, 0x08, 0x00, Acquire (T800, 0x0000))
        }

        If (Arg2)
        {
            CH00 (Arg0, 0x08, 0x01, Acquire (T801, 0xFFFF))
        }

        If (Arg3)
        {
            CH00 (Arg0, 0x08, 0x02, Acquire (T802, 0x8000))
        }

        If (Arg4)
        {
            CH00 (Arg0, 0x08, 0x03, Acquire (T803, 0x1000))
        }
    }

    Method (M019, 5, NotSerialized)
    {
        If (Arg1)
        {
            CH00 (Arg0, 0x09, 0x00, Acquire (T900, 0x0000))
        }

        If (Arg2)
        {
            CH00 (Arg0, 0x09, 0x01, Acquire (T901, 0xFFFF))
        }

        If (Arg3)
        {
            CH00 (Arg0, 0x09, 0x02, Acquire (T902, 0x8000))
        }

        If (Arg4)
        {
            CH00 (Arg0, 0x09, 0x03, Acquire (T903, 0x1000))
        }
    }

    Method (M01A, 5, NotSerialized)
    {
        If (Arg1)
        {
            CH00 (Arg0, 0x0A, 0x00, Acquire (TA00, 0x0000))
        }

        If (Arg2)
        {
            CH00 (Arg0, 0x0A, 0x01, Acquire (TA01, 0xFFFF))
        }

        If (Arg3)
        {
            CH00 (Arg0, 0x0A, 0x02, Acquire (TA02, 0x8000))
        }

        If (Arg4)
        {
            CH00 (Arg0, 0x0A, 0x03, Acquire (TA03, 0x1000))
        }
    }

    Method (M01B, 5, NotSerialized)
    {
        If (Arg1)
        {
            CH00 (Arg0, 0x0B, 0x00, Acquire (TB00, 0x0000))
        }

        If (Arg2)
        {
            CH00 (Arg0, 0x0B, 0x01, Acquire (TB01, 0xFFFF))
        }

        If (Arg3)
        {
            CH00 (Arg0, 0x0B, 0x02, Acquire (TB02, 0x8000))
        }

        If (Arg4)
        {
            CH00 (Arg0, 0x0B, 0x03, Acquire (TB03, 0x1000))
        }
    }

    Method (M01C, 5, NotSerialized)
    {
        If (Arg1)
        {
            CH00 (Arg0, 0x0C, 0x00, Acquire (TC00, 0x0000))
        }

        If (Arg2)
        {
            CH00 (Arg0, 0x0C, 0x01, Acquire (TC01, 0xFFFF))
        }

        If (Arg3)
        {
            CH00 (Arg0, 0x0C, 0x02, Acquire (TC02, 0x8000))
        }

        If (Arg4)
        {
            CH00 (Arg0, 0x0C, 0x03, Acquire (TC03, 0x1000))
        }
    }

    Method (M01D, 5, NotSerialized)
    {
        If (Arg1)
        {
            CH00 (Arg0, 0x0D, 0x00, Acquire (TD00, 0x0000))
        }

        If (Arg2)
        {
            CH00 (Arg0, 0x0D, 0x01, Acquire (TD01, 0xFFFF))
        }

        If (Arg3)
        {
            CH00 (Arg0, 0x0D, 0x02, Acquire (TD02, 0x8000))
        }

        If (Arg4)
        {
            CH00 (Arg0, 0x0D, 0x03, Acquire (TD03, 0x1000))
        }
    }

    Method (M01E, 5, NotSerialized)
    {
        If (Arg1)
        {
            CH00 (Arg0, 0x0E, 0x00, Acquire (TE00, 0x0000))
        }

        If (Arg2)
        {
            CH00 (Arg0, 0x0E, 0x01, Acquire (TE01, 0xFFFF))
        }

        If (Arg3)
        {
            CH00 (Arg0, 0x0E, 0x02, Acquire (TE02, 0x8000))
        }

        If (Arg4)
        {
            CH00 (Arg0, 0x0E, 0x03, Acquire (TE03, 0x1000))
        }
    }

    Method (M01F, 5, NotSerialized)
    {
        If (Arg1)
        {
            CH00 (Arg0, 0x0F, 0x00, Acquire (TF00, 0x0000))
        }

        If (Arg2)
        {
            CH00 (Arg0, 0x0F, 0x01, Acquire (TF01, 0xFFFF))
        }

        If (Arg3)
        {
            CH00 (Arg0, 0x0F, 0x02, Acquire (TF02, 0x8000))
        }

        If (Arg4)
        {
            CH00 (Arg0, 0x0F, 0x03, Acquire (TF03, 0x1000))
        }
    }

    /* ================================================= Release methods */

    Method (M020, 5, NotSerialized)
    {
        If (Arg4)
        {
            Release (T003)
        }

        If (Arg3)
        {
            Release (T002)
        }

        If (Arg2)
        {
            Release (T001)
        }

        If (Arg1)
        {
            Release (T000)
        }
    }

    Method (M021, 5, NotSerialized)
    {
        If (Arg4)
        {
            Release (T103)
        }

        If (Arg3)
        {
            Release (T102)
        }

        If (Arg2)
        {
            Release (T101)
        }

        If (Arg1)
        {
            Release (T100)
        }
    }

    Method (M022, 5, NotSerialized)
    {
        If (Arg4)
        {
            Release (T203)
        }

        If (Arg3)
        {
            Release (T202)
        }

        If (Arg2)
        {
            Release (T201)
        }

        If (Arg1)
        {
            Release (T200)
        }
    }

    Method (M023, 5, NotSerialized)
    {
        If (Arg4)
        {
            Release (T303)
        }

        If (Arg3)
        {
            Release (T302)
        }

        If (Arg2)
        {
            Release (T301)
        }

        If (Arg1)
        {
            Release (T300)
        }
    }

    Method (M024, 5, NotSerialized)
    {
        If (Arg4)
        {
            Release (T403)
        }

        If (Arg3)
        {
            Release (T402)
        }

        If (Arg2)
        {
            Release (T401)
        }

        If (Arg1)
        {
            Release (T400)
        }
    }

    Method (M025, 5, NotSerialized)
    {
        If (Arg4)
        {
            Release (T503)
        }

        If (Arg3)
        {
            Release (T502)
        }

        If (Arg2)
        {
            Release (T501)
        }

        If (Arg1)
        {
            Release (T500)
        }
    }

    Method (M026, 5, NotSerialized)
    {
        If (Arg4)
        {
            Release (T603)
        }

        If (Arg3)
        {
            Release (T602)
        }

        If (Arg2)
        {
            Release (T601)
        }

        If (Arg1)
        {
            Release (T600)
        }
    }

    Method (M027, 5, NotSerialized)
    {
        If (Arg4)
        {
            Release (T703)
        }

        If (Arg3)
        {
            Release (T702)
        }

        If (Arg2)
        {
            Release (T701)
        }

        If (Arg1)
        {
            Release (T700)
        }
    }

    Method (M028, 5, NotSerialized)
    {
        If (Arg4)
        {
            Release (T803)
        }

        If (Arg3)
        {
            Release (T802)
        }

        If (Arg2)
        {
            Release (T801)
        }

        If (Arg1)
        {
            Release (T800)
        }
    }

    Method (M029, 5, NotSerialized)
    {
        If (Arg4)
        {
            Release (T903)
        }

        If (Arg3)
        {
            Release (T902)
        }

        If (Arg2)
        {
            Release (T901)
        }

        If (Arg1)
        {
            Release (T900)
        }
    }

    Method (M02A, 5, NotSerialized)
    {
        If (Arg4)
        {
            Release (TA03)
        }

        If (Arg3)
        {
            Release (TA02)
        }

        If (Arg2)
        {
            Release (TA01)
        }

        If (Arg1)
        {
            Release (TA00)
        }
    }

    Method (M02B, 5, NotSerialized)
    {
        If (Arg4)
        {
            Release (TB03)
        }

        If (Arg3)
        {
            Release (TB02)
        }

        If (Arg2)
        {
            Release (TB01)
        }

        If (Arg1)
        {
            Release (TB00)
        }
    }

    Method (M02C, 5, NotSerialized)
    {
        If (Arg4)
        {
            Release (TC03)
        }

        If (Arg3)
        {
            Release (TC02)
        }

        If (Arg2)
        {
            Release (TC01)
        }

        If (Arg1)
        {
            Release (TC00)
        }
    }

    Method (M02D, 5, NotSerialized)
    {
        If (Arg4)
        {
            Release (TD03)
        }

        If (Arg3)
        {
            Release (TD02)
        }

        If (Arg2)
        {
            Release (TD01)
        }

        If (Arg1)
        {
            Release (TD00)
        }
    }

    Method (M02E, 5, NotSerialized)
    {
        If (Arg4)
        {
            Release (TE03)
        }

        If (Arg3)
        {
            Release (TE02)
        }

        If (Arg2)
        {
            Release (TE01)
        }

        If (Arg1)
        {
            Release (TE00)
        }
    }

    Method (M02F, 5, NotSerialized)
    {
        If (Arg4)
        {
            Release (TF03)
        }

        If (Arg3)
        {
            Release (TF02)
        }

        If (Arg2)
        {
            Release (TF01)
        }

        If (Arg1)
        {
            Release (TF00)
        }
    }

    /* ================================================= Run Acquire/Release */
    /*
     * Acquire
     *	arg0 - name of method to be reported
     *	arg1 - synclevel (0-15)
     *	arg2 - start mutex inside the first processed synclevel
     *           (0 for other levels)
     *           0 - starting with the # (arg3)
     *           1 - 0-th
     *           2 - 1-th
     *           3 - 2-th
     *           4 - 3-th
     *	arg3 - # operations to be performed for current synclevel
     */
    Method (M030, 4, NotSerialized)
    {
        If ((Arg3 == 0x00))
        {
            Return (0x00)
        }

        Local1 = 0x00
        Local2 = 0x00
        Local3 = 0x00
        Local4 = 0x00
        /* Local5 - index of highest */

        Store ((Arg2 + Arg3), Local5)
        Local5--
        Local6 = 0x00
        Local7 = 0x00
        If ((Arg2 <= 0x00))
        {
            Local6 = 0x01
        }

        If ((Local5 >= 0x00))
        {
            Local7 = 0x01
        }

        If ((Local6 && Local7))
        {
            Local1 = 0x01
        }

        Local6 = 0x00
        Local7 = 0x00
        If ((Arg2 <= 0x01))
        {
            Local6 = 0x01
        }

        If ((Local5 >= 0x01))
        {
            Local7 = 0x01
        }

        If ((Local6 && Local7))
        {
            Local2 = 0x01
        }

        Local6 = 0x00
        Local7 = 0x00
        If ((Arg2 <= 0x02))
        {
            Local6 = 0x01
        }

        If ((Local5 >= 0x02))
        {
            Local7 = 0x01
        }

        If ((Local6 && Local7))
        {
            Local3 = 0x01
        }

        Local6 = 0x00
        Local7 = 0x00
        If ((Arg2 <= 0x03))
        {
            Local6 = 0x01
        }

        If ((Local5 >= 0x03))
        {
            Local7 = 0x01
        }

        If ((Local6 && Local7))
        {
            Local4 = 0x01
        }

        If (0x00)
        {
            Debug = Local1
            Debug = Local2
            Debug = Local3
            Debug = Local4
            Return (0x00)
        }

        If ((Arg1 == 0x00))
        {
            M010 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x01))
        {
            M011 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x02))
        {
            M012 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x03))
        {
            M013 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x04))
        {
            M014 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x05))
        {
            M015 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x06))
        {
            M016 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x07))
        {
            M017 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x08))
        {
            M018 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x09))
        {
            M019 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x0A))
        {
            M01A (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x0B))
        {
            M01B (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x0C))
        {
            M01C (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x0D))
        {
            M01D (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x0E))
        {
            M01E (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x0F))
        {
            M01F (Arg0, Local1, Local2, Local3, Local4)
        }

        Return (0x00)
    }

    /*
     * Release
     *	arg0 - name of method to be reported
     *	arg1 - synclevel (0-15)
     *	arg2 - start mutex inside the first processed synclevel
     *           (0 for other levels)
     *           0 - starting with the # (arg3)
     *           4 - 3-th
     *           3 - 2-th
     *           2 - 1-th
     *           1 - 0-th
     *	arg3 - # operations to be performed for current synclevel
     */
    Method (M031, 4, NotSerialized)
    {
        If ((Arg3 == 0x00))
        {
            Return (0x00)
        }

        Local1 = 0x00
        Local2 = 0x00
        Local3 = 0x00
        Local4 = 0x00
        /* arg2 - index of highest */

        If ((Arg2 == 0x00))
        {
            Arg2 = Arg3
        }

        Arg2--
        /* Local5 - index of lowest */

        Store ((Arg2 - Arg3), Local5)
        Local5++
        Local6 = 0x00
        Local7 = 0x00
        If ((Local5 <= 0x00))
        {
            Local6 = 0x01
        }

        If ((Arg2 >= 0x00))
        {
            Local7 = 0x01
        }

        If ((Local6 && Local7))
        {
            Local1 = 0x01
        }

        Local6 = 0x00
        Local7 = 0x00
        If ((Local5 <= 0x01))
        {
            Local6 = 0x01
        }

        If ((Arg2 >= 0x01))
        {
            Local7 = 0x01
        }

        If ((Local6 && Local7))
        {
            Local2 = 0x01
        }

        Local6 = 0x00
        Local7 = 0x00
        If ((Local5 <= 0x02))
        {
            Local6 = 0x01
        }

        If ((Arg2 >= 0x02))
        {
            Local7 = 0x01
        }

        If ((Local6 && Local7))
        {
            Local3 = 0x01
        }

        Local6 = 0x00
        Local7 = 0x00
        If ((Local5 <= 0x03))
        {
            Local6 = 0x01
        }

        If ((Arg2 >= 0x03))
        {
            Local7 = 0x01
        }

        If ((Local6 && Local7))
        {
            Local4 = 0x01
        }

        If (0x00)
        {
            Debug = Local1
            Debug = Local2
            Debug = Local3
            Debug = Local4
            Return (0x00)
        }

        If ((Arg1 == 0x00))
        {
            M020 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x01))
        {
            M021 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x02))
        {
            M022 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x03))
        {
            M023 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x04))
        {
            M024 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x05))
        {
            M025 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x06))
        {
            M026 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x07))
        {
            M027 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x08))
        {
            M028 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x09))
        {
            M029 (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x0A))
        {
            M02A (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x0B))
        {
            M02B (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x0C))
        {
            M02C (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x0D))
        {
            M02D (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x0E))
        {
            M02E (Arg0, Local1, Local2, Local3, Local4)
        }

        If ((Arg1 == 0x0F))
        {
            M02F (Arg0, Local1, Local2, Local3, Local4)
        }

        Return (0x00)
    }

    /* ================================================= Tests */
    /* How many times run Acquire/Release for the particular level mutexes */
    /* 0 - Acquire */
    /* 1 - Release */
    /*
     * Name(p010, Buffer() {
     *	0, 0,   2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15, 16, 17,
     *	1, 0,  20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
     *	0, 0,  38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53,
     *	1, 0,  56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71,
     *	}
     * )
     */
    Name (P010, Buffer (0x03F0)
    {
        /* 0000 */  0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0010 */  0x00, 0x00, 0x01, 0x00, 0x04, 0x00, 0x00, 0x00,  // ........
        /* 0018 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0020 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x03,  // ........
        /* 0028 */  0x02, 0x01, 0x04, 0x03, 0x02, 0x01, 0x00, 0x00,  // ........
        /* 0030 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00,  // ........
        /* 0038 */  0x04, 0x03, 0x02, 0x01, 0x04, 0x03, 0x02, 0x01,  // ........
        /* 0040 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0048 */  0x00, 0x00, 0x04, 0x03, 0x02, 0x01, 0x04, 0x03,  // ........
        /* 0050 */  0x02, 0x01, 0x04, 0x03, 0x02, 0x01, 0x04, 0x03,  // ........
        /* 0058 */  0x02, 0x00, 0x01, 0x00, 0x04, 0x03, 0x02, 0x01,  // ........
        /* 0060 */  0x04, 0x03, 0x02, 0x01, 0x04, 0x03, 0x02, 0x01,  // ........
        /* 0068 */  0x04, 0x03, 0x02, 0x00, 0x00, 0x00, 0x04, 0x04,  // ........
        /* 0070 */  0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,  // ........
        /* 0078 */  0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x01, 0x00,  // ........
        /* 0080 */  0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,  // ........
        /* 0088 */  0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,  // ........
        /* 0090 */  0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0098 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 00A0 */  0x00, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00,  // ........
        /* 00A8 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 00B0 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x00,  // ........
        /* 00B8 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 00C0 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00,  // ........
        /* 00C8 */  0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 00D0 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 00D8 */  0x01, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 00E0 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 00E8 */  0x00, 0x00, 0x01, 0x00, 0x04, 0x00, 0x00, 0x00,  // ........
        /* 00F0 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 00F8 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x04,  // ........
        /* 0100 */  0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x00,  // ........
        /* 0108 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0110 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0118 */  0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0120 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0128 */  0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0130 */  0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0138 */  0x00, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00,  // ........
        /* 0140 */  0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,  // ........
        /* 0148 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x00,  // ........
        /* 0150 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00,  // ........
        /* 0158 */  0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,  // ........
        /* 0160 */  0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0168 */  0x00, 0x00, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,  // ........
        /* 0170 */  0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,  // ........
        /* 0178 */  0x04, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0180 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0188 */  0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0190 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0198 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x01, 0x00,  // ........
        /* 01A0 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 01A8 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04,  // ........
        /* 01B0 */  0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 01B8 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 01C0 */  0x00, 0x04, 0x01, 0x00, 0x04, 0x04, 0x04, 0x04,  // ........
        /* 01C8 */  0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,  // ........
        /* 01D0 */  0x04, 0x04, 0x04, 0x04, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 01D8 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 01E0 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x01, 0x00,  // ........
        /* 01E8 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 01F0 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04,  // ........
        /* 01F8 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0200 */  0x00, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,  // ........
        /* 0208 */  0x04, 0x04, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0210 */  0x00, 0x00, 0x00, 0x04, 0x04, 0x04, 0x04, 0x04,  // ........
        /* 0218 */  0x04, 0x04, 0x04, 0x04, 0x00, 0x00, 0x04, 0x00,  // ........
        /* 0220 */  0x04, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x04,  // ........
        /* 0228 */  0x00, 0x00, 0x00, 0x00, 0x04, 0x04, 0x01, 0x00,  // ........
        /* 0230 */  0x04, 0x00, 0x04, 0x00, 0x00, 0x04, 0x00, 0x00,  // ........
        /* 0238 */  0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x04, 0x04,  // ........
        /* 0240 */  0x00, 0x00, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,  // ........
        /* 0248 */  0x04, 0x04, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0250 */  0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0258 */  0x00, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00,  // ........
        /* 0260 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0268 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x00,  // ........
        /* 0270 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00,  // ........
        /* 0278 */  0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,  // ........
        /* 0280 */  0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0288 */  0x00, 0x00, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,  // ........
        /* 0290 */  0x04, 0x04, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0298 */  0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 02A0 */  0x00, 0x04, 0x04, 0x04, 0x04, 0x00, 0x00, 0x00,  // ........
        /* 02A8 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 02B0 */  0x00, 0x00, 0x00, 0x04, 0x04, 0x04, 0x04, 0x00,  // ........
        /* 02B8 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00,  // ........
        /* 02C0 */  0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,  // ........
        /* 02C8 */  0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 02D0 */  0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 02D8 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 02E0 */  0x00, 0x00, 0x01, 0x04, 0x01, 0x00, 0x00, 0x00,  // ........
        /* 02E8 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 02F0 */  0x00, 0x00, 0x00, 0x00, 0x01, 0x03, 0x01, 0x00,  // ........
        /* 02F8 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0300 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x02,  // ........
        /* 0308 */  0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0310 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0318 */  0x01, 0x01, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0320 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0328 */  0x00, 0x00, 0x00, 0x00, 0x04, 0x04, 0x04, 0x04,  // ........
        /* 0330 */  0x04, 0x04, 0x04, 0x04, 0x04, 0x00, 0x00, 0x00,  // ........
        /* 0338 */  0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,  // ........
        /* 0340 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x04, 0x00,  // ........
        /* 0348 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x04,  // ........
        /* 0350 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0x00,  // ........
        /* 0358 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0360 */  0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0368 */  0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0370 */  0x00, 0x00, 0x01, 0x00, 0x04, 0x04, 0x04, 0x04,  // ........
        /* 0378 */  0x04, 0x04, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0380 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x04,  // ........
        /* 0388 */  0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x00,  // ........
        /* 0390 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00,  // ........
        /* 0398 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x04, 0x04,  // ........
        /* 03A0 */  0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 03A8 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04,  // ........
        /* 03B0 */  0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x00,  // ........
        /* 03B8 */  0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 03C0 */  0x00, 0x00, 0x00, 0x04, 0x04, 0x04, 0x04, 0x04,  // ........
        /* 03C8 */  0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 03D0 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x04, 0x04,  // ........
        /* 03D8 */  0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x01, 0x00,  // ........
        /* 03E0 */  0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,  // ........
        /* 03E8 */  0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04   // ........
    })
    /*
     * Run Acquire/Release for all level mutexes
     *
     * Buffer:={N lines}
     * Line:= consists of 18 bytes:
     *   0:     operation: 0-Acquire, 1-Release
     *   1:     The start mutex inside the first processed synclevel
     *          (start mux and synclevels are ordered: Acquire: left->r,
     *           Release: r->l)
     *          0:   to start according to the given number (bytes 2-17)
     *          1-4: Acquire (left->right) (1-0th,2-1th,3-2th,4-3th)
     *               Release (right->left) (4-3th,3-2th,2-1th,1-0th)
     *   2-17:  per-synclevel numbers of operations to be performed:
     *          how many operations (from 0 up to 4) to be performed
     *          (at most one per mutex) on the mutexes of the relevant
     *          level (2th - synclevel 0, 3th - synclevel 1, etc.)
     * Variables:
     *	arg0   - name of method to be reported
     *	arg1   - lines total number
     *	arg2   - buffer of lines
     *	arg3   - name of buffer
     *	Local7 - index of line
     *	Local6 - synclevel (0-15)
     *	Local5 - operation (0-Acquire,1-Release)
     *	Local4 - abs index corresponding to synclevel inside the buffer
     *	Local3 - auxiliary = (Local6 + 1)
     *	Local2 - # operations to be performed for current synclevel
     *	Local1 - start mutex inside the first processed synclevel
     *             (0 for other levels)
     */
    Method (M032, 4, NotSerialized)
    {
        Local7 = 0x00
        While (Arg1)
        {
            Local6 = (Local7 * 0x12)
            Local5 = DerefOf (Arg2 [Local6])
            Local6++
            Local1 = DerefOf (Arg2 [Local6])
            If ((Local5 == 0x00))
            {
                If (0x00)
                {
                    Debug = "============= Acq"
                }

                Store ((Local6 + 0x01), Local4)
                Local6 = 0x00
                While ((Local6 < 0x10))
                {
                    Local2 = DerefOf (Arg2 [Local4])
                    If (0x00)
                    {
                        Debug = Local6
                        Debug = Local4
                        Debug = Local2
                    }

                    If (Local2)
                    {
                        M030 (Arg0, Local6, Local1, Local2)
                        Local1 = 0x00
                    }

                    Local6++
                    Local4++
                }
            }
            Else
            {
                If (0x00)
                {
                    Debug = "============= Rel"
                }

                Store ((Local6 + 0x10), Local4)
                Local3 = 0x10
                While (Local3)
                {
                    Store ((Local3 - 0x01), Local6)
                    Local2 = DerefOf (Arg2 [Local4])
                    If (0x00)
                    {
                        Debug = Local6
                        Debug = Local4
                        Debug = Local2
                    }

                    If (Local2)
                    {
                        M031 (Arg0, Local6, Local1, Local2)
                        Local1 = 0x00
                    }

                    Local3--
                    Local4--
                }
            }

            Local7++
            Arg1--
        }

        CH03 ("MUX0", Z150, __LINE__, 0x00, 0x00)
    }

    Method (M033, 0, Serialized)
    {
        Mutex (MTX0, 0x00)
        Local0 = Acquire (MTX0, 0x0000)
        If (Local0)
        {
            Debug = "M033: Could not acquire mutex"
            Return (Zero)
        }

        Release (MTX0)
    }

    Method (M034, 0, NotSerialized)
    {
        Local0 = 0xC8
        While (Local0)
        {
            M033 ()
            Local0--
        }
    }

    /* Run-method */

    Method (MUX0, 0, Serialized)
    {
        Debug = "TEST: MUX0, Acquire/Release Mutex"
        SRMT ("m032")
        M032 (__METHOD__, 0x38, P010, "p010")
        SRMT ("m034")
        M034 ()
    }
