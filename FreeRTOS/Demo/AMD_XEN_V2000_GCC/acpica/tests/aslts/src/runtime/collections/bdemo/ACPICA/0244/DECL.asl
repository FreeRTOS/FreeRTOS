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
     * Bug 244:
     *
     * SUMMARY: Acquire/Release in a global level AML code is not valid,
     * removed from test suite.
     */
    /*Mutex(T804, 8) */
    /*Mutex(T805, 8) */
    /*Mutex(T806, 8) */
    /*Mutex(T807, 8) */
    /*
     * These declarations are used for to check the Acquire
     * and Release operations in a global level AML code.
     */
    /*Name(i101, 0) // non-zero means that this test was run */
    /*Name(i104, 1) */
    /*Name(i105, 1) */
    /*Name(i106, 1) */
    /*Name(i107, 1) */
    /*
     Method(m137)
     {
     Store(1, i101)
     Store("m137 started", Debug)
     if (LNot(i104)) {
     Release(T804)
     }
     Store("m137 completed", Debug)
     return (1)
     }
     Method(m13e)
     {
     Store(1, i101)
     Store("m13e started", Debug)
     Store(Acquire(T805, 0xffff), i105)
     Store("m13e completed", Debug)
     return (1)
     }
     Method(m13f)
     {
     Store(1, i101)
     Store("m13f started", Debug)
     if (LNot(i105)) {
     Release(T805)
     }
     Store("m13f completed", Debug)
     return (1)
     }
     Method(m140)
     {
     Store(1, i101)
     Store("m140 started", Debug)
     Store(Acquire(T807, 0xffff), i107)
     Store("m140 completed", Debug)
     return (1)
     }
     */
    /* Acquire/Release T804 */
    /*Name(b11c, Buffer(Add(1, Store(Acquire(T804, 0xffff), i104))){0}) */
    /*Name(b11d, Buffer(m137()){0}) */
    /* Acquire/Release T805 */
    /*Name(b11e, Buffer(m13e()){0}) */
    /*Name(b11f, Buffer(m13f()){0}) */
    /* Acquire T806 */
    /*Name(b120, Buffer(Add(1, Store(Acquire(T806, 0xffff), i106))){0}) */
    /* Acquire T807 */
    /*Name(b121, Buffer(m140()){0}) */
    /*
     * m03c - check, register errors and reset the global level execution exception,
     *        set up id01 to non-zero in error case.
     */
    /*Name(i108, 0) */
    /*Name(BUF2, Buffer(m03c()){}) */
    /*
     Method(m03c)
     {
     if (CH03("", 0, 0x000, __LINE__, 0))
     {
     Store(1, i108)
     }
     }
     */
    Method (M02E, 0, NotSerialized)
    {
        /*
     Method(m0b9)
     {
     if (i108) {
     err("", zFFF, __LINE__, 0, 0, 0, 0)
     }
     if (LNot(i101)) {
     Store("******** Test was not run !!!!!!!!!!!!!", Debug)
     err("", zFFF, __LINE__, 0, 0, 0, 0)
     return
     }
     Store("******** Test started", Debug)
     CH03("", 0, 0x003, __LINE__, 0)
     if (i104) {
     Store("!!!!!!!! ERROR 1: Acquire(T804, 0xffff) failed", Debug)
     err("", zFFF, __LINE__, 0, 0, 0, 0)
     } else {
     Store("Ok: Acquire(T804, 0xffff)", Debug)
     }
     if (i105) {
     Store("!!!!!!!! ERROR 2: Acquire(T805, 0xffff) failed", Debug)
     err("", zFFF, __LINE__, 0, 0, 0, 0)
     } else {
     Store("Ok: Acquire(T805, 0xffff)", Debug)
     }
     Release(T804)
     CH04("", 0, 65, 0, __LINE__, 0, 0) // AE_AML_MUTEX_NOT_ACQUIRED
     Release(T805)
     CH04("", 0, 65, 0, __LINE__, 0, 0) // AE_AML_MUTEX_NOT_ACQUIRED
     // Release T807
     if (LNot(i107)) {
     Release(T807)
     } else {
     Store("!!!!!!!! ERROR 7: Acquire(T807, 0xffff) failed", Debug)
     err("", zFFF, __LINE__, 0, 0, 0, 0)
     }
     CH03("", 0, 0x009, __LINE__, 0)
     // Release T806
     if (LNot(i106)) {
     Release(T806)
     } else {
     Store("!!!!!!!! ERROR 5: Acquire(T806, 0xffff) failed", Debug)
     err("", zFFF, __LINE__, 0, 0, 0, 0)
     }
     CH03("", 0, 0x00b, __LINE__, 0)
     Store("******** Test finished", Debug)
     }
     Method(mm00)
     {
     m0b9()
     }
     mm00()
     */
    }

    Method (M030, 0, Serialized)
    {
        Mutex (T804, 0x08)
        Mutex (T805, 0x08)
        Mutex (T806, 0x08)
        Mutex (T807, 0x08)
        /*
         * These declarations are used for to check the Acquire
         * and Release operations in a global level AML code.
         */
        Name (I101, 0x00) /* non-zero means that this test was run */
        Name (I104, 0x01)
        Name (I105, 0x01)
        Name (I106, 0x01)
        Name (I107, 0x01)
        Method (M137, 0, NotSerialized)
        {
            I101 = 0x01
            Debug = "m137 started"
            If (!I104)
            {
                Release (T804)
            }

            Debug = "m137 completed"
            Return (0x01)
        }

        Method (M13E, 0, NotSerialized)
        {
            I101 = 0x01
            Debug = "m13e started"
            I105 = Acquire (T805, 0xFFFF)
            Debug = "m13e completed"
            Return (0x01)
        }

        Method (M13F, 0, NotSerialized)
        {
            I101 = 0x01
            Debug = "m13f started"
            If (!I105)
            {
                Release (T805)
            }

            Debug = "m13f completed"
            Return (0x01)
        }

        Method (M140, 0, NotSerialized)
        {
            I101 = 0x01
            Debug = "m140 started"
            I107 = Acquire (T807, 0xFFFF)
            Debug = "m140 completed"
            Return (0x01)
        }

        /* Acquire/Release T804 */

        Name (B11C, Buffer ((0x01 + I104 = Acquire (T804, 0xFFFF)))
        {
             0x00                                             // .
        })
        Name (B11D, Buffer (M137 ())
        {
             0x00                                             // .
        })
        /* Acquire/Release T805 */

        Name (B11E, Buffer (M13E ())
        {
             0x00                                             // .
        })
        Name (B11F, Buffer (M13F ())
        {
             0x00                                             // .
        })
        /* Acquire T806 */

        Name (B120, Buffer ((0x01 + I106 = Acquire (T806, 0xFFFF)))
        {
             0x00                                             // .
        })
        /* Acquire T807 */

        Name (B121, Buffer (M140 ())
        {
             0x00                                             // .
        })
        Method (M0B9, 0, NotSerialized)
        {
            If (!I101)
            {
                Debug = "******** Test was not run !!!!!!!!!!!!!"
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
                Return (Zero)
            }

            Debug = "******** Test started"
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            If (I104)
            {
                Debug = "!!!!!!!! ERROR 1: Acquire(T804, 0xffff) failed"
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
            }
            Else
            {
                Debug = "Ok: Acquire(T804, 0xffff)"
            }

            If (I105)
            {
                Debug = "!!!!!!!! ERROR 2: Acquire(T805, 0xffff) failed"
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
            }
            Else
            {
                Debug = "Ok: Acquire(T805, 0xffff)"
            }

            Release (T804)
            CH04 (__METHOD__, 0x00, 0x41, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_MUTEX_NOT_ACQUIRED */
            Release (T805)
            CH04 (__METHOD__, 0x00, 0x41, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_MUTEX_NOT_ACQUIRED */
            /* Release T807 */

            If (!I107)
            {
                Release (T807)
            }
            Else
            {
                Debug = "!!!!!!!! ERROR 7: Acquire(T807, 0xffff) failed"
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            /* Release T806 */

            If (!I106)
            {
                Release (T806)
            }
            Else
            {
                Debug = "!!!!!!!! ERROR 5: Acquire(T806, 0xffff) failed"
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Debug = "******** Test finished"
        }

        Method (MM00, 0, NotSerialized)
        {
            M0B9 ()
        }

        MM00 ()
    }
