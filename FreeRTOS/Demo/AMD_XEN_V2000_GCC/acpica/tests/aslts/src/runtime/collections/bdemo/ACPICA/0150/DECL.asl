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
     * Bug 150:
     *
     * SUMMARY: No exception when Serialized Method is run after the higher level mutex acquiring
     *
     * EXAMPLES
     *
     * ROOT CAUSE
     *
     * SEE ALSO:
     */
    /*
     1. Acquire of the same mux several times without Releases
     2. Acquire+Releases sequence of the same mux several times
     3. Acquire mux level 7 then Release it and try Acquire mux level 6
     4. Acquire mux level 7 then try Acquire mux level 6
     5. Check all the specified features
     */
    /*
     * The proper sequence of several enclosed Acquire operations.
     *
     * Acquire N level mutex then acquire (N+k) level mutex.
     */
    Method (MD8A, 0, Serialized)
    {
        Mutex (MX00, 0x00)
        Mutex (MX01, 0x01)
        Local0 = 0x00
        Local1 = 0x00
        If (Acquire (MX00, 0x0001))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
            Local0 = 0x01
            If (Acquire (MX01, 0x0001))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
            }
            Else
            {
                Local1 = 0x01
            }
        }

        If (Local1)
        {
            Release (MX01)
        }

        If (Local0)
        {
            Release (MX00)
        }
    }

    /*
     * Improper sequence of several enclosed Acquire operations.
     *
     * Acquire N level mutex then acquire (N-k) level mutex.
     * Exception AE_AML_MUTEX_ORDER is expected in this case.
     */
    Method (MD8B, 0, Serialized)
    {
        Mutex (MX00, 0x01)
        Mutex (MX01, 0x00)
        Local0 = 0x00
        Local1 = 0x00
        If (Acquire (MX00, 0x0001))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
            Local0 = 0x01
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Acquire (MX01, 0x0001)
            CH04 (__METHOD__, 0x00, 0x40, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_MUTEX_ORDER */
        }

        If (Local0)
        {
            Release (MX00)
        }
    }

    /*
     * The proper sequence of several enclosed operations.
     *
     * Acquire N level mutex then call to Serialized Method
     * declared with (N+k) SyncLevel.
     */
    Method (MD8C, 0, Serialized)
    {
        Mutex (MX00, 0x00)
        Method (MX01, 0, Serialized, 1)
        {
            Debug = "Run Method mx01"
        }

        Local0 = 0x00
        Local1 = 0x00
        If (Acquire (MX00, 0x0001))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
            Local0 = 0x01
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            MX01 ()
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        }

        If (Local0)
        {
            Release (MX00)
        }
    }

    /*
     * Improper sequence of several enclosed operations.
     *
     * Acquire N level mutex then call to Serialized Method declared with (N-k) SyncLevel.
     * Exception AE_AML_MUTEX_ORDER is expected in this case.
     */
    Method (MD8D, 0, Serialized)
    {
        Mutex (MX00, 0x01)
        Method (MX01, 0, Serialized)
        {
            Debug = "Run Method mx01"
        }

        Local0 = 0x00
        Local1 = 0x00
        If (Acquire (MX00, 0x0001))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }
        Else
        {
            Local0 = 0x01
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            MX01 ()
            CH04 (__METHOD__, 0x00, 0x40, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_MUTEX_ORDER */
        }

        If (Local0)
        {
            Release (MX00)
        }
    }

    Method (MD8E, 0, NotSerialized)
    {
        MD8A ()
        MD8B ()
        MD8C ()
        MD8D ()
    }
