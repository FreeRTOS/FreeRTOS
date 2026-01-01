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
     * Bug 238:
     *
     * SUMMARY: The jumping over levels in releasing mutexes is not prohibited
     */
    Method (M039, 0, Serialized)
    {
        Mutex (MX07, 0x07)
        Mutex (MX08, 0x08)
        Mutex (MX09, 0x09)
        Method (M000, 0, NotSerialized)
        {
            Acquire (MX07, 0xFFFF)
            Acquire (MX08, 0xFFFF)
            Acquire (MX09, 0xFFFF)
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Release (MX08)
            /*
             * Release(MX08) above doesn't cause exception
             * but, seems, it should.
             */
            CH04 (__METHOD__, 0x00, 0x40, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_MUTEX_ORDER */
            /* Also this */

            Release (MX07)
            CH04 (__METHOD__, 0x00, 0x40, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_MUTEX_ORDER */
            /*
             * Now, the Release(MX09) below causes exception,
             * so we have no way to release MX09.
             *
             * Considered:
             *   1. Both Releases above should cause AE_AML_MUTEX_ORDER
             *   2. The failed Releases above should not change the current level
             *   3. So, the Release below should succeed
             */
            Release (MX09)
            Release (MX08)
            Release (MX07)
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        }

        M000 ()
    }
