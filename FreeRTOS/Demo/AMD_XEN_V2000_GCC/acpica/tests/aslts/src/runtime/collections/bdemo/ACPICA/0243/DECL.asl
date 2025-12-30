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
     * Bug 243:
     *
     * SUMMARY: The normal work with mutexes is broken after the mutex Release order violation
     */
    Method (M02F, 0, Serialized)
    {
        Mutex (T500, 0x05)
        Mutex (T600, 0x06)
        Mutex (T700, 0x07)
        Method (M000, 0, NotSerialized)
        {
            Debug = "******** Test started"
            /* (1) */

            Debug = "Acquiring mutex of level 5:"
            Local0 = Acquire (T500, 0xFFFF)
            If (Local0)
            {
                Debug = "!!!!!!!! ERROR 0: Acquire T500 (Level 5, index 0)"
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
            }
            Else
            {
                Debug = "Ok: Acquired T500 (Level 5, index 0)"
            }

            /* (2) */

            Debug = "Acquiring mutex of level 6:"
            Local0 = Acquire (T600, 0xFFFF)
            If (Local0)
            {
                Debug = "!!!!!!!! ERROR 1: Acquire T600 (Level 6, index 0)"
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
            }
            Else
            {
                Debug = "Ok: Acquired T600 (Level 6, index 0)"
            }

            /* (3) */

            Debug = "Run Release of mutex of level 5 - exception AE_AML_MUTEX_ORDER is expected on it!"
            Debug = "Release T500 (Level 5, index 0)"
            Release (T500)
            /*
             * If no exception there:
             * ERROR: NO exception though expected! (it is the contents of bug 238)
             */
            CH04 (__METHOD__, 0x00, 0x40, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_MUTEX_ORDER */
            /* (4) */

            Debug = "Acquiring mutex of level 7:"
            Local0 = Acquire (T700, 0xFFFF)
            If (Local0)
            {
                Debug = "!!!!!!!! ERROR 3: Acquire T700 (Level 7, index 0)"
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
            }
            Else
            {
                Debug = "Ok: Acquired T700 (Level 7, index 0)"
                Debug = "Current level is equal to 7!"
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            /* (5) */

            Debug = "Releasing the mutex of the current level: T700 (Level 7, index 0)"
            Release (T700)
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            /*
             * (6)
             *
             * AE_AML_MUTEX_ORDER exception here which takes place
             * is an essence of this bug 243.
             */
            Debug = "Releasing mutex of level 6: T600 (Level 6, index 0)"
            Release (T600)
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            /* (7) */

            Debug = "Releasing mutex of level 5: T500 (Level 5, index 0)"
            Release (T500)
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        }

        Method (MM00, 0, NotSerialized)
        {
            M000 ()
        }

        MM00 ()
    }
