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
     * Bug 0048:
     *
     * SUMMARY: No exception on result of Concatenate longer than 210 bytes
     */
    Method (MDD8, 0, NotSerialized)
    {
        /* 100 characters */

        Local0 = "0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
        /* 101 characters */

        Local1 = "01234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890"
        /* Concatenate 100-byte long string with 101-byte long */
        /* string and expect AE_AML_STRING_LIMIT exception. */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local2 = Concatenate (Local0, Local1)
        /*
         * No restriction on the length of String objects now:
         *
         * CH04("", 0, 61, 0, __LINE__, 0, 0) // AE_AML_STRING_LIMIT
         */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }
