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
     * Bug 157:
     * Exception occurs while executing method md00.
     *
     * SUMMARY: Exception while processing the empty ParameterTypes list of Method
     *
     * ROOT CAUSE
     *
     * 19.09.2005, the root cause of it is the raw state of
     * implementation of "parametertypes list" feature of iASL.
     * iASL generates a wrong AML code for md00 as if it has one
     * parameter. Stopped fixing.
     *
     *
     * NOTE: add here new failing examples from name/method.asl and
     *       name/function.asl tests when starts fixing the bug.
     */
    Method (MD00, 0, NotSerialized)
    {
        Method (M000, 0, NotSerialized)
        {
            Return ("md00.m000")
        }

        Method (MM00, 0, NotSerialized)
        {
            Return ("md00.mm00")
        }

        /* Auxiliary names for to eliminate side-effects of the bug */

        Method (MMM0, 0, NotSerialized)
        {
            Return (Zero)
        }

        Method (MMM1, 0, NotSerialized)
        {
            Return (Zero)
        }

        /* Method */

        Local0 = "Local0"
        Local0 = M000 ()
        MMM0 ()
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        If (("md00.m000" != Local0))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, "md00.m000")
        }

        /* Function */

        Local0 = "Local0"
        Local0 = MM00 ()
        MMM1 ()
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        If (("md00.mm00" != Local0))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, "md00.mm00")
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }
