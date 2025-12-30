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
     * Bug 162:
     *
     * SUMMARY: Crash while processing the global level execution exception
     *
     * ROOT CAUSE
     *
     * While executing the AML code on a global level (out
     * of any Method, immediately on a DefinitionBlock level)
     * and being forced to handle some exception, ACPICA attempts
     * to retrieve elements of WalkState->MethodNode structure which
     * is a NULL pointer in that case (global level AML code execution
     * case).
     *
     * TO BE VERIFIED
     *
     * Run any Method to check that just after processing
     * the global level execution exception all became stable.
     */
    /* Set flag - demo-162 is there, allow compiling without it */
    Name (BD01, Buffer (ID02 = 0x01){})
    /* This declarations forces exception during the load of DefinitionBlock */

    Name (I002, 0x0A)
    Name (BUF0, Buffer ((I002 / 0x00))
    {
        /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
        /* 0008 */  0xFF                                             // .
    })
    /*
     * md7d - check, register errors and reset the global level execution exception,
     *        set up id01 to non-zero in error case.
     */
    Name (BUF1, Buffer (MD7D ()){})
    Method (MD78, 0, NotSerialized)
    {
        Debug = "Just after processing the global level execution exception all became stable!"
        /*
         * Since exception should be verified before STRT (see MAIN) we
         * have to initiate err here, to log the error in a usual way.
         */
        If (ID01)
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }
    }
