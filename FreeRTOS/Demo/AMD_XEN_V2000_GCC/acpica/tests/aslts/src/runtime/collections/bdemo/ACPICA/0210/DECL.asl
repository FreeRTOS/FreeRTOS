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
     * Bug 210 (local-bugzilla-349):
     *
     * COMPONENT:
     *
     * SUMMARY: Implicit return objects are not released in Slack Mode
     *          (Now on Slack Mode when an exception occurs and all nested control
     *          methods are terminated, Implicit return objects are not released).
     *
     * Note: automate in future counting the number of Outstanding allocations
     *       per-test and expect here zero which would mean success of test.
     *       Currently, always FAILURE.
     *
     * Note: the mentioned Outstanding allocation is not visible when _ERR
     *       is defined.
     */
    Method (M819, 0, NotSerialized)
    {
        Method (M000, 1, NotSerialized)
        {
            Local0 = 0x02
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Divide (0x01, Arg0, Local0)
            CH04 (__METHOD__, 0x00, 0x38, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_DIVIDE_BY_ZERO */
        }

        Method (M001, 0, NotSerialized)
        {
            Local0 = 0x01
            M000 (0x00)
        }

        M001 ()
        Debug = "Fight Outstanding allocations here"
        ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
    }
