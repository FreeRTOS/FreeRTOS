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
     * Bug 211:
     *
     * COMPONENT:
     *
     * SUMMARY: ACPI-CA memory leak due to optionally stored AML Object passed through "child" Method
     *          (On Slack mode outstanding allocations are detected)
     *
     * Note: automate in future counting the number of Outstanding allocations
     *       per-test and expect here zero which would mean success of test.
     *       Currently, always FAILURE.
     */
    Method (M81A, 0, NotSerialized)
    {
        Method (M000, 1, NotSerialized)
        {
            Debug = Arg0
        }

        Local0 = (0xF0 | 0x01)
        M000 (Local0)
        Debug = "Fight Outstanding allocations here"
        /*
     * FIXED:
     *
     * ------- Additional Comment #8 From Len Brown 2006-06-25 21:49 -------
     * ACPICA 20060608 shipped in 2.6.17-git9, closed.
     *
     * err("", zFFF, __LINE__, 0, 0, 0, 0)
     */
    }
