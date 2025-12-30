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
     * Bug 171:
     *
     * SUMMARY: Improper Integer to String implicit conversion in a specific case
     *
     * COMMENT:
     *
     * The demo program shows that the result
     * of Integer to String implicit conversion
     * in 32-bit mode can look like 64-bit mode
     * takes place.
     * The ComplianceRevision field of the demo program
     * should be 2, but run ASL compiler with "-r 1" option.
     * The anomaly is not observed when AML code is obtained
     * with "-r 1 -oa" options.
     */
    Method (MF5E, 0, NotSerialized)
    {
        Local0 = ("C179B3FE" == 0xC179B3FE)
        If ((Local0 != Ones))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Ones)
        }

        Local0 = (0xC179B3FE == "C179B3FE")
        If ((Local0 != Ones))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Ones)
        }
    }
