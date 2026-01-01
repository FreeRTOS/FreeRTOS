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
     * Bug 0103:
     *
     * SUMMARY: The Method type element of Package is being invoked
     */
    Method (ME64, 0, NotSerialized)
    {
        Debug = "me64 invoked"
        ID0D = 0x01
        Return (0x07)
    }

    Method (ME65, 0, NotSerialized)
    {
        Debug = "me65 invoked"
        ID0E = 0x01
        Return (0x7B)
    }

    Method (ME66, 0, Serialized)
    {
        Debug = "Start of test"
        Name (P000, Package (0x08)
        {
            0x01,
            0x02,
            ME64,
            0x04,
            ME64,
            ME65,
            0x07,
            ME64
        })
        Debug = "Finish of test"
        Return (0x00)
    }

    Method (ME67, 0, NotSerialized)
    {
        ME66 ()
        If (ID0D)
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (ID0E)
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }
    }
