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
     * Bug 182:
     *
     * SUMMARY: Exception on a specific declarations of objects of the same name
     *
     *          (no exception is expected here because id23 has already
     *          been defined at the first use of it).
     */
    Name (ID23, 0xABCD0000)
    Method (MF78, 0, Serialized)
    {
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        If ((ID23 != 0xABCD0000))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, ID23, 0xABCD0000)
        }

        Name (ID23, 0xABCD0001)
        If ((ID23 != 0xABCD0001))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, ID23, 0xABCD0001)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }

    /*
     * ATTENTION: i9z8 should be unique in the namespace,
     *            not declared somewhere else in the NS tree.
     */
    Method (MF85, 0, Serialized)
    {
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        If ((I9Z8 != 0xABCD0001))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, I9Z8, 0xABCD0001)
        }

        Name (I9Z8, 0xABCD0001)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
    }
