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
     * Bug 0028:
     *
     * SUMMARY: No exception on Create*Field for out of Buffer range
     */
    Method (MDBC, 0, Serialized)
    {
        Name (B000, Buffer (0x10){})
        CreateBitField (B000, 0x7F, F000)
        CreateByteField (B000, 0x0F, F001)
        CreateWordField (B000, 0x0E, F002)
        CreateDWordField (B000, 0x0C, F003)
        CreateQWordField (B000, 0x08, F004)
        CreateField (B000, 0x7F, 0x01, F005)
        CreateField (B000, 0x78, 0x08, F006)
    }

    Method (MDBD, 0, Serialized)
    {
        Name (B000, Buffer (0x10){})
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CreateBitField (B000, 0x80, F000)
        CH04 (__METHOD__, 0x00, 0x36, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_BUFFER_LIMIT */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CreateByteField (B000, 0x10, F001)
        CH04 (__METHOD__, 0x00, 0x36, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_BUFFER_LIMIT */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CreateWordField (B000, 0x0F, F002)
        CH04 (__METHOD__, 0x00, 0x36, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_BUFFER_LIMIT */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CreateDWordField (B000, 0x0D, F003)
        CH04 (__METHOD__, 0x00, 0x36, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_BUFFER_LIMIT */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CreateQWordField (B000, 0x09, F004)
        CH04 (__METHOD__, 0x00, 0x36, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_BUFFER_LIMIT */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CreateField (B000, 0x7F, 0x02, F005)
        CH04 (__METHOD__, 0x00, 0x36, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_BUFFER_LIMIT */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CreateField (B000, 0x78, 0x09, F006)
        CH04 (__METHOD__, 0x00, 0x36, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_BUFFER_LIMIT */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CreateField (B000, 0x80, 0x01, F007)
        CH04 (__METHOD__, 0x00, 0x36, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_BUFFER_LIMIT */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CreateField (B000, 0x79, 0x08, F008)
        CH04 (__METHOD__, 0x00, 0x36, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_BUFFER_LIMIT */
    }

    Method (MDBE, 0, NotSerialized)
    {
        MDBC ()
        MDBD ()
    }
