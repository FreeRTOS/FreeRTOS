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
     * Bug 121:
     *
     * SUMMARY: Crash on attempt to deal with the invalid BufferFields (zero NumBits passed to CreateField)
     *
     * This DECL.asl is for AML Interpreter, it should result in exceptions for this DECL.asl.
     */
    Method (MF03, 0, Serialized)
    {
        Name (B000, Buffer (0x02)
        {
             0xFF, 0xFF                                       // ..
        })
        Name (I000, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CreateField (B000, 0x00, 0x10, BF00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CreateField (B000, 0x00, I000, BF01)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CreateField (B000, 0x01, I000, BF02)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CreateField (B000, 0x07, I000, BF03)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CreateField (B000, 0x08, I000, BF04)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CreateField (B000, 0x0F, I000, BF05)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CreateField (B000, 0x10, I000, BF06)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Debug = "All CreateField-s finished"
        Debug = BF00 /* \MF03.BF00 */
        Debug = BF01 /* \MF03.BF01 */
        Debug = BF02 /* \MF03.BF02 */
        Debug = BF03 /* \MF03.BF03 */
        Debug = BF04 /* \MF03.BF04 */
        Debug = BF05 /* \MF03.BF05 */
        Debug = BF06 /* \MF03.BF06 */
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        Debug = "All Store-to-Debug-s finished"
    }
