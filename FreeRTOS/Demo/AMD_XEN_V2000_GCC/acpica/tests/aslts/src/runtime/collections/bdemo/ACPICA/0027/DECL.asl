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
     * Bug 0027:
     *
     * SUMMARY: Crash of ObjectType for the particular BufferFields
     *
     * Crash on ObjectType() in different conditions depending on F64.
     * Test remained as is (due to crash as a main symptom).
     */
    Method (MDBB, 0, Serialized)
    {
        Name (B001, Buffer (0xC8){})
        If ((F64 == 0x01))
        {
            /*//////////////// 64-bit mode //////////////////////////// */
            /* Field(1,71) - before the critical field */
            CreateField (B001, 0x01, 0x47, F004)
            Local0 = ObjectType (F004)
            Debug = "ObjectType of f004(1,71) field is equal to:"
            Debug = Local0
            /* Field(1,73) - after the critical field */

            CreateField (B001, 0x01, 0x49, F005)
            Local0 = ObjectType (F005)
            Debug = "ObjectType of f005(1,73) field is equal to:"
            Debug = Local0
            /* Field(1,72) - the field crashes the ACPICA in 64-bit mode */

            CreateField (B001, 0x01, 0x48, F006)
            Debug = "Before running ObjectType of f006(1,72) field."
            Local0 = ObjectType (F006)
            Debug = "ObjectType of f006(1,72) field is equal to:"
            Debug = Local0
        }
        Else
        {
            /*//////////////// 32-bit mode //////////////////////////// */
            /* Field(1,39) - before the critical field */
            CreateField (B001, 0x01, 0x27, F001)
            Local0 = ObjectType (F001)
            Debug = "ObjectType of f001(1,39) field is equal to:"
            Debug = Local0
            /* Field(1,41) - after the critical field */

            CreateField (B001, 0x01, 0x29, F002)
            Local0 = ObjectType (F002)
            Debug = "ObjectType of f002(1,41) field is equal to:"
            Debug = Local0
            /* Field(1,40) - the field crashes the ACPICA in 64-bit mode */

            CreateField (B001, 0x01, 0x28, F003)
            Debug = "Before running ObjectType of f003(1,40) field."
            Local0 = ObjectType (F003)
            Debug = "ObjectType of f003(1,40) field is equal to:"
            Debug = Local0
        }
    }
