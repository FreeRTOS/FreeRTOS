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
     * Data type conversion and manipulation
     *
     * EISA ID String To Integer Conversion Macro
     */
    Name (P360, Package (0x0A)
    {
        0x23014304,
        0x6745A610,
        0xBC8A091D,
        0xFADE6C29,
        0xDEBCCF35,
        0x12F03242,
        0x5634954E,
        0x9A78F85A,
        0xDEBC4167,
        /* check uppercase requirement to the EISAID */
        /* form "UUUXXXX" (UUU - 3 uppercase letters) */
        0x23014304
    })
    Name (P361, Package (0x0A)
    {
        0x23014304,
        0x6745A610,
        0xBC8A091D,
        0xFADE6C29,
        0xDEBCCF35,
        0x12F03242,
        0x5634954E,
        0x9A78F85A,
        0xDEBC4167,
        0x23014304 /* 0x23014384 */
    })
    /* Run-method */

    Method (EIS0, 0, Serialized)
    {
        Debug = "TEST: EIS0, EISA ID String To Integer Conversion Macro"
        M302 (__METHOD__, 0x0A, "p360", P360, P361, 0x09)
    }
