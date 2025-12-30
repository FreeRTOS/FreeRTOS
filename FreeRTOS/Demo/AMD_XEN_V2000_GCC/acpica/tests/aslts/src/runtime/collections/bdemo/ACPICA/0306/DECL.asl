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
     * Bug 306:
     *
     * SUMMARY: Complex indirect storing to a LocalX violates the Writing to LocalX Rule
     */
    Method (MFF3, 0, NotSerialized)
    {
        Method (M000, 1, NotSerialized)
        {
            Arg0 = 0x12345678
            Arg0 = "87654321"
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = 0x12345678
        Local0 = "87654321"
        If ((ObjectType (Local0) != 0x02))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, ObjectType (Local0), 0x02)
        }

        M000 (RefOf (Local1))
        If ((ObjectType (Local1) != 0x02))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, ObjectType (Local1), 0x02)
        }

        Local3 = RefOf (Local2)
        Local4 = RefOf (Local3)
        DerefOf (Local4) = 0x12345678
        DerefOf (Local4) = "87654321"
        If ((ObjectType (Local2) != 0x02))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, ObjectType (Local2), 0x02)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }
