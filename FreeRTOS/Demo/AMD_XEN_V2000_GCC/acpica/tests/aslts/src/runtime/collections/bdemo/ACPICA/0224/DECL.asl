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
     * Bug 224:
     *
     * SUMMARY: AcpiExec is unable to emulate access to IndexField Object
     */
    Method (M10C, 0, Serialized)
    {
        OperationRegion (OPR0, SystemMemory, 0x00, 0x0100)
        Method (CHCK, 3, NotSerialized)
        {
            If ((Arg0 != Arg1))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg0, Arg1)
            }
        }

        Field (OPR0, WordAcc, NoLock, WriteAsZeros)
        {
            IDX0,   16,
            DTA0,   16
        }

        IndexField (IDX0, DTA0, WordAcc, NoLock, WriteAsZeros)
        {
            IDF0,   8,
                ,   4,
            IDF1,   8,
            IDF2,   8,
            Offset (0x04),
            IDF3,   8
        }

        Method (M000, 3, NotSerialized)
        {
            Local0 = RefOf (Arg1)
            DerefOf (Local0) = Arg2
            Local1 = DerefOf (Arg1)
            CHCK (Local1, Arg2, Arg0)
        }

        Method (M001, 3, NotSerialized)
        {
            Local1 = DerefOf (Arg1)
            CHCK (Local1, Arg2, Arg0)
        }

        M000 (0x00, RefOf (IDF0), 0x12)
        M000 (0x01, RefOf (IDF1), 0x34)
        M000 (0x02, RefOf (IDF2), 0x56)
        M000 (0x03, RefOf (IDF3), 0x78)
        M000 (0x04, RefOf (IDF0), 0x12)
        M000 (0x05, RefOf (IDF1), 0x34)
        M000 (0x06, RefOf (IDF2), 0x56)
        M000 (0x07, RefOf (IDF3), 0x78)
    }
