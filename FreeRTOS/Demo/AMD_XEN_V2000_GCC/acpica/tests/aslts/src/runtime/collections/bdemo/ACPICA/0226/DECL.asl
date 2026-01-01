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
     * Bug 226:
     *
     * SUMMARY: Excessive data is written to the Data field if
     *          it is wider than Access Width of the IndexField
     */
    Method (M10E, 0, Serialized)
    {
        OperationRegion (OPR0, SystemMemory, 0x00, 0x0100)
        Field (OPR0, ByteAcc, NoLock, WriteAsZeros)
        {
            IDX0,   8,
            DTA0,   24
        }

        Field (OPR0, ByteAcc, NoLock, Preserve)
        {
            TOT0,   32
        }

        IndexField (IDX0, DTA0, ByteAcc, NoLock, WriteAsZeros)
        {
                ,   15,
            IDF0,   1
        }

        IDF0 = 0x03FF
        Local0 = TOT0 /* \M10E.TOT0 */
        If ((Local0 != 0x8001))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x8001)
        }
    }

    Method (M17A, 0, Serialized)
    {
        Name (B000, Buffer (0x40){})
        Name (B001, Buffer (0x08)
        {
             0xF0, 0xDE, 0xBC, 0x9A, 0x00, 0x00, 0x00, 0x00   // ........
        })
        CreateQWordField (B000, 0x05, BF00)
        BF00 = 0x123456789ABCDEF0
        If (F64)
        {
            If ((BF00 != 0x123456789ABCDEF0))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF00, 0x123456789ABCDEF0)
            }
        }
        ElseIf ((BF00 != B001))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF00, B001)
        }
    }
