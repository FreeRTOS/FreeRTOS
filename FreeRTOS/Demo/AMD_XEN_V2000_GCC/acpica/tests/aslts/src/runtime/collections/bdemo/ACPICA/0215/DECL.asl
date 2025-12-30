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
     * Bug 215 (local-bugzilla-351):
     *
     * SUMMARY: exception on accessing IndexField with IndexName Region Field exceeding 32 bits
     *
     * Exception AE_BUFFER_OVERFLOW unexpectedly
     * occurs on access to an IndexField object if
     * the length of the respective IndexName Region
     * Field exceeds 32 bits.
     */
    Method (M81D, 0, NotSerialized)
    {
        Method (M000, 0, Serialized)
        {
            OperationRegion (OPR0, SystemMemory, 0x00, 0x30)
            Field (OPR0, ByteAcc, NoLock, Preserve)
            {
                IDX0,   32,
                DTA0,   32
            }

            Field (OPR0, ByteAcc, NoLock, Preserve)
            {
                Offset (0x08),
                IDX1,   32,
                Offset (0x10),
                DTA1,   33
            }

            Field (OPR0, ByteAcc, NoLock, Preserve)
            {
                Offset (0x18),
                IDX2,   33,
                Offset (0x20),
                DTA2,   32
            }

            IndexField (IDX0, DTA0, ByteAcc, NoLock, Preserve)
            {
                IDF0,   1
            }

            IndexField (IDX1, DTA1, ByteAcc, NoLock, Preserve)
            {
                IDF1,   1
            }

            IndexField (IDX2, DTA2, ByteAcc, NoLock, Preserve)
            {
                IDF2,   1
            }

            IDF0 = 0x01
            If ((IDF0 != 0x01))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, IDF0, 0x01)
            }

            IDF1 = 0x01
            If ((IDF1 != 0x01))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, IDF1, 0x01)
            }

            IDF2 = 0x01
            If ((IDF2 != 0x01))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, IDF2, 0x01)
            }
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        M000 ()
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }
