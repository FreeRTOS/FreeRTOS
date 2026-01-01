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
     * Bug 221:
     *
     * SUMMARY: AcpiExec improper emulates alternating access to OpRegions
     *          covering different ranges
     */
    Method (M109, 0, Serialized)
    {
        Method (CHCK, 3, NotSerialized)
        {
            If ((Arg0 != Arg1))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg0, Arg1)
            }
        }

        OperationRegion (OPR0, SystemMemory, 0x00, 0x02)
        OperationRegion (OPR1, SystemMemory, 0x00, 0x01)
        OperationRegion (OPR2, SystemMemory, 0x01, 0x01)
        Field (OPR0, ByteAcc, NoLock, Preserve)
        {
            F000,        /* Byte 0 */   8,
            F001,        /* Byte 1 */   8
        }

        Field (OPR1, ByteAcc, NoLock, Preserve)
        {
            F002,        /* Byte 0 */   8
        }

        Field (OPR2, ByteAcc, NoLock, Preserve)
        {
            F003,        /* Byte 1 */   8
        }

        F001 = 0x5A   /* Byte 1 */
        CHCK (F001, 0x5A, 0x00)
        F002 = 0xC3   /* Byte 0 */
        CHCK (F002, 0xC3, 0x01)
        CHCK (F000, 0xC3, 0x02) /* Byte 0 */
        CHCK (F001, 0x5A, 0x03) /* Byte 1 */
        CHCK (F003, 0x5A, 0x04) /* Byte 1 */
    }
