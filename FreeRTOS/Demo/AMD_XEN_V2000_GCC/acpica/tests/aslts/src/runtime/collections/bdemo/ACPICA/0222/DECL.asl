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
     * Bug 222:
     *
     * SUMMARY: Alternating access to OpRegions of different Address Spaces issue
     */
    Method (M10A, 0, Serialized)
    {
        Method (CHCK, 3, NotSerialized)
        {
            If ((Arg0 != Arg1))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg0, Arg1)
            }
        }

        OperationRegion (OPR0, SystemMemory, 0x00, 0x01)
        OperationRegion (OPR1, SystemIO, 0x00, 0x01)
        Field (OPR0, ByteAcc, NoLock, Preserve)
        {
            F000,   8
        }

        Field (OPR1, ByteAcc, NoLock, Preserve)
        {
            F001,   8
        }

        F000 = 0x5A
        CHCK (F000, 0x5A, 0x00)
        F001 = 0xC3
        CHCK (F001, 0xC3, 0x01)
        CHCK (F000, 0x5A, 0x02)
        CHCK (F001, 0xC3, 0x03)
    }
