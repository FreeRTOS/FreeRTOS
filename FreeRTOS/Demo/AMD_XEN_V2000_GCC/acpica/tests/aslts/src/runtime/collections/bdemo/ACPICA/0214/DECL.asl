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
     * Bug 214 (local-bugzilla-350):
     *
     *
     * SUMMARY: crash of AcpiExec on repeated CopyObject of OpRegion
     *
     * Repeated duplication of an OpRegion to another
     * dynamic OpRegion by CopyObject ASL operator causes
     * crash of AcpiExec.
     */
    Method (M81C, 0, Serialized)
    {
        Method (M000, 1, Serialized)
        {
            OperationRegion (OPR0, SystemMemory, 0x00, 0x10)
            CopyObject (Arg0, OPR0) /* \M81C.M000.OPR0 */
        }

        OperationRegion (OPR1, SystemMemory, 0x00, 0x10)
        Method (M001, 0, Serialized)
        {
            Field (OPR1, ByteAcc, NoLock, WriteAsZeros)
            {
                RFU0,   8
            }

            RFU0 = 0x01
            M000 (OPR1)
            If ((RFU0 != 0x01))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, RFU0, 0x01)
            }

            RFU0 = 0x02
            M000 (OPR1)
            If ((RFU0 != 0x02))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, RFU0, 0x02)
            }

            RFU0 = 0x03
            M000 (OPR1)
            If ((RFU0 != 0x03))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, RFU0, 0x03)
            }

            RFU0 = 0x04
            If ((RFU0 != 0x04))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, RFU0, 0x04)
            }
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        M001 ()
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }
