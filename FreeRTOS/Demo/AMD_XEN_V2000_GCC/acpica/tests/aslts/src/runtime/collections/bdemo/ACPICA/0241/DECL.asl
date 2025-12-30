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
     * Bug 241:
     *
     * SUMMARY: Crash of AML interpreter after an exception in
     *          AcpiExReadDataFromField called from AcpiExResolveObjectToValue
     *
     * Note. The crash occurred when acpiexec is compiled in DEBUG mode.
     * July 2013: Problem is fixed with change for DeRefOf operator with FieldUnits.
     */
    Method (M129, 0, NotSerialized)
    {
        Method (M000, 1, Serialized)
        {
            OperationRegion (RGN1, SystemMemory, 0x0200, Arg0)
            Field (RGN1, ByteAcc, NoLock, Preserve)
            {
                FU01,   2049
            }

            Local2 = RefOf (FU01)
            If (CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00))
            {
                Return (Zero)
            }

            /* Read, Access out of OpRegion */

            Local0 = DerefOf (Local2)
            /* Store above should cause 2 errors:
             * 1) AE_AML_REGION_LIMIT
             * 2) AE_AML_NO_RETURN_VALUE
             */
            If ((EXC0 == 0x02))
            {
                EXC0 = 0x01
            }

            CH04 (__METHOD__, 0x00, 0x3E, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_NO_RETURN_VALUE */
        }

        M000 (0x0100)
    }
