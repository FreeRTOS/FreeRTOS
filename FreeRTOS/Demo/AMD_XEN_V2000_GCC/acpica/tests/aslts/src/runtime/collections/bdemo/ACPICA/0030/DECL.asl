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
     * Bug 0030:
     *
     * SUMMARY: Crash of ObjectType for the particular Fields
     *
     * Crash. Test remained as is (due to crash as a main symptom).
     */
    Method (MDC3, 0, Serialized)
    {
        /* Field Unit */

        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        Field (R000, ByteAcc, NoLock, Preserve)
        {
            F000,   8,
            F001,   16,
            F002,   32,
            F003,   33,
            F004,   1,
            F005,   64
        }

        Debug = "------------ Fields:"
        Debug = F000 /* \MDC3.F000 */
        Debug = F001 /* \MDC3.F001 */
        Debug = F002 /* \MDC3.F002 */
        Debug = F003 /* \MDC3.F003 */
        Debug = F004 /* \MDC3.F004 */
        Debug = F005 /* \MDC3.F005 */
        Debug = "------------."
        Return (0x00)
    }

    Method (MDC4, 0, Serialized)
    {
        /* Field Unit */

        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        Field (R000, ByteAcc, NoLock, Preserve)
        {
            F000,   8,
            F001,   16,
            F002,   32,
            F003,   33,
            F004,   7,
            F005,   64
        }

        Debug = "------------ Fields:"
        Debug = F000 /* \MDC4.F000 */
        Debug = F001 /* \MDC4.F001 */
        Debug = F002 /* \MDC4.F002 */
        Debug = F003 /* \MDC4.F003 */
        Debug = F004 /* \MDC4.F004 */
        Debug = F005 /* \MDC4.F005 */
        Debug = "------------."
        Return (0x00)
    }

    Method (MDC5, 0, NotSerialized)
    {
        MDC3 ()
        MDC4 ()
        Return (0x00)
    }
