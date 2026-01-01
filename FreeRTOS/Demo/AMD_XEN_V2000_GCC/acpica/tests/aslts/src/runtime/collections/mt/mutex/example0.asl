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
     * Example 0 (from some particular failed table)
     *
     * arg0 - ID of current thread
     * arg1 - Index of current thread
     * arg2 - Integer
     * arg3 - Integer
     * arg4 - Integer
     */
    Method (C0A2, 5, Serialized)
    {
        OperationRegion (C0A3, SystemIO, C0A1 (), 0x07)
        Field (C0A3, ByteAcc, NoLock, Preserve)
        {
            C0A4,   8,
            C0A5,   8,
            C0A6,   8,
            C0A7,   8,
            C0A8,   8,
            C0A9,   8,
            C0AA,   8
        }

        M310 (Arg0, Arg1, GLLL, GLIX, 0x00, 0x00, 0x00) /* Acquire */
        Local0 = 0x10
        While (Local0)
        {
            Local1 = C0A4 /* \C0A2.C0A4 */
            M207 (Arg1, 0x64) /* Stall */
            Local0--
        }

        Local0 = 0x01
        If (Local0)
        {
            C0A7 = Arg3
            C0A8 = Arg2
            If (((Arg2 & 0x01) == 0x00))
            {
                C0A9 = Arg4
            }

            C0A4 = 0xFF
            C0A6 = 0x48
            Local0 = 0x0B
            While (Local0)
            {
                Local1 = C0A4 /* \C0A2.C0A4 */
                M207 (Arg1, 0x64) /* Stall */
                Local0--
            }

            Local1 = (C0A4 & 0x1C)
            C0A4 = 0xFF
            If (((Local1 == 0x00) && (Arg2 & 0x01)))
            {
                Local2 = C0A9 /* \C0A2.C0A9 */
            }
        }
        Else
        {
            Local1 = 0x01
        }

        M311 (Arg0, Arg1, GLLL, GLIX, 0x00, 0x00) /* Release */
        Return (Local1)
    }

    Method (C0A1, 0, Serialized)
    {
        Return (0x0100)
    }

    /*
     * arg0 - ID of current thread
     * arg1 - Index of current thread
     */
    Method (C0AB, 2, NotSerialized)
    {
        M310 (Arg0, Arg1, GLLL, GLIX, 0x00, 0x00, 0x00) /* Acquire */
        Local0 = 0x10
        While (Local0)
        {
            M207 (Arg1, 0x32) /* Stall */
            Local0--
        }

        M311 (Arg0, Arg1, GLLL, GLIX, 0x00, 0x00) /* Release */
    }
