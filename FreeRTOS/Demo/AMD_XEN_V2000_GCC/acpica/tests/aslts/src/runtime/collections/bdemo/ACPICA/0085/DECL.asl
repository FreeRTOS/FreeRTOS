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
     * Bug 0085:
     *
     * SUMMARY: Exception on DeRefOf operator applied to IRef to Uninitialized element of Package
     */
    /* Uninitialized element of Package */
    Method (ME37, 0, Serialized)
    {
        /* Ref #1 */

        Name (P000, Package (0x01){})
        Local1 = DerefOf (P000 [0x00])
        Local0 = P000 [0x00]
        Debug = Local0
        Local1 = DerefOf (Local0)
        Local0 = P000 [0x00]
        Debug = Local0
    }

    /* Reference to Uninitialized Local */

    Method (ME38, 1, NotSerialized)
    {
        If (0x01)
        {
            /* Ref #2 */

            Debug = Arg0
            Local1 = DerefOf (Arg0)
            CH04 (__METHOD__, 0x02, 0x3E, 0x01, __LINE__, 0x00, 0x00)
        }
        Else
        {
            DerefOf (Arg0)++
        }
    }

    Method (ME39, 1, NotSerialized)
    {
        If (Arg0)
        {
            Local0 = 0x00
        }

        ME38 (RefOf (Local0))
    }

    Method (ME3A, 0, NotSerialized)
    {
        ME37 ()
        ME39 (0x00)
    }
