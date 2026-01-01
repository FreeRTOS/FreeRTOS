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
     * Bug 130:
     *
     * SUMMARY: Reference to String works differently to like the references to Buffer and Package work
     */
    Method (MF19, 1, NotSerialized)
    {
        Local2 = DerefOf (Arg0)
        Local2 [0x01] = 0x2B
        /*		Store(0x2b, Index(DerefOf(arg0), 1)) */
    }

    Method (MF1A, 1, NotSerialized)
    {
        Local0 = RefOf (Arg0)
        MF19 (Local0)
    }

    Method (MF1B, 0, NotSerialized)
    {
        /* Index of String */

        MF1A (SD04)
        If ((SD04 != "qwer0000"))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, SD04, "qwer0000")
        }

        /* Index of Buffer */

        MF1A (BD08)
        If ((BD08 != Buffer (0x04)
                    {
                         0x01, 0x77, 0x03, 0x04                           // .w..
                    }))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BD08, Buffer (0x04)
                {
                     0x01, 0x77, 0x03, 0x04                           // .w..
                })
        }

        /* Index of Package */

        MF1A (PD0D)
        Local0 = PD0D [0x01]
        Local1 = DerefOf (Local0)
        If ((Local1 != 0x77))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, 0x77)
        }
    }
