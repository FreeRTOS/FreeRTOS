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
     * Bug 133:
     *
     * SUMMARY: The Write access automatic dereference for Index reference doesn't work
     */
    Method (MF21, 1, NotSerialized)
    {
        Arg0 = 0x77
    }

    Method (MF22, 0, NotSerialized)
    {
        /* Writing by RefOf reference to Integer */

        Local0 = RefOf (ID13)
        MF21 (Local0)
        If ((ID13 != 0x77))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, ID13, 0x77)
        }

        /* Writing by Index to String */

        Local0 = SD05 [0x01]
        MF21 (Local0)
        If ((SD05 != "qwer0000"))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, SD05, "qwer0000")
        }

        /* Writing by Index to Buffer */

        Local0 = BD09 [0x01]
        MF21 (Local0)
        If ((BD09 != Buffer (0x04)
                    {
                         0x01, 0x77, 0x03, 0x04                           // .w..
                    }))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BD09, Buffer (0x04)
                {
                     0x01, 0x77, 0x03, 0x04                           // .w..
                })
        }

        /* Writing by Index to Package */

        Local0 = PD0F [0x01]
        MF21 (Local0)
        Local0 = PD0F [0x01]
        Local1 = DerefOf (Local0)
        If ((Local1 != 0x77))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, 0x77)
        }
    }
