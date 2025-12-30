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
     * Bug 0029:
     *
     * SUMMARY: Looks, like Sleep (or Wait) spend less time than specified
     */
    Method (MDBF, 2, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                Local1 = Timer
                Sleep (Arg1)
                Local2 = Timer
                Local6 = (Local2 - Local1)
                Local4 = (Arg1 * 0x2710)
                If ((Local6 < Local4))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local6, Local4)
                }
            }
            Case (0x01)
            {
                Local1 = Timer
                Stall (Arg1)
                Local2 = Timer
                Local6 = (Local2 - Local1)
                Local4 = (Arg1 * 0x0A)
                If ((Local6 < Local4))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local6, Local4)
                }
            }
            Case (0x02)
            {
                Local1 = Timer
                Wait (ED00, Arg1)
                Local2 = Timer
                Local6 = (Local2 - Local1)
                Local4 = (Arg1 * 0x2710)
                If ((Local6 < Local4))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local6, Local4)
                }
            }

        }
    }

    /* Sleep */

    Method (MDC0, 0, NotSerialized)
    {
        MDBF (0x00, 0x0A)
        MDBF (0x00, 0x64)
        MDBF (0x00, 0x01F4)
        MDBF (0x00, 0x03E8)
        MDBF (0x00, 0x07D0)
    }

    /* Wait */

    Method (MDC1, 0, NotSerialized)
    {
        MDBF (0x02, 0x0A)
        MDBF (0x02, 0x64)
        MDBF (0x02, 0x03E8)
        MDBF (0x02, 0x07D0)
    }

    Method (MDC2, 0, NotSerialized)
    {
        MDC0 ()
        MDC1 ()
    }
