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
     * Bug 134:
     *
     * SUMMARY: Writing RefOf reference from inside Method breaks effectively local Arg
     */
    Method (MF23, 7, NotSerialized)
    {
        Debug = "LocalX case of Method started:"
        Local0 = RefOf (ID14)
        Local1 = Local0
        Local2 = Local1
        Local3 = Local2
        Local4 = Local3
        Local5 = Local4
        Local6 = Local5
        Local6 = DerefOf (Local0)
        Debug = Local6
        If ((Local6 != 0x11))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local6, 0x11)
        }

        Debug = "LocalX case of Method finished"
    }

    Method (MF24, 7, NotSerialized)
    {
        Debug = "ArgX case (1) of Method started:"
        Arg0 = RefOf (ID14)
        Arg1 = Arg0
        Arg2 = Arg1
        Arg3 = Arg2
        Arg4 = Arg3
        Arg5 = Arg4
        Arg6 = Arg5
        Arg6 = DerefOf (Arg0)
        Debug = Arg6
        If ((Arg6 != 0x11))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg6, 0x11)
        }

        Debug = "ArgX case (1) of Method finished"
    }

    Method (MF25, 7, NotSerialized)
    {
        Debug = "ArgX case (2) of Method started:"
        Local0 = RefOf (ID14)
        Arg1 = Local0
        Arg2 = Local0
        Arg3 = Local0
        Arg4 = Local0
        Arg5 = Local0
        Arg6 = Local0
        Arg6 = DerefOf (Arg0)
        Debug = Arg6
        If ((Arg6 != 0x11))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg6, 0x11)
        }

        Debug = "ArgX case (2) of Method finished"
    }

    Method (MF26, 0, NotSerialized)
    {
        SRMT ("mf23")
        MF23 (ID14, ID15, ID16, ID17, ID18, ID19, ID1A)
        SRMT ("mf24")
        If (Y134)
        {
            MF24 (ID14, ID15, ID16, ID17, ID18, ID19, ID1A)
        }
        Else
        {
            BLCK ()
        }

        SRMT ("mf25")
        If (Y134)
        {
            MF25 (ID14, ID15, ID16, ID17, ID18, ID19, ID1A)
        }
        Else
        {
            BLCK ()
        }
    }
