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
     * Bug 115:
     *
     * SUMMARY: Unexpected dereference of Index reference returned by Method and immediately passed to another Method
     */
    Method (ME7E, 2, NotSerialized)
    {
        Debug = Arg0
        Arg0 = Arg1
    }

    Method (ME7F, 0, NotSerialized)
    {
        Return (PD04 [0x00])
    }

    Method (ME80, 0, NotSerialized)
    {
        Store (PD05 [0x00], Local0)
        Return (Local0)
    }

    Method (ME81, 0, NotSerialized)
    {
        Return (Local0 = PD06 [0x00])
    }

    Method (ME82, 0, NotSerialized)
    {
        Local0 = PD07 [0x00]
        Return (Local0)
    }

    Method (ME83, 0, NotSerialized)
    {
        Local1 = Local0 = PD08 [0x00]
        Return (Local0)
    }

    Method (ME84, 0, NotSerialized)
    {
        Local1 = Local0 = PD09 [0x00]
        Return (Local1)
    }

    Method (ME85, 0, NotSerialized)
    {
        Return (RefOf (ID10))
    }

    Method (ME86, 0, Serialized)
    {
        Name (PRN0, 0x00)
        /* To show: the RefOf reference is actually passed to method (Ok) */

        If (PRN0)
        {
            Debug = ME85 ()
        }

        Local0 = 0xABCD0000
        ME7E (ME85 (), Local0)
        If ((ID10 != Local0))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, ID10, Local0)
        }

        /* To show: all methods return Index references (Ok) */

        If (PRN0)
        {
            Debug = ME7F ()
            Debug = ME80 ()
            Debug = ME81 ()
            Debug = ME82 ()
            Debug = ME83 ()
            Debug = ME84 ()
        }

        /* To show: passed to methods are objects but */
        /* not Index references to them as expected (Bug) */
        Local0 = 0xABCD0001
        ME7E (ME7F (), Local0)
        Local1 = DerefOf (PD04 [0x00])
        If ((Local1 != Local0))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, Local0)
        }

        Local0 = 0xABCD0002
        ME7E (ME80 (), Local0)
        Local1 = DerefOf (PD05 [0x00])
        If ((Local1 != Local0))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, Local0)
        }

        Local0 = 0xABCD0003
        ME7E (ME81 (), Local0)
        Local1 = DerefOf (PD06 [0x00])
        If ((Local1 != Local0))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, Local0)
        }

        Local0 = 0xABCD0004
        ME7E (ME82 (), Local0)
        Local1 = DerefOf (PD07 [0x00])
        If ((Local1 != Local0))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, Local0)
        }

        Local0 = 0xABCD0005
        ME7E (ME83 (), Local0)
        Local1 = DerefOf (PD08 [0x00])
        If ((Local1 != Local0))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, Local0)
        }

        Local0 = 0xABCD0006
        ME7E (ME84 (), Local0)
        Local1 = DerefOf (PD09 [0x00])
        If ((Local1 != Local0))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, Local0)
        }
    }
