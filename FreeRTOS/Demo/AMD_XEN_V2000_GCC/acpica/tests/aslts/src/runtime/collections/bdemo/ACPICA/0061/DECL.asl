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
     * Bug 0061:
     *
     * SUMMARY: Crash on Store the OperationRegion result returned by Method
     *
     * Methods return the object of type OperationRegion
     * and just this causes the problems.
     */
    Method (M206, 2, NotSerialized)
    {
        If (SLCK)
        {
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        }
        Else
        {
            CH04 (__METHOD__, 0x00, 0x2F, 0x00, __LINE__, 0x00, 0x00)
        }
    }

    Method (ME02, 0, NotSerialized)
    {
        Local0 = 0x00
        /* Store directly a region should not be allowed. */
        /*
         // Removed 09/2015
         CH03("", 0, 0x000, __LINE__, 0)
         Store(rd01, Local7)
         m206(0x001, 0x002)
         */
        Return (Local0)
    }

    Method (ME03, 0, NotSerialized)
    {
        Debug = "============= Start of test"
        Local0 = ME02 ()
        Debug = "============= Finish of test"
    }

    Method (ME04, 0, NotSerialized)
    {
        Local0 = 0x00
        /* Store directly a region should not be allowed. */
        /*
         // Removed 09/2015
         CH03("", 0, 0x003, __LINE__, 0)
         Store(rd02, Local7)
         m206(0x004, 0x005)
         */
        Return (Local0)
    }

    Method (ME05, 0, NotSerialized)
    {
        Debug = "me05, point 0"
        Local0 = ME04 ()
        Debug = "me05, point 1"
        Local1 = ME04 ()
        Debug = "me05, point 2"
    }

    Method (ME06, 0, NotSerialized)
    {
        Debug = "============= me05 0"
        ME05 ()
        Debug = "============= me05 1"
        ME05 ()
        Debug = "============= me05 2"
        ME05 ()
        /* The message below doesn't appear */

        Debug = "============= me05 3"
        ID09 = 0x01
    }

    Method (ME07, 0, NotSerialized)
    {
        ID09 = 0x00
        ME03 ()
        ME06 ()
        If ((ID09 != 0x01))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, ID09, 0x01)
        }
    }
