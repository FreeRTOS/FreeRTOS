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
     * Bug 139:
     *
     * SUMMARY: DeRefof and Store operations on 64-bit Integers of 32-bit AML table has been loaded modify them
     *
     * ROOT CAUSE
     */
    Method (MF2A, 0, NotSerialized)
    {
        If ((ID1B != 0xFEDCBA9876543210))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, ID1B, 0xFEDCBA9876543210)
        }
        Else
        {
            Debug = "Ok, initially id1b = 0xfedcba9876543210"
            Debug = "Store(id1b, Local0)"
            Local0 = ID1B /* \ID1B */
            If ((ID1B != 0xFEDCBA9876543210))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, ID1B, 0xFEDCBA9876543210)
            }
        }
    }

    Method (MF2B, 0, NotSerialized)
    {
        Debug = "Store(Refof(id1c), Local0)"
        Local0 = RefOf (ID1C)
        If ((ID1C != 0xFEDCBA9876543211))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, ID1C, 0xFEDCBA9876543211)
        }
        Else
        {
            Debug = "Ok, initially id1c = 0xfedcba9876543211"
            Debug = "DeRefof(Local0)"
            Local1 = DerefOf (Local0)
            If ((ID1C != 0xFEDCBA9876543211))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, ID1C, 0xFEDCBA9876543211)
            }
        }
    }
