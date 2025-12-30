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
     * Bug 298:
     *
     * SUMMARY: AcpiExOpcode_XA_XT_XR routines assign addresses of released cache objects to WalkState->ResultObj causing further problems
     *
     * Note: appearance of bug greatly depends on the memory cache dynamics
     *
     *       So, PASS of this test doesn't mean yet that the root cause of the problem
     *       has been resolved.
     */
    Mutex (MX00, 0x00)
    Mutex (MX01, 0x01)
    Mutex (MX02, 0x02)
    Mutex (MX03, 0x03)
    Name (P000, Package (0x01)
    {
        0x67890000
    })
    Method (M1E7, 0, NotSerialized)
    {
        Local0 = 0x0123
        Acquire (MX03, 0x0100)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Acquire (MX02, 0x0100)
        CH04 (__METHOD__, 0x00, 0x40, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_MUTEX_ORDER */
        Local2 = RefOf (P000) /* L0(0x004d5ec8, 0x123), L2 (0x004d5dc8, res of RefOf) */
        Local3 = DerefOf (Local2)
        Debug = "Sit 1: Local2 contains bad object there!!!!!"
        Local5 = (0xABCD0000 && 0xABCD0001)
        Local0-- /* L0(0x004d5ec8, 0x123), L2 (0x004d5dc8, 0xCACA) */
        Debug = "============================== 0"
        Debug = Local0
        Debug = "============================== 1"
        Local2 = RefOf (P000)
        Debug = "============================== 2"
        Local4 = (Local0 + 0x11111111)
        Debug = Local4
        If ((Local4 != 0x11111233))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local4, 0x11111233)
        }

        Debug = "============================== 3"
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        /*
         * The problem is not automatically detected,
         * so remove this error report after the problem has been resolved.
         */
        ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
    }
