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
     * DynObj: Exceptions
     */
    Name (Z132, 0x84)
    /* Check exceptions */

    Method (M374, 0, Serialized)
    {
        /* Package for _TCI-begin statistics */
        /* (use NamedX, don't use ArgX/LocalX). */
        Name (PP0A, Package (0x01){})
        Method (M000, 1, NotSerialized)
        {
            Divide (0x01, Arg0, Local0, Local1)
        }

        /* Create and initialize the Memory Consumption Statistics Packages */

        Local1 = M3A0 (C200)   /* _TCI-end statistics */
        PP0A = M3A0 (C201)     /* _TCI-begin statistics */
        Local3 = M3A0 (0x00)      /* difference */
        SET0 (Z132, __METHOD__, 0x00)
        If (RN00)
        {
            CH03 (__METHOD__, Z132, __LINE__, 0x00, 0x00)
            _TCI (C200, Local1)
            M000 (0x00)
            _TCI (C201, PP0A)
            CH04 (__METHOD__, 0x00, 0xFF, Z132, __LINE__, 0x00, 0x00)
            M3A3 (Local1, PP0A, Local3)
            M3A4 (Local1, PP0A, Local3, 0x00, 0x00, 0x00, 0x00)
        }

        RST0 ()
    }
