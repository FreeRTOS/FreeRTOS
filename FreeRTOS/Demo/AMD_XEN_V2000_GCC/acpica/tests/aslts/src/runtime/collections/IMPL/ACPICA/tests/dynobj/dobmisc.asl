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
     * DynObj: miscellaneous tests
     */
    Name (Z140, 0x8C)
    Method (M375, 0, Serialized)
    {
        /* The Created Objects benchmark Package */

        Name (PP00, Package (0x01){})
        /* The Deleted Objects benchmark Package */

        Name (PP01, Package (0x01){})
        /* The per-memory type benchmark Package */

        Name (PP02, Package (0x01){})
        /* Package for _TCI-begin statistics */
        /* (use NamedX, don't use ArgX/LocalX). */
        Name (PP0A, Package (0x01){})
        /* Create and initialize the Memory Consumption Statistics Packages */

        Local0 = M3A0 (C200)   /* _TCI-end statistics */
        PP0A = M3A0 (C201)     /* _TCI-begin statistics */
        Local1 = M3A0 (0x00)      /* difference */
        SET0 (Z140, "m375", 0x00)
        /* Start of all sub-tests */

        Debug = "Test misc 0"
        _TCI (C200, Local0)
        /* ASL-construction being investigated */
        /* to be implemented, now arbitrary operation only */
        Store ((0x00 + 0x01), Local2)
        /* Use NamedX for _TCI-begin statistics Package */
        /* not to touch the LOCAL_REFERENCE entry. */
        _TCI (C201, PP0A)
        M3A3 (Local0, PP0A, Local1) /* calculate difference */
        /* Verify result */
        /* Is not correct yet !!! */
        PP00 = M3A8 ()
        PP00 [C009] = 0x02 /* Integer */
        M3A4 (Local0, PP0A, Local1, PP00, 0x00, 0x00, 0x04)
        /* End of all sub-tests */

        RST0 ()
    }
