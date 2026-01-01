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
     * Data type conversion and manipulation
     *
     * Convert Integer to BCD
     * Convert BCD To Integer
     */
    /* 32-bit */
    Name (P352, Package (0x0C)
    {
        0x00,
        0x01,
        0x0C,
        0x0159,
        0x1A85,
        0x3039,
        0x000A5BF5,
        0x0023CACE,
        0x055F2CC0,
        0x05F5E0FF,
        0xFF,
        0xFFFF
    })
    Name (P353, Package (0x0C)
    {
        0x00,
        0x01,
        0x12,
        0x0345,
        0x6789,
        0x00012345,
        0x00678901,
        0x02345678,
        0x90123456,
        0x99999999,
        0x0255,
        0x00065535
    })
    /* 64-bit */

    Name (P354, Package (0x0A)
    {
        0x1E89CAA5,
        0x00000002540BE3FF,
        0x00000002540BE400,
        0x00000007037F7916,
        0x0000001CBE991A14,
        0x00000324D8AE5F79,
        0x0000185D4D9097A5,
        0x00007048860DDF79,
        0x000D76162EE9EC35,
        0x002386F26FC0FFFF
    })
    Name (P355, Package (0x0A)
    {
        0x0000000512346789,
        0x0000009999999999,
        0x0000010000000000,
        0x0000030123456790,
        0x0000123456789012,
        0x0003456789012345,
        0x0026789012346789,
        0x0123456789012345,
        0x3789012345678901,
        0x9999999999999999
    })
    Method (BCD1, 0, Serialized)
    {
        Debug = "TEST: BCD1, Convert Integer to BCD"
        If ((F64 == 0x01))
        {
            M302 (__METHOD__, 0x0C, "p352", P352, P353, 0x05)
            M302 (__METHOD__, 0x0A, "p354", P354, P355, 0x05)
        }
        Else
        {
            M302 (__METHOD__, 0x0C, "p352", P352, P353, 0x05)
        }
    }

    Method (BCD2, 0, Serialized)
    {
        Debug = "TEST: BCD2, Convert BCD To Integer"
        If ((F64 == 0x01))
        {
            M302 (__METHOD__, 0x0C, "p353", P353, P352, 0x06)
            M302 (__METHOD__, 0x0A, "p355", P355, P354, 0x06)
        }
        Else
        {
            M302 (__METHOD__, 0x0C, "p353", P353, P352, 0x06)
        }
    }

    /* Run-method */

    Method (BCD0, 0, NotSerialized)
    {
        BCD1 ()
        BCD2 ()
    }
