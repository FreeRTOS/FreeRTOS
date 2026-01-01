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
     * SizeOf, Get the size of Integer, Buffer, String or Package
     */
    Name (Z041, 0x29)
    /* Simplest test of SizeOf for all available type objects */

    Method (M1EF, 0, Serialized)
    {
        Name (I000, 0x00)
        Name (S000, "vcd")
        Name (B000, Buffer (0x05)
        {
             0x01, 0x02, 0x03, 0x04, 0x05                     // .....
        })
        Name (P000, Package (0x07)
        {
            0x0B,
            0x0C,
            0x0D,
            0x0E,
            0x0F,
            0x10,
            0x11
        })
        Local0 = SizeOf (I000)
        If ((F64 == 0x01))
        {
            If ((Local0 != 0x08))
            {
                ERR (__METHOD__, Z041, __LINE__, 0x00, 0x00, Local0, 0x08)
            }
        }
        ElseIf ((Local0 != 0x04))
        {
            ERR (__METHOD__, Z041, __LINE__, 0x00, 0x00, Local0, 0x04)
        }

        Local0 = SizeOf (S000)
        If ((Local0 != 0x03))
        {
            ERR (__METHOD__, Z041, __LINE__, 0x00, 0x00, Local0, 0x03)
        }

        Local0 = SizeOf (B000)
        If ((Local0 != 0x05))
        {
            ERR (__METHOD__, Z041, __LINE__, 0x00, 0x00, Local0, 0x05)
        }

        Local0 = SizeOf (P000)
        If ((Local0 != 0x07))
        {
            ERR (__METHOD__, Z041, __LINE__, 0x00, 0x00, Local0, 0x07)
        }
    }

    /* Run-method */

    Method (SZO0, 0, NotSerialized)
    {
        Debug = "TEST: SZO0, Get the size of Integer, Buffer, String or Package:"
        M1EF ()
    }
