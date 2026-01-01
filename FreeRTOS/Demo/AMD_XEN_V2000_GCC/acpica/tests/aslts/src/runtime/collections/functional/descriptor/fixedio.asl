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
     * Resource Descriptor macros
     *
     * Fixed IO Resource Descriptor Macro
     */
    Name (P40A, Package (0x02)
    {
        ResourceTemplate ()
        {
            FixedIO (
                0x03F1,             // Address
                0xF2,               // Length
                )
        },

        ResourceTemplate ()
        {
            FixedIO (
                0x0000,             // Address
                0x00,               // Length
                )
        }
    })
    /*
     ACPI Specification, Revision 3.0, September 2, 2004
     6.4.2.6   Fixed Location I/O Port Descriptor
     Fixed Location I/O Port Descriptor layout:
     Byte 0 (Tag Bits): Value = 01001011B (0x4b)(Type = 0, Small item name = 0x9, Length = 3)
     Byte 1 (Range base address, _BAS bits[7:0])
     Byte 2 (Range base address, _BAS bits[9:8])
     Byte 3 (Range length, _LEN)
     */
    Name (P40B, Package (0x02)
    {
        ResourceTemplate ()
        {
            FixedIO (
                0x03F1,             // Address
                0xF2,               // Length
                )
        },

        ResourceTemplate ()
        {
            FixedIO (
                0x0000,             // Address
                0x00,               // Length
                )
        }
    })
    Method (RT06, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "FixedIO Resource Descriptor Macro", "fixedio.asl")
        /* Main test case for packages above */

        M330 (__METHOD__, 0x02, "p40a", P40A, P40B)
        /* Check resource descriptor tag offsets */

        Local0 = ResourceTemplate ()
            {
                FixedIO (
                    0x0001,             // Address
                    0xFF,               // Length
                    )
                FixedIO (
                    0x0001,             // Address
                    0xFF,               // Length
                    )
            }
        M331 (__METHOD__, 0x01, 0x08, 0x08, 0x28, 0x28, "_BAS")
        M331 (__METHOD__, 0x02, 0x18, 0x18, 0x38, 0x38, "_LEN")
    }
