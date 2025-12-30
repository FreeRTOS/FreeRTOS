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
     * Memory32Fixed() Memory Resource Descriptor Macro
     */
    Name (P414, Package (0x03)
    {
        ResourceTemplate ()
        {
            Memory32Fixed (ReadOnly,
                0xF0F1F2F3,         // Address Base
                0xF4F5F6F7,         // Address Length
                )
        },

        ResourceTemplate ()
        {
            Memory32Fixed (ReadWrite,
                0xF0F1F2F3,         // Address Base
                0xF4F5F6F7,         // Address Length
                )
        },

        ResourceTemplate ()
        {
            Memory32Fixed (ReadWrite,
                0x00000000,         // Address Base
                0x00000000,         // Address Length
                )
        }
    })
    /*
     ACPI Specification, Revision 3.0, September 2, 2004
     6.4.3.4   32-Bit Fixed Memory Range Descriptor
     32-Bit Fixed Memory Range Descriptor layout:
     Byte 0 (Tag Bits): Value = 10000110B (0x86) (Type = 1, Large item name = 6)
     Byte 1 (Length, bits[7:0]): Value = 00001001B (9)
     Byte 2 (Length, bits[15:8]): Value = 00000000B (0)
     Byte 3 (Information):
     Bit[7:1]	Ignored
     Bit[0]		Write status, _RW
     1	writeable (read/write)
     0	non-writeable (read-only)
     Byte 4 (Range base address, _BAS, bits[7:0])
     Byte 5 (Range base address, _BAS, bits[15:8])
     Byte 6 (Range base address, _BAS, bits[23:16])
     Byte 7 (Range base address, _BAS, bits[31:24])
     Byte 8 (Range length, _LEN bits[7:0])
     Byte 9 (Range length, _LEN, bits[15:8])
     Byte 10 (Range length, _LEN, bits[23:16])
     Byte 11 (Range length, _LEN, bits[31:24])
     */
    Name (P415, Package (0x03)
    {
        ResourceTemplate ()
        {
            Memory32Fixed (ReadOnly,
                0xF0F1F2F3,         // Address Base
                0xF4F5F6F7,         // Address Length
                )
        },

        ResourceTemplate ()
        {
            Memory32Fixed (ReadWrite,
                0xF0F1F2F3,         // Address Base
                0xF4F5F6F7,         // Address Length
                )
        },

        ResourceTemplate ()
        {
            Memory32Fixed (ReadWrite,
                0x00000000,         // Address Base
                0x00000000,         // Address Length
                )
        }
    })
    Method (RT0B, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "Memory32Fixed Resource Descriptor Macro", "memory32fixed.asl")
        /* Main test case for packages above */

        M330 (__METHOD__, 0x03, "p414", P414, P415)
        /* Check resource descriptor tag offsets */

        Local0 = ResourceTemplate ()
            {
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
            }
        M331 (__METHOD__, 0x01, 0x18, 0x18, 0x78, 0x78, "_RW")
        M331 (__METHOD__, 0x02, 0x20, 0x20, 0x80, 0x80, "_BAS")
        M331 (__METHOD__, 0x03, 0x40, 0x40, 0xA0, 0xA0, "_LEN")
    }
