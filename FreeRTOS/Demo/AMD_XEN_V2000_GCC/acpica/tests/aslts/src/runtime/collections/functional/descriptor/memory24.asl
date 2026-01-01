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
     * Memory24() Memory Resource Descriptor Macro
     */
    Name (P40E, Package (0x03)
    {
        ResourceTemplate ()
        {
            Memory24 (ReadOnly,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4F5,             // Alignment
                0xF6F7,             // Length
                )
        },

        ResourceTemplate ()
        {
            Memory24 (ReadWrite,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4F5,             // Alignment
                0xF6F7,             // Length
                )
        },

        ResourceTemplate ()
        {
            Memory24 (ReadWrite,
                0x0000,             // Range Minimum
                0x0000,             // Range Maximum
                0x0000,             // Alignment
                0x0000,             // Length
                )
        }
    })
    /*
     ACPI Specification, Revision 3.0, September 2, 2004
     6.4.3.1   24-Bit Memory Range Descriptor
     24-Bit Memory Range Descriptor layout:
     Byte 0 (Tag Bits): Value = 10000001B (0x81) (Type = 1, Large item name = 0x1)
     Byte 1 (Length, bits[7:0]): Value = 00001001B (9)
     Byte 2 (Length, bits[15:8]): Value = 00000000B (0)
     Byte 3 (Information):
     Bit[7:1]	Ignored
     Bit[0]		Write status, _RW
     1	writeable (read/write)
     0	non-writeable (read-only)
     Byte 4 (Range minimum base address, _MIN, bits[7:0]):
     Address bits[15:8] of the minimum base memory address
     for which the card may be configured.
     Byte 5 (Range minimum base address, _MIN, bits[15:8]):
     Address bits[23:16] of the minimum base memory address
     for which the card may be configured
     Byte 6 (Range maximum base address, _MAX, bits[7:0]):
     Address bits[15:8] of the maximum base memory address
     for which the card may be configured.
     Byte 7 (Range maximum base address, _MAX, bits[15:8]):
     Address bits[23:16] of the maximum base memory address
     for which the card may be configured
     Byte 8 (Base alignment, _ALN, bits[7:0]):
     This field contains the lower eight bits of the base alignment.
     The base alignment provides the increment for the minimum base
     address. (0x0000 = 64 KB)
     Byte 9 (Base alignment, _ALN, bits[15:8]):
     This field contains the upper eight bits of the base alignment.
     Byte 10 (Range length, _LEN, bits[7:0]):
     This field contains the lower eight bits of the memory range length.
     The range length provides the length of the memory range in 256 byte blocks.
     Byte 11 (Range length, _LEN, bits[15:8]):
     This field contains the upper eight bits of the memory range length.
     */
    Name (P40F, Package (0x03)
    {
        ResourceTemplate ()
        {
            Memory24 (ReadOnly,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4F5,             // Alignment
                0xF6F7,             // Length
                )
        },

        ResourceTemplate ()
        {
            Memory24 (ReadWrite,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4F5,             // Alignment
                0xF6F7,             // Length
                )
        },

        ResourceTemplate ()
        {
            Memory24 (ReadWrite,
                0x0000,             // Range Minimum
                0x0000,             // Range Maximum
                0x0000,             // Alignment
                0x0000,             // Length
                )
        }
    })
    Method (RT08, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "Memory24 Resource Descriptor Macro", "memory24.asl")
        /* Main test case for packages above */

        M330 (__METHOD__, 0x03, "p40e", P40E, P40F)
        /* Check resource descriptor tag offsets */

        Local0 = ResourceTemplate ()
            {
                Memory24 (ReadOnly,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory24 (ReadOnly,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
            }
        M331 (__METHOD__, 0x01, 0x18, 0x18, 0x78, 0x78, "_RW")
        M331 (__METHOD__, 0x02, 0x20, 0x20, 0x80, 0x80, "_MIN")
        M331 (__METHOD__, 0x03, 0x30, 0x30, 0x90, 0x90, "_MAX")
        M331 (__METHOD__, 0x04, 0x40, 0x40, 0xA0, 0xA0, "_ALN")
        M331 (__METHOD__, 0x05, 0x50, 0x50, 0xB0, 0xB0, "_LEN")
    }
