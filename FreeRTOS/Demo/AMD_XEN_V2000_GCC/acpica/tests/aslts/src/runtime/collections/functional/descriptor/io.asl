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
     * IO Resource Descriptor Macro
     */
    Name (P408, Package (0x03)
    {
        ResourceTemplate ()
        {
            IO (Decode10,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4,               // Alignment
                0xF5,               // Length
                )
        },

        ResourceTemplate ()
        {
            IO (Decode16,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4,               // Alignment
                0xF5,               // Length
                )
        },

        ResourceTemplate ()
        {
            IO (Decode16,
                0x0000,             // Range Minimum
                0x0000,             // Range Maximum
                0x00,               // Alignment
                0x00,               // Length
                )
        }
    })
    /*
     ACPI Specification, Revision 3.0, September 2, 2004
     6.4.2.5   I/O Port Descriptor
     I/O Port Descriptor layout:
     Byte 0 (Tag Bits): Value = 01000111B (0x47) (Type = 0, Small item name = 0x8, Length = 7)
     Byte 1 (Information): 0000000dB
     Bits[7:1] 	Reserved and must be 0
     Bit[0] 	 	(_DEC)
     1	The logical device decodes 16-bit addresses
     0	The logical device only decodes address bits[9:0]
     Byte 2 (Range minimum base address, _MIN bits[7:0])
     Byte 3 (Range minimum base address, _MIN bits[15:8])
     Byte 4 (Range maximum base address, _MAX bits[7:0])
     Byte 5 (Range maximum base address, _MAX bits[15:8])
     Byte 6 (Base alignment, _ALN): Alignment for minimum base address,
     increment in 1-byte blocks.
     Byte 7 (Range length, _LEN): The number of contiguous I/O ports requested.
     */
    Name (P409, Package (0x03)
    {
        ResourceTemplate ()
        {
            IO (Decode10,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4,               // Alignment
                0xF5,               // Length
                )
        },

        ResourceTemplate ()
        {
            IO (Decode16,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4,               // Alignment
                0xF5,               // Length
                )
        },

        ResourceTemplate ()
        {
            IO (Decode16,
                0x0000,             // Range Minimum
                0x0000,             // Range Maximum
                0x00,               // Alignment
                0x00,               // Length
                )
        }
    })
    Method (RT05, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "IO Resource Descriptor Macro", "io.asl")
        /* Main test case for packages above */

        M330 (__METHOD__, 0x03, "p408", P408, P409)
        /* Check resource descriptor tag offsets */

        Local0 = ResourceTemplate ()
            {
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
            }
        M331 (__METHOD__, 0x01, 0x08, 0x08, 0x48, 0x48, "_DEC")
        M331 (__METHOD__, 0x02, 0x10, 0x10, 0x50, 0x50, "_MIN")
        M331 (__METHOD__, 0x03, 0x20, 0x20, 0x60, 0x60, "_MAX")
        M331 (__METHOD__, 0x04, 0x30, 0x30, 0x70, 0x70, "_ALN")
        M331 (__METHOD__, 0x05, 0x38, 0x38, 0x78, 0x78, "_LEN")
    }
