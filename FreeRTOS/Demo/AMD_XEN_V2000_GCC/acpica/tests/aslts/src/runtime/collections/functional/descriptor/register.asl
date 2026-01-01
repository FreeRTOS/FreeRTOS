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
     * Generic Register Resource Descriptor Macro
     */
    Name (P436, Package (0x12)
    {
        ResourceTemplate ()
        {
            Register (SystemMemory,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (SystemIO,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (PCI_Config,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (EmbeddedControl,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (SMBus,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (SystemCMOS,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (PCIBARTarget,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (IPMI,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (GeneralPurposeIo,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (GenericSerialBus,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (FFixedHW,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (SystemMemory,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (SystemMemory,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                0x01,               // Access Size
                )
        },

        ResourceTemplate ()
        {
            Register (SystemMemory,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                0x02,               // Access Size
                )
        },

        ResourceTemplate ()
        {
            Register (SystemMemory,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                0x03,               // Access Size
                )
        },

        ResourceTemplate ()
        {
            Register (SystemMemory,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                0x04,               // Access Size
                )
        },

        ResourceTemplate ()
        {
            Register (SystemMemory,
                0x00,               // Bit Width
                0x00,               // Bit Offset
                0x0000000000000000, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (SystemMemory,
                0xFF,               // Bit Width
                0xFF,               // Bit Offset
                0x0000000000000000, // Address
                ,)
        }
    })
    /*
     ACPI Specification, Revision 3.0, September 2, 2004
     6.4.3.7   Generic Register Descriptor
     Generic Register Descriptor layout:
     Byte 0	Generic register descriptor	Value = 10000010B (0x82) (Type = 1, Large item name = 0x2)
     Byte 1	Length, bits[7:0]	Value = 00001100B (12)
     Byte 2	Length, bits[15:8]	Value = 00000000B (0)
     Byte 3	Address Space ID, _ASI	The address space where the data structure or register exists.
     Defined values are:
     0x00	System Memory
     0x01	System I/O
     0x02	PCI Configuration Space
     0x03	Embedded Controller
     0x04	SMBus
     0x7F	Functional Fixed Hardware
     Byte 4	Register Bit Width, _RBW	Indicates the register width in bits.
     Byte 5	Register Bit Offset, _RBO	Indicates the offset to the start of the register in bits
     from the Register Address.
     Byte 6	Address Size, _ASZ	Specifies access size.
     0-Undefined (legacy reasons)
     1-Byte access
     2-Word access
     3-Dword access
     4-Qword access
     Byte 7	Register Address, _ADR bits[7:0]	Register Address
     Byte 8	Register Address, _ADR bits[15:8]
     Byte 9	Register Address, _ADR bits[23:16]
     Byte 10	Register Address, _ADR bits[31:24]
     Byte 11	Register Address, _ADR bits[39:32]
     Byte 12	Register Address, _ADR bits[47:40]
     Byte 13	Register Address, _ADR bits[55:48]
     Byte 14	Register Address, _ADR bits[63:56]
     */
    Name (P437, Package (0x12)
    {
        /* Byte 3 (Address Space ID) of Register Descriptor */

        ResourceTemplate ()
        {
            Register (SystemMemory,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (SystemIO,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (PCI_Config,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (EmbeddedControl,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (SMBus,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (SystemCMOS,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (PCIBARTarget,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (IPMI,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (GeneralPurposeIo,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (GenericSerialBus,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (FFixedHW,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        /* Byte 6 (Address Size) of Register Descriptor */

        ResourceTemplate ()
        {
            Register (SystemMemory,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (SystemMemory,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                0x01,               // Access Size
                )
        },

        ResourceTemplate ()
        {
            Register (SystemMemory,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                0x02,               // Access Size
                )
        },

        ResourceTemplate ()
        {
            Register (SystemMemory,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                0x03,               // Access Size
                )
        },

        ResourceTemplate ()
        {
            Register (SystemMemory,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                0x04,               // Access Size
                )
        },

        /* Particular cases */

        ResourceTemplate ()
        {
            Register (SystemMemory,
                0x00,               // Bit Width
                0x00,               // Bit Offset
                0x0000000000000000, // Address
                ,)
        },

        ResourceTemplate ()
        {
            Register (SystemMemory,
                0xFF,               // Bit Width
                0xFF,               // Bit Offset
                0x0000000000000000, // Address
                ,)
        }
    })
    Method (RT19, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "Register Resource Descriptor Macro", "register.asl")
        /* The main test packages must have the same number of entries */

        If ((SizeOf (P436) != SizeOf (P437)))
        {
            ERR (__METHOD__, 0xB3, __LINE__, 0x00, 0x00, 0x00, "Incorrect package length")
            Return (Zero)
        }

        /* Main test case for packages above */

        M330 (__METHOD__, SizeOf (P436), "p436", P436, P437)
        /* Register macro DescriptorName is recently implemented */
        /* Check resource descriptor tag offsets */
        Local0 = ResourceTemplate ()
            {
                Register (SystemMemory,
                    0xF0,               // Bit Width
                    0xF1,               // Bit Offset
                    0xF2F3F4F5F6F7F8F9, // Address
                    ,)
                Register (SystemMemory,
                    0xF0,               // Bit Width
                    0xF1,               // Bit Offset
                    0xF2F3F4F5F6F7F8F9, // Address
                    ,)
            }
        M331 (__METHOD__, 0x01, 0x18, 0x18, 0x90, 0x90, "_ASI")
        M331 (__METHOD__, 0x02, 0x20, 0x20, 0x98, 0x98, "_RBW")
        M331 (__METHOD__, 0x03, 0x28, 0x28, 0xA0, 0xA0, "_RBO")
        M331 (__METHOD__, 0x04, 0x30, 0x30, 0xA8, 0xA8, "_ASZ")
        M331 (__METHOD__, 0x05, 0x38, 0x38, 0xB0, 0xB0, "_ADR")
    }
