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
     * Short Vendor Resource Descriptor
     */
    Name (P40C, Package (0x08)
    {
        ResourceTemplate ()
        {
            VendorShort ()      // Length = 0x00
            {
            }
        },

        ResourceTemplate ()
        {
            VendorShort ()      // Length = 0x01
            {
                 0xF1                                             // .
            }
        },

        ResourceTemplate ()
        {
            VendorShort ()      // Length = 0x02
            {
                 0xE1, 0xF2                                       // ..
            }
        },

        ResourceTemplate ()
        {
            VendorShort ()      // Length = 0x03
            {
                 0xD1, 0xE2, 0xF3                                 // ...
            }
        },

        ResourceTemplate ()
        {
            VendorShort ()      // Length = 0x04
            {
                 0x00, 0xD2, 0xE3, 0xF4                           // ....
            }
        },

        ResourceTemplate ()
        {
            VendorShort ()      // Length = 0x05
            {
                 0xB1, 0xC2, 0x00, 0xE4, 0xF5                     // .....
            }
        },

        ResourceTemplate ()
        {
            VendorShort ()      // Length = 0x06
            {
                 0xA1, 0xB2, 0xC3, 0xD4, 0xE5, 0xF6               // ......
            }
        },

        ResourceTemplate ()
        {
            VendorShort ()      // Length = 0x07
            {
                 0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
            }
        }
    })
    /*
     ACPI Specification, Revision 3.0, September 2, 2004
     6.4.2.7   Vendor-Defined Descriptor
     Vendor-Defined Descriptor layout:
     Byte 0 (Tag Bits): Value = 01110nnnB (0x71-0x77)(Type = 0, small item name = 0xE, length = (1-7))
     Byte 1 to 7 - Vendor defined
     */
    Name (P40D, Package (0x08)
    {
        ResourceTemplate ()
        {
            VendorShort ()      // Length = 0x00
            {
            }
        },

        ResourceTemplate ()
        {
            VendorShort ()      // Length = 0x01
            {
                 0xF1                                             // .
            }
        },

        ResourceTemplate ()
        {
            VendorShort ()      // Length = 0x02
            {
                 0xE1, 0xF2                                       // ..
            }
        },

        ResourceTemplate ()
        {
            VendorShort ()      // Length = 0x03
            {
                 0xD1, 0xE2, 0xF3                                 // ...
            }
        },

        ResourceTemplate ()
        {
            VendorShort ()      // Length = 0x04
            {
                 0x00, 0xD2, 0xE3, 0xF4                           // ....
            }
        },

        ResourceTemplate ()
        {
            VendorShort ()      // Length = 0x05
            {
                 0xB1, 0xC2, 0x00, 0xE4, 0xF5                     // .....
            }
        },

        ResourceTemplate ()
        {
            VendorShort ()      // Length = 0x06
            {
                 0xA1, 0xB2, 0xC3, 0xD4, 0xE5, 0xF6               // ......
            }
        },

        ResourceTemplate ()
        {
            VendorShort ()      // Length = 0x07
            {
                 0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
            }
        }
    })
    Method (RT07, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "Short Vendor Resource Descriptor Macro", "vendorshort.asl")
        /* Main test case for packages above */

        M330 (__METHOD__, 0x08, "p40c", P40C, P40D)
    }
