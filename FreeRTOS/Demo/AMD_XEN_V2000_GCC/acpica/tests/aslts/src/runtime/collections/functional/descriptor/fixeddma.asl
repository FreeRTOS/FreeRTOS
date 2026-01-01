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
     * FixedDma Resource Descriptor Macro
     */
    Name (P450, Package (0x08)
    {
        ResourceTemplate ()
        {
            FixedDMA (0xF1F2, 0x1234, Width8bit, )
        },

        ResourceTemplate ()
        {
            FixedDMA (0xE1E2, 0x000F, Width16bit, )
        },

        ResourceTemplate ()
        {
            FixedDMA (0xD1D2, 0x00F0, Width32bit, )
        },

        ResourceTemplate ()
        {
            FixedDMA (0xC1C2, 0x0F00, Width64bit, )
        },

        ResourceTemplate ()
        {
            FixedDMA (0xB1B2, 0xF000, Width128bit, )
        },

        ResourceTemplate ()
        {
            FixedDMA (0xA1A2, 0xFFFF, Width256bit, )
        },

        ResourceTemplate ()
        {
            FixedDMA (0x9192, 0x11D7, Width32bit, )
        },

        ResourceTemplate ()
        {
            FixedDMA (0x8182, 0x11D7, Width32bit, )
        }
    })
    Name (P451, Package (0x08)
    {
        ResourceTemplate ()
        {
            FixedDMA (0xF1F2, 0x1234, Width8bit, )
        },

        ResourceTemplate ()
        {
            FixedDMA (0xE1E2, 0x000F, Width16bit, )
        },

        ResourceTemplate ()
        {
            FixedDMA (0xD1D2, 0x00F0, Width32bit, )
        },

        ResourceTemplate ()
        {
            FixedDMA (0xC1C2, 0x0F00, Width64bit, )
        },

        ResourceTemplate ()
        {
            FixedDMA (0xB1B2, 0xF000, Width128bit, )
        },

        ResourceTemplate ()
        {
            FixedDMA (0xA1A2, 0xFFFF, Width256bit, )
        },

        ResourceTemplate ()
        {
            FixedDMA (0x9192, 0x11D7, Width32bit, )
        },

        ResourceTemplate ()
        {
            FixedDMA (0x8182, 0x11D7, Width32bit, )
        }
    })
    Method (RT20, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "FixedDMA Resource Descriptor Macro", "fixeddma.asl")
        /* The main test packages must have the same number of entries */

        If ((SizeOf (P450) != SizeOf (P451)))
        {
            ERR (__METHOD__, 0xB1, __LINE__, 0x00, 0x00, 0x00, "Incorrect package length")
            Return (Zero)
        }

        /* Main test case for packages above */

        M330 (__METHOD__, SizeOf (P450), "p450", P450, P451)
        /* Check resource descriptor tag offsets */

        Local0 = ResourceTemplate ()
            {
                FixedDMA (0xE1E2, 0x000F, Width16bit, )
                FixedDMA (0xD1D2, 0x00F0, Width32bit, )
            }
        M331 (__METHOD__, 0x01, 0x08, 0x08, 0x38, 0x38, "_DMA")
        M331 (__METHOD__, 0x02, 0x18, 0x18, 0x48, 0x48, "_TYP")
        M331 (__METHOD__, 0x03, 0x28, 0x28, 0x58, 0x58, "_SIZ")
    }
