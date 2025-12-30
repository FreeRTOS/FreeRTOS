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
     * IRQNoFlags() Interrupt Resource Descriptor Macro
     */
    Name (P402, Package (0x12)
    {
        ResourceTemplate ()
        {
            IRQNoFlags ()
                {0}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {1}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {2}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {3}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {4}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {5}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {6}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {7}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {8}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {9}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {10}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {11}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {12}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {13}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {14}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {15}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15}
        }
    })
    /*
     ACPI Specification, Revision 3.0, September 2, 2004
     6.4.2.1   IRQ Descriptor
     IRQ Descriptor layout (length = 2):
     Byte 0 (Tag Bits): Value = 00100010B (0x22) (Type = 0, small item name = 0x4, length = 2),
     Byte 1 (IRQ mask bits[7:0]): IRQ0 <=> bit[0]
     Byte 2 (IRQ mask bits[15:8]): IRQ8 <=> bit[0]
     */
    Name (P403, Package (0x12)
    {
        ResourceTemplate ()
        {
            IRQNoFlags ()
                {0}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {1}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {2}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {3}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {4}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {5}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {6}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {7}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {8}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {9}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {10}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {11}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {12}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {13}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {14}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {15}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15}
        }
    })
    Method (RT02, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "IRQNoFlags Resource Descriptor Macro", "irqnoflags.asl")
        /* Main test case for packages above */

        M330 (__METHOD__, 0x12, "p402", P402, P403)
    }
