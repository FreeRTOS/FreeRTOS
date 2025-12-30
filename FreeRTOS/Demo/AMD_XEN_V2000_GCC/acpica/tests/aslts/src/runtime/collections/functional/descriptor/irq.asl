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
     * IRQ() Interrupt Resource Descriptor Macro
     */
    Name (P400, Package (0x12)
    {
        ResourceTemplate ()
        {
            IRQ (Level, ActiveHigh, Exclusive, )
                {0}
        },

        ResourceTemplate ()
        {
            IRQ (Level, ActiveHigh, Shared, )
                {1}
        },

        ResourceTemplate ()
        {
            IRQ (Level, ActiveLow, Exclusive, )
                {2}
        },

        ResourceTemplate ()
        {
            IRQ (Level, ActiveLow, Shared, )
                {3}
        },

        ResourceTemplate ()
        {
            IRQ (Edge, ActiveHigh, Exclusive, )
                {4}
        },

        ResourceTemplate ()
        {
            IRQ (Edge, ActiveHigh, Shared, )
                {5}
        },

        ResourceTemplate ()
        {
            IRQ (Edge, ActiveLow, Exclusive, )
                {6}
        },

        ResourceTemplate ()
        {
            IRQ (Edge, ActiveLow, Shared, )
                {7}
        },

        ResourceTemplate ()
        {
            IRQ (Level, ActiveHigh, Exclusive, )
                {8}
        },

        ResourceTemplate ()
        {
            IRQ (Level, ActiveHigh, Shared, )
                {9}
        },

        ResourceTemplate ()
        {
            IRQ (Level, ActiveLow, Exclusive, )
                {10}
        },

        ResourceTemplate ()
        {
            IRQ (Level, ActiveLow, Shared, )
                {11}
        },

        ResourceTemplate ()
        {
            IRQ (Edge, ActiveHigh, Exclusive, )
                {12}
        },

        ResourceTemplate ()
        {
            IRQ (Edge, ActiveHigh, Shared, )
                {13}
        },

        ResourceTemplate ()
        {
            IRQ (Edge, ActiveLow, Exclusive, )
                {14}
        },

        ResourceTemplate ()
        {
            IRQ (Edge, ActiveLow, Shared, )
                {15}
        },

        ResourceTemplate ()
        {
            IRQ (Edge, ActiveLow, Exclusive, )
                {}
        },

        ResourceTemplate ()
        {
            IRQ (Level, ActiveHigh, Exclusive, )
                {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15}
        }
    })
    /*
     ACPI Specification, Revision 3.0, September 2, 2004
     6.4.2.1   IRQ Descriptor
     IRQ Descriptor layout (length = 3):
     Byte 0 (Tag Bits): Value = 00100011B (0x23) (Type = 0, small item name = 0x4, length = 3),
     Byte 1 (IRQ mask bits[7:0]): IRQ0 <=> bit[0]
     Byte 2 (IRQ mask bits[15:8]): IRQ8 <=> bit[0]
     Byte 3 (IRQ Information):
     Bit[4] 		Interrupt is shareable, _SHR
     Bit[3]		Interrupt Polarity, _LL
     0	Active-High - This interrupt is sampled when the signal is high, or true
     1	Active-Low - This interrupt is sampled when the signal is low, or false.
     Bit[0]		Interrupt Mode, _HE
     0	Level-Triggered - Interrupt is triggered in response to signal in a low state.
     1	Edge-Triggered - Interrupt is triggered in response to a change in signal state
     from low to high.
     */
    Name (P401, Package (0x12)
    {
        ResourceTemplate ()
        {
            IRQ (Level, ActiveHigh, Exclusive, )
                {0}
        },

        ResourceTemplate ()
        {
            IRQ (Level, ActiveHigh, Shared, )
                {1}
        },

        ResourceTemplate ()
        {
            IRQ (Level, ActiveLow, Exclusive, )
                {2}
        },

        ResourceTemplate ()
        {
            IRQ (Level, ActiveLow, Shared, )
                {3}
        },

        ResourceTemplate ()
        {
            IRQ (Edge, ActiveHigh, Exclusive, )
                {4}
        },

        ResourceTemplate ()
        {
            IRQ (Edge, ActiveHigh, Shared, )
                {5}
        },

        ResourceTemplate ()
        {
            IRQ (Edge, ActiveLow, Exclusive, )
                {6}
        },

        ResourceTemplate ()
        {
            IRQ (Edge, ActiveLow, Shared, )
                {7}
        },

        ResourceTemplate ()
        {
            IRQ (Level, ActiveHigh, Exclusive, )
                {8}
        },

        ResourceTemplate ()
        {
            IRQ (Level, ActiveHigh, Shared, )
                {9}
        },

        ResourceTemplate ()
        {
            IRQ (Level, ActiveLow, Exclusive, )
                {10}
        },

        ResourceTemplate ()
        {
            IRQ (Level, ActiveLow, Shared, )
                {11}
        },

        ResourceTemplate ()
        {
            IRQ (Edge, ActiveHigh, Exclusive, )
                {12}
        },

        ResourceTemplate ()
        {
            IRQ (Edge, ActiveHigh, Shared, )
                {13}
        },

        ResourceTemplate ()
        {
            IRQ (Edge, ActiveLow, Exclusive, )
                {14}
        },

        ResourceTemplate ()
        {
            IRQ (Edge, ActiveLow, Shared, )
                {15}
        },

        ResourceTemplate ()
        {
            IRQ (Edge, ActiveLow, Exclusive, )
                {}
        },

        ResourceTemplate ()
        {
            IRQ (Level, ActiveHigh, Exclusive, )
                {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15}
        }
    })
    Method (RT01, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "IRQ Resource Descriptor Macro", "irq.asl")
        /* Main test case for packages above */

        M330 (__METHOD__, 0x12, "p400", P400, P401)
        Local0 = ResourceTemplate ()
            {
                IRQ (Edge, ActiveLow, Shared, )
                    {}
                IRQ (Edge, ActiveLow, Shared, )
                    {}
            }
        M331 (__METHOD__, 0x01, 0x18, 0x18, 0x38, 0x38, "_HE")
        M331 (__METHOD__, 0x02, 0x1B, 0x1B, 0x3B, 0x3B, "_LL")
        M331 (__METHOD__, 0x03, 0x1C, 0x1C, 0x3C, 0x3C, "_SHR")
    }
