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
     * PinGroupFunction Resource Descriptor Macro
     */
    Name (P462, Package (0x07)
    {
        ResourceTemplate ()
        {
            PinGroupFunction (Exclusive, 0x1000, "\\_SB.GPO1", 0x00,
                "group0", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupFunction (Exclusive, 0x1234, "\\_SB.GPO1", 0x00,
                "group1", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupFunction (Shared, 0x1000, "\\_SB.GPO1", 0x00,
                "group0", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupFunction (Shared, 0x1234, "\\_SB.GPO1", 0x00,
                "group1", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupFunction (Shared, 0x1000, "\\_SB.GPO1", 0x00,
                "group0", ResourceConsumer, ,)
        },

        ResourceTemplate ()
        {
            PinGroupFunction (Shared, 0x1234, "\\_SB.GPO1", 0x00,
                "group1", ResourceConsumer, ,)
        },

        ResourceTemplate ()
        {
            PinGroupFunction (Exclusive, 0x1234, "\\_SB.GPO1", 0x00,
                "group0", ResourceConsumer, ,)
        }
    })
    Name (P463, Package (0x07)
    {
        ResourceTemplate ()
        {
            PinGroupFunction (Exclusive, 0x1000, "\\_SB.GPO1", 0x00,
                "group0", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupFunction (Exclusive, 0x1234, "\\_SB.GPO1", 0x00,
                "group1", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupFunction (Shared, 0x1000, "\\_SB.GPO1", 0x00,
                "group0", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupFunction (Shared, 0x1234, "\\_SB.GPO1", 0x00,
                "group1", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupFunction (Shared, 0x1000, "\\_SB.GPO1", 0x00,
                "group0", ResourceConsumer, ,)
        },

        ResourceTemplate ()
        {
            PinGroupFunction (Shared, 0x1234, "\\_SB.GPO1", 0x00,
                "group1", ResourceConsumer, ,)
        },

        ResourceTemplate ()
        {
            PinGroupFunction (Exclusive, 0x1234, "\\_SB.GPO1", 0x00,
                "group0", ResourceConsumer, ,)
        }
    })
    Method (RT29, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "PinGroupFunction Resource Descriptor Macro", "pingroupfunction.asl")
        /* The main test packages must have the same number of entries */

        If ((SizeOf (P462) != SizeOf (P463)))
        {
            ERR (__METHOD__, 0xB3, __LINE__, 0x00, 0x00, 0x00, "Incorrect package length")
            Return (Zero)
        }

        /* Main test case for packages above */

        M330 (__METHOD__, SizeOf (P462), "P462", P462, P463)
                    /* Check resource descriptor tag offsets */

Local0 = ResourceTemplate ()
            {
                PinGroupFunction (Shared, 0x1234, "\\_SB.GPO1", 0x00,
                    "group0", ResourceConsumer, ,
                    RawDataBuffer (0x04)  // Vendor Data
                    {
                        0x0A, 0x0B, 0x0C, 0x0D
                    })
                PinGroupFunction (Shared, 0x1234, "\\_SB.GPO1", 0x00,
                    "group0", ResourceConsumer, ,
                    RawDataBuffer (0x04)  // Vendor Data
                    {
                        0x0A, 0x0B, 0x0C, 0x0D
                    })
            }
        M331 (__METHOD__, 0x01, 0x20, 0x20, 0x0150, 0x0150, "_SHR")
        M331 (__METHOD__, 0x01, 0x30, 0x30, 0x0160, 0x0160, "_FUN")
        M331 (__METHOD__, 0x01, 0x0110, 0x0110, 0x0240, 0x0240, "_VEN")
    }
