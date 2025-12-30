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
     * PinGroupConfig Resource Descriptor Macro
     */
    Name (P464, Package (0x21)
    {
        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x00 /* Default */, 0x1000,
                "\\_SB.GPO2", 0x00, "group0", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x01 /* Bias Pull-up */, 0x2000,
                "\\_SB.GPO2", 0x00, "group1", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x02 /* Bias Pull-down */, 0x3000,
                "\\_SB.GPO2", 0x00, "group2", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x03 /* Bias Default */, 0x4000,
                "\\_SB.GPO2", 0x00, "group3", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x04 /* Bias Disable */, 0x5000,
                "\\_SB.GPO2", 0x00, "group4", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x05 /* Bias High Impedance */, 0x6000,
                "\\_SB.GPO2", 0x00, "group5", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x06 /* Bias Bus Hold */, 0x7000,
                "\\_SB.GPO2", 0x00, "group6", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x07 /* Drive Open Drain */, 0x8000,
                "\\_SB.GPO2", 0x00, "group7", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x08 /* Drive Open Source */, 0x9000,
                "\\_SB.GPO2", 0x00, "group8", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x09 /* Drive Push Pull */, 0xA000,
                "\\_SB.GPO2", 0x00, "group9", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x0A /* Drive Strength */, 0xB000,
                "\\_SB.GPO2", 0x00, "group10", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x0B /* Slew Rate */, 0xC000,
                "\\_SB.GPO2", 0x00, "group11", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x0C /* Input Debounce */, 0xD000,
                "\\_SB.GPO2", 0x00, "group12", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x0D /* Input Schmitt Trigger */, 0xE000,
                "\\_SB.GPO2", 0x00, "group13", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x80, /* Vendor Defined */ 0xE000,
                "\\_SB.GPO2", 0x00, "group128", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0xF0, /* Vendor Defined */ 0xF000,
                "\\_SB.GPO2", 0x00, "group240", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x00 /* Default */, 0x1000,
                "\\_SB.GPO2", 0x00, "group0", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x01 /* Bias Pull-up */, 0x2000,
                "\\_SB.GPO2", 0x00, "group1", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x02 /* Bias Pull-down */, 0x3000,
                "\\_SB.GPO2", 0x00, "group2", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x03 /* Bias Default */, 0x4000,
                "\\_SB.GPO2", 0x00, "group3", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x04 /* Bias Disable */, 0x5000,
                "\\_SB.GPO2", 0x00, "group4", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x05 /* Bias High Impedance */, 0x6000,
                "\\_SB.GPO2", 0x00, "group5", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x06 /* Bias Bus Hold */, 0x7000,
                "\\_SB.GPO2", 0x00, "group6", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x07 /* Drive Open Drain */, 0x8000,
                "\\_SB.GPO2", 0x00, "group7", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x08 /* Drive Open Source */, 0x9000,
                "\\_SB.GPO2", 0x00, "group8", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x09 /* Drive Push Pull */, 0xA000,
                "\\_SB.GPO2", 0x00, "group9", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x0A /* Drive Strength */, 0xB000,
                "\\_SB.GPO2", 0x00, "group10", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x0B /* Slew Rate */, 0xC000,
                "\\_SB.GPO2", 0x00, "group11", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x0C /* Input Debounce */, 0xD000,
                "\\_SB.GPO2", 0x00, "group12", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x0D /* Input Schmitt Trigger */, 0xE000,
                "\\_SB.GPO2", 0x00, "group13", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x80, /* Vendor Defined */ 0xE000,
                "\\_SB.GPO2", 0x00, "group128", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0xF0, /* Vendor Defined */ 0xF000,
                "\\_SB.GPO2", 0x00, "group240", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x01 /* Bias Pull-up */, 0xF000,
                "\\_SB.GPO2", 0x00, "group", ResourceConsumer, ,)
        }
    })
    Name (P465, Package (0x21)
    {
        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x00 /* Default */, 0x1000,
                "\\_SB.GPO2", 0x00, "group0", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x01 /* Bias Pull-up */, 0x2000,
                "\\_SB.GPO2", 0x00, "group1", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x02 /* Bias Pull-down */, 0x3000,
                "\\_SB.GPO2", 0x00, "group2", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x03 /* Bias Default */, 0x4000,
                "\\_SB.GPO2", 0x00, "group3", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x04 /* Bias Disable */, 0x5000,
                "\\_SB.GPO2", 0x00, "group4", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x05 /* Bias High Impedance */, 0x6000,
                "\\_SB.GPO2", 0x00, "group5", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x06 /* Bias Bus Hold */, 0x7000,
                "\\_SB.GPO2", 0x00, "group6", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x07 /* Drive Open Drain */, 0x8000,
                "\\_SB.GPO2", 0x00, "group7", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x08 /* Drive Open Source */, 0x9000,
                "\\_SB.GPO2", 0x00, "group8", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x09 /* Drive Push Pull */, 0xA000,
                "\\_SB.GPO2", 0x00, "group9", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x0A /* Drive Strength */, 0xB000,
                "\\_SB.GPO2", 0x00, "group10", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x0B /* Slew Rate */, 0xC000,
                "\\_SB.GPO2", 0x00, "group11", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x0C /* Input Debounce */, 0xD000,
                "\\_SB.GPO2", 0x00, "group12", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x0D /* Input Schmitt Trigger */, 0xE000,
                "\\_SB.GPO2", 0x00, "group13", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x80, /* Vendor Defined */ 0xE000,
                "\\_SB.GPO2", 0x00, "group128", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0xF0, /* Vendor Defined */ 0xF000,
                "\\_SB.GPO2", 0x00, "group240", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x00 /* Default */, 0x1000,
                "\\_SB.GPO2", 0x00, "group0", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x01 /* Bias Pull-up */, 0x2000,
                "\\_SB.GPO2", 0x00, "group1", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x02 /* Bias Pull-down */, 0x3000,
                "\\_SB.GPO2", 0x00, "group2", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x03 /* Bias Default */, 0x4000,
                "\\_SB.GPO2", 0x00, "group3", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x04 /* Bias Disable */, 0x5000,
                "\\_SB.GPO2", 0x00, "group4", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x05 /* Bias High Impedance */, 0x6000,
                "\\_SB.GPO2", 0x00, "group5", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x06 /* Bias Bus Hold */, 0x7000,
                "\\_SB.GPO2", 0x00, "group6", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x07 /* Drive Open Drain */, 0x8000,
                "\\_SB.GPO2", 0x00, "group7", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x08 /* Drive Open Source */, 0x9000,
                "\\_SB.GPO2", 0x00, "group8", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x09 /* Drive Push Pull */, 0xA000,
                "\\_SB.GPO2", 0x00, "group9", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x0A /* Drive Strength */, 0xB000,
                "\\_SB.GPO2", 0x00, "group10", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x0B /* Slew Rate */, 0xC000,
                "\\_SB.GPO2", 0x00, "group11", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x0C /* Input Debounce */, 0xD000,
                "\\_SB.GPO2", 0x00, "group12", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x0D /* Input Schmitt Trigger */, 0xE000,
                "\\_SB.GPO2", 0x00, "group13", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0x80, /* Vendor Defined */ 0xE000,
                "\\_SB.GPO2", 0x00, "group128", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Shared, 0xF0, /* Vendor Defined */ 0xF000,
                "\\_SB.GPO2", 0x00, "group240", ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
        },

        ResourceTemplate ()
        {
            PinGroupConfig (Exclusive, 0x01 /* Bias Pull-up */, 0xF000,
                "\\_SB.GPO2", 0x00, "group", ResourceConsumer, ,)
        }
    })
    Method (RT30, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "PinGroupConfig Resource Descriptor Macro", "pingroupconfig.asl")
        /* The main test packages must have the same number of entries */

        If ((SizeOf (P464) != SizeOf (P465)))
        {
            ERR (__METHOD__, 0xB3, __LINE__, 0x00, 0x00, 0x00, "Incorrect package length")
            Return (Zero)
        }

        /* Main test case for packages above */

        M330 (__METHOD__, SizeOf (P464), "P464", P464, P465)
                    /* Check resource descriptor tag offsets */

Local0 = ResourceTemplate ()
            {
                PinGroupConfig (Shared, 0x01 /* Bias Pull-up */, 0x2000,
                    "\\_SB.GPO2", 0x00, "group0", ResourceConsumer, ,
                    RawDataBuffer (0x04)  // Vendor Data
                    {
                        0x0A, 0x0B, 0x0C, 0x0D
                    })
                PinGroupConfig (Shared, 0x01 /* Bias Pull-up */, 0x2000,
                    "\\_SB.GPO2", 0x00, "group1", ResourceConsumer, ,
                    RawDataBuffer (0x04)  // Vendor Data
                    {
                        0x0A, 0x0B, 0x0C, 0x0D
                    })
            }
        M331 (__METHOD__, 0x01, 0x20, 0x20, 0x0168, 0x0168, "_SHR")
        M331 (__METHOD__, 0x01, 0x30, 0x30, 0x0178, 0x0178, "_TYP")
        M331 (__METHOD__, 0x01, 0x38, 0x38, 0x0180, 0x0180, "_VAL")
        M331 (__METHOD__, 0x01, 0x0128, 0x0128, 0x0270, 0x0270, "_VEN")
    }
