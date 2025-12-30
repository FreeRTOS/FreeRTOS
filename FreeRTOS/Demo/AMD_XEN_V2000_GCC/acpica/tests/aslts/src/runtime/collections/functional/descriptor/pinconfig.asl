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
     * PinConfig Resource Descriptor Macro
     */
    Name (P45E, Package (0x21)
    {
        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x00 /* Default */, 0x1000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x01 /* Bias Pull-up */, 0x2000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x000D
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x02 /* Bias Pull-down */, 0x3000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x03 /* Bias Default */, 0x4000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x04 /* Bias Disable */, 0x5000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x05 /* Bias High Impedance */, 0x6000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x06 /* Bias Bus Hold */, 0x7000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x07 /* Drive Open Drain */, 0x8000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x08 /* Drive Open Source */, 0x9000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x09 /* Drive Push Pull */, 0xA000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x0A /* Drive Strength */, 0xB000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x0B /* Slew Rate */, 0xC000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x0C /* Input Debounce */, 0xD000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x0D /* Input Schmitt Trigger */, 0xE000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x80, /* Vendor Defined */ 0xF000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0xFE, /* Vendor Defined */ 0xF100,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x00 /* Default */, 0x1000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x01 /* Bias Pull-up */, 0x2000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x000D
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x02 /* Bias Pull-down */, 0x3000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x03 /* Bias Default */, 0x4000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x04 /* Bias Disable */, 0x5000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x05 /* Bias High Impedance */, 0x6000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x06 /* Bias Bus Hold */, 0x7000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x07 /* Drive Open Drain */, 0x8000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x08 /* Drive Open Source */, 0x9000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x09 /* Drive Push Pull */, 0xA000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x0A /* Drive Strength */, 0xB000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x0B /* Slew Rate */, 0xC000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x0C /* Input Debounce */, 0xD000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x0D /* Input Schmitt Trigger */, 0xE000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x80, /* Vendor Defined */ 0xF000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0xFE, /* Vendor Defined */ 0xF100,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x00 /* Default */, 0x0000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,)
                {   // Pin list
                    0x0001,
                    0x0002
                }
        }
    })
    Name (P45F, Package (0x21)
    {
        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x00 /* Default */, 0x1000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x01 /* Bias Pull-up */, 0x2000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x000D
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x02 /* Bias Pull-down */, 0x3000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x03 /* Bias Default */, 0x4000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x04 /* Bias Disable */, 0x5000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x05 /* Bias High Impedance */, 0x6000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x06 /* Bias Bus Hold */, 0x7000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x07 /* Drive Open Drain */, 0x8000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x08 /* Drive Open Source */, 0x9000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x09 /* Drive Push Pull */, 0xA000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x0A /* Drive Strength */, 0xB000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x0B /* Slew Rate */, 0xC000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x0C /* Input Debounce */, 0xD000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x0D /* Input Schmitt Trigger */, 0xE000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x80, /* Vendor Defined */ 0xF000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0xFE, /* Vendor Defined */ 0xF100,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x00 /* Default */, 0x1000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x01 /* Bias Pull-up */, 0x2000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x000D
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x02 /* Bias Pull-down */, 0x3000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x03 /* Bias Default */, 0x4000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x04 /* Bias Disable */, 0x5000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x05 /* Bias High Impedance */, 0x6000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x06 /* Bias Bus Hold */, 0x7000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x07 /* Drive Open Drain */, 0x8000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x08 /* Drive Open Source */, 0x9000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x09 /* Drive Push Pull */, 0xA000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x0A /* Drive Strength */, 0xB000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x0B /* Slew Rate */, 0xC000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x0C /* Input Debounce */, 0xD000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x0D /* Input Schmitt Trigger */, 0xE000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0x80, /* Vendor Defined */ 0xF000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Shared, 0xFE, /* Vendor Defined */ 0xF100,
                "\\SB.GP01", 0x00, ResourceConsumer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C
                })
                {   // Pin list
                    0x00AA,
                    0x00BB,
                    0x00CC,
                    0x00DD
                }
        },

        ResourceTemplate ()
        {
            PinConfig (Exclusive, 0x00 /* Default */, 0x0000,
                "\\SB.GP01", 0x00, ResourceConsumer, ,)
                {   // Pin list
                    0x0001,
                    0x0002
                }
        }
    })
    Method (RT27, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "PinConfig Resource Descriptor Macro", "pinconfig.asl")
        /* The main test packages must have the same number of entries */

        If ((SizeOf (P45E) != SizeOf (P45F)))
        {
            ERR (__METHOD__, 0xB3, __LINE__, 0x00, 0x00, 0x00, "Incorrect package length")
            Return (Zero)
        }

        /* Main test case for packages above */

        M330 (__METHOD__, SizeOf (P45E), "P45E", P45E, P45F)
                    /* Check resource descriptor tag offsets */

Local0 = ResourceTemplate ()
            {
                PinConfig (Shared, 0x0C /* Input Debounce */, 0xABCD,
                    "\\SB.GP01", 0x00, ResourceConsumer, ,
                    RawDataBuffer (0x03)  // Vendor Data
                    {
                        0x0A, 0x0B, 0x0C
                    })
                    {   // Pin list
                        0x00AA,
                        0x00BB,
                        0x00CC,
                        0x00DD
                    }
                PinConfig (Shared, 0x0C /* Input Debounce */, 0xABCD,
                    "\\SB.GP01", 0x00, ResourceConsumer, ,
                    RawDataBuffer (0x03)  // Vendor Data
                    {
                        0x0A, 0x0B, 0x0C
                    })
                    {   // Pin list
                        0x00AA,
                        0x00BB,
                        0x00CC,
                        0x00DD
                    }
            }
        M331 (__METHOD__, 0x01, 0x20, 0x20, 0x0160, 0x0160, "_SHR")
        M331 (__METHOD__, 0x01, 0x30, 0x30, 0x0170, 0x0170, "_TYP")
        M331 (__METHOD__, 0x01, 0x38, 0x38, 0x0178, 0x0178, "_VAL")
        M331 (__METHOD__, 0x01, 0xA0, 0xA0, 0x01E0, 0x01E0, "_PIN")
        M331 (__METHOD__, 0x01, 0x0128, 0x0128, 0x0268, 0x0268, "_VEN")
    }
