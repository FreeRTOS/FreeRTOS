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
     * GpioInt Resource Descriptor Macro
     */
    Device (GPII)
    {
    }

    Name (P452, Package (0x0121)
    {
        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullUp, 0x0000,
                "\\GPII", 0x00, ResourceConsumer, ,
                )
                {   // Pin list
                    0xF1F2
                }
        }
    })
    Name (P453, Package (0x0121)
    {
        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveLow, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveBoth, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                )
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveHigh, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveLow, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Exclusive, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, ExclusiveAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, Shared, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullUp, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullDown, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullDefault, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Level, ActiveBoth, SharedAndWake, PullNone, 0x1234,
                "\\GPII", 0xBB, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x11, 0x22, 0x33, 0x44
                })
                {   // Pin list
                    0xC1A3
                }
        },

        ResourceTemplate ()
        {
            GpioInt (Edge, ActiveHigh, Exclusive, PullUp, 0x0000,
                "\\GPII", 0x00, ResourceConsumer, ,
                )
                {   // Pin list
                    0xF1F2
                }
        }
    })
    Method (RT21, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "GpioInt Resource Descriptor Macro", "gpioint.asl")
        /* The main test packages must have the same number of entries */

        If ((SizeOf (P452) != SizeOf (P453)))
        {
            ERR (__METHOD__, 0xB2, __LINE__, 0x00, 0x00, 0x00, "Incorrect package length")
            Return (Zero)
        }

        /* Main test case for packages above */

        M330 (__METHOD__, SizeOf (P452), "p452", P452, P453)
        /* Check resource descriptor tag offsets */

        Local0 = ResourceTemplate ()
            {
                GpioInt (Edge, ActiveHigh, Exclusive, PullUp, 0x1234,
                    "\\GPII", 0xBB, ResourceConsumer, ,
                    RawDataBuffer (0x04)  // Vendor Data
                    {
                        0x11, 0x22, 0x33, 0x44
                    })
                    {   // Pin list
                        0x00A3
                    }
                GpioInt (Edge, ActiveHigh, Exclusive, PullUp, 0x1234,
                    "\\GPII", 0xBB, ResourceConsumer, ,
                    RawDataBuffer (0x04)  // Vendor Data
                    {
                        0x11, 0x22, 0x33, 0x44
                    })
                    {   // Pin list
                        0x00A3
                    }
            }
        M331 (__METHOD__, 0x01, 0x38, 0x38, 0x0150, 0x0150, "_MOD")
        M331 (__METHOD__, 0x02, 0x39, 0x39, 0x0151, 0x0151, "_POL")
        M331 (__METHOD__, 0x03, 0x3B, 0x3B, 0x0153, 0x0153, "_SHR")
        M331 (__METHOD__, 0x04, 0x48, 0x48, 0x0160, 0x0160, "_PPI")
        M331 (__METHOD__, 0x05, 0x60, 0x60, 0x0178, 0x0178, "_DBT")
        M331 (__METHOD__, 0x06, 0xB8, 0xB8, 0x01D0, 0x01D0, "_PIN")
        M331 (__METHOD__, 0x07, 0xF8, 0xF8, 0x0210, 0x0210, "_VEN")
    }
