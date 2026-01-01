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
     * SpiSerialBus Resource Descriptor Macro
     */
    Device (SPI)
    {
    }

    Name (P458, Package (0x81)
    {
        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0x00, ResourceConsumer, , Exclusive,
                )
        }
    })
    Name (P459, Package (0x81)
    {
        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x05)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                })
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceConsumer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityHigh, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                DeviceInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseFirst, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, ThreeWireMode, 0x08,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityHigh,
                ClockPhaseSecond, "\\SPI",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            SpiSerialBusV2 (0x6789, PolarityLow, FourWireMode, 0x07,
                ControllerInitiated, 0xAABBCCDD, ClockPolarityLow,
                ClockPhaseSecond, "\\SPI",
                0x00, ResourceConsumer, , Exclusive,
                )
        }
    })
    Method (RT24, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "SpiSerialBus Resource Descriptor Macro", "spiserialbus.asl")
        /* The main test packages must have the same number of entries */

        If ((SizeOf (P458) != SizeOf (P459)))
        {
            ERR (__METHOD__, 0xB5, __LINE__, 0x00, 0x00, 0x00, "Incorrect package length")
            Return (Zero)
        }

        /* Main test case for packages above */

        M330 (__METHOD__, SizeOf (P458), "p458", P458, P459)
        /* Check resource descriptor tag offsets */

        Local0 = ResourceTemplate ()
            {
                SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                    DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                    ClockPhaseSecond, "\\SPI",
                    0xEE, ResourceConsumer, , Shared,
                    RawDataBuffer (0x05)  // Vendor Data
                    {
                        0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                    })
                SpiSerialBusV2 (0x6789, PolarityHigh, FourWireMode, 0x07,
                    DeviceInitiated, 0xAABBCCDD, ClockPolarityLow,
                    ClockPhaseSecond, "\\SPI",
                    0xEE, ResourceConsumer, , Exclusive,
                    RawDataBuffer (0x05)  // Vendor Data
                    {
                        0xF0, 0xF1, 0xF2, 0xF3, 0xF4
                    })
            }
        M331 (__METHOD__, 0x01, 0x30, 0x30, 0x0128, 0x0128, "_SLV")
        M331 (__METHOD__, 0x02, 0x38, 0x38, 0x0130, 0x0130, "_MOD")
        M331 (__METHOD__, 0x03, 0x39, 0x39, 0x0131, 0x0131, "_DPL")
        M331 (__METHOD__, 0x04, 0x60, 0x60, 0x0158, 0x0158, "_SPE")
        M331 (__METHOD__, 0x05, 0x80, 0x80, 0x0178, 0x0178, "_LEN")
        M331 (__METHOD__, 0x06, 0x88, 0x88, 0x0180, 0x0180, "_PHA")
        M331 (__METHOD__, 0x07, 0x90, 0x90, 0x0188, 0x0188, "_POL")
        M331 (__METHOD__, 0x08, 0x98, 0x98, 0x0190, 0x0190, "_ADR")
        M331 (__METHOD__, 0x09, 0xA8, 0xA8, 0x01A0, 0x01A0, "_VEN")
    }
