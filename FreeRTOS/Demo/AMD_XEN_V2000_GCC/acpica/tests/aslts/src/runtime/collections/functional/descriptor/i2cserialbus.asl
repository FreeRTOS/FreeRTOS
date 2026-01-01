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
     * I2cSerialBus Resource Descriptor Macro
     */
    Device (I2C)
    {
    }

    Name (P456, Package (0x12)
    {
        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, DeviceInitiated, 0x88775544,
                AddressingMode7Bit, "\\I2C",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xB1, 0xB2, 0xB3, 0xB4
                })
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, DeviceInitiated, 0x88775544,
                AddressingMode10Bit, "\\I2C",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xB1, 0xB2, 0xB3, 0xB4
                })
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode7Bit, "\\I2C",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xB1, 0xB2, 0xB3, 0xB4
                })
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode10Bit, "\\I2C",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xB1, 0xB2, 0xB3, 0xB4
                })
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, DeviceInitiated, 0x88775544,
                AddressingMode7Bit, "\\I2C",
                0xEE, ResourceProducer, , Shared,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xB1, 0xB2, 0xB3, 0xB4
                })
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, DeviceInitiated, 0x88775544,
                AddressingMode10Bit, "\\I2C",
                0xEE, ResourceProducer, , Shared,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xB1, 0xB2, 0xB3, 0xB4
                })
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode7Bit, "\\I2C",
                0xEE, ResourceProducer, , Shared,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xB1, 0xB2, 0xB3, 0xB4
                })
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode10Bit, "\\I2C",
                0xEE, ResourceProducer, , Shared,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xB1, 0xB2, 0xB3, 0xB4
                })
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, DeviceInitiated, 0x88775544,
                AddressingMode7Bit, "\\I2C",
                0xEE, ResourceConsumer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, DeviceInitiated, 0x88775544,
                AddressingMode10Bit, "\\I2C",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode7Bit, "\\I2C",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode10Bit, "\\I2C",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, DeviceInitiated, 0x88775544,
                AddressingMode7Bit, "\\I2C",
                0xEE, ResourceProducer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, DeviceInitiated, 0x88775544,
                AddressingMode10Bit, "\\I2C",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode7Bit, "\\I2C",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode10Bit, "\\I2C",
                0xEE, ResourceProducer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode7Bit, "\\I2C",
                0x00, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode10Bit, "\\I2C",
                0xEE, ResourceProducer, , Shared,
                RawDataBuffer (0x168)  // Vendor Data
                {
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8
                })
        }
    })
    Name (P457, Package (0x12)
    {
        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, DeviceInitiated, 0x88775544,
                AddressingMode7Bit, "\\I2C",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xB1, 0xB2, 0xB3, 0xB4
                })
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, DeviceInitiated, 0x88775544,
                AddressingMode10Bit, "\\I2C",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xB1, 0xB2, 0xB3, 0xB4
                })
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode7Bit, "\\I2C",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xB1, 0xB2, 0xB3, 0xB4
                })
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode10Bit, "\\I2C",
                0xEE, ResourceConsumer, , Shared,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xB1, 0xB2, 0xB3, 0xB4
                })
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, DeviceInitiated, 0x88775544,
                AddressingMode7Bit, "\\I2C",
                0xEE, ResourceProducer, , Shared,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xB1, 0xB2, 0xB3, 0xB4
                })
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, DeviceInitiated, 0x88775544,
                AddressingMode10Bit, "\\I2C",
                0xEE, ResourceProducer, , Shared,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xB1, 0xB2, 0xB3, 0xB4
                })
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode7Bit, "\\I2C",
                0xEE, ResourceProducer, , Shared,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xB1, 0xB2, 0xB3, 0xB4
                })
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode10Bit, "\\I2C",
                0xEE, ResourceProducer, , Shared,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xB1, 0xB2, 0xB3, 0xB4
                })
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, DeviceInitiated, 0x88775544,
                AddressingMode7Bit, "\\I2C",
                0xEE, ResourceConsumer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, DeviceInitiated, 0x88775544,
                AddressingMode10Bit, "\\I2C",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode7Bit, "\\I2C",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode10Bit, "\\I2C",
                0xEE, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, DeviceInitiated, 0x88775544,
                AddressingMode7Bit, "\\I2C",
                0xEE, ResourceProducer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, DeviceInitiated, 0x88775544,
                AddressingMode10Bit, "\\I2C",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode7Bit, "\\I2C",
                0xEE, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode10Bit, "\\I2C",
                0xEE, ResourceProducer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode7Bit, "\\I2C",
                0x00, ResourceConsumer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            I2cSerialBusV2 (0x1234, ControllerInitiated, 0x88775544,
                AddressingMode10Bit, "\\I2C",
                0xEE, ResourceProducer, , Shared,
                RawDataBuffer (0x168)  // Vendor Data
                {
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8,
                    0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8
                })
        }
    })
    Method (RT23, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "I2cSerialBus Resource Descriptor Macro", "i2cserialbus.asl")
        /* The main test packages must have the same number of entries */

        If ((SizeOf (P456) != SizeOf (P457)))
        {
            ERR (__METHOD__, 0xB4, __LINE__, 0x00, 0x00, 0x00, "Incorrect package length")
            Return (Zero)
        }

        /* Main test case for packages above */

        M330 (__METHOD__, SizeOf (P456), "p456", P456, P457)
        /* Check resource descriptor tag offsets */

        Local0 = ResourceTemplate ()
            {
                I2cSerialBusV2 (0x1234, DeviceInitiated, 0x88775544,
                    AddressingMode10Bit, "\\I2C",
                    0xEE, ResourceConsumer, , Exclusive,
                    RawDataBuffer (0x04)  // Vendor Data
                    {
                        0xB1, 0xB2, 0xB3, 0xB4
                    })
                I2cSerialBusV2 (0x1234, DeviceInitiated, 0x88775544,
                    AddressingMode10Bit, "\\I2C",
                    0xEE, ResourceConsumer, , Exclusive,
                    RawDataBuffer (0x04)  // Vendor Data
                    {
                        0xB1, 0xB2, 0xB3, 0xB4
                    })
            }
        M331 (__METHOD__, 0x01, 0x30, 0x30, 0x0108, 0x0108, "_SLV")
        M331 (__METHOD__, 0x02, 0x38, 0x38, 0x0110, 0x0110, "_MOD")
        M331 (__METHOD__, 0x03, 0x60, 0x60, 0x0138, 0x0138, "_SPE")
        M331 (__METHOD__, 0x04, 0x80, 0x80, 0x0158, 0x0158, "_ADR")
        M331 (__METHOD__, 0x05, 0x90, 0x90, 0x0168, 0x0168, "_VEN")
    }
