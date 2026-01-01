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
     * UartSerialBus Resource Descriptor Macro
     */
    Device (UART)
    {
    }

    Name (P45A, Package (0x28)
    {
        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeEven, FlowControlNone,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeEven, FlowControlXON,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeEven, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeNone, FlowControlNone,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeNone, FlowControlXON,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeNone, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeSpace, FlowControlNone,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeSpace, FlowControlXON,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeSpace, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeMark, FlowControlNone,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeMark, FlowControlXON,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeMark, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeOdd, FlowControlNone,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeOdd, FlowControlXON,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsZero,
                0xA5, BigEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsOne,
                0xA5, BigEndian, ParityTypeOdd, FlowControlNone,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsOnePlusHalf,
                0xA5, BigEndian, ParityTypeOdd, FlowControlXON,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsFive, StopBitsTwo,
                0xA5, BigEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsSix, StopBitsTwo,
                0xA5, BigEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsSeven, StopBitsTwo,
                0xA5, BigEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsNine, StopBitsTwo,
                0xA5, BigEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsZero,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsOne,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlNone,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsOnePlusHalf,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlXON,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsFive, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsSix, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsSeven, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsNine, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsZero,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceProducer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsOne,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlNone,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceProducer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsOnePlusHalf,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlXON,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsFive, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsSix, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsSeven, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsNine, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsOne,
                0xA5, LittleEndian, ParityTypeNone, FlowControlNone,
                0x3300, 0x4400, "\\UART",
                0x00, ResourceConsumer, , Exclusive,
                )
        }
    })
    Name (P45B, Package (0x28)
    {
        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeEven, FlowControlNone,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeEven, FlowControlXON,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeEven, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeNone, FlowControlNone,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeNone, FlowControlXON,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeNone, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeSpace, FlowControlNone,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeSpace, FlowControlXON,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeSpace, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeMark, FlowControlNone,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeMark, FlowControlXON,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeMark, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeOdd, FlowControlNone,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeOdd, FlowControlXON,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsZero,
                0xA5, BigEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsOne,
                0xA5, BigEndian, ParityTypeOdd, FlowControlNone,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsOnePlusHalf,
                0xA5, BigEndian, ParityTypeOdd, FlowControlXON,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsFive, StopBitsTwo,
                0xA5, BigEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsSix, StopBitsTwo,
                0xA5, BigEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsSeven, StopBitsTwo,
                0xA5, BigEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, BigEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsNine, StopBitsTwo,
                0xA5, BigEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsZero,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsOne,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlNone,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsOnePlusHalf,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlXON,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsFive, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsSix, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsSeven, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsNine, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceConsumer, , Exclusive,
                RawDataBuffer (0x07)  // Vendor Data
                {
                    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                })
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsZero,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceProducer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsOne,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlNone,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceProducer, , Shared,
                )
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsOnePlusHalf,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlXON,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsFive, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsSix, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsSeven, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsNine, StopBitsTwo,
                0xA5, LittleEndian, ParityTypeOdd, FlowControlHardware,
                0x3377, 0x4488, "\\UART",
                0x8C, ResourceProducer, , Exclusive,
                )
        },

        ResourceTemplate ()
        {
            UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsOne,
                0xA5, LittleEndian, ParityTypeNone, FlowControlNone,
                0x3300, 0x4400, "\\UART",
                0x00, ResourceConsumer, , Exclusive,
                )
        }
    })
    Method (RT25, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "UartSerialBus Resource Descriptor Macro", "uartserialbus.asl")
        /* The main test packages must have the same number of entries */

        If ((SizeOf (P45A) != SizeOf (P45B)))
        {
            ERR (__METHOD__, 0xB6, __LINE__, 0x00, 0x00, 0x00, "Incorrect package length")
            Return (Zero)
        }

        /* Main test case for packages above */

        M330 (__METHOD__, SizeOf (P45A), "p45A", P45A, P45B)
        /* Check resource descriptor tag offsets */

        Local0 = ResourceTemplate ()
            {
                UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                    0xA5, BigEndian, ParityTypeEven, FlowControlNone,
                    0x3300, 0x4400, "\\UART",
                    0xEE, ResourceProducer, , Shared,
                    RawDataBuffer (0x07)  // Vendor Data
                    {
                        0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                    })
                UartSerialBusV2 (0xFFEEDDCC, DataBitsEight, StopBitsTwo,
                    0xA5, BigEndian, ParityTypeEven, FlowControlNone,
                    0x3300, 0x4400, "\\UART",
                    0xEE, ResourceConsumer, , Exclusive,
                    RawDataBuffer (0x07)  // Vendor Data
                    {
                        0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6
                    })
            }
        M331 (__METHOD__, 0x01, 0x38, 0x38, 0x0150, 0x0150, "_FLC")
        M331 (__METHOD__, 0x02, 0x3A, 0x3A, 0x0152, 0x0152, "_STB")
        M331 (__METHOD__, 0x03, 0x3C, 0x3C, 0x0154, 0x0154, "_LEN")
        M331 (__METHOD__, 0x04, 0x3F, 0x3F, 0x0157, 0x0157, "_END")
        M331 (__METHOD__, 0x05, 0x60, 0x60, 0x0178, 0x0178, "_SPE")
        M331 (__METHOD__, 0x06, 0x80, 0x80, 0x0198, 0x0198, "_RXL")
        M331 (__METHOD__, 0x07, 0x90, 0x90, 0x01A8, 0x01A8, "_TXL")
        M331 (__METHOD__, 0x08, 0xA0, 0xA0, 0x01B8, 0x01B8, "_PAR")
        M331 (__METHOD__, 0x09, 0xA8, 0xA8, 0x01C0, 0x01C0, "_LIN")
        M331 (__METHOD__, 0x0A, 0xB0, 0xB0, 0x01C8, 0x01C8, "_VEN")
    }
