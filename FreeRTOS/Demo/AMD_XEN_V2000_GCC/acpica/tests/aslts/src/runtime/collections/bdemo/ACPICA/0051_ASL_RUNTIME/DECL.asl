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
     * Bug 0051:
     *
     * SUMMARY: Register() macro missing parameter
     *
     * NOTE: introduce into FULL after fixing bug of iASL
     */
    Method (MDDB, 5, NotSerialized)
    {
        If ((Arg0 != Arg1))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg0, Arg1)
        }

        If ((Arg2 != Arg3))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg0, Arg1)
        }
    }

    Method (MDDC, 0, Serialized)
    {
        Name (RT00, ResourceTemplate ()
        {
            Register (SystemMemory,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                0x01,               // Access Size
                )
        })
        Name (BUF0, ResourceTemplate ()
        {
            Register (SystemMemory,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                0x01,               // Access Size
                )
        })
        /* Currently Register macro DescriptorName is not implemented */

        Local0 = ResourceTemplate ()
            {
                Register (SystemMemory,
                    0xF0,               // Bit Width
                    0xF1,               // Bit Offset
                    0xF2F3F4F5F6F7F8F9, // Address
                    ,)
                Register (SystemMemory,
                    0xF0,               // Bit Width
                    0xF1,               // Bit Offset
                    0xF2F3F4F5F6F7F8F9, // Address
                    ,)
            }
        MDDB (0x18, 0x03, 0x90, 0x12, "_ASI")
        MDDB (0x20, 0x04, 0x98, 0x13, "_RBW")
        MDDB (0x28, 0x05, 0xA0, 0x14, "_RBO")
        MDDB (0x30, 0x06, 0xA8, 0x15, "_ASZ")
        MDDB (0x38, 0x07, 0xB0, 0x16, "_ADR")
        If ((RT00 != BUF0))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, RT00, BUF0)
        }
    }
