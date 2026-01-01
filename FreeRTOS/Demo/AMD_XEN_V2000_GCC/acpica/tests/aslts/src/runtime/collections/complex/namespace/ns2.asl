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
    Name (Z156, 0x9C)
    /*
     * Check access to elements Package/Buffer/String and Buffer Field
     * where the parent is an element of some complex object (Device).
     */
    Method (M200, 0, Serialized)
    {
        Device (D000)
        {
            Name (P000, Package (0x03)
            {
                0xABCD0000,
                0xABCD0001,
                0xABCD0002
            })
        }

        Method (M001, 2, NotSerialized)
        {
            Arg0 [0x00] = 0x11112222
        }

        M001 (D000.P000, RefOf (D000.P000))
        Local0 = DerefOf (D000.P000 [0x00])
        If ((Local0 != 0x11112222))
        {
            ERR (__METHOD__, Z156, __LINE__, 0x00, 0x00, Local0, 0x11112222)
        }

        CH03 (__METHOD__, Z156, __LINE__, 0x00, 0x00)
    }

    Method (M201, 0, Serialized)
    {
        Device (D000)
        {
            Name (B000, Buffer (0x03)
            {
                 0x10, 0x11, 0x12                                 // ...
            })
        }

        Method (M001, 2, NotSerialized)
        {
            Arg0 [0x00] = 0x67
        }

        M001 (D000.B000, RefOf (D000.B000))
        Local0 = DerefOf (D000.B000 [0x00])
        If ((Local0 != 0x67))
        {
            ERR (__METHOD__, Z156, __LINE__, 0x00, 0x00, Local0, 0x67)
        }

        CH03 (__METHOD__, Z156, __LINE__, 0x00, 0x00)
    }

    Method (M202, 0, Serialized)
    {
        Device (D000)
        {
            Name (S000, "qqqqqqqqqqqqqq")
        }

        Method (M001, 2, NotSerialized)
        {
            Arg0 [0x00] = 0x38
        }

        M001 (D000.S000, RefOf (D000.S000))
        Local0 = DerefOf (D000.S000 [0x00])
        If ((Local0 != 0x38))
        {
            ERR (__METHOD__, Z156, __LINE__, 0x00, 0x00, Local0, 0x38)
        }

        CH03 (__METHOD__, Z156, __LINE__, 0x00, 0x00)
    }

    /*
     * Element of Package instead of i000 (in m002)
     */
    Method (M204, 0, Serialized)
    {
        Name (I001, 0x00)
        Device (D000)
        {
            Name (PP00, Package (0x03)
            {
                0x11111111,
                0x00100000,
                0x22223333
            })
        }

        Method (M001, 0, NotSerialized)
        {
            If ((I001 < 0x64))
            {
                Local0 = DerefOf (^D000.PP00 [0x01])
                Local0++
                ^D000.PP00 [0x01] = Local0
                I001++
                Local0 = (DerefOf (^D000.PP00 [0x01]) + M001 ())
                Return (Local0)
            }

            Return (0x00)
        }

        Store ((DerefOf (D000.PP00 [0x01]) + M001 ()), Local0)
        If ((Local0 != 0x065013BA))
        {
            ERR (__METHOD__, Z156, __LINE__, 0x00, 0x00, Local0, 0x065013BA)
        }

        Local0 = DerefOf (D000.PP00 [0x01])
        If ((Local0 != 0x00100064))
        {
            ERR (__METHOD__, Z156, __LINE__, 0x00, 0x00, Local0, 0x00100064)
        }

        CH03 (__METHOD__, Z156, __LINE__, 0x00, 0x00)
    }

    Method (N002, 0, NotSerialized)
    {
        If (0x01)
        {
            SRMT ("m200")
            M200 ()
            SRMT ("m201")
            M201 ()
            SRMT ("m202")
            M202 ()
            SRMT ("m204")
            M204 ()
        }
        Else
        {
            SRMT ("m200")
            M200 ()
        }
    }
