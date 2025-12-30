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
     * Exceptions caused by inappropriate type of operands
     */
    Name (Z107, 0x6B)
    /* Run-method */

    Method (EOP2, 0, NotSerialized)
    {
        SRMT ("m4b0")
        M4B0 (0x00)
        SRMT ("m4b1")
        M4B1 (0x76543210)
        SRMT ("m4b2")
        M4B2 ("2")
        SRMT ("m4b3")
        M4B3 (Buffer (0x01)
            {
                 0x62                                             // b
            })
        SRMT ("m4b4")
        M4B4 (Package (0x01)
            {
                0x62
            })
        SRMT ("m4b5")
        M4B5 ()
        SRMT ("m4b6")
        If (Y120)
        {
            M4B6 ()
        }
        Else
        {
            BLCK ()
        }

        SRMT ("m4b7")
        M4B7 ()
        SRMT ("m4b8")
        M4B8 ()
        SRMT ("m4b9")
        M4B9 ()
        SRMT ("m4ba")
        If (Y362)
        {
            M4BA ()
        }
        Else
        {
            BLCK ()
        }

        SRMT ("m4bb")
        M4BB ()
        SRMT ("m4bc")
        M4BC ()
        SRMT ("m4bd")
        If (Y120)
        {
            M4BD ()
        }
        Else
        {
            BLCK ()
        }

        SRMT ("m4be")
        M4BE ()
    }
