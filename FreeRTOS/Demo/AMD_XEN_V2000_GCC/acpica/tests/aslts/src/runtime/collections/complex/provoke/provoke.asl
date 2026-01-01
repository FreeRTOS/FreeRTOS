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
     * Check operators under the known critical conditions
     *
     * Collection of the tests which exersice the operators under the
     * known conditions. If some operator was observed failing under some
     * conditions, do the similar checkings for other operators under the
     * similar conditions too.
     */
    Name (Z055, 0x37)
    /* Meaningless zero valued parameter */

    Method (M130, 1, Serialized)
    {
        Name (B000, Buffer (0x02)
        {
             0x21, 0x21                                       // !!
        })
        Local0 = 0x00
        Local2 = ToString (B000, Local0)
        If ((Local0 != 0x00))
        {
            ERR (Arg0, Z055, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (Arg0, Z055, __LINE__, 0x00, 0x00)
    }

    /* Store-like actions affect the source objects passed as parameter */

    Method (M131, 1, NotSerialized)
    {
        Arg0--
        /* Store(9, arg0) */
    }

    /* Operator updates the source object passed to method directly, */
    /* NOT as a reference to it. */
    Method (M132, 1, NotSerialized)
    {
        Local0 = 0x0A
        M131 (Local0)
        If ((Local0 != 0x0A))
        {
            ERR (Arg0, Z055, __LINE__, 0x00, 0x00, Local0, 0x0A)
        }

        CH03 (Arg0, Z055, __LINE__, 0x00, 0x00)
    }

    /* Operator doesn't update the source object passed to method as a REFERENCE */
    /* to the object. */
    Method (M133, 1, NotSerialized)
    {
        Local0 = 0x0A
        Local1 = RefOf (Local0)
        M131 (Local1)
        If ((Local0 != 0x09))
        {
            ERR (Arg0, Z055, __LINE__, 0x00, 0x00, Local0, 0x09)
        }

        CH03 (Arg0, Z055, __LINE__, 0x00, 0x00)
    }

    Method (M134, 1, NotSerialized)
    {
        Local0 = 0x0A
        M131 (RefOf (Local0))
        If ((Local0 != 0x09))
        {
            ERR (Arg0, Z055, __LINE__, 0x00, 0x00, Local0, 0x09)
        }

        CH03 (Arg0, Z055, __LINE__, 0x00, 0x00)
    }

    Method (M135, 1, NotSerialized)
    {
        Arg0 = 0x05
    }

    Method (M136, 1, NotSerialized)
    {
        Local0 = 0x0A
        M135 (RefOf (Local0))
        If ((Local0 != 0x05))
        {
            ERR (Arg0, Z055, __LINE__, 0x00, 0x00, Local0, 0x05)
        }

        CH03 (Arg0, Z055, __LINE__, 0x00, 0x00)
    }

    /* Run-method */

    Method (PRV0, 0, Serialized)
    {
        SRMT ("m130")
        M130 (__METHOD__)
        SRMT ("m132")
        M132 (__METHOD__)
        SRMT ("m133")
        M133 (__METHOD__)
        SRMT ("m134")
        M134 (__METHOD__)
        SRMT ("m136")
        M136 (__METHOD__)
    }
