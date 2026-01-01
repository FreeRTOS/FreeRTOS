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
     */
    Name (Z029, 0x1D)
    Name (LPN0, 0x00)
    Name (LPC0, 0x00)
    Method (M330, 5, NotSerialized)
    {
        LPN0 = Arg1
        LPC0 = 0x00
        While (LPN0)
        {
            /* Operand */

            Local0 = DerefOf (Arg3 [LPC0])
            /* Expected result */

            Local1 = DerefOf (Arg4 [LPC0])
            If ((Local0 != Local1))
            {
                ERR (Arg0, Z029, __LINE__, 0x00, 0x00, LPC0, Arg2)
            }

            LPN0--
            LPC0++
        }

        Return (0x00)
    }

    Method (M331, 7, NotSerialized)
    {
        If ((Arg2 != Arg3))
        {
            ERR (Arg0, Z029, __LINE__, Arg6, Arg6, Arg2, Arg3)
        }

        If ((Arg4 != Arg5))
        {
            ERR (Arg0, Z029, __LINE__, Arg6, Arg6, Arg4, Arg5)
        }
    }

    Method (M332, 6, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        LPN0 = Arg1
        LPC0 = 0x00
        While (LPN0)
        {
            /* Operand 1 */

            Local0 = DerefOf (Arg3 [LPC0])
            /* Operand 2 */

            Local1 = DerefOf (Arg4 [LPC0])
            /* Expected result */

            Local2 = DerefOf (Arg5 [LPC0])
            Local3 = ConcatenateResTemplate (Local0, Local1)
            If ((Local3 != Local2))
            {
                Debug = Local3
                Debug = Local2
                ERR (Arg0, Z029, __LINE__, 0x00, 0x00, LPC0, Arg2)
            }

            LPN0--
            LPC0++
        }

        Return (0x00)
    }

    /* components/utilities/utmisc.c AcpiUtGenerateChecksum() analog */

    Method (M335, 2, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        Local0 = 0x00 /* sum */
        LPN0 = Arg1
        LPC0 = 0x00
        While (LPN0)
        {
            Local1 = DerefOf (Arg0 [LPC0])
            Local0 += Local1
            Local0 %= 0x0100
            LPN0--
            LPC0++
        }

        Local0 = (0x00 - Local0)
        Local0 %= 0x0100
        Debug = "checksum"
        Debug = Local0
        Return (Local0)
    }

    /* Updates the last byte of each buffer in package with checksum */

    Method (M334, 2, Serialized)
    {
        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        LPN0 = Arg1
        LPC0 = 0x00
        While (LPN0)
        {
            Local1 = DerefOf (Arg0 [LPC0])
            Local2 = SizeOf (Local1)
            If (Local2)
            {
                Local2--
                Local3 = M335 (Local1, Local2)
                Local1 [Local2] = Local3
                Arg0 [LPC0] = Local1
            }

            LPN0--
            LPC0++
        }

        Return (0x00)
    }
