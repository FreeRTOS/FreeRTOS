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
     * Bug 248:
     *
     * SUMMARY: Incorrect ReferenceCount on Switch operation
     */
    Method (M02D, 0, NotSerialized)
    {
        /*
         * NoOp -
         * all them are for tracking only - to simplify debugging
         */
        Method (M003, 1, Serialized)
        {
            Noop
            Switch (ToInteger (Arg0))
            {
                Case (0x00)
                {
                    Debug = "m003"
                }

            }

            Noop
        }

        Method (M004, 1, NotSerialized)
        {
            Noop
            If (Arg0)
            {
                Debug = "m004"
            }

            Noop
        }

        Method (M1A8, 2, NotSerialized)
        {
            If (Arg1)
            {
                M003 (Arg0)
            }
            Else
            {
                M004 (Arg0)
            }
        }

        Method (M1A9, 0, Serialized)
        {
            Name (SW00, 0x01)
            Name (HG00, 0x00) /* if non-zero - the test hangs */
            Name (P91E, Package (0x01)
            {
                0xABCD0000
            })
            If (0x01)
            {
                Local0 = Local1 = P91E [0x00]
            }
            Else
            {
                Local0 = 0xABCD0000
                Local1 = 0xABCD0001
            }

            If ((DerefOf (Local0) != 0xABCD0000))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, DerefOf (Local0), 0xABCD0000)
            }

            Debug = "============== sit 0 (Local0):"
            M1A8 (Local0, SW00)
            /*
             * At this point, after returning from m1a8
             * for the non-zero sw00, the object attached
             * to Local0 has been deleted. It is the essence
             * of the bug.
             */
            If (HG00)
            {
                /*
                 * To show visually the consequences of the anomaly
                 * run this code. It causes hang.
                 */
                Debug = "============== sit 1 (Local1):"
                M1A8 (Local1, SW00)
                Debug = "============== sit 2:"
                Local7 = ObjectType (Local0)
                Debug = Local7
                Local7 = ObjectType (Local1)
                Debug = Local7
                Debug = Local0
                Debug = Local1
            }

            Debug = "============== before checking:"
            If ((DerefOf (Local0) != 0xABCD0000))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, DerefOf (Local0), 0xABCD0000)
            }

            Debug = "============== end of test"
        }

        Method (MM00, 0, NotSerialized)
        {
            M1A9 ()
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        MM00 ()
        /* Check opcode of the last exception */

        CH04 (__METHOD__, 0x02, 0x2F, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
    }

    /*
     * It is Functional:Reference:ref07.asl:Method(m1d5)
     */
    Method (M03D, 0, Serialized)
    {
        Name (I001, 0x00)
        Name (P000, Package (0x02)
        {
            0x77,
            0x88
        })
        Name (SW00, 0x01)
        Name (HG00, 0x01) /* if non-zero - the test hangs */
        Name (HG01, 0x01) /* if non-zero - the test hangs */
        Name (HG02, 0x01) /* if non-zero - the test hangs */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CopyObject (Local0 = P000 [0x01], I001) /* \M03D.I001 */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        /* Type of i001 should be already IRef here, */
        /* so, don't expect exception. */
        I001 = Local0 = P000 [0x00]
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local7 = (Local0 + 0x01)
        If (Y248)
        {
            HG00 = 0x01
            HG01 = 0x01
            HG02 = 0x01
        }

        /*
         * To show visually the consequences of the anomaly
         * run one of code below. They cause hang.
         */
        If (HG00)
        {
            /* Infinite loop of printing */

            Local1 = 0x00
            Debug = Local0
        }

        If (HG01)
        {
            /* Infinite loop of printing */

            Debug = Local0
            Debug = Local0
        }

        If (HG02)
        {
            Local1 = 0x00
            Debug = "============== sit 2:"
            Local7 = ObjectType (Local0)
            Debug = Local7
        }

        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        Local7 = (I001 + 0x01)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        /*
         * Looks identical to b248: "Incorrect ReferenceCount on Switch operation"
         * (though there is no Switch operation)
         *
         * Reference count of Local0 is mistakenly zeroed there too.
         *
         * [ACPI Debug]  String: [0x0F] "<-------- 0000>"
         * [ACPI Debug]  Reference: [Debug]
         * [ACPI Debug]  String: [0x0F] "<-------- 1111>"
         *
         * [ACPI Debug]  String: [0x0F] "<-------- 0000>"
         * [ACPI Debug]  [ACPI Debug]  String: [0x0F] "<-------- 1111>"
         */
        Debug = "<-------- 0000>"
        Debug = Local0
        Debug = "<-------- 1111>"
    }
