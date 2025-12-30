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
     * Check implicit conversion being applied to Buffer Field Objects'
     * values obtained by dereference of the references to these Objects.
     */
    Name (Z120, 0x78)
    Method (M61B, 0, Serialized)
    {
        /* Buffer Field to Buffer implicit conversion Cases. */
        /* Buffer Field to Buffer conversion of the Buffer Field second operand */
        /* of Logical operators when the first operand is evaluated as Buffer */
        /* (LEqual, LGreater, LGreaterEqual, LLess, LLessEqual, LNotEqual) */
        Method (M644, 1, NotSerialized)
        {
            /* LEqual */

            Local0 = (Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                    } == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFF   // ..P...|.
                    } == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x01, Local0, Zero)
            Local0 = (AUB4 == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x02, Local0, Ones)
            Local0 = (AUB3 == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x03, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB4)) == DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x04, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUB3)) == DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x05, Local0, Zero)
            }

            Local0 = (DerefOf (PAUB [0x04]) == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x06, Local0, Ones)
            Local0 = (DerefOf (PAUB [0x03]) == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x07, Local0, Zero)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x04) == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x08, Local0, Ones)
            Local0 = (M601 (0x03, 0x03) == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x09, Local0, Zero)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x04, 0x01)) == DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x0A, Local0, Ones)
                Local0 = (DerefOf (M602 (0x03, 0x03, 0x01)) == DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x0B, Local0, Zero)
            }

            /* LGreater */

            Local0 = (Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                    } > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = (Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFF   // ..P...|.
                    } > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFD   // ..P...|.
                    } > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = (Buffer (0x09)
                    {
                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                        /* 0008 */  0x01                                             // .
                    } > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0F, Local0, Ones)
            Local0 = (AUB4 > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x10, Local0, Zero)
            Local0 = (AUB5 > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x11, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB4)) > DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x12, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUB5)) > DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x13, Local0, Ones)
            }

            Local0 = (DerefOf (PAUB [0x04]) > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (DerefOf (PAUB [0x05]) > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x04) > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x16, Local0, Zero)
            Local0 = (M601 (0x03, 0x05) > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x17, Local0, Ones)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x04, 0x01)) > DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x18, Local0, Zero)
                Local0 = (DerefOf (M602 (0x03, 0x05, 0x01)) > DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x19, Local0, Ones)
            }

            /* LGreaterEqual */

            Local0 = (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                        } >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1A, Local0, Ones)
            Local0 = (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFF   // ..P...|.
                        } >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1B, Local0, Ones)
            Local0 = (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFD   // ..P...|.
                        } >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1C, Local0, Zero)
            Local0 = (Buffer (0x09)
                        {
                            /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                            /* 0008 */  0x01                                             // .
                        } >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1D, Local0, Ones)
            Local0 = (AUB4 >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1E, Local0, Ones)
            Local0 = (AUB5 >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB4)) >= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x20, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUB5)) >= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x21, Local0, Ones)
            }

            Local0 = (DerefOf (PAUB [0x04]) >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x22, Local0, Ones)
            Local0 = (DerefOf (PAUB [0x05]) >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x23, Local0, Ones)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x04) >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x24, Local0, Ones)
            Local0 = (M601 (0x03, 0x05) >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x25, Local0, Ones)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x04, 0x01)) >= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x26, Local0, Ones)
                Local0 = (DerefOf (M602 (0x03, 0x05, 0x01)) >= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x27, Local0, Ones)
            }

            /* LLess */

            Local0 = (Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                    } < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x28, Local0, Zero)
            Local0 = (Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFF   // ..P...|.
                    } < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x29, Local0, Zero)
            Local0 = (Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFD   // ..P...|.
                    } < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2A, Local0, Ones)
            Local0 = (Buffer (0x09)
                    {
                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                        /* 0008 */  0x01                                             // .
                    } < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2B, Local0, Zero)
            Local0 = (AUB4 < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2C, Local0, Zero)
            Local0 = (AUB5 < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2D, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB4)) < DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2E, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUB5)) < DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2F, Local0, Zero)
            }

            Local0 = (DerefOf (PAUB [0x04]) < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x30, Local0, Zero)
            Local0 = (DerefOf (PAUB [0x05]) < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x31, Local0, Zero)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x04) < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x32, Local0, Zero)
            Local0 = (M601 (0x03, 0x05) < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x33, Local0, Zero)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x04, 0x01)) < DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x34, Local0, Zero)
                Local0 = (DerefOf (M602 (0x03, 0x05, 0x01)) < DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x35, Local0, Zero)
            }

            /* LLessEqual */

            Local0 = (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                        } <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x36, Local0, Ones)
            Local0 = (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFF   // ..P...|.
                        } <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x37, Local0, Zero)
            Local0 = (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFD   // ..P...|.
                        } <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x38, Local0, Ones)
            Local0 = (Buffer (0x09)
                        {
                            /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                            /* 0008 */  0x01                                             // .
                        } <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x39, Local0, Zero)
            Local0 = (AUB4 <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x3A, Local0, Ones)
            Local0 = (AUB5 <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x3B, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB4)) <= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x3C, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUB5)) <= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x3D, Local0, Zero)
            }

            Local0 = (DerefOf (PAUB [0x04]) <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x3E, Local0, Ones)
            Local0 = (DerefOf (PAUB [0x05]) <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x3F, Local0, Zero)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x04) <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x40, Local0, Ones)
            Local0 = (M601 (0x03, 0x05) <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x41, Local0, Zero)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x04, 0x01)) <= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x42, Local0, Ones)
                Local0 = (DerefOf (M602 (0x03, 0x05, 0x01)) <= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x43, Local0, Zero)
            }

            /* LNotEqual */

            Local0 = (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                        } != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x44, Local0, Zero)
            Local0 = (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFF   // ..P...|.
                        } != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x45, Local0, Ones)
            Local0 = (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFD   // ..P...|.
                        } != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x46, Local0, Ones)
            Local0 = (Buffer (0x09)
                        {
                            /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                            /* 0008 */  0x01                                             // .
                        } != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x47, Local0, Ones)
            Local0 = (AUB4 != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x48, Local0, Zero)
            Local0 = (AUB5 != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x49, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB4)) != DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x4A, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUB5)) != DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x4B, Local0, Ones)
            }

            Local0 = (DerefOf (PAUB [0x04]) != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x4C, Local0, Zero)
            Local0 = (DerefOf (PAUB [0x05]) != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x4D, Local0, Ones)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x04) != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x4E, Local0, Zero)
            Local0 = (M601 (0x03, 0x05) != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x4F, Local0, Ones)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x04, 0x01)) != DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x50, Local0, Zero)
                Local0 = (DerefOf (M602 (0x03, 0x05, 0x01)) != DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x51, Local0, Ones)
            }
        }

        Method (M324, 1, NotSerialized)
        {
            /* LEqual */

            Local0 = (Buffer (0x04)
                    {
                         0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                    } == DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (Buffer (0x04)
                    {
                         0xFE, 0xB3, 0x79, 0xC0                           // ..y.
                    } == DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x01, Local0, Zero)
            Local0 = (AUB3 == DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x02, Local0, Ones)
            Local0 = (AUB2 == DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x03, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB3)) == DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x04, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUB2)) == DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x05, Local0, Zero)
            }

            Local0 = (DerefOf (PAUB [0x03]) == DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x06, Local0, Ones)
            Local0 = (DerefOf (PAUB [0x02]) == DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x07, Local0, Zero)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x03) == DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x08, Local0, Ones)
            Local0 = (M601 (0x03, 0x02) == DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x09, Local0, Zero)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x03, 0x01)) == DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x0A, Local0, Ones)
                Local0 = (DerefOf (M602 (0x03, 0x02, 0x01)) == DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x0B, Local0, Zero)
            }

            /* LGreater */

            Local0 = (Buffer (0x04)
                    {
                         0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                    } > DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = (Buffer (0x04)
                    {
                         0xFE, 0xB3, 0x79, 0xC2                           // ..y.
                    } > DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (Buffer (0x04)
                    {
                         0xFE, 0xB3, 0x79, 0xC0                           // ..y.
                    } > DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = (Buffer (0x05)
                    {
                         0xFE, 0xB3, 0x79, 0xC1, 0x01                     // ..y..
                    } > DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x0F, Local0, Ones)
            Local0 = (AUB3 > DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x10, Local0, Zero)
            Local0 = (AUB2 > DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x11, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB3)) > DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x12, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUB2)) > DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x13, Local0, Ones)
            }

            Local0 = (DerefOf (PAUB [0x03]) > DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (DerefOf (PAUB [0x02]) > DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x03) > DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x16, Local0, Zero)
            Local0 = (M601 (0x03, 0x02) > DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x17, Local0, Ones)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x03, 0x01)) > DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x18, Local0, Zero)
                Local0 = (DerefOf (M602 (0x03, 0x02, 0x01)) > DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x19, Local0, Ones)
            }

            /* LGreaterEqual */

            Local0 = (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                        } >= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x1A, Local0, Ones)
            Local0 = (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC2                           // ..y.
                        } >= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x1B, Local0, Ones)
            Local0 = (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC0                           // ..y.
                        } >= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x1C, Local0, Zero)
            Local0 = (Buffer (0x05)
                        {
                             0xFE, 0xB3, 0x79, 0xC1, 0x01                     // ..y..
                        } >= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x1D, Local0, Ones)
            Local0 = (AUB3 >= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x1E, Local0, Ones)
            Local0 = (AUB2 >= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x1F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB3)) >= DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x20, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUB2)) >= DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x21, Local0, Ones)
            }

            Local0 = (DerefOf (PAUB [0x03]) >= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x22, Local0, Ones)
            Local0 = (DerefOf (PAUB [0x02]) >= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x23, Local0, Ones)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x03) >= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x24, Local0, Ones)
            Local0 = (M601 (0x03, 0x02) >= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x25, Local0, Ones)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x03, 0x01)) >= DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x26, Local0, Ones)
                Local0 = (DerefOf (M602 (0x03, 0x02, 0x01)) >= DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x27, Local0, Ones)
            }

            /* LLess */

            Local0 = (Buffer (0x04)
                    {
                         0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                    } < DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x28, Local0, Zero)
            Local0 = (Buffer (0x04)
                    {
                         0xFE, 0xB3, 0x79, 0xC2                           // ..y.
                    } < DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x29, Local0, Zero)
            Local0 = (Buffer (0x04)
                    {
                         0xFE, 0xB3, 0x79, 0xC0                           // ..y.
                    } < DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x2A, Local0, Ones)
            Local0 = (Buffer (0x05)
                    {
                         0xFE, 0xB3, 0x79, 0xC1, 0x01                     // ..y..
                    } < DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x2B, Local0, Zero)
            Local0 = (AUB3 < DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x2C, Local0, Zero)
            Local0 = (AUB2 < DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x2D, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB3)) < DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x2E, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUB2)) < DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x2F, Local0, Zero)
            }

            Local0 = (DerefOf (PAUB [0x03]) < DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x30, Local0, Zero)
            Local0 = (DerefOf (PAUB [0x02]) < DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x31, Local0, Zero)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x03) < DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x32, Local0, Zero)
            Local0 = (M601 (0x03, 0x02) < DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x33, Local0, Zero)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x03, 0x01)) < DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x34, Local0, Zero)
                Local0 = (DerefOf (M602 (0x03, 0x02, 0x01)) < DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x35, Local0, Zero)
            }

            /* LLessEqual */

            Local0 = (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                        } <= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x36, Local0, Ones)
            Local0 = (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC2                           // ..y.
                        } <= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x37, Local0, Zero)
            Local0 = (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC0                           // ..y.
                        } <= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x38, Local0, Ones)
            Local0 = (Buffer (0x05)
                        {
                             0xFE, 0xB3, 0x79, 0xC1, 0x01                     // ..y..
                        } <= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x39, Local0, Zero)
            Local0 = (AUB3 <= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x3A, Local0, Ones)
            Local0 = (AUB2 <= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x3B, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB3)) <= DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x3C, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUB2)) <= DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x3D, Local0, Zero)
            }

            Local0 = (DerefOf (PAUB [0x03]) <= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x3E, Local0, Ones)
            Local0 = (DerefOf (PAUB [0x02]) <= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x3F, Local0, Zero)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x03) <= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x40, Local0, Ones)
            Local0 = (M601 (0x03, 0x02) <= DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x41, Local0, Zero)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x03, 0x01)) <= DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x42, Local0, Ones)
                Local0 = (DerefOf (M602 (0x03, 0x02, 0x01)) <= DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x43, Local0, Zero)
            }

            /* LNotEqual */

            Local0 = (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                        } != DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x44, Local0, Zero)
            Local0 = (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC2                           // ..y.
                        } != DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x45, Local0, Ones)
            Local0 = (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC0                           // ..y.
                        } != DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x46, Local0, Ones)
            Local0 = (Buffer (0x05)
                        {
                             0xFE, 0xB3, 0x79, 0xC1, 0x01                     // ..y..
                        } != DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x47, Local0, Ones)
            Local0 = (AUB3 != DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x48, Local0, Zero)
            Local0 = (AUB2 != DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x49, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB3)) != DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x4A, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUB2)) != DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x4B, Local0, Ones)
            }

            Local0 = (DerefOf (PAUB [0x03]) != DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x4C, Local0, Zero)
            Local0 = (DerefOf (PAUB [0x02]) != DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x4D, Local0, Ones)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x03) != DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x4E, Local0, Zero)
            Local0 = (M601 (0x03, 0x02) != DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x4F, Local0, Ones)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x03, 0x01)) != DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x50, Local0, Zero)
                Local0 = (DerefOf (M602 (0x03, 0x02, 0x01)) != DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x51, Local0, Ones)
            }
        }

        /* Buffer Field to Buffer conversion of the both Integer operands */
        /* of Concatenate operator */
        Method (M645, 1, NotSerialized)
        {
            Local0 = Concatenate (DerefOf (RefOf (BF65)), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x00, Local0, BB20)
            Local0 = Concatenate (0x0321, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x01, Local0, BB21)
            Local0 = Concatenate (DerefOf (RefOf (BF65)), 0x0321)
            M600 (Arg0, 0x01, Local0, BB22)
            Concatenate (DerefOf (RefOf (BF65)), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x00, Local0, BB20)
            Concatenate (0x0321, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x01, Local0, BB21)
            Concatenate (DerefOf (RefOf (BF65)), 0x0321, Local0)
            M600 (Arg0, 0x01, Local0, BB22)
        }

        Method (M325, 1, NotSerialized)
        {
            Local0 = Concatenate (DerefOf (RefOf (BF62)), DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x00, Local0, BB23)
            Local0 = Concatenate (0x0321, DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x01, Local0, BB24)
            Local0 = Concatenate (DerefOf (RefOf (BF62)), 0x0321)
            M600 (Arg0, 0x01, Local0, BB25)
            Concatenate (DerefOf (RefOf (BF62)), DerefOf (RefOf (BF62)), Local0)
            M600 (Arg0, 0x00, Local0, BB23)
            Concatenate (0x0321, DerefOf (RefOf (BF62)), Local0)
            M600 (Arg0, 0x01, Local0, BB24)
            Concatenate (DerefOf (RefOf (BF62)), 0x0321, Local0)
            M600 (Arg0, 0x01, Local0, BB25)
        }

        /* Buffer Field to Buffer conversion of the Buffer Field second operand */
        /* of Concatenate operator when the first operand is evaluated as Buffer */
        Method (M646, 1, NotSerialized)
        {
            Local0 = Concatenate (Buffer (0x01)
                    {
                         0x5A                                             // Z
                    }, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x00, Local0, BB10)
            Local0 = Concatenate (Buffer (0x02)
                    {
                        "Z"
                    }, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x01, Local0, BB11)
            Local0 = Concatenate (AUB0, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x02, Local0, BB10)
            Local0 = Concatenate (AUB1, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x03, Local0, BB11)
            If (Y078)
            {
                Local0 = Concatenate (DerefOf (RefOf (AUB0)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x04, Local0, BB10)
                Local0 = Concatenate (DerefOf (RefOf (AUB1)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x05, Local0, BB11)
            }

            Local0 = Concatenate (DerefOf (PAUB [0x00]), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x06, Local0, BB10)
            Local0 = Concatenate (DerefOf (PAUB [0x01]), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x07, Local0, BB11)
            /* Method returns Buffer */

            Local0 = Concatenate (M601 (0x03, 0x00), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x08, Local0, BB10)
            Local0 = Concatenate (M601 (0x03, 0x01), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x09, Local0, BB11)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = Concatenate (DerefOf (M602 (0x03, 0x00, 0x01)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x0A, Local0, BB10)
                Local0 = Concatenate (DerefOf (M602 (0x03, 0x01, 0x01)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x0B, Local0, BB11)
            }

            Concatenate (Buffer (0x01)
                {
                     0x5A                                             // Z
                }, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x0C, Local0, BB10)
            Concatenate (Buffer (0x02)
                {
                    "Z"
                }, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x0D, Local0, BB11)
            Concatenate (AUB0, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x0E, Local0, BB10)
            Concatenate (AUB1, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x0F, Local0, BB11)
            If (Y078)
            {
                Concatenate (DerefOf (RefOf (AUB0)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x10, Local0, BB10)
                Concatenate (DerefOf (RefOf (AUB1)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x11, Local0, BB11)
            }

            Concatenate (DerefOf (PAUB [0x00]), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x12, Local0, BB10)
            Concatenate (DerefOf (PAUB [0x01]), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x13, Local0, BB11)
            /* Method returns Buffer */

            Concatenate (M601 (0x03, 0x00), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x14, Local0, BB10)
            Concatenate (M601 (0x03, 0x01), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x15, Local0, BB11)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Concatenate (DerefOf (M602 (0x03, 0x00, 0x01)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x16, Local0, BB10)
                Concatenate (DerefOf (M602 (0x03, 0x01, 0x01)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x17, Local0, BB11)
            }
        }

        Method (M326, 1, NotSerialized)
        {
            Local0 = Concatenate (Buffer (0x01)
                    {
                         0x5A                                             // Z
                    }, DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x00, Local0, BB12)
            Local0 = Concatenate (Buffer (0x02)
                    {
                        "Z"
                    }, DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x01, Local0, BB13)
            Local0 = Concatenate (AUB0, DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x02, Local0, BB12)
            Local0 = Concatenate (AUB1, DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x03, Local0, BB13)
            If (Y078)
            {
                Local0 = Concatenate (DerefOf (RefOf (AUB0)), DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x04, Local0, BB12)
                Local0 = Concatenate (DerefOf (RefOf (AUB1)), DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x05, Local0, BB13)
            }

            Local0 = Concatenate (DerefOf (PAUB [0x00]), DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x06, Local0, BB12)
            Local0 = Concatenate (DerefOf (PAUB [0x01]), DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x07, Local0, BB13)
            /* Method returns Buffer */

            Local0 = Concatenate (M601 (0x03, 0x00), DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x08, Local0, BB12)
            Local0 = Concatenate (M601 (0x03, 0x01), DerefOf (RefOf (BF62)))
            M600 (Arg0, 0x09, Local0, BB13)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = Concatenate (DerefOf (M602 (0x03, 0x00, 0x01)), DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x0A, Local0, BB12)
                Local0 = Concatenate (DerefOf (M602 (0x03, 0x01, 0x01)), DerefOf (RefOf (BF62)))
                M600 (Arg0, 0x0B, Local0, BB13)
            }

            Local0 = Concatenate (Buffer (0x01)
                    {
                         0x5A                                             // Z
                    }, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0C, Local0, BB10)
            Local0 = Concatenate (Buffer (0x02)
                    {
                        "Z"
                    }, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0D, Local0, BB11)
            Concatenate (Buffer (0x01)
                {
                     0x5A                                             // Z
                }, DerefOf (RefOf (BF62)), Local0)
            M600 (Arg0, 0x0E, Local0, BB12)
            Concatenate (Buffer (0x02)
                {
                    "Z"
                }, DerefOf (RefOf (BF62)), Local0)
            M600 (Arg0, 0x0F, Local0, BB13)
            Concatenate (AUB0, DerefOf (RefOf (BF62)), Local0)
            M600 (Arg0, 0x10, Local0, BB12)
            Concatenate (AUB1, DerefOf (RefOf (BF62)), Local0)
            M600 (Arg0, 0x11, Local0, BB13)
            If (Y078)
            {
                Concatenate (DerefOf (RefOf (AUB0)), DerefOf (RefOf (BF62)), Local0)
                M600 (Arg0, 0x12, Local0, BB12)
                Concatenate (DerefOf (RefOf (AUB1)), DerefOf (RefOf (BF62)), Local0)
                M600 (Arg0, 0x13, Local0, BB13)
            }

            Concatenate (DerefOf (PAUB [0x00]), DerefOf (RefOf (BF62)), Local0)
            M600 (Arg0, 0x14, Local0, BB12)
            Concatenate (DerefOf (PAUB [0x01]), DerefOf (RefOf (BF62)), Local0)
            M600 (Arg0, 0x15, Local0, BB13)
            /* Method returns Buffer */

            Concatenate (M601 (0x03, 0x00), DerefOf (RefOf (BF62)), Local0)
            M600 (Arg0, 0x16, Local0, BB12)
            Concatenate (M601 (0x03, 0x01), DerefOf (RefOf (BF62)), Local0)
            M600 (Arg0, 0x17, Local0, BB13)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Concatenate (DerefOf (M602 (0x03, 0x00, 0x01)), DerefOf (RefOf (BF62)), Local0)
                M600 (Arg0, 0x18, Local0, BB12)
                Concatenate (DerefOf (M602 (0x03, 0x01, 0x01)), DerefOf (RefOf (BF62)), Local0)
                M600 (Arg0, 0x19, Local0, BB13)
            }

            Concatenate (Buffer (0x01)
                {
                     0x5A                                             // Z
                }, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x1A, Local0, BB10)
            Concatenate (Buffer (0x02)
                {
                    "Z"
                }, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x1B, Local0, BB11)
        }

        /* Buffer Field to Buffer conversion of the Buffer Field Source operand */
        /* of ToString operator */
        Method (M647, 1, NotSerialized)
        {
            Local0 = ToString (DerefOf (RefOf (BF71)), Ones)
            M600 (Arg0, 0x00, Local0, BS18)
            Local0 = ToString (DerefOf (RefOf (BF71)), 0x03)
            M600 (Arg0, 0x01, Local0, BS19)
            Local0 = ToString (DerefOf (RefOf (BF72)), Ones)
            M600 (Arg0, 0x02, Local0, BS1A)
            Local0 = ToString (DerefOf (RefOf (BF71)), AUI0)
            M600 (Arg0, 0x03, Local0, BS18)
            Local0 = ToString (DerefOf (RefOf (BF71)), AUI7)
            M600 (Arg0, 0x04, Local0, BS19)
            Local0 = ToString (DerefOf (RefOf (BF72)), AUI0)
            M600 (Arg0, 0x05, Local0, BS1A)
            If (Y078)
            {
                Local0 = ToString (DerefOf (RefOf (BF71)), DerefOf (RefOf (AUI0)))
                M600 (Arg0, 0x06, Local0, BS18)
                Local0 = ToString (DerefOf (RefOf (BF71)), DerefOf (RefOf (AUI7)))
                M600 (Arg0, 0x07, Local0, BS19)
                Local0 = ToString (DerefOf (RefOf (BF72)), DerefOf (RefOf (AUI0)))
                M600 (Arg0, 0x08, Local0, BS1A)
            }

            Local0 = ToString (DerefOf (RefOf (BF71)), DerefOf (PAUI [0x00]))
            M600 (Arg0, 0x09, Local0, BS18)
            Local0 = ToString (DerefOf (RefOf (BF71)), DerefOf (PAUI [0x07]))
            M600 (Arg0, 0x0A, Local0, BS19)
            Local0 = ToString (DerefOf (RefOf (BF72)), DerefOf (PAUI [0x00]))
            M600 (Arg0, 0x0B, Local0, BS1A)
            /* Method returns Length parameter */

            Local0 = ToString (DerefOf (RefOf (BF71)), M601 (0x01, 0x00))
            M600 (Arg0, 0x0C, Local0, BS18)
            Local0 = ToString (DerefOf (RefOf (BF71)), M601 (0x01, 0x07))
            M600 (Arg0, 0x0D, Local0, BS19)
            Local0 = ToString (DerefOf (RefOf (BF72)), M601 (0x01, 0x00))
            M600 (Arg0, 0x0E, Local0, BS1A)
            /* Method returns Reference to Length parameter */

            If (Y500)
            {
                Local0 = ToString (DerefOf (RefOf (BF71)), DerefOf (M601 (0x01, 0x00)))
                M600 (Arg0, 0x0F, Local0, BS18)
                Local0 = ToString (DerefOf (RefOf (BF71)), DerefOf (M601 (0x01, 0x07)))
                M600 (Arg0, 0x10, Local0, BS19)
                Local0 = ToString (DerefOf (RefOf (BF72)), DerefOf (M601 (0x01, 0x00)))
                M600 (Arg0, 0x11, Local0, BS1A)
            }

            ToString (DerefOf (RefOf (BF71)), Ones, Local0)
            M600 (Arg0, 0x12, Local0, BS18)
            ToString (DerefOf (RefOf (BF71)), 0x03, Local0)
            M600 (Arg0, 0x13, Local0, BS19)
            ToString (DerefOf (RefOf (BF72)), Ones, Local0)
            M600 (Arg0, 0x14, Local0, BS1A)
            ToString (DerefOf (RefOf (BF71)), AUI0, Local0)
            M600 (Arg0, 0x15, Local0, BS18)
            ToString (DerefOf (RefOf (BF71)), AUI7, Local0)
            M600 (Arg0, 0x16, Local0, BS19)
            ToString (DerefOf (RefOf (BF72)), AUI0, Local0)
            M600 (Arg0, 0x17, Local0, BS1A)
            If (Y078)
            {
                ToString (DerefOf (RefOf (BF71)), DerefOf (RefOf (AUI0)), Local0)
                M600 (Arg0, 0x18, Local0, BS18)
                ToString (DerefOf (RefOf (BF71)), DerefOf (RefOf (AUI7)), Local0)
                M600 (Arg0, 0x19, Local0, BS19)
                ToString (DerefOf (RefOf (BF72)), DerefOf (RefOf (AUI0)), Local0)
                M600 (Arg0, 0x1A, Local0, BS1A)
            }

            ToString (DerefOf (RefOf (BF71)), DerefOf (PAUI [0x00]), Local0)
            M600 (Arg0, 0x1B, Local0, BS18)
            ToString (DerefOf (RefOf (BF71)), DerefOf (PAUI [0x07]), Local0)
            M600 (Arg0, 0x1C, Local0, BS19)
            ToString (DerefOf (RefOf (BF72)), DerefOf (PAUI [0x00]), Local0)
            M600 (Arg0, 0x1D, Local0, BS1A)
            /* Method returns Length parameter */

            ToString (DerefOf (RefOf (BF71)), M601 (0x01, 0x00), Local0)
            M600 (Arg0, 0x1E, Local0, BS18)
            ToString (DerefOf (RefOf (BF71)), M601 (0x01, 0x07), Local0)
            M600 (Arg0, 0x1F, Local0, BS19)
            ToString (DerefOf (RefOf (BF72)), M601 (0x01, 0x00), Local0)
            M600 (Arg0, 0x20, Local0, BS1A)
            /* Method returns Reference to Length parameter */

            If (Y500)
            {
                ToString (DerefOf (RefOf (BF71)), DerefOf (M601 (0x01, 0x00)), Local0)
                M600 (Arg0, 0x21, Local0, BS18)
                ToString (DerefOf (RefOf (BF71)), DerefOf (M601 (0x01, 0x07)), Local0)
                M600 (Arg0, 0x22, Local0, BS19)
                ToString (DerefOf (RefOf (BF72)), DerefOf (M601 (0x01, 0x00)), Local0)
                M600 (Arg0, 0x23, Local0, BS1A)
            }
        }

        Method (M327, 1, NotSerialized)
        {
            Local0 = ToString (DerefOf (RefOf (BF70)), Ones)
            M600 (Arg0, 0x00, Local0, BS16)
            Local0 = ToString (DerefOf (RefOf (BF70)), 0x03)
            M600 (Arg0, 0x01, Local0, BS17)
            Local0 = ToString (DerefOf (RefOf (BF73)), Ones)
            M600 (Arg0, 0x02, Local0, BS1A)
            Local0 = ToString (DerefOf (RefOf (BF70)), AUI0)
            M600 (Arg0, 0x03, Local0, BS16)
            Local0 = ToString (DerefOf (RefOf (BF70)), AUI7)
            M600 (Arg0, 0x04, Local0, BS17)
            Local0 = ToString (DerefOf (RefOf (BF73)), AUI0)
            M600 (Arg0, 0x05, Local0, BS1A)
            If (Y078)
            {
                Local0 = ToString (DerefOf (RefOf (BF70)), DerefOf (RefOf (AUI0)))
                M600 (Arg0, 0x06, Local0, BS16)
                Local0 = ToString (DerefOf (RefOf (BF70)), DerefOf (RefOf (AUI7)))
                M600 (Arg0, 0x07, Local0, BS17)
                Local0 = ToString (DerefOf (RefOf (BF73)), DerefOf (RefOf (AUI0)))
                M600 (Arg0, 0x08, Local0, BS1A)
            }

            Local0 = ToString (DerefOf (RefOf (BF70)), DerefOf (PAUI [0x00]))
            M600 (Arg0, 0x09, Local0, BS16)
            Local0 = ToString (DerefOf (RefOf (BF70)), DerefOf (PAUI [0x07]))
            M600 (Arg0, 0x0A, Local0, BS17)
            Local0 = ToString (DerefOf (RefOf (BF73)), DerefOf (PAUI [0x00]))
            M600 (Arg0, 0x0B, Local0, BS1A)
            /* Method returns Length parameter */

            Local0 = ToString (DerefOf (RefOf (BF70)), M601 (0x01, 0x00))
            M600 (Arg0, 0x0C, Local0, BS16)
            Local0 = ToString (DerefOf (RefOf (BF70)), M601 (0x01, 0x07))
            M600 (Arg0, 0x0D, Local0, BS17)
            Local0 = ToString (DerefOf (RefOf (BF73)), M601 (0x01, 0x00))
            M600 (Arg0, 0x0E, Local0, BS1A)
            /* Method returns Reference to Length parameter */

            If (Y500)
            {
                Local0 = ToString (DerefOf (RefOf (BF70)), DerefOf (M601 (0x01, 0x00)))
                M600 (Arg0, 0x0F, Local0, BS16)
                Local0 = ToString (DerefOf (RefOf (BF70)), DerefOf (M601 (0x01, 0x07)))
                M600 (Arg0, 0x10, Local0, BS17)
                Local0 = ToString (DerefOf (RefOf (BF73)), DerefOf (M601 (0x01, 0x00)))
                M600 (Arg0, 0x11, Local0, BS1A)
            }

            ToString (DerefOf (RefOf (BF70)), Ones, Local0)
            M600 (Arg0, 0x12, Local0, BS16)
            ToString (DerefOf (RefOf (BF70)), 0x03, Local0)
            M600 (Arg0, 0x13, Local0, BS17)
            ToString (DerefOf (RefOf (BF73)), Ones, Local0)
            M600 (Arg0, 0x14, Local0, BS1A)
            ToString (DerefOf (RefOf (BF70)), AUI0, Local0)
            M600 (Arg0, 0x15, Local0, BS16)
            ToString (DerefOf (RefOf (BF70)), AUI7, Local0)
            M600 (Arg0, 0x16, Local0, BS17)
            ToString (DerefOf (RefOf (BF73)), AUI0, Local0)
            M600 (Arg0, 0x17, Local0, BS1A)
            If (Y078)
            {
                ToString (DerefOf (RefOf (BF70)), DerefOf (RefOf (AUI0)), Local0)
                M600 (Arg0, 0x18, Local0, BS16)
                ToString (DerefOf (RefOf (BF70)), DerefOf (RefOf (AUI7)), Local0)
                M600 (Arg0, 0x19, Local0, BS17)
                ToString (DerefOf (RefOf (BF73)), DerefOf (RefOf (AUI0)), Local0)
                M600 (Arg0, 0x1A, Local0, BS1A)
            }

            ToString (DerefOf (RefOf (BF70)), DerefOf (PAUI [0x00]), Local0)
            M600 (Arg0, 0x1B, Local0, BS16)
            ToString (DerefOf (RefOf (BF70)), DerefOf (PAUI [0x07]), Local0)
            M600 (Arg0, 0x1C, Local0, BS17)
            ToString (DerefOf (RefOf (BF73)), DerefOf (PAUI [0x00]), Local0)
            M600 (Arg0, 0x1D, Local0, BS1A)
            /* Method returns Length parameter */

            ToString (DerefOf (RefOf (BF70)), M601 (0x01, 0x00), Local0)
            M600 (Arg0, 0x1E, Local0, BS16)
            ToString (DerefOf (RefOf (BF70)), M601 (0x01, 0x07), Local0)
            M600 (Arg0, 0x1F, Local0, BS17)
            ToString (DerefOf (RefOf (BF73)), M601 (0x01, 0x00), Local0)
            M600 (Arg0, 0x20, Local0, BS1A)
            /* Method returns Reference to Length parameter */

            If (Y500)
            {
                ToString (DerefOf (RefOf (BF70)), DerefOf (M601 (0x01, 0x00)), Local0)
                M600 (Arg0, 0x21, Local0, BS16)
                ToString (DerefOf (RefOf (BF70)), DerefOf (M601 (0x01, 0x07)), Local0)
                M600 (Arg0, 0x22, Local0, BS17)
                ToString (DerefOf (RefOf (BF73)), DerefOf (M601 (0x01, 0x00)), Local0)
                M600 (Arg0, 0x23, Local0, BS1A)
            }
        }

        /* Buffer Field to Buffer conversion of the Buffer Field Source operand */
        /* of Mid operator */
        Method (M648, 1, NotSerialized)
        {
            Local0 = Mid (DerefOf (RefOf (BF65)), 0x00, 0x09)
            M600 (Arg0, 0x00, Local0, BB1D)
            Local0 = Mid (DerefOf (RefOf (BF66)), 0x00, 0x09)
            M600 (Arg0, 0x01, Local0, BB1F)
            Local0 = Mid (DerefOf (RefOf (BF73)), 0x01, 0x08)
            M600 (Arg0, 0x02, Local0, BB30)
            Local0 = Mid (DerefOf (RefOf (BF65)), AUI5, AUIB)
            M600 (Arg0, 0x03, Local0, BB1D)
            Local0 = Mid (DerefOf (RefOf (BF66)), AUI5, AUIB)
            M600 (Arg0, 0x04, Local0, BB1F)
            Local0 = Mid (DerefOf (RefOf (BF73)), AUI6, AUIA)
            M600 (Arg0, 0x05, Local0, BB30)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUI5)), DerefOf (RefOf (AUIB))
                    )
                M600 (Arg0, 0x06, Local0, BB1D)
                Local0 = Mid (DerefOf (RefOf (BF66)), DerefOf (RefOf (AUI5)), DerefOf (RefOf (AUIB))
                    )
                M600 (Arg0, 0x07, Local0, BB1F)
                Local0 = Mid (DerefOf (RefOf (BF73)), DerefOf (RefOf (AUI6)), DerefOf (RefOf (AUIA))
                    )
                M600 (Arg0, 0x08, Local0, BB30)
            }

            Local0 = Mid (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x05]), DerefOf (
                PAUI [0x0B]))
            M600 (Arg0, 0x09, Local0, BB1D)
            Local0 = Mid (DerefOf (RefOf (BF66)), DerefOf (PAUI [0x05]), DerefOf (
                PAUI [0x0B]))
            M600 (Arg0, 0x0A, Local0, BB1F)
            Local0 = Mid (DerefOf (RefOf (BF73)), DerefOf (PAUI [0x06]), DerefOf (
                PAUI [0x0A]))
            M600 (Arg0, 0x0B, Local0, BB30)
            /* Method returns Index and Length parameters */

            Local0 = Mid (DerefOf (RefOf (BF65)), M601 (0x01, 0x05), M601 (0x01, 0x0B)
                )
            M600 (Arg0, 0x0C, Local0, BB1D)
            Local0 = Mid (DerefOf (RefOf (BF66)), M601 (0x01, 0x05), M601 (0x01, 0x0B)
                )
            M600 (Arg0, 0x0D, Local0, BB1F)
            Local0 = Mid (DerefOf (RefOf (BF73)), M601 (0x01, 0x06), M601 (0x01, 0x0A)
                )
            M600 (Arg0, 0x0E, Local0, BB30)
            /* Method returns Reference to Index and Length parameters */

            If (Y500)
            {
                Local0 = Mid (DerefOf (RefOf (BF65)), DerefOf (M601 (0x01, 0x05)), DerefOf (M601 (
                    0x01, 0x0B)))
                M600 (Arg0, 0x0F, Local0, BB1D)
                Local0 = Mid (DerefOf (RefOf (BF66)), DerefOf (M601 (0x01, 0x05)), DerefOf (M601 (
                    0x01, 0x0B)))
                M600 (Arg0, 0x10, Local0, BB1F)
                Local0 = Mid (DerefOf (RefOf (BF73)), DerefOf (M601 (0x01, 0x06)), DerefOf (M601 (
                    0x01, 0x0A)))
                M600 (Arg0, 0x11, Local0, BB30)
            }

            Mid (DerefOf (RefOf (BF65)), 0x00, 0x09, Local0)
            M600 (Arg0, 0x12, Local0, BB1D)
            Mid (DerefOf (RefOf (BF66)), 0x00, 0x09, Local0)
            M600 (Arg0, 0x13, Local0, BB1F)
            Mid (DerefOf (RefOf (BF73)), 0x01, 0x08, Local0)
            M600 (Arg0, 0x14, Local0, BB30)
            Mid (DerefOf (RefOf (BF65)), AUI5, AUIB, Local0)
            M600 (Arg0, 0x15, Local0, BB1D)
            Mid (DerefOf (RefOf (BF66)), AUI5, AUIB, Local0)
            M600 (Arg0, 0x16, Local0, BB1F)
            Mid (DerefOf (RefOf (BF73)), AUI6, AUIA, Local0)
            M600 (Arg0, 0x17, Local0, BB30)
            If (Y078)
            {
                Mid (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUI5)), DerefOf (RefOf (AUIB)), Local0)
                M600 (Arg0, 0x18, Local0, BB1D)
                Mid (DerefOf (RefOf (BF66)), DerefOf (RefOf (AUI5)), DerefOf (RefOf (AUIB)), Local0)
                M600 (Arg0, 0x19, Local0, BB1F)
                Mid (DerefOf (RefOf (BF73)), DerefOf (RefOf (AUI6)), DerefOf (RefOf (AUIA)), Local0)
                M600 (Arg0, 0x1A, Local0, BB30)
            }

            Mid (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x05]), DerefOf (PAUI [
                0x0B]), Local0)
            M600 (Arg0, 0x1B, Local0, BB1D)
            Mid (DerefOf (RefOf (BF66)), DerefOf (PAUI [0x05]), DerefOf (PAUI [
                0x0B]), Local0)
            M600 (Arg0, 0x1C, Local0, BB1F)
            Mid (DerefOf (RefOf (BF73)), DerefOf (PAUI [0x06]), DerefOf (PAUI [
                0x0A]), Local0)
            M600 (Arg0, 0x1D, Local0, BB30)
            /* Method returns Index and Length parameters */

            Mid (DerefOf (RefOf (BF65)), M601 (0x01, 0x05), M601 (0x01, 0x0B), Local0)
            M600 (Arg0, 0x1E, Local0, BB1D)
            Mid (DerefOf (RefOf (BF66)), M601 (0x01, 0x05), M601 (0x01, 0x0B), Local0)
            M600 (Arg0, 0x1F, Local0, BB1F)
            Mid (DerefOf (RefOf (BF73)), M601 (0x01, 0x06), M601 (0x01, 0x0A), Local0)
            M600 (Arg0, 0x20, Local0, BB30)
            /* Method returns Reference to Index and Length parameters */

            If (Y500)
            {
                Mid (DerefOf (RefOf (BF65)), DerefOf (M601 (0x01, 0x05)), DerefOf (M601 (0x01, 0x0B)),
                    Local0)
                M600 (Arg0, 0x21, Local0, BB1D)
                Mid (DerefOf (RefOf (BF66)), DerefOf (M601 (0x01, 0x05)), DerefOf (M601 (0x01, 0x0B)),
                    Local0)
                M600 (Arg0, 0x22, Local0, BB1F)
                Mid (DerefOf (RefOf (BF73)), DerefOf (M601 (0x01, 0x06)), DerefOf (M601 (0x01, 0x0A)),
                    Local0)
                M600 (Arg0, 0x23, Local0, BB30)
            }
        }

        Method (M328, 1, NotSerialized)
        {
            Local0 = Mid (DerefOf (RefOf (BF62)), 0x00, 0x05)
            M600 (Arg0, 0x00, Local0, BB1C)
            Local0 = Mid (DerefOf (RefOf (BF63)), 0x00, 0x05)
            M600 (Arg0, 0x01, Local0, BB1E)
            Local0 = Mid (DerefOf (RefOf (BF77)), 0x01, 0x04)
            M600 (Arg0, 0x02, Local0, BB31)
            Local0 = Mid (DerefOf (RefOf (BF62)), AUI5, AUI9)
            M600 (Arg0, 0x03, Local0, BB1C)
            Local0 = Mid (DerefOf (RefOf (BF63)), AUI5, AUI9)
            M600 (Arg0, 0x04, Local0, BB1E)
            Local0 = Mid (DerefOf (RefOf (BF77)), AUI6, AUI8)
            M600 (Arg0, 0x05, Local0, BB31)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (BF62)), DerefOf (RefOf (AUI5)), DerefOf (RefOf (AUI9))
                    )
                M600 (Arg0, 0x06, Local0, BB1C)
                Local0 = Mid (DerefOf (RefOf (BF63)), DerefOf (RefOf (AUI5)), DerefOf (RefOf (AUI9))
                    )
                M600 (Arg0, 0x07, Local0, BB1E)
                Local0 = Mid (DerefOf (RefOf (BF77)), DerefOf (RefOf (AUI6)), DerefOf (RefOf (AUI8))
                    )
                M600 (Arg0, 0x08, Local0, BB31)
            }

            Local0 = Mid (DerefOf (RefOf (BF62)), DerefOf (PAUI [0x05]), DerefOf (
                PAUI [0x09]))
            M600 (Arg0, 0x09, Local0, BB1C)
            Local0 = Mid (DerefOf (RefOf (BF63)), DerefOf (PAUI [0x05]), DerefOf (
                PAUI [0x09]))
            M600 (Arg0, 0x0A, Local0, BB1E)
            Local0 = Mid (DerefOf (RefOf (BF77)), DerefOf (PAUI [0x06]), DerefOf (
                PAUI [0x08]))
            M600 (Arg0, 0x0B, Local0, BB31)
            /* Method returns Index and Length parameters */

            Local0 = Mid (DerefOf (RefOf (BF62)), M601 (0x01, 0x05), M601 (0x01, 0x09)
                )
            M600 (Arg0, 0x0C, Local0, BB1C)
            Local0 = Mid (DerefOf (RefOf (BF63)), M601 (0x01, 0x05), M601 (0x01, 0x09)
                )
            M600 (Arg0, 0x0D, Local0, BB1E)
            Local0 = Mid (DerefOf (RefOf (BF77)), M601 (0x01, 0x06), M601 (0x01, 0x08)
                )
            M600 (Arg0, 0x0E, Local0, BB31)
            /* Method returns Reference to Index and Length parameters */

            If (Y500)
            {
                Local0 = Mid (DerefOf (RefOf (BF62)), DerefOf (M601 (0x01, 0x05)), DerefOf (M601 (
                    0x01, 0x09)))
                M600 (Arg0, 0x0F, Local0, BB1C)
                Local0 = Mid (DerefOf (RefOf (BF63)), DerefOf (M601 (0x01, 0x05)), DerefOf (M601 (
                    0x01, 0x09)))
                M600 (Arg0, 0x10, Local0, BB1E)
                Local0 = Mid (DerefOf (RefOf (BF77)), DerefOf (M601 (0x01, 0x06)), DerefOf (M601 (
                    0x01, 0x08)))
                M600 (Arg0, 0x11, Local0, BB31)
            }

            Mid (DerefOf (RefOf (BF62)), 0x00, 0x05, Local0)
            M600 (Arg0, 0x12, Local0, BB1C)
            Mid (DerefOf (RefOf (BF63)), 0x00, 0x05, Local0)
            M600 (Arg0, 0x13, Local0, BB1E)
            Mid (DerefOf (RefOf (BF77)), 0x01, 0x04, Local0)
            M600 (Arg0, 0x14, Local0, BB31)
            Mid (DerefOf (RefOf (BF62)), AUI5, AUI9, Local0)
            M600 (Arg0, 0x15, Local0, BB1C)
            Mid (DerefOf (RefOf (BF63)), AUI5, AUI9, Local0)
            M600 (Arg0, 0x16, Local0, BB1E)
            Mid (DerefOf (RefOf (BF77)), AUI6, AUI8, Local0)
            M600 (Arg0, 0x17, Local0, BB31)
            If (Y078)
            {
                Mid (DerefOf (RefOf (BF62)), DerefOf (RefOf (AUI5)), DerefOf (RefOf (AUI9)), Local0)
                M600 (Arg0, 0x18, Local0, BB1C)
                Mid (DerefOf (RefOf (BF63)), DerefOf (RefOf (AUI5)), DerefOf (RefOf (AUI9)), Local0)
                M600 (Arg0, 0x19, Local0, BB1E)
                Mid (DerefOf (RefOf (BF77)), DerefOf (RefOf (AUI6)), DerefOf (RefOf (AUI8)), Local0)
                M600 (Arg0, 0x1A, Local0, BB31)
            }

            Mid (DerefOf (RefOf (BF62)), DerefOf (PAUI [0x05]), DerefOf (PAUI [
                0x09]), Local0)
            M600 (Arg0, 0x1B, Local0, BB1C)
            Mid (DerefOf (RefOf (BF63)), DerefOf (PAUI [0x05]), DerefOf (PAUI [
                0x09]), Local0)
            M600 (Arg0, 0x1C, Local0, BB1E)
            Mid (DerefOf (RefOf (BF77)), DerefOf (PAUI [0x06]), DerefOf (PAUI [
                0x08]), Local0)
            M600 (Arg0, 0x1D, Local0, BB31)
            /* Method returns Index and Length parameters */

            Mid (DerefOf (RefOf (BF62)), M601 (0x01, 0x05), M601 (0x01, 0x09), Local0)
            M600 (Arg0, 0x1E, Local0, BB1C)
            Mid (DerefOf (RefOf (BF63)), M601 (0x01, 0x05), M601 (0x01, 0x09), Local0)
            M600 (Arg0, 0x1F, Local0, BB1E)
            Mid (DerefOf (RefOf (BF77)), M601 (0x01, 0x06), M601 (0x01, 0x08), Local0)
            M600 (Arg0, 0x20, Local0, BB31)
            /* Method returns Reference to Index and Length parameters */

            If (Y500)
            {
                Mid (DerefOf (RefOf (BF62)), DerefOf (M601 (0x01, 0x05)), DerefOf (M601 (0x01, 0x09)),
                    Local0)
                M600 (Arg0, 0x21, Local0, BB1C)
                Mid (DerefOf (RefOf (BF63)), DerefOf (M601 (0x01, 0x05)), DerefOf (M601 (0x01, 0x09)),
                    Local0)
                M600 (Arg0, 0x22, Local0, BB1E)
                Mid (DerefOf (RefOf (BF77)), DerefOf (M601 (0x01, 0x06)), DerefOf (M601 (0x01, 0x08)),
                    Local0)
                M600 (Arg0, 0x23, Local0, BB31)
            }
        }

        /* Buffer Field to Integer implicit conversion Cases. */
        /* Buffer Field to Integer conversion of the Buffer Field sole operand */
        /* of the 1-parameter Integer arithmetic operators */
        /* (Decrement, Increment, FindSetLeftBit, FindSetRightBit, Not) */
        Method (M64L, 1, NotSerialized)
        {
            If (Y365)
            {
                /* Decrement */

                Local0 = DerefOf (RefOf (BF91))--
                M600 (Arg0, 0x00, Local0, BI12)
                Local0 = DerefOf (RefOf (BF95))--
                M600 (Arg0, 0x01, Local0, BI16)
                /* Increment */

                Local0 = DerefOf (RefOf (BFA1))++
                M600 (Arg0, 0x02, Local0, BI23)
                Local0 = DerefOf (RefOf (BFA5))++
                M600 (Arg0, 0x03, Local0, BI27)
            }

            /* FindSetLeftBit */

            Local0 = FindSetLeftBit (DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x00, Local0, 0x0A)
            Local0 = FindSetLeftBit (DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x01, Local0, 0x40)
            /* FindSetRightBit */

            Local0 = FindSetRightBit (DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x02, Local0, 0x01)
            Local0 = FindSetRightBit (DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x03, Local0, 0x03)
            /* Not */

            Store (~DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x04, Local0, 0xFFFFFFFFFFFFFCDE)
            Store (~DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x05, Local0, 0x01834C6E29AF5D7B)
        }

        Method (M32L, 1, NotSerialized)
        {
            If (Y365)
            {
                /* Decrement */

                Local0 = DerefOf (RefOf (BF91))--
                M600 (Arg0, 0x00, Local0, BI12)
                Local0 = DerefOf (RefOf (BF95))--
                M600 (Arg0, 0x01, Local0, BI18)
                /* Increment */

                Local0 = DerefOf (RefOf (BFA1))++
                M600 (Arg0, 0x02, Local0, BI23)
                Local0 = DerefOf (RefOf (BFA5))++
                M600 (Arg0, 0x03, Local0, BI29)
            }

            /* FindSetLeftBit */

            Local0 = FindSetLeftBit (DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x00, Local0, 0x0A)
            Local0 = FindSetLeftBit (DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x01, Local0, 0x20)
            /* FindSetRightBit */

            Local0 = FindSetRightBit (DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x02, Local0, 0x01)
            Local0 = FindSetRightBit (DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x03, Local0, 0x03)
            /* Not */

            Store (~DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x04, Local0, 0xFFFFFCDE)
            Store (~DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x05, Local0, 0x29AF5D7B)
        }

        /* Buffer Field to Integer conversion of the Buffer Field sole operand */
        /* of the LNot Logical Integer operator */
        Method (M03A, 1, NotSerialized)
        {
            Local0 = !DerefOf (RefOf (BF76))
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = !DerefOf (RefOf (BF61))
            M600 (Arg0, 0x01, Local0, Zero)
            If (F64)
            {
                Local0 = !DerefOf (RefOf (BF65))
                M600 (Arg0, 0x02, Local0, Zero)
            }
            Else
            {
                Local0 = !DerefOf (RefOf (BF65))
                M600 (Arg0, 0x03, Local0, Zero)
            }
        }

        /* Buffer Field to Integer conversion of the Buffer Field sole operand */
        /* of the FromBCD and ToBCD conversion operators */
        Method (M64M, 1, NotSerialized)
        {
            /* FromBCD */

            Local0 = FromBCD (DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x02, Local0, 0x0141)
            Local0 = FromBCD (DerefOf (RefOf (BF6C)))
            M600 (Arg0, 0x03, Local0, 0x000D76162EE9EC35)
            FromBCD (DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x02, Local0, 0x0141)
            FromBCD (DerefOf (RefOf (BF6C)), Local0)
            M600 (Arg0, 0x03, Local0, 0x000D76162EE9EC35)
            /* ToBCD */

            Local0 = ToBCD (DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x04, Local0, 0x0801)
            /* ??? No error of iASL on constant folding */

            Local0 = ToBCD (DerefOf (RefOf (BF6D)))
            M600 (Arg0, 0x05, Local0, 0x3789012345678901)
            ToBCD (DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x04, Local0, 0x0801)
            ToBCD (DerefOf (RefOf (BF6D)), Local0)
            M600 (Arg0, 0x05, Local0, 0x3789012345678901)
        }

        Method (M32M, 1, NotSerialized)
        {
            /* FromBCD */

            Local0 = FromBCD (DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x02, Local0, 0x0141)
            Local0 = FromBCD (DerefOf (RefOf (BF6E)))
            M600 (Arg0, 0x03, Local0, 0x055F2CC0)
            FromBCD (DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x02, Local0, 0x0141)
            FromBCD (DerefOf (RefOf (BF6E)), Local0)
            M600 (Arg0, 0x03, Local0, 0x055F2CC0)
            /* ToBCD */

            Local0 = ToBCD (DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x04, Local0, 0x0801)
            Local0 = ToBCD (DerefOf (RefOf (BF6F)))
            M600 (Arg0, 0x05, Local0, 0x90123456)
            ToBCD (DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x04, Local0, 0x0801)
            ToBCD (DerefOf (RefOf (BF6F)), Local0)
            M600 (Arg0, 0x05, Local0, 0x90123456)
        }

        /* Buffer Field to Integer conversion of each Buffer operand */
        /* of the 2-parameter Integer arithmetic operators */
        /* Add, And, Divide, Mod, Multiply, NAnd, NOr, Or, */
        /* ShiftLeft, ShiftRight, Subtract, Xor */
        /* Add, common 32-bit/64-bit test */
        Method (M03B, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF61)) + 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) + 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x0322)
            Store ((DerefOf (RefOf (BF61)) + AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) + AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x0322)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF61)) + DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((DerefOf (RefOf (BF61)) + DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x0322)
            }

            Store ((DerefOf (RefOf (BF61)) + DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) + DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x0322)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF61)) + M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) + M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x0322)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF61)) + DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((DerefOf (RefOf (BF61)) + DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x0322)
            }

            Local0 = (DerefOf (RefOf (BF61)) + 0x00)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) + 0x01)
            M600 (Arg0, 0x0D, Local0, 0x0322)
            Local0 = (DerefOf (RefOf (BF61)) + AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) + AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x0322)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF61)) + DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (BF61)) + DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x0322)
            }

            Local0 = (DerefOf (RefOf (BF61)) + DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) + DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x0322)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF61)) + M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) + M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x0322)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF61)) + DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (BF61)) + DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x0322)
            }

            /* Conversion of the second operand */

            Store ((0x00 + DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x18, Local0, 0x0321)
            Store ((0x01 + DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x19, Local0, 0x0322)
            Store ((AUI5 + DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x0321)
            Store ((AUI6 + DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0322)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) + DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x0321)
                Store ((DerefOf (RefOf (AUI6)) + DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0322)
            }

            Store ((DerefOf (PAUI [0x05]) + DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x0321)
            Store ((DerefOf (PAUI [0x06]) + DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0322)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) + DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x20, Local0, 0x0321)
            Store ((M601 (0x01, 0x06) + DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x21, Local0, 0x0322)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) + DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x22, Local0, 0x0321)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) + DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x23, Local0, 0x0322)
            }

            Local0 = (0x00 + DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x24, Local0, 0x0321)
            Local0 = (0x01 + DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x25, Local0, 0x0322)
            Local0 = (AUI5 + DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x26, Local0, 0x0321)
            Local0 = (AUI6 + DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x27, Local0, 0x0322)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) + DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x28, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (AUI6)) + DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x29, Local0, 0x0322)
            }

            Local0 = (DerefOf (PAUI [0x05]) + DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2A, Local0, 0x0321)
            Local0 = (DerefOf (PAUI [0x06]) + DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2B, Local0, 0x0322)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) + DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2C, Local0, 0x0321)
            Local0 = (M601 (0x01, 0x06) + DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2D, Local0, 0x0322)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) + DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x2E, Local0, 0x0321)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) + DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x2F, Local0, 0x0322)
            }
        }

        /* Add, 64-bit */

        Method (M03C, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) + 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) + 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xFE7CB391D650A285)
            Store ((DerefOf (RefOf (BF65)) + AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) + AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xFE7CB391D650A285)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) + DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (BF65)) + DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFE7CB391D650A285)
            }

            Store ((DerefOf (RefOf (BF65)) + DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) + DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFE7CB391D650A285)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) + M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) + M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFE7CB391D650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) + DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (BF65)) + DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFE7CB391D650A285)
            }

            Local0 = (DerefOf (RefOf (BF65)) + 0x00)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) + 0x01)
            M600 (Arg0, 0x0D, Local0, 0xFE7CB391D650A285)
            Local0 = (DerefOf (RefOf (BF65)) + AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) + AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xFE7CB391D650A285)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) + DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (BF65)) + DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xFE7CB391D650A285)
            }

            Local0 = (DerefOf (RefOf (BF65)) + DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) + DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xFE7CB391D650A285)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) + M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) + M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xFE7CB391D650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) + DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (BF65)) + DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFE7CB391D650A285)
            }

            /* Conversion of the second operand */

            Store ((0x00 + DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x18, Local0, 0xFE7CB391D650A284)
            Store ((0x01 + DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x19, Local0, 0xFE7CB391D650A285)
            Store ((AUI5 + DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1A, Local0, 0xFE7CB391D650A284)
            Store ((AUI6 + DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFE7CB391D650A285)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) + DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1C, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (AUI6)) + DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFE7CB391D650A285)
            }

            Store ((DerefOf (PAUI [0x05]) + DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1E, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (PAUI [0x06]) + DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFE7CB391D650A285)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) + DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x20, Local0, 0xFE7CB391D650A284)
            Store ((M601 (0x01, 0x06) + DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x21, Local0, 0xFE7CB391D650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) + DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x22, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) + DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x23, Local0, 0xFE7CB391D650A285)
            }

            Local0 = (0x00 + DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x24, Local0, 0xFE7CB391D650A284)
            Local0 = (0x01 + DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x25, Local0, 0xFE7CB391D650A285)
            Local0 = (AUI5 + DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x26, Local0, 0xFE7CB391D650A284)
            Local0 = (AUI6 + DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x27, Local0, 0xFE7CB391D650A285)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) + DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x28, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (AUI6)) + DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x29, Local0, 0xFE7CB391D650A285)
            }

            Local0 = (DerefOf (PAUI [0x05]) + DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2A, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (PAUI [0x06]) + DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2B, Local0, 0xFE7CB391D650A285)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) + DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2C, Local0, 0xFE7CB391D650A284)
            Local0 = (M601 (0x01, 0x06) + DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2D, Local0, 0xFE7CB391D650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) + DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2E, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) + DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2F, Local0, 0xFE7CB391D650A285)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) + DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x30, Local0, 0xFE7CB391D650A5A5)
            Store ((DerefOf (RefOf (BF65)) + DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x31, Local0, 0xFE7CB391D650A5A5)
            Local0 = (DerefOf (RefOf (BF61)) + DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x32, Local0, 0xFE7CB391D650A5A5)
            Local0 = (DerefOf (RefOf (BF65)) + DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x33, Local0, 0xFE7CB391D650A5A5)
        }

        /* Add, 32-bit */

        Method (M03D, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) + 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) + 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xD650A285)
            Store ((DerefOf (RefOf (BF65)) + AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) + AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xD650A285)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) + DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (BF65)) + DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xD650A285)
            }

            Store ((DerefOf (RefOf (BF65)) + DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) + DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xD650A285)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) + M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) + M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xD650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) + DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (BF65)) + DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xD650A285)
            }

            Local0 = (DerefOf (RefOf (BF65)) + 0x00)
            M600 (Arg0, 0x0C, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) + 0x01)
            M600 (Arg0, 0x0D, Local0, 0xD650A285)
            Local0 = (DerefOf (RefOf (BF65)) + AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) + AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xD650A285)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) + DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (BF65)) + DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xD650A285)
            }

            Local0 = (DerefOf (RefOf (BF65)) + DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) + DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xD650A285)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) + M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) + M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xD650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) + DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (BF65)) + DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xD650A285)
            }

            /* Conversion of the second operand */

            Store ((0x00 + DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x18, Local0, 0xD650A284)
            Store ((0x01 + DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x19, Local0, 0xD650A285)
            Store ((AUI5 + DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1A, Local0, 0xD650A284)
            Store ((AUI6 + DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1B, Local0, 0xD650A285)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) + DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1C, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (AUI6)) + DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1D, Local0, 0xD650A285)
            }

            Store ((DerefOf (PAUI [0x05]) + DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1E, Local0, 0xD650A284)
            Store ((DerefOf (PAUI [0x06]) + DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1F, Local0, 0xD650A285)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) + DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x20, Local0, 0xD650A284)
            Store ((M601 (0x01, 0x06) + DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x21, Local0, 0xD650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) + DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x22, Local0, 0xD650A284)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) + DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x23, Local0, 0xD650A285)
            }

            Local0 = (0x00 + DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x24, Local0, 0xD650A284)
            Local0 = (0x01 + DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x25, Local0, 0xD650A285)
            Local0 = (AUI5 + DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x26, Local0, 0xD650A284)
            Local0 = (AUI6 + DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x27, Local0, 0xD650A285)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) + DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x28, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (AUI6)) + DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x29, Local0, 0xD650A285)
            }

            Local0 = (DerefOf (PAUI [0x05]) + DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2A, Local0, 0xD650A284)
            Local0 = (DerefOf (PAUI [0x06]) + DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2B, Local0, 0xD650A285)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) + DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2C, Local0, 0xD650A284)
            Local0 = (M601 (0x01, 0x06) + DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2D, Local0, 0xD650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) + DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2E, Local0, 0xD650A284)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) + DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2F, Local0, 0xD650A285)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) + DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x30, Local0, 0xD650A5A5)
            Store ((DerefOf (RefOf (BF65)) + DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x31, Local0, 0xD650A5A5)
            Local0 = (DerefOf (RefOf (BF61)) + DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x32, Local0, 0xD650A5A5)
            Local0 = (DerefOf (RefOf (BF65)) + DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x33, Local0, 0xD650A5A5)
        }

        /* And, common 32-bit/64-bit test */

        Method (M03E, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF61)) & 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x00)
            Store ((DerefOf (RefOf (BF61)) & 0xFFFFFFFFFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) & AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x00)
            Store ((DerefOf (RefOf (BF61)) & AUIJ), Local0)
            M600 (Arg0, 0x03, Local0, 0x0321)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF61)) & DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x00)
                Store ((DerefOf (RefOf (BF61)) & DerefOf (RefOf (AUIJ))), Local0)
                M600 (Arg0, 0x05, Local0, 0x0321)
            }

            Store ((DerefOf (RefOf (BF61)) & DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x00)
            Store ((DerefOf (RefOf (BF61)) & DerefOf (PAUI [0x13])), Local0)
            M600 (Arg0, 0x07, Local0, 0x0321)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF61)) & M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x00)
            Store ((DerefOf (RefOf (BF61)) & M601 (0x01, 0x13)), Local0)
            M600 (Arg0, 0x09, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF61)) & DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x00)
                Store ((DerefOf (RefOf (BF61)) & DerefOf (M602 (0x01, 0x13, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x0321)
            }

            Local0 = (DerefOf (RefOf (BF61)) & 0x00)
            M600 (Arg0, 0x0C, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF61)) & 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) & AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF61)) & AUIJ) /* \AUIJ */
            M600 (Arg0, 0x0F, Local0, 0x0321)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF61)) & DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x00)
                Local0 = (DerefOf (RefOf (BF61)) & DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x11, Local0, 0x0321)
            }

            Local0 = (DerefOf (RefOf (BF61)) & DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF61)) & DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x13, Local0, 0x0321)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF61)) & M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF61)) & M601 (0x01, 0x13))
            M600 (Arg0, 0x15, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF61)) & DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x00)
                Local0 = (DerefOf (RefOf (BF61)) & DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x0321)
            }

            /* Conversion of the second operand */

            Store ((0x00 & DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xFFFFFFFFFFFFFFFF & DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x19, Local0, 0x0321)
            Store ((AUI5 & DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUIJ & DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0321)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) & DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUIJ)) & DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0321)
            }

            Store ((DerefOf (PAUI [0x05]) & DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x13]) & DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0321)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) & DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x13) & DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x21, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) & DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x13, 0x01)) & DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x23, Local0, 0x0321)
            }

            Local0 = (0x00 & DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0xFFFFFFFFFFFFFFFF & DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x25, Local0, 0x0321)
            Local0 = (AUI5 & DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUIJ & DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x27, Local0, 0x0321)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) & DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUIJ)) & DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x29, Local0, 0x0321)
            }

            Local0 = (DerefOf (PAUI [0x05]) & DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x13]) & DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2B, Local0, 0x0321)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) & DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x13) & DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2D, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) & DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x13, 0x01)) & DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x2F, Local0, 0x0321)
            }
        }

        /* And, 64-bit */

        Method (M03F, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) & 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) & 0xFFFFFFFFFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) & AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) & AUIJ), Local0)
            M600 (Arg0, 0x03, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) & DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x00)
                Store ((DerefOf (RefOf (BF65)) & DerefOf (RefOf (AUIJ))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFE7CB391D650A284)
            }

            Store ((DerefOf (RefOf (BF65)) & DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) & DerefOf (PAUI [0x13])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) & M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) & M601 (0x01, 0x13)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) & DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x00)
                Store ((DerefOf (RefOf (BF65)) & DerefOf (M602 (0x01, 0x13, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (DerefOf (RefOf (BF65)) & 0x00)
            M600 (Arg0, 0x0C, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF65)) & 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) & AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF65)) & AUIJ) /* \AUIJ */
            M600 (Arg0, 0x0F, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) & DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x00)
                Local0 = (DerefOf (RefOf (BF65)) & DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x11, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (DerefOf (RefOf (BF65)) & DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF65)) & DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x13, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) & M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF65)) & M601 (0x01, 0x13))
            M600 (Arg0, 0x15, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) & DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x00)
                Local0 = (DerefOf (RefOf (BF65)) & DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFE7CB391D650A284)
            }

            /* Conversion of the second operand */

            Store ((0x00 & DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xFFFFFFFFFFFFFFFF & DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x19, Local0, 0xFE7CB391D650A284)
            Store ((AUI5 & DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUIJ & DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) & DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUIJ)) & DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFE7CB391D650A284)
            }

            Store ((DerefOf (PAUI [0x05]) & DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x13]) & DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) & DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x13) & DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x21, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) & DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x13, 0x01)) & DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x23, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (0x00 & DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0xFFFFFFFFFFFFFFFF & DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x25, Local0, 0xFE7CB391D650A284)
            Local0 = (AUI5 & DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUIJ & DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x27, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) & DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUIJ)) & DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x29, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (DerefOf (PAUI [0x05]) & DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x13]) & DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2B, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) & DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x13) & DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2D, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) & DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x13, 0x01)) & DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2F, Local0, 0xFE7CB391D650A284)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) & DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x30, Local0, 0x0200)
            Store ((DerefOf (RefOf (BF65)) & DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x31, Local0, 0x0200)
            Local0 = (DerefOf (RefOf (BF61)) & DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x32, Local0, 0x0200)
            Local0 = (DerefOf (RefOf (BF65)) & DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x33, Local0, 0x0200)
        }

        /* And, 32-bit */

        Method (M040, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) & 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) & 0xFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) & AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) & AUII), Local0)
            M600 (Arg0, 0x03, Local0, 0xD650A284)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) & DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x00)
                Store ((DerefOf (RefOf (BF65)) & DerefOf (RefOf (AUII))), Local0)
                M600 (Arg0, 0x05, Local0, 0xD650A284)
            }

            Store ((DerefOf (RefOf (BF65)) & DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) & DerefOf (PAUI [0x12])), Local0)
            M600 (Arg0, 0x07, Local0, 0xD650A284)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) & M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) & M601 (0x01, 0x12)), Local0)
            M600 (Arg0, 0x09, Local0, 0xD650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) & DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x00)
                Store ((DerefOf (RefOf (BF65)) & DerefOf (M602 (0x01, 0x12, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xD650A284)
            }

            Local0 = (DerefOf (RefOf (BF65)) & 0x00)
            M600 (Arg0, 0x0C, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF65)) & 0xFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) & AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF65)) & AUII) /* \AUII */
            M600 (Arg0, 0x0F, Local0, 0xD650A284)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) & DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x00)
                Local0 = (DerefOf (RefOf (BF65)) & DerefOf (RefOf (AUII)))
                M600 (Arg0, 0x11, Local0, 0xD650A284)
            }

            Local0 = (DerefOf (RefOf (BF65)) & DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF65)) & DerefOf (PAUI [0x12]))
            M600 (Arg0, 0x13, Local0, 0xD650A284)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) & M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF65)) & M601 (0x01, 0x12))
            M600 (Arg0, 0x15, Local0, 0xD650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) & DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x00)
                Local0 = (DerefOf (RefOf (BF65)) & DerefOf (M602 (0x01, 0x12, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xD650A284)
            }

            /* Conversion of the second operand */

            Store ((0x00 & DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xFFFFFFFF & DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x19, Local0, 0xD650A284)
            Store ((AUI5 & DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUII & DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1B, Local0, 0xD650A284)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) & DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUII)) & DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1D, Local0, 0xD650A284)
            }

            Store ((DerefOf (PAUI [0x05]) & DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x12]) & DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1F, Local0, 0xD650A284)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) & DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x12) & DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x21, Local0, 0xD650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) & DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x12, 0x01)) & DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x23, Local0, 0xD650A284)
            }

            Local0 = (0x00 & DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0xFFFFFFFF & DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x25, Local0, 0xD650A284)
            Local0 = (AUI5 & DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUII & DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x27, Local0, 0xD650A284)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) & DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUII)) & DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x29, Local0, 0xD650A284)
            }

            Local0 = (DerefOf (PAUI [0x05]) & DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x12]) & DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2B, Local0, 0xD650A284)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) & DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x12) & DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2D, Local0, 0xD650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) & DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x12, 0x01)) & DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2F, Local0, 0xD650A284)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) & DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x30, Local0, 0x0200)
            Store ((DerefOf (RefOf (BF65)) & DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x31, Local0, 0x0200)
            Local0 = (DerefOf (RefOf (BF61)) & DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x32, Local0, 0x0200)
            Local0 = (DerefOf (RefOf (BF65)) & DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x33, Local0, 0x0200)
        }

        /* Divide, common 32-bit/64-bit test */

        Method (M041, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF61)) / 0x01), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) / 0x0321), Local0)
            M600 (Arg0, 0x01, Local0, 0x01)
            Store ((DerefOf (RefOf (BF61)) / AUI6), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) / AUI1), Local0)
            M600 (Arg0, 0x03, Local0, 0x01)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF61)) / DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((DerefOf (RefOf (BF61)) / DerefOf (RefOf (AUI1))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01)
            }

            Store ((DerefOf (RefOf (BF61)) / DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) / DerefOf (PAUI [0x01])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF61)) / M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) / M601 (0x01, 0x01)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF61)) / DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((DerefOf (RefOf (BF61)) / DerefOf (M602 (0x01, 0x01, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01)
            }

            Divide (DerefOf (RefOf (BF61)), 0x01, Local1, Local0)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Divide (DerefOf (RefOf (BF61)), 0x0321, Local1, Local0)
            M600 (Arg0, 0x0D, Local0, 0x01)
            Divide (DerefOf (RefOf (BF61)), AUI6, Local1, Local0)
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Divide (DerefOf (RefOf (BF61)), AUI1, Local1, Local0)
            M600 (Arg0, 0x0F, Local0, 0x01)
            If (Y078)
            {
                Divide (DerefOf (RefOf (BF61)), DerefOf (RefOf (AUI6)), Local1, Local0)
                M600 (Arg0, 0x10, Local0, 0x0321)
                Divide (DerefOf (RefOf (BF61)), DerefOf (RefOf (AUI1)), Local1, Local0)
                M600 (Arg0, 0x11, Local0, 0x01)
            }

            Divide (DerefOf (RefOf (BF61)), DerefOf (PAUI [0x06]), Local1, Local0)
            M600 (Arg0, 0x12, Local0, 0x0321)
            Divide (DerefOf (RefOf (BF61)), DerefOf (PAUI [0x01]), Local1, Local0)
            M600 (Arg0, 0x13, Local0, 0x01)
            /* Method returns Integer */

            Divide (DerefOf (RefOf (BF61)), M601 (0x01, 0x06), Local1, Local0)
            M600 (Arg0, 0x14, Local0, 0x0321)
            Divide (DerefOf (RefOf (BF61)), M601 (0x01, 0x01), Local1, Local0)
            M600 (Arg0, 0x15, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Divide (DerefOf (RefOf (BF61)), DerefOf (M602 (0x01, 0x06, 0x01)), Local1, Local0)
                M600 (Arg0, 0x16, Local0, 0x0321)
                Divide (DerefOf (RefOf (BF61)), DerefOf (M602 (0x01, 0x01, 0x01)), Local1, Local0)
                M600 (Arg0, 0x17, Local0, 0x01)
            }

            /* Conversion of the second operand */

            Store ((0x01 / DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x0321 / DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x19, Local0, 0x01)
            Store ((AUI6 / DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI1 / DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1B, Local0, 0x01)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI6)) / DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI1)) / DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x1D, Local0, 0x01)
            }

            Store ((DerefOf (PAUI [0x06]) / DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x01]) / DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1F, Local0, 0x01)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x06) / DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x01) / DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x21, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) / DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x01, 0x01)) / DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x23, Local0, 0x01)
            }

            Divide (0x01, DerefOf (RefOf (BF61)), Local1, Local0)
            M600 (Arg0, 0x24, Local0, 0x00)
            Divide (0x0321, DerefOf (RefOf (BF61)), Local1, Local0)
            M600 (Arg0, 0x25, Local0, 0x01)
            Divide (AUI6, DerefOf (RefOf (BF61)), Local1, Local0)
            M600 (Arg0, 0x26, Local0, 0x00)
            Divide (AUI1, DerefOf (RefOf (BF61)), Local1, Local0)
            M600 (Arg0, 0x27, Local0, 0x01)
            If (Y078)
            {
                Divide (DerefOf (RefOf (AUI6)), DerefOf (RefOf (BF61)), Local1, Local0)
                M600 (Arg0, 0x28, Local0, 0x00)
                Divide (DerefOf (RefOf (AUI1)), DerefOf (RefOf (BF61)), Local1, Local0)
                M600 (Arg0, 0x29, Local0, 0x01)
            }

            Divide (DerefOf (PAUI [0x06]), DerefOf (RefOf (BF61)), Local1, Local0)
            M600 (Arg0, 0x2A, Local0, 0x00)
            Divide (DerefOf (PAUI [0x01]), DerefOf (RefOf (BF61)), Local1, Local0)
            M600 (Arg0, 0x2B, Local0, 0x01)
            /* Method returns Integer */

            Divide (M601 (0x01, 0x06), DerefOf (RefOf (BF61)), Local1, Local0)
            M600 (Arg0, 0x2C, Local0, 0x00)
            Divide (M601 (0x01, 0x01), DerefOf (RefOf (BF61)), Local1, Local0)
            M600 (Arg0, 0x2D, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Divide (DerefOf (M602 (0x01, 0x06, 0x01)), DerefOf (RefOf (BF61)), Local1, Local0)
                M600 (Arg0, 0x2E, Local0, 0x00)
                Divide (DerefOf (M602 (0x01, 0x01, 0x01)), DerefOf (RefOf (BF61)), Local1, Local0)
                M600 (Arg0, 0x2F, Local0, 0x01)
            }
        }

        /* Divide, 64-bit */

        Method (M042, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) / 0x01), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) / 0xFE7CB391D650A284), Local0)
            M600 (Arg0, 0x01, Local0, 0x01)
            Store ((DerefOf (RefOf (BF65)) / AUI6), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) / AUI4), Local0)
            M600 (Arg0, 0x03, Local0, 0x01)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) / DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (BF65)) / DerefOf (RefOf (AUI4))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01)
            }

            Store ((DerefOf (RefOf (BF65)) / DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) / DerefOf (PAUI [0x04])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) / M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) / M601 (0x01, 0x04)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) / DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (BF65)) / DerefOf (M602 (0x01, 0x04, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01)
            }

            Divide (DerefOf (RefOf (BF65)), 0x01, Local1, Local0)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Divide (DerefOf (RefOf (BF65)), 0xFE7CB391D650A284, Local1, Local0)
            M600 (Arg0, 0x0D, Local0, 0x01)
            Divide (DerefOf (RefOf (BF65)), AUI6, Local1, Local0)
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Divide (DerefOf (RefOf (BF65)), AUI4, Local1, Local0)
            M600 (Arg0, 0x0F, Local0, 0x01)
            If (Y078)
            {
                Divide (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUI6)), Local1, Local0)
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Divide (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUI4)), Local1, Local0)
                M600 (Arg0, 0x11, Local0, 0x01)
            }

            Divide (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x06]), Local1, Local0)
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Divide (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x04]), Local1, Local0)
            M600 (Arg0, 0x13, Local0, 0x01)
            /* Method returns Integer */

            Divide (DerefOf (RefOf (BF65)), M601 (0x01, 0x06), Local1, Local0)
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Divide (DerefOf (RefOf (BF65)), M601 (0x01, 0x04), Local1, Local0)
            M600 (Arg0, 0x15, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Divide (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x06, 0x01)), Local1, Local0)
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Divide (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x04, 0x01)), Local1, Local0)
                M600 (Arg0, 0x17, Local0, 0x01)
            }

            /* Conversion of the second operand */

            Store ((0x01 / DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xFE7CB391D650A284 / DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x19, Local0, 0x01)
            Store ((AUI6 / DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI4 / DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1B, Local0, 0x01)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI6)) / DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI4)) / DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1D, Local0, 0x01)
            }

            Store ((DerefOf (PAUI [0x06]) / DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x04]) / DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1F, Local0, 0x01)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x06) / DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x04) / DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x21, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) / DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x04, 0x01)) / DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x23, Local0, 0x01)
            }

            Divide (0x01, DerefOf (RefOf (BF65)), Local1, Local0)
            M600 (Arg0, 0x24, Local0, 0x00)
            Divide (0xFE7CB391D650A284, DerefOf (RefOf (BF65)), Local1, Local0)
            M600 (Arg0, 0x25, Local0, 0x01)
            Divide (AUI6, DerefOf (RefOf (BF65)), Local1, Local0)
            M600 (Arg0, 0x26, Local0, 0x00)
            Divide (AUI4, DerefOf (RefOf (BF65)), Local1, Local0)
            M600 (Arg0, 0x27, Local0, 0x01)
            If (Y078)
            {
                Divide (DerefOf (RefOf (AUI6)), DerefOf (RefOf (BF65)), Local1, Local0)
                M600 (Arg0, 0x28, Local0, 0x00)
                Divide (DerefOf (RefOf (AUI4)), DerefOf (RefOf (BF65)), Local1, Local0)
                M600 (Arg0, 0x29, Local0, 0x01)
            }

            Divide (DerefOf (PAUI [0x06]), DerefOf (RefOf (BF65)), Local1, Local0)
            M600 (Arg0, 0x2A, Local0, 0x00)
            Divide (DerefOf (PAUI [0x04]), DerefOf (RefOf (BF65)), Local1, Local0)
            M600 (Arg0, 0x2B, Local0, 0x01)
            /* Method returns Integer */

            Divide (M601 (0x01, 0x06), DerefOf (RefOf (BF65)), Local1, Local0)
            M600 (Arg0, 0x2C, Local0, 0x00)
            Divide (M601 (0x01, 0x04), DerefOf (RefOf (BF65)), Local1, Local0)
            M600 (Arg0, 0x2D, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Divide (DerefOf (M602 (0x01, 0x06, 0x01)), DerefOf (RefOf (BF65)), Local1, Local0)
                M600 (Arg0, 0x2E, Local0, 0x00)
                Divide (DerefOf (M602 (0x01, 0x04, 0x01)), DerefOf (RefOf (BF65)), Local1, Local0)
                M600 (Arg0, 0x2F, Local0, 0x01)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) / DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x30, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) / DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x31, Local0, 0x0051558EB950F5A7)
            Divide (DerefOf (RefOf (BF61)), DerefOf (RefOf (BF65)), Local1, Local0)
            M600 (Arg0, 0x32, Local0, 0x00)
            Divide (DerefOf (RefOf (BF65)), DerefOf (RefOf (BF61)), Local1, Local0)
            M600 (Arg0, 0x33, Local0, 0x0051558EB950F5A7)
        }

        /* Divide, 32-bit */

        Method (M043, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) / 0x01), Local0)
            M600 (Arg0, 0x00, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) / 0xD650A284), Local0)
            M600 (Arg0, 0x01, Local0, 0x01)
            Store ((DerefOf (RefOf (BF65)) / AUI6), Local0)
            M600 (Arg0, 0x02, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) / AUIK), Local0)
            M600 (Arg0, 0x03, Local0, 0x01)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) / DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x04, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (BF65)) / DerefOf (RefOf (AUIK))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01)
            }

            Store ((DerefOf (RefOf (BF65)) / DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x06, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) / DerefOf (PAUI [0x14])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) / M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x08, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) / M601 (0x01, 0x14)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) / DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (BF65)) / DerefOf (M602 (0x01, 0x14, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01)
            }

            Divide (DerefOf (RefOf (BF65)), 0x01, Local1, Local0)
            M600 (Arg0, 0x0C, Local0, 0xD650A284)
            Divide (DerefOf (RefOf (BF65)), 0xD650A284, Local1, Local0)
            M600 (Arg0, 0x0D, Local0, 0x01)
            Divide (DerefOf (RefOf (BF65)), AUI6, Local1, Local0)
            M600 (Arg0, 0x0E, Local0, 0xD650A284)
            Divide (DerefOf (RefOf (BF65)), AUIK, Local1, Local0)
            M600 (Arg0, 0x0F, Local0, 0x01)
            If (Y078)
            {
                Divide (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUI6)), Local1, Local0)
                M600 (Arg0, 0x10, Local0, 0xD650A284)
                Divide (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUIK)), Local1, Local0)
                M600 (Arg0, 0x11, Local0, 0x01)
            }

            Divide (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x06]), Local1, Local0)
            M600 (Arg0, 0x12, Local0, 0xD650A284)
            Divide (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x14]), Local1, Local0)
            M600 (Arg0, 0x13, Local0, 0x01)
            /* Method returns Integer */

            Divide (DerefOf (RefOf (BF65)), M601 (0x01, 0x06), Local1, Local0)
            M600 (Arg0, 0x14, Local0, 0xD650A284)
            Divide (DerefOf (RefOf (BF65)), M601 (0x01, 0x14), Local1, Local0)
            M600 (Arg0, 0x15, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Divide (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x06, 0x01)), Local1, Local0)
                M600 (Arg0, 0x16, Local0, 0xD650A284)
                Divide (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x14, 0x01)), Local1, Local0)
                M600 (Arg0, 0x17, Local0, 0x01)
            }

            /* Conversion of the second operand */

            Store ((0x01 / DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xD650A284 / DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x19, Local0, 0x01)
            Store ((AUI6 / DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUIK / DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1B, Local0, 0x01)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI6)) / DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUIK)) / DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1D, Local0, 0x01)
            }

            Store ((DerefOf (PAUI [0x06]) / DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x14]) / DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1F, Local0, 0x01)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x06) / DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x14) / DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x21, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) / DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x14, 0x01)) / DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x23, Local0, 0x01)
            }

            Divide (0x01, DerefOf (RefOf (BF65)), Local1, Local0)
            M600 (Arg0, 0x24, Local0, 0x00)
            Divide (0xD650A284, DerefOf (RefOf (BF65)), Local1, Local0)
            M600 (Arg0, 0x25, Local0, 0x01)
            Divide (AUI6, DerefOf (RefOf (BF65)), Local1, Local0)
            M600 (Arg0, 0x26, Local0, 0x00)
            Divide (AUIK, DerefOf (RefOf (BF65)), Local1, Local0)
            M600 (Arg0, 0x27, Local0, 0x01)
            If (Y078)
            {
                Divide (DerefOf (RefOf (AUI6)), DerefOf (RefOf (BF65)), Local1, Local0)
                M600 (Arg0, 0x28, Local0, 0x00)
                Divide (DerefOf (RefOf (AUIK)), DerefOf (RefOf (BF65)), Local1, Local0)
                M600 (Arg0, 0x29, Local0, 0x01)
            }

            Divide (DerefOf (PAUI [0x06]), DerefOf (RefOf (BF65)), Local1, Local0)
            M600 (Arg0, 0x2A, Local0, 0x00)
            Divide (DerefOf (PAUI [0x14]), DerefOf (RefOf (BF65)), Local1, Local0)
            M600 (Arg0, 0x2B, Local0, 0x01)
            /* Method returns Integer */

            Divide (M601 (0x01, 0x06), DerefOf (RefOf (BF65)), Local1, Local0)
            M600 (Arg0, 0x2C, Local0, 0x00)
            Divide (M601 (0x01, 0x14), DerefOf (RefOf (BF65)), Local1, Local0)
            M600 (Arg0, 0x2D, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Divide (DerefOf (M602 (0x01, 0x06, 0x01)), DerefOf (RefOf (BF65)), Local1, Local0)
                M600 (Arg0, 0x2E, Local0, 0x00)
                Divide (DerefOf (M602 (0x01, 0x14, 0x01)), DerefOf (RefOf (BF65)), Local1, Local0)
                M600 (Arg0, 0x2F, Local0, 0x01)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) / DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x30, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) / DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x31, Local0, 0x00447EC3)
            Divide (DerefOf (RefOf (BF61)), DerefOf (RefOf (BF65)), Local1, Local0)
            M600 (Arg0, 0x32, Local0, 0x00)
            Divide (DerefOf (RefOf (BF65)), DerefOf (RefOf (BF61)), Local1, Local0)
            M600 (Arg0, 0x33, Local0, 0x00447EC3)
        }

        /* Mod, common 32-bit/64-bit test */

        Method (M044, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF61)) % 0x0322), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) % 0x0320), Local0)
            M600 (Arg0, 0x01, Local0, 0x01)
            Store ((DerefOf (RefOf (BF61)) % AUIG), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) % AUIH), Local0)
            M600 (Arg0, 0x03, Local0, 0x01)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF61)) % DerefOf (RefOf (AUIG))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((DerefOf (RefOf (BF61)) % DerefOf (RefOf (AUIH))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01)
            }

            Store ((DerefOf (RefOf (BF61)) % DerefOf (PAUI [0x10])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) % DerefOf (PAUI [0x11])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF61)) % M601 (0x01, 0x10)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) % M601 (0x01, 0x11)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF61)) % DerefOf (M602 (0x01, 0x10, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((DerefOf (RefOf (BF61)) % DerefOf (M602 (0x01, 0x11, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01)
            }

            Local0 = (DerefOf (RefOf (BF61)) % 0x0322)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) % 0x0320)
            M600 (Arg0, 0x0D, Local0, 0x01)
            Local0 = (DerefOf (RefOf (BF61)) % AUIG) /* \AUIG */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) % AUIH) /* \AUIH */
            M600 (Arg0, 0x0F, Local0, 0x01)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF61)) % DerefOf (RefOf (AUIG)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (BF61)) % DerefOf (RefOf (AUIH)))
                M600 (Arg0, 0x11, Local0, 0x01)
            }

            Local0 = (DerefOf (RefOf (BF61)) % DerefOf (PAUI [0x10]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) % DerefOf (PAUI [0x11]))
            M600 (Arg0, 0x13, Local0, 0x01)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF61)) % M601 (0x01, 0x10))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) % M601 (0x01, 0x11))
            M600 (Arg0, 0x15, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF61)) % DerefOf (M602 (0x01, 0x10, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (BF61)) % DerefOf (M602 (0x01, 0x11, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x01)
            }

            /* Conversion of the second operand */

            Store ((0x0322 % DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x18, Local0, 0x01)
            Store ((0x0320 % DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x19, Local0, 0x0320)
            Store ((AUIG % DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x01)
            Store ((AUIH % DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0320)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUIG)) % DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x01)
                Store ((DerefOf (RefOf (AUIH)) % DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0320)
            }

            Store ((DerefOf (PAUI [0x10]) % DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x01)
            Store ((DerefOf (PAUI [0x11]) % DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0320)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x10) % DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x20, Local0, 0x01)
            Store ((M601 (0x01, 0x11) % DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x21, Local0, 0x0320)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x10, 0x01)) % DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x22, Local0, 0x01)
                Store ((DerefOf (M602 (0x01, 0x11, 0x01)) % DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x23, Local0, 0x0320)
            }

            Local0 = (0x0322 % DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x24, Local0, 0x01)
            Local0 = (0x0320 % DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x25, Local0, 0x0320)
            Local0 = (AUIG % DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x26, Local0, 0x01)
            Local0 = (AUIH % DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x27, Local0, 0x0320)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUIG)) % DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x28, Local0, 0x01)
                Local0 = (DerefOf (RefOf (AUIH)) % DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x29, Local0, 0x0320)
            }

            Local0 = (DerefOf (PAUI [0x10]) % DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2A, Local0, 0x01)
            Local0 = (DerefOf (PAUI [0x11]) % DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2B, Local0, 0x0320)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x10) % DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2C, Local0, 0x01)
            Local0 = (M601 (0x01, 0x11) % DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2D, Local0, 0x0320)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) % DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x2E, Local0, 0x01)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) % DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x2F, Local0, 0x0320)
            }
        }

        /* Mod, 64-bit */

        Method (M045, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) % 0xFE7CB391D650A285), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) % 0xFE7CB391D650A283), Local0)
            M600 (Arg0, 0x01, Local0, 0x01)
            Store ((DerefOf (RefOf (BF65)) % AUID), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) % AUIF), Local0)
            M600 (Arg0, 0x03, Local0, 0x01)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) % DerefOf (RefOf (AUID))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (BF65)) % DerefOf (RefOf (AUIF))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01)
            }

            Store ((DerefOf (RefOf (BF65)) % DerefOf (PAUI [0x0D])), Local0)
            M600 (Arg0, 0x0D, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) % DerefOf (PAUI [0x0F])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) % M601 (0x01, 0x0D)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) % M601 (0x01, 0x0F)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) % DerefOf (M602 (0x01, 0x0D, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (BF65)) % DerefOf (M602 (0x01, 0x0F, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01)
            }

            Local0 = (DerefOf (RefOf (BF65)) % 0xFE7CB391D650A285)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) % 0xFE7CB391D650A283)
            M600 (Arg0, 0x0D, Local0, 0x01)
            Local0 = (DerefOf (RefOf (BF65)) % AUID) /* \AUID */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) % AUIF) /* \AUIF */
            M600 (Arg0, 0x0F, Local0, 0x01)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) % DerefOf (RefOf (AUID)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (BF65)) % DerefOf (RefOf (AUIF)))
                M600 (Arg0, 0x11, Local0, 0x01)
            }

            Local0 = (DerefOf (RefOf (BF65)) % DerefOf (PAUI [0x0D]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) % DerefOf (PAUI [0x0F]))
            M600 (Arg0, 0x13, Local0, 0x01)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) % M601 (0x01, 0x0D))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) % M601 (0x01, 0x0F))
            M600 (Arg0, 0x15, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) % DerefOf (M602 (0x01, 0x0D, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (BF65)) % DerefOf (M602 (0x01, 0x0F, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x01)
            }

            /* Conversion of the second operand */

            Store ((0xFE7CB391D650A285 % DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x18, Local0, 0x01)
            Store ((0xFE7CB391D650A283 % DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x19, Local0, 0xFE7CB391D650A283)
            Store ((AUID % DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x01)
            Store ((AUIF % DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFE7CB391D650A283)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUID)) % DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x01)
                Store ((DerefOf (RefOf (AUIF)) % DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFE7CB391D650A283)
            }

            Store ((DerefOf (PAUI [0x0D]) % DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x01)
            Store ((DerefOf (PAUI [0x0F]) % DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFE7CB391D650A283)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x0D) % DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x20, Local0, 0x01)
            Store ((M601 (0x01, 0x0F) % DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x21, Local0, 0xFE7CB391D650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x0D, 0x01)) % DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x22, Local0, 0x01)
                Store ((DerefOf (M602 (0x01, 0x0F, 0x01)) % DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x23, Local0, 0xFE7CB391D650A283)
            }

            Local0 = (0xFE7CB391D650A285 % DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x24, Local0, 0x01)
            Local0 = (0xFE7CB391D650A283 % DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x25, Local0, 0xFE7CB391D650A283)
            Local0 = (AUID % DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x26, Local0, 0x01)
            Local0 = (AUIF % DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x27, Local0, 0xFE7CB391D650A283)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUID)) % DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x28, Local0, 0x01)
                Local0 = (DerefOf (RefOf (AUIF)) % DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x29, Local0, 0xFE7CB391D650A283)
            }

            Local0 = (DerefOf (PAUI [0x0D]) % DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2A, Local0, 0x01)
            Local0 = (DerefOf (PAUI [0x0F]) % DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2B, Local0, 0xFE7CB391D650A283)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x0D) % DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2C, Local0, 0x01)
            Local0 = (M601 (0x01, 0x0F) % DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2D, Local0, 0xFE7CB391D650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) % DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2E, Local0, 0x01)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) % DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2F, Local0, 0xFE7CB391D650A283)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) % DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x30, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF65)) % DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x31, Local0, 0x02FD)
            Local0 = (DerefOf (RefOf (BF61)) % DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x32, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF65)) % DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x33, Local0, 0x02FD)
        }

        /* Mod, 32-bit */

        Method (M046, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) % 0xD650A285), Local0)
            M600 (Arg0, 0x00, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) % 0xD650A283), Local0)
            M600 (Arg0, 0x01, Local0, 0x01)
            Store ((DerefOf (RefOf (BF65)) % AUIL), Local0)
            M600 (Arg0, 0x02, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) % AUIM), Local0)
            M600 (Arg0, 0x0E, Local0, 0x01)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) % DerefOf (RefOf (AUIL))), Local0)
                M600 (Arg0, 0x04, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (BF65)) % DerefOf (RefOf (AUIM))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01)
            }

            Store ((DerefOf (RefOf (BF65)) % DerefOf (PAUI [0x15])), Local0)
            M600 (Arg0, 0x0C, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) % DerefOf (PAUI [0x16])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) % M601 (0x01, 0x15)), Local0)
            M600 (Arg0, 0x08, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) % M601 (0x01, 0x16)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) % DerefOf (M602 (0x01, 0x15, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (BF65)) % DerefOf (M602 (0x01, 0x16, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01)
            }

            Local0 = (DerefOf (RefOf (BF65)) % 0xD650A285)
            M600 (Arg0, 0x0C, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) % 0xD650A283)
            M600 (Arg0, 0x0D, Local0, 0x01)
            Local0 = (DerefOf (RefOf (BF65)) % AUIL) /* \AUIL */
            M600 (Arg0, 0x0E, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) % AUIM) /* \AUIM */
            M600 (Arg0, 0x0F, Local0, 0x01)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) % DerefOf (RefOf (AUIL)))
                M600 (Arg0, 0x10, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (BF65)) % DerefOf (RefOf (AUIM)))
                M600 (Arg0, 0x11, Local0, 0x01)
            }

            Local0 = (DerefOf (RefOf (BF65)) % DerefOf (PAUI [0x15]))
            M600 (Arg0, 0x12, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) % DerefOf (PAUI [0x16]))
            M600 (Arg0, 0x13, Local0, 0x01)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) % M601 (0x01, 0x15))
            M600 (Arg0, 0x14, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) % M601 (0x01, 0x16))
            M600 (Arg0, 0x15, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) % DerefOf (M602 (0x01, 0x15, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (BF65)) % DerefOf (M602 (0x01, 0x16, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x01)
            }

            /* Conversion of the second operand */

            Store ((0xD650A285 % DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x18, Local0, 0x01)
            Store ((0xD650A283 % DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x19, Local0, 0xD650A283)
            Store ((AUIL % DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x01)
            Store ((AUIM % DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1B, Local0, 0xD650A283)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUIL)) % DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x01)
                Store ((DerefOf (RefOf (AUIM)) % DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1D, Local0, 0xD650A283)
            }

            Store ((DerefOf (PAUI [0x15]) % DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x01)
            Store ((DerefOf (PAUI [0x16]) % DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1F, Local0, 0xD650A283)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x15) % DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x20, Local0, 0x01)
            Store ((M601 (0x01, 0x16) % DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x21, Local0, 0xD650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x15, 0x01)) % DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x22, Local0, 0x01)
                Store ((DerefOf (M602 (0x01, 0x16, 0x01)) % DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x23, Local0, 0xD650A283)
            }

            Local0 = (0xD650A285 % DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x24, Local0, 0x01)
            Local0 = (0xD650A283 % DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x25, Local0, 0xD650A283)
            Local0 = (AUIL % DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x26, Local0, 0x01)
            Local0 = (AUIM % DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x27, Local0, 0xD650A283)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUIL)) % DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x28, Local0, 0x01)
                Local0 = (DerefOf (RefOf (AUIM)) % DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x29, Local0, 0xD650A283)
            }

            Local0 = (DerefOf (PAUI [0x15]) % DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2A, Local0, 0x01)
            Local0 = (DerefOf (PAUI [0x16]) % DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2B, Local0, 0xD650A283)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x15) % DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2C, Local0, 0x01)
            Local0 = (M601 (0x01, 0x16) % DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2D, Local0, 0xD650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x15, 0x01)) % DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2E, Local0, 0x01)
                Local0 = (DerefOf (M602 (0x01, 0x16, 0x01)) % DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2F, Local0, 0xD650A283)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) % DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x30, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF65)) % DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x31, Local0, 0x0261)
            Local0 = (DerefOf (RefOf (BF61)) % DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x32, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF65)) % DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x33, Local0, 0x0261)
        }

        /* Multiply, common 32-bit/64-bit test */

        Method (M047, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF61)) * 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x00)
            Store ((DerefOf (RefOf (BF61)) * 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) * AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x00)
            Store ((DerefOf (RefOf (BF61)) * AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x0321)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF61)) * DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x00)
                Store ((DerefOf (RefOf (BF61)) * DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x0321)
            }

            Store ((DerefOf (RefOf (BF61)) * DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x00)
            Store ((DerefOf (RefOf (BF61)) * DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x0321)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF61)) * M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x00)
            Store ((DerefOf (RefOf (BF61)) * M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF61)) * DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x00)
                Store ((DerefOf (RefOf (BF61)) * DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x0321)
            }

            Local0 = (DerefOf (RefOf (BF61)) * 0x00)
            M600 (Arg0, 0x0C, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF61)) * 0x01)
            M600 (Arg0, 0x0D, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) * AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF61)) * AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x0321)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF61)) * DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x00)
                Local0 = (DerefOf (RefOf (BF61)) * DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x0321)
            }

            Local0 = (DerefOf (RefOf (BF61)) * DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF61)) * DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x0321)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF61)) * M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF61)) * M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF61)) * DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x00)
                Local0 = (DerefOf (RefOf (BF61)) * DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x0321)
            }

            /* Conversion of the second operand */

            Store ((0x00 * DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x01 * DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x19, Local0, 0x0321)
            Store ((AUI5 * DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI6 * DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0321)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) * DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI6)) * DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0321)
            }

            Store ((DerefOf (PAUI [0x05]) * DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x06]) * DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0321)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) * DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x06) * DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x21, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) * DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) * DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x23, Local0, 0x0321)
            }

            Local0 = (0x00 * DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0x01 * DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x25, Local0, 0x0321)
            Local0 = (AUI5 * DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI6 * DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x27, Local0, 0x0321)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) * DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI6)) * DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x29, Local0, 0x0321)
            }

            Local0 = (DerefOf (PAUI [0x05]) * DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x06]) * DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2B, Local0, 0x0321)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) * DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x06) * DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2D, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) * DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) * DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x2F, Local0, 0x0321)
            }
        }

        /* Multiply, 64-bit */

        Method (M048, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) * 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) * 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) * AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) * AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) * DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x00)
                Store ((DerefOf (RefOf (BF65)) * DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFE7CB391D650A284)
            }

            Store ((DerefOf (RefOf (BF65)) * DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) * DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) * M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) * M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) * DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x00)
                Store ((DerefOf (RefOf (BF65)) * DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (DerefOf (RefOf (BF65)) * 0x00)
            M600 (Arg0, 0x0C, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF65)) * 0x01)
            M600 (Arg0, 0x0D, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) * AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF65)) * AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) * DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x00)
                Local0 = (DerefOf (RefOf (BF65)) * DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (DerefOf (RefOf (BF65)) * DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF65)) * DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) * M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF65)) * M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) * DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x00)
                Local0 = (DerefOf (RefOf (BF65)) * DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFE7CB391D650A284)
            }

            /* Conversion of the second operand */

            Store ((0x00 * DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x01 * DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x19, Local0, 0xFE7CB391D650A284)
            Store ((AUI5 * DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI6 * DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) * DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI6)) * DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFE7CB391D650A284)
            }

            Store ((DerefOf (PAUI [0x05]) * DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x06]) * DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) * DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x06) * DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x21, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) * DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) * DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x23, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (0x00 * DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0x01 * DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x25, Local0, 0xFE7CB391D650A284)
            Local0 = (AUI5 * DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI6 * DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x27, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) * DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI6)) * DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x29, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (DerefOf (PAUI [0x05]) * DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x06]) * DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2B, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) * DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x06) * DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2D, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) * DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) * DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2F, Local0, 0xFE7CB391D650A284)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) * DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x30, Local0, 0x442DDB4F924C7F04)
            Store ((DerefOf (RefOf (BF65)) * DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x31, Local0, 0x442DDB4F924C7F04)
            Local0 = (DerefOf (RefOf (BF61)) * DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x32, Local0, 0x442DDB4F924C7F04)
            Local0 = (DerefOf (RefOf (BF65)) * DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x33, Local0, 0x442DDB4F924C7F04)
        }

        /* Multiply, 32-bit */

        Method (M049, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) * 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) * 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) * AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) * AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xD650A284)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) * DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x00)
                Store ((DerefOf (RefOf (BF65)) * DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xD650A284)
            }

            Store ((DerefOf (RefOf (BF65)) * DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) * DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xD650A284)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) * M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) * M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xD650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) * DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x00)
                Store ((DerefOf (RefOf (BF65)) * DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xD650A284)
            }

            Local0 = (DerefOf (RefOf (BF65)) * 0x00)
            M600 (Arg0, 0x0C, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF65)) * 0x01)
            M600 (Arg0, 0x0D, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) * AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF65)) * AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xD650A284)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) * DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x00)
                Local0 = (DerefOf (RefOf (BF65)) * DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xD650A284)
            }

            Local0 = (DerefOf (RefOf (BF65)) * DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF65)) * DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xD650A284)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) * M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF65)) * M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xD650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) * DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x00)
                Local0 = (DerefOf (RefOf (BF65)) * DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xD650A284)
            }

            /* Conversion of the second operand */

            Store ((0x00 * DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x01 * DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x19, Local0, 0xD650A284)
            Store ((AUI5 * DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI6 * DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1B, Local0, 0xD650A284)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) * DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI6)) * DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1D, Local0, 0xD650A284)
            }

            Store ((DerefOf (PAUI [0x05]) * DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x06]) * DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1F, Local0, 0xD650A284)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) * DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x06) * DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x21, Local0, 0xD650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) * DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) * DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x23, Local0, 0xD650A284)
            }

            Local0 = (0x00 * DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0x01 * DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x25, Local0, 0xD650A284)
            Local0 = (AUI5 * DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI6 * DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x27, Local0, 0xD650A284)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) * DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI6)) * DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x29, Local0, 0xD650A284)
            }

            Local0 = (DerefOf (PAUI [0x05]) * DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x06]) * DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2B, Local0, 0xD650A284)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) * DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x06) * DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2D, Local0, 0xD650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) * DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) * DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2F, Local0, 0xD650A284)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) * DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x30, Local0, 0x924C7F04)
            Store ((DerefOf (RefOf (BF65)) * DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x31, Local0, 0x924C7F04)
            Local0 = (DerefOf (RefOf (BF61)) * DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x32, Local0, 0x924C7F04)
            Local0 = (DerefOf (RefOf (BF65)) * DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x33, Local0, 0x924C7F04)
        }

        /* NAnd, common 32-bit/64-bit test */

        Method (M04A, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Local0 = NAnd (DerefOf (RefOf (BF61)), 0x00)
            M600 (Arg0, 0x00, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (DerefOf (RefOf (BF61)), 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x01, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NAnd (DerefOf (RefOf (BF61)), AUI5)
            M600 (Arg0, 0x02, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (DerefOf (RefOf (BF61)), AUIJ)
            M600 (Arg0, 0x03, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                Local0 = NAnd (DerefOf (RefOf (BF61)), DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (DerefOf (RefOf (BF61)), DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x05, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Local0 = NAnd (DerefOf (RefOf (BF61)), DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (DerefOf (RefOf (BF61)), DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x07, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            Local0 = NAnd (DerefOf (RefOf (BF61)), M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (DerefOf (RefOf (BF61)), M601 (0x01, 0x13))
            M600 (Arg0, 0x09, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NAnd (DerefOf (RefOf (BF61)), DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (DerefOf (RefOf (BF61)), DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x0B, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            NAnd (DerefOf (RefOf (BF61)), 0x00, Local0)
            M600 (Arg0, 0x0C, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (DerefOf (RefOf (BF61)), 0xFFFFFFFFFFFFFFFF, Local0)
            M600 (Arg0, 0x0D, Local0, 0xFFFFFFFFFFFFFCDE)
            NAnd (DerefOf (RefOf (BF61)), AUI5, Local0)
            M600 (Arg0, 0x0E, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (DerefOf (RefOf (BF61)), AUIJ, Local0)
            M600 (Arg0, 0x0F, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                NAnd (DerefOf (RefOf (BF61)), DerefOf (RefOf (AUI5)), Local0)
                M600 (Arg0, 0x10, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (DerefOf (RefOf (BF61)), DerefOf (RefOf (AUIJ)), Local0)
                M600 (Arg0, 0x11, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            NAnd (DerefOf (RefOf (BF61)), DerefOf (PAUI [0x05]), Local0)
            M600 (Arg0, 0x12, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (DerefOf (RefOf (BF61)), DerefOf (PAUI [0x13]), Local0)
            M600 (Arg0, 0x13, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            NAnd (DerefOf (RefOf (BF61)), M601 (0x01, 0x05), Local0)
            M600 (Arg0, 0x14, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (DerefOf (RefOf (BF61)), M601 (0x01, 0x13), Local0)
            M600 (Arg0, 0x15, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NAnd (DerefOf (RefOf (BF61)), DerefOf (M602 (0x01, 0x05, 0x01)), Local0)
                M600 (Arg0, 0x16, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (DerefOf (RefOf (BF61)), DerefOf (M602 (0x01, 0x13, 0x01)), Local0)
                M600 (Arg0, 0x17, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            /* Conversion of the second operand */

            Local0 = NAnd (0x00, DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x18, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (0xFFFFFFFFFFFFFFFF, DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x19, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NAnd (AUI5, DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x1A, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (AUIJ, DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x1B, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                Local0 = NAnd (DerefOf (RefOf (AUI5)), DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x1C, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (DerefOf (RefOf (AUIJ)), DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x1D, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Local0 = NAnd (DerefOf (PAUI [0x05]), DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x1E, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (DerefOf (PAUI [0x13]), DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x1F, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            Local0 = NAnd (M601 (0x01, 0x05), DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x20, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (M601 (0x01, 0x13), DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x21, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NAnd (DerefOf (M602 (0x01, 0x05, 0x01)), DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x22, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (DerefOf (M602 (0x01, 0x13, 0x01)), DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x23, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            NAnd (0x00, DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x24, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (0xFFFFFFFFFFFFFFFF, DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x25, Local0, 0xFFFFFFFFFFFFFCDE)
            NAnd (AUI5, DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x26, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (AUIJ, DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x27, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                NAnd (DerefOf (RefOf (AUI5)), DerefOf (RefOf (BF61)), Local0)
                M600 (Arg0, 0x28, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (DerefOf (RefOf (AUIJ)), DerefOf (RefOf (BF61)), Local0)
                M600 (Arg0, 0x29, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            NAnd (DerefOf (PAUI [0x05]), DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x2A, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (DerefOf (PAUI [0x13]), DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x2B, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            NAnd (M601 (0x01, 0x05), DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x2C, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (M601 (0x01, 0x13), DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x2D, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NAnd (DerefOf (M602 (0x01, 0x05, 0x01)), DerefOf (RefOf (BF61)), Local0)
                M600 (Arg0, 0x2E, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (DerefOf (M602 (0x01, 0x13, 0x01)), DerefOf (RefOf (BF61)), Local0)
                M600 (Arg0, 0x2F, Local0, 0xFFFFFFFFFFFFFCDE)
            }
        }

        /* NAnd, 64-bit */

        Method (M04B, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Local0 = NAnd (DerefOf (RefOf (BF65)), 0x00)
            M600 (Arg0, 0x00, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (DerefOf (RefOf (BF65)), 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x01, Local0, 0x01834C6E29AF5D7B)
            Local0 = NAnd (DerefOf (RefOf (BF65)), AUI5)
            M600 (Arg0, 0x02, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (DerefOf (RefOf (BF65)), AUIJ)
            M600 (Arg0, 0x03, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                Local0 = NAnd (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x05, Local0, 0x01834C6E29AF5D7B)
            }

            Local0 = NAnd (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x07, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            Local0 = NAnd (DerefOf (RefOf (BF65)), M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (DerefOf (RefOf (BF65)), M601 (0x01, 0x13))
            M600 (Arg0, 0x09, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NAnd (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x0B, Local0, 0x01834C6E29AF5D7B)
            }

            NAnd (DerefOf (RefOf (BF65)), 0x00, Local0)
            M600 (Arg0, 0x0C, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (DerefOf (RefOf (BF65)), 0xFFFFFFFFFFFFFFFF, Local0)
            M600 (Arg0, 0x0D, Local0, 0x01834C6E29AF5D7B)
            NAnd (DerefOf (RefOf (BF65)), AUI5, Local0)
            M600 (Arg0, 0x0E, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (DerefOf (RefOf (BF65)), AUIJ, Local0)
            M600 (Arg0, 0x0F, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                NAnd (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUI5)), Local0)
                M600 (Arg0, 0x10, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUIJ)), Local0)
                M600 (Arg0, 0x11, Local0, 0x01834C6E29AF5D7B)
            }

            NAnd (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x05]), Local0)
            M600 (Arg0, 0x12, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x13]), Local0)
            M600 (Arg0, 0x13, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            NAnd (DerefOf (RefOf (BF65)), M601 (0x01, 0x05), Local0)
            M600 (Arg0, 0x14, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (DerefOf (RefOf (BF65)), M601 (0x01, 0x13), Local0)
            M600 (Arg0, 0x15, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NAnd (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x05, 0x01)), Local0)
                M600 (Arg0, 0x16, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x13, 0x01)), Local0)
                M600 (Arg0, 0x17, Local0, 0x01834C6E29AF5D7B)
            }

            /* Conversion of the second operand */

            Local0 = NAnd (0x00, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x18, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (0xFFFFFFFFFFFFFFFF, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x19, Local0, 0x01834C6E29AF5D7B)
            Local0 = NAnd (AUI5, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1A, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (AUIJ, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1B, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                Local0 = NAnd (DerefOf (RefOf (AUI5)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x1C, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (DerefOf (RefOf (AUIJ)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x1D, Local0, 0x01834C6E29AF5D7B)
            }

            Local0 = NAnd (DerefOf (PAUI [0x05]), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1E, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (DerefOf (PAUI [0x13]), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1F, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            Local0 = NAnd (M601 (0x01, 0x05), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x20, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (M601 (0x01, 0x13), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x21, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NAnd (DerefOf (M602 (0x01, 0x05, 0x01)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x22, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (DerefOf (M602 (0x01, 0x13, 0x01)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x23, Local0, 0x01834C6E29AF5D7B)
            }

            NAnd (0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x24, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (0xFFFFFFFFFFFFFFFF, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x25, Local0, 0x01834C6E29AF5D7B)
            NAnd (AUI5, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x26, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (AUIJ, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x27, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                NAnd (DerefOf (RefOf (AUI5)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x28, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (DerefOf (RefOf (AUIJ)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x29, Local0, 0x01834C6E29AF5D7B)
            }

            NAnd (DerefOf (PAUI [0x05]), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2A, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (DerefOf (PAUI [0x13]), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2B, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            NAnd (M601 (0x01, 0x05), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2C, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (M601 (0x01, 0x13), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2D, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NAnd (DerefOf (M602 (0x01, 0x05, 0x01)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x2E, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (DerefOf (M602 (0x01, 0x13, 0x01)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x2F, Local0, 0x01834C6E29AF5D7B)
            }

            /* Conversion of the both operands */

            Local0 = NAnd (DerefOf (RefOf (BF61)), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x30, Local0, 0xFFFFFFFFFFFFFDFF)
            Local0 = NAnd (DerefOf (RefOf (BF65)), DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x31, Local0, 0xFFFFFFFFFFFFFDFF)
            NAnd (DerefOf (RefOf (BF61)), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x32, Local0, 0xFFFFFFFFFFFFFDFF)
            NAnd (DerefOf (RefOf (BF65)), DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x33, Local0, 0xFFFFFFFFFFFFFDFF)
        }

        /* NAnd, 32-bit */

        Method (M04C, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Local0 = NAnd (DerefOf (RefOf (BF65)), 0x00)
            M600 (Arg0, 0x00, Local0, 0xFFFFFFFF)
            Local0 = NAnd (DerefOf (RefOf (BF65)), 0xFFFFFFFF)
            M600 (Arg0, 0x01, Local0, 0x29AF5D7B)
            Local0 = NAnd (DerefOf (RefOf (BF65)), AUI5)
            M600 (Arg0, 0x02, Local0, 0xFFFFFFFF)
            Local0 = NAnd (DerefOf (RefOf (BF65)), AUII)
            M600 (Arg0, 0x03, Local0, 0x29AF5D7B)
            If (Y078)
            {
                Local0 = NAnd (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, 0xFFFFFFFF)
                Local0 = NAnd (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUII)))
                M600 (Arg0, 0x05, Local0, 0x29AF5D7B)
            }

            Local0 = NAnd (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, 0xFFFFFFFF)
            Local0 = NAnd (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x12]))
            M600 (Arg0, 0x07, Local0, 0x29AF5D7B)
            /* Method returns Integer */

            Local0 = NAnd (DerefOf (RefOf (BF65)), M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, 0xFFFFFFFF)
            Local0 = NAnd (DerefOf (RefOf (BF65)), M601 (0x01, 0x12))
            M600 (Arg0, 0x09, Local0, 0x29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NAnd (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, 0xFFFFFFFF)
                Local0 = NAnd (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x12, 0x01)))
                M600 (Arg0, 0x0B, Local0, 0x29AF5D7B)
            }

            NAnd (DerefOf (RefOf (BF65)), 0x00, Local0)
            M600 (Arg0, 0x0C, Local0, 0xFFFFFFFF)
            NAnd (DerefOf (RefOf (BF65)), 0xFFFFFFFF, Local0)
            M600 (Arg0, 0x0D, Local0, 0x29AF5D7B)
            NAnd (DerefOf (RefOf (BF65)), AUI5, Local0)
            M600 (Arg0, 0x0E, Local0, 0xFFFFFFFF)
            NAnd (DerefOf (RefOf (BF65)), AUII, Local0)
            M600 (Arg0, 0x0F, Local0, 0x29AF5D7B)
            If (Y078)
            {
                NAnd (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUI5)), Local0)
                M600 (Arg0, 0x10, Local0, 0xFFFFFFFF)
                NAnd (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUII)), Local0)
                M600 (Arg0, 0x11, Local0, 0x29AF5D7B)
            }

            NAnd (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x05]), Local0)
            M600 (Arg0, 0x12, Local0, 0xFFFFFFFF)
            NAnd (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x12]), Local0)
            M600 (Arg0, 0x13, Local0, 0x29AF5D7B)
            /* Method returns Integer */

            NAnd (DerefOf (RefOf (BF65)), M601 (0x01, 0x05), Local0)
            M600 (Arg0, 0x14, Local0, 0xFFFFFFFF)
            NAnd (DerefOf (RefOf (BF65)), M601 (0x01, 0x12), Local0)
            M600 (Arg0, 0x15, Local0, 0x29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NAnd (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x05, 0x01)), Local0)
                M600 (Arg0, 0x16, Local0, 0xFFFFFFFF)
                NAnd (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x12, 0x01)), Local0)
                M600 (Arg0, 0x17, Local0, 0x29AF5D7B)
            }

            /* Conversion of the second operand */

            Local0 = NAnd (0x00, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x18, Local0, 0xFFFFFFFF)
            Local0 = NAnd (0xFFFFFFFF, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x19, Local0, 0x29AF5D7B)
            Local0 = NAnd (AUI5, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1A, Local0, 0xFFFFFFFF)
            Local0 = NAnd (AUII, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1B, Local0, 0x29AF5D7B)
            If (Y078)
            {
                Local0 = NAnd (DerefOf (RefOf (AUI5)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x1C, Local0, 0xFFFFFFFF)
                Local0 = NAnd (DerefOf (RefOf (AUII)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x1D, Local0, 0x29AF5D7B)
            }

            Local0 = NAnd (DerefOf (PAUI [0x05]), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1E, Local0, 0xFFFFFFFF)
            Local0 = NAnd (DerefOf (PAUI [0x12]), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1F, Local0, 0x29AF5D7B)
            /* Method returns Integer */

            Local0 = NAnd (M601 (0x01, 0x05), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x20, Local0, 0xFFFFFFFF)
            Local0 = NAnd (M601 (0x01, 0x12), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x21, Local0, 0x29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NAnd (DerefOf (M602 (0x01, 0x05, 0x01)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x22, Local0, 0xFFFFFFFF)
                Local0 = NAnd (DerefOf (M602 (0x01, 0x12, 0x01)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x23, Local0, 0x29AF5D7B)
            }

            NAnd (0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x24, Local0, 0xFFFFFFFF)
            NAnd (0xFFFFFFFF, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x25, Local0, 0x29AF5D7B)
            NAnd (AUI5, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x26, Local0, 0xFFFFFFFF)
            NAnd (AUII, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x27, Local0, 0x29AF5D7B)
            If (Y078)
            {
                NAnd (DerefOf (RefOf (AUI5)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x28, Local0, 0xFFFFFFFF)
                NAnd (DerefOf (RefOf (AUII)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x29, Local0, 0x29AF5D7B)
            }

            NAnd (DerefOf (PAUI [0x05]), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2A, Local0, 0xFFFFFFFF)
            NAnd (DerefOf (PAUI [0x12]), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2B, Local0, 0x29AF5D7B)
            /* Method returns Integer */

            NAnd (M601 (0x01, 0x05), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2C, Local0, 0xFFFFFFFF)
            NAnd (M601 (0x01, 0x12), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2D, Local0, 0x29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NAnd (DerefOf (M602 (0x01, 0x05, 0x01)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x2E, Local0, 0xFFFFFFFF)
                NAnd (DerefOf (M602 (0x01, 0x12, 0x01)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x2F, Local0, 0x29AF5D7B)
            }

            /* Conversion of the both operands */

            Local0 = NAnd (DerefOf (RefOf (BF61)), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x30, Local0, 0xFFFFFDFF)
            Local0 = NAnd (DerefOf (RefOf (BF65)), DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x31, Local0, 0xFFFFFDFF)
            NAnd (DerefOf (RefOf (BF61)), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x32, Local0, 0xFFFFFDFF)
            NAnd (DerefOf (RefOf (BF65)), DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x33, Local0, 0xFFFFFDFF)
        }

        /* NOr, common 32-bit/64-bit test */

        Method (M04D, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Local0 = NOr (DerefOf (RefOf (BF61)), 0x00)
            M600 (Arg0, 0x00, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (DerefOf (RefOf (BF61)), 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x01, Local0, 0x00)
            Local0 = NOr (DerefOf (RefOf (BF61)), AUI5)
            M600 (Arg0, 0x02, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (DerefOf (RefOf (BF61)), AUIJ)
            M600 (Arg0, 0x03, Local0, 0x00)
            If (Y078)
            {
                Local0 = NOr (DerefOf (RefOf (BF61)), DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, 0xFFFFFFFFFFFFFCDE)
                Local0 = NOr (DerefOf (RefOf (BF61)), DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x05, Local0, 0x00)
            }

            Local0 = NOr (DerefOf (RefOf (BF61)), DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (DerefOf (RefOf (BF61)), DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x07, Local0, 0x00)
            /* Method returns Integer */

            Local0 = NOr (DerefOf (RefOf (BF61)), M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (DerefOf (RefOf (BF61)), M601 (0x01, 0x13))
            M600 (Arg0, 0x09, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NOr (DerefOf (RefOf (BF61)), DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, 0xFFFFFFFFFFFFFCDE)
                Local0 = NOr (DerefOf (RefOf (BF61)), DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x0B, Local0, 0x00)
            }

            NOr (DerefOf (RefOf (BF61)), 0x00, Local0)
            M600 (Arg0, 0x0C, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (DerefOf (RefOf (BF61)), 0xFFFFFFFFFFFFFFFF, Local0)
            M600 (Arg0, 0x0D, Local0, 0x00)
            NOr (DerefOf (RefOf (BF61)), AUI5, Local0)
            M600 (Arg0, 0x0E, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (DerefOf (RefOf (BF61)), AUIJ, Local0)
            M600 (Arg0, 0x0F, Local0, 0x00)
            If (Y078)
            {
                NOr (DerefOf (RefOf (BF61)), DerefOf (RefOf (AUI5)), Local0)
                M600 (Arg0, 0x10, Local0, 0xFFFFFFFFFFFFFCDE)
                NOr (DerefOf (RefOf (BF61)), DerefOf (RefOf (AUIJ)), Local0)
                M600 (Arg0, 0x11, Local0, 0x00)
            }

            NOr (DerefOf (RefOf (BF61)), DerefOf (PAUI [0x05]), Local0)
            M600 (Arg0, 0x12, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (DerefOf (RefOf (BF61)), DerefOf (PAUI [0x13]), Local0)
            M600 (Arg0, 0x13, Local0, 0x00)
            /* Method returns Integer */

            NOr (DerefOf (RefOf (BF61)), M601 (0x01, 0x05), Local0)
            M600 (Arg0, 0x14, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (DerefOf (RefOf (BF61)), M601 (0x01, 0x13), Local0)
            M600 (Arg0, 0x15, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NOr (DerefOf (RefOf (BF61)), DerefOf (M602 (0x01, 0x05, 0x01)), Local0)
                M600 (Arg0, 0x16, Local0, 0xFFFFFFFFFFFFFCDE)
                NOr (DerefOf (RefOf (BF61)), DerefOf (M602 (0x01, 0x13, 0x01)), Local0)
                M600 (Arg0, 0x17, Local0, 0x00)
            }

            /* Conversion of the second operand */

            Local0 = NOr (0x00, DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x18, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (0xFFFFFFFFFFFFFFFF, DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x19, Local0, 0x00)
            Local0 = NOr (AUI5, DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x1A, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (AUIJ, DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x1B, Local0, 0x00)
            If (Y078)
            {
                Local0 = NOr (DerefOf (RefOf (AUI5)), DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x1C, Local0, 0xFFFFFFFFFFFFFCDE)
                Local0 = NOr (DerefOf (RefOf (AUIJ)), DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x1D, Local0, 0x00)
            }

            Local0 = NOr (DerefOf (PAUI [0x05]), DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x1E, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (DerefOf (PAUI [0x13]), DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x1F, Local0, 0x00)
            /* Method returns Integer */

            Local0 = NOr (M601 (0x01, 0x05), DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x20, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (M601 (0x01, 0x13), DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x21, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NOr (DerefOf (M602 (0x01, 0x05, 0x01)), DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x22, Local0, 0xFFFFFFFFFFFFFCDE)
                Local0 = NOr (DerefOf (M602 (0x01, 0x13, 0x01)), DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x23, Local0, 0x00)
            }

            NOr (0x00, DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x24, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (0xFFFFFFFFFFFFFFFF, DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x25, Local0, 0x00)
            NOr (AUI5, DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x26, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (AUIJ, DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x27, Local0, 0x00)
            If (Y078)
            {
                NOr (DerefOf (RefOf (AUI5)), DerefOf (RefOf (BF61)), Local0)
                M600 (Arg0, 0x28, Local0, 0xFFFFFFFFFFFFFCDE)
                NOr (DerefOf (RefOf (AUIJ)), DerefOf (RefOf (BF61)), Local0)
                M600 (Arg0, 0x29, Local0, 0x00)
            }

            NOr (DerefOf (PAUI [0x05]), DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x2A, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (DerefOf (PAUI [0x13]), DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x2B, Local0, 0x00)
            /* Method returns Integer */

            NOr (M601 (0x01, 0x05), DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x2C, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (M601 (0x01, 0x13), DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x2D, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NOr (DerefOf (M602 (0x01, 0x05, 0x01)), DerefOf (RefOf (BF61)), Local0)
                M600 (Arg0, 0x2E, Local0, 0xFFFFFFFFFFFFFCDE)
                NOr (DerefOf (M602 (0x01, 0x13, 0x01)), DerefOf (RefOf (BF61)), Local0)
                M600 (Arg0, 0x2F, Local0, 0x00)
            }
        }

        /* NOr, 64-bit */

        Method (M04E, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Local0 = NOr (DerefOf (RefOf (BF65)), 0x00)
            M600 (Arg0, 0x00, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (DerefOf (RefOf (BF65)), 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x01, Local0, 0x00)
            Local0 = NOr (DerefOf (RefOf (BF65)), AUI5)
            M600 (Arg0, 0x02, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (DerefOf (RefOf (BF65)), AUIJ)
            M600 (Arg0, 0x03, Local0, 0x00)
            If (Y078)
            {
                Local0 = NOr (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, 0x01834C6E29AF5D7B)
                Local0 = NOr (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x05, Local0, 0x00)
            }

            Local0 = NOr (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x07, Local0, 0x00)
            /* Method returns Integer */

            Local0 = NOr (DerefOf (RefOf (BF65)), M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (DerefOf (RefOf (BF65)), M601 (0x01, 0x13))
            M600 (Arg0, 0x09, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NOr (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, 0x01834C6E29AF5D7B)
                Local0 = NOr (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x0B, Local0, 0x00)
            }

            NOr (DerefOf (RefOf (BF65)), 0x00, Local0)
            M600 (Arg0, 0x0C, Local0, 0x01834C6E29AF5D7B)
            NOr (DerefOf (RefOf (BF65)), 0xFFFFFFFFFFFFFFFF, Local0)
            M600 (Arg0, 0x0D, Local0, 0x00)
            NOr (DerefOf (RefOf (BF65)), AUI5, Local0)
            M600 (Arg0, 0x0E, Local0, 0x01834C6E29AF5D7B)
            NOr (DerefOf (RefOf (BF65)), AUIJ, Local0)
            M600 (Arg0, 0x0F, Local0, 0x00)
            If (Y078)
            {
                NOr (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUI5)), Local0)
                M600 (Arg0, 0x10, Local0, 0x01834C6E29AF5D7B)
                NOr (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUIJ)), Local0)
                M600 (Arg0, 0x11, Local0, 0x00)
            }

            NOr (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x05]), Local0)
            M600 (Arg0, 0x12, Local0, 0x01834C6E29AF5D7B)
            NOr (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x13]), Local0)
            M600 (Arg0, 0x13, Local0, 0x00)
            /* Method returns Integer */

            NOr (DerefOf (RefOf (BF65)), M601 (0x01, 0x05), Local0)
            M600 (Arg0, 0x14, Local0, 0x01834C6E29AF5D7B)
            NOr (DerefOf (RefOf (BF65)), M601 (0x01, 0x13), Local0)
            M600 (Arg0, 0x15, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NOr (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x05, 0x01)), Local0)
                M600 (Arg0, 0x16, Local0, 0x01834C6E29AF5D7B)
                NOr (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x13, 0x01)), Local0)
                M600 (Arg0, 0x17, Local0, 0x00)
            }

            /* Conversion of the second operand */

            Local0 = NOr (0x00, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x18, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (0xFFFFFFFFFFFFFFFF, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x19, Local0, 0x00)
            Local0 = NOr (AUI5, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1A, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (AUIJ, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1B, Local0, 0x00)
            If (Y078)
            {
                Local0 = NOr (DerefOf (RefOf (AUI5)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x1C, Local0, 0x01834C6E29AF5D7B)
                Local0 = NOr (DerefOf (RefOf (AUIJ)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x1D, Local0, 0x00)
            }

            Local0 = NOr (DerefOf (PAUI [0x05]), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1E, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (DerefOf (PAUI [0x13]), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1F, Local0, 0x00)
            /* Method returns Integer */

            Local0 = NOr (M601 (0x01, 0x05), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x20, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (M601 (0x01, 0x13), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x21, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NOr (DerefOf (M602 (0x01, 0x05, 0x01)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x22, Local0, 0x01834C6E29AF5D7B)
                Local0 = NOr (DerefOf (M602 (0x01, 0x13, 0x01)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x23, Local0, 0x00)
            }

            NOr (0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x24, Local0, 0x01834C6E29AF5D7B)
            NOr (0xFFFFFFFFFFFFFFFF, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x25, Local0, 0x00)
            NOr (AUI5, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x26, Local0, 0x01834C6E29AF5D7B)
            NOr (AUIJ, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x27, Local0, 0x00)
            If (Y078)
            {
                NOr (DerefOf (RefOf (AUI5)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x28, Local0, 0x01834C6E29AF5D7B)
                NOr (DerefOf (RefOf (AUIJ)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x29, Local0, 0x00)
            }

            NOr (DerefOf (PAUI [0x05]), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2A, Local0, 0x01834C6E29AF5D7B)
            NOr (DerefOf (PAUI [0x13]), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2B, Local0, 0x00)
            /* Method returns Integer */

            NOr (M601 (0x01, 0x05), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2C, Local0, 0x01834C6E29AF5D7B)
            NOr (M601 (0x01, 0x13), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2D, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NOr (DerefOf (M602 (0x01, 0x05, 0x01)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x2E, Local0, 0x01834C6E29AF5D7B)
                NOr (DerefOf (M602 (0x01, 0x13, 0x01)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x2F, Local0, 0x00)
            }

            /* Conversion of the both operands */

            Local0 = NOr (DerefOf (RefOf (BF61)), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x30, Local0, 0x01834C6E29AF5C5A)
            Local0 = NOr (DerefOf (RefOf (BF65)), DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x31, Local0, 0x01834C6E29AF5C5A)
            NOr (DerefOf (RefOf (BF61)), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x32, Local0, 0x01834C6E29AF5C5A)
            NOr (DerefOf (RefOf (BF65)), DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x33, Local0, 0x01834C6E29AF5C5A)
        }

        /* NOr, 32-bit */

        Method (M04F, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Local0 = NOr (DerefOf (RefOf (BF65)), 0x00)
            M600 (Arg0, 0x00, Local0, 0x29AF5D7B)
            Local0 = NOr (DerefOf (RefOf (BF65)), 0xFFFFFFFF)
            M600 (Arg0, 0x01, Local0, 0x00)
            Local0 = NOr (DerefOf (RefOf (BF65)), AUI5)
            M600 (Arg0, 0x02, Local0, 0x29AF5D7B)
            Local0 = NOr (DerefOf (RefOf (BF65)), AUII)
            M600 (Arg0, 0x03, Local0, 0x00)
            If (Y078)
            {
                Local0 = NOr (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, 0x29AF5D7B)
                Local0 = NOr (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUII)))
                M600 (Arg0, 0x05, Local0, 0x00)
            }

            Local0 = NOr (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, 0x29AF5D7B)
            Local0 = NOr (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x12]))
            M600 (Arg0, 0x07, Local0, 0x00)
            /* Method returns Integer */

            Local0 = NOr (DerefOf (RefOf (BF65)), M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, 0x29AF5D7B)
            Local0 = NOr (DerefOf (RefOf (BF65)), M601 (0x01, 0x12))
            M600 (Arg0, 0x09, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NOr (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, 0x29AF5D7B)
                Local0 = NOr (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x12, 0x01)))
                M600 (Arg0, 0x0B, Local0, 0x00)
            }

            NOr (DerefOf (RefOf (BF65)), 0x00, Local0)
            M600 (Arg0, 0x0C, Local0, 0x29AF5D7B)
            NOr (DerefOf (RefOf (BF65)), 0xFFFFFFFF, Local0)
            M600 (Arg0, 0x0D, Local0, 0x00)
            NOr (DerefOf (RefOf (BF65)), AUI5, Local0)
            M600 (Arg0, 0x0E, Local0, 0x29AF5D7B)
            NOr (DerefOf (RefOf (BF65)), AUII, Local0)
            M600 (Arg0, 0x0F, Local0, 0x00)
            If (Y078)
            {
                NOr (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUI5)), Local0)
                M600 (Arg0, 0x10, Local0, 0x29AF5D7B)
                NOr (DerefOf (RefOf (BF65)), DerefOf (RefOf (AUII)), Local0)
                M600 (Arg0, 0x11, Local0, 0x00)
            }

            NOr (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x05]), Local0)
            M600 (Arg0, 0x12, Local0, 0x29AF5D7B)
            NOr (DerefOf (RefOf (BF65)), DerefOf (PAUI [0x12]), Local0)
            M600 (Arg0, 0x13, Local0, 0x00)
            /* Method returns Integer */

            NOr (DerefOf (RefOf (BF65)), M601 (0x01, 0x05), Local0)
            M600 (Arg0, 0x14, Local0, 0x29AF5D7B)
            NOr (DerefOf (RefOf (BF65)), M601 (0x01, 0x12), Local0)
            M600 (Arg0, 0x15, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NOr (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x05, 0x01)), Local0)
                M600 (Arg0, 0x16, Local0, 0x29AF5D7B)
                NOr (DerefOf (RefOf (BF65)), DerefOf (M602 (0x01, 0x12, 0x01)), Local0)
                M600 (Arg0, 0x17, Local0, 0x00)
            }

            /* Conversion of the second operand */

            Local0 = NOr (0x00, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x18, Local0, 0x29AF5D7B)
            Local0 = NOr (0xFFFFFFFF, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x19, Local0, 0x00)
            Local0 = NOr (AUI5, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1A, Local0, 0x29AF5D7B)
            Local0 = NOr (AUII, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1B, Local0, 0x00)
            If (Y078)
            {
                Local0 = NOr (DerefOf (RefOf (AUI5)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x1C, Local0, 0x29AF5D7B)
                Local0 = NOr (DerefOf (RefOf (AUII)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x1D, Local0, 0x00)
            }

            Local0 = NOr (DerefOf (PAUI [0x05]), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1E, Local0, 0x29AF5D7B)
            Local0 = NOr (DerefOf (PAUI [0x12]), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1F, Local0, 0x00)
            /* Method returns Integer */

            Local0 = NOr (M601 (0x01, 0x05), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x20, Local0, 0x29AF5D7B)
            Local0 = NOr (M601 (0x01, 0x12), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x21, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NOr (DerefOf (M602 (0x01, 0x05, 0x01)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x22, Local0, 0x29AF5D7B)
                Local0 = NOr (DerefOf (M602 (0x01, 0x12, 0x01)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x23, Local0, 0x00)
            }

            NOr (0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x24, Local0, 0x29AF5D7B)
            NOr (0xFFFFFFFF, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x25, Local0, 0x00)
            NOr (AUI5, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x26, Local0, 0x29AF5D7B)
            NOr (AUII, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x27, Local0, 0x00)
            If (Y078)
            {
                NOr (DerefOf (RefOf (AUI5)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x28, Local0, 0x29AF5D7B)
                NOr (DerefOf (RefOf (AUII)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x29, Local0, 0x00)
            }

            NOr (DerefOf (PAUI [0x05]), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2A, Local0, 0x29AF5D7B)
            NOr (DerefOf (PAUI [0x12]), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2B, Local0, 0x00)
            /* Method returns Integer */

            NOr (M601 (0x01, 0x05), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2C, Local0, 0x29AF5D7B)
            NOr (M601 (0x01, 0x12), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2D, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NOr (DerefOf (M602 (0x01, 0x05, 0x01)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x2E, Local0, 0x29AF5D7B)
                NOr (DerefOf (M602 (0x01, 0x12, 0x01)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x2F, Local0, 0x00)
            }

            /* Conversion of the both operands */

            Local0 = NOr (DerefOf (RefOf (BF61)), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x30, Local0, 0x29AF5C5A)
            Local0 = NOr (DerefOf (RefOf (BF65)), DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x31, Local0, 0x29AF5C5A)
            NOr (DerefOf (RefOf (BF61)), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x32, Local0, 0x29AF5C5A)
            NOr (DerefOf (RefOf (BF65)), DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x33, Local0, 0x29AF5C5A)
        }

        /* Or, common 32-bit/64-bit test */

        Method (M050, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF61)) | 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) | 0xFFFFFFFFFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0xFFFFFFFFFFFFFFFF)
            Store ((DerefOf (RefOf (BF61)) | AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) | AUIJ), Local0)
            M600 (Arg0, 0x03, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF61)) | DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((DerefOf (RefOf (BF61)) | DerefOf (RefOf (AUIJ))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Store ((DerefOf (RefOf (BF61)) | DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) | DerefOf (PAUI [0x13])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF61)) | M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) | M601 (0x01, 0x13)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF61)) | DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((DerefOf (RefOf (BF61)) | DerefOf (M602 (0x01, 0x13, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (DerefOf (RefOf (BF61)) | 0x00)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) | 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = (DerefOf (RefOf (BF61)) | AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) | AUIJ) /* \AUIJ */
            M600 (Arg0, 0x0F, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF61)) | DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (BF61)) | DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x11, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (DerefOf (RefOf (BF61)) | DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) | DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x13, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF61)) | M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) | M601 (0x01, 0x13))
            M600 (Arg0, 0x15, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF61)) | DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (BF61)) | DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            /* Conversion of the second operand */

            Store ((0x00 | DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x18, Local0, 0x0321)
            Store ((0xFFFFFFFFFFFFFFFF | DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x19, Local0, 0xFFFFFFFFFFFFFFFF)
            Store ((AUI5 | DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x0321)
            Store ((AUIJ | DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) | DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x0321)
                Store ((DerefOf (RefOf (AUIJ)) | DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Store ((DerefOf (PAUI [0x05]) | DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x0321)
            Store ((DerefOf (PAUI [0x13]) | DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) | DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x20, Local0, 0x0321)
            Store ((M601 (0x01, 0x13) | DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x21, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) | DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x22, Local0, 0x0321)
                Store ((DerefOf (M602 (0x01, 0x13, 0x01)) | DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x23, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (0x00 | DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x24, Local0, 0x0321)
            Local0 = (0xFFFFFFFFFFFFFFFF | DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x25, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = (AUI5 | DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x26, Local0, 0x0321)
            Local0 = (AUIJ | DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x27, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) | DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x28, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (AUIJ)) | DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x29, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (DerefOf (PAUI [0x05]) | DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2A, Local0, 0x0321)
            Local0 = (DerefOf (PAUI [0x13]) | DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2B, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) | DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2C, Local0, 0x0321)
            Local0 = (M601 (0x01, 0x13) | DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2D, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) | DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x2E, Local0, 0x0321)
                Local0 = (DerefOf (M602 (0x01, 0x13, 0x01)) | DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x2F, Local0, 0xFFFFFFFFFFFFFFFF)
            }
        }

        /* Or, 64-bit */

        Method (M051, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) | 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) | 0xFFFFFFFFFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0xFFFFFFFFFFFFFFFF)
            Store ((DerefOf (RefOf (BF65)) | AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) | AUIJ), Local0)
            M600 (Arg0, 0x03, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) | DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (BF65)) | DerefOf (RefOf (AUIJ))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Store ((DerefOf (RefOf (BF65)) | DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) | DerefOf (PAUI [0x13])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) | M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) | M601 (0x01, 0x13)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) | DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (BF65)) | DerefOf (M602 (0x01, 0x13, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (DerefOf (RefOf (BF65)) | 0x00)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) | 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = (DerefOf (RefOf (BF65)) | AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) | AUIJ) /* \AUIJ */
            M600 (Arg0, 0x0F, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) | DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (BF65)) | DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x11, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (DerefOf (RefOf (BF65)) | DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) | DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x13, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) | M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) | M601 (0x01, 0x13))
            M600 (Arg0, 0x15, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) | DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (BF65)) | DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            /* Conversion of the second operand */

            Store ((0x00 | DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x18, Local0, 0xFE7CB391D650A284)
            Store ((0xFFFFFFFFFFFFFFFF | DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x19, Local0, 0xFFFFFFFFFFFFFFFF)
            Store ((AUI5 | DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1A, Local0, 0xFE7CB391D650A284)
            Store ((AUIJ | DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) | DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1C, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (AUIJ)) | DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Store ((DerefOf (PAUI [0x05]) | DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1E, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (PAUI [0x13]) | DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) | DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x20, Local0, 0xFE7CB391D650A284)
            Store ((M601 (0x01, 0x13) | DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x21, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) | DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x22, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (M602 (0x01, 0x13, 0x01)) | DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x23, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (0x00 | DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x24, Local0, 0xFE7CB391D650A284)
            Local0 = (0xFFFFFFFFFFFFFFFF | DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x25, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = (AUI5 | DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x26, Local0, 0xFE7CB391D650A284)
            Local0 = (AUIJ | DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x27, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) | DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x28, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (AUIJ)) | DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x29, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (DerefOf (PAUI [0x05]) | DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2A, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (PAUI [0x13]) | DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2B, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) | DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2C, Local0, 0xFE7CB391D650A284)
            Local0 = (M601 (0x01, 0x13) | DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2D, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) | DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2E, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (M602 (0x01, 0x13, 0x01)) | DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2F, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) | DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x30, Local0, 0xFE7CB391D650A3A5)
            Store ((DerefOf (RefOf (BF65)) | DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x31, Local0, 0xFE7CB391D650A3A5)
            Local0 = (DerefOf (RefOf (BF61)) | DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x32, Local0, 0xFE7CB391D650A3A5)
            Local0 = (DerefOf (RefOf (BF65)) | DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x33, Local0, 0xFE7CB391D650A3A5)
        }

        /* Or, 32-bit */

        Method (M052, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) | 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) | 0xFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0xFFFFFFFF)
            Store ((DerefOf (RefOf (BF65)) | AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) | AUII), Local0)
            M600 (Arg0, 0x03, Local0, 0xFFFFFFFF)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) | DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (BF65)) | DerefOf (RefOf (AUII))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFFFFFFFF)
            }

            Store ((DerefOf (RefOf (BF65)) | DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) | DerefOf (PAUI [0x12])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFFFFFFFF)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) | M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) | M601 (0x01, 0x12)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) | DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (BF65)) | DerefOf (M602 (0x01, 0x12, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFFFFFFFF)
            }

            Local0 = (DerefOf (RefOf (BF65)) | 0x00)
            M600 (Arg0, 0x0C, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) | 0xFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0xFFFFFFFF)
            Local0 = (DerefOf (RefOf (BF65)) | AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) | AUII) /* \AUII */
            M600 (Arg0, 0x0F, Local0, 0xFFFFFFFF)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) | DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (BF65)) | DerefOf (RefOf (AUII)))
                M600 (Arg0, 0x11, Local0, 0xFFFFFFFF)
            }

            Local0 = (DerefOf (RefOf (BF65)) | DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) | DerefOf (PAUI [0x12]))
            M600 (Arg0, 0x13, Local0, 0xFFFFFFFF)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) | M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) | M601 (0x01, 0x12))
            M600 (Arg0, 0x15, Local0, 0xFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) | DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (BF65)) | DerefOf (M602 (0x01, 0x12, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFFFFFFFF)
            }

            /* Conversion of the second operand */

            Store ((0x00 | DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x18, Local0, 0xD650A284)
            Store ((0xFFFFFFFF | DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x19, Local0, 0xFFFFFFFF)
            Store ((AUI5 | DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1A, Local0, 0xD650A284)
            Store ((AUII | DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFFFFFFFF)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) | DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1C, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (AUII)) | DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFFFFFFFF)
            }

            Store ((DerefOf (PAUI [0x05]) | DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1E, Local0, 0xD650A284)
            Store ((DerefOf (PAUI [0x12]) | DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFFFFFFFF)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) | DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x20, Local0, 0xD650A284)
            Store ((M601 (0x01, 0x12) | DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x21, Local0, 0xFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) | DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x22, Local0, 0xD650A284)
                Store ((DerefOf (M602 (0x01, 0x12, 0x01)) | DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x23, Local0, 0xFFFFFFFF)
            }

            Local0 = (0x00 | DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x24, Local0, 0xD650A284)
            Local0 = (0xFFFFFFFF | DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x25, Local0, 0xFFFFFFFF)
            Local0 = (AUI5 | DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x26, Local0, 0xD650A284)
            Local0 = (AUII | DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x27, Local0, 0xFFFFFFFF)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) | DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x28, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (AUII)) | DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x29, Local0, 0xFFFFFFFF)
            }

            Local0 = (DerefOf (PAUI [0x05]) | DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2A, Local0, 0xD650A284)
            Local0 = (DerefOf (PAUI [0x12]) | DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2B, Local0, 0xFFFFFFFF)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) | DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2C, Local0, 0xD650A284)
            Local0 = (M601 (0x01, 0x12) | DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2D, Local0, 0xFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) | DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2E, Local0, 0xD650A284)
                Local0 = (DerefOf (M602 (0x01, 0x12, 0x01)) | DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2F, Local0, 0xFFFFFFFF)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) | DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x30, Local0, 0xD650A3A5)
            Store ((DerefOf (RefOf (BF65)) | DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x31, Local0, 0xD650A3A5)
            Local0 = (DerefOf (RefOf (BF61)) | DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x32, Local0, 0xD650A3A5)
            Local0 = (DerefOf (RefOf (BF65)) | DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x33, Local0, 0xD650A3A5)
        }

        /* ShiftLeft, common 32-bit/64-bit test */

        Method (M053, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF61)) << 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) << 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x0642)
            Store ((DerefOf (RefOf (BF61)) << AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) << AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x0642)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF61)) << DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((DerefOf (RefOf (BF61)) << DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x0642)
            }

            Store ((DerefOf (RefOf (BF61)) << DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) << DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x0642)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF61)) << M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) << M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x0642)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF61)) << DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((DerefOf (RefOf (BF61)) << DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x0642)
            }

            Local0 = (DerefOf (RefOf (BF61)) << 0x00)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) << 0x01)
            M600 (Arg0, 0x0D, Local0, 0x0642)
            Local0 = (DerefOf (RefOf (BF61)) << AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) << AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x0642)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF61)) << DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (BF61)) << DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x0642)
            }

            Local0 = (DerefOf (RefOf (BF61)) << DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) << DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x0642)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF61)) << M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) << M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x0642)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF61)) << DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (BF61)) << DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x0642)
            }

            /* Conversion of the second operand */

            Store ((0x00 << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x01 << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x19, Local0, 0x0800)
            Store ((AUI5 << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI6 << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0800)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) << DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI6)) << DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0800)
            }

            Store ((DerefOf (PAUI [0x05]) << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x06]) << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0800)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x06) << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x21, Local0, 0x0800)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) << DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) << DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x23, Local0, 0x0800)
            }

            Local0 = (0x00 << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0x01 << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x25, Local0, 0x0800)
            Local0 = (AUI5 << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI6 << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x27, Local0, 0x0800)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) << DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI6)) << DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x29, Local0, 0x0800)
            }

            Local0 = (DerefOf (PAUI [0x05]) << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x06]) << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2B, Local0, 0x0800)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x06) << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2D, Local0, 0x0800)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) << DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) << DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x2F, Local0, 0x0800)
            }
        }

        /* ShiftLeft, 64-bit */

        Method (M054, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) << 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) << 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xFCF96723ACA14508)
            Store ((DerefOf (RefOf (BF65)) << AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) << AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xFCF96723ACA14508)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) << DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (BF65)) << DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFCF96723ACA14508)
            }

            Store ((DerefOf (RefOf (BF65)) << DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) << DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFCF96723ACA14508)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) << M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) << M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFCF96723ACA14508)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) << DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (BF65)) << DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFCF96723ACA14508)
            }

            Local0 = (DerefOf (RefOf (BF65)) << 0x00)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) << 0x01)
            M600 (Arg0, 0x0D, Local0, 0xFCF96723ACA14508)
            Local0 = (DerefOf (RefOf (BF65)) << AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) << AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xFCF96723ACA14508)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) << DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (BF65)) << DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xFCF96723ACA14508)
            }

            Local0 = (DerefOf (RefOf (BF65)) << DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) << DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xFCF96723ACA14508)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) << M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) << M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xFCF96723ACA14508)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) << DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (BF65)) << DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFCF96723ACA14508)
            }

            /* Conversion of the second operand */

            Store ((0x00 << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x01 << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x19, Local0, 0x0800)
            Store ((AUI5 << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI6 << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0800)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) << DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI6)) << DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0800)
            }

            Store ((DerefOf (PAUI [0x05]) << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x06]) << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0800)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x06) << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x21, Local0, 0x0800)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) << DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) << DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x23, Local0, 0x0800)
            }

            Local0 = (0x00 << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0x01 << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x25, Local0, 0x0800)
            Local0 = (AUI5 << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI6 << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x27, Local0, 0x0800)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) << DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI6)) << DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x29, Local0, 0x0800)
            }

            Local0 = (DerefOf (PAUI [0x05]) << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x06]) << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2B, Local0, 0x0800)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x06) << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2D, Local0, 0x0800)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) << DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) << DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x2F, Local0, 0x0800)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x30, Local0, 0x00190800)
            Store ((DerefOf (RefOf (BF65)) << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x31, Local0, 0xE59C8EB285142000)
            Local0 = (DerefOf (RefOf (BF61)) << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x32, Local0, 0x00190800)
            Local0 = (DerefOf (RefOf (BF65)) << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x33, Local0, 0xE59C8EB285142000)
        }

        /* ShiftLeft, 32-bit */

        Method (M055, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) << 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) << 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xACA14508)
            Store ((DerefOf (RefOf (BF65)) << AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) << AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xACA14508)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) << DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (BF65)) << DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xACA14508)
            }

            Store ((DerefOf (RefOf (BF65)) << DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) << DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xACA14508)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) << M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) << M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xACA14508)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) << DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (BF65)) << DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xACA14508)
            }

            Local0 = (DerefOf (RefOf (BF65)) << 0x00)
            M600 (Arg0, 0x0C, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) << 0x01)
            M600 (Arg0, 0x0D, Local0, 0xACA14508)
            Local0 = (DerefOf (RefOf (BF65)) << AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) << AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xACA14508)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) << DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (BF65)) << DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xACA14508)
            }

            Local0 = (DerefOf (RefOf (BF65)) << DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) << DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xACA14508)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) << M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) << M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xACA14508)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) << DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (BF65)) << DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xACA14508)
            }

            /* Conversion of the second operand */

            Store ((0x00 << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x01 << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x19, Local0, 0x0800)
            Store ((AUI5 << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI6 << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0800)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) << DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI6)) << DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0800)
            }

            Store ((DerefOf (PAUI [0x05]) << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x06]) << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0800)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x06) << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x21, Local0, 0x0800)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) << DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) << DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x23, Local0, 0x0800)
            }

            Local0 = (0x00 << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0x01 << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x25, Local0, 0x0800)
            Local0 = (AUI5 << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI6 << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x27, Local0, 0x0800)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) << DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI6)) << DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x29, Local0, 0x0800)
            }

            Local0 = (DerefOf (PAUI [0x05]) << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x06]) << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2B, Local0, 0x0800)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x06) << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2D, Local0, 0x0800)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) << DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) << DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x2F, Local0, 0x0800)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x30, Local0, 0x00190800)
            Store ((DerefOf (RefOf (BF65)) << DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x31, Local0, 0x85142000)
            Local0 = (DerefOf (RefOf (BF61)) << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x32, Local0, 0x00190800)
            Local0 = (DerefOf (RefOf (BF65)) << DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x33, Local0, 0x85142000)
        }

        /* ShiftRight, common 32-bit/64-bit test */

        Method (M056, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF61)) >> 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) >> 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x0190)
            Store ((DerefOf (RefOf (BF61)) >> AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) >> AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x0190)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF61)) >> DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((DerefOf (RefOf (BF61)) >> DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x0190)
            }

            Store ((DerefOf (RefOf (BF61)) >> DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) >> DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x0190)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF61)) >> M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) >> M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x0190)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF61)) >> DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((DerefOf (RefOf (BF61)) >> DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x0190)
            }

            Local0 = (DerefOf (RefOf (BF61)) >> 0x00)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) >> 0x01)
            M600 (Arg0, 0x0D, Local0, 0x0190)
            Local0 = (DerefOf (RefOf (BF61)) >> AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) >> AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x0190)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF61)) >> DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (BF61)) >> DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x0190)
            }

            Local0 = (DerefOf (RefOf (BF61)) >> DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) >> DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x0190)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF61)) >> M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) >> M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x0190)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF61)) >> DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (BF61)) >> DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x0190)
            }

            /* Conversion of the second operand */

            Store ((0x0321 >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xD650A284 >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x19, Local0, 0x001ACA14)
            Store ((AUI1 >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUIK >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1B, Local0, 0x001ACA14)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI1)) >> DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUIK)) >> DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x1D, Local0, 0x001ACA14)
            }

            Store ((DerefOf (PAUI [0x01]) >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x14]) >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1F, Local0, 0x001ACA14)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x01) >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x14) >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x21, Local0, 0x001ACA14)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x01, 0x01)) >> DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x14, 0x01)) >> DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x23, Local0, 0x001ACA14)
            }

            Local0 = (0x0321 >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0xD650A284 >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x25, Local0, 0x001ACA14)
            Local0 = (AUI1 >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUIK >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x27, Local0, 0x001ACA14)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) >> DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUIK)) >> DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x29, Local0, 0x001ACA14)
            }

            Local0 = (DerefOf (PAUI [0x01]) >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x14]) >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2B, Local0, 0x001ACA14)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x14) >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2D, Local0, 0x001ACA14)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) >> DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x14, 0x01)) >> DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x2F, Local0, 0x001ACA14)
            }
        }

        /* ShiftRight, 64-bit */

        Method (M057, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) >> 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) >> 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x7F3E59C8EB285142)
            Store ((DerefOf (RefOf (BF65)) >> AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) >> AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x7F3E59C8EB285142)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) >> DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (BF65)) >> DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x7F3E59C8EB285142)
            }

            Store ((DerefOf (RefOf (BF65)) >> DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) >> DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x7F3E59C8EB285142)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) >> M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) >> M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x7F3E59C8EB285142)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) >> DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (BF65)) >> DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x7F3E59C8EB285142)
            }

            Local0 = (DerefOf (RefOf (BF65)) >> 0x00)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) >> 0x01)
            M600 (Arg0, 0x0D, Local0, 0x7F3E59C8EB285142)
            Local0 = (DerefOf (RefOf (BF65)) >> AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) >> AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x7F3E59C8EB285142)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) >> DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (BF65)) >> DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x7F3E59C8EB285142)
            }

            Local0 = (DerefOf (RefOf (BF65)) >> DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) >> DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x7F3E59C8EB285142)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) >> M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) >> M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x7F3E59C8EB285142)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) >> DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (BF65)) >> DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x7F3E59C8EB285142)
            }

            /* Conversion of the second operand */

            Store ((0x0321 >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xFE7CB391D650A284 >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x19, Local0, 0x001FCF96723ACA14)
            Store ((AUI1 >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI4 >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1B, Local0, 0x001FCF96723ACA14)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI1)) >> DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI4)) >> DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x1D, Local0, 0x001FCF96723ACA14)
            }

            Store ((DerefOf (PAUI [0x01]) >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x04]) >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1F, Local0, 0x001FCF96723ACA14)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x01) >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x04) >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x21, Local0, 0x001FCF96723ACA14)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x01, 0x01)) >> DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x04, 0x01)) >> DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x23, Local0, 0x001FCF96723ACA14)
            }

            Local0 = (0x0321 >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0xFE7CB391D650A284 >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x25, Local0, 0x001FCF96723ACA14)
            Local0 = (AUI1 >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI4 >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x27, Local0, 0x001FCF96723ACA14)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) >> DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI4)) >> DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x29, Local0, 0x001FCF96723ACA14)
            }

            Local0 = (DerefOf (PAUI [0x01]) >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x04]) >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2B, Local0, 0x001FCF96723ACA14)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x04) >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2D, Local0, 0x001FCF96723ACA14)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) >> DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) >> DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x2F, Local0, 0x001FCF96723ACA14)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x30, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x31, Local0, 0x001FCF96723ACA14)
            Local0 = (DerefOf (RefOf (BF61)) >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x32, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF65)) >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x33, Local0, 0x001FCF96723ACA14)
        }

        /* ShiftRight, 32-bit */

        Method (M058, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) >> 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) >> 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x6B285142)
            Store ((DerefOf (RefOf (BF65)) >> AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) >> AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x6B285142)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) >> DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (BF65)) >> DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x6B285142)
            }

            Store ((DerefOf (RefOf (BF65)) >> DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) >> DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x6B285142)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) >> M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) >> M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x6B285142)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) >> DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (BF65)) >> DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x6B285142)
            }

            Local0 = (DerefOf (RefOf (BF65)) >> 0x00)
            M600 (Arg0, 0x0C, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) >> 0x01)
            M600 (Arg0, 0x0D, Local0, 0x6B285142)
            Local0 = (DerefOf (RefOf (BF65)) >> AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) >> AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x6B285142)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) >> DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (BF65)) >> DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x6B285142)
            }

            Local0 = (DerefOf (RefOf (BF65)) >> DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) >> DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x6B285142)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) >> M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) >> M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x6B285142)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) >> DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (BF65)) >> DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x6B285142)
            }

            /* Conversion of the second operand */

            Store ((0x0321 >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xD650A284 >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x19, Local0, 0x001ACA14)
            Store ((AUI1 >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUIK >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1B, Local0, 0x001ACA14)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI1)) >> DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUIK)) >> DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x1D, Local0, 0x001ACA14)
            }

            Store ((DerefOf (PAUI [0x01]) >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x14]) >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x1F, Local0, 0x001ACA14)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x01) >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x14) >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x21, Local0, 0x001ACA14)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x01, 0x01)) >> DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x14, 0x01)) >> DerefOf (RefOf (BF74))), Local0)
                M600 (Arg0, 0x23, Local0, 0x001ACA14)
            }

            Local0 = (0x0321 >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0xD650A284 >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x25, Local0, 0x001ACA14)
            Local0 = (AUI1 >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUIK >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x27, Local0, 0x001ACA14)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) >> DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUIK)) >> DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x29, Local0, 0x001ACA14)
            }

            Local0 = (DerefOf (PAUI [0x01]) >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x14]) >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2B, Local0, 0x001ACA14)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x14) >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x2D, Local0, 0x001ACA14)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) >> DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x14, 0x01)) >> DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x2F, Local0, 0x001ACA14)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x30, Local0, 0x00)
            Store ((DerefOf (RefOf (BF65)) >> DerefOf (RefOf (BF74))), Local0)
            M600 (Arg0, 0x31, Local0, 0x001ACA14)
            Local0 = (DerefOf (RefOf (BF61)) >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x32, Local0, 0x00)
            Local0 = (DerefOf (RefOf (BF65)) >> DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x33, Local0, 0x001ACA14)
        }

        /* Subtract, common 32-bit/64-bit test */

        Method (M059, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF61)) - 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) - 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x0320)
            Store ((DerefOf (RefOf (BF61)) - AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) - AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x0320)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF61)) - DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((DerefOf (RefOf (BF61)) - DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x0320)
            }

            Store ((DerefOf (RefOf (BF61)) - DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) - DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x0320)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF61)) - M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) - M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x0320)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF61)) - DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((DerefOf (RefOf (BF61)) - DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x0320)
            }

            Local0 = (DerefOf (RefOf (BF61)) - 0x00)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) - 0x01)
            M600 (Arg0, 0x0D, Local0, 0x0320)
            Local0 = (DerefOf (RefOf (BF61)) - AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) - AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x0320)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF61)) - DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (BF61)) - DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x0320)
            }

            Local0 = (DerefOf (RefOf (BF61)) - DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) - DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x0320)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF61)) - M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) - M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x0320)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF61)) - DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (BF61)) - DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x0320)
            }

            /* Conversion of the second operand */

            Store ((0x00 - DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x18, Local0, 0xFFFFFFFFFFFFFCDF)
            Store ((0x01 - DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x19, Local0, 0xFFFFFFFFFFFFFCE0)
            Store ((AUI5 - DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1A, Local0, 0xFFFFFFFFFFFFFCDF)
            Store ((AUI6 - DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFFFFFFFFFFFFFCE0)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) - DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x1C, Local0, 0xFFFFFFFFFFFFFCDF)
                Store ((DerefOf (RefOf (AUI6)) - DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFFFFFFFFFFFFFCE0)
            }

            Store ((DerefOf (PAUI [0x05]) - DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1E, Local0, 0xFFFFFFFFFFFFFCDF)
            Store ((DerefOf (PAUI [0x06]) - DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFFFFFFFFFFFFFCE0)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) - DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x20, Local0, 0xFFFFFFFFFFFFFCDF)
            Store ((M601 (0x01, 0x06) - DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x21, Local0, 0xFFFFFFFFFFFFFCE0)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) - DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x22, Local0, 0xFFFFFFFFFFFFFCDF)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) - DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x23, Local0, 0xFFFFFFFFFFFFFCE0)
            }

            Local0 = (0x00 - DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x24, Local0, 0xFFFFFFFFFFFFFCDF)
            Local0 = (0x01 - DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x25, Local0, 0xFFFFFFFFFFFFFCE0)
            Local0 = (AUI5 - DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x26, Local0, 0xFFFFFFFFFFFFFCDF)
            Local0 = (AUI6 - DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x27, Local0, 0xFFFFFFFFFFFFFCE0)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) - DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x28, Local0, 0xFFFFFFFFFFFFFCDF)
                Local0 = (DerefOf (RefOf (AUI6)) - DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x29, Local0, 0xFFFFFFFFFFFFFCE0)
            }

            Local0 = (DerefOf (PAUI [0x05]) - DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2A, Local0, 0xFFFFFFFFFFFFFCDF)
            Local0 = (DerefOf (PAUI [0x06]) - DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2B, Local0, 0xFFFFFFFFFFFFFCE0)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) - DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2C, Local0, 0xFFFFFFFFFFFFFCDF)
            Local0 = (M601 (0x01, 0x06) - DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2D, Local0, 0xFFFFFFFFFFFFFCE0)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) - DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x2E, Local0, 0xFFFFFFFFFFFFFCDF)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) - DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x2F, Local0, 0xFFFFFFFFFFFFFCE0)
            }
        }

        /* Subtract, 64-bit */

        Method (M05A, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) - 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) - 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xFE7CB391D650A283)
            Store ((DerefOf (RefOf (BF65)) - AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) - AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xFE7CB391D650A283)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) - DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (BF65)) - DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFE7CB391D650A283)
            }

            Store ((DerefOf (RefOf (BF65)) - DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) - DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFE7CB391D650A283)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) - M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) - M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFE7CB391D650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) - DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (BF65)) - DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFE7CB391D650A283)
            }

            Local0 = (DerefOf (RefOf (BF65)) - 0x00)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) - 0x01)
            M600 (Arg0, 0x0D, Local0, 0xFE7CB391D650A283)
            Local0 = (DerefOf (RefOf (BF65)) - AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) - AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xFE7CB391D650A283)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) - DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (BF65)) - DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xFE7CB391D650A283)
            }

            Local0 = (DerefOf (RefOf (BF65)) - DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) - DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xFE7CB391D650A283)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) - M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) - M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xFE7CB391D650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) - DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (BF65)) - DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFE7CB391D650A283)
            }

            /* Conversion of the second operand */

            Store ((0x00 - DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x18, Local0, 0x01834C6E29AF5D7C)
            Store ((0x01 - DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x19, Local0, 0x01834C6E29AF5D7D)
            Store ((AUI5 - DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x01834C6E29AF5D7C)
            Store ((AUI6 - DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1B, Local0, 0x01834C6E29AF5D7D)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) - DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x01834C6E29AF5D7C)
                Store ((DerefOf (RefOf (AUI6)) - DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1D, Local0, 0x01834C6E29AF5D7D)
            }

            Store ((DerefOf (PAUI [0x05]) - DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x01834C6E29AF5D7C)
            Store ((DerefOf (PAUI [0x06]) - DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1F, Local0, 0x01834C6E29AF5D7D)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) - DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x20, Local0, 0x01834C6E29AF5D7C)
            Store ((M601 (0x01, 0x06) - DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x21, Local0, 0x01834C6E29AF5D7D)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) - DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x22, Local0, 0x01834C6E29AF5D7C)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) - DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x23, Local0, 0x01834C6E29AF5D7D)
            }

            Local0 = (0x00 - DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x24, Local0, 0x01834C6E29AF5D7C)
            Local0 = (0x01 - DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x25, Local0, 0x01834C6E29AF5D7D)
            Local0 = (AUI5 - DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x26, Local0, 0x01834C6E29AF5D7C)
            Local0 = (AUI6 - DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x27, Local0, 0x01834C6E29AF5D7D)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) - DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x28, Local0, 0x01834C6E29AF5D7C)
                Local0 = (DerefOf (RefOf (AUI6)) - DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x29, Local0, 0x01834C6E29AF5D7D)
            }

            Local0 = (DerefOf (PAUI [0x05]) - DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2A, Local0, 0x01834C6E29AF5D7C)
            Local0 = (DerefOf (PAUI [0x06]) - DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2B, Local0, 0x01834C6E29AF5D7D)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) - DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2C, Local0, 0x01834C6E29AF5D7C)
            Local0 = (M601 (0x01, 0x06) - DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2D, Local0, 0x01834C6E29AF5D7D)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) - DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2E, Local0, 0x01834C6E29AF5D7C)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) - DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2F, Local0, 0x01834C6E29AF5D7D)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) - DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x30, Local0, 0x01834C6E29AF609D)
            Store ((DerefOf (RefOf (BF65)) - DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x31, Local0, 0xFE7CB391D6509F63)
            Local0 = (DerefOf (RefOf (BF61)) - DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x32, Local0, 0x01834C6E29AF609D)
            Local0 = (DerefOf (RefOf (BF65)) - DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x33, Local0, 0xFE7CB391D6509F63)
        }

        /* Subtract, 32-bit */

        Method (M05B, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) - 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) - 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xD650A283)
            Store ((DerefOf (RefOf (BF65)) - AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) - AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xD650A283)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) - DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (BF65)) - DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xD650A283)
            }

            Store ((DerefOf (RefOf (BF65)) - DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) - DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xD650A283)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) - M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) - M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xD650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) - DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (BF65)) - DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xD650A283)
            }

            Local0 = (DerefOf (RefOf (BF65)) - 0x00)
            M600 (Arg0, 0x0C, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) - 0x01)
            M600 (Arg0, 0x0D, Local0, 0xD650A283)
            Local0 = (DerefOf (RefOf (BF65)) - AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) - AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xD650A283)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) - DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (BF65)) - DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xD650A283)
            }

            Local0 = (DerefOf (RefOf (BF65)) - DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) - DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xD650A283)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) - M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) - M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xD650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) - DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (BF65)) - DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xD650A283)
            }

            /* Conversion of the second operand */

            Store ((0x00 - DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x18, Local0, 0x29AF5D7C)
            Store ((0x01 - DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x19, Local0, 0x29AF5D7D)
            Store ((AUI5 - DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x29AF5D7C)
            Store ((AUI6 - DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1B, Local0, 0x29AF5D7D)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) - DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x29AF5D7C)
                Store ((DerefOf (RefOf (AUI6)) - DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1D, Local0, 0x29AF5D7D)
            }

            Store ((DerefOf (PAUI [0x05]) - DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x29AF5D7C)
            Store ((DerefOf (PAUI [0x06]) - DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1F, Local0, 0x29AF5D7D)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) - DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x20, Local0, 0x29AF5D7C)
            Store ((M601 (0x01, 0x06) - DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x21, Local0, 0x29AF5D7D)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) - DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x22, Local0, 0x29AF5D7C)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) - DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x23, Local0, 0x29AF5D7D)
            }

            Local0 = (0x00 - DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x24, Local0, 0x29AF5D7C)
            Local0 = (0x01 - DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x25, Local0, 0x29AF5D7D)
            Local0 = (AUI5 - DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x26, Local0, 0x29AF5D7C)
            Local0 = (AUI6 - DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x27, Local0, 0x29AF5D7D)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) - DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x28, Local0, 0x29AF5D7C)
                Local0 = (DerefOf (RefOf (AUI6)) - DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x29, Local0, 0x29AF5D7D)
            }

            Local0 = (DerefOf (PAUI [0x05]) - DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2A, Local0, 0x29AF5D7C)
            Local0 = (DerefOf (PAUI [0x06]) - DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2B, Local0, 0x29AF5D7D)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) - DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2C, Local0, 0x29AF5D7C)
            Local0 = (M601 (0x01, 0x06) - DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2D, Local0, 0x29AF5D7D)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) - DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2E, Local0, 0x29AF5D7C)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) - DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2F, Local0, 0x29AF5D7D)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) - DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x30, Local0, 0x29AF609D)
            Store ((DerefOf (RefOf (BF65)) - DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x31, Local0, 0xD6509F63)
            Local0 = (DerefOf (RefOf (BF61)) - DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x32, Local0, 0x29AF609D)
            Local0 = (DerefOf (RefOf (BF65)) - DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x33, Local0, 0xD6509F63)
        }

        /* XOr, common 32-bit/64-bit test */

        Method (M05C, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF61)) ^ 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) ^ 0xFFFFFFFFFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0xFFFFFFFFFFFFFCDE)
            Store ((DerefOf (RefOf (BF61)) ^ AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) ^ AUIJ), Local0)
            M600 (Arg0, 0x03, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF61)) ^ DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((DerefOf (RefOf (BF61)) ^ DerefOf (RefOf (AUIJ))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Store ((DerefOf (RefOf (BF61)) ^ DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) ^ DerefOf (PAUI [0x13])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF61)) ^ M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((DerefOf (RefOf (BF61)) ^ M601 (0x01, 0x13)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF61)) ^ DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((DerefOf (RefOf (BF61)) ^ DerefOf (M602 (0x01, 0x13, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Local0 = (DerefOf (RefOf (BF61)) ^ 0x00)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) ^ 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = (DerefOf (RefOf (BF61)) ^ AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) ^ AUIJ) /* \AUIJ */
            M600 (Arg0, 0x0F, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF61)) ^ DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (BF61)) ^ DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x11, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Local0 = (DerefOf (RefOf (BF61)) ^ DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) ^ DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x13, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF61)) ^ M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (DerefOf (RefOf (BF61)) ^ M601 (0x01, 0x13))
            M600 (Arg0, 0x15, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF61)) ^ DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (BF61)) ^ DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            /* Conversion of the second operand */

            Store ((0x00 ^ DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x18, Local0, 0x0321)
            Store ((0xFFFFFFFFFFFFFFFF ^ DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x19, Local0, 0xFFFFFFFFFFFFFCDE)
            Store ((AUI5 ^ DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1A, Local0, 0x0321)
            Store ((AUIJ ^ DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) ^ DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x1C, Local0, 0x0321)
                Store ((DerefOf (RefOf (AUIJ)) ^ DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Store ((DerefOf (PAUI [0x05]) ^ DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1E, Local0, 0x0321)
            Store ((DerefOf (PAUI [0x13]) ^ DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) ^ DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x20, Local0, 0x0321)
            Store ((M601 (0x01, 0x13) ^ DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x21, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) ^ DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x22, Local0, 0x0321)
                Store ((DerefOf (M602 (0x01, 0x13, 0x01)) ^ DerefOf (RefOf (BF61))), Local0)
                M600 (Arg0, 0x23, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Local0 = (0x00 ^ DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x24, Local0, 0x0321)
            Local0 = (0xFFFFFFFFFFFFFFFF ^ DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x25, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = (AUI5 ^ DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x26, Local0, 0x0321)
            Local0 = (AUIJ ^ DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x27, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) ^ DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x28, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (AUIJ)) ^ DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x29, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Local0 = (DerefOf (PAUI [0x05]) ^ DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2A, Local0, 0x0321)
            Local0 = (DerefOf (PAUI [0x13]) ^ DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2B, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) ^ DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2C, Local0, 0x0321)
            Local0 = (M601 (0x01, 0x13) ^ DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2D, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) ^ DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x2E, Local0, 0x0321)
                Local0 = (DerefOf (M602 (0x01, 0x13, 0x01)) ^ DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x2F, Local0, 0xFFFFFFFFFFFFFCDE)
            }
        }

        /* XOr, 64-bit */

        Method (M05D, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) ^ 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) ^ 0xFFFFFFFFFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0x01834C6E29AF5D7B)
            Store ((DerefOf (RefOf (BF65)) ^ AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) ^ AUIJ), Local0)
            M600 (Arg0, 0x03, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) ^ DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (BF65)) ^ DerefOf (RefOf (AUIJ))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01834C6E29AF5D7B)
            }

            Store ((DerefOf (RefOf (BF65)) ^ DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) ^ DerefOf (PAUI [0x13])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) ^ M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (RefOf (BF65)) ^ M601 (0x01, 0x13)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) ^ DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (BF65)) ^ DerefOf (M602 (0x01, 0x13, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01834C6E29AF5D7B)
            }

            Local0 = (DerefOf (RefOf (BF65)) ^ 0x00)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) ^ 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0x01834C6E29AF5D7B)
            Local0 = (DerefOf (RefOf (BF65)) ^ AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) ^ AUIJ) /* \AUIJ */
            M600 (Arg0, 0x0F, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) ^ DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (BF65)) ^ DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x11, Local0, 0x01834C6E29AF5D7B)
            }

            Local0 = (DerefOf (RefOf (BF65)) ^ DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) ^ DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x13, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) ^ M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (RefOf (BF65)) ^ M601 (0x01, 0x13))
            M600 (Arg0, 0x15, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) ^ DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (BF65)) ^ DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x01834C6E29AF5D7B)
            }

            /* Conversion of the second operand */

            Store ((0x00 ^ DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x18, Local0, 0xFE7CB391D650A284)
            Store ((0xFFFFFFFFFFFFFFFF ^ DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x19, Local0, 0x01834C6E29AF5D7B)
            Store ((AUI5 ^ DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1A, Local0, 0xFE7CB391D650A284)
            Store ((AUIJ ^ DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1B, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) ^ DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1C, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (AUIJ)) ^ DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1D, Local0, 0x01834C6E29AF5D7B)
            }

            Store ((DerefOf (PAUI [0x05]) ^ DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1E, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (PAUI [0x13]) ^ DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1F, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) ^ DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x20, Local0, 0xFE7CB391D650A284)
            Store ((M601 (0x01, 0x13) ^ DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x21, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) ^ DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x22, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (M602 (0x01, 0x13, 0x01)) ^ DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x23, Local0, 0x01834C6E29AF5D7B)
            }

            Local0 = (0x00 ^ DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x24, Local0, 0xFE7CB391D650A284)
            Local0 = (0xFFFFFFFFFFFFFFFF ^ DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x25, Local0, 0x01834C6E29AF5D7B)
            Local0 = (AUI5 ^ DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x26, Local0, 0xFE7CB391D650A284)
            Local0 = (AUIJ ^ DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x27, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) ^ DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x28, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (AUIJ)) ^ DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x29, Local0, 0x01834C6E29AF5D7B)
            }

            Local0 = (DerefOf (PAUI [0x05]) ^ DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2A, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (PAUI [0x13]) ^ DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2B, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) ^ DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2C, Local0, 0xFE7CB391D650A284)
            Local0 = (M601 (0x01, 0x13) ^ DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2D, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) ^ DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2E, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (M602 (0x01, 0x13, 0x01)) ^ DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2F, Local0, 0x01834C6E29AF5D7B)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) ^ DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x30, Local0, 0xFE7CB391D650A1A5)
            Store ((DerefOf (RefOf (BF65)) ^ DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x31, Local0, 0xFE7CB391D650A1A5)
            Local0 = (DerefOf (RefOf (BF61)) ^ DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x32, Local0, 0xFE7CB391D650A1A5)
            Local0 = (DerefOf (RefOf (BF65)) ^ DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x33, Local0, 0xFE7CB391D650A1A5)
        }

        /* XOr, 32-bit */

        Method (M05E, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Store ((DerefOf (RefOf (BF65)) ^ 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) ^ 0xFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0x29AF5D7B)
            Store ((DerefOf (RefOf (BF65)) ^ AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) ^ AUII), Local0)
            M600 (Arg0, 0x03, Local0, 0x29AF5D7B)
            If (Y078)
            {
                Store ((DerefOf (RefOf (BF65)) ^ DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (BF65)) ^ DerefOf (RefOf (AUII))), Local0)
                M600 (Arg0, 0x05, Local0, 0x29AF5D7B)
            }

            Store ((DerefOf (RefOf (BF65)) ^ DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) ^ DerefOf (PAUI [0x12])), Local0)
            M600 (Arg0, 0x07, Local0, 0x29AF5D7B)
            /* Method returns Integer */

            Store ((DerefOf (RefOf (BF65)) ^ M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xD650A284)
            Store ((DerefOf (RefOf (BF65)) ^ M601 (0x01, 0x12)), Local0)
            M600 (Arg0, 0x09, Local0, 0x29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (RefOf (BF65)) ^ DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (BF65)) ^ DerefOf (M602 (0x01, 0x12, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x29AF5D7B)
            }

            Local0 = (DerefOf (RefOf (BF65)) ^ 0x00)
            M600 (Arg0, 0x0C, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) ^ 0xFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0x29AF5D7B)
            Local0 = (DerefOf (RefOf (BF65)) ^ AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) ^ AUII) /* \AUII */
            M600 (Arg0, 0x0F, Local0, 0x29AF5D7B)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) ^ DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (BF65)) ^ DerefOf (RefOf (AUII)))
                M600 (Arg0, 0x11, Local0, 0x29AF5D7B)
            }

            Local0 = (DerefOf (RefOf (BF65)) ^ DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) ^ DerefOf (PAUI [0x12]))
            M600 (Arg0, 0x13, Local0, 0x29AF5D7B)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) ^ M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xD650A284)
            Local0 = (DerefOf (RefOf (BF65)) ^ M601 (0x01, 0x12))
            M600 (Arg0, 0x15, Local0, 0x29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) ^ DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (BF65)) ^ DerefOf (M602 (0x01, 0x12, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x29AF5D7B)
            }

            /* Conversion of the second operand */

            Store ((0x00 ^ DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x18, Local0, 0xD650A284)
            Store ((0xFFFFFFFF ^ DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x19, Local0, 0x29AF5D7B)
            Store ((AUI5 ^ DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1A, Local0, 0xD650A284)
            Store ((AUII ^ DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1B, Local0, 0x29AF5D7B)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) ^ DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1C, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (AUII)) ^ DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x1D, Local0, 0x29AF5D7B)
            }

            Store ((DerefOf (PAUI [0x05]) ^ DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1E, Local0, 0xD650A284)
            Store ((DerefOf (PAUI [0x12]) ^ DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x1F, Local0, 0x29AF5D7B)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) ^ DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x20, Local0, 0xD650A284)
            Store ((M601 (0x01, 0x12) ^ DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x21, Local0, 0x29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) ^ DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x22, Local0, 0xD650A284)
                Store ((DerefOf (M602 (0x01, 0x12, 0x01)) ^ DerefOf (RefOf (BF65))), Local0)
                M600 (Arg0, 0x23, Local0, 0x29AF5D7B)
            }

            Local0 = (0x00 ^ DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x24, Local0, 0xD650A284)
            Local0 = (0xFFFFFFFF ^ DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x25, Local0, 0x29AF5D7B)
            Local0 = (AUI5 ^ DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x26, Local0, 0xD650A284)
            Local0 = (AUII ^ DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x27, Local0, 0x29AF5D7B)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) ^ DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x28, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (AUII)) ^ DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x29, Local0, 0x29AF5D7B)
            }

            Local0 = (DerefOf (PAUI [0x05]) ^ DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2A, Local0, 0xD650A284)
            Local0 = (DerefOf (PAUI [0x12]) ^ DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2B, Local0, 0x29AF5D7B)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) ^ DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2C, Local0, 0xD650A284)
            Local0 = (M601 (0x01, 0x12) ^ DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2D, Local0, 0x29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) ^ DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2E, Local0, 0xD650A284)
                Local0 = (DerefOf (M602 (0x01, 0x12, 0x01)) ^ DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2F, Local0, 0x29AF5D7B)
            }

            /* Conversion of the both operands */

            Store ((DerefOf (RefOf (BF61)) ^ DerefOf (RefOf (BF65))), Local0)
            M600 (Arg0, 0x30, Local0, 0xD650A1A5)
            Store ((DerefOf (RefOf (BF65)) ^ DerefOf (RefOf (BF61))), Local0)
            M600 (Arg0, 0x31, Local0, 0xD650A1A5)
            Local0 = (DerefOf (RefOf (BF61)) ^ DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x32, Local0, 0xD650A1A5)
            Local0 = (DerefOf (RefOf (BF65)) ^ DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x33, Local0, 0xD650A1A5)
        }

        /* Add, And, Divide, Mod, Multiply, NAnd, NOr, Or, */
        /* ShiftLeft, ShiftRight, Subtract, Xor */
        Method (M64N, 1, NotSerialized)
        {
            /* Add */

            Concatenate (Arg0, "-m03b", Local0)
            SRMT (Local0)
            M03B (Local0)
            Concatenate (Arg0, "-m03c", Local0)
            SRMT (Local0)
            M03C (Local0)
            /* And */

            Concatenate (Arg0, "-m03e", Local0)
            SRMT (Local0)
            M03E (Local0)
            Concatenate (Arg0, "-m03f", Local0)
            SRMT (Local0)
            M03F (Local0)
            /* Divide */

            Concatenate (Arg0, "-m041", Local0)
            SRMT (Local0)
            M041 (Local0)
            Concatenate (Arg0, "-m042", Local0)
            SRMT (Local0)
            M042 (Local0)
            /* Mod */

            Concatenate (Arg0, "-m044", Local0)
            SRMT (Local0)
            M044 (Local0)
            Concatenate (Arg0, "-m045", Local0)
            SRMT (Local0)
            M045 (Local0)
            /* Multiply */

            Concatenate (Arg0, "-m047", Local0)
            SRMT (Local0)
            M047 (Local0)
            Concatenate (Arg0, "-m048", Local0)
            SRMT (Local0)
            M048 (Local0)
            /* NAnd */

            Concatenate (Arg0, "-m04a", Local0)
            SRMT (Local0)
            M04A (Local0)
            Concatenate (Arg0, "-m04b", Local0)
            SRMT (Local0)
            M04B (Local0)
            /* NOr */

            Concatenate (Arg0, "-m04d", Local0)
            SRMT (Local0)
            M04D (Local0)
            Concatenate (Arg0, "-m04e", Local0)
            SRMT (Local0)
            M04E (Local0)
            /* Or */

            Concatenate (Arg0, "-m050", Local0)
            SRMT (Local0)
            M050 (Local0)
            Concatenate (Arg0, "-m051", Local0)
            SRMT (Local0)
            M051 (Local0)
            /* ShiftLeft */

            Concatenate (Arg0, "-m053", Local0)
            SRMT (Local0)
            M053 (Local0)
            Concatenate (Arg0, "-m054", Local0)
            SRMT (Local0)
            M054 (Local0)
            /* ShiftRight */

            Concatenate (Arg0, "-m056", Local0)
            SRMT (Local0)
            M056 (Local0)
            Concatenate (Arg0, "-m057", Local0)
            SRMT (Local0)
            M057 (Local0)
            /* Subtract */

            Concatenate (Arg0, "-m059", Local0)
            SRMT (Local0)
            M059 (Local0)
            Concatenate (Arg0, "-m05a", Local0)
            SRMT (Local0)
            M05A (Local0)
            /* XOr */

            Concatenate (Arg0, "-m05c", Local0)
            SRMT (Local0)
            M05C (Local0)
            Concatenate (Arg0, "-m05d", Local0)
            SRMT (Local0)
            M05D (Local0)
        }

        Method (M32N, 1, NotSerialized)
        {
            /* Add */

            Concatenate (Arg0, "-m03b", Local0)
            SRMT (Local0)
            M03B (Local0)
            Concatenate (Arg0, "-m03d", Local0)
            SRMT (Local0)
            M03D (Local0)
            /* And */

            Concatenate (Arg0, "-m03e", Local0)
            SRMT (Local0)
            M03E (Local0)
            Concatenate (Arg0, "-m040", Local0)
            SRMT (Local0)
            M040 (Local0)
            /* Divide */

            Concatenate (Arg0, "-m041", Local0)
            SRMT (Local0)
            M041 (Local0)
            Concatenate (Arg0, "-m043", Local0)
            SRMT (Local0)
            M043 (Local0)
            /* Mod */

            Concatenate (Arg0, "-m044", Local0)
            SRMT (Local0)
            M044 (Local0)
            Concatenate (Arg0, "-m046", Local0)
            SRMT (Local0)
            M046 (Local0)
            /* Multiply */

            Concatenate (Arg0, "-m047", Local0)
            SRMT (Local0)
            M047 (Local0)
            Concatenate (Arg0, "-m049", Local0)
            SRMT (Local0)
            M049 (Local0)
            /* NAnd */

            Concatenate (Arg0, "-m04a", Local0)
            SRMT (Local0)
            If (Y119)
            {
                M04A (Local0)
            }
            Else
            {
                BLCK ()
            }

            Concatenate (Arg0, "-m04c", Local0)
            SRMT (Local0)
            M04C (Local0)
            /* NOr */

            Concatenate (Arg0, "-m04d", Local0)
            SRMT (Local0)
            If (Y119)
            {
                M04D (Local0)
            }
            Else
            {
                BLCK ()
            }

            Concatenate (Arg0, "-m04f", Local0)
            SRMT (Local0)
            M04F (Local0)
            /* Or */

            Concatenate (Arg0, "-m050", Local0)
            SRMT (Local0)
            If (Y119)
            {
                M050 (Local0)
            }
            Else
            {
                BLCK ()
            }

            Concatenate (Arg0, "-m052", Local0)
            SRMT (Local0)
            M052 (Local0)
            /* ShiftLeft */

            Concatenate (Arg0, "-m053", Local0)
            SRMT (Local0)
            M053 (Local0)
            Concatenate (Arg0, "-m055", Local0)
            SRMT (Local0)
            M055 (Local0)
            /* ShiftRight */

            Concatenate (Arg0, "-m056", Local0)
            SRMT (Local0)
            M056 (Local0)
            Concatenate (Arg0, "-m058", Local0)
            SRMT (Local0)
            M058 (Local0)
            /* Subtract */

            Concatenate (Arg0, "-m059", Local0)
            SRMT (Local0)
            If (Y119)
            {
                M059 (Local0)
            }
            Else
            {
                BLCK ()
            }

            Concatenate (Arg0, "-m05b", Local0)
            SRMT (Local0)
            M05B (Local0)
            /* XOr */

            Concatenate (Arg0, "-m05c", Local0)
            SRMT (Local0)
            If (Y119)
            {
                M05C (Local0)
            }
            Else
            {
                BLCK ()
            }

            Concatenate (Arg0, "-m05e", Local0)
            SRMT (Local0)
            M05E (Local0)
        }

        /* Buffer Field to Integer conversion of each Buffer operand */
        /* of the 2-parameter Logical Integer operators LAnd and LOr */
        /* LAnd, common 32-bit/64-bit test */
        Method (M05F, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Local0 = (DerefOf (RefOf (BF61)) && 0x00)
            M600 (Arg0, 0x00, Local0, Zero)
            Local0 = (DerefOf (RefOf (BF61)) && 0x01)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = (DerefOf (RefOf (BF61)) && AUI5)
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (DerefOf (RefOf (BF61)) && AUI6)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF61)) && DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, Zero)
                Local0 = (DerefOf (RefOf (BF61)) && DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = (DerefOf (RefOf (BF61)) && DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, Zero)
            Local0 = (DerefOf (RefOf (BF61)) && DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF61)) && M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, Zero)
            Local0 = (DerefOf (RefOf (BF61)) && M601 (0x01, 0x06))
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF61)) && DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, Zero)
                Local0 = (DerefOf (RefOf (BF61)) && DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x0B, Local0, Ones)
            }

            /* Conversion of the second operand */

            Local0 = (0x00 && DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = (0x01 && DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (AUI5 && DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = (AUI6 && DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x0F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) && DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUI6)) && DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x11, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x05]) && DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x06]) && DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x13, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) && DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (M601 (0x01, 0x06) && DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) && DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x16, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) && DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x17, Local0, Ones)
            }
        }

        /* LAnd, 64-bit */

        Method (M060, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Local0 = (DerefOf (RefOf (BF65)) && 0x00)
            M600 (Arg0, 0x00, Local0, Zero)
            Local0 = (DerefOf (RefOf (BF65)) && 0x01)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = (DerefOf (RefOf (BF65)) && AUI5)
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (DerefOf (RefOf (BF65)) && AUI6)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) && DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, Zero)
                Local0 = (DerefOf (RefOf (BF65)) && DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = (DerefOf (RefOf (BF65)) && DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, Zero)
            Local0 = (DerefOf (RefOf (BF65)) && DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) && M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, Zero)
            Local0 = (DerefOf (RefOf (BF65)) && M601 (0x01, 0x06))
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) && DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, Zero)
                Local0 = (DerefOf (RefOf (BF65)) && DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x0B, Local0, Ones)
            }

            /* Conversion of the second operand */

            Local0 = (0x00 && DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = (0x01 && DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (AUI5 && DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = (AUI6 && DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) && DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUI6)) && DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x11, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x05]) && DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x06]) && DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x13, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) && DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (M601 (0x01, 0x06) && DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) && DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x16, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) && DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x17, Local0, Ones)
            }

            /* Conversion of the both operands */

            Local0 = (DerefOf (RefOf (BF61)) && DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x18, Local0, Ones)
            Local0 = (DerefOf (RefOf (BF65)) && DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x19, Local0, Ones)
        }

        /* LAnd, 32-bit */

        Method (M061, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Local0 = (DerefOf (RefOf (BF65)) && 0x00)
            M600 (Arg0, 0x00, Local0, Zero)
            Local0 = (DerefOf (RefOf (BF65)) && 0x01)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = (DerefOf (RefOf (BF65)) && AUI5)
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (DerefOf (RefOf (BF65)) && AUI6)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) && DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, Zero)
                Local0 = (DerefOf (RefOf (BF65)) && DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = (DerefOf (RefOf (BF65)) && DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, Zero)
            Local0 = (DerefOf (RefOf (BF65)) && DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) && M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, Zero)
            Local0 = (DerefOf (RefOf (BF65)) && M601 (0x01, 0x06))
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) && DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, Zero)
                Local0 = (DerefOf (RefOf (BF65)) && DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x0B, Local0, Ones)
            }

            /* Conversion of the second operand */

            Local0 = (0x00 && DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = (0x01 && DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (AUI5 && DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = (AUI6 && DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) && DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUI6)) && DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x11, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x05]) && DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x06]) && DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x13, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) && DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (M601 (0x01, 0x06) && DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) && DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x16, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) && DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x17, Local0, Ones)
            }

            /* Conversion of the both operands */

            Local0 = (DerefOf (RefOf (BF61)) && DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x18, Local0, Ones)
            Local0 = (DerefOf (RefOf (BF65)) && DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x19, Local0, Ones)
        }

        /* Lor, common 32-bit/64-bit test */

        Method (M062, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Local0 = (DerefOf (RefOf (BF76)) || 0x00)
            M600 (Arg0, 0x00, Local0, Zero)
            Local0 = (DerefOf (RefOf (BF76)) || 0x01)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = (DerefOf (RefOf (BF76)) || AUI5)
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (DerefOf (RefOf (BF76)) || AUI6)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF76)) || DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, Zero)
                Local0 = (DerefOf (RefOf (BF76)) || DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = (DerefOf (RefOf (BF76)) || DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, Zero)
            Local0 = (DerefOf (RefOf (BF76)) || DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF76)) || M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, Zero)
            Local0 = (DerefOf (RefOf (BF76)) || M601 (0x01, 0x06))
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF76)) || DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, Zero)
                Local0 = (DerefOf (RefOf (BF76)) || DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x0B, Local0, Ones)
            }

            /* Conversion of the second operand */

            Local0 = (0x00 || DerefOf (RefOf (BF76)))
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = (0x01 || DerefOf (RefOf (BF76)))
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (AUI5 || DerefOf (RefOf (BF76)))
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = (AUI6 || DerefOf (RefOf (BF76)))
            M600 (Arg0, 0x0F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) || DerefOf (RefOf (BF76)))
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUI6)) || DerefOf (RefOf (BF76)))
                M600 (Arg0, 0x11, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x05]) || DerefOf (RefOf (BF76)))
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x06]) || DerefOf (RefOf (BF76)))
            M600 (Arg0, 0x13, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) || DerefOf (RefOf (BF76)))
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (M601 (0x01, 0x06) || DerefOf (RefOf (BF76)))
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) || DerefOf (RefOf (BF76)))
                M600 (Arg0, 0x16, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) || DerefOf (RefOf (BF76)))
                M600 (Arg0, 0x17, Local0, Ones)
            }
        }

        /* Lor, 64-bit */

        Method (M063, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Local0 = (DerefOf (RefOf (BF65)) || 0x00)
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (DerefOf (RefOf (BF65)) || 0x01)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = (DerefOf (RefOf (BF65)) || AUI5)
            M600 (Arg0, 0x02, Local0, Ones)
            Local0 = (DerefOf (RefOf (BF65)) || AUI6)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) || DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, Ones)
                Local0 = (DerefOf (RefOf (BF65)) || DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = (DerefOf (RefOf (BF65)) || DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, Ones)
            Local0 = (DerefOf (RefOf (BF65)) || DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) || M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, Ones)
            Local0 = (DerefOf (RefOf (BF65)) || M601 (0x01, 0x06))
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) || DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, Ones)
                Local0 = (DerefOf (RefOf (BF65)) || DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x0B, Local0, Ones)
            }

            /* Conversion of the second operand */

            Local0 = (0x00 || DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0C, Local0, Ones)
            Local0 = (0x01 || DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (AUI5 || DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0E, Local0, Ones)
            Local0 = (AUI6 || DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) || DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x10, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUI6)) || DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x11, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x05]) || DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x12, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x06]) || DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x13, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) || DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x14, Local0, Ones)
            Local0 = (M601 (0x01, 0x06) || DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) || DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x16, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) || DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x17, Local0, Ones)
            }

            /* Conversion of the both operands */

            Local0 = (DerefOf (RefOf (BF76)) || DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x18, Local0, Ones)
            Local0 = (DerefOf (RefOf (BF65)) || DerefOf (RefOf (BF76)))
            M600 (Arg0, 0x19, Local0, Ones)
        }

        /* Lor, 32-bit */

        Method (M064, 1, NotSerialized)
        {
            /* Conversion of the first operand */

            Local0 = (DerefOf (RefOf (BF65)) || 0x00)
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (DerefOf (RefOf (BF65)) || 0x01)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = (DerefOf (RefOf (BF65)) || AUI5)
            M600 (Arg0, 0x02, Local0, Ones)
            Local0 = (DerefOf (RefOf (BF65)) || AUI6)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (BF65)) || DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, Ones)
                Local0 = (DerefOf (RefOf (BF65)) || DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = (DerefOf (RefOf (BF65)) || DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, Ones)
            Local0 = (DerefOf (RefOf (BF65)) || DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Integer */

            Local0 = (DerefOf (RefOf (BF65)) || M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, Ones)
            Local0 = (DerefOf (RefOf (BF65)) || M601 (0x01, 0x06))
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (RefOf (BF65)) || DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, Ones)
                Local0 = (DerefOf (RefOf (BF65)) || DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x0B, Local0, Ones)
            }

            /* Conversion of the second operand */

            Local0 = (0x00 || DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0C, Local0, Ones)
            Local0 = (0x01 || DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (AUI5 || DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0E, Local0, Ones)
            Local0 = (AUI6 || DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) || DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x10, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUI6)) || DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x11, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x05]) || DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x12, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x06]) || DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x13, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) || DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x14, Local0, Ones)
            Local0 = (M601 (0x01, 0x06) || DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) || DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x16, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) || DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x17, Local0, Ones)
            }

            /* Conversion of the both operands */

            Local0 = (DerefOf (RefOf (BF76)) || DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x18, Local0, Ones)
            Local0 = (DerefOf (RefOf (BF65)) || DerefOf (RefOf (BF76)))
            M600 (Arg0, 0x19, Local0, Ones)
        }

        Method (M64O, 1, NotSerialized)
        {
            /* LAnd */

            Concatenate (Arg0, "-m05f", Local0)
            SRMT (Local0)
            M05F (Local0)
            Concatenate (Arg0, "-m060", Local0)
            SRMT (Local0)
            M060 (Local0)
            /* LOr */

            Concatenate (Arg0, "-m062", Local0)
            SRMT (Local0)
            M062 (Local0)
            Concatenate (Arg0, "-m063", Local0)
            SRMT (Local0)
            M063 (Local0)
        }

        Method (M32O, 1, NotSerialized)
        {
            /* LAnd */

            Concatenate (Arg0, "-m05f", Local0)
            SRMT (Local0)
            M05F (Local0)
            Concatenate (Arg0, "-m061", Local0)
            SRMT (Local0)
            M061 (Local0)
            /* LOr */

            Concatenate (Arg0, "-m062", Local0)
            SRMT (Local0)
            M062 (Local0)
            Concatenate (Arg0, "-m064", Local0)
            SRMT (Local0)
            M064 (Local0)
        }

        /* Buffer Field to Integer conversion of the Buffer Field second operand */
        /* of Logical operators when the first operand is evaluated as Integer */
        /* (LEqual, LGreater, LGreaterEqual, LLess, LLessEqual, LNotEqual) */
        Method (M64P, 1, NotSerialized)
        {
            /* LEqual */

            Local0 = (0xFE7CB391D650A284 == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (0xFE7CB391D650A285 == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x01, Local0, Zero)
            Local0 = (0xFE7CB391D650A283 == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (AUI4 == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x03, Local0, Ones)
            Local0 = (AUID == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x04, Local0, Zero)
            Local0 = (AUIF == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x05, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI4)) == DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x06, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUID)) == DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x07, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIF)) == DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x08, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x04]) == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x09, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0D]) == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0A, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0F]) == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0B, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x04) == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0C, Local0, Ones)
            Local0 = (M601 (0x01, 0x0D) == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0D, Local0, Zero)
            Local0 = (M601 (0x01, 0x0F) == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0E, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) == DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x0F, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) == DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) == DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x11, Local0, Zero)
            }

            /* LGreater */

            Local0 = (0xFE7CB391D650A284 > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (0xFE7CB391D650A285 > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x13, Local0, Ones)
            Local0 = (0xFE7CB391D650A283 > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (AUI4 > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x15, Local0, Zero)
            Local0 = (AUID > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x16, Local0, Ones)
            Local0 = (AUIF > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x17, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI4)) > DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x18, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUID)) > DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x19, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIF)) > DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x1A, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x04]) > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1B, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0D]) > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1C, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0F]) > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1D, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x04) > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1E, Local0, Zero)
            Local0 = (M601 (0x01, 0x0D) > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1F, Local0, Ones)
            Local0 = (M601 (0x01, 0x0F) > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x20, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) > DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x21, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) > DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x22, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) > DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x23, Local0, Zero)
            }

            /* LGreaterEqual */

            Local0 = (0xFE7CB391D650A284 >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x24, Local0, Ones)
            Local0 = (0xFE7CB391D650A285 >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x25, Local0, Ones)
            Local0 = (0xFE7CB391D650A283 >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x26, Local0, Zero)
            Local0 = (AUI4 >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x27, Local0, Ones)
            Local0 = (AUID >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x28, Local0, Ones)
            Local0 = (AUIF >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x29, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI4)) >= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2A, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUID)) >= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2B, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIF)) >= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2C, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x04]) >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2D, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0D]) >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2E, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0F]) >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2F, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x04) >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x30, Local0, Ones)
            Local0 = (M601 (0x01, 0x0D) >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x31, Local0, Ones)
            Local0 = (M601 (0x01, 0x0F) >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x32, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) >= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x33, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) >= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x34, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) >= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x35, Local0, Zero)
            }

            /* LLess */

            Local0 = (0xFE7CB391D650A284 < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x36, Local0, Zero)
            Local0 = (0xFE7CB391D650A285 < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x37, Local0, Zero)
            Local0 = (0xFE7CB391D650A283 < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x38, Local0, Ones)
            Local0 = (AUI4 < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x39, Local0, Zero)
            Local0 = (AUID < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x3A, Local0, Zero)
            Local0 = (AUIF < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x3B, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI4)) < DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x3C, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUID)) < DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x3D, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIF)) < DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x3E, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x04]) < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x3F, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0D]) < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x40, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0F]) < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x41, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x04) < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x42, Local0, Zero)
            Local0 = (M601 (0x01, 0x0D) < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x43, Local0, Zero)
            Local0 = (M601 (0x01, 0x0F) < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x44, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) < DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x45, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) < DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x46, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) < DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x47, Local0, Ones)
            }

            /* LLessEqual */

            Local0 = (0xFE7CB391D650A284 <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x48, Local0, Ones)
            Local0 = (0xFE7CB391D650A285 <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x49, Local0, Zero)
            Local0 = (0xFE7CB391D650A283 <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x4A, Local0, Ones)
            Local0 = (AUI4 <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x4B, Local0, Ones)
            Local0 = (AUID <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x4C, Local0, Zero)
            Local0 = (AUIF <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x4D, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI4)) <= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x4E, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUID)) <= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x4F, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIF)) <= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x50, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x04]) <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x51, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0D]) <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x52, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0F]) <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x53, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x04) <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x54, Local0, Ones)
            Local0 = (M601 (0x01, 0x0D) <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x55, Local0, Zero)
            Local0 = (M601 (0x01, 0x0F) <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x56, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) <= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x57, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) <= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x58, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) <= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x59, Local0, Ones)
            }

            /* LNotEqual */

            Local0 = (0xFE7CB391D650A284 != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x5A, Local0, Zero)
            Local0 = (0xFE7CB391D650A285 != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x5B, Local0, Ones)
            Local0 = (0xFE7CB391D650A283 != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x5C, Local0, Ones)
            Local0 = (AUI4 != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x5D, Local0, Zero)
            Local0 = (AUID != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x5E, Local0, Ones)
            Local0 = (AUIF != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x5F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI4)) != DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x60, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUID)) != DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x61, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIF)) != DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x62, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x04]) != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x63, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0D]) != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x64, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0F]) != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x65, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x04) != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x66, Local0, Zero)
            Local0 = (M601 (0x01, 0x0D) != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x67, Local0, Ones)
            Local0 = (M601 (0x01, 0x0F) != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x68, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) != DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x69, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) != DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x6A, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) != DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x6B, Local0, Ones)
            }
        }

        Method (M32P, 1, NotSerialized)
        {
            /* LEqual */

            Local0 = (0xD650A284 == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (0xD650A285 == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x01, Local0, Zero)
            Local0 = (0xD650A283 == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (AUIK == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x03, Local0, Ones)
            Local0 = (AUIL == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x04, Local0, Zero)
            Local0 = (AUIM == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x05, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUIK)) == DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x06, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIL)) == DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x07, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIM)) == DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x08, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x14]) == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x09, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x15]) == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0A, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x16]) == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0B, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x14) == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0C, Local0, Ones)
            Local0 = (M601 (0x01, 0x15) == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0D, Local0, Zero)
            Local0 = (M601 (0x01, 0x16) == DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x0E, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x14, 0x01)) == DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x0F, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x15, 0x01)) == DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x16, 0x01)) == DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x11, Local0, Zero)
            }

            /* LGreater */

            Local0 = (0xD650A284 > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (0xD650A285 > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x13, Local0, Ones)
            Local0 = (0xD650A283 > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (AUIK > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x15, Local0, Zero)
            Local0 = (AUIL > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x16, Local0, Ones)
            Local0 = (AUIM > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x17, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUIK)) > DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x18, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIL)) > DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x19, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIM)) > DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x1A, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x14]) > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1B, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x15]) > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1C, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x16]) > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1D, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x14) > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1E, Local0, Zero)
            Local0 = (M601 (0x01, 0x15) > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1F, Local0, Ones)
            Local0 = (M601 (0x01, 0x16) > DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x20, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x14, 0x01)) > DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x21, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x15, 0x01)) > DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x22, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x16, 0x01)) > DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x23, Local0, Zero)
            }

            /* LGreaterEqual */

            Local0 = (0xD650A284 >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x24, Local0, Ones)
            Local0 = (0xD650A285 >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x25, Local0, Ones)
            Local0 = (0xD650A283 >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x26, Local0, Zero)
            Local0 = (AUIK >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x27, Local0, Ones)
            Local0 = (AUIL >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x28, Local0, Ones)
            Local0 = (AUIM >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x29, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUIK)) >= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2A, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIL)) >= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2B, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIM)) >= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x2C, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x14]) >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2D, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x15]) >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2E, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x16]) >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x2F, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x14) >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x30, Local0, Ones)
            Local0 = (M601 (0x01, 0x15) >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x31, Local0, Ones)
            Local0 = (M601 (0x01, 0x16) >= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x32, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x14, 0x01)) >= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x33, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x15, 0x01)) >= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x34, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x16, 0x01)) >= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x35, Local0, Zero)
            }

            /* LLess */

            Local0 = (0xD650A284 < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x36, Local0, Zero)
            Local0 = (0xD650A285 < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x37, Local0, Zero)
            Local0 = (0xD650A283 < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x38, Local0, Ones)
            Local0 = (AUIK < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x39, Local0, Zero)
            Local0 = (AUIL < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x3A, Local0, Zero)
            Local0 = (AUIM < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x3B, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUIK)) < DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x3C, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIL)) < DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x3D, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIM)) < DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x3E, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x14]) < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x3F, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x15]) < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x40, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x16]) < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x41, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x14) < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x42, Local0, Zero)
            Local0 = (M601 (0x01, 0x15) < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x43, Local0, Zero)
            Local0 = (M601 (0x01, 0x16) < DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x44, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x14, 0x01)) < DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x45, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x15, 0x01)) < DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x46, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x16, 0x01)) < DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x47, Local0, Ones)
            }

            /* LLessEqual */

            Local0 = (0xD650A284 <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x48, Local0, Ones)
            Local0 = (0xD650A285 <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x49, Local0, Zero)
            Local0 = (0xD650A283 <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x4A, Local0, Ones)
            Local0 = (AUIK <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x4B, Local0, Ones)
            Local0 = (AUIL <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x4C, Local0, Zero)
            Local0 = (AUIM <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x4D, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUIK)) <= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x4E, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIL)) <= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x4F, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIM)) <= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x50, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x14]) <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x51, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x15]) <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x52, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x16]) <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x53, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x14) <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x54, Local0, Ones)
            Local0 = (M601 (0x01, 0x15) <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x55, Local0, Zero)
            Local0 = (M601 (0x01, 0x16) <= DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x56, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x14, 0x01)) <= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x57, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x15, 0x01)) <= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x58, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x16, 0x01)) <= DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x59, Local0, Ones)
            }

            /* LNotEqual */

            Local0 = (0xD650A284 != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x5A, Local0, Zero)
            Local0 = (0xD650A285 != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x5B, Local0, Ones)
            Local0 = (0xD650A283 != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x5C, Local0, Ones)
            Local0 = (AUIK != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x5D, Local0, Zero)
            Local0 = (AUIL != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x5E, Local0, Ones)
            Local0 = (AUIM != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x5F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUIK)) != DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x60, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIL)) != DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x61, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIM)) != DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x62, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x14]) != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x63, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x15]) != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x64, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x16]) != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x65, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x14) != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x66, Local0, Zero)
            Local0 = (M601 (0x01, 0x15) != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x67, Local0, Ones)
            Local0 = (M601 (0x01, 0x16) != DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x68, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x14, 0x01)) != DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x69, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x15, 0x01)) != DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x6A, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x16, 0x01)) != DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x6B, Local0, Ones)
            }
        }

        Method (M065, 1, NotSerialized)
        {
            /* LEqual */

            Local0 = (0x0321 == DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (0x0322 == DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x01, Local0, Zero)
            Local0 = (0x0320 == DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (AUI1 == DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x03, Local0, Ones)
            Local0 = (AUIG == DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x04, Local0, Zero)
            Local0 = (AUIH == DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x05, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) == DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x06, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIG)) == DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x07, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIH)) == DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x08, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x01]) == DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x09, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x10]) == DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x0A, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x11]) == DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x0B, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) == DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x0C, Local0, Ones)
            Local0 = (M601 (0x01, 0x10) == DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x0D, Local0, Zero)
            Local0 = (M601 (0x01, 0x11) == DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x0E, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) == DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x0F, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) == DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) == DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x11, Local0, Zero)
            }

            /* LGreater */

            Local0 = (0x0321 > DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (0x0322 > DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x13, Local0, Ones)
            Local0 = (0x0320 > DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (AUI1 > DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x15, Local0, Zero)
            Local0 = (AUIG > DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x16, Local0, Ones)
            Local0 = (AUIH > DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x17, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) > DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x18, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIG)) > DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x19, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIH)) > DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x1A, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x01]) > DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x1B, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x10]) > DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x1C, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x11]) > DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x1D, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) > DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x1E, Local0, Zero)
            Local0 = (M601 (0x01, 0x10) > DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x1F, Local0, Ones)
            Local0 = (M601 (0x01, 0x11) > DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x20, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) > DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x21, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) > DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x22, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) > DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x23, Local0, Zero)
            }

            /* LGreaterEqual */

            Local0 = (0x0321 >= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x24, Local0, Ones)
            Local0 = (0x0322 >= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x25, Local0, Ones)
            Local0 = (0x0320 >= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x26, Local0, Zero)
            Local0 = (AUI1 >= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x27, Local0, Ones)
            Local0 = (AUIG >= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x28, Local0, Ones)
            Local0 = (AUIH >= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x29, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) >= DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x2A, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIG)) >= DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x2B, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIH)) >= DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x2C, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x01]) >= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2D, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x10]) >= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2E, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x11]) >= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x2F, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) >= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x30, Local0, Ones)
            Local0 = (M601 (0x01, 0x10) >= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x31, Local0, Ones)
            Local0 = (M601 (0x01, 0x11) >= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x32, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) >= DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x33, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) >= DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x34, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) >= DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x35, Local0, Zero)
            }

            /* LLess */

            Local0 = (0x0321 < DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x36, Local0, Zero)
            Local0 = (0x0322 < DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x37, Local0, Zero)
            Local0 = (0x0320 < DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x38, Local0, Ones)
            Local0 = (AUI1 < DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x39, Local0, Zero)
            Local0 = (AUIG < DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x3A, Local0, Zero)
            Local0 = (AUIH < DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x3B, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) < DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x3C, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIG)) < DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x3D, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIH)) < DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x3E, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x01]) < DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x3F, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x10]) < DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x40, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x11]) < DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x41, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) < DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x42, Local0, Zero)
            Local0 = (M601 (0x01, 0x10) < DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x43, Local0, Zero)
            Local0 = (M601 (0x01, 0x11) < DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x44, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) < DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x45, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) < DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x46, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) < DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x47, Local0, Ones)
            }

            /* LLessEqual */

            Local0 = (0x0321 <= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x48, Local0, Ones)
            Local0 = (0x0322 <= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x49, Local0, Zero)
            Local0 = (0x0320 <= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x4A, Local0, Ones)
            Local0 = (AUI1 <= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x4B, Local0, Ones)
            Local0 = (AUIG <= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x4C, Local0, Zero)
            Local0 = (AUIH <= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x4D, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) <= DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x4E, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIG)) <= DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x4F, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIH)) <= DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x50, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x01]) <= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x51, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x10]) <= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x52, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x11]) <= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x53, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) <= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x54, Local0, Ones)
            Local0 = (M601 (0x01, 0x10) <= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x55, Local0, Zero)
            Local0 = (M601 (0x01, 0x11) <= DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x56, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) <= DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x57, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) <= DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x58, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) <= DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x59, Local0, Ones)
            }

            /* LNotEqual */

            Local0 = (0x0321 != DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x5A, Local0, Zero)
            Local0 = (0x0322 != DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x5B, Local0, Ones)
            Local0 = (0x0320 != DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x5C, Local0, Ones)
            Local0 = (AUI1 != DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x5D, Local0, Zero)
            Local0 = (AUIG != DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x5E, Local0, Ones)
            Local0 = (AUIH != DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x5F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) != DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x60, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIG)) != DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x61, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIH)) != DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x62, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x01]) != DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x63, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x10]) != DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x64, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x11]) != DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x65, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) != DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x66, Local0, Zero)
            Local0 = (M601 (0x01, 0x10) != DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x67, Local0, Ones)
            Local0 = (M601 (0x01, 0x11) != DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x68, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) != DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x69, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) != DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x6A, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) != DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x6B, Local0, Ones)
            }
        }

        /* Buffer Field to Integer intermediate conversion of the Buffer Field */
        /* second operand of Concatenate operator in case the first one is Integer */
        Method (M64Q, 1, NotSerialized)
        {
            Local0 = Concatenate (0x0321, DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x00, Local0, BB26)
            Local0 = Concatenate (0x0321, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x01, Local0, BB21)
            Local0 = Concatenate (AUI1, DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x02, Local0, BB26)
            Local0 = Concatenate (AUI1, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x03, Local0, BB21)
            If (Y078)
            {
                Local0 = Concatenate (DerefOf (RefOf (AUI1)), DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x04, Local0, BB26)
                Local0 = Concatenate (DerefOf (RefOf (AUI1)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x05, Local0, BB21)
            }

            Local0 = Concatenate (DerefOf (PAUI [0x01]), DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x06, Local0, BB26)
            Local0 = Concatenate (DerefOf (PAUI [0x01]), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x07, Local0, BB21)
            /* Method returns Integer */

            Local0 = Concatenate (M601 (0x01, 0x01), DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x08, Local0, BB26)
            Local0 = Concatenate (M601 (0x01, 0x01), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x09, Local0, BB21)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x0A, Local0, BB26)
                Local0 = Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x0B, Local0, BB21)
            }

            Concatenate (0x0321, DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x0C, Local0, BB26)
            Concatenate (0x0321, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x0D, Local0, BB21)
            Concatenate (AUI1, DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x0E, Local0, BB26)
            Concatenate (AUI1, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x0F, Local0, BB21)
            If (Y078)
            {
                Concatenate (DerefOf (RefOf (AUI1)), DerefOf (RefOf (BF61)), Local0)
                M600 (Arg0, 0x10, Local0, BB26)
                Concatenate (DerefOf (RefOf (AUI1)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x11, Local0, BB21)
            }

            Concatenate (DerefOf (PAUI [0x01]), DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x12, Local0, BB26)
            Concatenate (DerefOf (PAUI [0x01]), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x13, Local0, BB21)
            /* Method returns Integer */

            Concatenate (M601 (0x01, 0x01), DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x14, Local0, BB26)
            Concatenate (M601 (0x01, 0x01), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x15, Local0, BB21)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), DerefOf (RefOf (BF61)), Local0)
                M600 (Arg0, 0x16, Local0, BB26)
                Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x17, Local0, BB21)
            }
        }

        Method (M32Q, 1, NotSerialized)
        {
            Local0 = Concatenate (0x0321, DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x00, Local0, BB27)
            Local0 = Concatenate (0x0321, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x01, Local0, BB28)
            Local0 = Concatenate (AUI1, DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x02, Local0, BB27)
            Local0 = Concatenate (AUI1, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x03, Local0, BB28)
            If (Y078)
            {
                Local0 = Concatenate (DerefOf (RefOf (AUI1)), DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x04, Local0, BB27)
                Local0 = Concatenate (DerefOf (RefOf (AUI1)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x05, Local0, BB28)
            }

            Local0 = Concatenate (DerefOf (PAUI [0x01]), DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x06, Local0, BB27)
            Local0 = Concatenate (DerefOf (PAUI [0x01]), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x07, Local0, BB28)
            /* Method returns Integer */

            Local0 = Concatenate (M601 (0x01, 0x01), DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x08, Local0, BB27)
            Local0 = Concatenate (M601 (0x01, 0x01), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x09, Local0, BB28)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x0A, Local0, BB27)
                Local0 = Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x0B, Local0, BB28)
            }

            Concatenate (0x0321, DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x0C, Local0, BB27)
            Concatenate (0x0321, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x0D, Local0, BB28)
            Concatenate (AUI1, DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x0E, Local0, BB27)
            Concatenate (AUI1, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x0F, Local0, BB28)
            If (Y078)
            {
                Concatenate (DerefOf (RefOf (AUI1)), DerefOf (RefOf (BF61)), Local0)
                M600 (Arg0, 0x10, Local0, BB27)
                Concatenate (DerefOf (RefOf (AUI1)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x11, Local0, BB28)
            }

            Concatenate (DerefOf (PAUI [0x01]), DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x12, Local0, BB27)
            Concatenate (DerefOf (PAUI [0x01]), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x14, Local0, BB28)
            /* Method returns Integer */

            Concatenate (M601 (0x01, 0x01), DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x15, Local0, BB27)
            Concatenate (M601 (0x01, 0x01), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x16, Local0, BB28)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), DerefOf (RefOf (BF61)), Local0)
                M600 (Arg0, 0x17, Local0, BB27)
                Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x18, Local0, BB28)
            }
        }

        /* Buffer Field to Integer conversion of the Buffer Field Length */
        /* (second) operand of the ToString operator */
        /* Common 32-bit/64-bit test */
        Method (M066, 1, NotSerialized)
        {
            Local0 = ToString (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x00, Local0, BS1B)
            Local0 = ToString (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x01, Local0, BS1C)
            Local0 = ToString (AUB6, DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x02, Local0, BS1B)
            Local0 = ToString (AUB6, DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x03, Local0, BS1C)
            If (Y078)
            {
                Local0 = ToString (DerefOf (RefOf (AUB6)), DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x04, Local0, BS1B)
                Local0 = ToString (DerefOf (RefOf (AUB6)), DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x05, Local0, BS1C)
            }

            Local0 = ToString (DerefOf (PAUB [0x06]), DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x06, Local0, BS1B)
            Local0 = ToString (DerefOf (PAUB [0x06]), DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x07, Local0, BS1C)
            /* Method returns Buffer */

            Local0 = ToString (M601 (0x03, 0x06), DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x08, Local0, BS1B)
            Local0 = ToString (M601 (0x03, 0x06), DerefOf (RefOf (BF61)))
            M600 (Arg0, 0x09, Local0, BS1C)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = ToString (DerefOf (M602 (0x03, 0x06, 0x01)), DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x0A, Local0, BS1B)
                Local0 = ToString (DerefOf (M602 (0x03, 0x06, 0x01)), DerefOf (RefOf (BF61)))
                M600 (Arg0, 0x0B, Local0, BS1C)
            }

            ToString (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, DerefOf (RefOf (BF74)), Local0)
            M600 (Arg0, 0x0C, Local0, BS1B)
            ToString (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x0D, Local0, BS1C)
            ToString (AUB6, DerefOf (RefOf (BF74)), Local0)
            M600 (Arg0, 0x0E, Local0, BS1B)
            ToString (AUB6, DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x0F, Local0, BS1C)
            If (Y078)
            {
                ToString (DerefOf (RefOf (AUB6)), DerefOf (RefOf (BF74)), Local0)
                M600 (Arg0, 0x10, Local0, BS1B)
                ToString (DerefOf (RefOf (AUB6)), DerefOf (RefOf (BF61)), Local0)
                M600 (Arg0, 0x11, Local0, BS1C)
            }

            ToString (DerefOf (PAUB [0x06]), DerefOf (RefOf (BF74)), Local0)
            M600 (Arg0, 0x12, Local0, BS1B)
            ToString (DerefOf (PAUB [0x06]), DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x13, Local0, BS1C)
            /* Method returns Buffer */

            ToString (M601 (0x03, 0x06), DerefOf (RefOf (BF74)), Local0)
            M600 (Arg0, 0x14, Local0, BS1B)
            ToString (M601 (0x03, 0x06), DerefOf (RefOf (BF61)), Local0)
            M600 (Arg0, 0x15, Local0, BS1C)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                ToString (DerefOf (M602 (0x03, 0x06, 0x01)), DerefOf (RefOf (BF74)), Local0)
                M600 (Arg0, 0x16, Local0, BS1B)
                ToString (DerefOf (M602 (0x03, 0x06, 0x01)), DerefOf (RefOf (BF61)), Local0)
                M600 (Arg0, 0x17, Local0, BS1C)
            }
        }

        Method (M64R, 1, NotSerialized)
        {
            Local0 = ToString (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x00, Local0, BS1C)
            Local0 = ToString (AUB6, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x01, Local0, BS1C)
            If (Y078)
            {
                Local0 = ToString (DerefOf (RefOf (AUB6)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x02, Local0, BS1C)
            }

            Local0 = ToString (DerefOf (PAUB [0x06]), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x03, Local0, BS1C)
            /* Method returns Buffer */

            Local0 = ToString (M601 (0x03, 0x06), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x04, Local0, BS1C)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = ToString (DerefOf (M602 (0x03, 0x06, 0x01)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x05, Local0, BS1C)
            }

            ToString (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x06, Local0, BS1C)
            ToString (AUB6, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x07, Local0, BS1C)
            If (Y078)
            {
                ToString (DerefOf (RefOf (AUB6)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x08, Local0, BS1C)
            }

            ToString (DerefOf (PAUB [0x06]), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x09, Local0, BS1C)
            /* Method returns Buffer */

            ToString (M601 (0x03, 0x06), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x0A, Local0, BS1C)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                ToString (DerefOf (M602 (0x03, 0x06, 0x01)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x0B, Local0, BS1C)
            }
        }

        Method (M32R, 1, NotSerialized)
        {
            Local0 = ToString (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x00, Local0, BS1C)
            Local0 = ToString (AUB6, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x01, Local0, BS1C)
            If (Y078)
            {
                Local0 = ToString (DerefOf (RefOf (AUB6)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x02, Local0, BS1C)
            }

            Local0 = ToString (DerefOf (PAUB [0x06]), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x03, Local0, BS1C)
            /* Method returns Buffer */

            Local0 = ToString (M601 (0x03, 0x06), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x04, Local0, BS1C)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = ToString (DerefOf (M602 (0x03, 0x06, 0x01)), DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x05, Local0, BS1C)
            }

            ToString (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x06, Local0, BS1C)
            ToString (AUB6, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x07, Local0, BS1C)
            If (Y078)
            {
                ToString (DerefOf (RefOf (AUB6)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x08, Local0, BS1C)
            }

            ToString (DerefOf (PAUB [0x06]), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x09, Local0, BS1C)
            /* Method returns Buffer */

            ToString (M601 (0x03, 0x06), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x0A, Local0, BS1C)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                ToString (DerefOf (M602 (0x03, 0x06, 0x01)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x0B, Local0, BS1C)
            }
        }

        /* Buffer Field to Integer conversion of the Buffer Field Index */
        /* (second) operand of the Index operator */
        Method (M067, 1, NotSerialized)
        {
            Store (AUS6 [DerefOf (RefOf (BF74))], Local0)
            M600 (Arg0, 0x00, DerefOf (Local0), BI10)
            Store (AUB6 [DerefOf (RefOf (BF74))], Local0)
            M600 (Arg0, 0x01, DerefOf (Local0), BI10)
            Store (AUP0 [DerefOf (RefOf (BF74))], Local0)
            M600 (Arg0, 0x02, DerefOf (Local0), BI11)
            If (Y078)
            {
                Store (DerefOf (RefOf (AUS6)) [DerefOf (RefOf (BF74))], Local0)
                M600 (Arg0, 0x03, DerefOf (Local0), BI10)
                Store (DerefOf (RefOf (AUB6)) [DerefOf (RefOf (BF74))], Local0)
                M600 (Arg0, 0x04, DerefOf (Local0), BI10)
                Store (DerefOf (RefOf (AUP0)) [DerefOf (RefOf (BF74))], Local0)
                M600 (Arg0, 0x05, DerefOf (Local0), BI11)
            }

            Store (DerefOf (PAUS [0x06]) [DerefOf (RefOf (BF74))], Local0)
            M600 (Arg0, 0x06, DerefOf (Local0), BI10)
            Store (DerefOf (PAUB [0x06]) [DerefOf (RefOf (BF74))], Local0)
            M600 (Arg0, 0x07, DerefOf (Local0), BI10)
            Store (DerefOf (PAUP [0x00]) [DerefOf (RefOf (BF74))], Local0)
            M600 (Arg0, 0x08, DerefOf (Local0), BI11)
            /* Method returns Object */

            If (Y900)
            {
                Store (M601 (0x02, 0x06) [DerefOf (RefOf (BF74))], Local0)
                M600 (Arg0, 0x09, DerefOf (Local0), BI10)
                Store (M601 (0x03, 0x06) [DerefOf (RefOf (BF74))], Local0)
                M600 (Arg0, 0x0A, DerefOf (Local0), BI10)
                Store (M601 (0x04, 0x00) [DerefOf (RefOf (BF74))], Local0)
                M600 (Arg0, 0x0B, DerefOf (Local0), BI11)
            }
            Else
            {
                CH03 (Arg0, Z120, __LINE__, 0x00, 0x00)
                Store (M601 (0x02, 0x06) [DerefOf (RefOf (BF74))], Local3)
                CH04 (Arg0, 0x00, 0x55, Z120, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
                Store (M601 (0x03, 0x06) [DerefOf (RefOf (BF74))], Local3)
                CH04 (Arg0, 0x00, 0x55, Z120, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
                Store (M601 (0x04, 0x00) [DerefOf (RefOf (BF74))], Local3)
                CH04 (Arg0, 0x00, 0x55, Z120, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
            }

            /* Method returns Reference */

            If (Y500)
            {
                Store (DerefOf (M602 (0x02, 0x06, 0x01)) [DerefOf (RefOf (BF74))], Local0)
                M600 (Arg0, 0x0C, DerefOf (Local0), BI10)
                Store (DerefOf (M602 (0x03, 0x06, 0x01)) [DerefOf (RefOf (BF74))], Local0)
                M600 (Arg0, 0x0D, DerefOf (Local0), BI10)
                Store (DerefOf (M602 (0x04, 0x00, 0x01)) [DerefOf (RefOf (BF74))], Local0)
                M600 (Arg0, 0x0E, DerefOf (Local0), BI11)
            }

            Local0 = AUS6 [DerefOf (RefOf (BF74))]
            M600 (Arg0, 0x0F, DerefOf (Local0), BI10)
            Local0 = AUB6 [DerefOf (RefOf (BF74))]
            M600 (Arg0, 0x10, DerefOf (Local0), BI10)
            Local0 = AUP0 [DerefOf (RefOf (BF74))]
            M600 (Arg0, 0x11, DerefOf (Local0), BI11)
            If (Y078)
            {
                Local0 = DerefOf (RefOf (AUS6)) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x12, DerefOf (Local0), BI10)
                Local0 = DerefOf (RefOf (AUB6)) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x13, DerefOf (Local0), BI10)
                Local0 = DerefOf (RefOf (AUP0)) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x14, DerefOf (Local0), BI11)
            }

            Local0 = DerefOf (PAUS [0x06]) [DerefOf (RefOf (BF74))]
            M600 (Arg0, 0x15, DerefOf (Local0), BI10)
            Local0 = DerefOf (PAUB [0x06]) [DerefOf (RefOf (BF74))]
            M600 (Arg0, 0x16, DerefOf (Local0), BI10)
            Local0 = DerefOf (PAUP [0x00]) [DerefOf (RefOf (BF74))]
            M600 (Arg0, 0x17, DerefOf (Local0), BI11)
            /* Method returns Object */

            If (Y900)
            {
                Local0 = M601 (0x02, 0x06) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x18, DerefOf (Local0), BI10)
                Local0 = M601 (0x03, 0x06) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x19, DerefOf (Local0), BI10)
                Local0 = M601 (0x04, 0x00) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x1A, DerefOf (Local0), BI11)
            }
            Else
            {
                CH03 (Arg0, Z120, __LINE__, 0x00, 0x00)
                Local0 = M601 (0x02, 0x06) [DerefOf (RefOf (BF74))]
                CH04 (Arg0, 0x00, 0x55, Z120, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
                Local0 = M601 (0x03, 0x06) [DerefOf (RefOf (BF74))]
                CH04 (Arg0, 0x00, 0x55, Z120, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
                Local0 = M601 (0x04, 0x00) [DerefOf (RefOf (BF74))]
                CH04 (Arg0, 0x00, 0x55, Z120, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
            }

            /* Method returns Reference */

            If (Y500)
            {
                Local0 = DerefOf (M602 (0x02, 0x06, 0x01)) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x1B, DerefOf (Local0), BI10)
                Local0 = DerefOf (M602 (0x03, 0x06, 0x01)) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x1C, DerefOf (Local0), BI10)
                Local0 = DerefOf (M602 (0x04, 0x00, 0x01)) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x1D, DerefOf (Local0), BI11)
            }

            If (Y098)
            {
                Local0 = Local1 = AUS6 [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x1E, DerefOf (Local0), BI10)
                Local0 = Local1 = AUB6 [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x1F, DerefOf (Local0), BI10)
                Local0 = Local1 = AUP0 [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x20, DerefOf (Local0), BI11)
            }

            If (Y078)
            {
                Local0 = Local1 = DerefOf (RefOf (AUS6)) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x21, DerefOf (Local0), BI10)
                Local0 = Local1 = DerefOf (RefOf (AUB6)) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x22, DerefOf (Local0), BI10)
                Local0 = Local1 = DerefOf (RefOf (AUP0)) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x23, DerefOf (Local0), BI11)
            }

            If (Y098)
            {
                Local0 = Local1 = DerefOf (PAUS [0x06]) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x24, DerefOf (Local0), BI10)
                Local0 = Local1 = DerefOf (PAUB [0x06]) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x25, DerefOf (Local0), BI10)
                Local0 = Local1 = DerefOf (PAUP [0x00]) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x26, DerefOf (Local0), BI11)
            }

            /* Method returns Object */

            If ((Y900 && Y098))
            {
                Local0 = Local1 = M601 (0x02, 0x06) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x27, DerefOf (Local0), BI10)
                Local0 = Local1 = M601 (0x03, 0x06) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x28, DerefOf (Local0), BI10)
                Local0 = Local1 = M601 (0x04, 0x00) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x29, DerefOf (Local0), BI11)
            }

            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Local1 = DerefOf (M602 (0x02, 0x06, 0x01)) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x2A, DerefOf (Local0), BI10)
                Local0 = Local1 = DerefOf (M602 (0x03, 0x06, 0x01)) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x2B, DerefOf (Local0), BI10)
                Local0 = Local1 = DerefOf (M602 (0x04, 0x00, 0x01)) [DerefOf (RefOf (BF74))]
                M600 (Arg0, 0x2C, DerefOf (Local0), BI11)
            }
        }

        /* Buffer Field to Integer conversion of the Buffer Field Arg (third) */
        /* operand of the Fatal operator */
        /* (it can only be checked an exception does not occur) */
        Method (M068, 1, NotSerialized)
        {
            CH03 (Arg0, Z120, __LINE__, 0x00, 0x00)
            Fatal (0xFF, 0xFFFFFFFF, DerefOf (RefOf (BF61)))
            If (F64)
            {
                Fatal (0xFF, 0xFFFFFFFF, DerefOf (RefOf (BF65)))
            }
            Else
            {
                Fatal (0xFF, 0xFFFFFFFF, DerefOf (RefOf (BF65)))
            }

            CH03 (Arg0, Z120, __LINE__, 0x00, 0x00)
        }

        /* Buffer Field to Integer conversion of the Buffer Field Index */
        /* and Length operands of the Mid operator */
        /* Common 32-bit/64-bit test */
        Method (M069, 1, NotSerialized)
        {
            /* Buffer Field to Integer conversion of the Buffer Field Index operand */

            Local0 = Mid ("This is auxiliary String", DerefOf (RefOf (BF74)), 0x0A)
            M600 (Arg0, 0x00, Local0, BS1D)
            Local0 = Mid (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, DerefOf (RefOf (BF74)), 0x0A)
            M600 (Arg0, 0x01, Local0, BB32)
            Local0 = Mid (AUS6, DerefOf (RefOf (BF74)), 0x0A)
            M600 (Arg0, 0x02, Local0, BS1D)
            Local0 = Mid (AUB6, DerefOf (RefOf (BF74)), 0x0A)
            M600 (Arg0, 0x03, Local0, BB32)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (AUS6)), DerefOf (RefOf (BF74)), 0x0A)
                M600 (Arg0, 0x04, Local0, BS1D)
                Local0 = Mid (DerefOf (RefOf (AUB6)), DerefOf (RefOf (BF74)), 0x0A)
                M600 (Arg0, 0x05, Local0, BB32)
            }

            Local0 = Mid (DerefOf (PAUS [0x06]), DerefOf (RefOf (BF74)), 0x0A
                )
            M600 (Arg0, 0x06, Local0, BS1D)
            Local0 = Mid (DerefOf (PAUB [0x06]), DerefOf (RefOf (BF74)), 0x0A
                )
            M600 (Arg0, 0x07, Local0, BB32)
            /* Method returns Object */

            Local0 = Mid (M601 (0x02, 0x06), DerefOf (RefOf (BF74)), 0x0A)
            M600 (Arg0, 0x08, Local0, BS1D)
            Local0 = Mid (M601 (0x03, 0x06), DerefOf (RefOf (BF74)), 0x0A)
            M600 (Arg0, 0x09, Local0, BB32)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Mid (DerefOf (M602 (0x02, 0x06, 0x01)), DerefOf (RefOf (BF74)), 0x0A
                    )
                M600 (Arg0, 0x0A, Local0, BS1D)
                Local0 = Mid (DerefOf (M602 (0x03, 0x06, 0x01)), DerefOf (RefOf (BF74)), 0x0A
                    )
                M600 (Arg0, 0x0B, Local0, BB32)
            }

            Mid ("This is auxiliary String", DerefOf (RefOf (BF74)), 0x0A, Local0)
            M600 (Arg0, 0x0C, Local0, BS1D)
            Mid (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, DerefOf (RefOf (BF74)), 0x0A, Local0)
            M600 (Arg0, 0x0D, Local0, BB32)
            Mid (AUS6, DerefOf (RefOf (BF74)), 0x0A, Local0)
            M600 (Arg0, 0x0E, Local0, BS1D)
            Mid (AUB6, DerefOf (RefOf (BF74)), 0x0A, Local0)
            M600 (Arg0, 0x0F, Local0, BB32)
            If (Y078)
            {
                Mid (DerefOf (RefOf (AUS6)), DerefOf (RefOf (BF74)), 0x0A, Local0)
                M600 (Arg0, 0x10, Local0, BS1D)
                Mid (DerefOf (RefOf (AUB6)), DerefOf (RefOf (BF74)), 0x0A, Local0)
                M600 (Arg0, 0x11, Local0, BB32)
            }

            Mid (DerefOf (PAUS [0x06]), DerefOf (RefOf (BF74)), 0x0A, Local0)
            M600 (Arg0, 0x12, Local0, BS1D)
            Mid (DerefOf (PAUB [0x06]), DerefOf (RefOf (BF74)), 0x0A, Local0)
            M600 (Arg0, 0x13, Local0, BB32)
            /* Method returns Object */

            Mid (M601 (0x02, 0x06), DerefOf (RefOf (BF74)), 0x0A, Local0)
            M600 (Arg0, 0x14, Local0, BS1D)
            Mid (M601 (0x03, 0x06), DerefOf (RefOf (BF74)), 0x0A, Local0)
            M600 (Arg0, 0x15, Local0, BB32)
            /* Method returns Reference */

            If (Y500)
            {
                Mid (DerefOf (M602 (0x02, 0x06, 0x01)), DerefOf (RefOf (BF74)), 0x0A, Local0)
                M600 (Arg0, 0x16, Local0, BS1D)
                Mid (DerefOf (M602 (0x03, 0x06, 0x01)), DerefOf (RefOf (BF74)), 0x0A, Local0)
                M600 (Arg0, 0x17, Local0, BB32)
            }

            /* Buffer Field to Integer conversion of the Buffer Field Length operand */

            Local0 = Mid ("This is auxiliary String", 0x00, DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x18, Local0, BS1B)
            Local0 = Mid (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, 0x00, DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x19, Local0, BB33)
            Local0 = Mid (AUS6, 0x00, DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x1A, Local0, BS1B)
            Local0 = Mid (AUB6, 0x00, DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x1B, Local0, BB33)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (AUS6)), 0x00, DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x1C, Local0, BS1B)
                Local0 = Mid (DerefOf (RefOf (AUB6)), 0x00, DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x1D, Local0, BB33)
            }

            Local0 = Mid (DerefOf (PAUS [0x06]), 0x00, DerefOf (RefOf (BF74))
                )
            M600 (Arg0, 0x1E, Local0, BS1B)
            Local0 = Mid (DerefOf (PAUB [0x06]), 0x00, DerefOf (RefOf (BF74))
                )
            M600 (Arg0, 0x1F, Local0, BB33)
            /* Method returns Object */

            Local0 = Mid (M601 (0x02, 0x06), 0x00, DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x20, Local0, BS1B)
            Local0 = Mid (M601 (0x03, 0x06), 0x00, DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x21, Local0, BB33)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Mid (DerefOf (M602 (0x02, 0x06, 0x01)), 0x00, DerefOf (RefOf (BF74))
                    )
                M600 (Arg0, 0x22, Local0, BS1B)
                Local0 = Mid (DerefOf (M602 (0x03, 0x06, 0x01)), 0x00, DerefOf (RefOf (BF74))
                    )
                M600 (Arg0, 0x23, Local0, BB33)
            }

            Mid ("This is auxiliary String", 0x00, DerefOf (RefOf (BF74)), Local0)
            M600 (Arg0, 0x24, Local0, BS1B)
            Mid (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, 0x00, DerefOf (RefOf (BF74)), Local0)
            M600 (Arg0, 0x25, Local0, BB33)
            Mid (AUS6, 0x00, DerefOf (RefOf (BF74)), Local0)
            M600 (Arg0, 0x25, Local0, BS1B)
            Mid (AUB6, 0x00, DerefOf (RefOf (BF74)), Local0)
            M600 (Arg0, 0x27, Local0, BB33)
            If (Y078)
            {
                Mid (DerefOf (RefOf (AUS6)), 0x00, DerefOf (RefOf (BF74)), Local0)
                M600 (Arg0, 0x28, Local0, BS1B)
                Mid (DerefOf (RefOf (AUB6)), 0x00, DerefOf (RefOf (BF74)), Local0)
                M600 (Arg0, 0x29, Local0, BB33)
            }

            Mid (DerefOf (PAUS [0x06]), 0x00, DerefOf (RefOf (BF74)), Local0)
            M600 (Arg0, 0x2A, Local0, BS1B)
            Mid (DerefOf (PAUB [0x06]), 0x00, DerefOf (RefOf (BF74)), Local0)
            M600 (Arg0, 0x2B, Local0, BB33)
            /* Method returns Object */

            Mid (M601 (0x02, 0x06), 0x00, DerefOf (RefOf (BF74)), Local0)
            M600 (Arg0, 0x2C, Local0, BS1B)
            Mid (M601 (0x03, 0x06), 0x00, DerefOf (RefOf (BF74)), Local0)
            M600 (Arg0, 0x2D, Local0, BB33)
            /* Method returns Reference */

            If (Y500)
            {
                Mid (DerefOf (M602 (0x02, 0x06, 0x01)), 0x00, DerefOf (RefOf (BF74)), Local0)
                M600 (Arg0, 0x2E, Local0, BS1B)
                Mid (DerefOf (M602 (0x03, 0x06, 0x01)), 0x00, DerefOf (RefOf (BF74)), Local0)
                M600 (Arg0, 0x2F, Local0, BB33)
            }
        }

        Method (M64S, 1, NotSerialized)
        {
            /* Buffer Field to Integer conversion of the Buffer Field Length operand */

            Local0 = Mid ("This is auxiliary String", 0x00, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x00, Local0, BS1E)
            Local0 = Mid (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, 0x00, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x01, Local0, BB34)
            Local0 = Mid (AUS6, 0x00, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x02, Local0, BS1E)
            Local0 = Mid (AUB6, 0x00, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x03, Local0, BB34)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (AUS6)), 0x00, DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x04, Local0, BS1E)
                Local0 = Mid (DerefOf (RefOf (AUB6)), 0x00, DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x05, Local0, BB34)
            }

            Local0 = Mid (DerefOf (PAUS [0x06]), 0x00, DerefOf (RefOf (BF65))
                )
            M600 (Arg0, 0x06, Local0, BS1E)
            Local0 = Mid (DerefOf (PAUB [0x06]), 0x00, DerefOf (RefOf (BF65))
                )
            M600 (Arg0, 0x07, Local0, BB34)
            /* Method returns Object */

            Local0 = Mid (M601 (0x02, 0x06), 0x00, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x08, Local0, BS1E)
            Local0 = Mid (M601 (0x03, 0x06), 0x00, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x09, Local0, BB34)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Mid (DerefOf (M602 (0x02, 0x06, 0x01)), 0x00, DerefOf (RefOf (BF65))
                    )
                M600 (Arg0, 0x0A, Local0, BS1E)
                Local0 = Mid (DerefOf (M602 (0x03, 0x06, 0x01)), 0x00, DerefOf (RefOf (BF65))
                    )
                M600 (Arg0, 0x0B, Local0, BB34)
            }

            Mid ("This is auxiliary String", 0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x0C, Local0, BS1E)
            Mid (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, 0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x0D, Local0, BB34)
            Mid (AUS6, 0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x0E, Local0, BS1E)
            Mid (AUB6, 0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x0F, Local0, BB34)
            If (Y078)
            {
                Mid (DerefOf (RefOf (AUS6)), 0x00, DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x10, Local0, BS1E)
                Mid (DerefOf (RefOf (AUB6)), 0x00, DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x11, Local0, BB34)
            }

            Mid (DerefOf (PAUS [0x06]), 0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x12, Local0, BS1E)
            Mid (DerefOf (PAUB [0x06]), 0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x13, Local0, BB34)
            /* Method returns Object */

            Mid (M601 (0x02, 0x06), 0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x14, Local0, BS1E)
            Mid (M601 (0x03, 0x06), 0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x15, Local0, BB34)
            /* Method returns Reference */

            If (Y500)
            {
                Mid (DerefOf (M602 (0x02, 0x06, 0x01)), 0x00, DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x16, Local0, BS1E)
                Mid (DerefOf (M602 (0x03, 0x06, 0x01)), 0x00, DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x17, Local0, BB34)
            }

            /* Buffer Field to Integer conversion of the both String operands */

            Local0 = Mid ("This is auxiliary String", DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x18, Local0, BS1F)
            Local0 = Mid (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65))
                )
            M600 (Arg0, 0x19, Local0, BB35)
            Local0 = Mid (AUS6, DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1A, Local0, BS1F)
            Local0 = Mid (AUB6, DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1B, Local0, BB35)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (AUS6)), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65))
                    )
                M600 (Arg0, 0x1C, Local0, BS1F)
                Local0 = Mid (DerefOf (RefOf (AUB6)), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65))
                    )
                M600 (Arg0, 0x1D, Local0, BB35)
            }

            Local0 = Mid (DerefOf (PAUS [0x06]), DerefOf (RefOf (BF74)), DerefOf (
                RefOf (BF65)))
            M600 (Arg0, 0x1E, Local0, BS1F)
            Local0 = Mid (DerefOf (PAUB [0x06]), DerefOf (RefOf (BF74)), DerefOf (
                RefOf (BF65)))
            M600 (Arg0, 0x1F, Local0, BB35)
            /* Method returns Object */

            Local0 = Mid (M601 (0x02, 0x06), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65))
                )
            M600 (Arg0, 0x20, Local0, BS1F)
            Local0 = Mid (M601 (0x03, 0x06), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65))
                )
            M600 (Arg0, 0x21, Local0, BB35)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Mid (DerefOf (M602 (0x02, 0x06, 0x01)), DerefOf (RefOf (BF74)), DerefOf (
                    RefOf (BF65)))
                M600 (Arg0, 0x22, Local0, BS1F)
                Local0 = Mid (DerefOf (M602 (0x03, 0x06, 0x01)), DerefOf (RefOf (BF74)), DerefOf (
                    RefOf (BF65)))
                M600 (Arg0, 0x23, Local0, BB35)
            }

            Mid ("This is auxiliary String", DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x24, Local0, BS1F)
            Mid (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x25, Local0, BB35)
            Mid (AUS6, DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x26, Local0, BS1F)
            Mid (AUB6, DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x27, Local0, BB35)
            If (Y078)
            {
                Mid (DerefOf (RefOf (AUS6)), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x28, Local0, BS1F)
                Mid (DerefOf (RefOf (AUB6)), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x29, Local0, BB35)
            }

            Mid (DerefOf (PAUS [0x06]), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)),
                Local0)
            M600 (Arg0, 0x2A, Local0, BS1F)
            Mid (DerefOf (PAUB [0x06]), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)),
                Local0)
            M600 (Arg0, 0x2B, Local0, BB35)
            /* Method returns Object */

            Mid (M601 (0x02, 0x06), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2C, Local0, BS1F)
            Mid (M601 (0x03, 0x06), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2D, Local0, BB35)
            /* Method returns Reference */

            If (Y500)
            {
                Mid (DerefOf (M602 (0x02, 0x06, 0x01)), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)),
                    Local0)
                M600 (Arg0, 0x2E, Local0, BS1F)
                Mid (DerefOf (M602 (0x03, 0x06, 0x01)), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)),
                    Local0)
                M600 (Arg0, 0x2F, Local0, BB35)
            }
        }

        Method (M32S, 1, NotSerialized)
        {
            /* Buffer Field to Integer conversion of the Buffer Field Length operand */

            Local0 = Mid ("This is auxiliary String", 0x00, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x00, Local0, BS1E)
            Local0 = Mid (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, 0x00, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x01, Local0, BB34)
            Local0 = Mid (AUS6, 0x00, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x02, Local0, BS1E)
            Local0 = Mid (AUB6, 0x00, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x03, Local0, BB34)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (AUS6)), 0x00, DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x04, Local0, BS1E)
                Local0 = Mid (DerefOf (RefOf (AUB6)), 0x00, DerefOf (RefOf (BF65)))
                M600 (Arg0, 0x05, Local0, BB34)
            }

            Local0 = Mid (DerefOf (PAUS [0x06]), 0x00, DerefOf (RefOf (BF65))
                )
            M600 (Arg0, 0x06, Local0, BS1E)
            Local0 = Mid (DerefOf (PAUB [0x06]), 0x00, DerefOf (RefOf (BF65))
                )
            M600 (Arg0, 0x07, Local0, BB34)
            /* Method returns Object */

            Local0 = Mid (M601 (0x02, 0x06), 0x00, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x08, Local0, BS1E)
            Local0 = Mid (M601 (0x03, 0x06), 0x00, DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x09, Local0, BB34)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Mid (DerefOf (M602 (0x02, 0x06, 0x01)), 0x00, DerefOf (RefOf (BF65))
                    )
                M600 (Arg0, 0x0A, Local0, BS1E)
                Local0 = Mid (DerefOf (M602 (0x03, 0x06, 0x01)), 0x00, DerefOf (RefOf (BF65))
                    )
                M600 (Arg0, 0x0B, Local0, BB34)
            }

            Mid ("This is auxiliary String", 0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x0C, Local0, BS1E)
            Mid (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, 0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x0D, Local0, BB34)
            Mid (AUS6, 0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x0E, Local0, BS1E)
            Mid (AUB6, 0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x0F, Local0, BB34)
            If (Y078)
            {
                Mid (DerefOf (RefOf (AUS6)), 0x00, DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x10, Local0, BS1E)
                Mid (DerefOf (RefOf (AUB6)), 0x00, DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x11, Local0, BB34)
            }

            Mid (DerefOf (PAUS [0x06]), 0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x12, Local0, BS1E)
            Mid (DerefOf (PAUB [0x06]), 0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x13, Local0, BB34)
            /* Method returns Object */

            Mid (M601 (0x02, 0x06), 0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x14, Local0, BS1E)
            Mid (M601 (0x03, 0x06), 0x00, DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x15, Local0, BB34)
            /* Method returns Reference */

            If (Y500)
            {
                Mid (DerefOf (M602 (0x02, 0x06, 0x01)), 0x00, DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x16, Local0, BS1E)
                Mid (DerefOf (M602 (0x03, 0x06, 0x01)), 0x00, DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x17, Local0, BB34)
            }

            /* Buffer Field to Integer conversion of the both String operands */

            Local0 = Mid ("This is auxiliary String", DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x18, Local0, BS1F)
            Local0 = Mid (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65))
                )
            M600 (Arg0, 0x19, Local0, BB35)
            Local0 = Mid (AUS6, DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1A, Local0, BS1F)
            Local0 = Mid (AUB6, DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)))
            M600 (Arg0, 0x1B, Local0, BB35)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (AUS6)), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65))
                    )
                M600 (Arg0, 0x1C, Local0, BS1F)
                Local0 = Mid (DerefOf (RefOf (AUB6)), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65))
                    )
                M600 (Arg0, 0x1D, Local0, BB35)
            }

            Local0 = Mid (DerefOf (PAUS [0x06]), DerefOf (RefOf (BF74)), DerefOf (
                RefOf (BF65)))
            M600 (Arg0, 0x1E, Local0, BS1F)
            Local0 = Mid (DerefOf (PAUB [0x06]), DerefOf (RefOf (BF74)), DerefOf (
                RefOf (BF65)))
            M600 (Arg0, 0x1F, Local0, BB35)
            /* Method returns Object */

            Local0 = Mid (M601 (0x02, 0x06), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65))
                )
            M600 (Arg0, 0x20, Local0, BS1F)
            Local0 = Mid (M601 (0x03, 0x06), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65))
                )
            M600 (Arg0, 0x21, Local0, BB35)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Mid (DerefOf (M602 (0x02, 0x06, 0x01)), DerefOf (RefOf (BF74)), DerefOf (
                    RefOf (BF65)))
                M600 (Arg0, 0x22, Local0, BS1F)
                Local0 = Mid (DerefOf (M602 (0x03, 0x06, 0x01)), DerefOf (RefOf (BF74)), DerefOf (
                    RefOf (BF65)))
                M600 (Arg0, 0x23, Local0, BB35)
            }

            Mid ("This is auxiliary String", DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x24, Local0, BS1F)
            Mid (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x25, Local0, BB35)
            Mid (AUS6, DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x26, Local0, BS1F)
            Mid (AUB6, DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x27, Local0, BB35)
            If (Y078)
            {
                Mid (DerefOf (RefOf (AUS6)), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x28, Local0, BS1F)
                Mid (DerefOf (RefOf (AUB6)), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)), Local0)
                M600 (Arg0, 0x29, Local0, BB35)
            }

            Mid (DerefOf (PAUS [0x06]), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)),
                Local0)
            M600 (Arg0, 0x2A, Local0, BS1F)
            Mid (DerefOf (PAUB [0x06]), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)),
                Local0)
            M600 (Arg0, 0x2B, Local0, BB35)
            /* Method returns Object */

            Mid (M601 (0x02, 0x06), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2C, Local0, BS1F)
            Mid (M601 (0x03, 0x06), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)), Local0)
            M600 (Arg0, 0x2D, Local0, BB35)
            /* Method returns Reference */

            If (Y500)
            {
                Mid (DerefOf (M602 (0x02, 0x06, 0x01)), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)),
                    Local0)
                M600 (Arg0, 0x2E, Local0, BS1F)
                Mid (DerefOf (M602 (0x03, 0x06, 0x01)), DerefOf (RefOf (BF74)), DerefOf (RefOf (BF65)),
                    Local0)
                M600 (Arg0, 0x2F, Local0, BB35)
            }
        }

        /* Buffer Field to Integer conversion of the Buffer Field StartIndex */
        /* operand of the Match operator */
        Method (M06A, 1, NotSerialized)
        {
            Local0 = Match (Package (0x0F)
                    {
                        0x0A50,
                        0x0A51,
                        0x0A52,
                        0x0A53,
                        0x0A54,
                        0x0A55,
                        0x0A56,
                        0x0A57,
                        0x0A58,
                        0x0A59,
                        0x0A5A,
                        0x0A5B,
                        0x0A5C,
                        0x0A5D,
                        0x0A5E
                    }, MEQ, 0x0A5D, MTR, 0x00, DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x00, Local0, 0x0D)
            Local0 = Match (Package (0x0F)
                    {
                        0x0A50,
                        0x0A51,
                        0x0A52,
                        0x0A53,
                        0x0A54,
                        0x0A55,
                        0x0A56,
                        0x0A57,
                        0x0A58,
                        0x0A59,
                        0x0A5A,
                        0x0A5B,
                        0x0A5C,
                        0x0A5D,
                        0x0A5E
                    }, MEQ, 0x0A5A, MTR, 0x00, DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = Match (AUP0, MEQ, 0x0A5D, MTR, 0x00, DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x02, Local0, 0x0D)
            Local0 = Match (AUP0, MEQ, 0x0A5A, MTR, 0x00, DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = Match (DerefOf (RefOf (AUP0)), MEQ, 0x0A5D, MTR, 0x00, DerefOf (RefOf (
                    BF74)))
                M600 (Arg0, 0x04, Local0, 0x0D)
                Local0 = Match (DerefOf (RefOf (AUP0)), MEQ, 0x0A5A, MTR, 0x00, DerefOf (RefOf (
                    BF74)))
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = Match (DerefOf (PAUP [0x00]), MEQ, 0x0A5D, MTR, 0x00,
                DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x06, Local0, 0x0D)
            Local0 = Match (DerefOf (PAUP [0x00]), MEQ, 0x0A5A, MTR, 0x00,
                DerefOf (RefOf (BF74)))
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Object */

            Local0 = Match (M601 (0x04, 0x00), MEQ, 0x0A5D, MTR, 0x00, DerefOf (RefOf (
                BF74)))
            M600 (Arg0, 0x08, Local0, 0x0D)
            Local0 = Match (M601 (0x04, 0x00), MEQ, 0x0A5A, MTR, 0x00, DerefOf (RefOf (
                BF74)))
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Match (DerefOf (M602 (0x04, 0x00, 0x01)), MEQ, 0x0A5D, MTR, 0x00,
                    DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x0A, Local0, 0x0D)
                Local0 = Match (DerefOf (M602 (0x04, 0x00, 0x01)), MEQ, 0x0A5A, MTR, 0x00,
                    DerefOf (RefOf (BF74)))
                M600 (Arg0, 0x0B, Local0, Ones)
            }
        }

        /* Buffer Field to Integer conversion of the Buffer Field sole operand */
        /* of the Method execution control operators (Sleep, Stall) */
        Method (M06B, 1, NotSerialized)
        {
            CH03 (Arg0, Z120, __LINE__, 0x00, 0x00)
            /* Sleep */

            Local0 = Timer
            Sleep (DerefOf (RefOf (BF61)))
            CH03 (Arg0, Z120, __LINE__, 0x00, 0x00)
            Local1 = Timer
            Local2 = (Local1 - Local0)
            If ((Local2 < C08C))
            {
                ERR (Arg0, Z120, __LINE__, 0x00, 0x00, Local2, C08C)
            }

            /* Stall */

            Local0 = Timer
            Stall (DerefOf (RefOf (BF75)))
            CH03 (Arg0, Z120, __LINE__, 0x00, 0x00)
            Local1 = Timer
            Local2 = (Local1 - Local0)
            If ((Local2 < 0x03DE))
            {
                ERR (Arg0, Z120, __LINE__, 0x00, 0x00, Local2, 0x03DE)
            }
        }

        /* Buffer Field to Integer conversion of the Buffer Field TimeoutValue */
        /* (second) operand of the Acquire operator */
        Method (M06C, 1, Serialized)
        {
            Mutex (MTX0, 0x00)
            Acquire (MTX0, 0x0000)
            CH03 (Arg0, Z120, __LINE__, 0x00, 0x00)
            Local0 = Timer
            /* Compiler allows only Integer constant as TimeoutValue (Bug 1)
             Acquire(MTX0, Derefof(Refof(bf61)))
             */
            CH03 (Arg0, Z120, __LINE__, 0x00, 0x00)
            Local1 = Timer
            Local2 = (Local1 - Local0)
            If ((Local2 < C08C))
            {
                ERR (Arg0, Z120, __LINE__, 0x00, 0x00, Local2, C08C)
            }
        }

        /* Buffer Field to Integer conversion of the Buffer Field TimeoutValue */
        /* (second) operand of the Wait operator */
        Method (M06D, 1, Serialized)
        {
            Event (EVT0)
            CH03 (Arg0, Z120, __LINE__, 0x00, 0x00)
            Local0 = Timer
            Wait (EVT0, DerefOf (RefOf (BF61)))
            CH03 (Arg0, Z120, __LINE__, 0x00, 0x00)
            Local1 = Timer
            Local2 = (Local1 - Local0)
            If ((Local2 < C08C))
            {
                ERR (Arg0, Z120, __LINE__, 0x00, 0x00, Local2, C08C)
            }
        }

        /* Buffer Field to Integer conversion of the Buffer Field value */
        /* of Predicate of the Method execution control statements */
        /* (If, ElseIf, While) */
        Method (M06E, 1, Serialized)
        {
            Name (IST0, 0x00)
            Method (M001, 0, NotSerialized)
            {
                If (DerefOf (RefOf (BF76)))
                {
                    IST0 = 0x00
                }
            }

            Method (M002, 0, NotSerialized)
            {
                If (DerefOf (RefOf (BF61)))
                {
                    IST0 = 0x02
                }
            }

            Method (M003, 0, NotSerialized)
            {
                If (DerefOf (RefOf (BF65)))
                {
                    IST0 = 0x03
                }
            }

            Method (M004, 0, NotSerialized)
            {
                If (DerefOf (RefOf (BF65)))
                {
                    IST0 = 0x04
                }
            }

            Method (M005, 1, NotSerialized)
            {
                If (Arg0)
                {
                    IST0 = 0xFF
                }
                ElseIf (DerefOf (RefOf (BF76)))
                {
                    IST0 = 0x00
                }
            }

            Method (M006, 1, NotSerialized)
            {
                If (Arg0)
                {
                    IST0 = 0xFF
                }
                ElseIf (DerefOf (RefOf (BF61)))
                {
                    IST0 = 0x06
                }
            }

            Method (M007, 1, NotSerialized)
            {
                If (Arg0)
                {
                    IST0 = 0xFF
                }
                ElseIf (DerefOf (RefOf (BF65)))
                {
                    IST0 = 0x07
                }
            }

            Method (M008, 1, NotSerialized)
            {
                If (Arg0)
                {
                    IST0 = 0xFF
                }
                ElseIf (DerefOf (RefOf (BF65)))
                {
                    IST0 = 0x08
                }
            }

            Method (M009, 0, NotSerialized)
            {
                While (DerefOf (RefOf (BF76)))
                {
                    IST0 = 0x00
                    Break
                }
            }

            /* If */

            IST0 = 0x01
            M001 ()
            M600 (Arg0, 0x00, IST0, 0x01)
            M002 ()
            M600 (Arg0, 0x01, IST0, 0x02)
            M003 ()
            M600 (Arg0, 0x02, IST0, 0x03)
            M004 ()
            M600 (Arg0, 0x03, IST0, 0x04)
            /* ElseIf */

            IST0 = 0x05
            M005 (0x00)
            M600 (Arg0, 0x04, IST0, 0x05)
            M006 (0x00)
            M600 (Arg0, 0x05, IST0, 0x06)
            M007 (0x00)
            M600 (Arg0, 0x06, IST0, 0x07)
            M008 (0x00)
            M600 (Arg0, 0x07, IST0, 0x08)
            /* While */

            IST0 = 0x09
            M009 ()
            M600 (Arg0, 0x08, IST0, 0x09)
        }

        /* Initialize Buffer Fields */

        Method (M073, 0, NotSerialized)
        {
            BF61 = Buffer (0x03)
                {
                     0x21, 0x03, 0x00                                 // !..
                }
            BF62 = Buffer (0x04)
                {
                     0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                }
            BF63 = Buffer (0x05)
                {
                     0xFE, 0xB3, 0x79, 0xC1, 0xA5                     // ..y..
                }
            BF64 = Buffer (0x08)
                {
                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                }
            BF65 = Buffer (0x08)
                {
                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                }
            BF66 = Buffer (0x09)
                {
                    /* 0000 */  0x21, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // !.......
                    /* 0008 */  0x01                                             // .
                }
            BF69 = Buffer (0x43)
                {
                    /* 0000 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
                    /* 0008 */  0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30,  // )*+,-./0
                    /* 0010 */  0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38,  // 12345678
                    /* 0018 */  0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40,  // 9:;<=>?@
                    /* 0020 */  0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48,  // ABCDEFGH
                    /* 0028 */  0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50,  // IJKLMNOP
                    /* 0030 */  0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58,  // QRSTUVWX
                    /* 0038 */  0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, 0x60,  // YZ[\]^_`
                    /* 0040 */  0x61, 0x62, 0x63                                 // abc
                }
            BF6C = Buffer (0x08)
                {
                     0x01, 0x89, 0x67, 0x45, 0x23, 0x01, 0x89, 0x37   // ..gE#..7
                }
            BF6D = Buffer (0x07)
                {
                     0x35, 0xEC, 0xE9, 0x2E, 0x16, 0x76, 0x0D         // 5....v.
                }
            BF6E = Buffer (0x04)
                {
                     0x56, 0x34, 0x12, 0x90                           // V4..
                }
            BF6F = Buffer (0x04)
                {
                     0xC0, 0x2C, 0x5F, 0x05                           // .,_.
                }
            BF70 = 0x6179534E
            BF71 = Buffer (0x08)
                {
                     0x14, 0x22, 0x50, 0x36, 0x41, 0x53, 0x7C, 0x6E   // ."P6AS|n
                }
            BF72 = Buffer (0x08)
                {
                     0x14, 0x22, 0x00, 0x36, 0x41, 0x53, 0x00, 0x6E   // .".6AS.n
                }
            BF73 = Buffer (0x08)
                {
                     0x14, 0x22, 0x00, 0x36, 0x41, 0x53, 0x7C, 0x6E   // .".6AS|n
                }
            BF74 = 0x0B
            BF75 = 0x3F
            BF76 = 0x00
            BF77 = 0x36002214
            If (Y365)
            {
                BF91 = Buffer (0x03)
                    {
                         0x21, 0x03, 0x00                                 // !..
                    }
                BF95 = Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                    }
                BFA1 = Buffer (0x03)
                    {
                         0x21, 0x03, 0x00                                 // !..
                    }
                BFA5 = Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                    }
            }
        }

        /* Check Buffer Fields consistency */

        Method (M074, 1, NotSerialized)
        {
            M600 (Arg0, 0x00, BF61, Buffer()
                {
                    0x21, 0x03, 0x00, 0x00
                })
            M600 (Arg0, 0x01, BF62, Buffer()
                {
                    0xFE, 0xB3, 0x79, 0xC1
                })
            M600 (Arg0, 0x02, BF63, Buffer (0x05)
                {
                     0xFE, 0xB3, 0x79, 0xC1, 0x01                     // ..y..
                })

            M600 (Arg0, 0x03, BF64, Buffer (0x08)
                {
                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0x7E   // ..P...|~
                })

            M600 (Arg0, 0x04, BF65, Buffer (0x08)
                {
                     0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                })

            M600 (Arg0, 0x05, BF66, Buffer (0x09)
                {
                    /* 0000 */  0x21, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // !.......
                    /* 0008 */  0x01                                             // .
                })
            M600 (Arg0, 0x06, BF69, Buffer (0x43)
                {
                    /* 0000 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
                    /* 0008 */  0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30,  // )*+,-./0
                    /* 0010 */  0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38,  // 12345678
                    /* 0018 */  0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40,  // 9:;<=>?@
                    /* 0020 */  0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48,  // ABCDEFGH
                    /* 0028 */  0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50,  // IJKLMNOP
                    /* 0030 */  0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58,  // QRSTUVWX
                    /* 0038 */  0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, 0x60,  // YZ[\]^_`
                    /* 0040 */  0x61, 0x62, 0x63                                 // abc
                })
            M600 (Arg0, 0x07, BF6C, Buffer (0x09)
                {
                    /* 0000 */  0x01, 0x89, 0x67, 0x45, 0x23, 0x01, 0x89, 0x37,  // ..gE#..7
                    /* 0008 */  0x00                                             // .
                })
            M600 (Arg0, 0x08, BF6D, Buffer (0x09)
                {
                    /* 0000 */  0x35, 0xEC, 0xE9, 0x2E, 0x16, 0x76, 0x0D, 0x00,  // 5....v..
                    /* 0008 */  0x00                                             // .
                })
            M600 (Arg0, 0x09, BF6E, Buffer (0x05)
                {
                     0x56, 0x34, 0x12, 0x90, 0x00                     // V4...
                })

            M600 (Arg0, 0x0A, BF6F, Buffer (0x05)
                {
                     0xC0, 0x2C, 0x5F, 0x05, 0x00                     // .,_..
                })

            M600 (Arg0, 0x0B, BF70, Buffer()
                {
                    0x4E, 0x53, 0x79, 0x61
                 })
            M600 (Arg0, 0x0C, BF71, Buffer (0x08)
                {
                     0x14, 0x22, 0x50, 0x36, 0x41, 0x53, 0x7C, 0x6E   // ."P6AS|n
                })
            M600 (Arg0, 0x0D, BF72, Buffer (0x08)
                {
                     0x14, 0x22, 0x00, 0x36, 0x41, 0x53, 0x00, 0x6E   // .".6AS.n
                })
            M600 (Arg0, 0x0E, BF73, Buffer (0x08)
                {
                     0x14, 0x22, 0x00, 0x36, 0x41, 0x53, 0x7C, 0x6E   // .".6AS|n
                })

            M600 (Arg0, 0x0F, BF74, Buffer (0x05)
                {
                     0x0B, 0x00, 0x00, 0x00, 0x00                     // .....
                })

            M600 (Arg0, 0x10, BF75, Buffer (0x05)
                {
                     0x3F, 0x00, 0x00, 0x00, 0x00                     // ?....
                })

            M600 (Arg0, 0x11, BF76, Buffer (0x05)
                {
                     0x00, 0x00, 0x00, 0x00, 0x00                     // .....
                })

            M600 (Arg0, 0x12, BF77, Buffer()
                {
                    0x14, 0x22, 0x00, 0x36
                })
            If (Y365)
            {
                M600 (Arg0, 0x13, BF91, 0x0320)
                M600 (Arg0, 0x14, BFA1, 0x0322)
                M600 (Arg0, 0x15, BF95, Buffer (0x08)
                {
                    0x83, 0xA2, 0x50, 0xD6, 0x00, 0x00, 0x00, 0x00   // ..P.....
                })

                M600 (Arg0, 0x16, BFA5, Buffer (0x08)
                {
                    0x85, 0xA2, 0x50, 0xD6, 0x00, 0x00, 0x00, 0x00   // ..P.....
                })
            }
        }

        /*
         * Begin of the test body
         */
        M073 ()
        /* Buffer Field to Buffer implicit conversion Cases. */
        /* Buffer Field to Buffer conversion of the Buffer Field second operand */
        /* of Logical operators when the first operand is evaluated as Buffer */
        /* (LEqual, LGreater, LGreaterEqual, LLess, LLessEqual, LNotEqual) */
        If (F64)
        {
            Concatenate (__METHOD__, "-m644", Local0)
            SRMT (Local0)
            M644 (Local0)
        }
        Else
        {
            Concatenate (__METHOD__, "-m324", Local0)
            SRMT (Local0)
            M324 (Local0)
        }

        /* Buffer Field to Buffer conversion of the both Integer operands */
        /* of Concatenate operator */
        If (F64)
        {
            Concatenate (__METHOD__, "-m645", Local0)
            SRMT (Local0)
            M645 (Local0)
        }
        Else
        {
            Concatenate (__METHOD__, "-m325", Local0)
            SRMT (Local0)
            M325 (Local0)
        }

        /* Buffer Field to Buffer conversion of the Buffer Field second operand */
        /* of Concatenate operator when the first operand is evaluated as Buffer */
        If (F64)
        {
            Concatenate (__METHOD__, "-m646", Local0)
            SRMT (Local0)
            M646 (Local0)
        }
        Else
        {
            Concatenate (__METHOD__, "-m326", Local0)
            SRMT (Local0)
            M326 (Local0)
        }

        /* Buffer Field to Buffer conversion of the Buffer Field Source operand */
        /* of ToString operator */
        If (F64)
        {
            Concatenate (__METHOD__, "-m647", Local0)
            SRMT (Local0)
            M647 (Local0)
        }
        Else
        {
            Concatenate (__METHOD__, "-m327", Local0)
            SRMT (Local0)
            M327 (Local0)
        }

        /* Buffer Field to Buffer conversion of the Buffer Field Source operand */
        /* of Mid operator */
        If (F64)
        {
            Concatenate (__METHOD__, "-m648", Local0)
            SRMT (Local0)
            M648 (Local0)
        }
        Else
        {
            Concatenate (__METHOD__, "-m328", Local0)
            SRMT (Local0)
            M328 (Local0)
        }

        /* Buffer Field to Integer implicit conversion Cases. */
        /* Buffer Field to Integer conversion of the Buffer Field sole operand */
        /* of the 1-parameter Integer arithmetic operators */
        /* (Decrement, Increment, FindSetLeftBit, FindSetRightBit, Not) */
        If (F64)
        {
            Concatenate (__METHOD__, "-m64l", Local0)
            SRMT (Local0)
            M64L (Local0)
        }
        Else
        {
            Concatenate (__METHOD__, "-m32l", Local0)
            SRMT (Local0)
            M32L (Local0)
        }

        /* Buffer Field to Integer conversion of the Buffer Field sole operand */
        /* of the LNot Logical Integer operator */
        Concatenate (__METHOD__, "-m03a", Local0)
        SRMT (Local0)
        M03A (Local0)
        /* Buffer Field to Integer conversion of the Buffer Field sole operand */
        /* of the FromBCD and ToBCD conversion operators */
        If (F64)
        {
            Concatenate (__METHOD__, "-m64m", Local0)
            SRMT (Local0)
            M64M (Local0)
        }
        Else
        {
            Concatenate (__METHOD__, "-m32m", Local0)
            SRMT (Local0)
            M32M (Local0)
        }

        /* Buffer Field to Integer conversion of each Buffer operand */
        /* of the 2-parameter Integer arithmetic operators */
        /* Add, And, Divide, Mod, Multiply, NAnd, NOr, Or, */
        /* ShiftLeft, ShiftRight, Subtract, Xor */
        If (F64)
        {
            M64N (Concatenate (__METHOD__, "-m64n"))
        }
        Else
        {
            M32N (Concatenate (__METHOD__, "-m32n"))
        }

        /* Buffer Field to Integer conversion of each Buffer operand */
        /* of the 2-parameter Logical Integer operators LAnd and LOr */
        If (F64)
        {
            M64O (Concatenate (__METHOD__, "-m64o"))
        }
        Else
        {
            M32O (Concatenate (__METHOD__, "-m32o"))
        }

        /* Buffer Field to Integer conversion of the Buffer Field second operand */
        /* of Logical operators when the first operand is evaluated as Integer */
        /* (LEqual, LGreater, LGreaterEqual, LLess, LLessEqual, LNotEqual) */
        Concatenate (__METHOD__, "-m065", Local0)
        SRMT (Local0)
        M065 (Local0)
        If (F64)
        {
            Concatenate (__METHOD__, "-m64p", Local0)
            SRMT (Local0)
            M64P (Local0)
        }
        Else
        {
            Concatenate (__METHOD__, "-m32p", Local0)
            SRMT (Local0)
            M32P (Local0)
        }

        /* Buffer Field to Integer intermediate conversion of the Buffer Field */
        /* second operand of Concatenate operator in case the first one is Integer */
        If (F64)
        {
            Concatenate (__METHOD__, "-m64q", Local0)
            SRMT (Local0)
            M64Q (Local0)
        }
        Else
        {
            Concatenate (__METHOD__, "-m32q", Local0)
            SRMT (Local0)
            M32Q (Local0)
        }

        /* Buffer Field to Integer conversion of the Buffer Field Length */
        /* (second) operand of the ToString operator */
        Concatenate (__METHOD__, "-m066", Local0)
        SRMT (Local0)
        M066 (Local0)
        If (F64)
        {
            Concatenate (__METHOD__, "-m64r", Local0)
            SRMT (Local0)
            M64R (Local0)
        }
        Else
        {
            Concatenate (__METHOD__, "-m32r", Local0)
            SRMT (Local0)
            M32R (Local0)
        }

        /* Buffer Field to Integer conversion of the Buffer Field Index */
        /* (second) operand of the Index operator */
        Concatenate (__METHOD__, "-m067", Local0)
        SRMT (Local0)
        M067 (Local0)
        /* Buffer Field to Integer conversion of the Buffer Field Arg (third) */
        /* operand of the Fatal operator */
        /* (it can only be checked an exception does not occur) */
        Concatenate (__METHOD__, "-m068", Local0)
        SRMT (Local0)
        M068 (Local0)
        /* Buffer Field to Integer conversion of the Buffer Field Index */
        /* and Length operands of the Mid operator */
        Concatenate (__METHOD__, "-m069", Local0)
        SRMT (Local0)
        M069 (Local0)
        If (F64)
        {
            Concatenate (__METHOD__, "-m64s", Local0)
            SRMT (Local0)
            M64S (Local0)
        }
        Else
        {
            Concatenate (__METHOD__, "-m32s", Local0)
            SRMT (Local0)
            M32S (Local0)
        }

        /* Buffer Field to Integer conversion of the Buffer Field StartIndex */
        /* operand of the Match operator */
        Concatenate (__METHOD__, "-m06a", Local0)
        SRMT (Local0)
        M06A (Local0)
        /* Buffer Field to Integer conversion of the Buffer Field sole operand */
        /* of the Method execution control operators (Sleep, Stall) */
        Concatenate (__METHOD__, "-m06b", Local0)
        SRMT (Local0)
        M06B (Local0)
        /* Buffer Field to Integer conversion of the Buffer Field TimeoutValue */
        /* (second) operand of the Wait operator */
        Concatenate (__METHOD__, "-m06d", Local0)
        SRMT (Local0)
        M06D (Local0)
        /* Buffer Field to Integer conversion of the Buffer Field value */
        /* of Predicate of the Method execution control statements */
        /* (If, ElseIf, While) */
        Concatenate (__METHOD__, "-m06e", Local0)
        SRMT (Local0)
        If (Y364)
        {
            M06E (Local0)
        }
        Else
        {
            BLCK ()
        }

        /* Check Buffer Fields consistency */

        Concatenate (__METHOD__, "-m074", Local0)
        SRMT (Local0)
        M074 (Local0)
    }
