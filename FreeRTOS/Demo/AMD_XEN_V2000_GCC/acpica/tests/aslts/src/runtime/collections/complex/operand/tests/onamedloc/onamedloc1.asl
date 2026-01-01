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
     * Check implicit conversion being applied to Named Objects
     * in the current Scope of the Global ACPI namespace.
     */
    Name (Z088, 0x58)
    Method (M613, 0, Serialized)
    {
        /* Integer to String implicit conversion Cases. */
        /* Integer to String conversion of the Integer second operand of */
        /* Logical operators when the first operand is evaluated as String. */
        /* LEqual LGreater LGreaterEqual LLess LLessEqual LNotEqual */
        Method (M640, 1, Serialized)
        {
            Name (I604, 0xFE7CB391D650A284)
            /* LEqual */

            Local0 = ("FE7CB391D650A284" == I604)
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = ("fE7CB391D650A284" == I604)
            M600 (Arg0, 0x01, Local0, Zero)
            Local0 = (AUS4 == I604)
            M600 (Arg0, 0x02, Local0, Ones)
            Local0 = (AUS5 == I604)
            M600 (Arg0, 0x03, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUS4)) == I604)
                M600 (Arg0, 0x04, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUS5)) == I604)
                M600 (Arg0, 0x05, Local0, Zero)
            }

            Local0 = (DerefOf (PAUS [0x04]) == I604)
            M600 (Arg0, 0x06, Local0, Ones)
            Local0 = (DerefOf (PAUS [0x05]) == I604)
            M600 (Arg0, 0x07, Local0, Zero)
            /* Method returns String */

            Local0 = (M601 (0x02, 0x04) == I604)
            M600 (Arg0, 0x08, Local0, Ones)
            Local0 = (M601 (0x02, 0x05) == I604)
            M600 (Arg0, 0x09, Local0, Zero)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x02, 0x04, 0x01)) == I604)
                M600 (Arg0, 0x0A, Local0, Ones)
                Local0 = (DerefOf (M602 (0x02, 0x05, 0x01)) == I604)
                M600 (Arg0, 0x0B, Local0, Zero)
            }

            /* LGreater */

            Local0 = ("FE7CB391D650A284" > I604)
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = ("fE7CB391D650A284" > I604)
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = ("FE7CB391D650A28 " > I604)
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = ("FE7CB391D650A284q" > I604)
            M600 (Arg0, 0x0F, Local0, Ones)
            Local0 = (AUS4 > I604)
            M600 (Arg0, 0x10, Local0, Zero)
            Local0 = (AUS5 > I604)
            M600 (Arg0, 0x11, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUS4)) > I604)
                M600 (Arg0, 0x12, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUS5)) > I604)
                M600 (Arg0, 0x13, Local0, Ones)
            }

            Local0 = (DerefOf (PAUS [0x04]) > I604)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (DerefOf (PAUS [0x05]) > I604)
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns String */

            Local0 = (M601 (0x02, 0x04) > I604)
            M600 (Arg0, 0x16, Local0, Zero)
            Local0 = (M601 (0x02, 0x05) > I604)
            M600 (Arg0, 0x17, Local0, Ones)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x02, 0x04, 0x01)) > I604)
                M600 (Arg0, 0x18, Local0, Zero)
                Local0 = (DerefOf (M602 (0x02, 0x05, 0x01)) > I604)
                M600 (Arg0, 0x19, Local0, Ones)
            }

            /* LGreaterEqual */

            Local0 = ("FE7CB391D650A284" >= I604)
            M600 (Arg0, 0x1A, Local0, Ones)
            Local0 = ("fE7CB391D650A284" >= I604)
            M600 (Arg0, 0x1B, Local0, Ones)
            Local0 = ("FE7CB391D650A28 " >= I604)
            M600 (Arg0, 0x1C, Local0, Zero)
            Local0 = ("FE7CB391D650A284q" >= I604)
            M600 (Arg0, 0x1D, Local0, Ones)
            Local0 = (AUS4 >= I604)
            M600 (Arg0, 0x1E, Local0, Ones)
            Local0 = (AUS5 >= I604)
            M600 (Arg0, 0x1F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUS4)) >= I604)
                M600 (Arg0, 0x20, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUS5)) >= I604)
                M600 (Arg0, 0x21, Local0, Ones)
            }

            Local0 = (DerefOf (PAUS [0x04]) >= I604)
            M600 (Arg0, 0x22, Local0, Ones)
            Local0 = (DerefOf (PAUS [0x05]) >= I604)
            M600 (Arg0, 0x23, Local0, Ones)
            /* Method returns String */

            Local0 = (M601 (0x02, 0x04) >= I604)
            M600 (Arg0, 0x24, Local0, Ones)
            Local0 = (M601 (0x02, 0x05) >= I604)
            M600 (Arg0, 0x25, Local0, Ones)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x02, 0x04, 0x01)) >= I604)
                M600 (Arg0, 0x26, Local0, Ones)
                Local0 = (DerefOf (M602 (0x02, 0x05, 0x01)) >= I604)
                M600 (Arg0, 0x27, Local0, Ones)
            }

            /* LLess */

            Local0 = ("FE7CB391D650A284" < I604)
            M600 (Arg0, 0x28, Local0, Zero)
            Local0 = ("fE7CB391D650A284" < I604)
            M600 (Arg0, 0x29, Local0, Zero)
            Local0 = ("FE7CB391D650A28 " < I604)
            M600 (Arg0, 0x2A, Local0, Ones)
            Local0 = ("FE7CB391D650A284q" < I604)
            M600 (Arg0, 0x2B, Local0, Zero)
            Local0 = (AUS4 < I604)
            M600 (Arg0, 0x2C, Local0, Zero)
            Local0 = (AUS5 < I604)
            M600 (Arg0, 0x2D, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUS4)) < I604)
                M600 (Arg0, 0x2E, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUS5)) < I604)
                M600 (Arg0, 0x2F, Local0, Zero)
            }

            Local0 = (DerefOf (PAUS [0x04]) < I604)
            M600 (Arg0, 0x30, Local0, Zero)
            Local0 = (DerefOf (PAUS [0x05]) < I604)
            M600 (Arg0, 0x31, Local0, Zero)
            /* Method returns String */

            Local0 = (M601 (0x02, 0x04) < I604)
            M600 (Arg0, 0x32, Local0, Zero)
            Local0 = (M601 (0x02, 0x05) < I604)
            M600 (Arg0, 0x33, Local0, Zero)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x02, 0x04, 0x01)) < I604)
                M600 (Arg0, 0x34, Local0, Zero)
                Local0 = (DerefOf (M602 (0x02, 0x05, 0x01)) < I604)
                M600 (Arg0, 0x35, Local0, Zero)
            }

            /* LLessEqual */

            Local0 = ("FE7CB391D650A284" <= I604)
            M600 (Arg0, 0x36, Local0, Ones)
            Local0 = ("fE7CB391D650A284" <= I604)
            M600 (Arg0, 0x37, Local0, Zero)
            Local0 = ("FE7CB391D650A28 " <= I604)
            M600 (Arg0, 0x38, Local0, Ones)
            Local0 = ("FE7CB391D650A284q" <= I604)
            M600 (Arg0, 0x39, Local0, Zero)
            Local0 = (AUS4 <= I604)
            M600 (Arg0, 0x3A, Local0, Ones)
            Local0 = (AUS5 <= I604)
            M600 (Arg0, 0x3B, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUS4)) <= I604)
                M600 (Arg0, 0x3C, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUS5)) <= I604)
                M600 (Arg0, 0x3D, Local0, Zero)
            }

            Local0 = (DerefOf (PAUS [0x04]) <= I604)
            M600 (Arg0, 0x3E, Local0, Ones)
            Local0 = (DerefOf (PAUS [0x05]) <= I604)
            M600 (Arg0, 0x3F, Local0, Zero)
            /* Method returns String */

            Local0 = (M601 (0x02, 0x04) <= I604)
            M600 (Arg0, 0x40, Local0, Ones)
            Local0 = (M601 (0x02, 0x05) <= I604)
            M600 (Arg0, 0x41, Local0, Zero)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x02, 0x04, 0x01)) <= I604)
                M600 (Arg0, 0x42, Local0, Ones)
                Local0 = (DerefOf (M602 (0x02, 0x05, 0x01)) <= I604)
                M600 (Arg0, 0x43, Local0, Zero)
            }

            /* LNotEqual */

            Local0 = ("FE7CB391D650A284" != I604)
            M600 (Arg0, 0x44, Local0, Zero)
            Local0 = ("fE7CB391D650A284" != I604)
            M600 (Arg0, 0x45, Local0, Ones)
            Local0 = ("FE7CB391D650A28 " != I604)
            M600 (Arg0, 0x46, Local0, Ones)
            Local0 = ("FE7CB391D650A284q" != I604)
            M600 (Arg0, 0x47, Local0, Ones)
            Local0 = (AUS4 != I604)
            M600 (Arg0, 0x48, Local0, Zero)
            Local0 = (AUS5 != I604)
            M600 (Arg0, 0x49, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUS4)) != I604)
                M600 (Arg0, 0x4A, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUS5)) != I604)
                M600 (Arg0, 0x4B, Local0, Ones)
            }

            Local0 = (DerefOf (PAUS [0x04]) != I604)
            M600 (Arg0, 0x4C, Local0, Zero)
            Local0 = (DerefOf (PAUS [0x05]) != I604)
            M600 (Arg0, 0x4D, Local0, Ones)
            /* Method returns String */

            Local0 = (M601 (0x02, 0x04) != I604)
            M600 (Arg0, 0x4E, Local0, Zero)
            Local0 = (M601 (0x02, 0x05) != I604)
            M600 (Arg0, 0x4F, Local0, Ones)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x02, 0x04, 0x01)) != I604)
                M600 (Arg0, 0x50, Local0, Zero)
                Local0 = (DerefOf (M602 (0x02, 0x05, 0x01)) != I604)
                M600 (Arg0, 0x51, Local0, Ones)
            }
        }

        Method (M320, 1, Serialized)
        {
            Name (I603, 0xC179B3FE)
            /* LEqual */

            Local0 = ("C179B3FE" == I603)
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = ("c179B3FE" == I603)
            M600 (Arg0, 0x01, Local0, Zero)
            Local0 = (AUS3 == I603)
            M600 (Arg0, 0x02, Local0, Ones)
            Local0 = (AUS2 == I603)
            M600 (Arg0, 0x03, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUS3)) == I603)
                M600 (Arg0, 0x04, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUS2)) == I603)
                M600 (Arg0, 0x05, Local0, Zero)
            }

            Local0 = (DerefOf (PAUS [0x03]) == I603)
            M600 (Arg0, 0x06, Local0, Ones)
            Local0 = (DerefOf (PAUS [0x02]) == I603)
            M600 (Arg0, 0x07, Local0, Zero)
            /* Method returns String */

            Local0 = (M601 (0x02, 0x03) == I603)
            M600 (Arg0, 0x08, Local0, Ones)
            Local0 = (M601 (0x02, 0x02) == I603)
            M600 (Arg0, 0x09, Local0, Zero)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x02, 0x03, 0x01)) == I603)
                M600 (Arg0, 0x0A, Local0, Ones)
                Local0 = (DerefOf (M602 (0x02, 0x02, 0x01)) == I603)
                M600 (Arg0, 0x0B, Local0, Zero)
            }

            /* LGreater */

            Local0 = ("C179B3FE" > I603)
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = ("c179B3FE" > I603)
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = ("C179B3F " > I603)
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = ("C179B3FEq" > I603)
            M600 (Arg0, 0x0F, Local0, Ones)
            Local0 = (AUS3 > I603)
            M600 (Arg0, 0x10, Local0, Zero)
            Local0 = (AUS2 > I603)
            M600 (Arg0, 0x11, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUS3)) > I603)
                M600 (Arg0, 0x12, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUS2)) > I603)
                M600 (Arg0, 0x13, Local0, Ones)
            }

            Local0 = (DerefOf (PAUS [0x03]) > I603)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (DerefOf (PAUS [0x02]) > I603)
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns String */

            Local0 = (M601 (0x02, 0x03) > I603)
            M600 (Arg0, 0x16, Local0, Zero)
            Local0 = (M601 (0x02, 0x02) > I603)
            M600 (Arg0, 0x17, Local0, Ones)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x02, 0x03, 0x01)) > I603)
                M600 (Arg0, 0x18, Local0, Zero)
                Local0 = (DerefOf (M602 (0x02, 0x02, 0x01)) > I603)
                M600 (Arg0, 0x19, Local0, Ones)
            }

            /* LGreaterEqual */

            Local0 = ("C179B3FE" >= I603)
            M600 (Arg0, 0x1A, Local0, Ones)
            Local0 = ("c179B3FE" >= I603)
            M600 (Arg0, 0x1B, Local0, Ones)
            Local0 = ("C179B3F " >= I603)
            M600 (Arg0, 0x1C, Local0, Zero)
            Local0 = ("C179B3FEq" >= I603)
            M600 (Arg0, 0x1D, Local0, Ones)
            Local0 = (AUS3 >= I603)
            M600 (Arg0, 0x1E, Local0, Ones)
            Local0 = (AUS2 >= I603)
            M600 (Arg0, 0x1F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUS3)) >= I603)
                M600 (Arg0, 0x20, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUS2)) >= I603)
                M600 (Arg0, 0x21, Local0, Ones)
            }

            Local0 = (DerefOf (PAUS [0x03]) >= I603)
            M600 (Arg0, 0x22, Local0, Ones)
            Local0 = (DerefOf (PAUS [0x02]) >= I603)
            M600 (Arg0, 0x23, Local0, Ones)
            /* Method returns String */

            Local0 = (M601 (0x02, 0x03) >= I603)
            M600 (Arg0, 0x24, Local0, Ones)
            Local0 = (M601 (0x02, 0x02) >= I603)
            M600 (Arg0, 0x25, Local0, Ones)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x02, 0x03, 0x01)) >= I603)
                M600 (Arg0, 0x26, Local0, Ones)
                Local0 = (DerefOf (M602 (0x02, 0x02, 0x01)) >= I603)
                M600 (Arg0, 0x27, Local0, Ones)
            }

            /* LLess */

            Local0 = ("C179B3FE" < I603)
            M600 (Arg0, 0x28, Local0, Zero)
            Local0 = ("c179B3FE" < I603)
            M600 (Arg0, 0x29, Local0, Zero)
            Local0 = ("C179B3F " < I603)
            M600 (Arg0, 0x2A, Local0, Ones)
            Local0 = ("C179B3FEq" < I603)
            M600 (Arg0, 0x2B, Local0, Zero)
            Local0 = (AUS3 < I603)
            M600 (Arg0, 0x2C, Local0, Zero)
            Local0 = (AUS2 < I603)
            M600 (Arg0, 0x2D, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUS3)) < I603)
                M600 (Arg0, 0x2E, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUS2)) < I603)
                M600 (Arg0, 0x2F, Local0, Zero)
            }

            Local0 = (DerefOf (PAUS [0x03]) < I603)
            M600 (Arg0, 0x30, Local0, Zero)
            Local0 = (DerefOf (PAUS [0x02]) < I603)
            M600 (Arg0, 0x31, Local0, Zero)
            /* Method returns String */

            Local0 = (M601 (0x02, 0x03) < I603)
            M600 (Arg0, 0x32, Local0, Zero)
            Local0 = (M601 (0x02, 0x02) < I603)
            M600 (Arg0, 0x33, Local0, Zero)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x02, 0x03, 0x01)) < I603)
                M600 (Arg0, 0x34, Local0, Zero)
                Local0 = (DerefOf (M602 (0x02, 0x02, 0x01)) < I603)
                M600 (Arg0, 0x35, Local0, Zero)
            }

            /* LLessEqual */

            Local0 = ("C179B3FE" <= I603)
            M600 (Arg0, 0x36, Local0, Ones)
            Local0 = ("c179B3FE" <= I603)
            M600 (Arg0, 0x37, Local0, Zero)
            Local0 = ("C179B3F " <= I603)
            M600 (Arg0, 0x38, Local0, Ones)
            Local0 = ("C179B3FEq" <= I603)
            M600 (Arg0, 0x39, Local0, Zero)
            Local0 = (AUS3 <= I603)
            M600 (Arg0, 0x3A, Local0, Ones)
            Local0 = (AUS2 <= I603)
            M600 (Arg0, 0x3B, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUS3)) <= I603)
                M600 (Arg0, 0x3C, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUS2)) <= I603)
                M600 (Arg0, 0x3D, Local0, Zero)
            }

            Local0 = (DerefOf (PAUS [0x03]) <= I603)
            M600 (Arg0, 0x3E, Local0, Ones)
            Local0 = (DerefOf (PAUS [0x02]) <= I603)
            M600 (Arg0, 0x3F, Local0, Zero)
            /* Method returns String */

            Local0 = (M601 (0x02, 0x03) <= I603)
            M600 (Arg0, 0x40, Local0, Ones)
            Local0 = (M601 (0x02, 0x02) <= I603)
            M600 (Arg0, 0x41, Local0, Zero)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x02, 0x03, 0x01)) <= I603)
                M600 (Arg0, 0x42, Local0, Ones)
                Local0 = (DerefOf (M602 (0x02, 0x02, 0x01)) <= I603)
                M600 (Arg0, 0x43, Local0, Zero)
            }

            /* LNotEqual */

            Local0 = ("C179B3FE" != I603)
            M600 (Arg0, 0x44, Local0, Zero)
            Local0 = ("c179B3FE" != I603)
            M600 (Arg0, 0x45, Local0, Ones)
            Local0 = ("C179B3F " != I603)
            M600 (Arg0, 0x46, Local0, Ones)
            Local0 = ("C179B3FEq" != I603)
            M600 (Arg0, 0x47, Local0, Ones)
            Local0 = (AUS3 != I603)
            M600 (Arg0, 0x48, Local0, Zero)
            Local0 = (AUS2 != I603)
            M600 (Arg0, 0x49, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUS3)) != I603)
                M600 (Arg0, 0x4A, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUS2)) != I603)
                M600 (Arg0, 0x4B, Local0, Ones)
            }

            Local0 = (DerefOf (PAUS [0x03]) != I603)
            M600 (Arg0, 0x4C, Local0, Zero)
            Local0 = (DerefOf (PAUS [0x02]) != I603)
            M600 (Arg0, 0x4D, Local0, Ones)
            /* Method returns String */

            Local0 = (M601 (0x02, 0x03) != I603)
            M600 (Arg0, 0x4E, Local0, Zero)
            Local0 = (M601 (0x02, 0x02) != I603)
            M600 (Arg0, 0x4F, Local0, Ones)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x02, 0x03, 0x01)) != I603)
                M600 (Arg0, 0x50, Local0, Zero)
                Local0 = (DerefOf (M602 (0x02, 0x02, 0x01)) != I603)
                M600 (Arg0, 0x51, Local0, Ones)
            }
        }

        /* Integer to String conversion of the Integer second operand of */
        /* Concatenate operator when the first operand is evaluated as String */
        Method (M641, 1, Serialized)
        {
            Name (I604, 0xFE7CB391D650A284)
            Local0 = Concatenate ("", I604)
            M600 (Arg0, 0x00, Local0, BS10)
            Local0 = Concatenate ("1234q", I604)
            M600 (Arg0, 0x01, Local0, BS11)
            Local0 = Concatenate (AUS0, I604)
            M600 (Arg0, 0x02, Local0, BS10)
            Local0 = Concatenate (AUS1, I604)
            M600 (Arg0, 0x03, Local0, BS11)
            If (Y078)
            {
                Local0 = Concatenate (DerefOf (RefOf (AUS0)), I604)
                M600 (Arg0, 0x04, Local0, BS10)
                Local0 = Concatenate (DerefOf (RefOf (AUS1)), I604)
                M600 (Arg0, 0x05, Local0, BS11)
            }

            Local0 = Concatenate (DerefOf (PAUS [0x00]), I604)
            M600 (Arg0, 0x06, Local0, BS10)
            Local0 = Concatenate (DerefOf (PAUS [0x01]), I604)
            M600 (Arg0, 0x07, Local0, BS11)
            /* Method returns String */

            Local0 = Concatenate (M601 (0x02, 0x00), I604)
            M600 (Arg0, 0x08, Local0, BS10)
            Local0 = Concatenate (M601 (0x02, 0x01), I604)
            M600 (Arg0, 0x09, Local0, BS11)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = Concatenate (DerefOf (M602 (0x02, 0x00, 0x01)), I604)
                M600 (Arg0, 0x0A, Local0, BS10)
                Local0 = Concatenate (DerefOf (M602 (0x02, 0x01, 0x01)), I604)
                M600 (Arg0, 0x0B, Local0, BS11)
            }

            Concatenate ("", I604, Local0)
            M600 (Arg0, 0x0C, Local0, BS10)
            Concatenate ("1234q", I604, Local0)
            M600 (Arg0, 0x0D, Local0, BS11)
            Concatenate (AUS0, I604, Local0)
            M600 (Arg0, 0x0E, Local0, BS10)
            Concatenate (AUS1, I604, Local0)
            M600 (Arg0, 0x0F, Local0, BS11)
            If (Y078)
            {
                Concatenate (DerefOf (RefOf (AUS0)), I604, Local0)
                M600 (Arg0, 0x10, Local0, BS10)
                Concatenate (DerefOf (RefOf (AUS1)), I604, Local0)
                M600 (Arg0, 0x11, Local0, BS11)
            }

            Concatenate (DerefOf (PAUS [0x00]), I604, Local0)
            M600 (Arg0, 0x12, Local0, BS10)
            Concatenate (DerefOf (PAUS [0x01]), I604, Local0)
            M600 (Arg0, 0x13, Local0, BS11)
            /* Method returns String */

            Concatenate (M601 (0x02, 0x00), I604, Local0)
            M600 (Arg0, 0x14, Local0, BS10)
            Concatenate (M601 (0x02, 0x01), I604, Local0)
            M600 (Arg0, 0x15, Local0, BS11)
            /* Method returns Reference to String */

            If (Y500)
            {
                Concatenate (DerefOf (M602 (0x02, 0x00, 0x01)), I604, Local0)
                M600 (Arg0, 0x16, Local0, BS10)
                Concatenate (DerefOf (M602 (0x02, 0x01, 0x01)), I604, Local0)
                M600 (Arg0, 0x17, Local0, BS11)
            }
        }

        Method (M321, 1, Serialized)
        {
            Name (I603, 0xC179B3FE)
            Name (I604, 0xFE7CB391D650A284)
            Local0 = Concatenate ("", I603)
            M600 (Arg0, 0x00, Local0, BS12)
            Local0 = Concatenate ("1234q", I603)
            M600 (Arg0, 0x01, Local0, BS13)
            Local0 = Concatenate (AUS0, I603)
            M600 (Arg0, 0x02, Local0, BS12)
            Local0 = Concatenate (AUS1, I603)
            M600 (Arg0, 0x03, Local0, BS13)
            If (Y078)
            {
                Local0 = Concatenate (DerefOf (RefOf (AUS0)), I603)
                M600 (Arg0, 0x04, Local0, BS12)
                Local0 = Concatenate (DerefOf (RefOf (AUS1)), I603)
                M600 (Arg0, 0x05, Local0, BS13)
            }

            Local0 = Concatenate (DerefOf (PAUS [0x00]), I603)
            M600 (Arg0, 0x06, Local0, BS12)
            Local0 = Concatenate (DerefOf (PAUS [0x01]), I603)
            M600 (Arg0, 0x07, Local0, BS13)
            /* Method returns String */

            Local0 = Concatenate (M601 (0x02, 0x00), I603)
            M600 (Arg0, 0x08, Local0, BS12)
            Local0 = Concatenate (M601 (0x02, 0x01), I603)
            M600 (Arg0, 0x09, Local0, BS13)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = Concatenate (DerefOf (M602 (0x02, 0x00, 0x01)), I603)
                M600 (Arg0, 0x0A, Local0, BS12)
                Local0 = Concatenate (DerefOf (M602 (0x02, 0x01, 0x01)), I603)
                M600 (Arg0, 0x0B, Local0, BS13)
            }

            Local0 = Concatenate ("", I604)
            M600 (Arg0, 0x0C, Local0, BS14)
            Local0 = Concatenate ("1234q", I604)
            M600 (Arg0, 0x0D, Local0, BS15)
            Concatenate ("", I603, Local0)
            M600 (Arg0, 0x0E, Local0, BS12)
            Concatenate ("1234q", I603, Local0)
            M600 (Arg0, 0x0F, Local0, BS13)
            Concatenate (AUS0, I603, Local0)
            M600 (Arg0, 0x10, Local0, BS12)
            Concatenate (AUS1, I603, Local0)
            M600 (Arg0, 0x11, Local0, BS13)
            If (Y078)
            {
                Concatenate (DerefOf (RefOf (AUS0)), I603, Local0)
                M600 (Arg0, 0x12, Local0, BS12)
                Concatenate (DerefOf (RefOf (AUS1)), I603, Local0)
                M600 (Arg0, 0x13, Local0, BS13)
            }

            Concatenate (DerefOf (PAUS [0x00]), I603, Local0)
            M600 (Arg0, 0x14, Local0, BS12)
            Concatenate (DerefOf (PAUS [0x01]), I603, Local0)
            M600 (Arg0, 0x15, Local0, BS13)
            /* Method returns String */

            Concatenate (M601 (0x02, 0x00), I603, Local0)
            M600 (Arg0, 0x16, Local0, BS12)
            Concatenate (M601 (0x02, 0x01), I603, Local0)
            M600 (Arg0, 0x17, Local0, BS13)
            /* Method returns Reference to String */

            If (Y500)
            {
                Concatenate (DerefOf (M602 (0x02, 0x00, 0x01)), I603, Local0)
                M600 (Arg0, 0x18, Local0, BS12)
                Concatenate (DerefOf (M602 (0x02, 0x01, 0x01)), I603, Local0)
                M600 (Arg0, 0x19, Local0, BS13)
            }

            Concatenate ("", I604, Local0)
            M600 (Arg0, 0x1A, Local0, BS14)
            Concatenate ("1234q", I604, Local0)
            M600 (Arg0, 0x1B, Local0, BS15)
        }

        /*	Method(m642, 1) */
        /*	Method(m322, 1) */
        /*	Method(m643, 1) */
        /*	Method(m323, 1) */
        /* Integer to Buffer implicit conversion Cases. */
        /* Integer to Buffer conversion of the Integer second operand of */
        /* Logical operators when the first operand is evaluated as Buffer */
        /* (LEqual, LGreater, LGreaterEqual, LLess, LLessEqual, LNotEqual) */
        Method (M644, 1, Serialized)
        {
            Name (I604, 0xFE7CB391D650A284)
            /* LEqual */

            Local0 = (Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                    } == I604)
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFF   // ..P...|.
                    } == I604)
            M600 (Arg0, 0x01, Local0, Zero)
            Local0 = (AUB4 == I604)
            M600 (Arg0, 0x02, Local0, Ones)
            Local0 = (AUB3 == I604)
            M600 (Arg0, 0x03, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB4)) == I604)
                M600 (Arg0, 0x04, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUB3)) == I604)
                M600 (Arg0, 0x05, Local0, Zero)
            }

            Local0 = (DerefOf (PAUB [0x04]) == I604)
            M600 (Arg0, 0x06, Local0, Ones)
            Local0 = (DerefOf (PAUB [0x03]) == I604)
            M600 (Arg0, 0x07, Local0, Zero)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x04) == I604)
            M600 (Arg0, 0x08, Local0, Ones)
            Local0 = (M601 (0x03, 0x03) == I604)
            M600 (Arg0, 0x09, Local0, Zero)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x04, 0x01)) == I604)
                M600 (Arg0, 0x0A, Local0, Ones)
                Local0 = (DerefOf (M602 (0x03, 0x03, 0x01)) == I604)
                M600 (Arg0, 0x0B, Local0, Zero)
            }

            /* LGreater */

            Local0 = (Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                    } > I604)
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = (Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFF   // ..P...|.
                    } > I604)
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFD   // ..P...|.
                    } > I604)
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = (Buffer (0x09)
                    {
                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                        /* 0008 */  0x01                                             // .
                    } > I604)
            M600 (Arg0, 0x0F, Local0, Ones)
            Local0 = (AUB4 > I604)
            M600 (Arg0, 0x10, Local0, Zero)
            Local0 = (AUB5 > I604)
            M600 (Arg0, 0x11, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB4)) > I604)
                M600 (Arg0, 0x12, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUB5)) > I604)
                M600 (Arg0, 0x13, Local0, Ones)
            }

            Local0 = (DerefOf (PAUB [0x04]) > I604)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (DerefOf (PAUB [0x05]) > I604)
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x04) > I604)
            M600 (Arg0, 0x16, Local0, Zero)
            Local0 = (M601 (0x03, 0x05) > I604)
            M600 (Arg0, 0x17, Local0, Ones)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x04, 0x01)) > I604)
                M600 (Arg0, 0x18, Local0, Zero)
                Local0 = (DerefOf (M602 (0x03, 0x05, 0x01)) > I604)
                M600 (Arg0, 0x19, Local0, Ones)
            }

            /* LGreaterEqual */

            Local0 = (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                        } >= I604)
            M600 (Arg0, 0x1A, Local0, Ones)
            Local0 = (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFF   // ..P...|.
                        } >= I604)
            M600 (Arg0, 0x1B, Local0, Ones)
            Local0 = (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFD   // ..P...|.
                        } >= I604)
            M600 (Arg0, 0x1C, Local0, Zero)
            Local0 = (Buffer (0x09)
                        {
                            /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                            /* 0008 */  0x01                                             // .
                        } >= I604)
            M600 (Arg0, 0x1D, Local0, Ones)
            Local0 = (AUB4 >= I604)
            M600 (Arg0, 0x1E, Local0, Ones)
            Local0 = (AUB5 >= I604)
            M600 (Arg0, 0x1F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB4)) >= I604)
                M600 (Arg0, 0x20, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUB5)) >= I604)
                M600 (Arg0, 0x21, Local0, Ones)
            }

            Local0 = (DerefOf (PAUB [0x04]) >= I604)
            M600 (Arg0, 0x22, Local0, Ones)
            Local0 = (DerefOf (PAUB [0x05]) >= I604)
            M600 (Arg0, 0x23, Local0, Ones)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x04) >= I604)
            M600 (Arg0, 0x24, Local0, Ones)
            Local0 = (M601 (0x03, 0x05) >= I604)
            M600 (Arg0, 0x25, Local0, Ones)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x04, 0x01)) >= I604)
                M600 (Arg0, 0x26, Local0, Ones)
                Local0 = (DerefOf (M602 (0x03, 0x05, 0x01)) >= I604)
                M600 (Arg0, 0x27, Local0, Ones)
            }

            /* LLess */

            Local0 = (Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                    } < I604)
            M600 (Arg0, 0x28, Local0, Zero)
            Local0 = (Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFF   // ..P...|.
                    } < I604)
            M600 (Arg0, 0x29, Local0, Zero)
            Local0 = (Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFD   // ..P...|.
                    } < I604)
            M600 (Arg0, 0x2A, Local0, Ones)
            Local0 = (Buffer (0x09)
                    {
                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                        /* 0008 */  0x01                                             // .
                    } < I604)
            M600 (Arg0, 0x2B, Local0, Zero)
            Local0 = (AUB4 < I604)
            M600 (Arg0, 0x2C, Local0, Zero)
            Local0 = (AUB5 < I604)
            M600 (Arg0, 0x2D, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB4)) < I604)
                M600 (Arg0, 0x2E, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUB5)) < I604)
                M600 (Arg0, 0x2F, Local0, Zero)
            }

            Local0 = (DerefOf (PAUB [0x04]) < I604)
            M600 (Arg0, 0x30, Local0, Zero)
            Local0 = (DerefOf (PAUB [0x05]) < I604)
            M600 (Arg0, 0x31, Local0, Zero)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x04) < I604)
            M600 (Arg0, 0x32, Local0, Zero)
            Local0 = (M601 (0x03, 0x05) < I604)
            M600 (Arg0, 0x33, Local0, Zero)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x04, 0x01)) < I604)
                M600 (Arg0, 0x34, Local0, Zero)
                Local0 = (DerefOf (M602 (0x03, 0x05, 0x01)) < I604)
                M600 (Arg0, 0x35, Local0, Zero)
            }

            /* LLessEqual */

            Local0 = (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                        } <= I604)
            M600 (Arg0, 0x36, Local0, Ones)
            Local0 = (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFF   // ..P...|.
                        } <= I604)
            M600 (Arg0, 0x37, Local0, Zero)
            Local0 = (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFD   // ..P...|.
                        } <= I604)
            M600 (Arg0, 0x38, Local0, Ones)
            Local0 = (Buffer (0x09)
                        {
                            /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                            /* 0008 */  0x01                                             // .
                        } <= I604)
            M600 (Arg0, 0x39, Local0, Zero)
            Local0 = (AUB4 <= I604)
            M600 (Arg0, 0x3A, Local0, Ones)
            Local0 = (AUB5 <= I604)
            M600 (Arg0, 0x3B, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB4)) <= I604)
                M600 (Arg0, 0x3C, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUB5)) <= I604)
                M600 (Arg0, 0x3D, Local0, Zero)
            }

            Local0 = (DerefOf (PAUB [0x04]) <= I604)
            M600 (Arg0, 0x3E, Local0, Ones)
            Local0 = (DerefOf (PAUB [0x05]) <= I604)
            M600 (Arg0, 0x3F, Local0, Zero)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x04) <= I604)
            M600 (Arg0, 0x40, Local0, Ones)
            Local0 = (M601 (0x03, 0x05) <= I604)
            M600 (Arg0, 0x41, Local0, Zero)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x04, 0x01)) <= I604)
                M600 (Arg0, 0x42, Local0, Ones)
                Local0 = (DerefOf (M602 (0x03, 0x05, 0x01)) <= I604)
                M600 (Arg0, 0x43, Local0, Zero)
            }

            /* LNotEqual */

            Local0 = (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                        } != I604)
            M600 (Arg0, 0x44, Local0, Zero)
            Local0 = (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFF   // ..P...|.
                        } != I604)
            M600 (Arg0, 0x45, Local0, Ones)
            Local0 = (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFD   // ..P...|.
                        } != I604)
            M600 (Arg0, 0x46, Local0, Ones)
            Local0 = (Buffer (0x09)
                        {
                            /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                            /* 0008 */  0x01                                             // .
                        } != I604)
            M600 (Arg0, 0x47, Local0, Ones)
            Local0 = (AUB4 != I604)
            M600 (Arg0, 0x48, Local0, Zero)
            Local0 = (AUB5 != I604)
            M600 (Arg0, 0x49, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB4)) != I604)
                M600 (Arg0, 0x4A, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUB5)) != I604)
                M600 (Arg0, 0x4B, Local0, Ones)
            }

            Local0 = (DerefOf (PAUB [0x04]) != I604)
            M600 (Arg0, 0x4C, Local0, Zero)
            Local0 = (DerefOf (PAUB [0x05]) != I604)
            M600 (Arg0, 0x4D, Local0, Ones)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x04) != I604)
            M600 (Arg0, 0x4E, Local0, Zero)
            Local0 = (M601 (0x03, 0x05) != I604)
            M600 (Arg0, 0x4F, Local0, Ones)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x04, 0x01)) != I604)
                M600 (Arg0, 0x50, Local0, Zero)
                Local0 = (DerefOf (M602 (0x03, 0x05, 0x01)) != I604)
                M600 (Arg0, 0x51, Local0, Ones)
            }
        }

        Method (M324, 1, Serialized)
        {
            Name (I603, 0xC179B3FE)
            /* LEqual */

            Local0 = (Buffer (0x04)
                    {
                         0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                    } == I603)
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (Buffer (0x04)
                    {
                         0xFE, 0xB3, 0x79, 0xC0                           // ..y.
                    } == I603)
            M600 (Arg0, 0x01, Local0, Zero)
            Local0 = (AUB3 == I603)
            M600 (Arg0, 0x02, Local0, Ones)
            Local0 = (AUB2 == I603)
            M600 (Arg0, 0x03, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB3)) == I603)
                M600 (Arg0, 0x04, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUB2)) == I603)
                M600 (Arg0, 0x05, Local0, Zero)
            }

            Local0 = (DerefOf (PAUB [0x03]) == I603)
            M600 (Arg0, 0x06, Local0, Ones)
            Local0 = (DerefOf (PAUB [0x02]) == I603)
            M600 (Arg0, 0x07, Local0, Zero)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x03) == I603)
            M600 (Arg0, 0x08, Local0, Ones)
            Local0 = (M601 (0x03, 0x02) == I603)
            M600 (Arg0, 0x09, Local0, Zero)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x03, 0x01)) == I603)
                M600 (Arg0, 0x0A, Local0, Ones)
                Local0 = (DerefOf (M602 (0x03, 0x02, 0x01)) == I603)
                M600 (Arg0, 0x0B, Local0, Zero)
            }

            /* LGreater */

            Local0 = (Buffer (0x04)
                    {
                         0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                    } > I603)
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = (Buffer (0x04)
                    {
                         0xFE, 0xB3, 0x79, 0xC2                           // ..y.
                    } > I603)
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (Buffer (0x04)
                    {
                         0xFE, 0xB3, 0x79, 0xC0                           // ..y.
                    } > I603)
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = (Buffer (0x05)
                    {
                         0xFE, 0xB3, 0x79, 0xC1, 0x01                     // ..y..
                    } > I603)
            M600 (Arg0, 0x0F, Local0, Ones)
            Local0 = (AUB3 > I603)
            M600 (Arg0, 0x10, Local0, Zero)
            Local0 = (AUB2 > I603)
            M600 (Arg0, 0x11, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB3)) > I603)
                M600 (Arg0, 0x12, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUB2)) > I603)
                M600 (Arg0, 0x13, Local0, Ones)
            }

            Local0 = (DerefOf (PAUB [0x03]) > I603)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (DerefOf (PAUB [0x02]) > I603)
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x03) > I603)
            M600 (Arg0, 0x16, Local0, Zero)
            Local0 = (M601 (0x03, 0x02) > I603)
            M600 (Arg0, 0x17, Local0, Ones)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x03, 0x01)) > I603)
                M600 (Arg0, 0x18, Local0, Zero)
                Local0 = (DerefOf (M602 (0x03, 0x02, 0x01)) > I603)
                M600 (Arg0, 0x19, Local0, Ones)
            }

            /* LGreaterEqual */

            Local0 = (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                        } >= I603)
            M600 (Arg0, 0x1A, Local0, Ones)
            Local0 = (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC2                           // ..y.
                        } >= I603)
            M600 (Arg0, 0x1B, Local0, Ones)
            Local0 = (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC0                           // ..y.
                        } >= I603)
            M600 (Arg0, 0x1C, Local0, Zero)
            Local0 = (Buffer (0x05)
                        {
                             0xFE, 0xB3, 0x79, 0xC1, 0x01                     // ..y..
                        } >= I603)
            M600 (Arg0, 0x1D, Local0, Ones)
            Local0 = (AUB3 >= I603)
            M600 (Arg0, 0x1E, Local0, Ones)
            Local0 = (AUB2 >= I603)
            M600 (Arg0, 0x1F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB3)) >= I603)
                M600 (Arg0, 0x20, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUB2)) >= I603)
                M600 (Arg0, 0x21, Local0, Ones)
            }

            Local0 = (DerefOf (PAUB [0x03]) >= I603)
            M600 (Arg0, 0x22, Local0, Ones)
            Local0 = (DerefOf (PAUB [0x02]) >= I603)
            M600 (Arg0, 0x23, Local0, Ones)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x03) >= I603)
            M600 (Arg0, 0x24, Local0, Ones)
            Local0 = (M601 (0x03, 0x02) >= I603)
            M600 (Arg0, 0x25, Local0, Ones)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x03, 0x01)) >= I603)
                M600 (Arg0, 0x26, Local0, Ones)
                Local0 = (DerefOf (M602 (0x03, 0x02, 0x01)) >= I603)
                M600 (Arg0, 0x27, Local0, Ones)
            }

            /* LLess */

            Local0 = (Buffer (0x04)
                    {
                         0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                    } < I603)
            M600 (Arg0, 0x28, Local0, Zero)
            Local0 = (Buffer (0x04)
                    {
                         0xFE, 0xB3, 0x79, 0xC2                           // ..y.
                    } < I603)
            M600 (Arg0, 0x29, Local0, Zero)
            Local0 = (Buffer (0x04)
                    {
                         0xFE, 0xB3, 0x79, 0xC0                           // ..y.
                    } < I603)
            M600 (Arg0, 0x2A, Local0, Ones)
            Local0 = (Buffer (0x05)
                    {
                         0xFE, 0xB3, 0x79, 0xC1, 0x01                     // ..y..
                    } < I603)
            M600 (Arg0, 0x2B, Local0, Zero)
            Local0 = (AUB3 < I603)
            M600 (Arg0, 0x2C, Local0, Zero)
            Local0 = (AUB2 < I603)
            M600 (Arg0, 0x2D, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB3)) < I603)
                M600 (Arg0, 0x2E, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUB2)) < I603)
                M600 (Arg0, 0x2F, Local0, Zero)
            }

            Local0 = (DerefOf (PAUB [0x03]) < I603)
            M600 (Arg0, 0x30, Local0, Zero)
            Local0 = (DerefOf (PAUB [0x02]) < I603)
            M600 (Arg0, 0x31, Local0, Zero)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x03) < I603)
            M600 (Arg0, 0x32, Local0, Zero)
            Local0 = (M601 (0x03, 0x02) < I603)
            M600 (Arg0, 0x33, Local0, Zero)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x03, 0x01)) < I603)
                M600 (Arg0, 0x34, Local0, Zero)
                Local0 = (DerefOf (M602 (0x03, 0x02, 0x01)) < I603)
                M600 (Arg0, 0x35, Local0, Zero)
            }

            /* LLessEqual */

            Local0 = (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                        } <= I603)
            M600 (Arg0, 0x36, Local0, Ones)
            Local0 = (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC2                           // ..y.
                        } <= I603)
            M600 (Arg0, 0x37, Local0, Zero)
            Local0 = (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC0                           // ..y.
                        } <= I603)
            M600 (Arg0, 0x38, Local0, Ones)
            Local0 = (Buffer (0x05)
                        {
                             0xFE, 0xB3, 0x79, 0xC1, 0x01                     // ..y..
                        } <= I603)
            M600 (Arg0, 0x39, Local0, Zero)
            Local0 = (AUB3 <= I603)
            M600 (Arg0, 0x3A, Local0, Ones)
            Local0 = (AUB2 <= I603)
            M600 (Arg0, 0x3B, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB3)) <= I603)
                M600 (Arg0, 0x3C, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUB2)) <= I603)
                M600 (Arg0, 0x3D, Local0, Zero)
            }

            Local0 = (DerefOf (PAUB [0x03]) <= I603)
            M600 (Arg0, 0x3E, Local0, Ones)
            Local0 = (DerefOf (PAUB [0x02]) <= I603)
            M600 (Arg0, 0x3F, Local0, Zero)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x03) <= I603)
            M600 (Arg0, 0x40, Local0, Ones)
            Local0 = (M601 (0x03, 0x02) <= I603)
            M600 (Arg0, 0x41, Local0, Zero)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x03, 0x01)) <= I603)
                M600 (Arg0, 0x42, Local0, Ones)
                Local0 = (DerefOf (M602 (0x03, 0x02, 0x01)) <= I603)
                M600 (Arg0, 0x43, Local0, Zero)
            }

            /* LNotEqual */

            Local0 = (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                        } != I603)
            M600 (Arg0, 0x44, Local0, Zero)
            Local0 = (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC2                           // ..y.
                        } != I603)
            M600 (Arg0, 0x45, Local0, Ones)
            Local0 = (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC0                           // ..y.
                        } != I603)
            M600 (Arg0, 0x46, Local0, Ones)
            Local0 = (Buffer (0x05)
                        {
                             0xFE, 0xB3, 0x79, 0xC1, 0x01                     // ..y..
                        } != I603)
            M600 (Arg0, 0x47, Local0, Ones)
            Local0 = (AUB3 != I603)
            M600 (Arg0, 0x48, Local0, Zero)
            Local0 = (AUB2 != I603)
            M600 (Arg0, 0x49, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB3)) != I603)
                M600 (Arg0, 0x4A, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUB2)) != I603)
                M600 (Arg0, 0x4B, Local0, Ones)
            }

            Local0 = (DerefOf (PAUB [0x03]) != I603)
            M600 (Arg0, 0x4C, Local0, Zero)
            Local0 = (DerefOf (PAUB [0x02]) != I603)
            M600 (Arg0, 0x4D, Local0, Ones)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x03) != I603)
            M600 (Arg0, 0x4E, Local0, Zero)
            Local0 = (M601 (0x03, 0x02) != I603)
            M600 (Arg0, 0x4F, Local0, Ones)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x03, 0x01)) != I603)
                M600 (Arg0, 0x50, Local0, Zero)
                Local0 = (DerefOf (M602 (0x03, 0x02, 0x01)) != I603)
                M600 (Arg0, 0x51, Local0, Ones)
            }
        }

        /* Integer to Buffer conversion of the both Integer operands of */
        /* Concatenate operator */
        Method (M645, 1, Serialized)
        {
            Name (I604, 0xFE7CB391D650A284)
            Local0 = Concatenate (I604, I604)
            M600 (Arg0, 0x00, Local0, BB20)
            Local0 = Concatenate (0x0321, I604)
            M600 (Arg0, 0x01, Local0, BB21)
            Local0 = Concatenate (I604, 0x0321)
            M600 (Arg0, 0x01, Local0, BB22)
            Concatenate (I604, I604, Local0)
            M600 (Arg0, 0x00, Local0, BB20)
            Concatenate (0x0321, I604, Local0)
            M600 (Arg0, 0x01, Local0, BB21)
            Concatenate (I604, 0x0321, Local0)
            M600 (Arg0, 0x01, Local0, BB22)
        }

        Method (M325, 1, Serialized)
        {
            Name (I603, 0xC179B3FE)
            Local0 = Concatenate (I603, I603)
            M600 (Arg0, 0x00, Local0, BB23)
            Local0 = Concatenate (0x0321, I603)
            M600 (Arg0, 0x01, Local0, BB24)
            Local0 = Concatenate (I603, 0x0321)
            M600 (Arg0, 0x01, Local0, BB25)
            Concatenate (I603, I603, Local0)
            M600 (Arg0, 0x00, Local0, BB23)
            Concatenate (0x0321, I603, Local0)
            M600 (Arg0, 0x01, Local0, BB24)
            Concatenate (I603, 0x0321, Local0)
            M600 (Arg0, 0x01, Local0, BB25)
        }

        /* Integer to Buffer conversion of the Integer second operand of */
        /* Concatenate operator when the first operand is evaluated as Buffer */
        Method (M646, 1, Serialized)
        {
            Name (I604, 0xFE7CB391D650A284)
            Local0 = Concatenate (Buffer (0x01)
                    {
                         0x5A                                             // Z
                    }, I604)
            M600 (Arg0, 0x00, Local0, BB10)
            Local0 = Concatenate (Buffer (0x02)
                    {
                        "Z"
                    }, I604)
            M600 (Arg0, 0x01, Local0, BB11)
            Local0 = Concatenate (AUB0, I604)
            M600 (Arg0, 0x02, Local0, BB10)
            Local0 = Concatenate (AUB1, I604)
            M600 (Arg0, 0x03, Local0, BB11)
            If (Y078)
            {
                Local0 = Concatenate (DerefOf (RefOf (AUB0)), I604)
                M600 (Arg0, 0x04, Local0, BB10)
                Local0 = Concatenate (DerefOf (RefOf (AUB1)), I604)
                M600 (Arg0, 0x05, Local0, BB11)
            }

            Local0 = Concatenate (DerefOf (PAUB [0x00]), I604)
            M600 (Arg0, 0x06, Local0, BB10)
            Local0 = Concatenate (DerefOf (PAUB [0x01]), I604)
            M600 (Arg0, 0x07, Local0, BB11)
            /* Method returns Buffer */

            Local0 = Concatenate (M601 (0x03, 0x00), I604)
            M600 (Arg0, 0x08, Local0, BB10)
            Local0 = Concatenate (M601 (0x03, 0x01), I604)
            M600 (Arg0, 0x09, Local0, BB11)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = Concatenate (DerefOf (M602 (0x03, 0x00, 0x01)), I604)
                M600 (Arg0, 0x0A, Local0, BB10)
                Local0 = Concatenate (DerefOf (M602 (0x03, 0x01, 0x01)), I604)
                M600 (Arg0, 0x0B, Local0, BB11)
            }

            Concatenate (Buffer (0x01)
                {
                     0x5A                                             // Z
                }, I604, Local0)
            M600 (Arg0, 0x0C, Local0, BB10)
            Concatenate (Buffer (0x02)
                {
                    "Z"
                }, I604, Local0)
            M600 (Arg0, 0x0D, Local0, BB11)
            Concatenate (AUB0, I604, Local0)
            M600 (Arg0, 0x0E, Local0, BB10)
            Concatenate (AUB1, I604, Local0)
            M600 (Arg0, 0x0F, Local0, BB11)
            If (Y078)
            {
                Concatenate (DerefOf (RefOf (AUB0)), I604, Local0)
                M600 (Arg0, 0x10, Local0, BB10)
                Concatenate (DerefOf (RefOf (AUB1)), I604, Local0)
                M600 (Arg0, 0x11, Local0, BB11)
            }

            Concatenate (DerefOf (PAUB [0x00]), I604, Local0)
            M600 (Arg0, 0x12, Local0, BB10)
            Concatenate (DerefOf (PAUB [0x01]), I604, Local0)
            M600 (Arg0, 0x13, Local0, BB11)
            /* Method returns Buffer */

            Concatenate (M601 (0x03, 0x00), I604, Local0)
            M600 (Arg0, 0x14, Local0, BB10)
            Concatenate (M601 (0x03, 0x01), I604, Local0)
            M600 (Arg0, 0x15, Local0, BB11)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Concatenate (DerefOf (M602 (0x03, 0x00, 0x01)), I604, Local0)
                M600 (Arg0, 0x16, Local0, BB10)
                Concatenate (DerefOf (M602 (0x03, 0x01, 0x01)), I604, Local0)
                M600 (Arg0, 0x17, Local0, BB11)
            }
        }

        Method (M326, 1, Serialized)
        {
            Name (I603, 0xC179B3FE)
            Name (I604, 0xFE7CB391D650A284)
            Local0 = Concatenate (Buffer (0x01)
                    {
                         0x5A                                             // Z
                    }, I603)
            M600 (Arg0, 0x00, Local0, BB12)
            Local0 = Concatenate (Buffer (0x02)
                    {
                        "Z"
                    }, I603)
            M600 (Arg0, 0x01, Local0, BB13)
            Local0 = Concatenate (AUB0, I603)
            M600 (Arg0, 0x02, Local0, BB12)
            Local0 = Concatenate (AUB1, I603)
            M600 (Arg0, 0x03, Local0, BB13)
            If (Y078)
            {
                Local0 = Concatenate (DerefOf (RefOf (AUB0)), I603)
                M600 (Arg0, 0x04, Local0, BB12)
                Local0 = Concatenate (DerefOf (RefOf (AUB1)), I603)
                M600 (Arg0, 0x05, Local0, BB13)
            }

            Local0 = Concatenate (DerefOf (PAUB [0x00]), I603)
            M600 (Arg0, 0x06, Local0, BB12)
            Local0 = Concatenate (DerefOf (PAUB [0x01]), I603)
            M600 (Arg0, 0x07, Local0, BB13)
            /* Method returns Buffer */

            Local0 = Concatenate (M601 (0x03, 0x00), I603)
            M600 (Arg0, 0x08, Local0, BB12)
            Local0 = Concatenate (M601 (0x03, 0x01), I603)
            M600 (Arg0, 0x09, Local0, BB13)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = Concatenate (DerefOf (M602 (0x03, 0x00, 0x01)), I603)
                M600 (Arg0, 0x0A, Local0, BB12)
                Local0 = Concatenate (DerefOf (M602 (0x03, 0x01, 0x01)), I603)
                M600 (Arg0, 0x0B, Local0, BB13)
            }

            Local0 = Concatenate (Buffer (0x01)
                    {
                         0x5A                                             // Z
                    }, I604)
            M600 (Arg0, 0x0C, Local0, BB14)
            Local0 = Concatenate (Buffer (0x02)
                    {
                        "Z"
                    }, I604)
            M600 (Arg0, 0x0D, Local0, BB15)
            Concatenate (Buffer (0x01)
                {
                     0x5A                                             // Z
                }, I603, Local0)
            M600 (Arg0, 0x0E, Local0, BB12)
            Concatenate (Buffer (0x02)
                {
                    "Z"
                }, I603, Local0)
            M600 (Arg0, 0x0F, Local0, BB13)
            Concatenate (AUB0, I603, Local0)
            M600 (Arg0, 0x10, Local0, BB12)
            Concatenate (AUB1, I603, Local0)
            M600 (Arg0, 0x11, Local0, BB13)
            If (Y078)
            {
                Concatenate (DerefOf (RefOf (AUB0)), I603, Local0)
                M600 (Arg0, 0x12, Local0, BB12)
                Concatenate (DerefOf (RefOf (AUB1)), I603, Local0)
                M600 (Arg0, 0x13, Local0, BB13)
            }

            Concatenate (DerefOf (PAUB [0x00]), I603, Local0)
            M600 (Arg0, 0x14, Local0, BB12)
            Concatenate (DerefOf (PAUB [0x01]), I603, Local0)
            M600 (Arg0, 0x15, Local0, BB13)
            /* Method returns Buffer */

            Concatenate (M601 (0x03, 0x00), I603, Local0)
            M600 (Arg0, 0x16, Local0, BB12)
            Concatenate (M601 (0x03, 0x01), I603, Local0)
            M600 (Arg0, 0x17, Local0, BB13)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Concatenate (DerefOf (M602 (0x03, 0x00, 0x01)), I603, Local0)
                M600 (Arg0, 0x18, Local0, BB12)
                Concatenate (DerefOf (M602 (0x03, 0x01, 0x01)), I603, Local0)
                M600 (Arg0, 0x19, Local0, BB13)
            }

            Concatenate (Buffer (0x01)
                {
                     0x5A                                             // Z
                }, I604, Local0)
            M600 (Arg0, 0x1A, Local0, BB14)
            Concatenate (Buffer (0x02)
                {
                    "Z"
                }, I604, Local0)
            M600 (Arg0, 0x1B, Local0, BB15)
        }

        /* Integer to Buffer conversion of the Integer Source operand of */
        /* ToString operator */
        Method (M647, 1, Serialized)
        {
            Name (I60D, 0x6E7C534136502214)
            Name (I60E, 0x6E00534136002214)
            Local0 = ToString (I60D, Ones)
            M600 (Arg0, 0x00, Local0, BS18)
            Local0 = ToString (I60D, 0x03)
            M600 (Arg0, 0x01, Local0, BS19)
            Local0 = ToString (I60E, Ones)
            M600 (Arg0, 0x02, Local0, BS1A)
            Local0 = ToString (I60D, AUI0)
            M600 (Arg0, 0x03, Local0, BS18)
            Local0 = ToString (I60D, AUI7)
            M600 (Arg0, 0x04, Local0, BS19)
            Local0 = ToString (I60E, AUI0)
            M600 (Arg0, 0x05, Local0, BS1A)
            If (Y078)
            {
                Local0 = ToString (I60D, DerefOf (RefOf (AUI0)))
                M600 (Arg0, 0x06, Local0, BS18)
                Local0 = ToString (I60D, DerefOf (RefOf (AUI7)))
                M600 (Arg0, 0x07, Local0, BS19)
                Local0 = ToString (I60E, DerefOf (RefOf (AUI0)))
                M600 (Arg0, 0x08, Local0, BS1A)
            }

            Local0 = ToString (I60D, DerefOf (PAUI [0x00]))
            M600 (Arg0, 0x09, Local0, BS18)
            Local0 = ToString (I60D, DerefOf (PAUI [0x07]))
            M600 (Arg0, 0x0A, Local0, BS19)
            Local0 = ToString (I60E, DerefOf (PAUI [0x00]))
            M600 (Arg0, 0x0B, Local0, BS1A)
            /* Method returns Length parameter */

            Local0 = ToString (I60D, M601 (0x01, 0x00))
            M600 (Arg0, 0x0C, Local0, BS18)
            Local0 = ToString (I60D, M601 (0x01, 0x07))
            M600 (Arg0, 0x0D, Local0, BS19)
            Local0 = ToString (I60E, M601 (0x01, 0x00))
            M600 (Arg0, 0x0E, Local0, BS1A)
            /* Method returns Reference to Length parameter */

            If (Y500)
            {
                Local0 = ToString (I60D, DerefOf (M601 (0x01, 0x00)))
                M600 (Arg0, 0x0F, Local0, BS18)
                Local0 = ToString (I60D, DerefOf (M601 (0x01, 0x07)))
                M600 (Arg0, 0x10, Local0, BS19)
                Local0 = ToString (I60E, DerefOf (M601 (0x01, 0x00)))
                M600 (Arg0, 0x11, Local0, BS1A)
            }

            ToString (I60D, Ones, Local0)
            M600 (Arg0, 0x12, Local0, BS18)
            ToString (I60D, 0x03, Local0)
            M600 (Arg0, 0x13, Local0, BS19)
            ToString (I60E, Ones, Local0)
            M600 (Arg0, 0x14, Local0, BS1A)
            ToString (I60D, AUI0, Local0)
            M600 (Arg0, 0x15, Local0, BS18)
            ToString (I60D, AUI7, Local0)
            M600 (Arg0, 0x16, Local0, BS19)
            ToString (I60E, AUI0, Local0)
            M600 (Arg0, 0x17, Local0, BS1A)
            If (Y078)
            {
                ToString (I60D, DerefOf (RefOf (AUI0)), Local0)
                M600 (Arg0, 0x18, Local0, BS18)
                ToString (I60D, DerefOf (RefOf (AUI7)), Local0)
                M600 (Arg0, 0x19, Local0, BS19)
                ToString (I60E, DerefOf (RefOf (AUI0)), Local0)
                M600 (Arg0, 0x1A, Local0, BS1A)
            }

            ToString (I60D, DerefOf (PAUI [0x00]), Local0)
            M600 (Arg0, 0x1B, Local0, BS18)
            ToString (I60D, DerefOf (PAUI [0x07]), Local0)
            M600 (Arg0, 0x1C, Local0, BS19)
            ToString (I60E, DerefOf (PAUI [0x00]), Local0)
            M600 (Arg0, 0x1D, Local0, BS1A)
            /* Method returns Length parameter */

            ToString (I60D, M601 (0x01, 0x00), Local0)
            M600 (Arg0, 0x1E, Local0, BS18)
            ToString (I60D, M601 (0x01, 0x07), Local0)
            M600 (Arg0, 0x1F, Local0, BS19)
            ToString (I60E, M601 (0x01, 0x00), Local0)
            M600 (Arg0, 0x20, Local0, BS1A)
            /* Method returns Reference to Length parameter */

            If (Y500)
            {
                ToString (I60D, DerefOf (M601 (0x01, 0x00)), Local0)
                M600 (Arg0, 0x21, Local0, BS18)
                ToString (I60D, DerefOf (M601 (0x01, 0x07)), Local0)
                M600 (Arg0, 0x22, Local0, BS19)
                ToString (I60E, DerefOf (M601 (0x01, 0x00)), Local0)
                M600 (Arg0, 0x23, Local0, BS1A)
            }
        }

        Method (M327, 1, Serialized)
        {
            Name (I60C, 0x6179534E)
            Name (I60F, 0x6E7C534136002214)
            Local0 = ToString (I60C, Ones)
            M600 (Arg0, 0x00, Local0, BS16)
            Local0 = ToString (I60C, 0x03)
            M600 (Arg0, 0x01, Local0, BS17)
            Local0 = ToString (I60F, Ones)
            M600 (Arg0, 0x02, Local0, BS1A)
            Local0 = ToString (I60C, AUI0)
            M600 (Arg0, 0x03, Local0, BS16)
            Local0 = ToString (I60C, AUI7)
            M600 (Arg0, 0x04, Local0, BS17)
            Local0 = ToString (I60F, AUI0)
            M600 (Arg0, 0x05, Local0, BS1A)
            If (Y078)
            {
                Local0 = ToString (I60C, DerefOf (RefOf (AUI0)))
                M600 (Arg0, 0x06, Local0, BS16)
                Local0 = ToString (I60C, DerefOf (RefOf (AUI7)))
                M600 (Arg0, 0x07, Local0, BS17)
                Local0 = ToString (I60F, DerefOf (RefOf (AUI0)))
                M600 (Arg0, 0x08, Local0, BS1A)
            }

            Local0 = ToString (I60C, DerefOf (PAUI [0x00]))
            M600 (Arg0, 0x09, Local0, BS16)
            Local0 = ToString (I60C, DerefOf (PAUI [0x07]))
            M600 (Arg0, 0x0A, Local0, BS17)
            Local0 = ToString (I60F, DerefOf (PAUI [0x00]))
            M600 (Arg0, 0x0B, Local0, BS1A)
            /* Method returns Length parameter */

            Local0 = ToString (I60C, M601 (0x01, 0x00))
            M600 (Arg0, 0x0C, Local0, BS16)
            Local0 = ToString (I60C, M601 (0x01, 0x07))
            M600 (Arg0, 0x0D, Local0, BS17)
            Local0 = ToString (I60F, M601 (0x01, 0x00))
            M600 (Arg0, 0x0E, Local0, BS1A)
            /* Method returns Reference to Length parameter */

            If (Y500)
            {
                Local0 = ToString (I60C, DerefOf (M601 (0x01, 0x00)))
                M600 (Arg0, 0x0F, Local0, BS16)
                Local0 = ToString (I60C, DerefOf (M601 (0x01, 0x07)))
                M600 (Arg0, 0x10, Local0, BS17)
                Local0 = ToString (I60F, DerefOf (M601 (0x01, 0x00)))
                M600 (Arg0, 0x11, Local0, BS1A)
            }

            ToString (I60C, Ones, Local0)
            M600 (Arg0, 0x12, Local0, BS16)
            ToString (I60C, 0x03, Local0)
            M600 (Arg0, 0x13, Local0, BS17)
            ToString (I60F, Ones, Local0)
            M600 (Arg0, 0x14, Local0, BS1A)
            ToString (I60C, AUI0, Local0)
            M600 (Arg0, 0x15, Local0, BS16)
            ToString (I60C, AUI7, Local0)
            M600 (Arg0, 0x16, Local0, BS17)
            ToString (I60F, AUI0, Local0)
            M600 (Arg0, 0x17, Local0, BS1A)
            If (Y078)
            {
                ToString (I60C, DerefOf (RefOf (AUI0)), Local0)
                M600 (Arg0, 0x18, Local0, BS16)
                ToString (I60C, DerefOf (RefOf (AUI7)), Local0)
                M600 (Arg0, 0x19, Local0, BS17)
                ToString (I60F, DerefOf (RefOf (AUI0)), Local0)
                M600 (Arg0, 0x1A, Local0, BS1A)
            }

            ToString (I60C, DerefOf (PAUI [0x00]), Local0)
            M600 (Arg0, 0x1B, Local0, BS16)
            ToString (I60C, DerefOf (PAUI [0x07]), Local0)
            M600 (Arg0, 0x1C, Local0, BS17)
            ToString (I60F, DerefOf (PAUI [0x00]), Local0)
            M600 (Arg0, 0x1D, Local0, BS1A)
            /* Method returns Length parameter */

            ToString (I60C, M601 (0x01, 0x00), Local0)
            M600 (Arg0, 0x1E, Local0, BS16)
            ToString (I60C, M601 (0x01, 0x07), Local0)
            M600 (Arg0, 0x1F, Local0, BS17)
            ToString (I60F, M601 (0x01, 0x00), Local0)
            M600 (Arg0, 0x20, Local0, BS1A)
            /* Method returns Reference to Length parameter */

            If (Y500)
            {
                ToString (I60C, DerefOf (M601 (0x01, 0x00)), Local0)
                M600 (Arg0, 0x21, Local0, BS16)
                ToString (I60C, DerefOf (M601 (0x01, 0x07)), Local0)
                M600 (Arg0, 0x22, Local0, BS17)
                ToString (I60F, DerefOf (M601 (0x01, 0x00)), Local0)
                M600 (Arg0, 0x23, Local0, BS1A)
            }
        }

        /* Integer to Buffer conversion of the Integer Source operand of */
        /* Mid operator */
        Method (M648, 1, Serialized)
        {
            Name (I604, 0xFE7CB391D650A284)
            Name (I60F, 0x6E7C534136002214)
            Local0 = Mid (I604, 0x00, 0x09)
            M600 (Arg0, 0x00, Local0, BB1D)
            Local0 = Mid (I60F, 0x01, 0x08)
            M600 (Arg0, 0x01, Local0, BB30)
            Local0 = Mid (I604, AUI5, AUIB)
            M600 (Arg0, 0x02, Local0, BB1D)
            Local0 = Mid (I60F, AUI6, AUIA)
            M600 (Arg0, 0x03, Local0, BB30)
            If (Y078)
            {
                Local0 = Mid (I604, DerefOf (RefOf (AUI5)), DerefOf (RefOf (AUIB)))
                M600 (Arg0, 0x04, Local0, BB1D)
                Local0 = Mid (I60F, DerefOf (RefOf (AUI6)), DerefOf (RefOf (AUIA)))
                M600 (Arg0, 0x05, Local0, BB30)
            }

            Local0 = Mid (I604, DerefOf (PAUI [0x05]), DerefOf (PAUI [
                0x0B]))
            M600 (Arg0, 0x06, Local0, BB1D)
            Local0 = Mid (I60F, DerefOf (PAUI [0x06]), DerefOf (PAUI [
                0x0A]))
            M600 (Arg0, 0x07, Local0, BB30)
            /* Method returns Index and Length parameters */

            Local0 = Mid (I604, M601 (0x01, 0x05), M601 (0x01, 0x0B))
            M600 (Arg0, 0x08, Local0, BB1D)
            Local0 = Mid (I60F, M601 (0x01, 0x06), M601 (0x01, 0x0A))
            M600 (Arg0, 0x09, Local0, BB30)
            /* Method returns Reference to Index and Length parameters */

            If (Y500)
            {
                Local0 = Mid (I604, DerefOf (M601 (0x01, 0x05)), DerefOf (M601 (0x01, 0x0B))
                    )
                M600 (Arg0, 0x0A, Local0, BB1D)
                Local0 = Mid (I60F, DerefOf (M601 (0x01, 0x06)), DerefOf (M601 (0x01, 0x0A))
                    )
                M600 (Arg0, 0x0B, Local0, BB30)
            }

            Mid (I604, 0x00, 0x09, Local0)
            M600 (Arg0, 0x0C, Local0, BB1D)
            Mid (I60F, 0x01, 0x08, Local0)
            M600 (Arg0, 0x0D, Local0, BB30)
            Mid (I604, AUI5, AUIB, Local0)
            M600 (Arg0, 0x0E, Local0, BB1D)
            Mid (I60F, AUI6, AUIA, Local0)
            M600 (Arg0, 0x0F, Local0, BB30)
            If (Y078)
            {
                Mid (I604, DerefOf (RefOf (AUI5)), DerefOf (RefOf (AUIB)), Local0)
                M600 (Arg0, 0x10, Local0, BB1D)
                Mid (I60F, DerefOf (RefOf (AUI6)), DerefOf (RefOf (AUIA)), Local0)
                M600 (Arg0, 0x11, Local0, BB30)
            }

            Mid (I604, DerefOf (PAUI [0x05]), DerefOf (PAUI [0x0B]),
                Local0)
            M600 (Arg0, 0x12, Local0, BB1D)
            Mid (I60F, DerefOf (PAUI [0x06]), DerefOf (PAUI [0x0A]),
                Local0)
            M600 (Arg0, 0x13, Local0, BB30)
            /* Method returns Index and Length parameters */

            Mid (I604, M601 (0x01, 0x05), M601 (0x01, 0x0B), Local0)
            M600 (Arg0, 0x14, Local0, BB1D)
            Mid (I60F, M601 (0x01, 0x06), M601 (0x01, 0x0A), Local0)
            M600 (Arg0, 0x15, Local0, BB30)
            /* Method returns Reference to Index and Length parameters */

            If (Y500)
            {
                Mid (I604, DerefOf (M601 (0x01, 0x05)), DerefOf (M601 (0x01, 0x0B)), Local0)
                M600 (Arg0, 0x16, Local0, BB1D)
                Mid (I60F, DerefOf (M601 (0x01, 0x06)), DerefOf (M601 (0x01, 0x0A)), Local0)
                M600 (Arg0, 0x17, Local0, BB30)
            }
        }

        Method (M328, 1, Serialized)
        {
            Name (I603, 0xC179B3FE)
            Name (I60F, 0x6E7C534136002214)
            Local0 = Mid (I603, 0x00, 0x05)
            M600 (Arg0, 0x00, Local0, BB1C)
            Local0 = Mid (I60F, 0x01, 0x04)
            M600 (Arg0, 0x01, Local0, BB31)
            Local0 = Mid (I603, AUI5, AUI9)
            M600 (Arg0, 0x02, Local0, BB1C)
            Local0 = Mid (I60F, AUI6, AUI8)
            M600 (Arg0, 0x03, Local0, BB31)
            If (Y078)
            {
                Local0 = Mid (I603, DerefOf (RefOf (AUI5)), DerefOf (RefOf (AUI9)))
                M600 (Arg0, 0x04, Local0, BB1C)
                Local0 = Mid (I60F, DerefOf (RefOf (AUI6)), DerefOf (RefOf (AUI8)))
                M600 (Arg0, 0x05, Local0, BB31)
            }

            Local0 = Mid (I603, DerefOf (PAUI [0x05]), DerefOf (PAUI [
                0x09]))
            M600 (Arg0, 0x06, Local0, BB1C)
            Local0 = Mid (I60F, DerefOf (PAUI [0x06]), DerefOf (PAUI [
                0x08]))
            M600 (Arg0, 0x07, Local0, BB31)
            /* Method returns Index and Length parameters */

            Local0 = Mid (I603, M601 (0x01, 0x05), M601 (0x01, 0x09))
            M600 (Arg0, 0x08, Local0, BB1C)
            Local0 = Mid (I60F, M601 (0x01, 0x06), M601 (0x01, 0x08))
            M600 (Arg0, 0x09, Local0, BB31)
            /* Method returns Reference to Index and Length parameters */

            If (Y500)
            {
                Local0 = Mid (I603, DerefOf (M601 (0x01, 0x05)), DerefOf (M601 (0x01, 0x09))
                    )
                M600 (Arg0, 0x0A, Local0, BB1C)
                Local0 = Mid (I60F, DerefOf (M601 (0x01, 0x06)), DerefOf (M601 (0x01, 0x08))
                    )
                M600 (Arg0, 0x0B, Local0, BB31)
            }

            Mid (I603, 0x00, 0x05, Local0)
            M600 (Arg0, 0x0C, Local0, BB1C)
            Mid (I60F, 0x01, 0x04, Local0)
            M600 (Arg0, 0x0D, Local0, BB31)
            Mid (I603, AUI5, AUI9, Local0)
            M600 (Arg0, 0x0E, Local0, BB1C)
            Mid (I60F, AUI6, AUI8, Local0)
            M600 (Arg0, 0x0F, Local0, BB31)
            If (Y078)
            {
                Mid (I603, DerefOf (RefOf (AUI5)), DerefOf (RefOf (AUI9)), Local0)
                M600 (Arg0, 0x10, Local0, BB1C)
                Mid (I60F, DerefOf (RefOf (AUI6)), DerefOf (RefOf (AUI8)), Local0)
                M600 (Arg0, 0x11, Local0, BB31)
            }

            Mid (I603, DerefOf (PAUI [0x05]), DerefOf (PAUI [0x09]),
                Local0)
            M600 (Arg0, 0x12, Local0, BB1C)
            Mid (I60F, DerefOf (PAUI [0x06]), DerefOf (PAUI [0x08]),
                Local0)
            M600 (Arg0, 0x13, Local0, BB31)
            /* Method returns Index and Length parameters */

            Mid (I603, M601 (0x01, 0x05), M601 (0x01, 0x09), Local0)
            M600 (Arg0, 0x14, Local0, BB1C)
            Mid (I60F, M601 (0x01, 0x06), M601 (0x01, 0x08), Local0)
            M600 (Arg0, 0x15, Local0, BB31)
            /* Method returns Reference to Index and Length parameters */

            If (Y500)
            {
                Mid (I603, DerefOf (M601 (0x01, 0x05)), DerefOf (M601 (0x01, 0x09)), Local0)
                M600 (Arg0, 0x16, Local0, BB1C)
                Mid (I60F, DerefOf (M601 (0x01, 0x06)), DerefOf (M601 (0x01, 0x08)), Local0)
                M600 (Arg0, 0x17, Local0, BB31)
            }
        }

        /*	Method(m649, 1) */
        /*	Method(m329, 1) */
        /*	Method(m64a, 1) */
        /*	Method(m32a, 1) */
        /* String to Integer implicit conversion Cases. */
        /* String to Integer conversion of the String sole operand */
        /* of the 1-parameter Integer arithmetic operators */
        /* (Decrement, Increment, FindSetLeftBit, FindSetRightBit, Not) */
        Method (M64B, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S605, "FE7CB391D650A284")
            /* Decrement */

            If (Y501)
            {
                Local0 = S601--
                M600 (Arg0, 0x00, Local0, BI12)
                Local0 = S605--
                M600 (Arg0, 0x01, Local0, BI16)
            }

            /* Increment */

            If (Y501)
            {
                Local0 = S601++
                M600 (Arg0, 0x02, Local0, BI13)
                Local0 = S605++
                M600 (Arg0, 0x03, Local0, BI17)
            }

            /* FindSetLeftBit */

            Local0 = FindSetLeftBit (S601)
            M600 (Arg0, 0x04, Local0, 0x0A)
            Local0 = FindSetLeftBit (S605)
            M600 (Arg0, 0x05, Local0, 0x40)
            /* FindSetRightBit */

            Local0 = FindSetRightBit (S601)
            M600 (Arg0, 0x06, Local0, 0x01)
            Local0 = FindSetRightBit (S605)
            M600 (Arg0, 0x07, Local0, 0x03)
            /* Not */

            Store (~S601, Local0)
            M600 (Arg0, 0x08, Local0, 0xFFFFFFFFFFFFFCDE)
            Store (~S605, Local0)
            M600 (Arg0, 0x09, Local0, 0x01834C6E29AF5D7B)
        }

        Method (M32B, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            /* Decrement */

            If (Y501)
            {
                Local0 = S601--
                M600 (Arg0, 0x00, Local0, BI12)
                Local0 = S604--
                M600 (Arg0, 0x01, Local0, BI14)
            }

            /* Increment */

            If (Y501)
            {
                Local0 = S601++
                M600 (Arg0, 0x02, Local0, BI13)
                Local0 = S604++
                M600 (Arg0, 0x03, Local0, BI15)
            }

            /* FindSetLeftBit */

            Local0 = FindSetLeftBit (S601)
            M600 (Arg0, 0x04, Local0, 0x0A)
            Local0 = FindSetLeftBit (S604)
            M600 (Arg0, 0x05, Local0, 0x20)
            /* FindSetRightBit */

            Local0 = FindSetRightBit (S601)
            M600 (Arg0, 0x06, Local0, 0x01)
            Local0 = FindSetRightBit (S604)
            M600 (Arg0, 0x07, Local0, 0x02)
            /* Not */

            Store (~S601, Local0)
            M600 (Arg0, 0x08, Local0, 0xFFFFFCDE)
            Store (~S604, Local0)
            M600 (Arg0, 0x09, Local0, 0x3E864C01)
        }

        /* String to Integer conversion of the String sole operand */
        /* of the LNot Logical Integer operator */
        Method (M000, 1, Serialized)
        {
            Name (S600, "0")
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            Name (S605, "FE7CB391D650A284")
            Local0 = !S600
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = !S601
            M600 (Arg0, 0x01, Local0, Zero)
            If (F64)
            {
                Local0 = !S605
                M600 (Arg0, 0x02, Local0, Zero)
            }
            Else
            {
                Local0 = !S604
                M600 (Arg0, 0x03, Local0, Zero)
            }
        }

        /* String to Integer conversion of the String sole operand */
        /* of the FromBCD and ToBCD conversion operators */
        Method (M64C, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            Name (S605, "FE7CB391D650A284")
            Name (S615, "3789012345678901")
            Name (S616, "D76162EE9EC35")
            /* FromBCD */

            Local0 = FromBCD (S601)
            M600 (Arg0, 0x02, Local0, 0x0141)
            Local0 = FromBCD (S615)
            M600 (Arg0, 0x03, Local0, 0x000D76162EE9EC35)
            FromBCD (S601, Local0)
            M600 (Arg0, 0x02, Local0, 0x0141)
            FromBCD (S615, Local0)
            M600 (Arg0, 0x03, Local0, 0x000D76162EE9EC35)
            /* ToBCD */

            Local0 = ToBCD (S601)
            M600 (Arg0, 0x04, Local0, 0x0801)
            /* Error of iASL on constant folding
             Store(ToBCD(s616), Local0)
             m600(arg0, 5, Local0, 0x3789012345678901)
             */
            ToBCD (S601, Local0)
            M600 (Arg0, 0x04, Local0, 0x0801)
            ToBCD (S616, Local0)
            M600 (Arg0, 0x05, Local0, 0x3789012345678901)
        }

        Method (M32C, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            Name (S605, "FE7CB391D650A284")
            Name (S617, "90123456")
            Name (S618, "55F2CC0")
            /* FromBCD */

            Local0 = FromBCD (S601)
            M600 (Arg0, 0x02, Local0, 0x0141)
            Local0 = FromBCD (S617)
            M600 (Arg0, 0x03, Local0, 0x055F2CC0)
            FromBCD (S601, Local0)
            M600 (Arg0, 0x02, Local0, 0x0141)
            FromBCD (S617, Local0)
            M600 (Arg0, 0x03, Local0, 0x055F2CC0)
            /* ToBCD */

            Local0 = ToBCD (S601)
            M600 (Arg0, 0x04, Local0, 0x0801)
            Local0 = ToBCD (S618)
            M600 (Arg0, 0x05, Local0, 0x90123456)
            ToBCD (S601, Local0)
            M600 (Arg0, 0x04, Local0, 0x0801)
            ToBCD (S618, Local0)
            M600 (Arg0, 0x05, Local0, 0x90123456)
        }

        /* String to Integer conversion of each String operand */
        /* of the 2-parameter Integer arithmetic operators */
        /* Add, And, Divide, Mod, Multiply, NAnd, NOr, Or, */
        /* ShiftLeft, ShiftRight, Subtract, Xor */
        /* Add, common 32-bit/64-bit test */
        Method (M001, 1, Serialized)
        {
            Name (S601, "0321")
            /* Conversion of the first operand */

            Store ((S601 + 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((S601 + 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x0322)
            Store ((S601 + AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((S601 + AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x0322)
            If (Y078)
            {
                Store ((S601 + DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((S601 + DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x0322)
            }

            Store ((S601 + DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((S601 + DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x0322)
            /* Method returns Integer */

            Store ((S601 + M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((S601 + M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x0322)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S601 + DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((S601 + DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x0322)
            }

            Local0 = (S601 + 0x00)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (S601 + 0x01)
            M600 (Arg0, 0x0D, Local0, 0x0322)
            Local0 = (S601 + AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (S601 + AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x0322)
            If (Y078)
            {
                Local0 = (S601 + DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (S601 + DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x0322)
            }

            Local0 = (S601 + DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (S601 + DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x0322)
            /* Method returns Integer */

            Local0 = (S601 + M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (S601 + M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x0322)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S601 + DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (S601 + DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x0322)
            }

            /* Conversion of the second operand */

            Store ((0x00 + S601), Local0)
            M600 (Arg0, 0x18, Local0, 0x0321)
            Store ((0x01 + S601), Local0)
            M600 (Arg0, 0x19, Local0, 0x0322)
            Store ((AUI5 + S601), Local0)
            M600 (Arg0, 0x1A, Local0, 0x0321)
            Store ((AUI6 + S601), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0322)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) + S601), Local0)
                M600 (Arg0, 0x1C, Local0, 0x0321)
                Store ((DerefOf (RefOf (AUI6)) + S601), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0322)
            }

            Store ((DerefOf (PAUI [0x05]) + S601), Local0)
            M600 (Arg0, 0x1E, Local0, 0x0321)
            Store ((DerefOf (PAUI [0x06]) + S601), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0322)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) + S601), Local0)
            M600 (Arg0, 0x20, Local0, 0x0321)
            Store ((M601 (0x01, 0x06) + S601), Local0)
            M600 (Arg0, 0x21, Local0, 0x0322)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) + S601), Local0)
                M600 (Arg0, 0x22, Local0, 0x0321)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) + S601), Local0)
                M600 (Arg0, 0x23, Local0, 0x0322)
            }

            Local0 = (0x00 + S601) /* \M613.M001.S601 */
            M600 (Arg0, 0x24, Local0, 0x0321)
            Local0 = (0x01 + S601) /* \M613.M001.S601 */
            M600 (Arg0, 0x25, Local0, 0x0322)
            Local0 = (AUI5 + S601) /* \M613.M001.S601 */
            M600 (Arg0, 0x26, Local0, 0x0321)
            Local0 = (AUI6 + S601) /* \M613.M001.S601 */
            M600 (Arg0, 0x27, Local0, 0x0322)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) + S601) /* \M613.M001.S601 */
                M600 (Arg0, 0x28, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (AUI6)) + S601) /* \M613.M001.S601 */
                M600 (Arg0, 0x29, Local0, 0x0322)
            }

            Local0 = (DerefOf (PAUI [0x05]) + S601) /* \M613.M001.S601 */
            M600 (Arg0, 0x2A, Local0, 0x0321)
            Local0 = (DerefOf (PAUI [0x06]) + S601) /* \M613.M001.S601 */
            M600 (Arg0, 0x2B, Local0, 0x0322)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) + S601) /* \M613.M001.S601 */
            M600 (Arg0, 0x2C, Local0, 0x0321)
            Local0 = (M601 (0x01, 0x06) + S601) /* \M613.M001.S601 */
            M600 (Arg0, 0x2D, Local0, 0x0322)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) + S601) /* \M613.M001.S601 */
                M600 (Arg0, 0x2E, Local0, 0x0321)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) + S601) /* \M613.M001.S601 */
                M600 (Arg0, 0x2F, Local0, 0x0322)
            }
        }

        /* Add, 64-bit */

        Method (M002, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S605, "FE7CB391D650A284")
            /* Conversion of the first operand */

            Store ((S605 + 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((S605 + 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xFE7CB391D650A285)
            Store ((S605 + AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((S605 + AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xFE7CB391D650A285)
            If (Y078)
            {
                Store ((S605 + DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((S605 + DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFE7CB391D650A285)
            }

            Store ((S605 + DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((S605 + DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFE7CB391D650A285)
            /* Method returns Integer */

            Store ((S605 + M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((S605 + M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFE7CB391D650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S605 + DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((S605 + DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFE7CB391D650A285)
            }

            Local0 = (S605 + 0x00)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 + 0x01)
            M600 (Arg0, 0x0D, Local0, 0xFE7CB391D650A285)
            Local0 = (S605 + AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 + AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xFE7CB391D650A285)
            If (Y078)
            {
                Local0 = (S605 + DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (S605 + DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xFE7CB391D650A285)
            }

            Local0 = (S605 + DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 + DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xFE7CB391D650A285)
            /* Method returns Integer */

            Local0 = (S605 + M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 + M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xFE7CB391D650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S605 + DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (S605 + DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFE7CB391D650A285)
            }

            /* Conversion of the second operand */

            Store ((0x00 + S605), Local0)
            M600 (Arg0, 0x18, Local0, 0xFE7CB391D650A284)
            Store ((0x01 + S605), Local0)
            M600 (Arg0, 0x19, Local0, 0xFE7CB391D650A285)
            Store ((AUI5 + S605), Local0)
            M600 (Arg0, 0x1A, Local0, 0xFE7CB391D650A284)
            Store ((AUI6 + S605), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFE7CB391D650A285)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) + S605), Local0)
                M600 (Arg0, 0x1C, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (AUI6)) + S605), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFE7CB391D650A285)
            }

            Store ((DerefOf (PAUI [0x05]) + S605), Local0)
            M600 (Arg0, 0x1E, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (PAUI [0x06]) + S605), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFE7CB391D650A285)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) + S605), Local0)
            M600 (Arg0, 0x20, Local0, 0xFE7CB391D650A284)
            Store ((M601 (0x01, 0x06) + S605), Local0)
            M600 (Arg0, 0x21, Local0, 0xFE7CB391D650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) + S605), Local0)
                M600 (Arg0, 0x22, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) + S605), Local0)
                M600 (Arg0, 0x23, Local0, 0xFE7CB391D650A285)
            }

            Local0 = (0x00 + S605) /* \M613.M002.S605 */
            M600 (Arg0, 0x24, Local0, 0xFE7CB391D650A284)
            Local0 = (0x01 + S605) /* \M613.M002.S605 */
            M600 (Arg0, 0x25, Local0, 0xFE7CB391D650A285)
            Local0 = (AUI5 + S605) /* \M613.M002.S605 */
            M600 (Arg0, 0x26, Local0, 0xFE7CB391D650A284)
            Local0 = (AUI6 + S605) /* \M613.M002.S605 */
            M600 (Arg0, 0x27, Local0, 0xFE7CB391D650A285)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) + S605) /* \M613.M002.S605 */
                M600 (Arg0, 0x28, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (AUI6)) + S605) /* \M613.M002.S605 */
                M600 (Arg0, 0x29, Local0, 0xFE7CB391D650A285)
            }

            Local0 = (DerefOf (PAUI [0x05]) + S605) /* \M613.M002.S605 */
            M600 (Arg0, 0x2A, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (PAUI [0x06]) + S605) /* \M613.M002.S605 */
            M600 (Arg0, 0x2B, Local0, 0xFE7CB391D650A285)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) + S605) /* \M613.M002.S605 */
            M600 (Arg0, 0x2C, Local0, 0xFE7CB391D650A284)
            Local0 = (M601 (0x01, 0x06) + S605) /* \M613.M002.S605 */
            M600 (Arg0, 0x2D, Local0, 0xFE7CB391D650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) + S605) /* \M613.M002.S605 */
                M600 (Arg0, 0x2E, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) + S605) /* \M613.M002.S605 */
                M600 (Arg0, 0x2F, Local0, 0xFE7CB391D650A285)
            }

            /* Conversion of the both operands */

            Store ((S601 + S605), Local0)
            M600 (Arg0, 0x30, Local0, 0xFE7CB391D650A5A5)
            Store ((S605 + S601), Local0)
            M600 (Arg0, 0x31, Local0, 0xFE7CB391D650A5A5)
            Local0 = (S601 + S605) /* \M613.M002.S605 */
            M600 (Arg0, 0x32, Local0, 0xFE7CB391D650A5A5)
            Local0 = (S605 + S601) /* \M613.M002.S601 */
            M600 (Arg0, 0x33, Local0, 0xFE7CB391D650A5A5)
        }

        /* Add, 32-bit */

        Method (M003, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            /* Conversion of the first operand */

            Store ((S604 + 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xC179B3FE)
            Store ((S604 + 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xC179B3FF)
            Store ((S604 + AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xC179B3FE)
            Store ((S604 + AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xC179B3FF)
            If (Y078)
            {
                Store ((S604 + DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xC179B3FE)
                Store ((S604 + DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xC179B3FF)
            }

            Store ((S604 + DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xC179B3FE)
            Store ((S604 + DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xC179B3FF)
            /* Method returns Integer */

            Store ((S604 + M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xC179B3FE)
            Store ((S604 + M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xC179B3FF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S604 + DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xC179B3FE)
                Store ((S604 + DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xC179B3FF)
            }

            Local0 = (S604 + 0x00)
            M600 (Arg0, 0x0C, Local0, 0xC179B3FE)
            Local0 = (S604 + 0x01)
            M600 (Arg0, 0x0D, Local0, 0xC179B3FF)
            Local0 = (S604 + AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xC179B3FE)
            Local0 = (S604 + AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xC179B3FF)
            If (Y078)
            {
                Local0 = (S604 + DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xC179B3FE)
                Local0 = (S604 + DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xC179B3FF)
            }

            Local0 = (S604 + DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xC179B3FE)
            Local0 = (S604 + DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xC179B3FF)
            /* Method returns Integer */

            Local0 = (S604 + M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xC179B3FE)
            Local0 = (S604 + M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xC179B3FF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S604 + DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xC179B3FE)
                Local0 = (S604 + DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xC179B3FF)
            }

            /* Conversion of the second operand */

            Store ((0x00 + S604), Local0)
            M600 (Arg0, 0x18, Local0, 0xC179B3FE)
            Store ((0x01 + S604), Local0)
            M600 (Arg0, 0x19, Local0, 0xC179B3FF)
            Store ((AUI5 + S604), Local0)
            M600 (Arg0, 0x1A, Local0, 0xC179B3FE)
            Store ((AUI6 + S604), Local0)
            M600 (Arg0, 0x1B, Local0, 0xC179B3FF)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) + S604), Local0)
                M600 (Arg0, 0x1C, Local0, 0xC179B3FE)
                Store ((DerefOf (RefOf (AUI6)) + S604), Local0)
                M600 (Arg0, 0x1D, Local0, 0xC179B3FF)
            }

            Store ((DerefOf (PAUI [0x05]) + S604), Local0)
            M600 (Arg0, 0x1E, Local0, 0xC179B3FE)
            Store ((DerefOf (PAUI [0x06]) + S604), Local0)
            M600 (Arg0, 0x1F, Local0, 0xC179B3FF)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) + S604), Local0)
            M600 (Arg0, 0x20, Local0, 0xC179B3FE)
            Store ((M601 (0x01, 0x06) + S604), Local0)
            M600 (Arg0, 0x21, Local0, 0xC179B3FF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) + S604), Local0)
                M600 (Arg0, 0x22, Local0, 0xC179B3FE)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) + S604), Local0)
                M600 (Arg0, 0x23, Local0, 0xC179B3FF)
            }

            Local0 = (0x00 + S604) /* \M613.M003.S604 */
            M600 (Arg0, 0x24, Local0, 0xC179B3FE)
            Local0 = (0x01 + S604) /* \M613.M003.S604 */
            M600 (Arg0, 0x25, Local0, 0xC179B3FF)
            Local0 = (AUI5 + S604) /* \M613.M003.S604 */
            M600 (Arg0, 0x26, Local0, 0xC179B3FE)
            Local0 = (AUI6 + S604) /* \M613.M003.S604 */
            M600 (Arg0, 0x27, Local0, 0xC179B3FF)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) + S604) /* \M613.M003.S604 */
                M600 (Arg0, 0x28, Local0, 0xC179B3FE)
                Local0 = (DerefOf (RefOf (AUI6)) + S604) /* \M613.M003.S604 */
                M600 (Arg0, 0x29, Local0, 0xC179B3FF)
            }

            Local0 = (DerefOf (PAUI [0x05]) + S604) /* \M613.M003.S604 */
            M600 (Arg0, 0x2A, Local0, 0xC179B3FE)
            Local0 = (DerefOf (PAUI [0x06]) + S604) /* \M613.M003.S604 */
            M600 (Arg0, 0x2B, Local0, 0xC179B3FF)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) + S604) /* \M613.M003.S604 */
            M600 (Arg0, 0x2C, Local0, 0xC179B3FE)
            Local0 = (M601 (0x01, 0x06) + S604) /* \M613.M003.S604 */
            M600 (Arg0, 0x2D, Local0, 0xC179B3FF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) + S604) /* \M613.M003.S604 */
                M600 (Arg0, 0x2E, Local0, 0xC179B3FE)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) + S604) /* \M613.M003.S604 */
                M600 (Arg0, 0x2F, Local0, 0xC179B3FF)
            }

            /* Conversion of the both operands */

            Store ((S601 + S604), Local0)
            M600 (Arg0, 0x30, Local0, 0xC179B71F)
            Store ((S604 + S601), Local0)
            M600 (Arg0, 0x31, Local0, 0xC179B71F)
            Local0 = (S601 + S604) /* \M613.M003.S604 */
            M600 (Arg0, 0x32, Local0, 0xC179B71F)
            Local0 = (S604 + S601) /* \M613.M003.S601 */
            M600 (Arg0, 0x33, Local0, 0xC179B71F)
        }

        /* And, common 32-bit/64-bit test */

        Method (M004, 1, Serialized)
        {
            Name (S601, "0321")
            /* Conversion of the first operand */

            Store ((S601 & 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x00)
            Store ((S601 & 0xFFFFFFFFFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0x0321)
            Store ((S601 & AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x00)
            Store ((S601 & AUIJ), Local0)
            M600 (Arg0, 0x03, Local0, 0x0321)
            If (Y078)
            {
                Store ((S601 & DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x00)
                Store ((S601 & DerefOf (RefOf (AUIJ))), Local0)
                M600 (Arg0, 0x05, Local0, 0x0321)
            }

            Store ((S601 & DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x00)
            Store ((S601 & DerefOf (PAUI [0x13])), Local0)
            M600 (Arg0, 0x07, Local0, 0x0321)
            /* Method returns Integer */

            Store ((S601 & M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x00)
            Store ((S601 & M601 (0x01, 0x13)), Local0)
            M600 (Arg0, 0x09, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S601 & DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x00)
                Store ((S601 & DerefOf (M602 (0x01, 0x13, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x0321)
            }

            Local0 = (S601 & 0x00)
            M600 (Arg0, 0x0C, Local0, 0x00)
            Local0 = (S601 & 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0x0321)
            Local0 = (S601 & AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x00)
            Local0 = (S601 & AUIJ) /* \AUIJ */
            M600 (Arg0, 0x0F, Local0, 0x0321)
            If (Y078)
            {
                Local0 = (S601 & DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x00)
                Local0 = (S601 & DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x11, Local0, 0x0321)
            }

            Local0 = (S601 & DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x00)
            Local0 = (S601 & DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x13, Local0, 0x0321)
            /* Method returns Integer */

            Local0 = (S601 & M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x00)
            Local0 = (S601 & M601 (0x01, 0x13))
            M600 (Arg0, 0x15, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S601 & DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x00)
                Local0 = (S601 & DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x0321)
            }

            /* Conversion of the second operand */

            Store ((0x00 & S601), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xFFFFFFFFFFFFFFFF & S601), Local0)
            M600 (Arg0, 0x19, Local0, 0x0321)
            Store ((AUI5 & S601), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUIJ & S601), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0321)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) & S601), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUIJ)) & S601), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0321)
            }

            Store ((DerefOf (PAUI [0x05]) & S601), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x13]) & S601), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0321)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) & S601), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x13) & S601), Local0)
            M600 (Arg0, 0x21, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) & S601), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x13, 0x01)) & S601), Local0)
                M600 (Arg0, 0x23, Local0, 0x0321)
            }

            Local0 = (0x00 & S601) /* \M613.M004.S601 */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0xFFFFFFFFFFFFFFFF & S601) /* \M613.M004.S601 */
            M600 (Arg0, 0x25, Local0, 0x0321)
            Local0 = (AUI5 & S601) /* \M613.M004.S601 */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUIJ & S601) /* \M613.M004.S601 */
            M600 (Arg0, 0x27, Local0, 0x0321)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) & S601) /* \M613.M004.S601 */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUIJ)) & S601) /* \M613.M004.S601 */
                M600 (Arg0, 0x29, Local0, 0x0321)
            }

            Local0 = (DerefOf (PAUI [0x05]) & S601) /* \M613.M004.S601 */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x13]) & S601) /* \M613.M004.S601 */
            M600 (Arg0, 0x2B, Local0, 0x0321)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) & S601) /* \M613.M004.S601 */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x13) & S601) /* \M613.M004.S601 */
            M600 (Arg0, 0x2D, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) & S601) /* \M613.M004.S601 */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x13, 0x01)) & S601) /* \M613.M004.S601 */
                M600 (Arg0, 0x2F, Local0, 0x0321)
            }
        }

        /* And, 64-bit */

        Method (M005, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S605, "FE7CB391D650A284")
            /* Conversion of the first operand */

            Store ((S605 & 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x00)
            Store ((S605 & 0xFFFFFFFFFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0xFE7CB391D650A284)
            Store ((S605 & AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x00)
            Store ((S605 & AUIJ), Local0)
            M600 (Arg0, 0x03, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Store ((S605 & DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x00)
                Store ((S605 & DerefOf (RefOf (AUIJ))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFE7CB391D650A284)
            }

            Store ((S605 & DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x00)
            Store ((S605 & DerefOf (PAUI [0x13])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Store ((S605 & M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x00)
            Store ((S605 & M601 (0x01, 0x13)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S605 & DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x00)
                Store ((S605 & DerefOf (M602 (0x01, 0x13, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (S605 & 0x00)
            M600 (Arg0, 0x0C, Local0, 0x00)
            Local0 = (S605 & 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 & AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x00)
            Local0 = (S605 & AUIJ) /* \AUIJ */
            M600 (Arg0, 0x0F, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Local0 = (S605 & DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x00)
                Local0 = (S605 & DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x11, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (S605 & DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x00)
            Local0 = (S605 & DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x13, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Local0 = (S605 & M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x00)
            Local0 = (S605 & M601 (0x01, 0x13))
            M600 (Arg0, 0x15, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S605 & DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x00)
                Local0 = (S605 & DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFE7CB391D650A284)
            }

            /* Conversion of the second operand */

            Store ((0x00 & S605), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xFFFFFFFFFFFFFFFF & S605), Local0)
            M600 (Arg0, 0x19, Local0, 0xFE7CB391D650A284)
            Store ((AUI5 & S605), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUIJ & S605), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) & S605), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUIJ)) & S605), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFE7CB391D650A284)
            }

            Store ((DerefOf (PAUI [0x05]) & S605), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x13]) & S605), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) & S605), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x13) & S605), Local0)
            M600 (Arg0, 0x21, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) & S605), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x13, 0x01)) & S605), Local0)
                M600 (Arg0, 0x23, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (0x00 & S605) /* \M613.M005.S605 */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0xFFFFFFFFFFFFFFFF & S605) /* \M613.M005.S605 */
            M600 (Arg0, 0x25, Local0, 0xFE7CB391D650A284)
            Local0 = (AUI5 & S605) /* \M613.M005.S605 */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUIJ & S605) /* \M613.M005.S605 */
            M600 (Arg0, 0x27, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) & S605) /* \M613.M005.S605 */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUIJ)) & S605) /* \M613.M005.S605 */
                M600 (Arg0, 0x29, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (DerefOf (PAUI [0x05]) & S605) /* \M613.M005.S605 */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x13]) & S605) /* \M613.M005.S605 */
            M600 (Arg0, 0x2B, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) & S605) /* \M613.M005.S605 */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x13) & S605) /* \M613.M005.S605 */
            M600 (Arg0, 0x2D, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) & S605) /* \M613.M005.S605 */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x13, 0x01)) & S605) /* \M613.M005.S605 */
                M600 (Arg0, 0x2F, Local0, 0xFE7CB391D650A284)
            }

            /* Conversion of the both operands */

            Store ((S601 & S605), Local0)
            M600 (Arg0, 0x30, Local0, 0x0200)
            Store ((S605 & S601), Local0)
            M600 (Arg0, 0x31, Local0, 0x0200)
            Local0 = (S601 & S605) /* \M613.M005.S605 */
            M600 (Arg0, 0x32, Local0, 0x0200)
            Local0 = (S605 & S601) /* \M613.M005.S601 */
            M600 (Arg0, 0x33, Local0, 0x0200)
        }

        /* And, 32-bit */

        Method (M006, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            /* Conversion of the first operand */

            Store ((S604 & 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x00)
            Store ((S604 & 0xFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0xC179B3FE)
            Store ((S604 & AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x00)
            Store ((S604 & AUII), Local0)
            M600 (Arg0, 0x03, Local0, 0xC179B3FE)
            If (Y078)
            {
                Store ((S604 & DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x00)
                Store ((S604 & DerefOf (RefOf (AUII))), Local0)
                M600 (Arg0, 0x05, Local0, 0xC179B3FE)
            }

            Store ((S604 & DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x00)
            Store ((S604 & DerefOf (PAUI [0x12])), Local0)
            M600 (Arg0, 0x07, Local0, 0xC179B3FE)
            /* Method returns Integer */

            Store ((S604 & M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x00)
            Store ((S604 & M601 (0x01, 0x12)), Local0)
            M600 (Arg0, 0x09, Local0, 0xC179B3FE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S604 & DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x00)
                Store ((S604 & DerefOf (M602 (0x01, 0x12, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xC179B3FE)
            }

            Local0 = (S604 & 0x00)
            M600 (Arg0, 0x0C, Local0, 0x00)
            Local0 = (S604 & 0xFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0xC179B3FE)
            Local0 = (S604 & AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x00)
            Local0 = (S604 & AUII) /* \AUII */
            M600 (Arg0, 0x0F, Local0, 0xC179B3FE)
            If (Y078)
            {
                Local0 = (S604 & DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x00)
                Local0 = (S604 & DerefOf (RefOf (AUII)))
                M600 (Arg0, 0x11, Local0, 0xC179B3FE)
            }

            Local0 = (S604 & DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x00)
            Local0 = (S604 & DerefOf (PAUI [0x12]))
            M600 (Arg0, 0x13, Local0, 0xC179B3FE)
            /* Method returns Integer */

            Local0 = (S604 & M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x00)
            Local0 = (S604 & M601 (0x01, 0x12))
            M600 (Arg0, 0x15, Local0, 0xC179B3FE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S604 & DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x00)
                Local0 = (S604 & DerefOf (M602 (0x01, 0x12, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xC179B3FE)
            }

            /* Conversion of the second operand */

            Store ((0x00 & S604), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xFFFFFFFF & S604), Local0)
            M600 (Arg0, 0x19, Local0, 0xC179B3FE)
            Store ((AUI5 & S604), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUII & S604), Local0)
            M600 (Arg0, 0x1B, Local0, 0xC179B3FE)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) & S604), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUII)) & S604), Local0)
                M600 (Arg0, 0x1D, Local0, 0xC179B3FE)
            }

            Store ((DerefOf (PAUI [0x05]) & S604), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x12]) & S604), Local0)
            M600 (Arg0, 0x1F, Local0, 0xC179B3FE)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) & S604), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x12) & S604), Local0)
            M600 (Arg0, 0x21, Local0, 0xC179B3FE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) & S604), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x12, 0x01)) & S604), Local0)
                M600 (Arg0, 0x23, Local0, 0xC179B3FE)
            }

            Local0 = (0x00 & S604) /* \M613.M006.S604 */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0xFFFFFFFF & S604) /* \M613.M006.S604 */
            M600 (Arg0, 0x25, Local0, 0xC179B3FE)
            Local0 = (AUI5 & S604) /* \M613.M006.S604 */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUII & S604) /* \M613.M006.S604 */
            M600 (Arg0, 0x27, Local0, 0xC179B3FE)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) & S604) /* \M613.M006.S604 */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUII)) & S604) /* \M613.M006.S604 */
                M600 (Arg0, 0x29, Local0, 0xC179B3FE)
            }

            Local0 = (DerefOf (PAUI [0x05]) & S604) /* \M613.M006.S604 */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x12]) & S604) /* \M613.M006.S604 */
            M600 (Arg0, 0x2B, Local0, 0xC179B3FE)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) & S604) /* \M613.M006.S604 */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x12) & S604) /* \M613.M006.S604 */
            M600 (Arg0, 0x2D, Local0, 0xC179B3FE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) & S604) /* \M613.M006.S604 */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x12, 0x01)) & S604) /* \M613.M006.S604 */
                M600 (Arg0, 0x2F, Local0, 0xC179B3FE)
            }

            /* Conversion of the both operands */

            Store ((S601 & S604), Local0)
            M600 (Arg0, 0x30, Local0, 0x0320)
            Store ((S604 & S601), Local0)
            M600 (Arg0, 0x31, Local0, 0x0320)
            Local0 = (S601 & S604) /* \M613.M006.S604 */
            M600 (Arg0, 0x32, Local0, 0x0320)
            Local0 = (S604 & S601) /* \M613.M006.S601 */
            M600 (Arg0, 0x33, Local0, 0x0320)
        }

        /* Divide, common 32-bit/64-bit test */

        Method (M007, 1, Serialized)
        {
            Name (S601, "0321")
            /* Conversion of the first operand */

            Store ((S601 / 0x01), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((S601 / 0x0321), Local0)
            M600 (Arg0, 0x01, Local0, 0x01)
            Store ((S601 / AUI6), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((S601 / AUI1), Local0)
            M600 (Arg0, 0x03, Local0, 0x01)
            If (Y078)
            {
                Store ((S601 / DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((S601 / DerefOf (RefOf (AUI1))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01)
            }

            Store ((S601 / DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((S601 / DerefOf (PAUI [0x01])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01)
            /* Method returns Integer */

            Store ((S601 / M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((S601 / M601 (0x01, 0x01)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S601 / DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((S601 / DerefOf (M602 (0x01, 0x01, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01)
            }

            Divide (S601, 0x01, Local1, Local0)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Divide (S601, 0x0321, Local1, Local0)
            M600 (Arg0, 0x0D, Local0, 0x01)
            Divide (S601, AUI6, Local1, Local0)
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Divide (S601, AUI1, Local1, Local0)
            M600 (Arg0, 0x0F, Local0, 0x01)
            If (Y078)
            {
                Divide (S601, DerefOf (RefOf (AUI6)), Local1, Local0)
                M600 (Arg0, 0x10, Local0, 0x0321)
                Divide (S601, DerefOf (RefOf (AUI1)), Local1, Local0)
                M600 (Arg0, 0x11, Local0, 0x01)
            }

            Divide (S601, DerefOf (PAUI [0x06]), Local1, Local0)
            M600 (Arg0, 0x12, Local0, 0x0321)
            Divide (S601, DerefOf (PAUI [0x01]), Local1, Local0)
            M600 (Arg0, 0x13, Local0, 0x01)
            /* Method returns Integer */

            Divide (S601, M601 (0x01, 0x06), Local1, Local0)
            M600 (Arg0, 0x14, Local0, 0x0321)
            Divide (S601, M601 (0x01, 0x01), Local1, Local0)
            M600 (Arg0, 0x15, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Divide (S601, DerefOf (M602 (0x01, 0x06, 0x01)), Local1, Local0)
                M600 (Arg0, 0x16, Local0, 0x0321)
                Divide (S601, DerefOf (M602 (0x01, 0x01, 0x01)), Local1, Local0)
                M600 (Arg0, 0x17, Local0, 0x01)
            }

            /* Conversion of the second operand */

            Store ((0x01 / S601), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x0321 / S601), Local0)
            M600 (Arg0, 0x19, Local0, 0x01)
            Store ((AUI6 / S601), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI1 / S601), Local0)
            M600 (Arg0, 0x1B, Local0, 0x01)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI6)) / S601), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI1)) / S601), Local0)
                M600 (Arg0, 0x1D, Local0, 0x01)
            }

            Store ((DerefOf (PAUI [0x06]) / S601), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x01]) / S601), Local0)
            M600 (Arg0, 0x1F, Local0, 0x01)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x06) / S601), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x01) / S601), Local0)
            M600 (Arg0, 0x21, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) / S601), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x01, 0x01)) / S601), Local0)
                M600 (Arg0, 0x23, Local0, 0x01)
            }

            Divide (0x01, S601, Local1, Local0)
            M600 (Arg0, 0x24, Local0, 0x00)
            Divide (0x0321, S601, Local1, Local0)
            M600 (Arg0, 0x25, Local0, 0x01)
            Divide (AUI6, S601, Local1, Local0)
            M600 (Arg0, 0x26, Local0, 0x00)
            Divide (AUI1, S601, Local1, Local0)
            M600 (Arg0, 0x27, Local0, 0x01)
            If (Y078)
            {
                Divide (DerefOf (RefOf (AUI6)), S601, Local1, Local0)
                M600 (Arg0, 0x28, Local0, 0x00)
                Divide (DerefOf (RefOf (AUI1)), S601, Local1, Local0)
                M600 (Arg0, 0x29, Local0, 0x01)
            }

            Divide (DerefOf (PAUI [0x06]), S601, Local1, Local0)
            M600 (Arg0, 0x2A, Local0, 0x00)
            Divide (DerefOf (PAUI [0x01]), S601, Local1, Local0)
            M600 (Arg0, 0x2B, Local0, 0x01)
            /* Method returns Integer */

            Divide (M601 (0x01, 0x06), S601, Local1, Local0)
            M600 (Arg0, 0x2C, Local0, 0x00)
            Divide (M601 (0x01, 0x01), S601, Local1, Local0)
            M600 (Arg0, 0x2D, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Divide (DerefOf (M602 (0x01, 0x06, 0x01)), S601, Local1, Local0)
                M600 (Arg0, 0x2E, Local0, 0x00)
                Divide (DerefOf (M602 (0x01, 0x01, 0x01)), S601, Local1, Local0)
                M600 (Arg0, 0x2F, Local0, 0x01)
            }
        }

        /* Divide, 64-bit */

        Method (M008, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S605, "FE7CB391D650A284")
            /* Conversion of the first operand */

            Store ((S605 / 0x01), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((S605 / 0xFE7CB391D650A284), Local0)
            M600 (Arg0, 0x01, Local0, 0x01)
            Store ((S605 / AUI6), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((S605 / AUI4), Local0)
            M600 (Arg0, 0x03, Local0, 0x01)
            If (Y078)
            {
                Store ((S605 / DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((S605 / DerefOf (RefOf (AUI4))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01)
            }

            Store ((S605 / DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((S605 / DerefOf (PAUI [0x04])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01)
            /* Method returns Integer */

            Store ((S605 / M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((S605 / M601 (0x01, 0x04)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S605 / DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((S605 / DerefOf (M602 (0x01, 0x04, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01)
            }

            Divide (S605, 0x01, Local1, Local0)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Divide (S605, 0xFE7CB391D650A284, Local1, Local0)
            M600 (Arg0, 0x0D, Local0, 0x01)
            Divide (S605, AUI6, Local1, Local0)
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Divide (S605, AUI4, Local1, Local0)
            M600 (Arg0, 0x0F, Local0, 0x01)
            If (Y078)
            {
                Divide (S605, DerefOf (RefOf (AUI6)), Local1, Local0)
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Divide (S605, DerefOf (RefOf (AUI4)), Local1, Local0)
                M600 (Arg0, 0x11, Local0, 0x01)
            }

            Divide (S605, DerefOf (PAUI [0x06]), Local1, Local0)
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Divide (S605, DerefOf (PAUI [0x04]), Local1, Local0)
            M600 (Arg0, 0x13, Local0, 0x01)
            /* Method returns Integer */

            Divide (S605, M601 (0x01, 0x06), Local1, Local0)
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Divide (S605, M601 (0x01, 0x04), Local1, Local0)
            M600 (Arg0, 0x15, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Divide (S605, DerefOf (M602 (0x01, 0x06, 0x01)), Local1, Local0)
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Divide (S605, DerefOf (M602 (0x01, 0x04, 0x01)), Local1, Local0)
                M600 (Arg0, 0x17, Local0, 0x01)
            }

            /* Conversion of the second operand */

            Store ((0x01 / S605), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xFE7CB391D650A284 / S605), Local0)
            M600 (Arg0, 0x19, Local0, 0x01)
            Store ((AUI6 / S605), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI4 / S605), Local0)
            M600 (Arg0, 0x1B, Local0, 0x01)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI6)) / S605), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI4)) / S605), Local0)
                M600 (Arg0, 0x1D, Local0, 0x01)
            }

            Store ((DerefOf (PAUI [0x06]) / S605), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x04]) / S605), Local0)
            M600 (Arg0, 0x1F, Local0, 0x01)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x06) / S605), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x04) / S605), Local0)
            M600 (Arg0, 0x21, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) / S605), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x04, 0x01)) / S605), Local0)
                M600 (Arg0, 0x23, Local0, 0x01)
            }

            Divide (0x01, S605, Local1, Local0)
            M600 (Arg0, 0x24, Local0, 0x00)
            Divide (0xFE7CB391D650A284, S605, Local1, Local0)
            M600 (Arg0, 0x25, Local0, 0x01)
            Divide (AUI6, S605, Local1, Local0)
            M600 (Arg0, 0x26, Local0, 0x00)
            Divide (AUI4, S605, Local1, Local0)
            M600 (Arg0, 0x27, Local0, 0x01)
            If (Y078)
            {
                Divide (DerefOf (RefOf (AUI6)), S605, Local1, Local0)
                M600 (Arg0, 0x28, Local0, 0x00)
                Divide (DerefOf (RefOf (AUI4)), S605, Local1, Local0)
                M600 (Arg0, 0x29, Local0, 0x01)
            }

            Divide (DerefOf (PAUI [0x06]), S605, Local1, Local0)
            M600 (Arg0, 0x2A, Local0, 0x00)
            Divide (DerefOf (PAUI [0x04]), S605, Local1, Local0)
            M600 (Arg0, 0x2B, Local0, 0x01)
            /* Method returns Integer */

            Divide (M601 (0x01, 0x06), S605, Local1, Local0)
            M600 (Arg0, 0x2C, Local0, 0x00)
            Divide (M601 (0x01, 0x04), S605, Local1, Local0)
            M600 (Arg0, 0x2D, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Divide (DerefOf (M602 (0x01, 0x06, 0x01)), S605, Local1, Local0)
                M600 (Arg0, 0x2E, Local0, 0x00)
                Divide (DerefOf (M602 (0x01, 0x04, 0x01)), S605, Local1, Local0)
                M600 (Arg0, 0x2F, Local0, 0x01)
            }

            /* Conversion of the both operands */

            Store ((S601 / S605), Local0)
            M600 (Arg0, 0x30, Local0, 0x00)
            Store ((S605 / S601), Local0)
            M600 (Arg0, 0x31, Local0, 0x0051558EB950F5A7)
            Divide (S601, S605, Local1, Local0)
            M600 (Arg0, 0x32, Local0, 0x00)
            Divide (S605, S601, Local1, Local0)
            M600 (Arg0, 0x33, Local0, 0x0051558EB950F5A7)
        }

        /* Divide, 32-bit */

        Method (M009, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            /* Conversion of the first operand */

            Store ((S604 / 0x01), Local0)
            M600 (Arg0, 0x00, Local0, 0xC179B3FE)
            Store ((S604 / 0xC179B3FE), Local0)
            M600 (Arg0, 0x01, Local0, 0x01)
            Store ((S604 / AUI6), Local0)
            M600 (Arg0, 0x02, Local0, 0xC179B3FE)
            Store ((S604 / AUI3), Local0)
            M600 (Arg0, 0x03, Local0, 0x01)
            If (Y078)
            {
                Store ((S604 / DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x04, Local0, 0xC179B3FE)
                Store ((S604 / DerefOf (RefOf (AUI3))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01)
            }

            Store ((S604 / DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x06, Local0, 0xC179B3FE)
            Store ((S604 / DerefOf (PAUI [0x03])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01)
            /* Method returns Integer */

            Store ((S604 / M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x08, Local0, 0xC179B3FE)
            Store ((S604 / M601 (0x01, 0x03)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S604 / DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xC179B3FE)
                Store ((S604 / DerefOf (M602 (0x01, 0x03, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01)
            }

            Divide (S604, 0x01, Local1, Local0)
            M600 (Arg0, 0x0C, Local0, 0xC179B3FE)
            Divide (S604, 0xC179B3FE, Local1, Local0)
            M600 (Arg0, 0x0D, Local0, 0x01)
            Divide (S604, AUI6, Local1, Local0)
            M600 (Arg0, 0x0E, Local0, 0xC179B3FE)
            Divide (S604, AUI3, Local1, Local0)
            M600 (Arg0, 0x0F, Local0, 0x01)
            If (Y078)
            {
                Divide (S604, DerefOf (RefOf (AUI6)), Local1, Local0)
                M600 (Arg0, 0x10, Local0, 0xC179B3FE)
                Divide (S604, DerefOf (RefOf (AUI3)), Local1, Local0)
                M600 (Arg0, 0x11, Local0, 0x01)
            }

            Divide (S604, DerefOf (PAUI [0x06]), Local1, Local0)
            M600 (Arg0, 0x12, Local0, 0xC179B3FE)
            Divide (S604, DerefOf (PAUI [0x03]), Local1, Local0)
            M600 (Arg0, 0x13, Local0, 0x01)
            /* Method returns Integer */

            Divide (S604, M601 (0x01, 0x06), Local1, Local0)
            M600 (Arg0, 0x14, Local0, 0xC179B3FE)
            Divide (S604, M601 (0x01, 0x03), Local1, Local0)
            M600 (Arg0, 0x15, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Divide (S604, DerefOf (M602 (0x01, 0x06, 0x01)), Local1, Local0)
                M600 (Arg0, 0x16, Local0, 0xC179B3FE)
                Divide (S604, DerefOf (M602 (0x01, 0x03, 0x01)), Local1, Local0)
                M600 (Arg0, 0x17, Local0, 0x01)
            }

            /* Conversion of the second operand */

            Store ((0x01 / S604), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xC179B3FE / S604), Local0)
            M600 (Arg0, 0x19, Local0, 0x01)
            Store ((AUI6 / S604), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI3 / S604), Local0)
            M600 (Arg0, 0x1B, Local0, 0x01)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI6)) / S604), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI3)) / S604), Local0)
                M600 (Arg0, 0x1D, Local0, 0x01)
            }

            Store ((DerefOf (PAUI [0x06]) / S604), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x03]) / S604), Local0)
            M600 (Arg0, 0x1F, Local0, 0x01)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x06) / S604), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x03) / S604), Local0)
            M600 (Arg0, 0x21, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) / S604), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x03, 0x01)) / S604), Local0)
                M600 (Arg0, 0x23, Local0, 0x01)
            }

            Divide (0x01, S604, Local1, Local0)
            M600 (Arg0, 0x24, Local0, 0x00)
            Divide (0xC179B3FE, S604, Local1, Local0)
            M600 (Arg0, 0x25, Local0, 0x01)
            Divide (AUI6, S604, Local1, Local0)
            M600 (Arg0, 0x26, Local0, 0x00)
            Divide (AUI3, S604, Local1, Local0)
            M600 (Arg0, 0x27, Local0, 0x01)
            If (Y078)
            {
                Divide (DerefOf (RefOf (AUI6)), S604, Local1, Local0)
                M600 (Arg0, 0x28, Local0, 0x00)
                Divide (DerefOf (RefOf (AUI3)), S604, Local1, Local0)
                M600 (Arg0, 0x29, Local0, 0x01)
            }

            Divide (DerefOf (PAUI [0x06]), S604, Local1, Local0)
            M600 (Arg0, 0x2A, Local0, 0x00)
            Divide (DerefOf (PAUI [0x03]), S604, Local1, Local0)
            M600 (Arg0, 0x2B, Local0, 0x01)
            /* Method returns Integer */

            Divide (M601 (0x01, 0x06), S604, Local1, Local0)
            M600 (Arg0, 0x2C, Local0, 0x00)
            Divide (M601 (0x01, 0x03), S604, Local1, Local0)
            M600 (Arg0, 0x2D, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Divide (DerefOf (M602 (0x01, 0x06, 0x01)), S604, Local1, Local0)
                M600 (Arg0, 0x2E, Local0, 0x00)
                Divide (DerefOf (M602 (0x01, 0x03, 0x01)), S604, Local1, Local0)
                M600 (Arg0, 0x2F, Local0, 0x01)
            }

            /* Conversion of the both operands */

            Store ((S601 / S604), Local0)
            M600 (Arg0, 0x30, Local0, 0x00)
            Store ((S604 / S601), Local0)
            M600 (Arg0, 0x31, Local0, 0x003DD5B7)
            Divide (S601, S604, Local1, Local0)
            M600 (Arg0, 0x32, Local0, 0x00)
            Divide (S604, S601, Local1, Local0)
            M600 (Arg0, 0x33, Local0, 0x003DD5B7)
        }

        /* Mod, common 32-bit/64-bit test */

        Method (M00A, 1, Serialized)
        {
            Name (S601, "0321")
            /* Conversion of the first operand */

            Store ((S601 % 0x0322), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((S601 % 0x0320), Local0)
            M600 (Arg0, 0x01, Local0, 0x01)
            Store ((S601 % AUIG), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((S601 % AUIH), Local0)
            M600 (Arg0, 0x03, Local0, 0x01)
            If (Y078)
            {
                Store ((S601 % DerefOf (RefOf (AUIG))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((S601 % DerefOf (RefOf (AUIH))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01)
            }

            Store ((S601 % DerefOf (PAUI [0x10])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((S601 % DerefOf (PAUI [0x11])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01)
            /* Method returns Integer */

            Store ((S601 % M601 (0x01, 0x10)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((S601 % M601 (0x01, 0x11)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S601 % DerefOf (M602 (0x01, 0x10, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((S601 % DerefOf (M602 (0x01, 0x11, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01)
            }

            Local0 = (S601 % 0x0322)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (S601 % 0x0320)
            M600 (Arg0, 0x0D, Local0, 0x01)
            Local0 = (S601 % AUIG) /* \AUIG */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (S601 % AUIH) /* \AUIH */
            M600 (Arg0, 0x0F, Local0, 0x01)
            If (Y078)
            {
                Local0 = (S601 % DerefOf (RefOf (AUIG)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (S601 % DerefOf (RefOf (AUIH)))
                M600 (Arg0, 0x11, Local0, 0x01)
            }

            Local0 = (S601 % DerefOf (PAUI [0x10]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (S601 % DerefOf (PAUI [0x11]))
            M600 (Arg0, 0x13, Local0, 0x01)
            /* Method returns Integer */

            Local0 = (S601 % M601 (0x01, 0x10))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (S601 % M601 (0x01, 0x11))
            M600 (Arg0, 0x15, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S601 % DerefOf (M602 (0x01, 0x10, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (S601 % DerefOf (M602 (0x01, 0x11, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x01)
            }

            /* Conversion of the second operand */

            Store ((0x0322 % S601), Local0)
            M600 (Arg0, 0x18, Local0, 0x01)
            Store ((0x0320 % S601), Local0)
            M600 (Arg0, 0x19, Local0, 0x0320)
            Store ((AUIG % S601), Local0)
            M600 (Arg0, 0x1A, Local0, 0x01)
            Store ((AUIH % S601), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0320)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUIG)) % S601), Local0)
                M600 (Arg0, 0x1C, Local0, 0x01)
                Store ((DerefOf (RefOf (AUIH)) % S601), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0320)
            }

            Store ((DerefOf (PAUI [0x10]) % S601), Local0)
            M600 (Arg0, 0x1E, Local0, 0x01)
            Store ((DerefOf (PAUI [0x11]) % S601), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0320)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x10) % S601), Local0)
            M600 (Arg0, 0x20, Local0, 0x01)
            Store ((M601 (0x01, 0x11) % S601), Local0)
            M600 (Arg0, 0x21, Local0, 0x0320)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x10, 0x01)) % S601), Local0)
                M600 (Arg0, 0x22, Local0, 0x01)
                Store ((DerefOf (M602 (0x01, 0x11, 0x01)) % S601), Local0)
                M600 (Arg0, 0x23, Local0, 0x0320)
            }

            Local0 = (0x0322 % S601) /* \M613.M00A.S601 */
            M600 (Arg0, 0x24, Local0, 0x01)
            Local0 = (0x0320 % S601) /* \M613.M00A.S601 */
            M600 (Arg0, 0x25, Local0, 0x0320)
            Local0 = (AUIG % S601) /* \M613.M00A.S601 */
            M600 (Arg0, 0x26, Local0, 0x01)
            Local0 = (AUIH % S601) /* \M613.M00A.S601 */
            M600 (Arg0, 0x27, Local0, 0x0320)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUIG)) % S601) /* \M613.M00A.S601 */
                M600 (Arg0, 0x28, Local0, 0x01)
                Local0 = (DerefOf (RefOf (AUIH)) % S601) /* \M613.M00A.S601 */
                M600 (Arg0, 0x29, Local0, 0x0320)
            }

            Local0 = (DerefOf (PAUI [0x10]) % S601) /* \M613.M00A.S601 */
            M600 (Arg0, 0x2A, Local0, 0x01)
            Local0 = (DerefOf (PAUI [0x11]) % S601) /* \M613.M00A.S601 */
            M600 (Arg0, 0x2B, Local0, 0x0320)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x10) % S601) /* \M613.M00A.S601 */
            M600 (Arg0, 0x2C, Local0, 0x01)
            Local0 = (M601 (0x01, 0x11) % S601) /* \M613.M00A.S601 */
            M600 (Arg0, 0x2D, Local0, 0x0320)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) % S601) /* \M613.M00A.S601 */
                M600 (Arg0, 0x2E, Local0, 0x01)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) % S601) /* \M613.M00A.S601 */
                M600 (Arg0, 0x2F, Local0, 0x0320)
            }
        }

        /* Mod, 64-bit */

        Method (M00B, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S605, "FE7CB391D650A284")
            /* Conversion of the first operand */

            Store ((S605 % 0xFE7CB391D650A285), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((S605 % 0xFE7CB391D650A283), Local0)
            M600 (Arg0, 0x01, Local0, 0x01)
            Store ((S605 % AUID), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((S605 % AUIF), Local0)
            M600 (Arg0, 0x03, Local0, 0x01)
            If (Y078)
            {
                Store ((S605 % DerefOf (RefOf (AUID))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((S605 % DerefOf (RefOf (AUIF))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01)
            }

            Store ((S605 % DerefOf (PAUI [0x0D])), Local0)
            M600 (Arg0, 0x0D, Local0, 0xFE7CB391D650A284)
            Store ((S605 % DerefOf (PAUI [0x0F])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01)
            /* Method returns Integer */

            Store ((S605 % M601 (0x01, 0x0D)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((S605 % M601 (0x01, 0x0F)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S605 % DerefOf (M602 (0x01, 0x0D, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((S605 % DerefOf (M602 (0x01, 0x0F, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01)
            }

            Local0 = (S605 % 0xFE7CB391D650A285)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 % 0xFE7CB391D650A283)
            M600 (Arg0, 0x0D, Local0, 0x01)
            Local0 = (S605 % AUID) /* \AUID */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 % AUIF) /* \AUIF */
            M600 (Arg0, 0x0F, Local0, 0x01)
            If (Y078)
            {
                Local0 = (S605 % DerefOf (RefOf (AUID)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (S605 % DerefOf (RefOf (AUIF)))
                M600 (Arg0, 0x11, Local0, 0x01)
            }

            Local0 = (S605 % DerefOf (PAUI [0x0D]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 % DerefOf (PAUI [0x0F]))
            M600 (Arg0, 0x13, Local0, 0x01)
            /* Method returns Integer */

            Local0 = (S605 % M601 (0x01, 0x0D))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 % M601 (0x01, 0x0F))
            M600 (Arg0, 0x15, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S605 % DerefOf (M602 (0x01, 0x0D, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (S605 % DerefOf (M602 (0x01, 0x0F, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x01)
            }

            /* Conversion of the second operand */

            Store ((0xFE7CB391D650A285 % S605), Local0)
            M600 (Arg0, 0x18, Local0, 0x01)
            Store ((0xFE7CB391D650A283 % S605), Local0)
            M600 (Arg0, 0x19, Local0, 0xFE7CB391D650A283)
            Store ((AUID % S605), Local0)
            M600 (Arg0, 0x1A, Local0, 0x01)
            Store ((AUIF % S605), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFE7CB391D650A283)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUID)) % S605), Local0)
                M600 (Arg0, 0x1C, Local0, 0x01)
                Store ((DerefOf (RefOf (AUIF)) % S605), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFE7CB391D650A283)
            }

            Store ((DerefOf (PAUI [0x0D]) % S605), Local0)
            M600 (Arg0, 0x1E, Local0, 0x01)
            Store ((DerefOf (PAUI [0x0F]) % S605), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFE7CB391D650A283)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x0D) % S605), Local0)
            M600 (Arg0, 0x20, Local0, 0x01)
            Store ((M601 (0x01, 0x0F) % S605), Local0)
            M600 (Arg0, 0x21, Local0, 0xFE7CB391D650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x0D, 0x01)) % S605), Local0)
                M600 (Arg0, 0x22, Local0, 0x01)
                Store ((DerefOf (M602 (0x01, 0x0F, 0x01)) % S605), Local0)
                M600 (Arg0, 0x23, Local0, 0xFE7CB391D650A283)
            }

            Local0 = (0xFE7CB391D650A285 % S605) /* \M613.M00B.S605 */
            M600 (Arg0, 0x24, Local0, 0x01)
            Local0 = (0xFE7CB391D650A283 % S605) /* \M613.M00B.S605 */
            M600 (Arg0, 0x25, Local0, 0xFE7CB391D650A283)
            Local0 = (AUID % S605) /* \M613.M00B.S605 */
            M600 (Arg0, 0x26, Local0, 0x01)
            Local0 = (AUIF % S605) /* \M613.M00B.S605 */
            M600 (Arg0, 0x27, Local0, 0xFE7CB391D650A283)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUID)) % S605) /* \M613.M00B.S605 */
                M600 (Arg0, 0x28, Local0, 0x01)
                Local0 = (DerefOf (RefOf (AUIF)) % S605) /* \M613.M00B.S605 */
                M600 (Arg0, 0x29, Local0, 0xFE7CB391D650A283)
            }

            Local0 = (DerefOf (PAUI [0x0D]) % S605) /* \M613.M00B.S605 */
            M600 (Arg0, 0x2A, Local0, 0x01)
            Local0 = (DerefOf (PAUI [0x0F]) % S605) /* \M613.M00B.S605 */
            M600 (Arg0, 0x2B, Local0, 0xFE7CB391D650A283)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x0D) % S605) /* \M613.M00B.S605 */
            M600 (Arg0, 0x2C, Local0, 0x01)
            Local0 = (M601 (0x01, 0x0F) % S605) /* \M613.M00B.S605 */
            M600 (Arg0, 0x2D, Local0, 0xFE7CB391D650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) % S605) /* \M613.M00B.S605 */
                M600 (Arg0, 0x2E, Local0, 0x01)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) % S605) /* \M613.M00B.S605 */
                M600 (Arg0, 0x2F, Local0, 0xFE7CB391D650A283)
            }

            /* Conversion of the both operands */

            Store ((S601 % S605), Local0)
            M600 (Arg0, 0x30, Local0, 0x0321)
            Store ((S605 % S601), Local0)
            M600 (Arg0, 0x31, Local0, 0x02FD)
            Local0 = (S601 % S605) /* \M613.M00B.S605 */
            M600 (Arg0, 0x32, Local0, 0x0321)
            Local0 = (S605 % S601) /* \M613.M00B.S601 */
            M600 (Arg0, 0x33, Local0, 0x02FD)
        }

        /* Mod, 32-bit */

        Method (M00C, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            /* Conversion of the first operand */

            Store ((S604 % 0xC179B3FF), Local0)
            M600 (Arg0, 0x00, Local0, 0xC179B3FE)
            Store ((S604 % 0xC179B3FD), Local0)
            M600 (Arg0, 0x01, Local0, 0x01)
            Store ((S604 % AUIC), Local0)
            M600 (Arg0, 0x02, Local0, 0xC179B3FE)
            Store ((S604 % AUIE), Local0)
            M600 (Arg0, 0x0E, Local0, 0x01)
            If (Y078)
            {
                Store ((S604 % DerefOf (RefOf (AUIC))), Local0)
                M600 (Arg0, 0x04, Local0, 0xC179B3FE)
                Store ((S604 % DerefOf (RefOf (AUIE))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01)
            }

            Store ((S604 % DerefOf (PAUI [0x0C])), Local0)
            M600 (Arg0, 0x0C, Local0, 0xC179B3FE)
            Store ((S604 % DerefOf (PAUI [0x0E])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01)
            /* Method returns Integer */

            Store ((S604 % M601 (0x01, 0x0C)), Local0)
            M600 (Arg0, 0x08, Local0, 0xC179B3FE)
            Store ((S604 % M601 (0x01, 0x0E)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S604 % DerefOf (M602 (0x01, 0x0C, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xC179B3FE)
                Store ((S604 % DerefOf (M602 (0x01, 0x0E, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01)
            }

            Local0 = (S604 % 0xC179B3FF)
            M600 (Arg0, 0x0C, Local0, 0xC179B3FE)
            Local0 = (S604 % 0xC179B3FD)
            M600 (Arg0, 0x0D, Local0, 0x01)
            Local0 = (S604 % AUIC) /* \AUIC */
            M600 (Arg0, 0x0E, Local0, 0xC179B3FE)
            Local0 = (S604 % AUIE) /* \AUIE */
            M600 (Arg0, 0x0F, Local0, 0x01)
            If (Y078)
            {
                Local0 = (S604 % DerefOf (RefOf (AUIC)))
                M600 (Arg0, 0x10, Local0, 0xC179B3FE)
                Local0 = (S604 % DerefOf (RefOf (AUIE)))
                M600 (Arg0, 0x11, Local0, 0x01)
            }

            Local0 = (S604 % DerefOf (PAUI [0x0C]))
            M600 (Arg0, 0x12, Local0, 0xC179B3FE)
            Local0 = (S604 % DerefOf (PAUI [0x0E]))
            M600 (Arg0, 0x13, Local0, 0x01)
            /* Method returns Integer */

            Local0 = (S604 % M601 (0x01, 0x0C))
            M600 (Arg0, 0x14, Local0, 0xC179B3FE)
            Local0 = (S604 % M601 (0x01, 0x0E))
            M600 (Arg0, 0x15, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S604 % DerefOf (M602 (0x01, 0x0C, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xC179B3FE)
                Local0 = (S604 % DerefOf (M602 (0x01, 0x0E, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x01)
            }

            /* Conversion of the second operand */

            Store ((0xC179B3FF % S604), Local0)
            M600 (Arg0, 0x18, Local0, 0x01)
            Store ((0xC179B3FD % S604), Local0)
            M600 (Arg0, 0x19, Local0, 0xC179B3FD)
            Store ((AUIC % S604), Local0)
            M600 (Arg0, 0x1A, Local0, 0x01)
            Store ((AUIE % S604), Local0)
            M600 (Arg0, 0x1B, Local0, 0xC179B3FD)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUIC)) % S604), Local0)
                M600 (Arg0, 0x1C, Local0, 0x01)
                Store ((DerefOf (RefOf (AUIE)) % S604), Local0)
                M600 (Arg0, 0x1D, Local0, 0xC179B3FD)
            }

            Store ((DerefOf (PAUI [0x0C]) % S604), Local0)
            M600 (Arg0, 0x1E, Local0, 0x01)
            Store ((DerefOf (PAUI [0x0E]) % S604), Local0)
            M600 (Arg0, 0x1F, Local0, 0xC179B3FD)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x0C) % S604), Local0)
            M600 (Arg0, 0x20, Local0, 0x01)
            Store ((M601 (0x01, 0x0E) % S604), Local0)
            M600 (Arg0, 0x21, Local0, 0xC179B3FD)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x0C, 0x01)) % S604), Local0)
                M600 (Arg0, 0x22, Local0, 0x01)
                Store ((DerefOf (M602 (0x01, 0x0E, 0x01)) % S604), Local0)
                M600 (Arg0, 0x23, Local0, 0xC179B3FD)
            }

            Local0 = (0xC179B3FF % S604) /* \M613.M00C.S604 */
            M600 (Arg0, 0x24, Local0, 0x01)
            Local0 = (0xC179B3FD % S604) /* \M613.M00C.S604 */
            M600 (Arg0, 0x25, Local0, 0xC179B3FD)
            Local0 = (AUIC % S604) /* \M613.M00C.S604 */
            M600 (Arg0, 0x26, Local0, 0x01)
            Local0 = (AUIE % S604) /* \M613.M00C.S604 */
            M600 (Arg0, 0x27, Local0, 0xC179B3FD)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUIC)) % S604) /* \M613.M00C.S604 */
                M600 (Arg0, 0x28, Local0, 0x01)
                Local0 = (DerefOf (RefOf (AUIE)) % S604) /* \M613.M00C.S604 */
                M600 (Arg0, 0x29, Local0, 0xC179B3FD)
            }

            Local0 = (DerefOf (PAUI [0x0C]) % S604) /* \M613.M00C.S604 */
            M600 (Arg0, 0x2A, Local0, 0x01)
            Local0 = (DerefOf (PAUI [0x0E]) % S604) /* \M613.M00C.S604 */
            M600 (Arg0, 0x2B, Local0, 0xC179B3FD)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x0C) % S604) /* \M613.M00C.S604 */
            M600 (Arg0, 0x2C, Local0, 0x01)
            Local0 = (M601 (0x01, 0x0E) % S604) /* \M613.M00C.S604 */
            M600 (Arg0, 0x2D, Local0, 0xC179B3FD)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x0C, 0x01)) % S604) /* \M613.M00C.S604 */
                M600 (Arg0, 0x2E, Local0, 0x01)
                Local0 = (DerefOf (M602 (0x01, 0x0E, 0x01)) % S604) /* \M613.M00C.S604 */
                M600 (Arg0, 0x2F, Local0, 0xC179B3FD)
            }

            /* Conversion of the both operands */

            Store ((S601 % S604), Local0)
            M600 (Arg0, 0x30, Local0, 0x0321)
            Store ((S604 % S601), Local0)
            M600 (Arg0, 0x31, Local0, 0x0267)
            Local0 = (S601 % S604) /* \M613.M00C.S604 */
            M600 (Arg0, 0x32, Local0, 0x0321)
            Local0 = (S604 % S601) /* \M613.M00C.S601 */
            M600 (Arg0, 0x33, Local0, 0x0267)
        }

        /* Multiply, common 32-bit/64-bit test */

        Method (M00D, 1, Serialized)
        {
            Name (S601, "0321")
            /* Conversion of the first operand */

            Store ((S601 * 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x00)
            Store ((S601 * 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x0321)
            Store ((S601 * AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x00)
            Store ((S601 * AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x0321)
            If (Y078)
            {
                Store ((S601 * DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x00)
                Store ((S601 * DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x0321)
            }

            Store ((S601 * DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x00)
            Store ((S601 * DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x0321)
            /* Method returns Integer */

            Store ((S601 * M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x00)
            Store ((S601 * M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S601 * DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x00)
                Store ((S601 * DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x0321)
            }

            Local0 = (S601 * 0x00)
            M600 (Arg0, 0x0C, Local0, 0x00)
            Local0 = (S601 * 0x01)
            M600 (Arg0, 0x0D, Local0, 0x0321)
            Local0 = (S601 * AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x00)
            Local0 = (S601 * AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x0321)
            If (Y078)
            {
                Local0 = (S601 * DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x00)
                Local0 = (S601 * DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x0321)
            }

            Local0 = (S601 * DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x00)
            Local0 = (S601 * DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x0321)
            /* Method returns Integer */

            Local0 = (S601 * M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x00)
            Local0 = (S601 * M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S601 * DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x00)
                Local0 = (S601 * DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x0321)
            }

            /* Conversion of the second operand */

            Store ((0x00 * S601), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x01 * S601), Local0)
            M600 (Arg0, 0x19, Local0, 0x0321)
            Store ((AUI5 * S601), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI6 * S601), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0321)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) * S601), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI6)) * S601), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0321)
            }

            Store ((DerefOf (PAUI [0x05]) * S601), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x06]) * S601), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0321)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) * S601), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x06) * S601), Local0)
            M600 (Arg0, 0x21, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) * S601), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) * S601), Local0)
                M600 (Arg0, 0x23, Local0, 0x0321)
            }

            Local0 = (0x00 * S601) /* \M613.M00D.S601 */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0x01 * S601) /* \M613.M00D.S601 */
            M600 (Arg0, 0x25, Local0, 0x0321)
            Local0 = (AUI5 * S601) /* \M613.M00D.S601 */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI6 * S601) /* \M613.M00D.S601 */
            M600 (Arg0, 0x27, Local0, 0x0321)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) * S601) /* \M613.M00D.S601 */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI6)) * S601) /* \M613.M00D.S601 */
                M600 (Arg0, 0x29, Local0, 0x0321)
            }

            Local0 = (DerefOf (PAUI [0x05]) * S601) /* \M613.M00D.S601 */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x06]) * S601) /* \M613.M00D.S601 */
            M600 (Arg0, 0x2B, Local0, 0x0321)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) * S601) /* \M613.M00D.S601 */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x06) * S601) /* \M613.M00D.S601 */
            M600 (Arg0, 0x2D, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) * S601) /* \M613.M00D.S601 */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) * S601) /* \M613.M00D.S601 */
                M600 (Arg0, 0x2F, Local0, 0x0321)
            }
        }

        /* Multiply, 64-bit */

        Method (M00E, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S605, "FE7CB391D650A284")
            /* Conversion of the first operand */

            Store ((S605 * 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x00)
            Store ((S605 * 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xFE7CB391D650A284)
            Store ((S605 * AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x00)
            Store ((S605 * AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Store ((S605 * DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x00)
                Store ((S605 * DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFE7CB391D650A284)
            }

            Store ((S605 * DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x00)
            Store ((S605 * DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Store ((S605 * M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x00)
            Store ((S605 * M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S605 * DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x00)
                Store ((S605 * DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (S605 * 0x00)
            M600 (Arg0, 0x0C, Local0, 0x00)
            Local0 = (S605 * 0x01)
            M600 (Arg0, 0x0D, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 * AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x00)
            Local0 = (S605 * AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Local0 = (S605 * DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x00)
                Local0 = (S605 * DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (S605 * DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x00)
            Local0 = (S605 * DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Local0 = (S605 * M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x00)
            Local0 = (S605 * M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S605 * DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x00)
                Local0 = (S605 * DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFE7CB391D650A284)
            }

            /* Conversion of the second operand */

            Store ((0x00 * S605), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x01 * S605), Local0)
            M600 (Arg0, 0x19, Local0, 0xFE7CB391D650A284)
            Store ((AUI5 * S605), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI6 * S605), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) * S605), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI6)) * S605), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFE7CB391D650A284)
            }

            Store ((DerefOf (PAUI [0x05]) * S605), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x06]) * S605), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) * S605), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x06) * S605), Local0)
            M600 (Arg0, 0x21, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) * S605), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) * S605), Local0)
                M600 (Arg0, 0x23, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (0x00 * S605) /* \M613.M00E.S605 */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0x01 * S605) /* \M613.M00E.S605 */
            M600 (Arg0, 0x25, Local0, 0xFE7CB391D650A284)
            Local0 = (AUI5 * S605) /* \M613.M00E.S605 */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI6 * S605) /* \M613.M00E.S605 */
            M600 (Arg0, 0x27, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) * S605) /* \M613.M00E.S605 */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI6)) * S605) /* \M613.M00E.S605 */
                M600 (Arg0, 0x29, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (DerefOf (PAUI [0x05]) * S605) /* \M613.M00E.S605 */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x06]) * S605) /* \M613.M00E.S605 */
            M600 (Arg0, 0x2B, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) * S605) /* \M613.M00E.S605 */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x06) * S605) /* \M613.M00E.S605 */
            M600 (Arg0, 0x2D, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) * S605) /* \M613.M00E.S605 */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) * S605) /* \M613.M00E.S605 */
                M600 (Arg0, 0x2F, Local0, 0xFE7CB391D650A284)
            }

            /* Conversion of the both operands */

            Store ((S601 * S605), Local0)
            M600 (Arg0, 0x30, Local0, 0x442DDB4F924C7F04)
            Store ((S605 * S601), Local0)
            M600 (Arg0, 0x31, Local0, 0x442DDB4F924C7F04)
            Local0 = (S601 * S605) /* \M613.M00E.S605 */
            M600 (Arg0, 0x32, Local0, 0x442DDB4F924C7F04)
            Local0 = (S605 * S601) /* \M613.M00E.S601 */
            M600 (Arg0, 0x33, Local0, 0x442DDB4F924C7F04)
        }

        /* Multiply, 32-bit */

        Method (M00F, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            /* Conversion of the first operand */

            Store ((S604 * 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x00)
            Store ((S604 * 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xC179B3FE)
            Store ((S604 * AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x00)
            Store ((S604 * AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xC179B3FE)
            If (Y078)
            {
                Store ((S604 * DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x00)
                Store ((S604 * DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xC179B3FE)
            }

            Store ((S604 * DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x00)
            Store ((S604 * DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xC179B3FE)
            /* Method returns Integer */

            Store ((S604 * M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x00)
            Store ((S604 * M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xC179B3FE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S604 * DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x00)
                Store ((S604 * DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xC179B3FE)
            }

            Local0 = (S604 * 0x00)
            M600 (Arg0, 0x0C, Local0, 0x00)
            Local0 = (S604 * 0x01)
            M600 (Arg0, 0x0D, Local0, 0xC179B3FE)
            Local0 = (S604 * AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x00)
            Local0 = (S604 * AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xC179B3FE)
            If (Y078)
            {
                Local0 = (S604 * DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x00)
                Local0 = (S604 * DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xC179B3FE)
            }

            Local0 = (S604 * DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x00)
            Local0 = (S604 * DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xC179B3FE)
            /* Method returns Integer */

            Local0 = (S604 * M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x00)
            Local0 = (S604 * M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xC179B3FE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S604 * DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x00)
                Local0 = (S604 * DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xC179B3FE)
            }

            /* Conversion of the second operand */

            Store ((0x00 * S604), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x01 * S604), Local0)
            M600 (Arg0, 0x19, Local0, 0xC179B3FE)
            Store ((AUI5 * S604), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI6 * S604), Local0)
            M600 (Arg0, 0x1B, Local0, 0xC179B3FE)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) * S604), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI6)) * S604), Local0)
                M600 (Arg0, 0x1D, Local0, 0xC179B3FE)
            }

            Store ((DerefOf (PAUI [0x05]) * S604), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x06]) * S604), Local0)
            M600 (Arg0, 0x1F, Local0, 0xC179B3FE)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) * S604), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x06) * S604), Local0)
            M600 (Arg0, 0x21, Local0, 0xC179B3FE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) * S604), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) * S604), Local0)
                M600 (Arg0, 0x23, Local0, 0xC179B3FE)
            }

            Local0 = (0x00 * S604) /* \M613.M00F.S604 */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0x01 * S604) /* \M613.M00F.S604 */
            M600 (Arg0, 0x25, Local0, 0xC179B3FE)
            Local0 = (AUI5 * S604) /* \M613.M00F.S604 */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI6 * S604) /* \M613.M00F.S604 */
            M600 (Arg0, 0x27, Local0, 0xC179B3FE)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) * S604) /* \M613.M00F.S604 */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI6)) * S604) /* \M613.M00F.S604 */
                M600 (Arg0, 0x29, Local0, 0xC179B3FE)
            }

            Local0 = (DerefOf (PAUI [0x05]) * S604) /* \M613.M00F.S604 */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x06]) * S604) /* \M613.M00F.S604 */
            M600 (Arg0, 0x2B, Local0, 0xC179B3FE)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) * S604) /* \M613.M00F.S604 */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x06) * S604) /* \M613.M00F.S604 */
            M600 (Arg0, 0x2D, Local0, 0xC179B3FE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) * S604) /* \M613.M00F.S604 */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) * S604) /* \M613.M00F.S604 */
                M600 (Arg0, 0x2F, Local0, 0xC179B3FE)
            }

            /* Conversion of the both operands */

            Store ((S601 * S604), Local0)
            M600 (Arg0, 0x30, Local0, 0x5DCC2DBE)
            Store ((S604 * S601), Local0)
            M600 (Arg0, 0x31, Local0, 0x5DCC2DBE)
            Local0 = (S601 * S604) /* \M613.M00F.S604 */
            M600 (Arg0, 0x32, Local0, 0x5DCC2DBE)
            Local0 = (S604 * S601) /* \M613.M00F.S601 */
            M600 (Arg0, 0x33, Local0, 0x5DCC2DBE)
        }

        /* NAnd, common 32-bit/64-bit test */

        Method (M010, 1, Serialized)
        {
            Name (S601, "0321")
            /* Conversion of the first operand */

            Local0 = NAnd (S601, 0x00)
            M600 (Arg0, 0x00, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (S601, 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x01, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NAnd (S601, AUI5)
            M600 (Arg0, 0x02, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (S601, AUIJ)
            M600 (Arg0, 0x03, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                Local0 = NAnd (S601, DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (S601, DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x05, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Local0 = NAnd (S601, DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (S601, DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x07, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            Local0 = NAnd (S601, M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (S601, M601 (0x01, 0x13))
            M600 (Arg0, 0x09, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NAnd (S601, DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (S601, DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x0B, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            NAnd (S601, 0x00, Local0)
            M600 (Arg0, 0x0C, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (S601, 0xFFFFFFFFFFFFFFFF, Local0)
            M600 (Arg0, 0x0D, Local0, 0xFFFFFFFFFFFFFCDE)
            NAnd (S601, AUI5, Local0)
            M600 (Arg0, 0x0E, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (S601, AUIJ, Local0)
            M600 (Arg0, 0x0F, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                NAnd (S601, DerefOf (RefOf (AUI5)), Local0)
                M600 (Arg0, 0x10, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (S601, DerefOf (RefOf (AUIJ)), Local0)
                M600 (Arg0, 0x11, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            NAnd (S601, DerefOf (PAUI [0x05]), Local0)
            M600 (Arg0, 0x12, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (S601, DerefOf (PAUI [0x13]), Local0)
            M600 (Arg0, 0x13, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            NAnd (S601, M601 (0x01, 0x05), Local0)
            M600 (Arg0, 0x14, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (S601, M601 (0x01, 0x13), Local0)
            M600 (Arg0, 0x15, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NAnd (S601, DerefOf (M602 (0x01, 0x05, 0x01)), Local0)
                M600 (Arg0, 0x16, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (S601, DerefOf (M602 (0x01, 0x13, 0x01)), Local0)
                M600 (Arg0, 0x17, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            /* Conversion of the second operand */

            Local0 = NAnd (0x00, S601)
            M600 (Arg0, 0x18, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (0xFFFFFFFFFFFFFFFF, S601)
            M600 (Arg0, 0x19, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NAnd (AUI5, S601)
            M600 (Arg0, 0x1A, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (AUIJ, S601)
            M600 (Arg0, 0x1B, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                Local0 = NAnd (DerefOf (RefOf (AUI5)), S601)
                M600 (Arg0, 0x1C, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (DerefOf (RefOf (AUIJ)), S601)
                M600 (Arg0, 0x1D, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Local0 = NAnd (DerefOf (PAUI [0x05]), S601)
            M600 (Arg0, 0x1E, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (DerefOf (PAUI [0x13]), S601)
            M600 (Arg0, 0x1F, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            Local0 = NAnd (M601 (0x01, 0x05), S601)
            M600 (Arg0, 0x20, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (M601 (0x01, 0x13), S601)
            M600 (Arg0, 0x21, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NAnd (DerefOf (M602 (0x01, 0x05, 0x01)), S601)
                M600 (Arg0, 0x22, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (DerefOf (M602 (0x01, 0x13, 0x01)), S601)
                M600 (Arg0, 0x23, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            NAnd (0x00, S601, Local0)
            M600 (Arg0, 0x24, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (0xFFFFFFFFFFFFFFFF, S601, Local0)
            M600 (Arg0, 0x25, Local0, 0xFFFFFFFFFFFFFCDE)
            NAnd (AUI5, S601, Local0)
            M600 (Arg0, 0x26, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (AUIJ, S601, Local0)
            M600 (Arg0, 0x27, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                NAnd (DerefOf (RefOf (AUI5)), S601, Local0)
                M600 (Arg0, 0x28, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (DerefOf (RefOf (AUIJ)), S601, Local0)
                M600 (Arg0, 0x29, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            NAnd (DerefOf (PAUI [0x05]), S601, Local0)
            M600 (Arg0, 0x2A, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (DerefOf (PAUI [0x13]), S601, Local0)
            M600 (Arg0, 0x2B, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            NAnd (M601 (0x01, 0x05), S601, Local0)
            M600 (Arg0, 0x2C, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (M601 (0x01, 0x13), S601, Local0)
            M600 (Arg0, 0x2D, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NAnd (DerefOf (M602 (0x01, 0x05, 0x01)), S601, Local0)
                M600 (Arg0, 0x2E, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (DerefOf (M602 (0x01, 0x13, 0x01)), S601, Local0)
                M600 (Arg0, 0x2F, Local0, 0xFFFFFFFFFFFFFCDE)
            }
        }

        /* NAnd, 64-bit */

        Method (M011, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S605, "FE7CB391D650A284")
            /* Conversion of the first operand */

            Local0 = NAnd (S605, 0x00)
            M600 (Arg0, 0x00, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (S605, 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x01, Local0, 0x01834C6E29AF5D7B)
            Local0 = NAnd (S605, AUI5)
            M600 (Arg0, 0x02, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (S605, AUIJ)
            M600 (Arg0, 0x03, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                Local0 = NAnd (S605, DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (S605, DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x05, Local0, 0x01834C6E29AF5D7B)
            }

            Local0 = NAnd (S605, DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (S605, DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x07, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            Local0 = NAnd (S605, M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (S605, M601 (0x01, 0x13))
            M600 (Arg0, 0x09, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NAnd (S605, DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (S605, DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x0B, Local0, 0x01834C6E29AF5D7B)
            }

            NAnd (S605, 0x00, Local0)
            M600 (Arg0, 0x0C, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (S605, 0xFFFFFFFFFFFFFFFF, Local0)
            M600 (Arg0, 0x0D, Local0, 0x01834C6E29AF5D7B)
            NAnd (S605, AUI5, Local0)
            M600 (Arg0, 0x0E, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (S605, AUIJ, Local0)
            M600 (Arg0, 0x0F, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                NAnd (S605, DerefOf (RefOf (AUI5)), Local0)
                M600 (Arg0, 0x10, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (S605, DerefOf (RefOf (AUIJ)), Local0)
                M600 (Arg0, 0x11, Local0, 0x01834C6E29AF5D7B)
            }

            NAnd (S605, DerefOf (PAUI [0x05]), Local0)
            M600 (Arg0, 0x12, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (S605, DerefOf (PAUI [0x13]), Local0)
            M600 (Arg0, 0x13, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            NAnd (S605, M601 (0x01, 0x05), Local0)
            M600 (Arg0, 0x14, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (S605, M601 (0x01, 0x13), Local0)
            M600 (Arg0, 0x15, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NAnd (S605, DerefOf (M602 (0x01, 0x05, 0x01)), Local0)
                M600 (Arg0, 0x16, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (S605, DerefOf (M602 (0x01, 0x13, 0x01)), Local0)
                M600 (Arg0, 0x17, Local0, 0x01834C6E29AF5D7B)
            }

            /* Conversion of the second operand */

            Local0 = NAnd (0x00, S605)
            M600 (Arg0, 0x18, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (0xFFFFFFFFFFFFFFFF, S605)
            M600 (Arg0, 0x19, Local0, 0x01834C6E29AF5D7B)
            Local0 = NAnd (AUI5, S605)
            M600 (Arg0, 0x1A, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (AUIJ, S605)
            M600 (Arg0, 0x1B, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                Local0 = NAnd (DerefOf (RefOf (AUI5)), S605)
                M600 (Arg0, 0x1C, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (DerefOf (RefOf (AUIJ)), S605)
                M600 (Arg0, 0x1D, Local0, 0x01834C6E29AF5D7B)
            }

            Local0 = NAnd (DerefOf (PAUI [0x05]), S605)
            M600 (Arg0, 0x1E, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (DerefOf (PAUI [0x13]), S605)
            M600 (Arg0, 0x1F, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            Local0 = NAnd (M601 (0x01, 0x05), S605)
            M600 (Arg0, 0x20, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (M601 (0x01, 0x13), S605)
            M600 (Arg0, 0x21, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NAnd (DerefOf (M602 (0x01, 0x05, 0x01)), S605)
                M600 (Arg0, 0x22, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (DerefOf (M602 (0x01, 0x13, 0x01)), S605)
                M600 (Arg0, 0x23, Local0, 0x01834C6E29AF5D7B)
            }

            NAnd (0x00, S605, Local0)
            M600 (Arg0, 0x24, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (0xFFFFFFFFFFFFFFFF, S605, Local0)
            M600 (Arg0, 0x25, Local0, 0x01834C6E29AF5D7B)
            NAnd (AUI5, S605, Local0)
            M600 (Arg0, 0x26, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (AUIJ, S605, Local0)
            M600 (Arg0, 0x27, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                NAnd (DerefOf (RefOf (AUI5)), S605, Local0)
                M600 (Arg0, 0x28, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (DerefOf (RefOf (AUIJ)), S605, Local0)
                M600 (Arg0, 0x29, Local0, 0x01834C6E29AF5D7B)
            }

            NAnd (DerefOf (PAUI [0x05]), S605, Local0)
            M600 (Arg0, 0x2A, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (DerefOf (PAUI [0x13]), S605, Local0)
            M600 (Arg0, 0x2B, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            NAnd (M601 (0x01, 0x05), S605, Local0)
            M600 (Arg0, 0x2C, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (M601 (0x01, 0x13), S605, Local0)
            M600 (Arg0, 0x2D, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NAnd (DerefOf (M602 (0x01, 0x05, 0x01)), S605, Local0)
                M600 (Arg0, 0x2E, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (DerefOf (M602 (0x01, 0x13, 0x01)), S605, Local0)
                M600 (Arg0, 0x2F, Local0, 0x01834C6E29AF5D7B)
            }

            /* Conversion of the both operands */

            Local0 = NAnd (S601, S605)
            M600 (Arg0, 0x30, Local0, 0xFFFFFFFFFFFFFDFF)
            Local0 = NAnd (S605, S601)
            M600 (Arg0, 0x31, Local0, 0xFFFFFFFFFFFFFDFF)
            NAnd (S601, S605, Local0)
            M600 (Arg0, 0x32, Local0, 0xFFFFFFFFFFFFFDFF)
            NAnd (S605, S601, Local0)
            M600 (Arg0, 0x33, Local0, 0xFFFFFFFFFFFFFDFF)
        }

        /* NAnd, 32-bit */

        Method (M012, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            /* Conversion of the first operand */

            Local0 = NAnd (S604, 0x00)
            M600 (Arg0, 0x00, Local0, 0xFFFFFFFF)
            Local0 = NAnd (S604, 0xFFFFFFFF)
            M600 (Arg0, 0x01, Local0, 0x3E864C01)
            Local0 = NAnd (S604, AUI5)
            M600 (Arg0, 0x02, Local0, 0xFFFFFFFF)
            Local0 = NAnd (S604, AUII)
            M600 (Arg0, 0x03, Local0, 0x3E864C01)
            If (Y078)
            {
                Local0 = NAnd (S604, DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, 0xFFFFFFFF)
                Local0 = NAnd (S604, DerefOf (RefOf (AUII)))
                M600 (Arg0, 0x05, Local0, 0x3E864C01)
            }

            Local0 = NAnd (S604, DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, 0xFFFFFFFF)
            Local0 = NAnd (S604, DerefOf (PAUI [0x12]))
            M600 (Arg0, 0x07, Local0, 0x3E864C01)
            /* Method returns Integer */

            Local0 = NAnd (S604, M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, 0xFFFFFFFF)
            Local0 = NAnd (S604, M601 (0x01, 0x12))
            M600 (Arg0, 0x09, Local0, 0x3E864C01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NAnd (S604, DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, 0xFFFFFFFF)
                Local0 = NAnd (S604, DerefOf (M602 (0x01, 0x12, 0x01)))
                M600 (Arg0, 0x0B, Local0, 0x3E864C01)
            }

            NAnd (S604, 0x00, Local0)
            M600 (Arg0, 0x0C, Local0, 0xFFFFFFFF)
            NAnd (S604, 0xFFFFFFFF, Local0)
            M600 (Arg0, 0x0D, Local0, 0x3E864C01)
            NAnd (S604, AUI5, Local0)
            M600 (Arg0, 0x0E, Local0, 0xFFFFFFFF)
            NAnd (S604, AUII, Local0)
            M600 (Arg0, 0x0F, Local0, 0x3E864C01)
            If (Y078)
            {
                NAnd (S604, DerefOf (RefOf (AUI5)), Local0)
                M600 (Arg0, 0x10, Local0, 0xFFFFFFFF)
                NAnd (S604, DerefOf (RefOf (AUII)), Local0)
                M600 (Arg0, 0x11, Local0, 0x3E864C01)
            }

            NAnd (S604, DerefOf (PAUI [0x05]), Local0)
            M600 (Arg0, 0x12, Local0, 0xFFFFFFFF)
            NAnd (S604, DerefOf (PAUI [0x12]), Local0)
            M600 (Arg0, 0x13, Local0, 0x3E864C01)
            /* Method returns Integer */

            NAnd (S604, M601 (0x01, 0x05), Local0)
            M600 (Arg0, 0x14, Local0, 0xFFFFFFFF)
            NAnd (S604, M601 (0x01, 0x12), Local0)
            M600 (Arg0, 0x15, Local0, 0x3E864C01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NAnd (S604, DerefOf (M602 (0x01, 0x05, 0x01)), Local0)
                M600 (Arg0, 0x16, Local0, 0xFFFFFFFF)
                NAnd (S604, DerefOf (M602 (0x01, 0x12, 0x01)), Local0)
                M600 (Arg0, 0x17, Local0, 0x3E864C01)
            }

            /* Conversion of the second operand */

            Local0 = NAnd (0x00, S604)
            M600 (Arg0, 0x18, Local0, 0xFFFFFFFF)
            Local0 = NAnd (0xFFFFFFFF, S604)
            M600 (Arg0, 0x19, Local0, 0x3E864C01)
            Local0 = NAnd (AUI5, S604)
            M600 (Arg0, 0x1A, Local0, 0xFFFFFFFF)
            Local0 = NAnd (AUII, S604)
            M600 (Arg0, 0x1B, Local0, 0x3E864C01)
            If (Y078)
            {
                Local0 = NAnd (DerefOf (RefOf (AUI5)), S604)
                M600 (Arg0, 0x1C, Local0, 0xFFFFFFFF)
                Local0 = NAnd (DerefOf (RefOf (AUII)), S604)
                M600 (Arg0, 0x1D, Local0, 0x3E864C01)
            }

            Local0 = NAnd (DerefOf (PAUI [0x05]), S604)
            M600 (Arg0, 0x1E, Local0, 0xFFFFFFFF)
            Local0 = NAnd (DerefOf (PAUI [0x12]), S604)
            M600 (Arg0, 0x1F, Local0, 0x3E864C01)
            /* Method returns Integer */

            Local0 = NAnd (M601 (0x01, 0x05), S604)
            M600 (Arg0, 0x20, Local0, 0xFFFFFFFF)
            Local0 = NAnd (M601 (0x01, 0x12), S604)
            M600 (Arg0, 0x21, Local0, 0x3E864C01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NAnd (DerefOf (M602 (0x01, 0x05, 0x01)), S604)
                M600 (Arg0, 0x22, Local0, 0xFFFFFFFF)
                Local0 = NAnd (DerefOf (M602 (0x01, 0x12, 0x01)), S604)
                M600 (Arg0, 0x23, Local0, 0x3E864C01)
            }

            NAnd (0x00, S604, Local0)
            M600 (Arg0, 0x24, Local0, 0xFFFFFFFF)
            NAnd (0xFFFFFFFF, S604, Local0)
            M600 (Arg0, 0x25, Local0, 0x3E864C01)
            NAnd (AUI5, S604, Local0)
            M600 (Arg0, 0x26, Local0, 0xFFFFFFFF)
            NAnd (AUII, S604, Local0)
            M600 (Arg0, 0x27, Local0, 0x3E864C01)
            If (Y078)
            {
                NAnd (DerefOf (RefOf (AUI5)), S604, Local0)
                M600 (Arg0, 0x28, Local0, 0xFFFFFFFF)
                NAnd (DerefOf (RefOf (AUII)), S604, Local0)
                M600 (Arg0, 0x29, Local0, 0x3E864C01)
            }

            NAnd (DerefOf (PAUI [0x05]), S604, Local0)
            M600 (Arg0, 0x2A, Local0, 0xFFFFFFFF)
            NAnd (DerefOf (PAUI [0x12]), S604, Local0)
            M600 (Arg0, 0x2B, Local0, 0x3E864C01)
            /* Method returns Integer */

            NAnd (M601 (0x01, 0x05), S604, Local0)
            M600 (Arg0, 0x2C, Local0, 0xFFFFFFFF)
            NAnd (M601 (0x01, 0x12), S604, Local0)
            M600 (Arg0, 0x2D, Local0, 0x3E864C01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NAnd (DerefOf (M602 (0x01, 0x05, 0x01)), S604, Local0)
                M600 (Arg0, 0x2E, Local0, 0xFFFFFFFF)
                NAnd (DerefOf (M602 (0x01, 0x12, 0x01)), S604, Local0)
                M600 (Arg0, 0x2F, Local0, 0x3E864C01)
            }

            /* Conversion of the both operands */

            Local0 = NAnd (S601, S604)
            M600 (Arg0, 0x30, Local0, 0xFFFFFCDF)
            Local0 = NAnd (S604, S601)
            M600 (Arg0, 0x31, Local0, 0xFFFFFCDF)
            NAnd (S601, S604, Local0)
            M600 (Arg0, 0x32, Local0, 0xFFFFFCDF)
            NAnd (S604, S601, Local0)
            M600 (Arg0, 0x33, Local0, 0xFFFFFCDF)
        }

        /* NOr, common 32-bit/64-bit test */

        Method (M013, 1, Serialized)
        {
            Name (S601, "0321")
            /* Conversion of the first operand */

            Local0 = NOr (S601, 0x00)
            M600 (Arg0, 0x00, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (S601, 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x01, Local0, 0x00)
            Local0 = NOr (S601, AUI5)
            M600 (Arg0, 0x02, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (S601, AUIJ)
            M600 (Arg0, 0x03, Local0, 0x00)
            If (Y078)
            {
                Local0 = NOr (S601, DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, 0xFFFFFFFFFFFFFCDE)
                Local0 = NOr (S601, DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x05, Local0, 0x00)
            }

            Local0 = NOr (S601, DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (S601, DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x07, Local0, 0x00)
            /* Method returns Integer */

            Local0 = NOr (S601, M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (S601, M601 (0x01, 0x13))
            M600 (Arg0, 0x09, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NOr (S601, DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, 0xFFFFFFFFFFFFFCDE)
                Local0 = NOr (S601, DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x0B, Local0, 0x00)
            }

            NOr (S601, 0x00, Local0)
            M600 (Arg0, 0x0C, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (S601, 0xFFFFFFFFFFFFFFFF, Local0)
            M600 (Arg0, 0x0D, Local0, 0x00)
            NOr (S601, AUI5, Local0)
            M600 (Arg0, 0x0E, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (S601, AUIJ, Local0)
            M600 (Arg0, 0x0F, Local0, 0x00)
            If (Y078)
            {
                NOr (S601, DerefOf (RefOf (AUI5)), Local0)
                M600 (Arg0, 0x10, Local0, 0xFFFFFFFFFFFFFCDE)
                NOr (S601, DerefOf (RefOf (AUIJ)), Local0)
                M600 (Arg0, 0x11, Local0, 0x00)
            }

            NOr (S601, DerefOf (PAUI [0x05]), Local0)
            M600 (Arg0, 0x12, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (S601, DerefOf (PAUI [0x13]), Local0)
            M600 (Arg0, 0x13, Local0, 0x00)
            /* Method returns Integer */

            NOr (S601, M601 (0x01, 0x05), Local0)
            M600 (Arg0, 0x14, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (S601, M601 (0x01, 0x13), Local0)
            M600 (Arg0, 0x15, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NOr (S601, DerefOf (M602 (0x01, 0x05, 0x01)), Local0)
                M600 (Arg0, 0x16, Local0, 0xFFFFFFFFFFFFFCDE)
                NOr (S601, DerefOf (M602 (0x01, 0x13, 0x01)), Local0)
                M600 (Arg0, 0x17, Local0, 0x00)
            }

            /* Conversion of the second operand */

            Local0 = NOr (0x00, S601)
            M600 (Arg0, 0x18, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (0xFFFFFFFFFFFFFFFF, S601)
            M600 (Arg0, 0x19, Local0, 0x00)
            Local0 = NOr (AUI5, S601)
            M600 (Arg0, 0x1A, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (AUIJ, S601)
            M600 (Arg0, 0x1B, Local0, 0x00)
            If (Y078)
            {
                Local0 = NOr (DerefOf (RefOf (AUI5)), S601)
                M600 (Arg0, 0x1C, Local0, 0xFFFFFFFFFFFFFCDE)
                Local0 = NOr (DerefOf (RefOf (AUIJ)), S601)
                M600 (Arg0, 0x1D, Local0, 0x00)
            }

            Local0 = NOr (DerefOf (PAUI [0x05]), S601)
            M600 (Arg0, 0x1E, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (DerefOf (PAUI [0x13]), S601)
            M600 (Arg0, 0x1F, Local0, 0x00)
            /* Method returns Integer */

            Local0 = NOr (M601 (0x01, 0x05), S601)
            M600 (Arg0, 0x20, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (M601 (0x01, 0x13), S601)
            M600 (Arg0, 0x21, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NOr (DerefOf (M602 (0x01, 0x05, 0x01)), S601)
                M600 (Arg0, 0x22, Local0, 0xFFFFFFFFFFFFFCDE)
                Local0 = NOr (DerefOf (M602 (0x01, 0x13, 0x01)), S601)
                M600 (Arg0, 0x23, Local0, 0x00)
            }

            NOr (0x00, S601, Local0)
            M600 (Arg0, 0x24, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (0xFFFFFFFFFFFFFFFF, S601, Local0)
            M600 (Arg0, 0x25, Local0, 0x00)
            NOr (AUI5, S601, Local0)
            M600 (Arg0, 0x26, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (AUIJ, S601, Local0)
            M600 (Arg0, 0x27, Local0, 0x00)
            If (Y078)
            {
                NOr (DerefOf (RefOf (AUI5)), S601, Local0)
                M600 (Arg0, 0x28, Local0, 0xFFFFFFFFFFFFFCDE)
                NOr (DerefOf (RefOf (AUIJ)), S601, Local0)
                M600 (Arg0, 0x29, Local0, 0x00)
            }

            NOr (DerefOf (PAUI [0x05]), S601, Local0)
            M600 (Arg0, 0x2A, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (DerefOf (PAUI [0x13]), S601, Local0)
            M600 (Arg0, 0x2B, Local0, 0x00)
            /* Method returns Integer */

            NOr (M601 (0x01, 0x05), S601, Local0)
            M600 (Arg0, 0x2C, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (M601 (0x01, 0x13), S601, Local0)
            M600 (Arg0, 0x2D, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NOr (DerefOf (M602 (0x01, 0x05, 0x01)), S601, Local0)
                M600 (Arg0, 0x2E, Local0, 0xFFFFFFFFFFFFFCDE)
                NOr (DerefOf (M602 (0x01, 0x13, 0x01)), S601, Local0)
                M600 (Arg0, 0x2F, Local0, 0x00)
            }
        }

        /* NOr, 64-bit */

        Method (M014, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S605, "FE7CB391D650A284")
            /* Conversion of the first operand */

            Local0 = NOr (S605, 0x00)
            M600 (Arg0, 0x00, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (S605, 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x01, Local0, 0x00)
            Local0 = NOr (S605, AUI5)
            M600 (Arg0, 0x02, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (S605, AUIJ)
            M600 (Arg0, 0x03, Local0, 0x00)
            If (Y078)
            {
                Local0 = NOr (S605, DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, 0x01834C6E29AF5D7B)
                Local0 = NOr (S605, DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x05, Local0, 0x00)
            }

            Local0 = NOr (S605, DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (S605, DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x07, Local0, 0x00)
            /* Method returns Integer */

            Local0 = NOr (S605, M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (S605, M601 (0x01, 0x13))
            M600 (Arg0, 0x09, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NOr (S605, DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, 0x01834C6E29AF5D7B)
                Local0 = NOr (S605, DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x0B, Local0, 0x00)
            }

            NOr (S605, 0x00, Local0)
            M600 (Arg0, 0x0C, Local0, 0x01834C6E29AF5D7B)
            NOr (S605, 0xFFFFFFFFFFFFFFFF, Local0)
            M600 (Arg0, 0x0D, Local0, 0x00)
            NOr (S605, AUI5, Local0)
            M600 (Arg0, 0x0E, Local0, 0x01834C6E29AF5D7B)
            NOr (S605, AUIJ, Local0)
            M600 (Arg0, 0x0F, Local0, 0x00)
            If (Y078)
            {
                NOr (S605, DerefOf (RefOf (AUI5)), Local0)
                M600 (Arg0, 0x10, Local0, 0x01834C6E29AF5D7B)
                NOr (S605, DerefOf (RefOf (AUIJ)), Local0)
                M600 (Arg0, 0x11, Local0, 0x00)
            }

            NOr (S605, DerefOf (PAUI [0x05]), Local0)
            M600 (Arg0, 0x12, Local0, 0x01834C6E29AF5D7B)
            NOr (S605, DerefOf (PAUI [0x13]), Local0)
            M600 (Arg0, 0x13, Local0, 0x00)
            /* Method returns Integer */

            NOr (S605, M601 (0x01, 0x05), Local0)
            M600 (Arg0, 0x14, Local0, 0x01834C6E29AF5D7B)
            NOr (S605, M601 (0x01, 0x13), Local0)
            M600 (Arg0, 0x15, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NOr (S605, DerefOf (M602 (0x01, 0x05, 0x01)), Local0)
                M600 (Arg0, 0x16, Local0, 0x01834C6E29AF5D7B)
                NOr (S605, DerefOf (M602 (0x01, 0x13, 0x01)), Local0)
                M600 (Arg0, 0x17, Local0, 0x00)
            }

            /* Conversion of the second operand */

            Local0 = NOr (0x00, S605)
            M600 (Arg0, 0x18, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (0xFFFFFFFFFFFFFFFF, S605)
            M600 (Arg0, 0x19, Local0, 0x00)
            Local0 = NOr (AUI5, S605)
            M600 (Arg0, 0x1A, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (AUIJ, S605)
            M600 (Arg0, 0x1B, Local0, 0x00)
            If (Y078)
            {
                Local0 = NOr (DerefOf (RefOf (AUI5)), S605)
                M600 (Arg0, 0x1C, Local0, 0x01834C6E29AF5D7B)
                Local0 = NOr (DerefOf (RefOf (AUIJ)), S605)
                M600 (Arg0, 0x1D, Local0, 0x00)
            }

            Local0 = NOr (DerefOf (PAUI [0x05]), S605)
            M600 (Arg0, 0x1E, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (DerefOf (PAUI [0x13]), S605)
            M600 (Arg0, 0x1F, Local0, 0x00)
            /* Method returns Integer */

            Local0 = NOr (M601 (0x01, 0x05), S605)
            M600 (Arg0, 0x20, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (M601 (0x01, 0x13), S605)
            M600 (Arg0, 0x21, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NOr (DerefOf (M602 (0x01, 0x05, 0x01)), S605)
                M600 (Arg0, 0x22, Local0, 0x01834C6E29AF5D7B)
                Local0 = NOr (DerefOf (M602 (0x01, 0x13, 0x01)), S605)
                M600 (Arg0, 0x23, Local0, 0x00)
            }

            NOr (0x00, S605, Local0)
            M600 (Arg0, 0x24, Local0, 0x01834C6E29AF5D7B)
            NOr (0xFFFFFFFFFFFFFFFF, S605, Local0)
            M600 (Arg0, 0x25, Local0, 0x00)
            NOr (AUI5, S605, Local0)
            M600 (Arg0, 0x26, Local0, 0x01834C6E29AF5D7B)
            NOr (AUIJ, S605, Local0)
            M600 (Arg0, 0x27, Local0, 0x00)
            If (Y078)
            {
                NOr (DerefOf (RefOf (AUI5)), S605, Local0)
                M600 (Arg0, 0x28, Local0, 0x01834C6E29AF5D7B)
                NOr (DerefOf (RefOf (AUIJ)), S605, Local0)
                M600 (Arg0, 0x29, Local0, 0x00)
            }

            NOr (DerefOf (PAUI [0x05]), S605, Local0)
            M600 (Arg0, 0x2A, Local0, 0x01834C6E29AF5D7B)
            NOr (DerefOf (PAUI [0x13]), S605, Local0)
            M600 (Arg0, 0x2B, Local0, 0x00)
            /* Method returns Integer */

            NOr (M601 (0x01, 0x05), S605, Local0)
            M600 (Arg0, 0x2C, Local0, 0x01834C6E29AF5D7B)
            NOr (M601 (0x01, 0x13), S605, Local0)
            M600 (Arg0, 0x2D, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NOr (DerefOf (M602 (0x01, 0x05, 0x01)), S605, Local0)
                M600 (Arg0, 0x2E, Local0, 0x01834C6E29AF5D7B)
                NOr (DerefOf (M602 (0x01, 0x13, 0x01)), S605, Local0)
                M600 (Arg0, 0x2F, Local0, 0x00)
            }

            /* Conversion of the both operands */

            Local0 = NOr (S601, S605)
            M600 (Arg0, 0x30, Local0, 0x01834C6E29AF5C5A)
            Local0 = NOr (S605, S601)
            M600 (Arg0, 0x31, Local0, 0x01834C6E29AF5C5A)
            NOr (S601, S605, Local0)
            M600 (Arg0, 0x32, Local0, 0x01834C6E29AF5C5A)
            NOr (S605, S601, Local0)
            M600 (Arg0, 0x33, Local0, 0x01834C6E29AF5C5A)
        }

        /* NOr, 32-bit */

        Method (M015, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            /* Conversion of the first operand */

            Local0 = NOr (S604, 0x00)
            M600 (Arg0, 0x00, Local0, 0x3E864C01)
            Local0 = NOr (S604, 0xFFFFFFFF)
            M600 (Arg0, 0x01, Local0, 0x00)
            Local0 = NOr (S604, AUI5)
            M600 (Arg0, 0x02, Local0, 0x3E864C01)
            Local0 = NOr (S604, AUII)
            M600 (Arg0, 0x03, Local0, 0x00)
            If (Y078)
            {
                Local0 = NOr (S604, DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, 0x3E864C01)
                Local0 = NOr (S604, DerefOf (RefOf (AUII)))
                M600 (Arg0, 0x05, Local0, 0x00)
            }

            Local0 = NOr (S604, DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, 0x3E864C01)
            Local0 = NOr (S604, DerefOf (PAUI [0x12]))
            M600 (Arg0, 0x07, Local0, 0x00)
            /* Method returns Integer */

            Local0 = NOr (S604, M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, 0x3E864C01)
            Local0 = NOr (S604, M601 (0x01, 0x12))
            M600 (Arg0, 0x09, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NOr (S604, DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, 0x3E864C01)
                Local0 = NOr (S604, DerefOf (M602 (0x01, 0x12, 0x01)))
                M600 (Arg0, 0x0B, Local0, 0x00)
            }

            NOr (S604, 0x00, Local0)
            M600 (Arg0, 0x0C, Local0, 0x3E864C01)
            NOr (S604, 0xFFFFFFFF, Local0)
            M600 (Arg0, 0x0D, Local0, 0x00)
            NOr (S604, AUI5, Local0)
            M600 (Arg0, 0x0E, Local0, 0x3E864C01)
            NOr (S604, AUII, Local0)
            M600 (Arg0, 0x0F, Local0, 0x00)
            If (Y078)
            {
                NOr (S604, DerefOf (RefOf (AUI5)), Local0)
                M600 (Arg0, 0x10, Local0, 0x3E864C01)
                NOr (S604, DerefOf (RefOf (AUII)), Local0)
                M600 (Arg0, 0x11, Local0, 0x00)
            }

            NOr (S604, DerefOf (PAUI [0x05]), Local0)
            M600 (Arg0, 0x12, Local0, 0x3E864C01)
            NOr (S604, DerefOf (PAUI [0x12]), Local0)
            M600 (Arg0, 0x13, Local0, 0x00)
            /* Method returns Integer */

            NOr (S604, M601 (0x01, 0x05), Local0)
            M600 (Arg0, 0x14, Local0, 0x3E864C01)
            NOr (S604, M601 (0x01, 0x12), Local0)
            M600 (Arg0, 0x15, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NOr (S604, DerefOf (M602 (0x01, 0x05, 0x01)), Local0)
                M600 (Arg0, 0x16, Local0, 0x3E864C01)
                NOr (S604, DerefOf (M602 (0x01, 0x12, 0x01)), Local0)
                M600 (Arg0, 0x17, Local0, 0x00)
            }

            /* Conversion of the second operand */

            Local0 = NOr (0x00, S604)
            M600 (Arg0, 0x18, Local0, 0x3E864C01)
            Local0 = NOr (0xFFFFFFFF, S604)
            M600 (Arg0, 0x19, Local0, 0x00)
            Local0 = NOr (AUI5, S604)
            M600 (Arg0, 0x1A, Local0, 0x3E864C01)
            Local0 = NOr (AUII, S604)
            M600 (Arg0, 0x1B, Local0, 0x00)
            If (Y078)
            {
                Local0 = NOr (DerefOf (RefOf (AUI5)), S604)
                M600 (Arg0, 0x1C, Local0, 0x3E864C01)
                Local0 = NOr (DerefOf (RefOf (AUII)), S604)
                M600 (Arg0, 0x1D, Local0, 0x00)
            }

            Local0 = NOr (DerefOf (PAUI [0x05]), S604)
            M600 (Arg0, 0x1E, Local0, 0x3E864C01)
            Local0 = NOr (DerefOf (PAUI [0x12]), S604)
            M600 (Arg0, 0x1F, Local0, 0x00)
            /* Method returns Integer */

            Local0 = NOr (M601 (0x01, 0x05), S604)
            M600 (Arg0, 0x20, Local0, 0x3E864C01)
            Local0 = NOr (M601 (0x01, 0x12), S604)
            M600 (Arg0, 0x21, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NOr (DerefOf (M602 (0x01, 0x05, 0x01)), S604)
                M600 (Arg0, 0x22, Local0, 0x3E864C01)
                Local0 = NOr (DerefOf (M602 (0x01, 0x12, 0x01)), S604)
                M600 (Arg0, 0x23, Local0, 0x00)
            }

            NOr (0x00, S604, Local0)
            M600 (Arg0, 0x24, Local0, 0x3E864C01)
            NOr (0xFFFFFFFF, S604, Local0)
            M600 (Arg0, 0x25, Local0, 0x00)
            NOr (AUI5, S604, Local0)
            M600 (Arg0, 0x26, Local0, 0x3E864C01)
            NOr (AUII, S604, Local0)
            M600 (Arg0, 0x27, Local0, 0x00)
            If (Y078)
            {
                NOr (DerefOf (RefOf (AUI5)), S604, Local0)
                M600 (Arg0, 0x28, Local0, 0x3E864C01)
                NOr (DerefOf (RefOf (AUII)), S604, Local0)
                M600 (Arg0, 0x29, Local0, 0x00)
            }

            NOr (DerefOf (PAUI [0x05]), S604, Local0)
            M600 (Arg0, 0x2A, Local0, 0x3E864C01)
            NOr (DerefOf (PAUI [0x12]), S604, Local0)
            M600 (Arg0, 0x2B, Local0, 0x00)
            /* Method returns Integer */

            NOr (M601 (0x01, 0x05), S604, Local0)
            M600 (Arg0, 0x2C, Local0, 0x3E864C01)
            NOr (M601 (0x01, 0x12), S604, Local0)
            M600 (Arg0, 0x2D, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NOr (DerefOf (M602 (0x01, 0x05, 0x01)), S604, Local0)
                M600 (Arg0, 0x2E, Local0, 0x3E864C01)
                NOr (DerefOf (M602 (0x01, 0x12, 0x01)), S604, Local0)
                M600 (Arg0, 0x2F, Local0, 0x00)
            }

            /* Conversion of the both operands */

            Local0 = NOr (S601, S604)
            M600 (Arg0, 0x30, Local0, 0x3E864C00)
            Local0 = NOr (S604, S601)
            M600 (Arg0, 0x31, Local0, 0x3E864C00)
            NOr (S601, S604, Local0)
            M600 (Arg0, 0x32, Local0, 0x3E864C00)
            NOr (S604, S601, Local0)
            M600 (Arg0, 0x33, Local0, 0x3E864C00)
        }

        /* Or, common 32-bit/64-bit test */

        Method (M016, 1, Serialized)
        {
            Name (S601, "0321")
            /* Conversion of the first operand */

            Store ((S601 | 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((S601 | 0xFFFFFFFFFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0xFFFFFFFFFFFFFFFF)
            Store ((S601 | AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((S601 | AUIJ), Local0)
            M600 (Arg0, 0x03, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Store ((S601 | DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((S601 | DerefOf (RefOf (AUIJ))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Store ((S601 | DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((S601 | DerefOf (PAUI [0x13])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Store ((S601 | M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((S601 | M601 (0x01, 0x13)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S601 | DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((S601 | DerefOf (M602 (0x01, 0x13, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (S601 | 0x00)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (S601 | 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = (S601 | AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (S601 | AUIJ) /* \AUIJ */
            M600 (Arg0, 0x0F, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Local0 = (S601 | DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (S601 | DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x11, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (S601 | DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (S601 | DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x13, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Local0 = (S601 | M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (S601 | M601 (0x01, 0x13))
            M600 (Arg0, 0x15, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S601 | DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (S601 | DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            /* Conversion of the second operand */

            Store ((0x00 | S601), Local0)
            M600 (Arg0, 0x18, Local0, 0x0321)
            Store ((0xFFFFFFFFFFFFFFFF | S601), Local0)
            M600 (Arg0, 0x19, Local0, 0xFFFFFFFFFFFFFFFF)
            Store ((AUI5 | S601), Local0)
            M600 (Arg0, 0x1A, Local0, 0x0321)
            Store ((AUIJ | S601), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) | S601), Local0)
                M600 (Arg0, 0x1C, Local0, 0x0321)
                Store ((DerefOf (RefOf (AUIJ)) | S601), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Store ((DerefOf (PAUI [0x05]) | S601), Local0)
            M600 (Arg0, 0x1E, Local0, 0x0321)
            Store ((DerefOf (PAUI [0x13]) | S601), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) | S601), Local0)
            M600 (Arg0, 0x20, Local0, 0x0321)
            Store ((M601 (0x01, 0x13) | S601), Local0)
            M600 (Arg0, 0x21, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) | S601), Local0)
                M600 (Arg0, 0x22, Local0, 0x0321)
                Store ((DerefOf (M602 (0x01, 0x13, 0x01)) | S601), Local0)
                M600 (Arg0, 0x23, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (0x00 | S601) /* \M613.M016.S601 */
            M600 (Arg0, 0x24, Local0, 0x0321)
            Local0 = (0xFFFFFFFFFFFFFFFF | S601) /* \M613.M016.S601 */
            M600 (Arg0, 0x25, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = (AUI5 | S601) /* \M613.M016.S601 */
            M600 (Arg0, 0x26, Local0, 0x0321)
            Local0 = (AUIJ | S601) /* \M613.M016.S601 */
            M600 (Arg0, 0x27, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) | S601) /* \M613.M016.S601 */
                M600 (Arg0, 0x28, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (AUIJ)) | S601) /* \M613.M016.S601 */
                M600 (Arg0, 0x29, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (DerefOf (PAUI [0x05]) | S601) /* \M613.M016.S601 */
            M600 (Arg0, 0x2A, Local0, 0x0321)
            Local0 = (DerefOf (PAUI [0x13]) | S601) /* \M613.M016.S601 */
            M600 (Arg0, 0x2B, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) | S601) /* \M613.M016.S601 */
            M600 (Arg0, 0x2C, Local0, 0x0321)
            Local0 = (M601 (0x01, 0x13) | S601) /* \M613.M016.S601 */
            M600 (Arg0, 0x2D, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) | S601) /* \M613.M016.S601 */
                M600 (Arg0, 0x2E, Local0, 0x0321)
                Local0 = (DerefOf (M602 (0x01, 0x13, 0x01)) | S601) /* \M613.M016.S601 */
                M600 (Arg0, 0x2F, Local0, 0xFFFFFFFFFFFFFFFF)
            }
        }

        /* Or, 64-bit */

        Method (M017, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S605, "FE7CB391D650A284")
            /* Conversion of the first operand */

            Store ((S605 | 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((S605 | 0xFFFFFFFFFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0xFFFFFFFFFFFFFFFF)
            Store ((S605 | AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((S605 | AUIJ), Local0)
            M600 (Arg0, 0x03, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Store ((S605 | DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((S605 | DerefOf (RefOf (AUIJ))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Store ((S605 | DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((S605 | DerefOf (PAUI [0x13])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Store ((S605 | M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((S605 | M601 (0x01, 0x13)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S605 | DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((S605 | DerefOf (M602 (0x01, 0x13, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (S605 | 0x00)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 | 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = (S605 | AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 | AUIJ) /* \AUIJ */
            M600 (Arg0, 0x0F, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Local0 = (S605 | DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (S605 | DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x11, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (S605 | DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 | DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x13, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Local0 = (S605 | M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 | M601 (0x01, 0x13))
            M600 (Arg0, 0x15, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S605 | DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (S605 | DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            /* Conversion of the second operand */

            Store ((0x00 | S605), Local0)
            M600 (Arg0, 0x18, Local0, 0xFE7CB391D650A284)
            Store ((0xFFFFFFFFFFFFFFFF | S605), Local0)
            M600 (Arg0, 0x19, Local0, 0xFFFFFFFFFFFFFFFF)
            Store ((AUI5 | S605), Local0)
            M600 (Arg0, 0x1A, Local0, 0xFE7CB391D650A284)
            Store ((AUIJ | S605), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) | S605), Local0)
                M600 (Arg0, 0x1C, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (AUIJ)) | S605), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Store ((DerefOf (PAUI [0x05]) | S605), Local0)
            M600 (Arg0, 0x1E, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (PAUI [0x13]) | S605), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) | S605), Local0)
            M600 (Arg0, 0x20, Local0, 0xFE7CB391D650A284)
            Store ((M601 (0x01, 0x13) | S605), Local0)
            M600 (Arg0, 0x21, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) | S605), Local0)
                M600 (Arg0, 0x22, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (M602 (0x01, 0x13, 0x01)) | S605), Local0)
                M600 (Arg0, 0x23, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (0x00 | S605) /* \M613.M017.S605 */
            M600 (Arg0, 0x24, Local0, 0xFE7CB391D650A284)
            Local0 = (0xFFFFFFFFFFFFFFFF | S605) /* \M613.M017.S605 */
            M600 (Arg0, 0x25, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = (AUI5 | S605) /* \M613.M017.S605 */
            M600 (Arg0, 0x26, Local0, 0xFE7CB391D650A284)
            Local0 = (AUIJ | S605) /* \M613.M017.S605 */
            M600 (Arg0, 0x27, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) | S605) /* \M613.M017.S605 */
                M600 (Arg0, 0x28, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (AUIJ)) | S605) /* \M613.M017.S605 */
                M600 (Arg0, 0x29, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (DerefOf (PAUI [0x05]) | S605) /* \M613.M017.S605 */
            M600 (Arg0, 0x2A, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (PAUI [0x13]) | S605) /* \M613.M017.S605 */
            M600 (Arg0, 0x2B, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) | S605) /* \M613.M017.S605 */
            M600 (Arg0, 0x2C, Local0, 0xFE7CB391D650A284)
            Local0 = (M601 (0x01, 0x13) | S605) /* \M613.M017.S605 */
            M600 (Arg0, 0x2D, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) | S605) /* \M613.M017.S605 */
                M600 (Arg0, 0x2E, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (M602 (0x01, 0x13, 0x01)) | S605) /* \M613.M017.S605 */
                M600 (Arg0, 0x2F, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            /* Conversion of the both operands */

            Store ((S601 | S605), Local0)
            M600 (Arg0, 0x30, Local0, 0xFE7CB391D650A3A5)
            Store ((S605 | S601), Local0)
            M600 (Arg0, 0x31, Local0, 0xFE7CB391D650A3A5)
            Local0 = (S601 | S605) /* \M613.M017.S605 */
            M600 (Arg0, 0x32, Local0, 0xFE7CB391D650A3A5)
            Local0 = (S605 | S601) /* \M613.M017.S601 */
            M600 (Arg0, 0x33, Local0, 0xFE7CB391D650A3A5)
        }

        /* Or, 32-bit */

        Method (M018, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            /* Conversion of the first operand */

            Store ((S604 | 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xC179B3FE)
            Store ((S604 | 0xFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0xFFFFFFFF)
            Store ((S604 | AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xC179B3FE)
            Store ((S604 | AUII), Local0)
            M600 (Arg0, 0x03, Local0, 0xFFFFFFFF)
            If (Y078)
            {
                Store ((S604 | DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xC179B3FE)
                Store ((S604 | DerefOf (RefOf (AUII))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFFFFFFFF)
            }

            Store ((S604 | DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xC179B3FE)
            Store ((S604 | DerefOf (PAUI [0x12])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFFFFFFFF)
            /* Method returns Integer */

            Store ((S604 | M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xC179B3FE)
            Store ((S604 | M601 (0x01, 0x12)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S604 | DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xC179B3FE)
                Store ((S604 | DerefOf (M602 (0x01, 0x12, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFFFFFFFF)
            }

            Local0 = (S604 | 0x00)
            M600 (Arg0, 0x0C, Local0, 0xC179B3FE)
            Local0 = (S604 | 0xFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0xFFFFFFFF)
            Local0 = (S604 | AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xC179B3FE)
            Local0 = (S604 | AUII) /* \AUII */
            M600 (Arg0, 0x0F, Local0, 0xFFFFFFFF)
            If (Y078)
            {
                Local0 = (S604 | DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xC179B3FE)
                Local0 = (S604 | DerefOf (RefOf (AUII)))
                M600 (Arg0, 0x11, Local0, 0xFFFFFFFF)
            }

            Local0 = (S604 | DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xC179B3FE)
            Local0 = (S604 | DerefOf (PAUI [0x12]))
            M600 (Arg0, 0x13, Local0, 0xFFFFFFFF)
            /* Method returns Integer */

            Local0 = (S604 | M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xC179B3FE)
            Local0 = (S604 | M601 (0x01, 0x12))
            M600 (Arg0, 0x15, Local0, 0xFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S604 | DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xC179B3FE)
                Local0 = (S604 | DerefOf (M602 (0x01, 0x12, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFFFFFFFF)
            }

            /* Conversion of the second operand */

            Store ((0x00 | S604), Local0)
            M600 (Arg0, 0x18, Local0, 0xC179B3FE)
            Store ((0xFFFFFFFF | S604), Local0)
            M600 (Arg0, 0x19, Local0, 0xFFFFFFFF)
            Store ((AUI5 | S604), Local0)
            M600 (Arg0, 0x1A, Local0, 0xC179B3FE)
            Store ((AUII | S604), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFFFFFFFF)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) | S604), Local0)
                M600 (Arg0, 0x1C, Local0, 0xC179B3FE)
                Store ((DerefOf (RefOf (AUII)) | S604), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFFFFFFFF)
            }

            Store ((DerefOf (PAUI [0x05]) | S604), Local0)
            M600 (Arg0, 0x1E, Local0, 0xC179B3FE)
            Store ((DerefOf (PAUI [0x12]) | S604), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFFFFFFFF)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) | S604), Local0)
            M600 (Arg0, 0x20, Local0, 0xC179B3FE)
            Store ((M601 (0x01, 0x12) | S604), Local0)
            M600 (Arg0, 0x21, Local0, 0xFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) | S604), Local0)
                M600 (Arg0, 0x22, Local0, 0xC179B3FE)
                Store ((DerefOf (M602 (0x01, 0x12, 0x01)) | S604), Local0)
                M600 (Arg0, 0x23, Local0, 0xFFFFFFFF)
            }

            Local0 = (0x00 | S604) /* \M613.M018.S604 */
            M600 (Arg0, 0x24, Local0, 0xC179B3FE)
            Local0 = (0xFFFFFFFF | S604) /* \M613.M018.S604 */
            M600 (Arg0, 0x25, Local0, 0xFFFFFFFF)
            Local0 = (AUI5 | S604) /* \M613.M018.S604 */
            M600 (Arg0, 0x26, Local0, 0xC179B3FE)
            Local0 = (AUII | S604) /* \M613.M018.S604 */
            M600 (Arg0, 0x27, Local0, 0xFFFFFFFF)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) | S604) /* \M613.M018.S604 */
                M600 (Arg0, 0x28, Local0, 0xC179B3FE)
                Local0 = (DerefOf (RefOf (AUII)) | S604) /* \M613.M018.S604 */
                M600 (Arg0, 0x29, Local0, 0xFFFFFFFF)
            }

            Local0 = (DerefOf (PAUI [0x05]) | S604) /* \M613.M018.S604 */
            M600 (Arg0, 0x2A, Local0, 0xC179B3FE)
            Local0 = (DerefOf (PAUI [0x12]) | S604) /* \M613.M018.S604 */
            M600 (Arg0, 0x2B, Local0, 0xFFFFFFFF)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) | S604) /* \M613.M018.S604 */
            M600 (Arg0, 0x2C, Local0, 0xC179B3FE)
            Local0 = (M601 (0x01, 0x12) | S604) /* \M613.M018.S604 */
            M600 (Arg0, 0x2D, Local0, 0xFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) | S604) /* \M613.M018.S604 */
                M600 (Arg0, 0x2E, Local0, 0xC179B3FE)
                Local0 = (DerefOf (M602 (0x01, 0x12, 0x01)) | S604) /* \M613.M018.S604 */
                M600 (Arg0, 0x2F, Local0, 0xFFFFFFFF)
            }

            /* Conversion of the both operands */

            Store ((S601 | S604), Local0)
            M600 (Arg0, 0x30, Local0, 0xC179B3FF)
            Store ((S604 | S601), Local0)
            M600 (Arg0, 0x31, Local0, 0xC179B3FF)
            Local0 = (S601 | S604) /* \M613.M018.S604 */
            M600 (Arg0, 0x32, Local0, 0xC179B3FF)
            Local0 = (S604 | S601) /* \M613.M018.S601 */
            M600 (Arg0, 0x33, Local0, 0xC179B3FF)
        }

        /* ShiftLeft, common 32-bit/64-bit test */

        Method (M019, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S614, "B")
            /* Conversion of the first operand */

            Store ((S601 << 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((S601 << 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x0642)
            Store ((S601 << AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((S601 << AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x0642)
            If (Y078)
            {
                Store ((S601 << DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((S601 << DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x0642)
            }

            Store ((S601 << DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((S601 << DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x0642)
            /* Method returns Integer */

            Store ((S601 << M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((S601 << M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x0642)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S601 << DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((S601 << DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x0642)
            }

            Local0 = (S601 << 0x00)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (S601 << 0x01)
            M600 (Arg0, 0x0D, Local0, 0x0642)
            Local0 = (S601 << AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (S601 << AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x0642)
            If (Y078)
            {
                Local0 = (S601 << DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (S601 << DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x0642)
            }

            Local0 = (S601 << DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (S601 << DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x0642)
            /* Method returns Integer */

            Local0 = (S601 << M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (S601 << M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x0642)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S601 << DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (S601 << DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x0642)
            }

            /* Conversion of the second operand */

            Store ((0x00 << S614), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x01 << S614), Local0)
            M600 (Arg0, 0x19, Local0, 0x0800)
            Store ((AUI5 << S614), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI6 << S614), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0800)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) << S614), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI6)) << S614), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0800)
            }

            Store ((DerefOf (PAUI [0x05]) << S614), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x06]) << S614), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0800)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) << S614), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x06) << S614), Local0)
            M600 (Arg0, 0x21, Local0, 0x0800)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) << S614), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) << S614), Local0)
                M600 (Arg0, 0x23, Local0, 0x0800)
            }

            Local0 = (0x00 << S614) /* \M613.M019.S614 */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0x01 << S614) /* \M613.M019.S614 */
            M600 (Arg0, 0x25, Local0, 0x0800)
            Local0 = (AUI5 << S614) /* \M613.M019.S614 */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI6 << S614) /* \M613.M019.S614 */
            M600 (Arg0, 0x27, Local0, 0x0800)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) << S614) /* \M613.M019.S614 */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI6)) << S614) /* \M613.M019.S614 */
                M600 (Arg0, 0x29, Local0, 0x0800)
            }

            Local0 = (DerefOf (PAUI [0x05]) << S614) /* \M613.M019.S614 */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x06]) << S614) /* \M613.M019.S614 */
            M600 (Arg0, 0x2B, Local0, 0x0800)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) << S614) /* \M613.M019.S614 */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x06) << S614) /* \M613.M019.S614 */
            M600 (Arg0, 0x2D, Local0, 0x0800)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) << S614) /* \M613.M019.S614 */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) << S614) /* \M613.M019.S614 */
                M600 (Arg0, 0x2F, Local0, 0x0800)
            }
        }

        /* ShiftLeft, 64-bit */

        Method (M01A, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S605, "FE7CB391D650A284")
            Name (S614, "B")
            /* Conversion of the first operand */

            Store ((S605 << 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((S605 << 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xFCF96723ACA14508)
            Store ((S605 << AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((S605 << AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xFCF96723ACA14508)
            If (Y078)
            {
                Store ((S605 << DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((S605 << DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFCF96723ACA14508)
            }

            Store ((S605 << DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((S605 << DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFCF96723ACA14508)
            /* Method returns Integer */

            Store ((S605 << M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((S605 << M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFCF96723ACA14508)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S605 << DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((S605 << DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFCF96723ACA14508)
            }

            Local0 = (S605 << 0x00)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 << 0x01)
            M600 (Arg0, 0x0D, Local0, 0xFCF96723ACA14508)
            Local0 = (S605 << AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 << AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xFCF96723ACA14508)
            If (Y078)
            {
                Local0 = (S605 << DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (S605 << DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xFCF96723ACA14508)
            }

            Local0 = (S605 << DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 << DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xFCF96723ACA14508)
            /* Method returns Integer */

            Local0 = (S605 << M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 << M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xFCF96723ACA14508)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S605 << DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (S605 << DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFCF96723ACA14508)
            }

            /* Conversion of the second operand */

            Store ((0x00 << S614), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x01 << S614), Local0)
            M600 (Arg0, 0x19, Local0, 0x0800)
            Store ((AUI5 << S614), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI6 << S614), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0800)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) << S614), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI6)) << S614), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0800)
            }

            Store ((DerefOf (PAUI [0x05]) << S614), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x06]) << S614), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0800)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) << S614), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x06) << S614), Local0)
            M600 (Arg0, 0x21, Local0, 0x0800)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) << S614), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) << S614), Local0)
                M600 (Arg0, 0x23, Local0, 0x0800)
            }

            Local0 = (0x00 << S614) /* \M613.M01A.S614 */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0x01 << S614) /* \M613.M01A.S614 */
            M600 (Arg0, 0x25, Local0, 0x0800)
            Local0 = (AUI5 << S614) /* \M613.M01A.S614 */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI6 << S614) /* \M613.M01A.S614 */
            M600 (Arg0, 0x27, Local0, 0x0800)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) << S614) /* \M613.M01A.S614 */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI6)) << S614) /* \M613.M01A.S614 */
                M600 (Arg0, 0x29, Local0, 0x0800)
            }

            Local0 = (DerefOf (PAUI [0x05]) << S614) /* \M613.M01A.S614 */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x06]) << S614) /* \M613.M01A.S614 */
            M600 (Arg0, 0x2B, Local0, 0x0800)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) << S614) /* \M613.M01A.S614 */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x06) << S614) /* \M613.M01A.S614 */
            M600 (Arg0, 0x2D, Local0, 0x0800)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) << S614) /* \M613.M01A.S614 */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) << S614) /* \M613.M01A.S614 */
                M600 (Arg0, 0x2F, Local0, 0x0800)
            }

            /* Conversion of the both operands */

            Store ((S601 << S614), Local0)
            M600 (Arg0, 0x30, Local0, 0x00190800)
            Store ((S605 << S614), Local0)
            M600 (Arg0, 0x31, Local0, 0xE59C8EB285142000)
            Local0 = (S601 << S614) /* \M613.M01A.S614 */
            M600 (Arg0, 0x32, Local0, 0x00190800)
            Local0 = (S605 << S614) /* \M613.M01A.S614 */
            M600 (Arg0, 0x33, Local0, 0xE59C8EB285142000)
        }

        /* ShiftLeft, 32-bit */

        Method (M01B, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            Name (S614, "B")
            /* Conversion of the first operand */

            Store ((S604 << 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xC179B3FE)
            Store ((S604 << 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x82F367FC)
            Store ((S604 << AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xC179B3FE)
            Store ((S604 << AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x82F367FC)
            If (Y078)
            {
                Store ((S604 << DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xC179B3FE)
                Store ((S604 << DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x82F367FC)
            }

            Store ((S604 << DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xC179B3FE)
            Store ((S604 << DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x82F367FC)
            /* Method returns Integer */

            Store ((S604 << M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xC179B3FE)
            Store ((S604 << M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x82F367FC)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S604 << DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xC179B3FE)
                Store ((S604 << DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x82F367FC)
            }

            Local0 = (S604 << 0x00)
            M600 (Arg0, 0x0C, Local0, 0xC179B3FE)
            Local0 = (S604 << 0x01)
            M600 (Arg0, 0x0D, Local0, 0x82F367FC)
            Local0 = (S604 << AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xC179B3FE)
            Local0 = (S604 << AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x82F367FC)
            If (Y078)
            {
                Local0 = (S604 << DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xC179B3FE)
                Local0 = (S604 << DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x82F367FC)
            }

            Local0 = (S604 << DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xC179B3FE)
            Local0 = (S604 << DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x82F367FC)
            /* Method returns Integer */

            Local0 = (S604 << M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xC179B3FE)
            Local0 = (S604 << M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x82F367FC)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S604 << DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xC179B3FE)
                Local0 = (S604 << DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x82F367FC)
            }

            /* Conversion of the second operand */

            Store ((0x00 << S614), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x01 << S614), Local0)
            M600 (Arg0, 0x19, Local0, 0x0800)
            Store ((AUI5 << S614), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI6 << S614), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0800)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) << S614), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI6)) << S614), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0800)
            }

            Store ((DerefOf (PAUI [0x05]) << S614), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x06]) << S614), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0800)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) << S614), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x06) << S614), Local0)
            M600 (Arg0, 0x21, Local0, 0x0800)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) << S614), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) << S614), Local0)
                M600 (Arg0, 0x23, Local0, 0x0800)
            }

            Local0 = (0x00 << S614) /* \M613.M01B.S614 */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0x01 << S614) /* \M613.M01B.S614 */
            M600 (Arg0, 0x25, Local0, 0x0800)
            Local0 = (AUI5 << S614) /* \M613.M01B.S614 */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI6 << S614) /* \M613.M01B.S614 */
            M600 (Arg0, 0x27, Local0, 0x0800)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) << S614) /* \M613.M01B.S614 */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI6)) << S614) /* \M613.M01B.S614 */
                M600 (Arg0, 0x29, Local0, 0x0800)
            }

            Local0 = (DerefOf (PAUI [0x05]) << S614) /* \M613.M01B.S614 */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x06]) << S614) /* \M613.M01B.S614 */
            M600 (Arg0, 0x2B, Local0, 0x0800)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) << S614) /* \M613.M01B.S614 */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x06) << S614) /* \M613.M01B.S614 */
            M600 (Arg0, 0x2D, Local0, 0x0800)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) << S614) /* \M613.M01B.S614 */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) << S614) /* \M613.M01B.S614 */
                M600 (Arg0, 0x2F, Local0, 0x0800)
            }

            /* Conversion of the both operands */

            Store ((S601 << S614), Local0)
            M600 (Arg0, 0x30, Local0, 0x00190800)
            Store ((S604 << S614), Local0)
            M600 (Arg0, 0x31, Local0, 0xCD9FF000)
            Local0 = (S601 << S614) /* \M613.M01B.S614 */
            M600 (Arg0, 0x32, Local0, 0x00190800)
            Local0 = (S604 << S614) /* \M613.M01B.S614 */
            M600 (Arg0, 0x33, Local0, 0xCD9FF000)
        }

        /* ShiftRight, common 32-bit/64-bit test */

        Method (M01C, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S614, "B")
            /* Conversion of the first operand */

            Store ((S601 >> 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((S601 >> 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x0190)
            Store ((S601 >> AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((S601 >> AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x0190)
            If (Y078)
            {
                Store ((S601 >> DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((S601 >> DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x0190)
            }

            Store ((S601 >> DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((S601 >> DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x0190)
            /* Method returns Integer */

            Store ((S601 >> M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((S601 >> M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x0190)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S601 >> DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((S601 >> DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x0190)
            }

            Local0 = (S601 >> 0x00)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (S601 >> 0x01)
            M600 (Arg0, 0x0D, Local0, 0x0190)
            Local0 = (S601 >> AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (S601 >> AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x0190)
            If (Y078)
            {
                Local0 = (S601 >> DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (S601 >> DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x0190)
            }

            Local0 = (S601 >> DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (S601 >> DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x0190)
            /* Method returns Integer */

            Local0 = (S601 >> M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (S601 >> M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x0190)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S601 >> DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (S601 >> DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x0190)
            }

            /* Conversion of the second operand */

            Store ((0x0321 >> S614), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xC179B3FE >> S614), Local0)
            M600 (Arg0, 0x19, Local0, 0x00182F36)
            Store ((AUI1 >> S614), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI3 >> S614), Local0)
            M600 (Arg0, 0x1B, Local0, 0x00182F36)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI1)) >> S614), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI3)) >> S614), Local0)
                M600 (Arg0, 0x1D, Local0, 0x00182F36)
            }

            Store ((DerefOf (PAUI [0x01]) >> S614), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x03]) >> S614), Local0)
            M600 (Arg0, 0x1F, Local0, 0x00182F36)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x01) >> S614), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x03) >> S614), Local0)
            M600 (Arg0, 0x21, Local0, 0x00182F36)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x01, 0x01)) >> S614), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x03, 0x01)) >> S614), Local0)
                M600 (Arg0, 0x23, Local0, 0x00182F36)
            }

            Local0 = (0x0321 >> S614) /* \M613.M01C.S614 */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0xC179B3FE >> S614) /* \M613.M01C.S614 */
            M600 (Arg0, 0x25, Local0, 0x00182F36)
            Local0 = (AUI1 >> S614) /* \M613.M01C.S614 */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI3 >> S614) /* \M613.M01C.S614 */
            M600 (Arg0, 0x27, Local0, 0x00182F36)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) >> S614) /* \M613.M01C.S614 */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI3)) >> S614) /* \M613.M01C.S614 */
                M600 (Arg0, 0x29, Local0, 0x00182F36)
            }

            Local0 = (DerefOf (PAUI [0x01]) >> S614) /* \M613.M01C.S614 */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x03]) >> S614) /* \M613.M01C.S614 */
            M600 (Arg0, 0x2B, Local0, 0x00182F36)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) >> S614) /* \M613.M01C.S614 */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x03) >> S614) /* \M613.M01C.S614 */
            M600 (Arg0, 0x2D, Local0, 0x00182F36)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) >> S614) /* \M613.M01C.S614 */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x03, 0x01)) >> S614) /* \M613.M01C.S614 */
                M600 (Arg0, 0x2F, Local0, 0x00182F36)
            }
        }

        /* ShiftRight, 64-bit */

        Method (M01D, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S605, "FE7CB391D650A284")
            Name (S614, "B")
            /* Conversion of the first operand */

            Store ((S605 >> 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((S605 >> 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x7F3E59C8EB285142)
            Store ((S605 >> AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((S605 >> AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x7F3E59C8EB285142)
            If (Y078)
            {
                Store ((S605 >> DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((S605 >> DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x7F3E59C8EB285142)
            }

            Store ((S605 >> DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((S605 >> DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x7F3E59C8EB285142)
            /* Method returns Integer */

            Store ((S605 >> M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((S605 >> M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x7F3E59C8EB285142)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S605 >> DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((S605 >> DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x7F3E59C8EB285142)
            }

            Local0 = (S605 >> 0x00)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 >> 0x01)
            M600 (Arg0, 0x0D, Local0, 0x7F3E59C8EB285142)
            Local0 = (S605 >> AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 >> AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x7F3E59C8EB285142)
            If (Y078)
            {
                Local0 = (S605 >> DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (S605 >> DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x7F3E59C8EB285142)
            }

            Local0 = (S605 >> DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 >> DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x7F3E59C8EB285142)
            /* Method returns Integer */

            Local0 = (S605 >> M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 >> M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x7F3E59C8EB285142)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S605 >> DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (S605 >> DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x7F3E59C8EB285142)
            }

            /* Conversion of the second operand */

            Store ((0x0321 >> S614), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xFE7CB391D650A284 >> S614), Local0)
            M600 (Arg0, 0x19, Local0, 0x001FCF96723ACA14)
            Store ((AUI1 >> S614), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI4 >> S614), Local0)
            M600 (Arg0, 0x1B, Local0, 0x001FCF96723ACA14)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI1)) >> S614), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI4)) >> S614), Local0)
                M600 (Arg0, 0x1D, Local0, 0x001FCF96723ACA14)
            }

            Store ((DerefOf (PAUI [0x01]) >> S614), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x04]) >> S614), Local0)
            M600 (Arg0, 0x1F, Local0, 0x001FCF96723ACA14)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x01) >> S614), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x04) >> S614), Local0)
            M600 (Arg0, 0x21, Local0, 0x001FCF96723ACA14)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x01, 0x01)) >> S614), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x04, 0x01)) >> S614), Local0)
                M600 (Arg0, 0x23, Local0, 0x001FCF96723ACA14)
            }

            Local0 = (0x0321 >> S614) /* \M613.M01D.S614 */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0xFE7CB391D650A284 >> S614) /* \M613.M01D.S614 */
            M600 (Arg0, 0x25, Local0, 0x001FCF96723ACA14)
            Local0 = (AUI1 >> S614) /* \M613.M01D.S614 */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI4 >> S614) /* \M613.M01D.S614 */
            M600 (Arg0, 0x27, Local0, 0x001FCF96723ACA14)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) >> S614) /* \M613.M01D.S614 */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI4)) >> S614) /* \M613.M01D.S614 */
                M600 (Arg0, 0x29, Local0, 0x001FCF96723ACA14)
            }

            Local0 = (DerefOf (PAUI [0x01]) >> S614) /* \M613.M01D.S614 */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x04]) >> S614) /* \M613.M01D.S614 */
            M600 (Arg0, 0x2B, Local0, 0x001FCF96723ACA14)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) >> S614) /* \M613.M01D.S614 */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x04) >> S614) /* \M613.M01D.S614 */
            M600 (Arg0, 0x2D, Local0, 0x001FCF96723ACA14)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) >> S614) /* \M613.M01D.S614 */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) >> S614) /* \M613.M01D.S614 */
                M600 (Arg0, 0x2F, Local0, 0x001FCF96723ACA14)
            }

            /* Conversion of the both operands */

            Store ((S601 >> S614), Local0)
            M600 (Arg0, 0x30, Local0, 0x00)
            Store ((S605 >> S614), Local0)
            M600 (Arg0, 0x31, Local0, 0x001FCF96723ACA14)
            Local0 = (S601 >> S614) /* \M613.M01D.S614 */
            M600 (Arg0, 0x32, Local0, 0x00)
            Local0 = (S605 >> S614) /* \M613.M01D.S614 */
            M600 (Arg0, 0x33, Local0, 0x001FCF96723ACA14)
        }

        /* ShiftRight, 32-bit */

        Method (M01E, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            Name (S614, "B")
            /* Conversion of the first operand */

            Store ((S604 >> 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xC179B3FE)
            Store ((S604 >> 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x60BCD9FF)
            Store ((S604 >> AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xC179B3FE)
            Store ((S604 >> AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x60BCD9FF)
            If (Y078)
            {
                Store ((S604 >> DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xC179B3FE)
                Store ((S604 >> DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x60BCD9FF)
            }

            Store ((S604 >> DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xC179B3FE)
            Store ((S604 >> DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x60BCD9FF)
            /* Method returns Integer */

            Store ((S604 >> M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xC179B3FE)
            Store ((S604 >> M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x60BCD9FF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S604 >> DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xC179B3FE)
                Store ((S604 >> DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x60BCD9FF)
            }

            Local0 = (S604 >> 0x00)
            M600 (Arg0, 0x0C, Local0, 0xC179B3FE)
            Local0 = (S604 >> 0x01)
            M600 (Arg0, 0x0D, Local0, 0x60BCD9FF)
            Local0 = (S604 >> AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xC179B3FE)
            Local0 = (S604 >> AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x60BCD9FF)
            If (Y078)
            {
                Local0 = (S604 >> DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xC179B3FE)
                Local0 = (S604 >> DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x60BCD9FF)
            }

            Local0 = (S604 >> DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xC179B3FE)
            Local0 = (S604 >> DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x60BCD9FF)
            /* Method returns Integer */

            Local0 = (S604 >> M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xC179B3FE)
            Local0 = (S604 >> M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x60BCD9FF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S604 >> DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xC179B3FE)
                Local0 = (S604 >> DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x60BCD9FF)
            }

            /* Conversion of the second operand */

            Store ((0x0321 >> S614), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xC179B3FE >> S614), Local0)
            M600 (Arg0, 0x19, Local0, 0x00182F36)
            Store ((AUI1 >> S614), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI3 >> S614), Local0)
            M600 (Arg0, 0x1B, Local0, 0x00182F36)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI1)) >> S614), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI3)) >> S614), Local0)
                M600 (Arg0, 0x1D, Local0, 0x00182F36)
            }

            Store ((DerefOf (PAUI [0x01]) >> S614), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x03]) >> S614), Local0)
            M600 (Arg0, 0x1F, Local0, 0x00182F36)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x01) >> S614), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x03) >> S614), Local0)
            M600 (Arg0, 0x21, Local0, 0x00182F36)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x01, 0x01)) >> S614), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x03, 0x01)) >> S614), Local0)
                M600 (Arg0, 0x23, Local0, 0x00182F36)
            }

            Local0 = (0x0321 >> S614) /* \M613.M01E.S614 */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0xC179B3FE >> S614) /* \M613.M01E.S614 */
            M600 (Arg0, 0x25, Local0, 0x00182F36)
            Local0 = (AUI1 >> S614) /* \M613.M01E.S614 */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI3 >> S614) /* \M613.M01E.S614 */
            M600 (Arg0, 0x27, Local0, 0x00182F36)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) >> S614) /* \M613.M01E.S614 */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI3)) >> S614) /* \M613.M01E.S614 */
                M600 (Arg0, 0x29, Local0, 0x00182F36)
            }

            Local0 = (DerefOf (PAUI [0x01]) >> S614) /* \M613.M01E.S614 */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x03]) >> S614) /* \M613.M01E.S614 */
            M600 (Arg0, 0x2B, Local0, 0x00182F36)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) >> S614) /* \M613.M01E.S614 */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x03) >> S614) /* \M613.M01E.S614 */
            M600 (Arg0, 0x2D, Local0, 0x00182F36)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) >> S614) /* \M613.M01E.S614 */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x03, 0x01)) >> S614) /* \M613.M01E.S614 */
                M600 (Arg0, 0x2F, Local0, 0x00182F36)
            }

            /* Conversion of the both operands */

            Store ((S601 >> S614), Local0)
            M600 (Arg0, 0x30, Local0, 0x00)
            Store ((S604 >> S614), Local0)
            M600 (Arg0, 0x31, Local0, 0x00182F36)
            Local0 = (S601 >> S614) /* \M613.M01E.S614 */
            M600 (Arg0, 0x32, Local0, 0x00)
            Local0 = (S604 >> S614) /* \M613.M01E.S614 */
            M600 (Arg0, 0x33, Local0, 0x00182F36)
        }

        /* Subtract, common 32-bit/64-bit test */

        Method (M01F, 1, Serialized)
        {
            Name (S601, "0321")
            /* Conversion of the first operand */

            Store ((S601 - 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((S601 - 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x0320)
            Store ((S601 - AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((S601 - AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x0320)
            If (Y078)
            {
                Store ((S601 - DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((S601 - DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x0320)
            }

            Store ((S601 - DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((S601 - DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x0320)
            /* Method returns Integer */

            Store ((S601 - M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((S601 - M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x0320)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S601 - DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((S601 - DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x0320)
            }

            Local0 = (S601 - 0x00)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (S601 - 0x01)
            M600 (Arg0, 0x0D, Local0, 0x0320)
            Local0 = (S601 - AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (S601 - AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x0320)
            If (Y078)
            {
                Local0 = (S601 - DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (S601 - DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x0320)
            }

            Local0 = (S601 - DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (S601 - DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x0320)
            /* Method returns Integer */

            Local0 = (S601 - M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (S601 - M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x0320)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S601 - DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (S601 - DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x0320)
            }

            /* Conversion of the second operand */

            Store ((0x00 - S601), Local0)
            M600 (Arg0, 0x18, Local0, 0xFFFFFFFFFFFFFCDF)
            Store ((0x01 - S601), Local0)
            M600 (Arg0, 0x19, Local0, 0xFFFFFFFFFFFFFCE0)
            Store ((AUI5 - S601), Local0)
            M600 (Arg0, 0x1A, Local0, 0xFFFFFFFFFFFFFCDF)
            Store ((AUI6 - S601), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFFFFFFFFFFFFFCE0)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) - S601), Local0)
                M600 (Arg0, 0x1C, Local0, 0xFFFFFFFFFFFFFCDF)
                Store ((DerefOf (RefOf (AUI6)) - S601), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFFFFFFFFFFFFFCE0)
            }

            Store ((DerefOf (PAUI [0x05]) - S601), Local0)
            M600 (Arg0, 0x1E, Local0, 0xFFFFFFFFFFFFFCDF)
            Store ((DerefOf (PAUI [0x06]) - S601), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFFFFFFFFFFFFFCE0)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) - S601), Local0)
            M600 (Arg0, 0x20, Local0, 0xFFFFFFFFFFFFFCDF)
            Store ((M601 (0x01, 0x06) - S601), Local0)
            M600 (Arg0, 0x21, Local0, 0xFFFFFFFFFFFFFCE0)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) - S601), Local0)
                M600 (Arg0, 0x22, Local0, 0xFFFFFFFFFFFFFCDF)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) - S601), Local0)
                M600 (Arg0, 0x23, Local0, 0xFFFFFFFFFFFFFCE0)
            }

            Local0 = (0x00 - S601) /* \M613.M01F.S601 */
            M600 (Arg0, 0x24, Local0, 0xFFFFFFFFFFFFFCDF)
            Local0 = (0x01 - S601) /* \M613.M01F.S601 */
            M600 (Arg0, 0x25, Local0, 0xFFFFFFFFFFFFFCE0)
            Local0 = (AUI5 - S601) /* \M613.M01F.S601 */
            M600 (Arg0, 0x26, Local0, 0xFFFFFFFFFFFFFCDF)
            Local0 = (AUI6 - S601) /* \M613.M01F.S601 */
            M600 (Arg0, 0x27, Local0, 0xFFFFFFFFFFFFFCE0)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) - S601) /* \M613.M01F.S601 */
                M600 (Arg0, 0x28, Local0, 0xFFFFFFFFFFFFFCDF)
                Local0 = (DerefOf (RefOf (AUI6)) - S601) /* \M613.M01F.S601 */
                M600 (Arg0, 0x29, Local0, 0xFFFFFFFFFFFFFCE0)
            }

            Local0 = (DerefOf (PAUI [0x05]) - S601) /* \M613.M01F.S601 */
            M600 (Arg0, 0x2A, Local0, 0xFFFFFFFFFFFFFCDF)
            Local0 = (DerefOf (PAUI [0x06]) - S601) /* \M613.M01F.S601 */
            M600 (Arg0, 0x2B, Local0, 0xFFFFFFFFFFFFFCE0)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) - S601) /* \M613.M01F.S601 */
            M600 (Arg0, 0x2C, Local0, 0xFFFFFFFFFFFFFCDF)
            Local0 = (M601 (0x01, 0x06) - S601) /* \M613.M01F.S601 */
            M600 (Arg0, 0x2D, Local0, 0xFFFFFFFFFFFFFCE0)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) - S601) /* \M613.M01F.S601 */
                M600 (Arg0, 0x2E, Local0, 0xFFFFFFFFFFFFFCDF)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) - S601) /* \M613.M01F.S601 */
                M600 (Arg0, 0x2F, Local0, 0xFFFFFFFFFFFFFCE0)
            }
        }

        /* Subtract, 64-bit */

        Method (M020, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S605, "FE7CB391D650A284")
            /* Conversion of the first operand */

            Store ((S605 - 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((S605 - 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xFE7CB391D650A283)
            Store ((S605 - AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((S605 - AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xFE7CB391D650A283)
            If (Y078)
            {
                Store ((S605 - DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((S605 - DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFE7CB391D650A283)
            }

            Store ((S605 - DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((S605 - DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFE7CB391D650A283)
            /* Method returns Integer */

            Store ((S605 - M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((S605 - M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFE7CB391D650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S605 - DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((S605 - DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFE7CB391D650A283)
            }

            Local0 = (S605 - 0x00)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 - 0x01)
            M600 (Arg0, 0x0D, Local0, 0xFE7CB391D650A283)
            Local0 = (S605 - AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 - AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xFE7CB391D650A283)
            If (Y078)
            {
                Local0 = (S605 - DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (S605 - DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xFE7CB391D650A283)
            }

            Local0 = (S605 - DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 - DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xFE7CB391D650A283)
            /* Method returns Integer */

            Local0 = (S605 - M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 - M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xFE7CB391D650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S605 - DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (S605 - DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFE7CB391D650A283)
            }

            /* Conversion of the second operand */

            Store ((0x00 - S605), Local0)
            M600 (Arg0, 0x18, Local0, 0x01834C6E29AF5D7C)
            Store ((0x01 - S605), Local0)
            M600 (Arg0, 0x19, Local0, 0x01834C6E29AF5D7D)
            Store ((AUI5 - S605), Local0)
            M600 (Arg0, 0x1A, Local0, 0x01834C6E29AF5D7C)
            Store ((AUI6 - S605), Local0)
            M600 (Arg0, 0x1B, Local0, 0x01834C6E29AF5D7D)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) - S605), Local0)
                M600 (Arg0, 0x1C, Local0, 0x01834C6E29AF5D7C)
                Store ((DerefOf (RefOf (AUI6)) - S605), Local0)
                M600 (Arg0, 0x1D, Local0, 0x01834C6E29AF5D7D)
            }

            Store ((DerefOf (PAUI [0x05]) - S605), Local0)
            M600 (Arg0, 0x1E, Local0, 0x01834C6E29AF5D7C)
            Store ((DerefOf (PAUI [0x06]) - S605), Local0)
            M600 (Arg0, 0x1F, Local0, 0x01834C6E29AF5D7D)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) - S605), Local0)
            M600 (Arg0, 0x20, Local0, 0x01834C6E29AF5D7C)
            Store ((M601 (0x01, 0x06) - S605), Local0)
            M600 (Arg0, 0x21, Local0, 0x01834C6E29AF5D7D)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) - S605), Local0)
                M600 (Arg0, 0x22, Local0, 0x01834C6E29AF5D7C)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) - S605), Local0)
                M600 (Arg0, 0x23, Local0, 0x01834C6E29AF5D7D)
            }

            Local0 = (0x00 - S605) /* \M613.M020.S605 */
            M600 (Arg0, 0x24, Local0, 0x01834C6E29AF5D7C)
            Local0 = (0x01 - S605) /* \M613.M020.S605 */
            M600 (Arg0, 0x25, Local0, 0x01834C6E29AF5D7D)
            Local0 = (AUI5 - S605) /* \M613.M020.S605 */
            M600 (Arg0, 0x26, Local0, 0x01834C6E29AF5D7C)
            Local0 = (AUI6 - S605) /* \M613.M020.S605 */
            M600 (Arg0, 0x27, Local0, 0x01834C6E29AF5D7D)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) - S605) /* \M613.M020.S605 */
                M600 (Arg0, 0x28, Local0, 0x01834C6E29AF5D7C)
                Local0 = (DerefOf (RefOf (AUI6)) - S605) /* \M613.M020.S605 */
                M600 (Arg0, 0x29, Local0, 0x01834C6E29AF5D7D)
            }

            Local0 = (DerefOf (PAUI [0x05]) - S605) /* \M613.M020.S605 */
            M600 (Arg0, 0x2A, Local0, 0x01834C6E29AF5D7C)
            Local0 = (DerefOf (PAUI [0x06]) - S605) /* \M613.M020.S605 */
            M600 (Arg0, 0x2B, Local0, 0x01834C6E29AF5D7D)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) - S605) /* \M613.M020.S605 */
            M600 (Arg0, 0x2C, Local0, 0x01834C6E29AF5D7C)
            Local0 = (M601 (0x01, 0x06) - S605) /* \M613.M020.S605 */
            M600 (Arg0, 0x2D, Local0, 0x01834C6E29AF5D7D)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) - S605) /* \M613.M020.S605 */
                M600 (Arg0, 0x2E, Local0, 0x01834C6E29AF5D7C)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) - S605) /* \M613.M020.S605 */
                M600 (Arg0, 0x2F, Local0, 0x01834C6E29AF5D7D)
            }

            /* Conversion of the both operands */

            Store ((S601 - S605), Local0)
            M600 (Arg0, 0x30, Local0, 0x01834C6E29AF609D)
            Store ((S605 - S601), Local0)
            M600 (Arg0, 0x31, Local0, 0xFE7CB391D6509F63)
            Local0 = (S601 - S605) /* \M613.M020.S605 */
            M600 (Arg0, 0x32, Local0, 0x01834C6E29AF609D)
            Local0 = (S605 - S601) /* \M613.M020.S601 */
            M600 (Arg0, 0x33, Local0, 0xFE7CB391D6509F63)
        }

        /* Subtract, 32-bit */

        Method (M021, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            /* Conversion of the first operand */

            Store ((S604 - 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xC179B3FE)
            Store ((S604 - 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xC179B3FD)
            Store ((S604 - AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xC179B3FE)
            Store ((S604 - AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xC179B3FD)
            If (Y078)
            {
                Store ((S604 - DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xC179B3FE)
                Store ((S604 - DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xC179B3FD)
            }

            Store ((S604 - DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xC179B3FE)
            Store ((S604 - DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xC179B3FD)
            /* Method returns Integer */

            Store ((S604 - M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xC179B3FE)
            Store ((S604 - M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xC179B3FD)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S604 - DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xC179B3FE)
                Store ((S604 - DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xC179B3FD)
            }

            Local0 = (S604 - 0x00)
            M600 (Arg0, 0x0C, Local0, 0xC179B3FE)
            Local0 = (S604 - 0x01)
            M600 (Arg0, 0x0D, Local0, 0xC179B3FD)
            Local0 = (S604 - AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xC179B3FE)
            Local0 = (S604 - AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xC179B3FD)
            If (Y078)
            {
                Local0 = (S604 - DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xC179B3FE)
                Local0 = (S604 - DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xC179B3FD)
            }

            Local0 = (S604 - DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xC179B3FE)
            Local0 = (S604 - DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xC179B3FD)
            /* Method returns Integer */

            Local0 = (S604 - M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xC179B3FE)
            Local0 = (S604 - M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xC179B3FD)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S604 - DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xC179B3FE)
                Local0 = (S604 - DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xC179B3FD)
            }

            /* Conversion of the second operand */

            Store ((0x00 - S604), Local0)
            M600 (Arg0, 0x18, Local0, 0x3E864C02)
            Store ((0x01 - S604), Local0)
            M600 (Arg0, 0x19, Local0, 0x3E864C03)
            Store ((AUI5 - S604), Local0)
            M600 (Arg0, 0x1A, Local0, 0x3E864C02)
            Store ((AUI6 - S604), Local0)
            M600 (Arg0, 0x1B, Local0, 0x3E864C03)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) - S604), Local0)
                M600 (Arg0, 0x1C, Local0, 0x3E864C02)
                Store ((DerefOf (RefOf (AUI6)) - S604), Local0)
                M600 (Arg0, 0x1D, Local0, 0x3E864C03)
            }

            Store ((DerefOf (PAUI [0x05]) - S604), Local0)
            M600 (Arg0, 0x1E, Local0, 0x3E864C02)
            Store ((DerefOf (PAUI [0x06]) - S604), Local0)
            M600 (Arg0, 0x1F, Local0, 0x3E864C03)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) - S604), Local0)
            M600 (Arg0, 0x20, Local0, 0x3E864C02)
            Store ((M601 (0x01, 0x06) - S604), Local0)
            M600 (Arg0, 0x21, Local0, 0x3E864C03)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) - S604), Local0)
                M600 (Arg0, 0x22, Local0, 0x3E864C02)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) - S604), Local0)
                M600 (Arg0, 0x23, Local0, 0x3E864C03)
            }

            Local0 = (0x00 - S604) /* \M613.M021.S604 */
            M600 (Arg0, 0x24, Local0, 0x3E864C02)
            Local0 = (0x01 - S604) /* \M613.M021.S604 */
            M600 (Arg0, 0x25, Local0, 0x3E864C03)
            Local0 = (AUI5 - S604) /* \M613.M021.S604 */
            M600 (Arg0, 0x26, Local0, 0x3E864C02)
            Local0 = (AUI6 - S604) /* \M613.M021.S604 */
            M600 (Arg0, 0x27, Local0, 0x3E864C03)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) - S604) /* \M613.M021.S604 */
                M600 (Arg0, 0x28, Local0, 0x3E864C02)
                Local0 = (DerefOf (RefOf (AUI6)) - S604) /* \M613.M021.S604 */
                M600 (Arg0, 0x29, Local0, 0x3E864C03)
            }

            Local0 = (DerefOf (PAUI [0x05]) - S604) /* \M613.M021.S604 */
            M600 (Arg0, 0x2A, Local0, 0x3E864C02)
            Local0 = (DerefOf (PAUI [0x06]) - S604) /* \M613.M021.S604 */
            M600 (Arg0, 0x2B, Local0, 0x3E864C03)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) - S604) /* \M613.M021.S604 */
            M600 (Arg0, 0x2C, Local0, 0x3E864C02)
            Local0 = (M601 (0x01, 0x06) - S604) /* \M613.M021.S604 */
            M600 (Arg0, 0x2D, Local0, 0x3E864C03)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) - S604) /* \M613.M021.S604 */
                M600 (Arg0, 0x2E, Local0, 0x3E864C02)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) - S604) /* \M613.M021.S604 */
                M600 (Arg0, 0x2F, Local0, 0x3E864C03)
            }

            /* Conversion of the both operands */

            Store ((S601 - S604), Local0)
            M600 (Arg0, 0x30, Local0, 0x3E864F23)
            Store ((S604 - S601), Local0)
            M600 (Arg0, 0x31, Local0, 0xC179B0DD)
            Local0 = (S601 - S604) /* \M613.M021.S604 */
            M600 (Arg0, 0x32, Local0, 0x3E864F23)
            Local0 = (S604 - S601) /* \M613.M021.S601 */
            M600 (Arg0, 0x33, Local0, 0xC179B0DD)
        }

        /* XOr, common 32-bit/64-bit test */

        Method (M022, 1, Serialized)
        {
            Name (S601, "0321")
            /* Conversion of the first operand */

            Store ((S601 ^ 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((S601 ^ 0xFFFFFFFFFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0xFFFFFFFFFFFFFCDE)
            Store ((S601 ^ AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((S601 ^ AUIJ), Local0)
            M600 (Arg0, 0x03, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                Store ((S601 ^ DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((S601 ^ DerefOf (RefOf (AUIJ))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Store ((S601 ^ DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((S601 ^ DerefOf (PAUI [0x13])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            Store ((S601 ^ M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((S601 ^ M601 (0x01, 0x13)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S601 ^ DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((S601 ^ DerefOf (M602 (0x01, 0x13, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Local0 = (S601 ^ 0x00)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (S601 ^ 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = (S601 ^ AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (S601 ^ AUIJ) /* \AUIJ */
            M600 (Arg0, 0x0F, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                Local0 = (S601 ^ DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (S601 ^ DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x11, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Local0 = (S601 ^ DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (S601 ^ DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x13, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            Local0 = (S601 ^ M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (S601 ^ M601 (0x01, 0x13))
            M600 (Arg0, 0x15, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S601 ^ DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (S601 ^ DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            /* Conversion of the second operand */

            Store ((0x00 ^ S601), Local0)
            M600 (Arg0, 0x18, Local0, 0x0321)
            Store ((0xFFFFFFFFFFFFFFFF ^ S601), Local0)
            M600 (Arg0, 0x19, Local0, 0xFFFFFFFFFFFFFCDE)
            Store ((AUI5 ^ S601), Local0)
            M600 (Arg0, 0x1A, Local0, 0x0321)
            Store ((AUIJ ^ S601), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) ^ S601), Local0)
                M600 (Arg0, 0x1C, Local0, 0x0321)
                Store ((DerefOf (RefOf (AUIJ)) ^ S601), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Store ((DerefOf (PAUI [0x05]) ^ S601), Local0)
            M600 (Arg0, 0x1E, Local0, 0x0321)
            Store ((DerefOf (PAUI [0x13]) ^ S601), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) ^ S601), Local0)
            M600 (Arg0, 0x20, Local0, 0x0321)
            Store ((M601 (0x01, 0x13) ^ S601), Local0)
            M600 (Arg0, 0x21, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) ^ S601), Local0)
                M600 (Arg0, 0x22, Local0, 0x0321)
                Store ((DerefOf (M602 (0x01, 0x13, 0x01)) ^ S601), Local0)
                M600 (Arg0, 0x23, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Local0 = (0x00 ^ S601) /* \M613.M022.S601 */
            M600 (Arg0, 0x24, Local0, 0x0321)
            Local0 = (0xFFFFFFFFFFFFFFFF ^ S601) /* \M613.M022.S601 */
            M600 (Arg0, 0x25, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = (AUI5 ^ S601) /* \M613.M022.S601 */
            M600 (Arg0, 0x26, Local0, 0x0321)
            Local0 = (AUIJ ^ S601) /* \M613.M022.S601 */
            M600 (Arg0, 0x27, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) ^ S601) /* \M613.M022.S601 */
                M600 (Arg0, 0x28, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (AUIJ)) ^ S601) /* \M613.M022.S601 */
                M600 (Arg0, 0x29, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Local0 = (DerefOf (PAUI [0x05]) ^ S601) /* \M613.M022.S601 */
            M600 (Arg0, 0x2A, Local0, 0x0321)
            Local0 = (DerefOf (PAUI [0x13]) ^ S601) /* \M613.M022.S601 */
            M600 (Arg0, 0x2B, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) ^ S601) /* \M613.M022.S601 */
            M600 (Arg0, 0x2C, Local0, 0x0321)
            Local0 = (M601 (0x01, 0x13) ^ S601) /* \M613.M022.S601 */
            M600 (Arg0, 0x2D, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) ^ S601) /* \M613.M022.S601 */
                M600 (Arg0, 0x2E, Local0, 0x0321)
                Local0 = (DerefOf (M602 (0x01, 0x13, 0x01)) ^ S601) /* \M613.M022.S601 */
                M600 (Arg0, 0x2F, Local0, 0xFFFFFFFFFFFFFCDE)
            }
        }

        /* XOr, 64-bit */

        Method (M023, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S605, "FE7CB391D650A284")
            /* Conversion of the first operand */

            Store ((S605 ^ 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((S605 ^ 0xFFFFFFFFFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0x01834C6E29AF5D7B)
            Store ((S605 ^ AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((S605 ^ AUIJ), Local0)
            M600 (Arg0, 0x03, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                Store ((S605 ^ DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((S605 ^ DerefOf (RefOf (AUIJ))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01834C6E29AF5D7B)
            }

            Store ((S605 ^ DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((S605 ^ DerefOf (PAUI [0x13])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            Store ((S605 ^ M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((S605 ^ M601 (0x01, 0x13)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S605 ^ DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((S605 ^ DerefOf (M602 (0x01, 0x13, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01834C6E29AF5D7B)
            }

            Local0 = (S605 ^ 0x00)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 ^ 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0x01834C6E29AF5D7B)
            Local0 = (S605 ^ AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 ^ AUIJ) /* \AUIJ */
            M600 (Arg0, 0x0F, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                Local0 = (S605 ^ DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (S605 ^ DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x11, Local0, 0x01834C6E29AF5D7B)
            }

            Local0 = (S605 ^ DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 ^ DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x13, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            Local0 = (S605 ^ M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (S605 ^ M601 (0x01, 0x13))
            M600 (Arg0, 0x15, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S605 ^ DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (S605 ^ DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x01834C6E29AF5D7B)
            }

            /* Conversion of the second operand */

            Store ((0x00 ^ S605), Local0)
            M600 (Arg0, 0x18, Local0, 0xFE7CB391D650A284)
            Store ((0xFFFFFFFFFFFFFFFF ^ S605), Local0)
            M600 (Arg0, 0x19, Local0, 0x01834C6E29AF5D7B)
            Store ((AUI5 ^ S605), Local0)
            M600 (Arg0, 0x1A, Local0, 0xFE7CB391D650A284)
            Store ((AUIJ ^ S605), Local0)
            M600 (Arg0, 0x1B, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) ^ S605), Local0)
                M600 (Arg0, 0x1C, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (AUIJ)) ^ S605), Local0)
                M600 (Arg0, 0x1D, Local0, 0x01834C6E29AF5D7B)
            }

            Store ((DerefOf (PAUI [0x05]) ^ S605), Local0)
            M600 (Arg0, 0x1E, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (PAUI [0x13]) ^ S605), Local0)
            M600 (Arg0, 0x1F, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) ^ S605), Local0)
            M600 (Arg0, 0x20, Local0, 0xFE7CB391D650A284)
            Store ((M601 (0x01, 0x13) ^ S605), Local0)
            M600 (Arg0, 0x21, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) ^ S605), Local0)
                M600 (Arg0, 0x22, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (M602 (0x01, 0x13, 0x01)) ^ S605), Local0)
                M600 (Arg0, 0x23, Local0, 0x01834C6E29AF5D7B)
            }

            Local0 = (0x00 ^ S605) /* \M613.M023.S605 */
            M600 (Arg0, 0x24, Local0, 0xFE7CB391D650A284)
            Local0 = (0xFFFFFFFFFFFFFFFF ^ S605) /* \M613.M023.S605 */
            M600 (Arg0, 0x25, Local0, 0x01834C6E29AF5D7B)
            Local0 = (AUI5 ^ S605) /* \M613.M023.S605 */
            M600 (Arg0, 0x26, Local0, 0xFE7CB391D650A284)
            Local0 = (AUIJ ^ S605) /* \M613.M023.S605 */
            M600 (Arg0, 0x27, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) ^ S605) /* \M613.M023.S605 */
                M600 (Arg0, 0x28, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (AUIJ)) ^ S605) /* \M613.M023.S605 */
                M600 (Arg0, 0x29, Local0, 0x01834C6E29AF5D7B)
            }

            Local0 = (DerefOf (PAUI [0x05]) ^ S605) /* \M613.M023.S605 */
            M600 (Arg0, 0x2A, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (PAUI [0x13]) ^ S605) /* \M613.M023.S605 */
            M600 (Arg0, 0x2B, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) ^ S605) /* \M613.M023.S605 */
            M600 (Arg0, 0x2C, Local0, 0xFE7CB391D650A284)
            Local0 = (M601 (0x01, 0x13) ^ S605) /* \M613.M023.S605 */
            M600 (Arg0, 0x2D, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) ^ S605) /* \M613.M023.S605 */
                M600 (Arg0, 0x2E, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (M602 (0x01, 0x13, 0x01)) ^ S605) /* \M613.M023.S605 */
                M600 (Arg0, 0x2F, Local0, 0x01834C6E29AF5D7B)
            }

            /* Conversion of the both operands */

            Store ((S601 ^ S605), Local0)
            M600 (Arg0, 0x30, Local0, 0xFE7CB391D650A1A5)
            Store ((S605 ^ S601), Local0)
            M600 (Arg0, 0x31, Local0, 0xFE7CB391D650A1A5)
            Local0 = (S601 ^ S605) /* \M613.M023.S605 */
            M600 (Arg0, 0x32, Local0, 0xFE7CB391D650A1A5)
            Local0 = (S605 ^ S601) /* \M613.M023.S601 */
            M600 (Arg0, 0x33, Local0, 0xFE7CB391D650A1A5)
        }

        /* XOr, 32-bit */

        Method (M024, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            /* Conversion of the first operand */

            Store ((S604 ^ 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xC179B3FE)
            Store ((S604 ^ 0xFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0x3E864C01)
            Store ((S604 ^ AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xC179B3FE)
            Store ((S604 ^ AUII), Local0)
            M600 (Arg0, 0x03, Local0, 0x3E864C01)
            If (Y078)
            {
                Store ((S604 ^ DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xC179B3FE)
                Store ((S604 ^ DerefOf (RefOf (AUII))), Local0)
                M600 (Arg0, 0x05, Local0, 0x3E864C01)
            }

            Store ((S604 ^ DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xC179B3FE)
            Store ((S604 ^ DerefOf (PAUI [0x12])), Local0)
            M600 (Arg0, 0x07, Local0, 0x3E864C01)
            /* Method returns Integer */

            Store ((S604 ^ M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xC179B3FE)
            Store ((S604 ^ M601 (0x01, 0x12)), Local0)
            M600 (Arg0, 0x09, Local0, 0x3E864C01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((S604 ^ DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xC179B3FE)
                Store ((S604 ^ DerefOf (M602 (0x01, 0x12, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x3E864C01)
            }

            Local0 = (S604 ^ 0x00)
            M600 (Arg0, 0x0C, Local0, 0xC179B3FE)
            Local0 = (S604 ^ 0xFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0x3E864C01)
            Local0 = (S604 ^ AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xC179B3FE)
            Local0 = (S604 ^ AUII) /* \AUII */
            M600 (Arg0, 0x0F, Local0, 0x3E864C01)
            If (Y078)
            {
                Local0 = (S604 ^ DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xC179B3FE)
                Local0 = (S604 ^ DerefOf (RefOf (AUII)))
                M600 (Arg0, 0x11, Local0, 0x3E864C01)
            }

            Local0 = (S604 ^ DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xC179B3FE)
            Local0 = (S604 ^ DerefOf (PAUI [0x12]))
            M600 (Arg0, 0x13, Local0, 0x3E864C01)
            /* Method returns Integer */

            Local0 = (S604 ^ M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xC179B3FE)
            Local0 = (S604 ^ M601 (0x01, 0x12))
            M600 (Arg0, 0x15, Local0, 0x3E864C01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S604 ^ DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xC179B3FE)
                Local0 = (S604 ^ DerefOf (M602 (0x01, 0x12, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x3E864C01)
            }

            /* Conversion of the second operand */

            Store ((0x00 ^ S604), Local0)
            M600 (Arg0, 0x18, Local0, 0xC179B3FE)
            Store ((0xFFFFFFFF ^ S604), Local0)
            M600 (Arg0, 0x19, Local0, 0x3E864C01)
            Store ((AUI5 ^ S604), Local0)
            M600 (Arg0, 0x1A, Local0, 0xC179B3FE)
            Store ((AUII ^ S604), Local0)
            M600 (Arg0, 0x1B, Local0, 0x3E864C01)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) ^ S604), Local0)
                M600 (Arg0, 0x1C, Local0, 0xC179B3FE)
                Store ((DerefOf (RefOf (AUII)) ^ S604), Local0)
                M600 (Arg0, 0x1D, Local0, 0x3E864C01)
            }

            Store ((DerefOf (PAUI [0x05]) ^ S604), Local0)
            M600 (Arg0, 0x1E, Local0, 0xC179B3FE)
            Store ((DerefOf (PAUI [0x12]) ^ S604), Local0)
            M600 (Arg0, 0x1F, Local0, 0x3E864C01)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) ^ S604), Local0)
            M600 (Arg0, 0x20, Local0, 0xC179B3FE)
            Store ((M601 (0x01, 0x12) ^ S604), Local0)
            M600 (Arg0, 0x21, Local0, 0x3E864C01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) ^ S604), Local0)
                M600 (Arg0, 0x22, Local0, 0xC179B3FE)
                Store ((DerefOf (M602 (0x01, 0x12, 0x01)) ^ S604), Local0)
                M600 (Arg0, 0x23, Local0, 0x3E864C01)
            }

            Local0 = (0x00 ^ S604) /* \M613.M024.S604 */
            M600 (Arg0, 0x24, Local0, 0xC179B3FE)
            Local0 = (0xFFFFFFFF ^ S604) /* \M613.M024.S604 */
            M600 (Arg0, 0x25, Local0, 0x3E864C01)
            Local0 = (AUI5 ^ S604) /* \M613.M024.S604 */
            M600 (Arg0, 0x26, Local0, 0xC179B3FE)
            Local0 = (AUII ^ S604) /* \M613.M024.S604 */
            M600 (Arg0, 0x27, Local0, 0x3E864C01)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) ^ S604) /* \M613.M024.S604 */
                M600 (Arg0, 0x28, Local0, 0xC179B3FE)
                Local0 = (DerefOf (RefOf (AUII)) ^ S604) /* \M613.M024.S604 */
                M600 (Arg0, 0x29, Local0, 0x3E864C01)
            }

            Local0 = (DerefOf (PAUI [0x05]) ^ S604) /* \M613.M024.S604 */
            M600 (Arg0, 0x2A, Local0, 0xC179B3FE)
            Local0 = (DerefOf (PAUI [0x12]) ^ S604) /* \M613.M024.S604 */
            M600 (Arg0, 0x2B, Local0, 0x3E864C01)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) ^ S604) /* \M613.M024.S604 */
            M600 (Arg0, 0x2C, Local0, 0xC179B3FE)
            Local0 = (M601 (0x01, 0x12) ^ S604) /* \M613.M024.S604 */
            M600 (Arg0, 0x2D, Local0, 0x3E864C01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) ^ S604) /* \M613.M024.S604 */
                M600 (Arg0, 0x2E, Local0, 0xC179B3FE)
                Local0 = (DerefOf (M602 (0x01, 0x12, 0x01)) ^ S604) /* \M613.M024.S604 */
                M600 (Arg0, 0x2F, Local0, 0x3E864C01)
            }

            /* Conversion of the both operands */

            Store ((S601 ^ S604), Local0)
            M600 (Arg0, 0x30, Local0, 0xC179B0DF)
            Store ((S604 ^ S601), Local0)
            M600 (Arg0, 0x31, Local0, 0xC179B0DF)
            Local0 = (S601 ^ S604) /* \M613.M024.S604 */
            M600 (Arg0, 0x32, Local0, 0xC179B0DF)
            Local0 = (S604 ^ S601) /* \M613.M024.S601 */
            M600 (Arg0, 0x33, Local0, 0xC179B0DF)
        }

        /* Add, And, Divide, Mod, Multiply, NAnd, NOr, Or, */
        /* ShiftLeft, ShiftRight, Subtract, Xor */
        Method (M64D, 1, NotSerialized)
        {
            /* Add */

            Concatenate (Arg0, "-m001", Local0)
            SRMT (Local0)
            M001 (Local0)
            Concatenate (Arg0, "-m002", Local0)
            SRMT (Local0)
            M002 (Local0)
            /* And */

            Concatenate (Arg0, "-m004", Local0)
            SRMT (Local0)
            M004 (Local0)
            Concatenate (Arg0, "-m005", Local0)
            SRMT (Local0)
            M005 (Local0)
            /* Divide */

            Concatenate (Arg0, "-m007", Local0)
            SRMT (Local0)
            M007 (Local0)
            Concatenate (Arg0, "-m008", Local0)
            SRMT (Local0)
            M008 (Local0)
            /* Mod */

            Concatenate (Arg0, "-m00a", Local0)
            SRMT (Local0)
            M00A (Local0)
            Concatenate (Arg0, "-m00b", Local0)
            SRMT (Local0)
            M00B (Local0)
            /* Multiply */

            Concatenate (Arg0, "-m00d", Local0)
            SRMT (Local0)
            M00D (Local0)
            Concatenate (Arg0, "-m00e", Local0)
            SRMT (Local0)
            M00E (Local0)
            /* NAnd */

            Concatenate (Arg0, "-m010", Local0)
            SRMT (Local0)
            M010 (Local0)
            Concatenate (Arg0, "-m011", Local0)
            SRMT (Local0)
            M011 (Local0)
            /* NOr */

            Concatenate (Arg0, "-m013", Local0)
            SRMT (Local0)
            M013 (Local0)
            Concatenate (Arg0, "-m014", Local0)
            SRMT (Local0)
            M014 (Local0)
            /* Or */

            Concatenate (Arg0, "-m016", Local0)
            SRMT (Local0)
            M016 (Local0)
            Concatenate (Arg0, "-m017", Local0)
            SRMT (Local0)
            M017 (Local0)
            /* ShiftLeft */

            Concatenate (Arg0, "-m019", Local0)
            SRMT (Local0)
            M019 (Local0)
            Concatenate (Arg0, "-m01a", Local0)
            SRMT (Local0)
            M01A (Local0)
            /* ShiftRight */

            Concatenate (Arg0, "-m01c", Local0)
            SRMT (Local0)
            M01C (Local0)
            Concatenate (Arg0, "-m01d", Local0)
            SRMT (Local0)
            M01D (Local0)
            /* Subtract */

            Concatenate (Arg0, "-m01f", Local0)
            SRMT (Local0)
            M01F (Local0)
            Concatenate (Arg0, "-m020", Local0)
            SRMT (Local0)
            M020 (Local0)
            /* XOr */

            Concatenate (Arg0, "-m022", Local0)
            SRMT (Local0)
            M022 (Local0)
            Concatenate (Arg0, "-m023", Local0)
            SRMT (Local0)
            M023 (Local0)
        }

        Method (M32D, 1, NotSerialized)
        {
            /* Add */

            Concatenate (Arg0, "-m001", Local0)
            SRMT (Local0)
            M001 (Local0)
            Concatenate (Arg0, "-m003", Local0)
            SRMT (Local0)
            M003 (Local0)
            /* And */

            Concatenate (Arg0, "-m004", Local0)
            SRMT (Local0)
            M004 (Local0)
            Concatenate (Arg0, "-m006", Local0)
            SRMT (Local0)
            M006 (Local0)
            /* Divide */

            Concatenate (Arg0, "-m007", Local0)
            SRMT (Local0)
            M007 (Local0)
            Concatenate (Arg0, "-m009", Local0)
            SRMT (Local0)
            M009 (Local0)
            /* Mod */

            Concatenate (Arg0, "-m00a", Local0)
            SRMT (Local0)
            M00A (Local0)
            Concatenate (Arg0, "-m00c", Local0)
            SRMT (Local0)
            M00C (Local0)
            /* Multiply */

            Concatenate (Arg0, "-m00d", Local0)
            SRMT (Local0)
            M00D (Local0)
            Concatenate (Arg0, "-m00f", Local0)
            SRMT (Local0)
            M00F (Local0)
            /* NAnd */

            Concatenate (Arg0, "-m010", Local0)
            SRMT (Local0)
            If (Y119)
            {
                M010 (Local0)
            }
            Else
            {
                BLCK ()
            }

            Concatenate (Arg0, "-m012", Local0)
            SRMT (Local0)
            M012 (Local0)
            /* NOr */

            Concatenate (Arg0, "-m013", Local0)
            SRMT (Local0)
            If (Y119)
            {
                M013 (Local0)
            }
            Else
            {
                BLCK ()
            }

            Concatenate (Arg0, "-m015", Local0)
            SRMT (Local0)
            M015 (Local0)
            /* Or */

            Concatenate (Arg0, "-m016", Local0)
            SRMT (Local0)
            If (Y119)
            {
                M016 (Local0)
            }
            Else
            {
                BLCK ()
            }

            Concatenate (Arg0, "-m018", Local0)
            SRMT (Local0)
            M018 (Local0)
            /* ShiftLeft */

            Concatenate (Arg0, "-m019", Local0)
            SRMT (Local0)
            M019 (Local0)
            Concatenate (Arg0, "-m01b", Local0)
            SRMT (Local0)
            M01B (Local0)
            /* ShiftRight */

            Concatenate (Arg0, "-m01c", Local0)
            SRMT (Local0)
            M01C (Local0)
            Concatenate (Arg0, "-m01e", Local0)
            SRMT (Local0)
            M01E (Local0)
            /* Subtract */

            Concatenate (Arg0, "-m01f", Local0)
            SRMT (Local0)
            If (Y119)
            {
                M01F (Local0)
            }
            Else
            {
                BLCK ()
            }

            Concatenate (Arg0, "-m021", Local0)
            SRMT (Local0)
            M021 (Local0)
            /* XOr */

            Concatenate (Arg0, "-m022", Local0)
            SRMT (Local0)
            If (Y119)
            {
                M022 (Local0)
            }
            Else
            {
                BLCK ()
            }

            Concatenate (Arg0, "-m024", Local0)
            SRMT (Local0)
            M024 (Local0)
        }

        /* String to Integer conversion of each String operand */
        /* of the 2-parameter Logical Integer operators LAnd and LOr */
        /* LAnd, common 32-bit/64-bit test */
        Method (M025, 1, Serialized)
        {
            Name (S601, "0321")
            /* Conversion of the first operand */

            Local0 = (S601 && 0x00)
            M600 (Arg0, 0x00, Local0, Zero)
            Local0 = (S601 && 0x01)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = (S601 && AUI5)
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (S601 && AUI6)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = (S601 && DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, Zero)
                Local0 = (S601 && DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = (S601 && DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, Zero)
            Local0 = (S601 && DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Integer */

            Local0 = (S601 && M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, Zero)
            Local0 = (S601 && M601 (0x01, 0x06))
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S601 && DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, Zero)
                Local0 = (S601 && DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x0B, Local0, Ones)
            }

            /* Conversion of the second operand */

            Local0 = (0x00 && S601)
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = (0x01 && S601)
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (AUI5 && S601)
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = (AUI6 && S601)
            M600 (Arg0, 0x0F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) && S601)
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUI6)) && S601)
                M600 (Arg0, 0x11, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x05]) && S601)
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x06]) && S601)
            M600 (Arg0, 0x13, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) && S601)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (M601 (0x01, 0x06) && S601)
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) && S601)
                M600 (Arg0, 0x16, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) && S601)
                M600 (Arg0, 0x17, Local0, Ones)
            }
        }

        /* LAnd, 64-bit */

        Method (M026, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S605, "FE7CB391D650A284")
            /* Conversion of the first operand */

            Local0 = (S605 && 0x00)
            M600 (Arg0, 0x00, Local0, Zero)
            Local0 = (S605 && 0x01)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = (S605 && AUI5)
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (S605 && AUI6)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = (S605 && DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, Zero)
                Local0 = (S605 && DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = (S605 && DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, Zero)
            Local0 = (S605 && DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Integer */

            Local0 = (S605 && M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, Zero)
            Local0 = (S605 && M601 (0x01, 0x06))
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S605 && DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, Zero)
                Local0 = (S605 && DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x0B, Local0, Ones)
            }

            /* Conversion of the second operand */

            Local0 = (0x00 && S605)
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = (0x01 && S605)
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (AUI5 && S605)
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = (AUI6 && S605)
            M600 (Arg0, 0x0F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) && S605)
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUI6)) && S605)
                M600 (Arg0, 0x11, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x05]) && S605)
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x06]) && S605)
            M600 (Arg0, 0x13, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) && S605)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (M601 (0x01, 0x06) && S605)
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) && S605)
                M600 (Arg0, 0x16, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) && S605)
                M600 (Arg0, 0x17, Local0, Ones)
            }

            /* Conversion of the both operands */

            Local0 = (S601 && S605)
            M600 (Arg0, 0x18, Local0, Ones)
            Local0 = (S605 && S601)
            M600 (Arg0, 0x19, Local0, Ones)
        }

        /* LAnd, 32-bit */

        Method (M027, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            /* Conversion of the first operand */

            Local0 = (S604 && 0x00)
            M600 (Arg0, 0x00, Local0, Zero)
            Local0 = (S604 && 0x01)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = (S604 && AUI5)
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (S604 && AUI6)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = (S604 && DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, Zero)
                Local0 = (S604 && DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = (S604 && DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, Zero)
            Local0 = (S604 && DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Integer */

            Local0 = (S604 && M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, Zero)
            Local0 = (S604 && M601 (0x01, 0x06))
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S604 && DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, Zero)
                Local0 = (S604 && DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x0B, Local0, Ones)
            }

            /* Conversion of the second operand */

            Local0 = (0x00 && S604)
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = (0x01 && S604)
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (AUI5 && S604)
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = (AUI6 && S604)
            M600 (Arg0, 0x0F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) && S604)
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUI6)) && S604)
                M600 (Arg0, 0x11, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x05]) && S604)
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x06]) && S604)
            M600 (Arg0, 0x13, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) && S604)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (M601 (0x01, 0x06) && S604)
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) && S604)
                M600 (Arg0, 0x16, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) && S604)
                M600 (Arg0, 0x17, Local0, Ones)
            }

            /* Conversion of the both operands */

            Local0 = (S601 && S604)
            M600 (Arg0, 0x18, Local0, Ones)
            Local0 = (S604 && S601)
            M600 (Arg0, 0x19, Local0, Ones)
        }

        /* Lor, common 32-bit/64-bit test */

        Method (M028, 1, Serialized)
        {
            Name (S600, "0")
            /* Conversion of the first operand */

            Local0 = (S600 || 0x00)
            M600 (Arg0, 0x00, Local0, Zero)
            Local0 = (S600 || 0x01)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = (S600 || AUI5)
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (S600 || AUI6)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = (S600 || DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, Zero)
                Local0 = (S600 || DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = (S600 || DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, Zero)
            Local0 = (S600 || DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Integer */

            Local0 = (S600 || M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, Zero)
            Local0 = (S600 || M601 (0x01, 0x06))
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S600 || DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, Zero)
                Local0 = (S600 || DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x0B, Local0, Ones)
            }

            /* Conversion of the second operand */

            Local0 = (0x00 || S600)
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = (0x01 || S600)
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (AUI5 || S600)
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = (AUI6 || S600)
            M600 (Arg0, 0x0F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) || S600)
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUI6)) || S600)
                M600 (Arg0, 0x11, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x05]) || S600)
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x06]) || S600)
            M600 (Arg0, 0x13, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) || S600)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (M601 (0x01, 0x06) || S600)
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) || S600)
                M600 (Arg0, 0x16, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) || S600)
                M600 (Arg0, 0x17, Local0, Ones)
            }
        }

        /* Lor, 64-bit */

        Method (M029, 1, Serialized)
        {
            Name (S600, "0")
            Name (S605, "FE7CB391D650A284")
            /* Conversion of the first operand */

            Local0 = (S605 || 0x00)
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (S605 || 0x01)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = (S605 || AUI5)
            M600 (Arg0, 0x02, Local0, Ones)
            Local0 = (S605 || AUI6)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = (S605 || DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, Ones)
                Local0 = (S605 || DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = (S605 || DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, Ones)
            Local0 = (S605 || DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Integer */

            Local0 = (S605 || M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, Ones)
            Local0 = (S605 || M601 (0x01, 0x06))
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S605 || DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, Ones)
                Local0 = (S605 || DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x0B, Local0, Ones)
            }

            /* Conversion of the second operand */

            Local0 = (0x00 || S605)
            M600 (Arg0, 0x0C, Local0, Ones)
            Local0 = (0x01 || S605)
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (AUI5 || S605)
            M600 (Arg0, 0x0E, Local0, Ones)
            Local0 = (AUI6 || S605)
            M600 (Arg0, 0x0F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) || S605)
                M600 (Arg0, 0x10, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUI6)) || S605)
                M600 (Arg0, 0x11, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x05]) || S605)
            M600 (Arg0, 0x12, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x06]) || S605)
            M600 (Arg0, 0x13, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) || S605)
            M600 (Arg0, 0x14, Local0, Ones)
            Local0 = (M601 (0x01, 0x06) || S605)
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) || S605)
                M600 (Arg0, 0x16, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) || S605)
                M600 (Arg0, 0x17, Local0, Ones)
            }

            /* Conversion of the both operands */

            Local0 = (S600 || S605)
            M600 (Arg0, 0x18, Local0, Ones)
            Local0 = (S605 || S600)
            M600 (Arg0, 0x19, Local0, Ones)
        }

        /* Lor, 32-bit */

        Method (M02A, 1, Serialized)
        {
            Name (S600, "0")
            Name (S604, "C179B3FE")
            /* Conversion of the first operand */

            Local0 = (S604 || 0x00)
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (S604 || 0x01)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = (S604 || AUI5)
            M600 (Arg0, 0x02, Local0, Ones)
            Local0 = (S604 || AUI6)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = (S604 || DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, Ones)
                Local0 = (S604 || DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = (S604 || DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, Ones)
            Local0 = (S604 || DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Integer */

            Local0 = (S604 || M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, Ones)
            Local0 = (S604 || M601 (0x01, 0x06))
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (S604 || DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, Ones)
                Local0 = (S604 || DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x0B, Local0, Ones)
            }

            /* Conversion of the second operand */

            Local0 = (0x00 || S604)
            M600 (Arg0, 0x0C, Local0, Ones)
            Local0 = (0x01 || S604)
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (AUI5 || S604)
            M600 (Arg0, 0x0E, Local0, Ones)
            Local0 = (AUI6 || S604)
            M600 (Arg0, 0x0F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) || S604)
                M600 (Arg0, 0x10, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUI6)) || S604)
                M600 (Arg0, 0x11, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x05]) || S604)
            M600 (Arg0, 0x12, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x06]) || S604)
            M600 (Arg0, 0x13, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) || S604)
            M600 (Arg0, 0x14, Local0, Ones)
            Local0 = (M601 (0x01, 0x06) || S604)
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) || S604)
                M600 (Arg0, 0x16, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) || S604)
                M600 (Arg0, 0x17, Local0, Ones)
            }

            /* Conversion of the both operands */

            Local0 = (S600 || S604)
            M600 (Arg0, 0x18, Local0, Ones)
            Local0 = (S604 || S600)
            M600 (Arg0, 0x19, Local0, Ones)
        }

        Method (M64E, 1, NotSerialized)
        {
            /* LAnd */

            Concatenate (Arg0, "-m025", Local0)
            SRMT (Local0)
            M025 (Local0)
            Concatenate (Arg0, "-m026", Local0)
            SRMT (Local0)
            M026 (Local0)
            /* LOr */

            Concatenate (Arg0, "-m028", Local0)
            SRMT (Local0)
            M028 (Local0)
            Concatenate (Arg0, "-m029", Local0)
            SRMT (Local0)
            M029 (Local0)
        }

        Method (M32E, 1, NotSerialized)
        {
            /* LAnd */

            Concatenate (Arg0, "-m025", Local0)
            SRMT (Local0)
            M025 (Local0)
            Concatenate (Arg0, "-m027", Local0)
            SRMT (Local0)
            M027 (Local0)
            /* LOr */

            Concatenate (Arg0, "-m028", Local0)
            SRMT (Local0)
            M028 (Local0)
            Concatenate (Arg0, "-m02a", Local0)
            SRMT (Local0)
            M02A (Local0)
        }

        /* String to Integer conversion of the String second operand of */
        /* Logical operators when the first operand is evaluated as Integer */
        /* (LEqual, LGreater, LGreaterEqual, LLess, LLessEqual, LNotEqual) */
        Method (M64F, 1, Serialized)
        {
            Name (S605, "FE7CB391D650A284")
            /* LEqual */

            Local0 = (0xFE7CB391D650A284 == S605)
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (0xFE7CB391D650A285 == S605)
            M600 (Arg0, 0x01, Local0, Zero)
            Local0 = (0xFE7CB391D650A283 == S605)
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (AUI4 == S605)
            M600 (Arg0, 0x03, Local0, Ones)
            Local0 = (AUID == S605)
            M600 (Arg0, 0x04, Local0, Zero)
            Local0 = (AUIF == S605)
            M600 (Arg0, 0x05, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI4)) == S605)
                M600 (Arg0, 0x06, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUID)) == S605)
                M600 (Arg0, 0x07, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIF)) == S605)
                M600 (Arg0, 0x08, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x04]) == S605)
            M600 (Arg0, 0x09, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0D]) == S605)
            M600 (Arg0, 0x0A, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0F]) == S605)
            M600 (Arg0, 0x0B, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x04) == S605)
            M600 (Arg0, 0x0C, Local0, Ones)
            Local0 = (M601 (0x01, 0x0D) == S605)
            M600 (Arg0, 0x0D, Local0, Zero)
            Local0 = (M601 (0x01, 0x0F) == S605)
            M600 (Arg0, 0x0E, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) == S605)
                M600 (Arg0, 0x0F, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) == S605)
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) == S605)
                M600 (Arg0, 0x11, Local0, Zero)
            }

            /* LGreater */

            Local0 = (0xFE7CB391D650A284 > S605)
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (0xFE7CB391D650A285 > S605)
            M600 (Arg0, 0x13, Local0, Ones)
            Local0 = (0xFE7CB391D650A283 > S605)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (AUI4 > S605)
            M600 (Arg0, 0x15, Local0, Zero)
            Local0 = (AUID > S605)
            M600 (Arg0, 0x16, Local0, Ones)
            Local0 = (AUIF > S605)
            M600 (Arg0, 0x17, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI4)) > S605)
                M600 (Arg0, 0x18, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUID)) > S605)
                M600 (Arg0, 0x19, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIF)) > S605)
                M600 (Arg0, 0x1A, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x04]) > S605)
            M600 (Arg0, 0x1B, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0D]) > S605)
            M600 (Arg0, 0x1C, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0F]) > S605)
            M600 (Arg0, 0x1D, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x04) > S605)
            M600 (Arg0, 0x1E, Local0, Zero)
            Local0 = (M601 (0x01, 0x0D) > S605)
            M600 (Arg0, 0x1F, Local0, Ones)
            Local0 = (M601 (0x01, 0x0F) > S605)
            M600 (Arg0, 0x20, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) > S605)
                M600 (Arg0, 0x21, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) > S605)
                M600 (Arg0, 0x22, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) > S605)
                M600 (Arg0, 0x23, Local0, Zero)
            }

            /* LGreaterEqual */

            Local0 = (0xFE7CB391D650A284 >= S605)
            M600 (Arg0, 0x24, Local0, Ones)
            Local0 = (0xFE7CB391D650A285 >= S605)
            M600 (Arg0, 0x25, Local0, Ones)
            Local0 = (0xFE7CB391D650A283 >= S605)
            M600 (Arg0, 0x26, Local0, Zero)
            Local0 = (AUI4 >= S605)
            M600 (Arg0, 0x27, Local0, Ones)
            Local0 = (AUID >= S605)
            M600 (Arg0, 0x28, Local0, Ones)
            Local0 = (AUIF >= S605)
            M600 (Arg0, 0x29, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI4)) >= S605)
                M600 (Arg0, 0x2A, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUID)) >= S605)
                M600 (Arg0, 0x2B, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIF)) >= S605)
                M600 (Arg0, 0x2C, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x04]) >= S605)
            M600 (Arg0, 0x2D, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0D]) >= S605)
            M600 (Arg0, 0x2E, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0F]) >= S605)
            M600 (Arg0, 0x2F, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x04) >= S605)
            M600 (Arg0, 0x30, Local0, Ones)
            Local0 = (M601 (0x01, 0x0D) >= S605)
            M600 (Arg0, 0x31, Local0, Ones)
            Local0 = (M601 (0x01, 0x0F) >= S605)
            M600 (Arg0, 0x32, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) >= S605)
                M600 (Arg0, 0x33, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) >= S605)
                M600 (Arg0, 0x34, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) >= S605)
                M600 (Arg0, 0x35, Local0, Zero)
            }

            /* LLess */

            Local0 = (0xFE7CB391D650A284 < S605)
            M600 (Arg0, 0x36, Local0, Zero)
            Local0 = (0xFE7CB391D650A285 < S605)
            M600 (Arg0, 0x37, Local0, Zero)
            Local0 = (0xFE7CB391D650A283 < S605)
            M600 (Arg0, 0x38, Local0, Ones)
            Local0 = (AUI4 < S605)
            M600 (Arg0, 0x39, Local0, Zero)
            Local0 = (AUID < S605)
            M600 (Arg0, 0x3A, Local0, Zero)
            Local0 = (AUIF < S605)
            M600 (Arg0, 0x3B, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI4)) < S605)
                M600 (Arg0, 0x3C, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUID)) < S605)
                M600 (Arg0, 0x3D, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIF)) < S605)
                M600 (Arg0, 0x3E, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x04]) < S605)
            M600 (Arg0, 0x3F, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0D]) < S605)
            M600 (Arg0, 0x40, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0F]) < S605)
            M600 (Arg0, 0x41, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x04) < S605)
            M600 (Arg0, 0x42, Local0, Zero)
            Local0 = (M601 (0x01, 0x0D) < S605)
            M600 (Arg0, 0x43, Local0, Zero)
            Local0 = (M601 (0x01, 0x0F) < S605)
            M600 (Arg0, 0x44, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) < S605)
                M600 (Arg0, 0x45, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) < S605)
                M600 (Arg0, 0x46, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) < S605)
                M600 (Arg0, 0x47, Local0, Ones)
            }

            /* LLessEqual */

            Local0 = (0xFE7CB391D650A284 <= S605)
            M600 (Arg0, 0x48, Local0, Ones)
            Local0 = (0xFE7CB391D650A285 <= S605)
            M600 (Arg0, 0x49, Local0, Zero)
            Local0 = (0xFE7CB391D650A283 <= S605)
            M600 (Arg0, 0x4A, Local0, Ones)
            Local0 = (AUI4 <= S605)
            M600 (Arg0, 0x4B, Local0, Ones)
            Local0 = (AUID <= S605)
            M600 (Arg0, 0x4C, Local0, Zero)
            Local0 = (AUIF <= S605)
            M600 (Arg0, 0x4D, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI4)) <= S605)
                M600 (Arg0, 0x4E, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUID)) <= S605)
                M600 (Arg0, 0x4F, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIF)) <= S605)
                M600 (Arg0, 0x50, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x04]) <= S605)
            M600 (Arg0, 0x51, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0D]) <= S605)
            M600 (Arg0, 0x52, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0F]) <= S605)
            M600 (Arg0, 0x53, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x04) <= S605)
            M600 (Arg0, 0x54, Local0, Ones)
            Local0 = (M601 (0x01, 0x0D) <= S605)
            M600 (Arg0, 0x55, Local0, Zero)
            Local0 = (M601 (0x01, 0x0F) <= S605)
            M600 (Arg0, 0x56, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) <= S605)
                M600 (Arg0, 0x57, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) <= S605)
                M600 (Arg0, 0x58, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) <= S605)
                M600 (Arg0, 0x59, Local0, Ones)
            }

            /* LNotEqual */

            Local0 = (0xFE7CB391D650A284 != S605)
            M600 (Arg0, 0x5A, Local0, Zero)
            Local0 = (0xFE7CB391D650A285 != S605)
            M600 (Arg0, 0x5B, Local0, Ones)
            Local0 = (0xFE7CB391D650A283 != S605)
            M600 (Arg0, 0x5C, Local0, Ones)
            Local0 = (AUI4 != S605)
            M600 (Arg0, 0x5D, Local0, Zero)
            Local0 = (AUID != S605)
            M600 (Arg0, 0x5E, Local0, Ones)
            Local0 = (AUIF != S605)
            M600 (Arg0, 0x5F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI4)) != S605)
                M600 (Arg0, 0x60, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUID)) != S605)
                M600 (Arg0, 0x61, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIF)) != S605)
                M600 (Arg0, 0x62, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x04]) != S605)
            M600 (Arg0, 0x63, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0D]) != S605)
            M600 (Arg0, 0x64, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0F]) != S605)
            M600 (Arg0, 0x65, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x04) != S605)
            M600 (Arg0, 0x66, Local0, Zero)
            Local0 = (M601 (0x01, 0x0D) != S605)
            M600 (Arg0, 0x67, Local0, Ones)
            Local0 = (M601 (0x01, 0x0F) != S605)
            M600 (Arg0, 0x68, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) != S605)
                M600 (Arg0, 0x69, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) != S605)
                M600 (Arg0, 0x6A, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) != S605)
                M600 (Arg0, 0x6B, Local0, Ones)
            }
        }

        Method (M32F, 1, Serialized)
        {
            Name (S604, "C179B3FE")
            /* LEqual */

            Local0 = (0xC179B3FE == S604)
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (0xC179B3FF == S604)
            M600 (Arg0, 0x01, Local0, Zero)
            Local0 = (0xC179B3FD == S604)
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (AUI3 == S604)
            M600 (Arg0, 0x03, Local0, Ones)
            Local0 = (AUIC == S604)
            M600 (Arg0, 0x04, Local0, Zero)
            Local0 = (AUIE == S604)
            M600 (Arg0, 0x05, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI3)) == S604)
                M600 (Arg0, 0x06, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIC)) == S604)
                M600 (Arg0, 0x07, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIE)) == S604)
                M600 (Arg0, 0x08, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x03]) == S604)
            M600 (Arg0, 0x09, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0C]) == S604)
            M600 (Arg0, 0x0A, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0E]) == S604)
            M600 (Arg0, 0x0B, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x03) == S604)
            M600 (Arg0, 0x0C, Local0, Ones)
            Local0 = (M601 (0x01, 0x0C) == S604)
            M600 (Arg0, 0x0D, Local0, Zero)
            Local0 = (M601 (0x01, 0x0E) == S604)
            M600 (Arg0, 0x0E, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x03, 0x01)) == S604)
                M600 (Arg0, 0x0F, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0C, 0x01)) == S604)
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0E, 0x01)) == S604)
                M600 (Arg0, 0x11, Local0, Zero)
            }

            /* LGreater */

            Local0 = (0xC179B3FE > S604)
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (0xC179B3FF > S604)
            M600 (Arg0, 0x13, Local0, Ones)
            Local0 = (0xC179B3FD > S604)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (AUI3 > S604)
            M600 (Arg0, 0x15, Local0, Zero)
            Local0 = (AUIC > S604)
            M600 (Arg0, 0x16, Local0, Ones)
            Local0 = (AUIE > S604)
            M600 (Arg0, 0x17, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI3)) > S604)
                M600 (Arg0, 0x18, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIC)) > S604)
                M600 (Arg0, 0x19, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIE)) > S604)
                M600 (Arg0, 0x1A, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x03]) > S604)
            M600 (Arg0, 0x1B, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0C]) > S604)
            M600 (Arg0, 0x1C, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0E]) > S604)
            M600 (Arg0, 0x1D, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x03) > S604)
            M600 (Arg0, 0x1E, Local0, Zero)
            Local0 = (M601 (0x01, 0x0C) > S604)
            M600 (Arg0, 0x1F, Local0, Ones)
            Local0 = (M601 (0x01, 0x0E) > S604)
            M600 (Arg0, 0x20, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x03, 0x01)) > S604)
                M600 (Arg0, 0x21, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0C, 0x01)) > S604)
                M600 (Arg0, 0x22, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0E, 0x01)) > S604)
                M600 (Arg0, 0x23, Local0, Zero)
            }

            /* LGreaterEqual */

            Local0 = (0xC179B3FE >= S604)
            M600 (Arg0, 0x24, Local0, Ones)
            Local0 = (0xC179B3FF >= S604)
            M600 (Arg0, 0x25, Local0, Ones)
            Local0 = (0xC179B3FD >= S604)
            M600 (Arg0, 0x26, Local0, Zero)
            Local0 = (AUI3 >= S604)
            M600 (Arg0, 0x27, Local0, Ones)
            Local0 = (AUIC >= S604)
            M600 (Arg0, 0x28, Local0, Ones)
            Local0 = (AUIE >= S604)
            M600 (Arg0, 0x29, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI3)) >= S604)
                M600 (Arg0, 0x2A, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIC)) >= S604)
                M600 (Arg0, 0x2B, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIE)) >= S604)
                M600 (Arg0, 0x2C, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x03]) >= S604)
            M600 (Arg0, 0x2D, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0C]) >= S604)
            M600 (Arg0, 0x2E, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0E]) >= S604)
            M600 (Arg0, 0x2F, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x03) >= S604)
            M600 (Arg0, 0x30, Local0, Ones)
            Local0 = (M601 (0x01, 0x0C) >= S604)
            M600 (Arg0, 0x31, Local0, Ones)
            Local0 = (M601 (0x01, 0x0E) >= S604)
            M600 (Arg0, 0x32, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x03, 0x01)) >= S604)
                M600 (Arg0, 0x33, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0C, 0x01)) >= S604)
                M600 (Arg0, 0x34, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0E, 0x01)) >= S604)
                M600 (Arg0, 0x35, Local0, Zero)
            }

            /* LLess */

            Local0 = (0xC179B3FE < S604)
            M600 (Arg0, 0x36, Local0, Zero)
            Local0 = (0xC179B3FF < S604)
            M600 (Arg0, 0x37, Local0, Zero)
            Local0 = (0xC179B3FD < S604)
            M600 (Arg0, 0x38, Local0, Ones)
            Local0 = (AUI3 < S604)
            M600 (Arg0, 0x39, Local0, Zero)
            Local0 = (AUIC < S604)
            M600 (Arg0, 0x3A, Local0, Zero)
            Local0 = (AUIE < S604)
            M600 (Arg0, 0x3B, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI3)) < S604)
                M600 (Arg0, 0x3C, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIC)) < S604)
                M600 (Arg0, 0x3D, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIE)) < S604)
                M600 (Arg0, 0x3E, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x03]) < S604)
            M600 (Arg0, 0x3F, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0C]) < S604)
            M600 (Arg0, 0x40, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0E]) < S604)
            M600 (Arg0, 0x41, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x03) < S604)
            M600 (Arg0, 0x42, Local0, Zero)
            Local0 = (M601 (0x01, 0x0C) < S604)
            M600 (Arg0, 0x43, Local0, Zero)
            Local0 = (M601 (0x01, 0x0E) < S604)
            M600 (Arg0, 0x44, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x03, 0x01)) < S604)
                M600 (Arg0, 0x45, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0C, 0x01)) < S604)
                M600 (Arg0, 0x46, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0E, 0x01)) < S604)
                M600 (Arg0, 0x47, Local0, Ones)
            }

            /* LLessEqual */

            Local0 = (0xC179B3FE <= S604)
            M600 (Arg0, 0x48, Local0, Ones)
            Local0 = (0xC179B3FF <= S604)
            M600 (Arg0, 0x49, Local0, Zero)
            Local0 = (0xC179B3FD <= S604)
            M600 (Arg0, 0x4A, Local0, Ones)
            Local0 = (AUI3 <= S604)
            M600 (Arg0, 0x4B, Local0, Ones)
            Local0 = (AUIC <= S604)
            M600 (Arg0, 0x4C, Local0, Zero)
            Local0 = (AUIE <= S604)
            M600 (Arg0, 0x4D, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI3)) <= S604)
                M600 (Arg0, 0x4E, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIC)) <= S604)
                M600 (Arg0, 0x4F, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIE)) <= S604)
                M600 (Arg0, 0x50, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x03]) <= S604)
            M600 (Arg0, 0x51, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0C]) <= S604)
            M600 (Arg0, 0x52, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0E]) <= S604)
            M600 (Arg0, 0x53, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x03) <= S604)
            M600 (Arg0, 0x54, Local0, Ones)
            Local0 = (M601 (0x01, 0x0C) <= S604)
            M600 (Arg0, 0x55, Local0, Zero)
            Local0 = (M601 (0x01, 0x0E) <= S604)
            M600 (Arg0, 0x56, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x03, 0x01)) <= S604)
                M600 (Arg0, 0x57, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0C, 0x01)) <= S604)
                M600 (Arg0, 0x58, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0E, 0x01)) <= S604)
                M600 (Arg0, 0x59, Local0, Ones)
            }

            /* LNotEqual */

            Local0 = (0xC179B3FE != S604)
            M600 (Arg0, 0x5A, Local0, Zero)
            Local0 = (0xC179B3FF != S604)
            M600 (Arg0, 0x5B, Local0, Ones)
            Local0 = (0xC179B3FD != S604)
            M600 (Arg0, 0x5C, Local0, Ones)
            Local0 = (AUI3 != S604)
            M600 (Arg0, 0x5D, Local0, Zero)
            Local0 = (AUIC != S604)
            M600 (Arg0, 0x5E, Local0, Ones)
            Local0 = (AUIE != S604)
            M600 (Arg0, 0x5F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI3)) != S604)
                M600 (Arg0, 0x60, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIC)) != S604)
                M600 (Arg0, 0x61, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIE)) != S604)
                M600 (Arg0, 0x62, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x03]) != S604)
            M600 (Arg0, 0x63, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0C]) != S604)
            M600 (Arg0, 0x64, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0E]) != S604)
            M600 (Arg0, 0x65, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x03) != S604)
            M600 (Arg0, 0x66, Local0, Zero)
            Local0 = (M601 (0x01, 0x0C) != S604)
            M600 (Arg0, 0x67, Local0, Ones)
            Local0 = (M601 (0x01, 0x0E) != S604)
            M600 (Arg0, 0x68, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x03, 0x01)) != S604)
                M600 (Arg0, 0x69, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0C, 0x01)) != S604)
                M600 (Arg0, 0x6A, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0E, 0x01)) != S604)
                M600 (Arg0, 0x6B, Local0, Ones)
            }
        }

        Method (M02B, 1, Serialized)
        {
            Name (S601, "0321")
            /* LEqual */

            Local0 = (0x0321 == S601)
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (0x0322 == S601)
            M600 (Arg0, 0x01, Local0, Zero)
            Local0 = (0x0320 == S601)
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (AUI1 == S601)
            M600 (Arg0, 0x03, Local0, Ones)
            Local0 = (AUIG == S601)
            M600 (Arg0, 0x04, Local0, Zero)
            Local0 = (AUIH == S601)
            M600 (Arg0, 0x05, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) == S601)
                M600 (Arg0, 0x06, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIG)) == S601)
                M600 (Arg0, 0x07, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIH)) == S601)
                M600 (Arg0, 0x08, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x01]) == S601)
            M600 (Arg0, 0x09, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x10]) == S601)
            M600 (Arg0, 0x0A, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x11]) == S601)
            M600 (Arg0, 0x0B, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) == S601)
            M600 (Arg0, 0x0C, Local0, Ones)
            Local0 = (M601 (0x01, 0x10) == S601)
            M600 (Arg0, 0x0D, Local0, Zero)
            Local0 = (M601 (0x01, 0x11) == S601)
            M600 (Arg0, 0x0E, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) == S601)
                M600 (Arg0, 0x0F, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) == S601)
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) == S601)
                M600 (Arg0, 0x11, Local0, Zero)
            }

            /* LGreater */

            Local0 = (0x0321 > S601)
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (0x0322 > S601)
            M600 (Arg0, 0x13, Local0, Ones)
            Local0 = (0x0320 > S601)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (AUI1 > S601)
            M600 (Arg0, 0x15, Local0, Zero)
            Local0 = (AUIG > S601)
            M600 (Arg0, 0x16, Local0, Ones)
            Local0 = (AUIH > S601)
            M600 (Arg0, 0x17, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) > S601)
                M600 (Arg0, 0x18, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIG)) > S601)
                M600 (Arg0, 0x19, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIH)) > S601)
                M600 (Arg0, 0x1A, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x01]) > S601)
            M600 (Arg0, 0x1B, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x10]) > S601)
            M600 (Arg0, 0x1C, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x11]) > S601)
            M600 (Arg0, 0x1D, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) > S601)
            M600 (Arg0, 0x1E, Local0, Zero)
            Local0 = (M601 (0x01, 0x10) > S601)
            M600 (Arg0, 0x1F, Local0, Ones)
            Local0 = (M601 (0x01, 0x11) > S601)
            M600 (Arg0, 0x20, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) > S601)
                M600 (Arg0, 0x21, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) > S601)
                M600 (Arg0, 0x22, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) > S601)
                M600 (Arg0, 0x23, Local0, Zero)
            }

            /* LGreaterEqual */

            Local0 = (0x0321 >= S601)
            M600 (Arg0, 0x24, Local0, Ones)
            Local0 = (0x0322 >= S601)
            M600 (Arg0, 0x25, Local0, Ones)
            Local0 = (0x0320 >= S601)
            M600 (Arg0, 0x26, Local0, Zero)
            Local0 = (AUI1 >= S601)
            M600 (Arg0, 0x27, Local0, Ones)
            Local0 = (AUIG >= S601)
            M600 (Arg0, 0x28, Local0, Ones)
            Local0 = (AUIH >= S601)
            M600 (Arg0, 0x29, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) >= S601)
                M600 (Arg0, 0x2A, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIG)) >= S601)
                M600 (Arg0, 0x2B, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIH)) >= S601)
                M600 (Arg0, 0x2C, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x01]) >= S601)
            M600 (Arg0, 0x2D, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x10]) >= S601)
            M600 (Arg0, 0x2E, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x11]) >= S601)
            M600 (Arg0, 0x2F, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) >= S601)
            M600 (Arg0, 0x30, Local0, Ones)
            Local0 = (M601 (0x01, 0x10) >= S601)
            M600 (Arg0, 0x31, Local0, Ones)
            Local0 = (M601 (0x01, 0x11) >= S601)
            M600 (Arg0, 0x32, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) >= S601)
                M600 (Arg0, 0x33, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) >= S601)
                M600 (Arg0, 0x34, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) >= S601)
                M600 (Arg0, 0x35, Local0, Zero)
            }

            /* LLess */

            Local0 = (0x0321 < S601)
            M600 (Arg0, 0x36, Local0, Zero)
            Local0 = (0x0322 < S601)
            M600 (Arg0, 0x37, Local0, Zero)
            Local0 = (0x0320 < S601)
            M600 (Arg0, 0x38, Local0, Ones)
            Local0 = (AUI1 < S601)
            M600 (Arg0, 0x39, Local0, Zero)
            Local0 = (AUIG < S601)
            M600 (Arg0, 0x3A, Local0, Zero)
            Local0 = (AUIH < S601)
            M600 (Arg0, 0x3B, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) < S601)
                M600 (Arg0, 0x3C, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIG)) < S601)
                M600 (Arg0, 0x3D, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIH)) < S601)
                M600 (Arg0, 0x3E, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x01]) < S601)
            M600 (Arg0, 0x3F, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x10]) < S601)
            M600 (Arg0, 0x40, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x11]) < S601)
            M600 (Arg0, 0x41, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) < S601)
            M600 (Arg0, 0x42, Local0, Zero)
            Local0 = (M601 (0x01, 0x10) < S601)
            M600 (Arg0, 0x43, Local0, Zero)
            Local0 = (M601 (0x01, 0x11) < S601)
            M600 (Arg0, 0x44, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) < S601)
                M600 (Arg0, 0x45, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) < S601)
                M600 (Arg0, 0x46, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) < S601)
                M600 (Arg0, 0x47, Local0, Ones)
            }

            /* LLessEqual */

            Local0 = (0x0321 <= S601)
            M600 (Arg0, 0x48, Local0, Ones)
            Local0 = (0x0322 <= S601)
            M600 (Arg0, 0x49, Local0, Zero)
            Local0 = (0x0320 <= S601)
            M600 (Arg0, 0x4A, Local0, Ones)
            Local0 = (AUI1 <= S601)
            M600 (Arg0, 0x4B, Local0, Ones)
            Local0 = (AUIG <= S601)
            M600 (Arg0, 0x4C, Local0, Zero)
            Local0 = (AUIH <= S601)
            M600 (Arg0, 0x4D, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) <= S601)
                M600 (Arg0, 0x4E, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIG)) <= S601)
                M600 (Arg0, 0x4F, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIH)) <= S601)
                M600 (Arg0, 0x50, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x01]) <= S601)
            M600 (Arg0, 0x51, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x10]) <= S601)
            M600 (Arg0, 0x52, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x11]) <= S601)
            M600 (Arg0, 0x53, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) <= S601)
            M600 (Arg0, 0x54, Local0, Ones)
            Local0 = (M601 (0x01, 0x10) <= S601)
            M600 (Arg0, 0x55, Local0, Zero)
            Local0 = (M601 (0x01, 0x11) <= S601)
            M600 (Arg0, 0x56, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) <= S601)
                M600 (Arg0, 0x57, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) <= S601)
                M600 (Arg0, 0x58, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) <= S601)
                M600 (Arg0, 0x59, Local0, Ones)
            }

            /* LNotEqual */

            Local0 = (0x0321 != S601)
            M600 (Arg0, 0x5A, Local0, Zero)
            Local0 = (0x0322 != S601)
            M600 (Arg0, 0x5B, Local0, Ones)
            Local0 = (0x0320 != S601)
            M600 (Arg0, 0x5C, Local0, Ones)
            Local0 = (AUI1 != S601)
            M600 (Arg0, 0x5D, Local0, Zero)
            Local0 = (AUIG != S601)
            M600 (Arg0, 0x5E, Local0, Ones)
            Local0 = (AUIH != S601)
            M600 (Arg0, 0x5F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) != S601)
                M600 (Arg0, 0x60, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIG)) != S601)
                M600 (Arg0, 0x61, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIH)) != S601)
                M600 (Arg0, 0x62, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x01]) != S601)
            M600 (Arg0, 0x63, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x10]) != S601)
            M600 (Arg0, 0x64, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x11]) != S601)
            M600 (Arg0, 0x65, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) != S601)
            M600 (Arg0, 0x66, Local0, Zero)
            Local0 = (M601 (0x01, 0x10) != S601)
            M600 (Arg0, 0x67, Local0, Ones)
            Local0 = (M601 (0x01, 0x11) != S601)
            M600 (Arg0, 0x68, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) != S601)
                M600 (Arg0, 0x69, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) != S601)
                M600 (Arg0, 0x6A, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) != S601)
                M600 (Arg0, 0x6B, Local0, Ones)
            }
        }

        /* String to Integer intermediate conversion of the String second */
        /* operand of Concatenate operator in case the first one is Integer */
        Method (M64G, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S605, "FE7CB391D650A284")
            Local0 = Concatenate (0x0321, S601)
            M600 (Arg0, 0x00, Local0, BB26)
            Local0 = Concatenate (0x0321, S605)
            M600 (Arg0, 0x01, Local0, BB21)
            Local0 = Concatenate (AUI1, S601)
            M600 (Arg0, 0x02, Local0, BB26)
            Local0 = Concatenate (AUI1, S605)
            M600 (Arg0, 0x03, Local0, BB21)
            If (Y078)
            {
                Local0 = Concatenate (DerefOf (RefOf (AUI1)), S601)
                M600 (Arg0, 0x04, Local0, BB26)
                Local0 = Concatenate (DerefOf (RefOf (AUI1)), S605)
                M600 (Arg0, 0x05, Local0, BB21)
            }

            Local0 = Concatenate (DerefOf (PAUI [0x01]), S601)
            M600 (Arg0, 0x06, Local0, BB26)
            Local0 = Concatenate (DerefOf (PAUI [0x01]), S605)
            M600 (Arg0, 0x07, Local0, BB21)
            /* Method returns Integer */

            Local0 = Concatenate (M601 (0x01, 0x01), S601)
            M600 (Arg0, 0x08, Local0, BB26)
            Local0 = Concatenate (M601 (0x01, 0x01), S605)
            M600 (Arg0, 0x09, Local0, BB21)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), S601)
                M600 (Arg0, 0x0A, Local0, BB26)
                Local0 = Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), S605)
                M600 (Arg0, 0x0B, Local0, BB21)
            }

            Concatenate (0x0321, S601, Local0)
            M600 (Arg0, 0x0C, Local0, BB26)
            Concatenate (0x0321, S605, Local0)
            M600 (Arg0, 0x0D, Local0, BB21)
            Concatenate (AUI1, S601, Local0)
            M600 (Arg0, 0x0E, Local0, BB26)
            Concatenate (AUI1, S605, Local0)
            M600 (Arg0, 0x0F, Local0, BB21)
            If (Y078)
            {
                Concatenate (DerefOf (RefOf (AUI1)), S601, Local0)
                M600 (Arg0, 0x10, Local0, BB26)
                Concatenate (DerefOf (RefOf (AUI1)), S605, Local0)
                M600 (Arg0, 0x11, Local0, BB21)
            }

            Concatenate (DerefOf (PAUI [0x01]), S601, Local0)
            M600 (Arg0, 0x12, Local0, BB26)
            Concatenate (DerefOf (PAUI [0x01]), S605, Local0)
            M600 (Arg0, 0x13, Local0, BB21)
            /* Method returns Integer */

            Concatenate (M601 (0x01, 0x01), S601, Local0)
            M600 (Arg0, 0x14, Local0, BB26)
            Concatenate (M601 (0x01, 0x01), S605, Local0)
            M600 (Arg0, 0x15, Local0, BB21)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), S601, Local0)
                M600 (Arg0, 0x16, Local0, BB26)
                Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), S605, Local0)
                M600 (Arg0, 0x17, Local0, BB21)
            }
        }

        Method (M32G, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            Local0 = Concatenate (0x0321, S601)
            M600 (Arg0, 0x00, Local0, BB27)
            Local0 = Concatenate (0x0321, S604)
            M600 (Arg0, 0x01, Local0, BB24)
            Local0 = Concatenate (AUI1, S601)
            M600 (Arg0, 0x02, Local0, BB27)
            Local0 = Concatenate (AUI1, S604)
            M600 (Arg0, 0x03, Local0, BB24)
            If (Y078)
            {
                Local0 = Concatenate (DerefOf (RefOf (AUI1)), S601)
                M600 (Arg0, 0x04, Local0, BB27)
                Local0 = Concatenate (DerefOf (RefOf (AUI1)), S604)
                M600 (Arg0, 0x05, Local0, BB24)
            }

            Local0 = Concatenate (DerefOf (PAUI [0x01]), S601)
            M600 (Arg0, 0x06, Local0, BB27)
            Local0 = Concatenate (DerefOf (PAUI [0x01]), S604)
            M600 (Arg0, 0x07, Local0, BB24)
            /* Method returns Integer */

            Local0 = Concatenate (M601 (0x01, 0x01), S601)
            M600 (Arg0, 0x08, Local0, BB27)
            Local0 = Concatenate (M601 (0x01, 0x01), S604)
            M600 (Arg0, 0x09, Local0, BB24)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), S601)
                M600 (Arg0, 0x0A, Local0, BB27)
                Local0 = Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), S604)
                M600 (Arg0, 0x0B, Local0, BB24)
            }

            Concatenate (0x0321, S601, Local0)
            M600 (Arg0, 0x0C, Local0, BB27)
            Concatenate (0x0321, S604, Local0)
            M600 (Arg0, 0x0D, Local0, BB24)
            Concatenate (AUI1, S601, Local0)
            M600 (Arg0, 0x0E, Local0, BB27)
            Concatenate (AUI1, S604, Local0)
            M600 (Arg0, 0x0F, Local0, BB24)
            If (Y078)
            {
                Concatenate (DerefOf (RefOf (AUI1)), S601, Local0)
                M600 (Arg0, 0x10, Local0, BB27)
                Concatenate (DerefOf (RefOf (AUI1)), S604, Local0)
                M600 (Arg0, 0x11, Local0, BB24)
            }

            Concatenate (DerefOf (PAUI [0x01]), S601, Local0)
            M600 (Arg0, 0x12, Local0, BB27)
            Concatenate (DerefOf (PAUI [0x01]), S604, Local0)
            M600 (Arg0, 0x14, Local0, BB24)
            /* Method returns Integer */

            Concatenate (M601 (0x01, 0x01), S601, Local0)
            M600 (Arg0, 0x15, Local0, BB27)
            Concatenate (M601 (0x01, 0x01), S604, Local0)
            M600 (Arg0, 0x16, Local0, BB24)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), S601, Local0)
                M600 (Arg0, 0x17, Local0, BB27)
                Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), S604, Local0)
                M600 (Arg0, 0x18, Local0, BB24)
            }
        }

        /* String to Integer conversion of the String Length (second) */
        /* operand of the ToString operator */
        /* Common 32-bit/64-bit test */
        Method (M02C, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S614, "B")
            Local0 = ToString (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, S614)
            M600 (Arg0, 0x00, Local0, BS1B)
            Local0 = ToString (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, S601)
            M600 (Arg0, 0x01, Local0, BS1C)
            Local0 = ToString (AUB6, S614)
            M600 (Arg0, 0x02, Local0, BS1B)
            Local0 = ToString (AUB6, S601)
            M600 (Arg0, 0x03, Local0, BS1C)
            If (Y078)
            {
                Local0 = ToString (DerefOf (RefOf (AUB6)), S614)
                M600 (Arg0, 0x04, Local0, BS1B)
                Local0 = ToString (DerefOf (RefOf (AUB6)), S601)
                M600 (Arg0, 0x05, Local0, BS1C)
            }

            Local0 = ToString (DerefOf (PAUB [0x06]), S614)
            M600 (Arg0, 0x06, Local0, BS1B)
            Local0 = ToString (DerefOf (PAUB [0x06]), S601)
            M600 (Arg0, 0x07, Local0, BS1C)
            /* Method returns Buffer */

            Local0 = ToString (M601 (0x03, 0x06), S614)
            M600 (Arg0, 0x08, Local0, BS1B)
            Local0 = ToString (M601 (0x03, 0x06), S601)
            M600 (Arg0, 0x09, Local0, BS1C)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = ToString (DerefOf (M602 (0x03, 0x06, 0x01)), S614)
                M600 (Arg0, 0x0A, Local0, BS1B)
                Local0 = ToString (DerefOf (M602 (0x03, 0x06, 0x01)), S601)
                M600 (Arg0, 0x0B, Local0, BS1C)
            }

            ToString (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, S614, Local0)
            M600 (Arg0, 0x0C, Local0, BS1B)
            ToString (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, S601, Local0)
            M600 (Arg0, 0x0D, Local0, BS1C)
            ToString (AUB6, S614, Local0)
            M600 (Arg0, 0x0E, Local0, BS1B)
            ToString (AUB6, S601, Local0)
            M600 (Arg0, 0x0F, Local0, BS1C)
            If (Y078)
            {
                ToString (DerefOf (RefOf (AUB6)), S614, Local0)
                M600 (Arg0, 0x10, Local0, BS1B)
                ToString (DerefOf (RefOf (AUB6)), S601, Local0)
                M600 (Arg0, 0x11, Local0, BS1C)
            }

            ToString (DerefOf (PAUB [0x06]), S614, Local0)
            M600 (Arg0, 0x12, Local0, BS1B)
            ToString (DerefOf (PAUB [0x06]), S601, Local0)
            M600 (Arg0, 0x13, Local0, BS1C)
            /* Method returns Buffer */

            ToString (M601 (0x03, 0x06), S614, Local0)
            M600 (Arg0, 0x14, Local0, BS1B)
            ToString (M601 (0x03, 0x06), S601, Local0)
            M600 (Arg0, 0x15, Local0, BS1C)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                ToString (DerefOf (M602 (0x03, 0x06, 0x01)), S614, Local0)
                M600 (Arg0, 0x16, Local0, BS1B)
                ToString (DerefOf (M602 (0x03, 0x06, 0x01)), S601, Local0)
                M600 (Arg0, 0x17, Local0, BS1C)
            }
        }

        Method (M64H, 1, Serialized)
        {
            Name (S605, "FE7CB391D650A284")
            Local0 = ToString (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, S605)
            M600 (Arg0, 0x00, Local0, BS1C)
            Local0 = ToString (AUB6, S605)
            M600 (Arg0, 0x01, Local0, BS1C)
            If (Y078)
            {
                Local0 = ToString (DerefOf (RefOf (AUB6)), S605)
                M600 (Arg0, 0x02, Local0, BS1C)
            }

            Local0 = ToString (DerefOf (PAUB [0x06]), S605)
            M600 (Arg0, 0x03, Local0, BS1C)
            /* Method returns Buffer */

            Local0 = ToString (M601 (0x03, 0x06), S605)
            M600 (Arg0, 0x04, Local0, BS1C)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = ToString (DerefOf (M602 (0x03, 0x06, 0x01)), S605)
                M600 (Arg0, 0x05, Local0, BS1C)
            }

            ToString (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, S605, Local0)
            M600 (Arg0, 0x06, Local0, BS1C)
            ToString (AUB6, S605, Local0)
            M600 (Arg0, 0x07, Local0, BS1C)
            If (Y078)
            {
                ToString (DerefOf (RefOf (AUB6)), S605, Local0)
                M600 (Arg0, 0x08, Local0, BS1C)
            }

            ToString (DerefOf (PAUB [0x06]), S605, Local0)
            M600 (Arg0, 0x09, Local0, BS1C)
            /* Method returns Buffer */

            ToString (M601 (0x03, 0x06), S605, Local0)
            M600 (Arg0, 0x0A, Local0, BS1C)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                ToString (DerefOf (M602 (0x03, 0x06, 0x01)), S605, Local0)
                M600 (Arg0, 0x0B, Local0, BS1C)
            }
        }

        Method (M32H, 1, Serialized)
        {
            Name (S604, "C179B3FE")
            Local0 = ToString (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, S604)
            M600 (Arg0, 0x00, Local0, BS1C)
            Local0 = ToString (AUB6, S604)
            M600 (Arg0, 0x01, Local0, BS1C)
            If (Y078)
            {
                Local0 = ToString (DerefOf (RefOf (AUB6)), S604)
                M600 (Arg0, 0x02, Local0, BS1C)
            }

            Local0 = ToString (DerefOf (PAUB [0x06]), S604)
            M600 (Arg0, 0x03, Local0, BS1C)
            /* Method returns Buffer */

            Local0 = ToString (M601 (0x03, 0x06), S604)
            M600 (Arg0, 0x04, Local0, BS1C)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = ToString (DerefOf (M602 (0x03, 0x06, 0x01)), S604)
                M600 (Arg0, 0x05, Local0, BS1C)
            }

            ToString (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, S604, Local0)
            M600 (Arg0, 0x06, Local0, BS1C)
            ToString (AUB6, S604, Local0)
            M600 (Arg0, 0x07, Local0, BS1C)
            If (Y078)
            {
                ToString (DerefOf (RefOf (AUB6)), S604, Local0)
                M600 (Arg0, 0x08, Local0, BS1C)
            }

            ToString (DerefOf (PAUB [0x06]), S604, Local0)
            M600 (Arg0, 0x09, Local0, BS1C)
            /* Method returns Buffer */

            ToString (M601 (0x03, 0x06), S604, Local0)
            M600 (Arg0, 0x0A, Local0, BS1C)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                ToString (DerefOf (M602 (0x03, 0x06, 0x01)), S604, Local0)
                M600 (Arg0, 0x0B, Local0, BS1C)
            }
        }

        /* String to Integer conversion of the String Index (second) */
        /* operand of the Index operator */
        Method (M02D, 1, Serialized)
        {
            Name (S614, "B")
            Store (AUS6 [S614], Local0)
            M600 (Arg0, 0x00, DerefOf (Local0), BI10)
            Store (AUB6 [S614], Local0)
            M600 (Arg0, 0x01, DerefOf (Local0), BI10)
            Store (AUP0 [S614], Local0)
            M600 (Arg0, 0x02, DerefOf (Local0), BI11)
            If (Y078)
            {
                Store (DerefOf (RefOf (AUS6)) [S614], Local0)
                M600 (Arg0, 0x03, DerefOf (Local0), BI10)
                Store (DerefOf (RefOf (AUB6)) [S614], Local0)
                M600 (Arg0, 0x04, DerefOf (Local0), BI10)
                Store (DerefOf (RefOf (AUP0)) [S614], Local0)
                M600 (Arg0, 0x05, DerefOf (Local0), BI11)
            }

            Store (DerefOf (PAUS [0x06]) [S614], Local0)
            M600 (Arg0, 0x06, DerefOf (Local0), BI10)
            Store (DerefOf (PAUB [0x06]) [S614], Local0)
            M600 (Arg0, 0x07, DerefOf (Local0), BI10)
            Store (DerefOf (PAUP [0x00]) [S614], Local0)
            M600 (Arg0, 0x08, DerefOf (Local0), BI11)
            /* Method returns Object */

            If (Y900)
            {
                Store (M601 (0x02, 0x06) [S614], Local0)
                M600 (Arg0, 0x09, DerefOf (Local0), BI10)
                Store (M601 (0x03, 0x06) [S614], Local0)
                M600 (Arg0, 0x0A, DerefOf (Local0), BI10)
                Store (M601 (0x04, 0x00) [S614], Local0)
                M600 (Arg0, 0x0B, DerefOf (Local0), BI11)
            }
            Else
            {
                CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
                Store (M601 (0x02, 0x06) [S614], Local3)
                CH04 (Arg0, 0x00, 0x55, Z088, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
                Store (M601 (0x03, 0x06) [S614], Local3)
                CH04 (Arg0, 0x00, 0x55, Z088, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
                Store (M601 (0x04, 0x00) [S614], Local3)
                CH04 (Arg0, 0x00, 0x55, Z088, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
            }

            /* Method returns Reference */

            If (Y500)
            {
                Store (DerefOf (M602 (0x02, 0x06, 0x01)) [S614], Local0)
                M600 (Arg0, 0x0C, DerefOf (Local0), BI10)
                Store (DerefOf (M602 (0x03, 0x06, 0x01)) [S614], Local0)
                M600 (Arg0, 0x0D, DerefOf (Local0), BI10)
                Store (DerefOf (M602 (0x04, 0x00, 0x01)) [S614], Local0)
                M600 (Arg0, 0x0E, DerefOf (Local0), BI11)
            }

            Local0 = AUS6 [S614] /* \M613.M02D.S614 */
            M600 (Arg0, 0x0F, DerefOf (Local0), BI10)
            Local0 = AUB6 [S614] /* \M613.M02D.S614 */
            M600 (Arg0, 0x10, DerefOf (Local0), BI10)
            Local0 = AUP0 [S614] /* \M613.M02D.S614 */
            M600 (Arg0, 0x11, DerefOf (Local0), BI11)
            If (Y078)
            {
                Local0 = DerefOf (RefOf (AUS6)) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x12, DerefOf (Local0), BI10)
                Local0 = DerefOf (RefOf (AUB6)) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x13, DerefOf (Local0), BI10)
                Local0 = DerefOf (RefOf (AUP0)) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x14, DerefOf (Local0), BI11)
            }

            Local0 = DerefOf (PAUS [0x06]) [S614] /* \M613.M02D.S614 */
            M600 (Arg0, 0x15, DerefOf (Local0), BI10)
            Local0 = DerefOf (PAUB [0x06]) [S614] /* \M613.M02D.S614 */
            M600 (Arg0, 0x16, DerefOf (Local0), BI10)
            Local0 = DerefOf (PAUP [0x00]) [S614] /* \M613.M02D.S614 */
            M600 (Arg0, 0x17, DerefOf (Local0), BI11)
            /* Method returns Object */

            If (Y900)
            {
                Local0 = M601 (0x02, 0x06) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x18, DerefOf (Local0), BI10)
                Local0 = M601 (0x03, 0x06) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x19, DerefOf (Local0), BI10)
                Local0 = M601 (0x04, 0x00) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x1A, DerefOf (Local0), BI11)
            }
            Else
            {
                CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
                Local0 = M601 (0x02, 0x06) [S614] /* \M613.M02D.S614 */
                CH04 (Arg0, 0x00, 0x55, Z088, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
                Local0 = M601 (0x03, 0x06) [S614] /* \M613.M02D.S614 */
                CH04 (Arg0, 0x00, 0x55, Z088, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
                Local0 = M601 (0x04, 0x00) [S614] /* \M613.M02D.S614 */
                CH04 (Arg0, 0x00, 0x55, Z088, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
            }

            /* Method returns Reference */

            If (Y500)
            {
                Local0 = DerefOf (M602 (0x02, 0x06, 0x01)) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x1B, DerefOf (Local0), BI10)
                Local0 = DerefOf (M602 (0x03, 0x06, 0x01)) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x1C, DerefOf (Local0), BI10)
                Local0 = DerefOf (M602 (0x04, 0x00, 0x01)) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x1D, DerefOf (Local0), BI11)
            }

            If (Y098)
            {
                Local0 = Local1 = AUS6 [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x1E, DerefOf (Local0), BI10)
                Local0 = Local1 = AUB6 [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x1F, DerefOf (Local0), BI10)
                Local0 = Local1 = AUP0 [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x20, DerefOf (Local0), BI11)
            }

            If (Y078)
            {
                Local0 = Local1 = DerefOf (RefOf (AUS6)) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x21, DerefOf (Local0), BI10)
                Local0 = Local1 = DerefOf (RefOf (AUB6)) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x22, DerefOf (Local0), BI10)
                Local0 = Local1 = DerefOf (RefOf (AUP0)) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x23, DerefOf (Local0), BI11)
            }

            If (Y098)
            {
                Local0 = Local1 = DerefOf (PAUS [0x06]) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x24, DerefOf (Local0), BI10)
                Local0 = Local1 = DerefOf (PAUB [0x06]) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x25, DerefOf (Local0), BI10)
                Local0 = Local1 = DerefOf (PAUP [0x00]) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x26, DerefOf (Local0), BI11)
            }

            /* Method returns Object */

            If ((Y900 && Y098))
            {
                Local0 = Local1 = M601 (0x02, 0x06) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x27, DerefOf (Local0), BI10)
                Local0 = Local1 = M601 (0x03, 0x06) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x28, DerefOf (Local0), BI10)
                Local0 = Local1 = M601 (0x04, 0x00) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x29, DerefOf (Local0), BI11)
            }

            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Local1 = DerefOf (M602 (0x02, 0x06, 0x01)) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x2A, DerefOf (Local0), BI10)
                Local0 = Local1 = DerefOf (M602 (0x03, 0x06, 0x01)) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x2B, DerefOf (Local0), BI10)
                Local0 = Local1 = DerefOf (M602 (0x04, 0x00, 0x01)) [S614] /* \M613.M02D.S614 */
                M600 (Arg0, 0x2C, DerefOf (Local0), BI11)
            }
        }

        /* String to Integer conversion of the String Arg (third) */
        /* operand of the Fatal operator */
        /* (it can only be checked an exception does not occur) */
        Method (M02E, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            Name (S605, "FE7CB391D650A284")
            CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
            Fatal (0xFF, 0xFFFFFFFF, S601)
            If (F64)
            {
                Fatal (0xFF, 0xFFFFFFFF, S605)
            }
            Else
            {
                Fatal (0xFF, 0xFFFFFFFF, S604)
            }

            CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
        }

        /* String to Integer conversion of the String Index and Length */
        /* operands of the Mid operator */
        /* Common 32-bit/64-bit test */
        Method (M02F, 1, Serialized)
        {
            Name (S614, "B")
            /* String to Integer conversion of the String Index operand */

            Local0 = Mid ("This is auxiliary String", S614, 0x0A)
            M600 (Arg0, 0x00, Local0, BS1D)
            Local0 = Mid (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, S614, 0x0A)
            M600 (Arg0, 0x01, Local0, BB32)
            Local0 = Mid (AUS6, S614, 0x0A)
            M600 (Arg0, 0x02, Local0, BS1D)
            Local0 = Mid (AUB6, S614, 0x0A)
            M600 (Arg0, 0x03, Local0, BB32)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (AUS6)), S614, 0x0A)
                M600 (Arg0, 0x04, Local0, BS1D)
                Local0 = Mid (DerefOf (RefOf (AUB6)), S614, 0x0A)
                M600 (Arg0, 0x05, Local0, BB32)
            }

            Local0 = Mid (DerefOf (PAUS [0x06]), S614, 0x0A)
            M600 (Arg0, 0x06, Local0, BS1D)
            Local0 = Mid (DerefOf (PAUB [0x06]), S614, 0x0A)
            M600 (Arg0, 0x07, Local0, BB32)
            /* Method returns Object */

            Local0 = Mid (M601 (0x02, 0x06), S614, 0x0A)
            M600 (Arg0, 0x08, Local0, BS1D)
            Local0 = Mid (M601 (0x03, 0x06), S614, 0x0A)
            M600 (Arg0, 0x09, Local0, BB32)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Mid (DerefOf (M602 (0x02, 0x06, 0x01)), S614, 0x0A)
                M600 (Arg0, 0x0A, Local0, BS1D)
                Local0 = Mid (DerefOf (M602 (0x03, 0x06, 0x01)), S614, 0x0A)
                M600 (Arg0, 0x0B, Local0, BB32)
            }

            Mid ("This is auxiliary String", S614, 0x0A, Local0)
            M600 (Arg0, 0x0C, Local0, BS1D)
            Mid (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, S614, 0x0A, Local0)
            M600 (Arg0, 0x0D, Local0, BB32)
            Mid (AUS6, S614, 0x0A, Local0)
            M600 (Arg0, 0x0E, Local0, BS1D)
            Mid (AUB6, S614, 0x0A, Local0)
            M600 (Arg0, 0x0F, Local0, BB32)
            If (Y078)
            {
                Mid (DerefOf (RefOf (AUS6)), S614, 0x0A, Local0)
                M600 (Arg0, 0x10, Local0, BS1D)
                Mid (DerefOf (RefOf (AUB6)), S614, 0x0A, Local0)
                M600 (Arg0, 0x11, Local0, BB32)
            }

            Mid (DerefOf (PAUS [0x06]), S614, 0x0A, Local0)
            M600 (Arg0, 0x12, Local0, BS1D)
            Mid (DerefOf (PAUB [0x06]), S614, 0x0A, Local0)
            M600 (Arg0, 0x13, Local0, BB32)
            /* Method returns Object */

            Mid (M601 (0x02, 0x06), S614, 0x0A, Local0)
            M600 (Arg0, 0x14, Local0, BS1D)
            Mid (M601 (0x03, 0x06), S614, 0x0A, Local0)
            M600 (Arg0, 0x15, Local0, BB32)
            /* Method returns Reference */

            If (Y500)
            {
                Mid (DerefOf (M602 (0x02, 0x06, 0x01)), S614, 0x0A, Local0)
                M600 (Arg0, 0x16, Local0, BS1D)
                Mid (DerefOf (M602 (0x03, 0x06, 0x01)), S614, 0x0A, Local0)
                M600 (Arg0, 0x17, Local0, BB32)
            }

            /* String to Integer conversion of the String Length operand */

            Local0 = Mid ("This is auxiliary String", 0x00, S614)
            M600 (Arg0, 0x18, Local0, BS1B)
            Local0 = Mid (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, 0x00, S614)
            M600 (Arg0, 0x19, Local0, BB33)
            Local0 = Mid (AUS6, 0x00, S614)
            M600 (Arg0, 0x1A, Local0, BS1B)
            Local0 = Mid (AUB6, 0x00, S614)
            M600 (Arg0, 0x1B, Local0, BB33)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (AUS6)), 0x00, S614)
                M600 (Arg0, 0x1C, Local0, BS1B)
                Local0 = Mid (DerefOf (RefOf (AUB6)), 0x00, S614)
                M600 (Arg0, 0x1D, Local0, BB33)
            }

            Local0 = Mid (DerefOf (PAUS [0x06]), 0x00, S614)
            M600 (Arg0, 0x1E, Local0, BS1B)
            Local0 = Mid (DerefOf (PAUB [0x06]), 0x00, S614)
            M600 (Arg0, 0x1F, Local0, BB33)
            /* Method returns Object */

            Local0 = Mid (M601 (0x02, 0x06), 0x00, S614)
            M600 (Arg0, 0x20, Local0, BS1B)
            Local0 = Mid (M601 (0x03, 0x06), 0x00, S614)
            M600 (Arg0, 0x21, Local0, BB33)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Mid (DerefOf (M602 (0x02, 0x06, 0x01)), 0x00, S614)
                M600 (Arg0, 0x22, Local0, BS1B)
                Local0 = Mid (DerefOf (M602 (0x03, 0x06, 0x01)), 0x00, S614)
                M600 (Arg0, 0x23, Local0, BB33)
            }

            Mid ("This is auxiliary String", 0x00, S614, Local0)
            M600 (Arg0, 0x24, Local0, BS1B)
            Mid (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, 0x00, S614, Local0)
            M600 (Arg0, 0x25, Local0, BB33)
            Mid (AUS6, 0x00, S614, Local0)
            M600 (Arg0, 0x25, Local0, BS1B)
            Mid (AUB6, 0x00, S614, Local0)
            M600 (Arg0, 0x27, Local0, BB33)
            If (Y078)
            {
                Mid (DerefOf (RefOf (AUS6)), 0x00, S614, Local0)
                M600 (Arg0, 0x28, Local0, BS1B)
                Mid (DerefOf (RefOf (AUB6)), 0x00, S614, Local0)
                M600 (Arg0, 0x29, Local0, BB33)
            }

            Mid (DerefOf (PAUS [0x06]), 0x00, S614, Local0)
            M600 (Arg0, 0x2A, Local0, BS1B)
            Mid (DerefOf (PAUB [0x06]), 0x00, S614, Local0)
            M600 (Arg0, 0x2B, Local0, BB33)
            /* Method returns Object */

            Mid (M601 (0x02, 0x06), 0x00, S614, Local0)
            M600 (Arg0, 0x2C, Local0, BS1B)
            Mid (M601 (0x03, 0x06), 0x00, S614, Local0)
            M600 (Arg0, 0x2D, Local0, BB33)
            /* Method returns Reference */

            If (Y500)
            {
                Mid (DerefOf (M602 (0x02, 0x06, 0x01)), 0x00, S614, Local0)
                M600 (Arg0, 0x2E, Local0, BS1B)
                Mid (DerefOf (M602 (0x03, 0x06, 0x01)), 0x00, S614, Local0)
                M600 (Arg0, 0x2F, Local0, BB33)
            }
        }

        Method (M64I, 1, Serialized)
        {
            Name (S605, "FE7CB391D650A284")
            Name (S614, "B")
            /* String to Integer conversion of the String Length operand */

            Local0 = Mid ("This is auxiliary String", 0x00, S605)
            M600 (Arg0, 0x00, Local0, BS1E)
            Local0 = Mid (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, 0x00, S605)
            M600 (Arg0, 0x01, Local0, BB34)
            Local0 = Mid (AUS6, 0x00, S605)
            M600 (Arg0, 0x02, Local0, BS1E)
            Local0 = Mid (AUB6, 0x00, S605)
            M600 (Arg0, 0x03, Local0, BB34)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (AUS6)), 0x00, S605)
                M600 (Arg0, 0x04, Local0, BS1E)
                Local0 = Mid (DerefOf (RefOf (AUB6)), 0x00, S605)
                M600 (Arg0, 0x05, Local0, BB34)
            }

            Local0 = Mid (DerefOf (PAUS [0x06]), 0x00, S605)
            M600 (Arg0, 0x06, Local0, BS1E)
            Local0 = Mid (DerefOf (PAUB [0x06]), 0x00, S605)
            M600 (Arg0, 0x07, Local0, BB34)
            /* Method returns Object */

            Local0 = Mid (M601 (0x02, 0x06), 0x00, S605)
            M600 (Arg0, 0x08, Local0, BS1E)
            Local0 = Mid (M601 (0x03, 0x06), 0x00, S605)
            M600 (Arg0, 0x09, Local0, BB34)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Mid (DerefOf (M602 (0x02, 0x06, 0x01)), 0x00, S605)
                M600 (Arg0, 0x0A, Local0, BS1E)
                Local0 = Mid (DerefOf (M602 (0x03, 0x06, 0x01)), 0x00, S605)
                M600 (Arg0, 0x0B, Local0, BB34)
            }

            Mid ("This is auxiliary String", 0x00, S605, Local0)
            M600 (Arg0, 0x0C, Local0, BS1E)
            Mid (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, 0x00, S605, Local0)
            M600 (Arg0, 0x0D, Local0, BB34)
            Mid (AUS6, 0x00, S605, Local0)
            M600 (Arg0, 0x0E, Local0, BS1E)
            Mid (AUB6, 0x00, S605, Local0)
            M600 (Arg0, 0x0F, Local0, BB34)
            If (Y078)
            {
                Mid (DerefOf (RefOf (AUS6)), 0x00, S605, Local0)
                M600 (Arg0, 0x10, Local0, BS1E)
                Mid (DerefOf (RefOf (AUB6)), 0x00, S605, Local0)
                M600 (Arg0, 0x11, Local0, BB34)
            }

            Mid (DerefOf (PAUS [0x06]), 0x00, S605, Local0)
            M600 (Arg0, 0x12, Local0, BS1E)
            Mid (DerefOf (PAUB [0x06]), 0x00, S605, Local0)
            M600 (Arg0, 0x13, Local0, BB34)
            /* Method returns Object */

            Mid (M601 (0x02, 0x06), 0x00, S605, Local0)
            M600 (Arg0, 0x14, Local0, BS1E)
            Mid (M601 (0x03, 0x06), 0x00, S605, Local0)
            M600 (Arg0, 0x15, Local0, BB34)
            /* Method returns Reference */

            If (Y500)
            {
                Mid (DerefOf (M602 (0x02, 0x06, 0x01)), 0x00, S605, Local0)
                M600 (Arg0, 0x16, Local0, BS1E)
                Mid (DerefOf (M602 (0x03, 0x06, 0x01)), 0x00, S605, Local0)
                M600 (Arg0, 0x17, Local0, BB34)
            }

            /* String to Integer conversion of the both String operands */

            Local0 = Mid ("This is auxiliary String", S614, S605)
            M600 (Arg0, 0x18, Local0, BS1F)
            Local0 = Mid (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, S614, S605)
            M600 (Arg0, 0x19, Local0, BB35)
            Local0 = Mid (AUS6, S614, S605)
            M600 (Arg0, 0x1A, Local0, BS1F)
            Local0 = Mid (AUB6, S614, S605)
            M600 (Arg0, 0x1B, Local0, BB35)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (AUS6)), S614, S605)
                M600 (Arg0, 0x1C, Local0, BS1F)
                Local0 = Mid (DerefOf (RefOf (AUB6)), S614, S605)
                M600 (Arg0, 0x1D, Local0, BB35)
            }

            Local0 = Mid (DerefOf (PAUS [0x06]), S614, S605)
            M600 (Arg0, 0x1E, Local0, BS1F)
            Local0 = Mid (DerefOf (PAUB [0x06]), S614, S605)
            M600 (Arg0, 0x1F, Local0, BB35)
            /* Method returns Object */

            Local0 = Mid (M601 (0x02, 0x06), S614, S605)
            M600 (Arg0, 0x20, Local0, BS1F)
            Local0 = Mid (M601 (0x03, 0x06), S614, S605)
            M600 (Arg0, 0x21, Local0, BB35)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Mid (DerefOf (M602 (0x02, 0x06, 0x01)), S614, S605)
                M600 (Arg0, 0x22, Local0, BS1F)
                Local0 = Mid (DerefOf (M602 (0x03, 0x06, 0x01)), S614, S605)
                M600 (Arg0, 0x23, Local0, BB35)
            }

            Mid ("This is auxiliary String", S614, S605, Local0)
            M600 (Arg0, 0x24, Local0, BS1F)
            Mid (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, S614, S605, Local0)
            M600 (Arg0, 0x25, Local0, BB35)
            Mid (AUS6, S614, S605, Local0)
            M600 (Arg0, 0x26, Local0, BS1F)
            Mid (AUB6, S614, S605, Local0)
            M600 (Arg0, 0x27, Local0, BB35)
            If (Y078)
            {
                Mid (DerefOf (RefOf (AUS6)), S614, S605, Local0)
                M600 (Arg0, 0x28, Local0, BS1F)
                Mid (DerefOf (RefOf (AUB6)), S614, S605, Local0)
                M600 (Arg0, 0x29, Local0, BB35)
            }

            Mid (DerefOf (PAUS [0x06]), S614, S605, Local0)
            M600 (Arg0, 0x2A, Local0, BS1F)
            Mid (DerefOf (PAUB [0x06]), S614, S605, Local0)
            M600 (Arg0, 0x2B, Local0, BB35)
            /* Method returns Object */

            Mid (M601 (0x02, 0x06), S614, S605, Local0)
            M600 (Arg0, 0x2C, Local0, BS1F)
            Mid (M601 (0x03, 0x06), S614, S605, Local0)
            M600 (Arg0, 0x2D, Local0, BB35)
            /* Method returns Reference */

            If (Y500)
            {
                Mid (DerefOf (M602 (0x02, 0x06, 0x01)), S614, S605, Local0)
                M600 (Arg0, 0x2E, Local0, BS1F)
                Mid (DerefOf (M602 (0x03, 0x06, 0x01)), S614, S605, Local0)
                M600 (Arg0, 0x2F, Local0, BB35)
            }
        }

        Method (M32I, 1, Serialized)
        {
            Name (S604, "C179B3FE")
            Name (S614, "B")
            /* String to Integer conversion of the String Length operand */

            Local0 = Mid ("This is auxiliary String", 0x00, S604)
            M600 (Arg0, 0x00, Local0, BS1E)
            Local0 = Mid (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, 0x00, S604)
            M600 (Arg0, 0x01, Local0, BB34)
            Local0 = Mid (AUS6, 0x00, S604)
            M600 (Arg0, 0x02, Local0, BS1E)
            Local0 = Mid (AUB6, 0x00, S604)
            M600 (Arg0, 0x03, Local0, BB34)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (AUS6)), 0x00, S604)
                M600 (Arg0, 0x04, Local0, BS1E)
                Local0 = Mid (DerefOf (RefOf (AUB6)), 0x00, S604)
                M600 (Arg0, 0x05, Local0, BB34)
            }

            Local0 = Mid (DerefOf (PAUS [0x06]), 0x00, S604)
            M600 (Arg0, 0x06, Local0, BS1E)
            Local0 = Mid (DerefOf (PAUB [0x06]), 0x00, S604)
            M600 (Arg0, 0x07, Local0, BB34)
            /* Method returns Object */

            Local0 = Mid (M601 (0x02, 0x06), 0x00, S604)
            M600 (Arg0, 0x08, Local0, BS1E)
            Local0 = Mid (M601 (0x03, 0x06), 0x00, S604)
            M600 (Arg0, 0x09, Local0, BB34)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Mid (DerefOf (M602 (0x02, 0x06, 0x01)), 0x00, S604)
                M600 (Arg0, 0x0A, Local0, BS1E)
                Local0 = Mid (DerefOf (M602 (0x03, 0x06, 0x01)), 0x00, S604)
                M600 (Arg0, 0x0B, Local0, BB34)
            }

            Mid ("This is auxiliary String", 0x00, S604, Local0)
            M600 (Arg0, 0x0C, Local0, BS1E)
            Mid (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, 0x00, S604, Local0)
            M600 (Arg0, 0x0D, Local0, BB34)
            Mid (AUS6, 0x00, S604, Local0)
            M600 (Arg0, 0x0E, Local0, BS1E)
            Mid (AUB6, 0x00, S604, Local0)
            M600 (Arg0, 0x0F, Local0, BB34)
            If (Y078)
            {
                Mid (DerefOf (RefOf (AUS6)), 0x00, S604, Local0)
                M600 (Arg0, 0x10, Local0, BS1E)
                Mid (DerefOf (RefOf (AUB6)), 0x00, S604, Local0)
                M600 (Arg0, 0x11, Local0, BB34)
            }

            Mid (DerefOf (PAUS [0x06]), 0x00, S604, Local0)
            M600 (Arg0, 0x12, Local0, BS1E)
            Mid (DerefOf (PAUB [0x06]), 0x00, S604, Local0)
            M600 (Arg0, 0x13, Local0, BB34)
            /* Method returns Object */

            Mid (M601 (0x02, 0x06), 0x00, S604, Local0)
            M600 (Arg0, 0x14, Local0, BS1E)
            Mid (M601 (0x03, 0x06), 0x00, S604, Local0)
            M600 (Arg0, 0x15, Local0, BB34)
            /* Method returns Reference */

            If (Y500)
            {
                Mid (DerefOf (M602 (0x02, 0x06, 0x01)), 0x00, S604, Local0)
                M600 (Arg0, 0x16, Local0, BS1E)
                Mid (DerefOf (M602 (0x03, 0x06, 0x01)), 0x00, S604, Local0)
                M600 (Arg0, 0x17, Local0, BB34)
            }

            /* String to Integer conversion of the both String operands */

            Local0 = Mid ("This is auxiliary String", S614, S604)
            M600 (Arg0, 0x18, Local0, BS1F)
            Local0 = Mid (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, S614, S604)
            M600 (Arg0, 0x19, Local0, BB35)
            Local0 = Mid (AUS6, S614, S604)
            M600 (Arg0, 0x1A, Local0, BS1F)
            Local0 = Mid (AUB6, S614, S604)
            M600 (Arg0, 0x1B, Local0, BB35)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (AUS6)), S614, S604)
                M600 (Arg0, 0x1C, Local0, BS1F)
                Local0 = Mid (DerefOf (RefOf (AUB6)), S614, S604)
                M600 (Arg0, 0x1D, Local0, BB35)
            }

            Local0 = Mid (DerefOf (PAUS [0x06]), S614, S604)
            M600 (Arg0, 0x1E, Local0, BS1F)
            Local0 = Mid (DerefOf (PAUB [0x06]), S614, S604)
            M600 (Arg0, 0x1F, Local0, BB35)
            /* Method returns Object */

            Local0 = Mid (M601 (0x02, 0x06), S614, S604)
            M600 (Arg0, 0x20, Local0, BS1F)
            Local0 = Mid (M601 (0x03, 0x06), S614, S604)
            M600 (Arg0, 0x21, Local0, BB35)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Mid (DerefOf (M602 (0x02, 0x06, 0x01)), S614, S604)
                M600 (Arg0, 0x22, Local0, BS1F)
                Local0 = Mid (DerefOf (M602 (0x03, 0x06, 0x01)), S614, S604)
                M600 (Arg0, 0x23, Local0, BB35)
            }

            Mid ("This is auxiliary String", S614, S604, Local0)
            M600 (Arg0, 0x24, Local0, BS1F)
            Mid (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, S614, S604, Local0)
            M600 (Arg0, 0x25, Local0, BB35)
            Mid (AUS6, S614, S604, Local0)
            M600 (Arg0, 0x26, Local0, BS1F)
            Mid (AUB6, S614, S604, Local0)
            M600 (Arg0, 0x27, Local0, BB35)
            If (Y078)
            {
                Mid (DerefOf (RefOf (AUS6)), S614, S604, Local0)
                M600 (Arg0, 0x28, Local0, BS1F)
                Mid (DerefOf (RefOf (AUB6)), S614, S604, Local0)
                M600 (Arg0, 0x29, Local0, BB35)
            }

            Mid (DerefOf (PAUS [0x06]), S614, S604, Local0)
            M600 (Arg0, 0x2A, Local0, BS1F)
            Mid (DerefOf (PAUB [0x06]), S614, S604, Local0)
            M600 (Arg0, 0x2B, Local0, BB35)
            /* Method returns Object */

            Mid (M601 (0x02, 0x06), S614, S604, Local0)
            M600 (Arg0, 0x2C, Local0, BS1F)
            Mid (M601 (0x03, 0x06), S614, S604, Local0)
            M600 (Arg0, 0x2D, Local0, BB35)
            /* Method returns Reference */

            If (Y500)
            {
                Mid (DerefOf (M602 (0x02, 0x06, 0x01)), S614, S604, Local0)
                M600 (Arg0, 0x2E, Local0, BS1F)
                Mid (DerefOf (M602 (0x03, 0x06, 0x01)), S614, S604, Local0)
                M600 (Arg0, 0x2F, Local0, BB35)
            }
        }

        /* String to Integer conversion of the String StartIndex */
        /* operand of the Match operator */
        Method (M030, 1, Serialized)
        {
            Name (S614, "B")
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
                    }, MEQ, 0x0A5D, MTR, 0x00, S614)
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
                    }, MEQ, 0x0A5A, MTR, 0x00, S614)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = Match (AUP0, MEQ, 0x0A5D, MTR, 0x00, S614)
            M600 (Arg0, 0x02, Local0, 0x0D)
            Local0 = Match (AUP0, MEQ, 0x0A5A, MTR, 0x00, S614)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = Match (DerefOf (RefOf (AUP0)), MEQ, 0x0A5D, MTR, 0x00, S614)
                M600 (Arg0, 0x04, Local0, 0x0D)
                Local0 = Match (DerefOf (RefOf (AUP0)), MEQ, 0x0A5A, MTR, 0x00, S614)
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = Match (DerefOf (PAUP [0x00]), MEQ, 0x0A5D, MTR, 0x00,
                S614)
            M600 (Arg0, 0x06, Local0, 0x0D)
            Local0 = Match (DerefOf (PAUP [0x00]), MEQ, 0x0A5A, MTR, 0x00,
                S614)
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Object */

            Local0 = Match (M601 (0x04, 0x00), MEQ, 0x0A5D, MTR, 0x00, S614)
            M600 (Arg0, 0x08, Local0, 0x0D)
            Local0 = Match (M601 (0x04, 0x00), MEQ, 0x0A5A, MTR, 0x00, S614)
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Match (DerefOf (M602 (0x04, 0x00, 0x01)), MEQ, 0x0A5D, MTR, 0x00,
                    S614)
                M600 (Arg0, 0x0A, Local0, 0x0D)
                Local0 = Match (DerefOf (M602 (0x04, 0x00, 0x01)), MEQ, 0x0A5A, MTR, 0x00,
                    S614)
                M600 (Arg0, 0x0B, Local0, Ones)
            }
        }

        /*	Method(m64j, 1) */
        /*	Method(m32j, 1) */
        /* String to Integer conversion of the String sole operand */
        /* of the Method execution control operators (Sleep, Stall) */
        Method (M031, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S61B, "63")
            CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
            /* Sleep */

            Local0 = Timer
            Sleep (S601)
            CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
            Local1 = Timer
            Local2 = (Local1 - Local0)
            If ((Local2 < C08C))
            {
                ERR (Arg0, Z088, __LINE__, 0x00, 0x00, Local2, C08C)
            }

            /* Stall */

            Local0 = Timer
            Stall (S61B)
            CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
            Local1 = Timer
            Local2 = (Local1 - Local0)
            If ((Local2 < 0x03DE))
            {
                ERR (Arg0, Z088, __LINE__, 0x00, 0x00, Local2, 0x03DE)
            }
        }

        /* String to Integer conversion of the String TimeoutValue */
        /* (second) operand of the Acquire operator ??? */
        Method (M032, 1, Serialized)
        {
            Name (S601, "0321")
            Mutex (MTX0, 0x00)
            Acquire (MTX0, 0x0000)
            CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
            Local0 = Timer
            /* Compiler allows only Integer constant as TimeoutValue (Bug 1)
             Acquire(MTX0, s601)
             */
            CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
            Local1 = Timer
            Local2 = (Local1 - Local0)
            If ((Local2 < C08C))
            {
                ERR (Arg0, Z088, __LINE__, 0x00, 0x00, Local2, C08C)
            }
        }

        /* String to Integer conversion of the String TimeoutValue */
        /* (second) operand of the Wait operator */
        Method (M033, 1, Serialized)
        {
            Name (S601, "0321")
            Event (EVT0)
            CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
            Local0 = Timer
            Wait (EVT0, S601)
            CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
            Local1 = Timer
            Local2 = (Local1 - Local0)
            If ((Local2 < C08C))
            {
                ERR (Arg0, Z088, __LINE__, 0x00, 0x00, Local2, C08C)
            }
        }

        /* String to Integer conversion of the String value */
        /* of Predicate of the Method execution control statements */
        /* (If, ElseIf, While) */
        Method (M034, 1, Serialized)
        {
            Name (S600, "0")
            Name (S601, "0321")
            Name (S604, "C179B3FE")
            Name (S605, "FE7CB391D650A284")
            Name (IST0, 0x00)
            Method (M001, 0, NotSerialized)
            {
                If (S600)
                {
                    IST0 = 0x00
                }
            }

            Method (M002, 0, NotSerialized)
            {
                If (S601)
                {
                    IST0 = 0x02
                }
            }

            Method (M003, 0, NotSerialized)
            {
                If (S604)
                {
                    IST0 = 0x03
                }
            }

            Method (M004, 0, NotSerialized)
            {
                If (S605)
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
                ElseIf (S600)
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
                ElseIf (S601)
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
                ElseIf (S604)
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
                ElseIf (S605)
                {
                    IST0 = 0x08
                }
            }

            Method (M009, 0, NotSerialized)
            {
                While (S600)
                {
                    IST0 = 0x00
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

        /*	Method(m64k, 1) */
        /*	Method(m32k, 1) */
        /* String to Buffer implicit conversion Cases. */
        /* String to Buffer conversion of the String second operand of */
        /* Logical operators when the first operand is evaluated as Buffer */
        /* (LEqual, LGreater, LGreaterEqual, LLess, LLessEqual, LNotEqual) */
        Method (M035, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S60C, "")
            Name (S60E, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*")
            /* LEqual */

            Local0 = (Buffer (0x05)
                    {
                        "0321"
                    } == S601)
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (Buffer (0x05)
                    {
                         0x30, 0x33, 0x32, 0x31, 0x01                     // 0321.
                    } == S601)
            M600 (Arg0, 0x01, Local0, Zero)
            Local0 = (AUB7 == S601)
            M600 (Arg0, 0x02, Local0, Ones)
            Local0 = (AUB3 == S601)
            M600 (Arg0, 0x03, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB7)) == S601)
                M600 (Arg0, 0x04, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUB3)) == S601)
                M600 (Arg0, 0x05, Local0, Zero)
            }

            Local0 = (DerefOf (PAUB [0x07]) == S601)
            M600 (Arg0, 0x06, Local0, Ones)
            Local0 = (DerefOf (PAUB [0x03]) == S601)
            M600 (Arg0, 0x07, Local0, Zero)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x07) == S601)
            M600 (Arg0, 0x08, Local0, Ones)
            Local0 = (M601 (0x03, 0x03) == S601)
            M600 (Arg0, 0x09, Local0, Zero)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x07, 0x01)) == S601)
                M600 (Arg0, 0x0A, Local0, Ones)
                Local0 = (DerefOf (M602 (0x03, 0x03, 0x01)) == S601)
                M600 (Arg0, 0x0B, Local0, Zero)
            }

            /* LGreater */

            Local0 = (Buffer (0x05)
                    {
                        "0321"
                    } > S601)
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = (Buffer (0x05)
                    {
                         0x30, 0x33, 0x32, 0x31, 0x01                     // 0321.
                    } > S601)
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (Buffer (0x04)
                    {
                         0x30, 0x33, 0x32, 0x31                           // 0321
                    } > S601)
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = (Buffer (0x06)
                    {
                         0x30, 0x33, 0x32, 0x31, 0x00, 0x01               // 0321..
                    } > S601)
            M600 (Arg0, 0x0F, Local0, Ones)
            Local0 = (AUB7 > S601)
            M600 (Arg0, 0x10, Local0, Zero)
            Local0 = (AUB8 > S601)
            M600 (Arg0, 0x11, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB7)) > S601)
                M600 (Arg0, 0x12, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUB8)) > S601)
                M600 (Arg0, 0x13, Local0, Ones)
            }

            Local0 = (DerefOf (PAUB [0x07]) > S601)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (DerefOf (PAUB [0x08]) > S601)
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x07) > S601)
            M600 (Arg0, 0x16, Local0, Zero)
            Local0 = (M601 (0x03, 0x08) > S601)
            M600 (Arg0, 0x17, Local0, Ones)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x07, 0x01)) > S601)
                M600 (Arg0, 0x18, Local0, Zero)
                Local0 = (DerefOf (M602 (0x03, 0x08, 0x01)) > S601)
                M600 (Arg0, 0x19, Local0, Ones)
            }

            /* LGreaterEqual */

            Local0 = (Buffer (0x05)
                        {
                            "0321"
                        } >= S601)
            M600 (Arg0, 0x1A, Local0, Ones)
            Local0 = (Buffer (0x05)
                        {
                             0x30, 0x33, 0x32, 0x31, 0x01                     // 0321.
                        } >= S601)
            M600 (Arg0, 0x1B, Local0, Ones)
            Local0 = (Buffer (0x04)
                        {
                             0x30, 0x33, 0x32, 0x31                           // 0321
                        } >= S601)
            M600 (Arg0, 0x1C, Local0, Zero)
            Local0 = (Buffer (0x06)
                        {
                             0x30, 0x33, 0x32, 0x31, 0x00, 0x01               // 0321..
                        } >= S601)
            M600 (Arg0, 0x1D, Local0, Ones)
            Local0 = (AUB7 >= S601)
            M600 (Arg0, 0x1E, Local0, Ones)
            Local0 = (AUB8 >= S601)
            M600 (Arg0, 0x1F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB7)) >= S601)
                M600 (Arg0, 0x20, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUB8)) >= S601)
                M600 (Arg0, 0x21, Local0, Ones)
            }

            Local0 = (DerefOf (PAUB [0x07]) >= S601)
            M600 (Arg0, 0x22, Local0, Ones)
            Local0 = (DerefOf (PAUB [0x08]) >= S601)
            M600 (Arg0, 0x23, Local0, Ones)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x07) >= S601)
            M600 (Arg0, 0x24, Local0, Ones)
            Local0 = (M601 (0x03, 0x08) >= S601)
            M600 (Arg0, 0x25, Local0, Ones)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x07, 0x01)) >= S601)
                M600 (Arg0, 0x26, Local0, Ones)
                Local0 = (DerefOf (M602 (0x03, 0x08, 0x01)) >= S601)
                M600 (Arg0, 0x27, Local0, Ones)
            }

            /* LLess */

            Local0 = (Buffer (0x05)
                    {
                        "0321"
                    } < S601)
            M600 (Arg0, 0x28, Local0, Zero)
            Local0 = (Buffer (0x05)
                    {
                         0x30, 0x33, 0x32, 0x31, 0x01                     // 0321.
                    } < S601)
            M600 (Arg0, 0x29, Local0, Zero)
            Local0 = (Buffer (0x04)
                    {
                         0x30, 0x33, 0x32, 0x31                           // 0321
                    } < S601)
            M600 (Arg0, 0x2A, Local0, Ones)
            Local0 = (Buffer (0x06)
                    {
                         0x30, 0x33, 0x32, 0x31, 0x00, 0x01               // 0321..
                    } < S601)
            M600 (Arg0, 0x2B, Local0, Zero)
            Local0 = (AUB7 < S601)
            M600 (Arg0, 0x2C, Local0, Zero)
            Local0 = (AUB8 < S601)
            M600 (Arg0, 0x2D, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB7)) < S601)
                M600 (Arg0, 0x2E, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUB8)) < S601)
                M600 (Arg0, 0x2F, Local0, Zero)
            }

            Local0 = (DerefOf (PAUB [0x07]) < S601)
            M600 (Arg0, 0x30, Local0, Zero)
            Local0 = (DerefOf (PAUB [0x08]) < S601)
            M600 (Arg0, 0x31, Local0, Zero)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x07) < S601)
            M600 (Arg0, 0x32, Local0, Zero)
            Local0 = (M601 (0x03, 0x08) < S601)
            M600 (Arg0, 0x33, Local0, Zero)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x07, 0x01)) < S601)
                M600 (Arg0, 0x34, Local0, Zero)
                Local0 = (DerefOf (M602 (0x03, 0x08, 0x01)) < S601)
                M600 (Arg0, 0x35, Local0, Zero)
            }

            /* LLessEqual */

            Local0 = (Buffer (0x05)
                        {
                            "0321"
                        } <= S601)
            M600 (Arg0, 0x36, Local0, Ones)
            Local0 = (Buffer (0x05)
                        {
                             0x30, 0x33, 0x32, 0x31, 0x01                     // 0321.
                        } <= S601)
            M600 (Arg0, 0x37, Local0, Zero)
            Local0 = (Buffer (0x04)
                        {
                             0x30, 0x33, 0x32, 0x31                           // 0321
                        } <= S601)
            M600 (Arg0, 0x38, Local0, Ones)
            Local0 = (Buffer (0x06)
                        {
                             0x30, 0x33, 0x32, 0x31, 0x00, 0x01               // 0321..
                        } <= S601)
            M600 (Arg0, 0x39, Local0, Zero)
            Local0 = (AUB7 <= S601)
            M600 (Arg0, 0x3A, Local0, Ones)
            Local0 = (AUB8 <= S601)
            M600 (Arg0, 0x3B, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB7)) <= S601)
                M600 (Arg0, 0x3C, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUB8)) <= S601)
                M600 (Arg0, 0x3D, Local0, Zero)
            }

            Local0 = (DerefOf (PAUB [0x07]) <= S601)
            M600 (Arg0, 0x3E, Local0, Ones)
            Local0 = (DerefOf (PAUB [0x08]) <= S601)
            M600 (Arg0, 0x3F, Local0, Zero)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x07) <= S601)
            M600 (Arg0, 0x40, Local0, Ones)
            Local0 = (M601 (0x03, 0x08) <= S601)
            M600 (Arg0, 0x41, Local0, Zero)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x07, 0x01)) <= S601)
                M600 (Arg0, 0x42, Local0, Ones)
                Local0 = (DerefOf (M602 (0x03, 0x08, 0x01)) <= S601)
                M600 (Arg0, 0x43, Local0, Zero)
            }

            /* LNotEqual */

            Local0 = (Buffer (0x05)
                        {
                            "0321"
                        } != S601)
            M600 (Arg0, 0x44, Local0, Zero)
            Local0 = (Buffer (0x05)
                        {
                             0x30, 0x33, 0x32, 0x31, 0x01                     // 0321.
                        } != S601)
            M600 (Arg0, 0x45, Local0, Ones)
            Local0 = (Buffer (0x04)
                        {
                             0x30, 0x33, 0x32, 0x31                           // 0321
                        } != S601)
            M600 (Arg0, 0x46, Local0, Ones)
            Local0 = (Buffer (0x06)
                        {
                             0x30, 0x33, 0x32, 0x31, 0x00, 0x01               // 0321..
                        } != S601)
            M600 (Arg0, 0x47, Local0, Ones)
            Local0 = (AUB7 != S601)
            M600 (Arg0, 0x48, Local0, Zero)
            Local0 = (AUB8 != S601)
            M600 (Arg0, 0x49, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUB7)) != S601)
                M600 (Arg0, 0x4A, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUB8)) != S601)
                M600 (Arg0, 0x4B, Local0, Ones)
            }

            Local0 = (DerefOf (PAUB [0x07]) != S601)
            M600 (Arg0, 0x4C, Local0, Zero)
            Local0 = (DerefOf (PAUB [0x08]) != S601)
            M600 (Arg0, 0x4D, Local0, Ones)
            /* Method returns Buffer */

            Local0 = (M601 (0x03, 0x07) != S601)
            M600 (Arg0, 0x4E, Local0, Zero)
            Local0 = (M601 (0x03, 0x08) != S601)
            M600 (Arg0, 0x4F, Local0, Ones)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x03, 0x07, 0x01)) != S601)
                M600 (Arg0, 0x50, Local0, Zero)
                Local0 = (DerefOf (M602 (0x03, 0x08, 0x01)) != S601)
                M600 (Arg0, 0x51, Local0, Ones)
            }

            /* Boundary Cases */

            Local0 = (Buffer (0x01)
                    {
                         0x00                                             // .
                    } == S60C)
            M600 (Arg0, 0x52, Local0, Ones)
            Local0 = (Buffer (0x01)
                    {
                         0x01                                             // .
                    } == S60C)
            M600 (Arg0, 0x53, Local0, Zero)
            Local0 = (Buffer (0x01)
                    {
                         0x00                                             // .
                    } > S60C)
            M600 (Arg0, 0x54, Local0, Zero)
            Local0 = (Buffer (0x01)
                    {
                         0x01                                             // .
                    } > S60C)
            M600 (Arg0, 0x55, Local0, Ones)
            Local0 = (Buffer (0x01)
                        {
                             0x00                                             // .
                        } >= S60C)
            M600 (Arg0, 0x56, Local0, Ones)
            Local0 = (Buffer (0x01)
                    {
                         0x01                                             // .
                    } > S60C)
            M600 (Arg0, 0x57, Local0, Ones)
            Local0 = (Buffer (0x01)
                    {
                         0x00                                             // .
                    } < S60C)
            M600 (Arg0, 0x58, Local0, Zero)
            Local0 = (Buffer (0x01)
                    {
                         0x01                                             // .
                    } < S60C)
            M600 (Arg0, 0x59, Local0, Zero)
            Local0 = (Buffer (0x01)
                        {
                             0x00                                             // .
                        } <= S60C)
            M600 (Arg0, 0x5A, Local0, Ones)
            Local0 = (Buffer (0x01)
                        {
                             0x01                                             // .
                        } <= S60C)
            M600 (Arg0, 0x5B, Local0, Zero)
            Local0 = (Buffer (0x01)
                        {
                             0x00                                             // .
                        } != S60C)
            M600 (Arg0, 0x5C, Local0, Zero)
            Local0 = (Buffer (0x01)
                        {
                             0x01                                             // .
                        } != S60C)
            M600 (Arg0, 0x5D, Local0, Ones)
            Local0 = (Buffer (0xC9)
                    {
                        "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*"
                    } == S60E)
            M600 (Arg0, 0x5E, Local0, Ones)
            Local0 = (Buffer (0xC9)
                    {
                        /* 0000 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
                        /* 0008 */  0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30,  // )*+,-./0
                        /* 0010 */  0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38,  // 12345678
                        /* 0018 */  0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40,  // 9:;<=>?@
                        /* 0020 */  0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48,  // ABCDEFGH
                        /* 0028 */  0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50,  // IJKLMNOP
                        /* 0030 */  0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58,  // QRSTUVWX
                        /* 0038 */  0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, 0x60,  // YZ[\]^_`
                        /* 0040 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68,  // abcdefgh
                        /* 0048 */  0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70,  // ijklmnop
                        /* 0050 */  0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78,  // qrstuvwx
                        /* 0058 */  0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x20, 0x21,  // yz{|}~ !
                        /* 0060 */  0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29,  // "#$%&'()
                        /* 0068 */  0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30, 0x31,  // *+,-./01
                        /* 0070 */  0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39,  // 23456789
                        /* 0078 */  0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40, 0x41,  // :;<=>?@A
                        /* 0080 */  0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49,  // BCDEFGHI
                        /* 0088 */  0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51,  // JKLMNOPQ
                        /* 0090 */  0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59,  // RSTUVWXY
                        /* 0098 */  0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, 0x60, 0x61,  // Z[\]^_`a
                        /* 00A0 */  0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69,  // bcdefghi
                        /* 00A8 */  0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71,  // jklmnopq
                        /* 00B0 */  0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79,  // rstuvwxy
                        /* 00B8 */  0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x20, 0x21, 0x22,  // z{|}~ !"
                        /* 00C0 */  0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2A,  // #$%&'()*
                        /* 00C8 */  0x01                                             // .
                    } == S60E)
            M600 (Arg0, 0x5F, Local0, Zero)
            Local0 = (Buffer (0xC9)
                    {
                        "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*"
                    } > S60E)
            M600 (Arg0, 0x60, Local0, Zero)
            Local0 = (Buffer (0xC9)
                    {
                        /* 0000 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
                        /* 0008 */  0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30,  // )*+,-./0
                        /* 0010 */  0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38,  // 12345678
                        /* 0018 */  0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40,  // 9:;<=>?@
                        /* 0020 */  0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48,  // ABCDEFGH
                        /* 0028 */  0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50,  // IJKLMNOP
                        /* 0030 */  0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58,  // QRSTUVWX
                        /* 0038 */  0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, 0x60,  // YZ[\]^_`
                        /* 0040 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68,  // abcdefgh
                        /* 0048 */  0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70,  // ijklmnop
                        /* 0050 */  0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78,  // qrstuvwx
                        /* 0058 */  0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x20, 0x21,  // yz{|}~ !
                        /* 0060 */  0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29,  // "#$%&'()
                        /* 0068 */  0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30, 0x31,  // *+,-./01
                        /* 0070 */  0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39,  // 23456789
                        /* 0078 */  0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40, 0x41,  // :;<=>?@A
                        /* 0080 */  0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49,  // BCDEFGHI
                        /* 0088 */  0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51,  // JKLMNOPQ
                        /* 0090 */  0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59,  // RSTUVWXY
                        /* 0098 */  0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, 0x60, 0x61,  // Z[\]^_`a
                        /* 00A0 */  0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69,  // bcdefghi
                        /* 00A8 */  0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71,  // jklmnopq
                        /* 00B0 */  0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79,  // rstuvwxy
                        /* 00B8 */  0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x20, 0x21, 0x22,  // z{|}~ !"
                        /* 00C0 */  0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2A,  // #$%&'()*
                        /* 00C8 */  0x01                                             // .
                    } > S60E)
            M600 (Arg0, 0x61, Local0, Ones)
            Local0 = (Buffer (0xC9)
                        {
                            "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*"
                        } >= S60E)
            M600 (Arg0, 0x62, Local0, Ones)
            Local0 = (Buffer (0xC9)
                    {
                        /* 0000 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
                        /* 0008 */  0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30,  // )*+,-./0
                        /* 0010 */  0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38,  // 12345678
                        /* 0018 */  0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40,  // 9:;<=>?@
                        /* 0020 */  0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48,  // ABCDEFGH
                        /* 0028 */  0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50,  // IJKLMNOP
                        /* 0030 */  0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58,  // QRSTUVWX
                        /* 0038 */  0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, 0x60,  // YZ[\]^_`
                        /* 0040 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68,  // abcdefgh
                        /* 0048 */  0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70,  // ijklmnop
                        /* 0050 */  0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78,  // qrstuvwx
                        /* 0058 */  0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x20, 0x21,  // yz{|}~ !
                        /* 0060 */  0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29,  // "#$%&'()
                        /* 0068 */  0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30, 0x31,  // *+,-./01
                        /* 0070 */  0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39,  // 23456789
                        /* 0078 */  0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40, 0x41,  // :;<=>?@A
                        /* 0080 */  0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49,  // BCDEFGHI
                        /* 0088 */  0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51,  // JKLMNOPQ
                        /* 0090 */  0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59,  // RSTUVWXY
                        /* 0098 */  0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, 0x60, 0x61,  // Z[\]^_`a
                        /* 00A0 */  0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69,  // bcdefghi
                        /* 00A8 */  0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71,  // jklmnopq
                        /* 00B0 */  0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79,  // rstuvwxy
                        /* 00B8 */  0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x20, 0x21, 0x22,  // z{|}~ !"
                        /* 00C0 */  0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2A,  // #$%&'()*
                        /* 00C8 */  0x01                                             // .
                    } > S60E)
            M600 (Arg0, 0x63, Local0, Ones)
            Local0 = (Buffer (0xC9)
                    {
                        "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*"
                    } < S60E)
            M600 (Arg0, 0x64, Local0, Zero)
            Local0 = (Buffer (0xC9)
                    {
                        /* 0000 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
                        /* 0008 */  0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30,  // )*+,-./0
                        /* 0010 */  0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38,  // 12345678
                        /* 0018 */  0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40,  // 9:;<=>?@
                        /* 0020 */  0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48,  // ABCDEFGH
                        /* 0028 */  0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50,  // IJKLMNOP
                        /* 0030 */  0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58,  // QRSTUVWX
                        /* 0038 */  0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, 0x60,  // YZ[\]^_`
                        /* 0040 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68,  // abcdefgh
                        /* 0048 */  0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70,  // ijklmnop
                        /* 0050 */  0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78,  // qrstuvwx
                        /* 0058 */  0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x20, 0x21,  // yz{|}~ !
                        /* 0060 */  0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29,  // "#$%&'()
                        /* 0068 */  0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30, 0x31,  // *+,-./01
                        /* 0070 */  0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39,  // 23456789
                        /* 0078 */  0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40, 0x41,  // :;<=>?@A
                        /* 0080 */  0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49,  // BCDEFGHI
                        /* 0088 */  0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51,  // JKLMNOPQ
                        /* 0090 */  0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59,  // RSTUVWXY
                        /* 0098 */  0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, 0x60, 0x61,  // Z[\]^_`a
                        /* 00A0 */  0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69,  // bcdefghi
                        /* 00A8 */  0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71,  // jklmnopq
                        /* 00B0 */  0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79,  // rstuvwxy
                        /* 00B8 */  0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x20, 0x21, 0x22,  // z{|}~ !"
                        /* 00C0 */  0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2A,  // #$%&'()*
                        /* 00C8 */  0x01                                             // .
                    } < S60E)
            M600 (Arg0, 0x65, Local0, Zero)
            Local0 = (Buffer (0xC9)
                        {
                            "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*"
                        } <= S60E)
            M600 (Arg0, 0x66, Local0, Ones)
            Local0 = (Buffer (0xC9)
                        {
                            /* 0000 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
                            /* 0008 */  0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30,  // )*+,-./0
                            /* 0010 */  0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38,  // 12345678
                            /* 0018 */  0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40,  // 9:;<=>?@
                            /* 0020 */  0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48,  // ABCDEFGH
                            /* 0028 */  0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50,  // IJKLMNOP
                            /* 0030 */  0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58,  // QRSTUVWX
                            /* 0038 */  0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, 0x60,  // YZ[\]^_`
                            /* 0040 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68,  // abcdefgh
                            /* 0048 */  0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70,  // ijklmnop
                            /* 0050 */  0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78,  // qrstuvwx
                            /* 0058 */  0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x20, 0x21,  // yz{|}~ !
                            /* 0060 */  0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29,  // "#$%&'()
                            /* 0068 */  0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30, 0x31,  // *+,-./01
                            /* 0070 */  0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39,  // 23456789
                            /* 0078 */  0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40, 0x41,  // :;<=>?@A
                            /* 0080 */  0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49,  // BCDEFGHI
                            /* 0088 */  0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51,  // JKLMNOPQ
                            /* 0090 */  0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59,  // RSTUVWXY
                            /* 0098 */  0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, 0x60, 0x61,  // Z[\]^_`a
                            /* 00A0 */  0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69,  // bcdefghi
                            /* 00A8 */  0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71,  // jklmnopq
                            /* 00B0 */  0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79,  // rstuvwxy
                            /* 00B8 */  0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x20, 0x21, 0x22,  // z{|}~ !"
                            /* 00C0 */  0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2A,  // #$%&'()*
                            /* 00C8 */  0x01                                             // .
                        } <= S60E)
            M600 (Arg0, 0x67, Local0, Zero)
            Local0 = (Buffer (0xC9)
                        {
                            "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*"
                        } != S60E)
            M600 (Arg0, 0x68, Local0, Zero)
            Local0 = (Buffer (0xC9)
                        {
                            /* 0000 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
                            /* 0008 */  0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30,  // )*+,-./0
                            /* 0010 */  0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38,  // 12345678
                            /* 0018 */  0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40,  // 9:;<=>?@
                            /* 0020 */  0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48,  // ABCDEFGH
                            /* 0028 */  0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50,  // IJKLMNOP
                            /* 0030 */  0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58,  // QRSTUVWX
                            /* 0038 */  0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, 0x60,  // YZ[\]^_`
                            /* 0040 */  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68,  // abcdefgh
                            /* 0048 */  0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70,  // ijklmnop
                            /* 0050 */  0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78,  // qrstuvwx
                            /* 0058 */  0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x20, 0x21,  // yz{|}~ !
                            /* 0060 */  0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29,  // "#$%&'()
                            /* 0068 */  0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30, 0x31,  // *+,-./01
                            /* 0070 */  0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39,  // 23456789
                            /* 0078 */  0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40, 0x41,  // :;<=>?@A
                            /* 0080 */  0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49,  // BCDEFGHI
                            /* 0088 */  0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51,  // JKLMNOPQ
                            /* 0090 */  0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59,  // RSTUVWXY
                            /* 0098 */  0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, 0x60, 0x61,  // Z[\]^_`a
                            /* 00A0 */  0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69,  // bcdefghi
                            /* 00A8 */  0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71,  // jklmnopq
                            /* 00B0 */  0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79,  // rstuvwxy
                            /* 00B8 */  0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x20, 0x21, 0x22,  // z{|}~ !"
                            /* 00C0 */  0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2A,  // #$%&'()*
                            /* 00C8 */  0x01                                             // .
                        } != S60E)
            M600 (Arg0, 0x69, Local0, Ones)
        }

        /* String to Buffer conversion of the String second operand of */
        /* Concatenate operator when the first operand is evaluated as Buffer */
        Method (M036, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S60C, "")
            Name (S60E, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*")
            Local0 = Concatenate (Buffer (0x01)
                    {
                         0x5A                                             // Z
                    }, S601)
            M600 (Arg0, 0x00, Local0, BB29)
            Local0 = Concatenate (Buffer (0x02)
                    {
                        "Z"
                    }, S601)
            M600 (Arg0, 0x01, Local0, BB2A)
            Local0 = Concatenate (AUB0, S601)
            M600 (Arg0, 0x02, Local0, BB29)
            Local0 = Concatenate (AUB1, S601)
            M600 (Arg0, 0x03, Local0, BB2A)
            If (Y078)
            {
                Local0 = Concatenate (DerefOf (RefOf (AUB0)), S601)
                M600 (Arg0, 0x04, Local0, BB29)
                Local0 = Concatenate (DerefOf (RefOf (AUB1)), S601)
                M600 (Arg0, 0x05, Local0, BB2A)
            }

            Local0 = Concatenate (DerefOf (PAUB [0x00]), S601)
            M600 (Arg0, 0x06, Local0, BB29)
            Local0 = Concatenate (DerefOf (PAUB [0x01]), S601)
            M600 (Arg0, 0x07, Local0, BB2A)
            /* Method returns Buffer */

            Local0 = Concatenate (M601 (0x03, 0x00), S601)
            M600 (Arg0, 0x08, Local0, BB29)
            Local0 = Concatenate (M601 (0x03, 0x01), S601)
            M600 (Arg0, 0x09, Local0, BB2A)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = Concatenate (DerefOf (M602 (0x03, 0x00, 0x01)), S601)
                M600 (Arg0, 0x0A, Local0, BB29)
                Local0 = Concatenate (DerefOf (M602 (0x03, 0x01, 0x01)), S601)
                M600 (Arg0, 0x0B, Local0, BB2A)
            }

            Concatenate (Buffer (0x01)
                {
                     0x5A                                             // Z
                }, S601, Local0)
            M600 (Arg0, 0x0C, Local0, BB29)
            Concatenate (Buffer (0x02)
                {
                    "Z"
                }, S601, Local0)
            M600 (Arg0, 0x0D, Local0, BB2A)
            Concatenate (AUB0, S601, Local0)
            M600 (Arg0, 0x0E, Local0, BB29)
            Concatenate (AUB1, S601, Local0)
            M600 (Arg0, 0x0F, Local0, BB2A)
            If (Y078)
            {
                Concatenate (DerefOf (RefOf (AUB0)), S601, Local0)
                M600 (Arg0, 0x10, Local0, BB29)
                Concatenate (DerefOf (RefOf (AUB1)), S601, Local0)
                M600 (Arg0, 0x11, Local0, BB2A)
            }

            Concatenate (DerefOf (PAUB [0x00]), S601, Local0)
            M600 (Arg0, 0x12, Local0, BB29)
            Concatenate (DerefOf (PAUB [0x01]), S601, Local0)
            M600 (Arg0, 0x13, Local0, BB2A)
            /* Method returns Buffer */

            Concatenate (M601 (0x03, 0x00), S601, Local0)
            M600 (Arg0, 0x14, Local0, BB29)
            Concatenate (M601 (0x03, 0x01), S601, Local0)
            M600 (Arg0, 0x15, Local0, BB2A)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Concatenate (DerefOf (M602 (0x03, 0x00, 0x01)), S601, Local0)
                M600 (Arg0, 0x16, Local0, BB29)
                Concatenate (DerefOf (M602 (0x03, 0x01, 0x01)), S601, Local0)
                M600 (Arg0, 0x17, Local0, BB2A)
            }

            /* Boundary Cases */

            Local0 = Concatenate (Buffer (0x01)
                    {
                         0x5A                                             // Z
                    }, S60C)
            M600 (Arg0, 0x18, Local0, BB2B)
            Local0 = Concatenate (Buffer (0x02)
                    {
                        "Z"
                    }, S60C)
            M600 (Arg0, 0x19, Local0, BB2C)
            Local1 = 0x00
            Local0 = Concatenate (Buffer (Local1){}, S60E)
            M600 (Arg0, 0x1A, Local0, BB2D)
        }

        /* String to Buffer conversion of the String Source operand of */
        /* ToString operator (has a visual effect in shortening of the */
        /* String taken the null character, that is impossible to show */
        /* with an immediate String constant). */
        Method (M037, 1, Serialized)
        {
            Name (S601, "0321")
            Name (S60C, "")
            Name (S60E, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*")
            Local0 = ToString (S601, Ones)
            M600 (Arg0, 0x00, Local0, BS20)
            Local0 = ToString (S601, 0x03)
            M600 (Arg0, 0x01, Local0, BS21)
            Local0 = ToString (S601, AUI0)
            M600 (Arg0, 0x02, Local0, BS20)
            Local0 = ToString (S601, AUI7)
            M600 (Arg0, 0x03, Local0, BS21)
            If (Y078)
            {
                Local0 = ToString (S601, DerefOf (RefOf (AUI0)))
                M600 (Arg0, 0x04, Local0, BS20)
                Local0 = ToString (S601, DerefOf (RefOf (AUI7)))
                M600 (Arg0, 0x05, Local0, BS21)
            }

            Local0 = ToString (S601, DerefOf (PAUI [0x00]))
            M600 (Arg0, 0x06, Local0, BS20)
            Local0 = ToString (S601, DerefOf (PAUI [0x07]))
            M600 (Arg0, 0x07, Local0, BS21)
            /* Method returns Length parameter */

            Local0 = ToString (S601, M601 (0x01, 0x00))
            M600 (Arg0, 0x08, Local0, BS20)
            Local0 = ToString (S601, M601 (0x01, 0x07))
            M600 (Arg0, 0x09, Local0, BS21)
            /* Method returns Reference to Length parameter */

            If (Y500)
            {
                Local0 = ToString (S601, DerefOf (M601 (0x01, 0x00)))
                M600 (Arg0, 0x0A, Local0, BS20)
                Local0 = ToString (S601, DerefOf (M601 (0x01, 0x07)))
                M600 (Arg0, 0x0B, Local0, BS21)
            }

            ToString (S601, Ones, Local0)
            M600 (Arg0, 0x0C, Local0, BS20)
            ToString (S601, 0x03, Local0)
            M600 (Arg0, 0x0D, Local0, BS21)
            ToString (S601, AUI0, Local0)
            M600 (Arg0, 0x0E, Local0, BS20)
            ToString (S601, AUI7, Local0)
            M600 (Arg0, 0x0F, Local0, BS21)
            If (Y078)
            {
                ToString (S601, DerefOf (RefOf (AUI0)), Local0)
                M600 (Arg0, 0x10, Local0, BS20)
                ToString (S601, DerefOf (RefOf (AUI7)), Local0)
                M600 (Arg0, 0x11, Local0, BS21)
            }

            ToString (S601, DerefOf (PAUI [0x00]), Local0)
            M600 (Arg0, 0x12, Local0, BS20)
            ToString (S601, DerefOf (PAUI [0x07]), Local0)
            M600 (Arg0, 0x13, Local0, BS21)
            /* Method returns Length parameter */

            ToString (S601, M601 (0x01, 0x00), Local0)
            M600 (Arg0, 0x14, Local0, BS20)
            ToString (S601, M601 (0x01, 0x07), Local0)
            M600 (Arg0, 0x15, Local0, BS21)
            /* Method returns Reference to Length parameter */

            If (Y500)
            {
                ToString (S601, DerefOf (M601 (0x01, 0x00)), Local0)
                M600 (Arg0, 0x16, Local0, BS20)
                ToString (S601, DerefOf (M601 (0x01, 0x07)), Local0)
                M600 (Arg0, 0x17, Local0, BS21)
            }

            /* Boundary Cases */

            Local0 = ToString (S60C, Ones)
            M600 (Arg0, 0x18, Local0, BS22)
            Local0 = ToString (S60C, 0x03)
            M600 (Arg0, 0x19, Local0, BS22)
            Local0 = ToString (S60E, Ones)
            M600 (Arg0, 0x1A, Local0, BS23)
            Local0 = ToString (S60E, 0x03)
            M600 (Arg0, 0x1B, Local0, BS24)
        }

        /*	Method(m038, 1) */
        /*	Method(m039, 1) */
        /* Buffer to Integer implicit conversion Cases. */
        /* Buffer to Integer conversion of the Buffer sole operand */
        /* of the 1-parameter Integer arithmetic operators */
        /* (Decrement, Increment, FindSetLeftBit, FindSetRightBit, Not) */
        Method (M64L, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Decrement */

            If (Y501)
            {
                Local0 = B606--
                M600 (Arg0, 0x00, Local0, BI12)
                Local0 = B60A--
                M600 (Arg0, 0x01, Local0, BI16)
            }

            /* Increment */

            If (Y501)
            {
                Local0 = B606++
                M600 (Arg0, 0x02, Local0, BI13)
                Local0 = B60A++
                M600 (Arg0, 0x03, Local0, BI17)
            }

            /* FindSetLeftBit */

            Local0 = FindSetLeftBit (B606)
            M600 (Arg0, 0x04, Local0, 0x0A)
            Local0 = FindSetLeftBit (B60A)
            M600 (Arg0, 0x05, Local0, 0x40)
            /* FindSetRightBit */

            Local0 = FindSetRightBit (B606)
            M600 (Arg0, 0x06, Local0, 0x01)
            Local0 = FindSetRightBit (B60A)
            M600 (Arg0, 0x07, Local0, 0x03)
            /* Not */

            Store (~B606, Local0)
            M600 (Arg0, 0x08, Local0, 0xFFFFFFFFFFFFFCDE)
            Store (~B60A, Local0)
            M600 (Arg0, 0x09, Local0, 0x01834C6E29AF5D7B)
        }

        Method (M32L, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Decrement */

            If (Y501)
            {
                Local0 = B606--
                M600 (Arg0, 0x00, Local0, BI12)
                Local0 = B60A--
                M600 (Arg0, 0x01, Local0, BI18)
            }

            /* Increment */

            If (Y501)
            {
                Local0 = B606++
                M600 (Arg0, 0x02, Local0, BI13)
                Local0 = B60A++
                M600 (Arg0, 0x03, Local0, BI19)
            }

            /* FindSetLeftBit */

            Local0 = FindSetLeftBit (B606)
            M600 (Arg0, 0x04, Local0, 0x0A)
            Local0 = FindSetLeftBit (B60A)
            M600 (Arg0, 0x05, Local0, 0x20)
            /* FindSetRightBit */

            Local0 = FindSetRightBit (B606)
            M600 (Arg0, 0x06, Local0, 0x01)
            Local0 = FindSetRightBit (B60A)
            M600 (Arg0, 0x07, Local0, 0x03)
            /* Not */

            Store (~B606, Local0)
            M600 (Arg0, 0x08, Local0, 0xFFFFFCDE)
            Store (~B60A, Local0)
            M600 (Arg0, 0x09, Local0, 0x29AF5D7B)
        }

        /* Buffer to Integer conversion of the Buffer sole operand */
        /* of the LNot Logical Integer operator */
        Method (M03A, 1, Serialized)
        {
            Name (B600, Buffer (0x01)
            {
                 0x00                                             // .
            })
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            Local0 = !B600
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = !B606
            M600 (Arg0, 0x01, Local0, Zero)
            If (F64)
            {
                Local0 = !B60A
                M600 (Arg0, 0x02, Local0, Zero)
            }
            Else
            {
                Local0 = !B60A
                M600 (Arg0, 0x03, Local0, Zero)
            }
        }

        /* Buffer to Integer conversion of the Buffer sole operand */
        /* of the FromBCD and ToBCD conversion operators */
        Method (M64M, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60F, Buffer (0x08)
            {
                 0x01, 0x89, 0x67, 0x45, 0x23, 0x01, 0x89, 0x37   // ..gE#..7
            })
            Name (B610, Buffer (0x07)
            {
                 0x35, 0xEC, 0xE9, 0x2E, 0x16, 0x76, 0x0D         // 5....v.
            })
            /* FromBCD */

            Local0 = FromBCD (B606)
            M600 (Arg0, 0x02, Local0, 0x0141)
            Local0 = FromBCD (B60F)
            M600 (Arg0, 0x03, Local0, 0x000D76162EE9EC35)
            FromBCD (B606, Local0)
            M600 (Arg0, 0x02, Local0, 0x0141)
            FromBCD (B60F, Local0)
            M600 (Arg0, 0x03, Local0, 0x000D76162EE9EC35)
            /* ToBCD */

            Local0 = ToBCD (B606)
            M600 (Arg0, 0x04, Local0, 0x0801)
            /* ??? No error of iASL on constant folding */

            Local0 = ToBCD (B610)
            M600 (Arg0, 0x05, Local0, 0x3789012345678901)
            ToBCD (B606, Local0)
            M600 (Arg0, 0x04, Local0, 0x0801)
            ToBCD (B610, Local0)
            M600 (Arg0, 0x05, Local0, 0x3789012345678901)
        }

        Method (M32M, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B611, Buffer (0x04)
            {
                 0x56, 0x34, 0x12, 0x90                           // V4..
            })
            Name (B612, Buffer (0x04)
            {
                 0xC0, 0x2C, 0x5F, 0x05                           // .,_.
            })
            /* FromBCD */

            Local0 = FromBCD (B606)
            M600 (Arg0, 0x02, Local0, 0x0141)
            Local0 = FromBCD (B611)
            M600 (Arg0, 0x03, Local0, 0x055F2CC0)
            FromBCD (B606, Local0)
            M600 (Arg0, 0x02, Local0, 0x0141)
            FromBCD (B611, Local0)
            M600 (Arg0, 0x03, Local0, 0x055F2CC0)
            /* ToBCD */

            Local0 = ToBCD (B606)
            M600 (Arg0, 0x04, Local0, 0x0801)
            Local0 = ToBCD (B612)
            M600 (Arg0, 0x05, Local0, 0x90123456)
            ToBCD (B606, Local0)
            M600 (Arg0, 0x04, Local0, 0x0801)
            ToBCD (B612, Local0)
            M600 (Arg0, 0x05, Local0, 0x90123456)
        }

        /* Buffer to Integer conversion of each Buffer operand */
        /* of the 2-parameter Integer arithmetic operators */
        /* Add, And, Divide, Mod, Multiply, NAnd, NOr, Or, */
        /* ShiftLeft, ShiftRight, Subtract, Xor */
        /* Add, common 32-bit/64-bit test */
        Method (M03B, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            /* Conversion of the first operand */

            Store ((B606 + 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((B606 + 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x0322)
            Store ((B606 + AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((B606 + AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x0322)
            If (Y078)
            {
                Store ((B606 + DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((B606 + DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x0322)
            }

            Store ((B606 + DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((B606 + DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x0322)
            /* Method returns Integer */

            Store ((B606 + M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((B606 + M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x0322)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B606 + DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((B606 + DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x0322)
            }

            Local0 = (B606 + 0x00)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (B606 + 0x01)
            M600 (Arg0, 0x0D, Local0, 0x0322)
            Local0 = (B606 + AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (B606 + AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x0322)
            If (Y078)
            {
                Local0 = (B606 + DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (B606 + DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x0322)
            }

            Local0 = (B606 + DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (B606 + DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x0322)
            /* Method returns Integer */

            Local0 = (B606 + M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (B606 + M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x0322)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B606 + DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (B606 + DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x0322)
            }

            /* Conversion of the second operand */

            Store ((0x00 + B606), Local0)
            M600 (Arg0, 0x18, Local0, 0x0321)
            Store ((0x01 + B606), Local0)
            M600 (Arg0, 0x19, Local0, 0x0322)
            Store ((AUI5 + B606), Local0)
            M600 (Arg0, 0x1A, Local0, 0x0321)
            Store ((AUI6 + B606), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0322)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) + B606), Local0)
                M600 (Arg0, 0x1C, Local0, 0x0321)
                Store ((DerefOf (RefOf (AUI6)) + B606), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0322)
            }

            Store ((DerefOf (PAUI [0x05]) + B606), Local0)
            M600 (Arg0, 0x1E, Local0, 0x0321)
            Store ((DerefOf (PAUI [0x06]) + B606), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0322)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) + B606), Local0)
            M600 (Arg0, 0x20, Local0, 0x0321)
            Store ((M601 (0x01, 0x06) + B606), Local0)
            M600 (Arg0, 0x21, Local0, 0x0322)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) + B606), Local0)
                M600 (Arg0, 0x22, Local0, 0x0321)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) + B606), Local0)
                M600 (Arg0, 0x23, Local0, 0x0322)
            }

            Local0 = (0x00 + B606) /* \M613.M03B.B606 */
            M600 (Arg0, 0x24, Local0, 0x0321)
            Local0 = (0x01 + B606) /* \M613.M03B.B606 */
            M600 (Arg0, 0x25, Local0, 0x0322)
            Local0 = (AUI5 + B606) /* \M613.M03B.B606 */
            M600 (Arg0, 0x26, Local0, 0x0321)
            Local0 = (AUI6 + B606) /* \M613.M03B.B606 */
            M600 (Arg0, 0x27, Local0, 0x0322)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) + B606) /* \M613.M03B.B606 */
                M600 (Arg0, 0x28, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (AUI6)) + B606) /* \M613.M03B.B606 */
                M600 (Arg0, 0x29, Local0, 0x0322)
            }

            Local0 = (DerefOf (PAUI [0x05]) + B606) /* \M613.M03B.B606 */
            M600 (Arg0, 0x2A, Local0, 0x0321)
            Local0 = (DerefOf (PAUI [0x06]) + B606) /* \M613.M03B.B606 */
            M600 (Arg0, 0x2B, Local0, 0x0322)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) + B606) /* \M613.M03B.B606 */
            M600 (Arg0, 0x2C, Local0, 0x0321)
            Local0 = (M601 (0x01, 0x06) + B606) /* \M613.M03B.B606 */
            M600 (Arg0, 0x2D, Local0, 0x0322)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) + B606) /* \M613.M03B.B606 */
                M600 (Arg0, 0x2E, Local0, 0x0321)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) + B606) /* \M613.M03B.B606 */
                M600 (Arg0, 0x2F, Local0, 0x0322)
            }
        }

        /* Add, 64-bit */

        Method (M03C, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A + 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((B60A + 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xFE7CB391D650A285)
            Store ((B60A + AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((B60A + AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xFE7CB391D650A285)
            If (Y078)
            {
                Store ((B60A + DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((B60A + DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFE7CB391D650A285)
            }

            Store ((B60A + DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((B60A + DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFE7CB391D650A285)
            /* Method returns Integer */

            Store ((B60A + M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((B60A + M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFE7CB391D650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A + DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((B60A + DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFE7CB391D650A285)
            }

            Local0 = (B60A + 0x00)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A + 0x01)
            M600 (Arg0, 0x0D, Local0, 0xFE7CB391D650A285)
            Local0 = (B60A + AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A + AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xFE7CB391D650A285)
            If (Y078)
            {
                Local0 = (B60A + DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (B60A + DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xFE7CB391D650A285)
            }

            Local0 = (B60A + DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A + DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xFE7CB391D650A285)
            /* Method returns Integer */

            Local0 = (B60A + M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A + M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xFE7CB391D650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A + DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (B60A + DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFE7CB391D650A285)
            }

            /* Conversion of the second operand */

            Store ((0x00 + B60A), Local0)
            M600 (Arg0, 0x18, Local0, 0xFE7CB391D650A284)
            Store ((0x01 + B60A), Local0)
            M600 (Arg0, 0x19, Local0, 0xFE7CB391D650A285)
            Store ((AUI5 + B60A), Local0)
            M600 (Arg0, 0x1A, Local0, 0xFE7CB391D650A284)
            Store ((AUI6 + B60A), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFE7CB391D650A285)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) + B60A), Local0)
                M600 (Arg0, 0x1C, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (AUI6)) + B60A), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFE7CB391D650A285)
            }

            Store ((DerefOf (PAUI [0x05]) + B60A), Local0)
            M600 (Arg0, 0x1E, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (PAUI [0x06]) + B60A), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFE7CB391D650A285)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) + B60A), Local0)
            M600 (Arg0, 0x20, Local0, 0xFE7CB391D650A284)
            Store ((M601 (0x01, 0x06) + B60A), Local0)
            M600 (Arg0, 0x21, Local0, 0xFE7CB391D650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) + B60A), Local0)
                M600 (Arg0, 0x22, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) + B60A), Local0)
                M600 (Arg0, 0x23, Local0, 0xFE7CB391D650A285)
            }

            Local0 = (0x00 + B60A) /* \M613.M03C.B60A */
            M600 (Arg0, 0x24, Local0, 0xFE7CB391D650A284)
            Local0 = (0x01 + B60A) /* \M613.M03C.B60A */
            M600 (Arg0, 0x25, Local0, 0xFE7CB391D650A285)
            Local0 = (AUI5 + B60A) /* \M613.M03C.B60A */
            M600 (Arg0, 0x26, Local0, 0xFE7CB391D650A284)
            Local0 = (AUI6 + B60A) /* \M613.M03C.B60A */
            M600 (Arg0, 0x27, Local0, 0xFE7CB391D650A285)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) + B60A) /* \M613.M03C.B60A */
                M600 (Arg0, 0x28, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (AUI6)) + B60A) /* \M613.M03C.B60A */
                M600 (Arg0, 0x29, Local0, 0xFE7CB391D650A285)
            }

            Local0 = (DerefOf (PAUI [0x05]) + B60A) /* \M613.M03C.B60A */
            M600 (Arg0, 0x2A, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (PAUI [0x06]) + B60A) /* \M613.M03C.B60A */
            M600 (Arg0, 0x2B, Local0, 0xFE7CB391D650A285)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) + B60A) /* \M613.M03C.B60A */
            M600 (Arg0, 0x2C, Local0, 0xFE7CB391D650A284)
            Local0 = (M601 (0x01, 0x06) + B60A) /* \M613.M03C.B60A */
            M600 (Arg0, 0x2D, Local0, 0xFE7CB391D650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) + B60A) /* \M613.M03C.B60A */
                M600 (Arg0, 0x2E, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) + B60A) /* \M613.M03C.B60A */
                M600 (Arg0, 0x2F, Local0, 0xFE7CB391D650A285)
            }

            /* Conversion of the both operands */

            Store ((B606 + B60A), Local0)
            M600 (Arg0, 0x30, Local0, 0xFE7CB391D650A5A5)
            Store ((B60A + B606), Local0)
            M600 (Arg0, 0x31, Local0, 0xFE7CB391D650A5A5)
            Local0 = (B606 + B60A) /* \M613.M03C.B60A */
            M600 (Arg0, 0x32, Local0, 0xFE7CB391D650A5A5)
            Local0 = (B60A + B606) /* \M613.M03C.B606 */
            M600 (Arg0, 0x33, Local0, 0xFE7CB391D650A5A5)
        }

        /* Add, 32-bit */

        Method (M03D, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A + 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xD650A284)
            Store ((B60A + 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xD650A285)
            Store ((B60A + AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xD650A284)
            Store ((B60A + AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xD650A285)
            If (Y078)
            {
                Store ((B60A + DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xD650A284)
                Store ((B60A + DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xD650A285)
            }

            Store ((B60A + DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xD650A284)
            Store ((B60A + DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xD650A285)
            /* Method returns Integer */

            Store ((B60A + M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xD650A284)
            Store ((B60A + M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xD650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A + DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xD650A284)
                Store ((B60A + DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xD650A285)
            }

            Local0 = (B60A + 0x00)
            M600 (Arg0, 0x0C, Local0, 0xD650A284)
            Local0 = (B60A + 0x01)
            M600 (Arg0, 0x0D, Local0, 0xD650A285)
            Local0 = (B60A + AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xD650A284)
            Local0 = (B60A + AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xD650A285)
            If (Y078)
            {
                Local0 = (B60A + DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xD650A284)
                Local0 = (B60A + DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xD650A285)
            }

            Local0 = (B60A + DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xD650A284)
            Local0 = (B60A + DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xD650A285)
            /* Method returns Integer */

            Local0 = (B60A + M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xD650A284)
            Local0 = (B60A + M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xD650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A + DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xD650A284)
                Local0 = (B60A + DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xD650A285)
            }

            /* Conversion of the second operand */

            Store ((0x00 + B60A), Local0)
            M600 (Arg0, 0x18, Local0, 0xD650A284)
            Store ((0x01 + B60A), Local0)
            M600 (Arg0, 0x19, Local0, 0xD650A285)
            Store ((AUI5 + B60A), Local0)
            M600 (Arg0, 0x1A, Local0, 0xD650A284)
            Store ((AUI6 + B60A), Local0)
            M600 (Arg0, 0x1B, Local0, 0xD650A285)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) + B60A), Local0)
                M600 (Arg0, 0x1C, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (AUI6)) + B60A), Local0)
                M600 (Arg0, 0x1D, Local0, 0xD650A285)
            }

            Store ((DerefOf (PAUI [0x05]) + B60A), Local0)
            M600 (Arg0, 0x1E, Local0, 0xD650A284)
            Store ((DerefOf (PAUI [0x06]) + B60A), Local0)
            M600 (Arg0, 0x1F, Local0, 0xD650A285)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) + B60A), Local0)
            M600 (Arg0, 0x20, Local0, 0xD650A284)
            Store ((M601 (0x01, 0x06) + B60A), Local0)
            M600 (Arg0, 0x21, Local0, 0xD650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) + B60A), Local0)
                M600 (Arg0, 0x22, Local0, 0xD650A284)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) + B60A), Local0)
                M600 (Arg0, 0x23, Local0, 0xD650A285)
            }

            Local0 = (0x00 + B60A) /* \M613.M03D.B60A */
            M600 (Arg0, 0x24, Local0, 0xD650A284)
            Local0 = (0x01 + B60A) /* \M613.M03D.B60A */
            M600 (Arg0, 0x25, Local0, 0xD650A285)
            Local0 = (AUI5 + B60A) /* \M613.M03D.B60A */
            M600 (Arg0, 0x26, Local0, 0xD650A284)
            Local0 = (AUI6 + B60A) /* \M613.M03D.B60A */
            M600 (Arg0, 0x27, Local0, 0xD650A285)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) + B60A) /* \M613.M03D.B60A */
                M600 (Arg0, 0x28, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (AUI6)) + B60A) /* \M613.M03D.B60A */
                M600 (Arg0, 0x29, Local0, 0xD650A285)
            }

            Local0 = (DerefOf (PAUI [0x05]) + B60A) /* \M613.M03D.B60A */
            M600 (Arg0, 0x2A, Local0, 0xD650A284)
            Local0 = (DerefOf (PAUI [0x06]) + B60A) /* \M613.M03D.B60A */
            M600 (Arg0, 0x2B, Local0, 0xD650A285)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) + B60A) /* \M613.M03D.B60A */
            M600 (Arg0, 0x2C, Local0, 0xD650A284)
            Local0 = (M601 (0x01, 0x06) + B60A) /* \M613.M03D.B60A */
            M600 (Arg0, 0x2D, Local0, 0xD650A285)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) + B60A) /* \M613.M03D.B60A */
                M600 (Arg0, 0x2E, Local0, 0xD650A284)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) + B60A) /* \M613.M03D.B60A */
                M600 (Arg0, 0x2F, Local0, 0xD650A285)
            }

            /* Conversion of the both operands */

            Store ((B606 + B60A), Local0)
            M600 (Arg0, 0x30, Local0, 0xD650A5A5)
            Store ((B60A + B606), Local0)
            M600 (Arg0, 0x31, Local0, 0xD650A5A5)
            Local0 = (B606 + B60A) /* \M613.M03D.B60A */
            M600 (Arg0, 0x32, Local0, 0xD650A5A5)
            Local0 = (B60A + B606) /* \M613.M03D.B606 */
            M600 (Arg0, 0x33, Local0, 0xD650A5A5)
        }

        /* And, common 32-bit/64-bit test */

        Method (M03E, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            /* Conversion of the first operand */

            Store ((B606 & 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x00)
            Store ((B606 & 0xFFFFFFFFFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0x0321)
            Store ((B606 & AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x00)
            Store ((B606 & AUIJ), Local0)
            M600 (Arg0, 0x03, Local0, 0x0321)
            If (Y078)
            {
                Store ((B606 & DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x00)
                Store ((B606 & DerefOf (RefOf (AUIJ))), Local0)
                M600 (Arg0, 0x05, Local0, 0x0321)
            }

            Store ((B606 & DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x00)
            Store ((B606 & DerefOf (PAUI [0x13])), Local0)
            M600 (Arg0, 0x07, Local0, 0x0321)
            /* Method returns Integer */

            Store ((B606 & M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x00)
            Store ((B606 & M601 (0x01, 0x13)), Local0)
            M600 (Arg0, 0x09, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B606 & DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x00)
                Store ((B606 & DerefOf (M602 (0x01, 0x13, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x0321)
            }

            Local0 = (B606 & 0x00)
            M600 (Arg0, 0x0C, Local0, 0x00)
            Local0 = (B606 & 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0x0321)
            Local0 = (B606 & AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x00)
            Local0 = (B606 & AUIJ) /* \AUIJ */
            M600 (Arg0, 0x0F, Local0, 0x0321)
            If (Y078)
            {
                Local0 = (B606 & DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x00)
                Local0 = (B606 & DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x11, Local0, 0x0321)
            }

            Local0 = (B606 & DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x00)
            Local0 = (B606 & DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x13, Local0, 0x0321)
            /* Method returns Integer */

            Local0 = (B606 & M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x00)
            Local0 = (B606 & M601 (0x01, 0x13))
            M600 (Arg0, 0x15, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B606 & DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x00)
                Local0 = (B606 & DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x0321)
            }

            /* Conversion of the second operand */

            Store ((0x00 & B606), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xFFFFFFFFFFFFFFFF & B606), Local0)
            M600 (Arg0, 0x19, Local0, 0x0321)
            Store ((AUI5 & B606), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUIJ & B606), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0321)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) & B606), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUIJ)) & B606), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0321)
            }

            Store ((DerefOf (PAUI [0x05]) & B606), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x13]) & B606), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0321)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) & B606), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x13) & B606), Local0)
            M600 (Arg0, 0x21, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) & B606), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x13, 0x01)) & B606), Local0)
                M600 (Arg0, 0x23, Local0, 0x0321)
            }

            Local0 = (0x00 & B606) /* \M613.M03E.B606 */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0xFFFFFFFFFFFFFFFF & B606) /* \M613.M03E.B606 */
            M600 (Arg0, 0x25, Local0, 0x0321)
            Local0 = (AUI5 & B606) /* \M613.M03E.B606 */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUIJ & B606) /* \M613.M03E.B606 */
            M600 (Arg0, 0x27, Local0, 0x0321)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) & B606) /* \M613.M03E.B606 */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUIJ)) & B606) /* \M613.M03E.B606 */
                M600 (Arg0, 0x29, Local0, 0x0321)
            }

            Local0 = (DerefOf (PAUI [0x05]) & B606) /* \M613.M03E.B606 */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x13]) & B606) /* \M613.M03E.B606 */
            M600 (Arg0, 0x2B, Local0, 0x0321)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) & B606) /* \M613.M03E.B606 */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x13) & B606) /* \M613.M03E.B606 */
            M600 (Arg0, 0x2D, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) & B606) /* \M613.M03E.B606 */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x13, 0x01)) & B606) /* \M613.M03E.B606 */
                M600 (Arg0, 0x2F, Local0, 0x0321)
            }
        }

        /* And, 64-bit */

        Method (M03F, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A & 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x00)
            Store ((B60A & 0xFFFFFFFFFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0xFE7CB391D650A284)
            Store ((B60A & AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x00)
            Store ((B60A & AUIJ), Local0)
            M600 (Arg0, 0x03, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Store ((B60A & DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x00)
                Store ((B60A & DerefOf (RefOf (AUIJ))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFE7CB391D650A284)
            }

            Store ((B60A & DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x00)
            Store ((B60A & DerefOf (PAUI [0x13])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Store ((B60A & M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x00)
            Store ((B60A & M601 (0x01, 0x13)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A & DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x00)
                Store ((B60A & DerefOf (M602 (0x01, 0x13, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (B60A & 0x00)
            M600 (Arg0, 0x0C, Local0, 0x00)
            Local0 = (B60A & 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A & AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x00)
            Local0 = (B60A & AUIJ) /* \AUIJ */
            M600 (Arg0, 0x0F, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Local0 = (B60A & DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x00)
                Local0 = (B60A & DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x11, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (B60A & DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x00)
            Local0 = (B60A & DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x13, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Local0 = (B60A & M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x00)
            Local0 = (B60A & M601 (0x01, 0x13))
            M600 (Arg0, 0x15, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A & DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x00)
                Local0 = (B60A & DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFE7CB391D650A284)
            }

            /* Conversion of the second operand */

            Store ((0x00 & B60A), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xFFFFFFFFFFFFFFFF & B60A), Local0)
            M600 (Arg0, 0x19, Local0, 0xFE7CB391D650A284)
            Store ((AUI5 & B60A), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUIJ & B60A), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) & B60A), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUIJ)) & B60A), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFE7CB391D650A284)
            }

            Store ((DerefOf (PAUI [0x05]) & B60A), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x13]) & B60A), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) & B60A), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x13) & B60A), Local0)
            M600 (Arg0, 0x21, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) & B60A), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x13, 0x01)) & B60A), Local0)
                M600 (Arg0, 0x23, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (0x00 & B60A) /* \M613.M03F.B60A */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0xFFFFFFFFFFFFFFFF & B60A) /* \M613.M03F.B60A */
            M600 (Arg0, 0x25, Local0, 0xFE7CB391D650A284)
            Local0 = (AUI5 & B60A) /* \M613.M03F.B60A */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUIJ & B60A) /* \M613.M03F.B60A */
            M600 (Arg0, 0x27, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) & B60A) /* \M613.M03F.B60A */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUIJ)) & B60A) /* \M613.M03F.B60A */
                M600 (Arg0, 0x29, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (DerefOf (PAUI [0x05]) & B60A) /* \M613.M03F.B60A */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x13]) & B60A) /* \M613.M03F.B60A */
            M600 (Arg0, 0x2B, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) & B60A) /* \M613.M03F.B60A */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x13) & B60A) /* \M613.M03F.B60A */
            M600 (Arg0, 0x2D, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) & B60A) /* \M613.M03F.B60A */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x13, 0x01)) & B60A) /* \M613.M03F.B60A */
                M600 (Arg0, 0x2F, Local0, 0xFE7CB391D650A284)
            }

            /* Conversion of the both operands */

            Store ((B606 & B60A), Local0)
            M600 (Arg0, 0x30, Local0, 0x0200)
            Store ((B60A & B606), Local0)
            M600 (Arg0, 0x31, Local0, 0x0200)
            Local0 = (B606 & B60A) /* \M613.M03F.B60A */
            M600 (Arg0, 0x32, Local0, 0x0200)
            Local0 = (B60A & B606) /* \M613.M03F.B606 */
            M600 (Arg0, 0x33, Local0, 0x0200)
        }

        /* And, 32-bit */

        Method (M040, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A & 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x00)
            Store ((B60A & 0xFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0xD650A284)
            Store ((B60A & AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x00)
            Store ((B60A & AUII), Local0)
            M600 (Arg0, 0x03, Local0, 0xD650A284)
            If (Y078)
            {
                Store ((B60A & DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x00)
                Store ((B60A & DerefOf (RefOf (AUII))), Local0)
                M600 (Arg0, 0x05, Local0, 0xD650A284)
            }

            Store ((B60A & DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x00)
            Store ((B60A & DerefOf (PAUI [0x12])), Local0)
            M600 (Arg0, 0x07, Local0, 0xD650A284)
            /* Method returns Integer */

            Store ((B60A & M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x00)
            Store ((B60A & M601 (0x01, 0x12)), Local0)
            M600 (Arg0, 0x09, Local0, 0xD650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A & DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x00)
                Store ((B60A & DerefOf (M602 (0x01, 0x12, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xD650A284)
            }

            Local0 = (B60A & 0x00)
            M600 (Arg0, 0x0C, Local0, 0x00)
            Local0 = (B60A & 0xFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0xD650A284)
            Local0 = (B60A & AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x00)
            Local0 = (B60A & AUII) /* \AUII */
            M600 (Arg0, 0x0F, Local0, 0xD650A284)
            If (Y078)
            {
                Local0 = (B60A & DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x00)
                Local0 = (B60A & DerefOf (RefOf (AUII)))
                M600 (Arg0, 0x11, Local0, 0xD650A284)
            }

            Local0 = (B60A & DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x00)
            Local0 = (B60A & DerefOf (PAUI [0x12]))
            M600 (Arg0, 0x13, Local0, 0xD650A284)
            /* Method returns Integer */

            Local0 = (B60A & M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x00)
            Local0 = (B60A & M601 (0x01, 0x12))
            M600 (Arg0, 0x15, Local0, 0xD650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A & DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x00)
                Local0 = (B60A & DerefOf (M602 (0x01, 0x12, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xD650A284)
            }

            /* Conversion of the second operand */

            Store ((0x00 & B60A), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xFFFFFFFF & B60A), Local0)
            M600 (Arg0, 0x19, Local0, 0xD650A284)
            Store ((AUI5 & B60A), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUII & B60A), Local0)
            M600 (Arg0, 0x1B, Local0, 0xD650A284)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) & B60A), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUII)) & B60A), Local0)
                M600 (Arg0, 0x1D, Local0, 0xD650A284)
            }

            Store ((DerefOf (PAUI [0x05]) & B60A), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x12]) & B60A), Local0)
            M600 (Arg0, 0x1F, Local0, 0xD650A284)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) & B60A), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x12) & B60A), Local0)
            M600 (Arg0, 0x21, Local0, 0xD650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) & B60A), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x12, 0x01)) & B60A), Local0)
                M600 (Arg0, 0x23, Local0, 0xD650A284)
            }

            Local0 = (0x00 & B60A) /* \M613.M040.B60A */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0xFFFFFFFF & B60A) /* \M613.M040.B60A */
            M600 (Arg0, 0x25, Local0, 0xD650A284)
            Local0 = (AUI5 & B60A) /* \M613.M040.B60A */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUII & B60A) /* \M613.M040.B60A */
            M600 (Arg0, 0x27, Local0, 0xD650A284)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) & B60A) /* \M613.M040.B60A */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUII)) & B60A) /* \M613.M040.B60A */
                M600 (Arg0, 0x29, Local0, 0xD650A284)
            }

            Local0 = (DerefOf (PAUI [0x05]) & B60A) /* \M613.M040.B60A */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x12]) & B60A) /* \M613.M040.B60A */
            M600 (Arg0, 0x2B, Local0, 0xD650A284)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) & B60A) /* \M613.M040.B60A */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x12) & B60A) /* \M613.M040.B60A */
            M600 (Arg0, 0x2D, Local0, 0xD650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) & B60A) /* \M613.M040.B60A */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x12, 0x01)) & B60A) /* \M613.M040.B60A */
                M600 (Arg0, 0x2F, Local0, 0xD650A284)
            }

            /* Conversion of the both operands */

            Store ((B606 & B60A), Local0)
            M600 (Arg0, 0x30, Local0, 0x0200)
            Store ((B60A & B606), Local0)
            M600 (Arg0, 0x31, Local0, 0x0200)
            Local0 = (B606 & B60A) /* \M613.M040.B60A */
            M600 (Arg0, 0x32, Local0, 0x0200)
            Local0 = (B60A & B606) /* \M613.M040.B606 */
            M600 (Arg0, 0x33, Local0, 0x0200)
        }

        /* Divide, common 32-bit/64-bit test */

        Method (M041, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            /* Conversion of the first operand */

            Store ((B606 / 0x01), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((B606 / 0x0321), Local0)
            M600 (Arg0, 0x01, Local0, 0x01)
            Store ((B606 / AUI6), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((B606 / AUI1), Local0)
            M600 (Arg0, 0x03, Local0, 0x01)
            If (Y078)
            {
                Store ((B606 / DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((B606 / DerefOf (RefOf (AUI1))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01)
            }

            Store ((B606 / DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((B606 / DerefOf (PAUI [0x01])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01)
            /* Method returns Integer */

            Store ((B606 / M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((B606 / M601 (0x01, 0x01)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B606 / DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((B606 / DerefOf (M602 (0x01, 0x01, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01)
            }

            Divide (B606, 0x01, Local1, Local0)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Divide (B606, 0x0321, Local1, Local0)
            M600 (Arg0, 0x0D, Local0, 0x01)
            Divide (B606, AUI6, Local1, Local0)
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Divide (B606, AUI1, Local1, Local0)
            M600 (Arg0, 0x0F, Local0, 0x01)
            If (Y078)
            {
                Divide (B606, DerefOf (RefOf (AUI6)), Local1, Local0)
                M600 (Arg0, 0x10, Local0, 0x0321)
                Divide (B606, DerefOf (RefOf (AUI1)), Local1, Local0)
                M600 (Arg0, 0x11, Local0, 0x01)
            }

            Divide (B606, DerefOf (PAUI [0x06]), Local1, Local0)
            M600 (Arg0, 0x12, Local0, 0x0321)
            Divide (B606, DerefOf (PAUI [0x01]), Local1, Local0)
            M600 (Arg0, 0x13, Local0, 0x01)
            /* Method returns Integer */

            Divide (B606, M601 (0x01, 0x06), Local1, Local0)
            M600 (Arg0, 0x14, Local0, 0x0321)
            Divide (B606, M601 (0x01, 0x01), Local1, Local0)
            M600 (Arg0, 0x15, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Divide (B606, DerefOf (M602 (0x01, 0x06, 0x01)), Local1, Local0)
                M600 (Arg0, 0x16, Local0, 0x0321)
                Divide (B606, DerefOf (M602 (0x01, 0x01, 0x01)), Local1, Local0)
                M600 (Arg0, 0x17, Local0, 0x01)
            }

            /* Conversion of the second operand */

            Store ((0x01 / B606), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x0321 / B606), Local0)
            M600 (Arg0, 0x19, Local0, 0x01)
            Store ((AUI6 / B606), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI1 / B606), Local0)
            M600 (Arg0, 0x1B, Local0, 0x01)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI6)) / B606), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI1)) / B606), Local0)
                M600 (Arg0, 0x1D, Local0, 0x01)
            }

            Store ((DerefOf (PAUI [0x06]) / B606), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x01]) / B606), Local0)
            M600 (Arg0, 0x1F, Local0, 0x01)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x06) / B606), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x01) / B606), Local0)
            M600 (Arg0, 0x21, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) / B606), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x01, 0x01)) / B606), Local0)
                M600 (Arg0, 0x23, Local0, 0x01)
            }

            Divide (0x01, B606, Local1, Local0)
            M600 (Arg0, 0x24, Local0, 0x00)
            Divide (0x0321, B606, Local1, Local0)
            M600 (Arg0, 0x25, Local0, 0x01)
            Divide (AUI6, B606, Local1, Local0)
            M600 (Arg0, 0x26, Local0, 0x00)
            Divide (AUI1, B606, Local1, Local0)
            M600 (Arg0, 0x27, Local0, 0x01)
            If (Y078)
            {
                Divide (DerefOf (RefOf (AUI6)), B606, Local1, Local0)
                M600 (Arg0, 0x28, Local0, 0x00)
                Divide (DerefOf (RefOf (AUI1)), B606, Local1, Local0)
                M600 (Arg0, 0x29, Local0, 0x01)
            }

            Divide (DerefOf (PAUI [0x06]), B606, Local1, Local0)
            M600 (Arg0, 0x2A, Local0, 0x00)
            Divide (DerefOf (PAUI [0x01]), B606, Local1, Local0)
            M600 (Arg0, 0x2B, Local0, 0x01)
            /* Method returns Integer */

            Divide (M601 (0x01, 0x06), B606, Local1, Local0)
            M600 (Arg0, 0x2C, Local0, 0x00)
            Divide (M601 (0x01, 0x01), B606, Local1, Local0)
            M600 (Arg0, 0x2D, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Divide (DerefOf (M602 (0x01, 0x06, 0x01)), B606, Local1, Local0)
                M600 (Arg0, 0x2E, Local0, 0x00)
                Divide (DerefOf (M602 (0x01, 0x01, 0x01)), B606, Local1, Local0)
                M600 (Arg0, 0x2F, Local0, 0x01)
            }
        }

        /* Divide, 64-bit */

        Method (M042, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A / 0x01), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((B60A / 0xFE7CB391D650A284), Local0)
            M600 (Arg0, 0x01, Local0, 0x01)
            Store ((B60A / AUI6), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((B60A / AUI4), Local0)
            M600 (Arg0, 0x03, Local0, 0x01)
            If (Y078)
            {
                Store ((B60A / DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((B60A / DerefOf (RefOf (AUI4))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01)
            }

            Store ((B60A / DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((B60A / DerefOf (PAUI [0x04])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01)
            /* Method returns Integer */

            Store ((B60A / M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((B60A / M601 (0x01, 0x04)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A / DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((B60A / DerefOf (M602 (0x01, 0x04, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01)
            }

            Divide (B60A, 0x01, Local1, Local0)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Divide (B60A, 0xFE7CB391D650A284, Local1, Local0)
            M600 (Arg0, 0x0D, Local0, 0x01)
            Divide (B60A, AUI6, Local1, Local0)
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Divide (B60A, AUI4, Local1, Local0)
            M600 (Arg0, 0x0F, Local0, 0x01)
            If (Y078)
            {
                Divide (B60A, DerefOf (RefOf (AUI6)), Local1, Local0)
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Divide (B60A, DerefOf (RefOf (AUI4)), Local1, Local0)
                M600 (Arg0, 0x11, Local0, 0x01)
            }

            Divide (B60A, DerefOf (PAUI [0x06]), Local1, Local0)
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Divide (B60A, DerefOf (PAUI [0x04]), Local1, Local0)
            M600 (Arg0, 0x13, Local0, 0x01)
            /* Method returns Integer */

            Divide (B60A, M601 (0x01, 0x06), Local1, Local0)
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Divide (B60A, M601 (0x01, 0x04), Local1, Local0)
            M600 (Arg0, 0x15, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Divide (B60A, DerefOf (M602 (0x01, 0x06, 0x01)), Local1, Local0)
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Divide (B60A, DerefOf (M602 (0x01, 0x04, 0x01)), Local1, Local0)
                M600 (Arg0, 0x17, Local0, 0x01)
            }

            /* Conversion of the second operand */

            Store ((0x01 / B60A), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xFE7CB391D650A284 / B60A), Local0)
            M600 (Arg0, 0x19, Local0, 0x01)
            Store ((AUI6 / B60A), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI4 / B60A), Local0)
            M600 (Arg0, 0x1B, Local0, 0x01)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI6)) / B60A), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI4)) / B60A), Local0)
                M600 (Arg0, 0x1D, Local0, 0x01)
            }

            Store ((DerefOf (PAUI [0x06]) / B60A), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x04]) / B60A), Local0)
            M600 (Arg0, 0x1F, Local0, 0x01)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x06) / B60A), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x04) / B60A), Local0)
            M600 (Arg0, 0x21, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) / B60A), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x04, 0x01)) / B60A), Local0)
                M600 (Arg0, 0x23, Local0, 0x01)
            }

            Divide (0x01, B60A, Local1, Local0)
            M600 (Arg0, 0x24, Local0, 0x00)
            Divide (0xFE7CB391D650A284, B60A, Local1, Local0)
            M600 (Arg0, 0x25, Local0, 0x01)
            Divide (AUI6, B60A, Local1, Local0)
            M600 (Arg0, 0x26, Local0, 0x00)
            Divide (AUI4, B60A, Local1, Local0)
            M600 (Arg0, 0x27, Local0, 0x01)
            If (Y078)
            {
                Divide (DerefOf (RefOf (AUI6)), B60A, Local1, Local0)
                M600 (Arg0, 0x28, Local0, 0x00)
                Divide (DerefOf (RefOf (AUI4)), B60A, Local1, Local0)
                M600 (Arg0, 0x29, Local0, 0x01)
            }

            Divide (DerefOf (PAUI [0x06]), B60A, Local1, Local0)
            M600 (Arg0, 0x2A, Local0, 0x00)
            Divide (DerefOf (PAUI [0x04]), B60A, Local1, Local0)
            M600 (Arg0, 0x2B, Local0, 0x01)
            /* Method returns Integer */

            Divide (M601 (0x01, 0x06), B60A, Local1, Local0)
            M600 (Arg0, 0x2C, Local0, 0x00)
            Divide (M601 (0x01, 0x04), B60A, Local1, Local0)
            M600 (Arg0, 0x2D, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Divide (DerefOf (M602 (0x01, 0x06, 0x01)), B60A, Local1, Local0)
                M600 (Arg0, 0x2E, Local0, 0x00)
                Divide (DerefOf (M602 (0x01, 0x04, 0x01)), B60A, Local1, Local0)
                M600 (Arg0, 0x2F, Local0, 0x01)
            }

            /* Conversion of the both operands */

            Store ((B606 / B60A), Local0)
            M600 (Arg0, 0x30, Local0, 0x00)
            Store ((B60A / B606), Local0)
            M600 (Arg0, 0x31, Local0, 0x0051558EB950F5A7)
            Divide (B606, B60A, Local1, Local0)
            M600 (Arg0, 0x32, Local0, 0x00)
            Divide (B60A, B606, Local1, Local0)
            M600 (Arg0, 0x33, Local0, 0x0051558EB950F5A7)
        }

        /* Divide, 32-bit */

        Method (M043, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A / 0x01), Local0)
            M600 (Arg0, 0x00, Local0, 0xD650A284)
            Store ((B60A / 0xD650A284), Local0)
            M600 (Arg0, 0x01, Local0, 0x01)
            Store ((B60A / AUI6), Local0)
            M600 (Arg0, 0x02, Local0, 0xD650A284)
            Store ((B60A / AUIK), Local0)
            M600 (Arg0, 0x03, Local0, 0x01)
            If (Y078)
            {
                Store ((B60A / DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x04, Local0, 0xD650A284)
                Store ((B60A / DerefOf (RefOf (AUIK))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01)
            }

            Store ((B60A / DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x06, Local0, 0xD650A284)
            Store ((B60A / DerefOf (PAUI [0x14])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01)
            /* Method returns Integer */

            Store ((B60A / M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x08, Local0, 0xD650A284)
            Store ((B60A / M601 (0x01, 0x14)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A / DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xD650A284)
                Store ((B60A / DerefOf (M602 (0x01, 0x14, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01)
            }

            Divide (B60A, 0x01, Local1, Local0)
            M600 (Arg0, 0x0C, Local0, 0xD650A284)
            Divide (B60A, 0xD650A284, Local1, Local0)
            M600 (Arg0, 0x0D, Local0, 0x01)
            Divide (B60A, AUI6, Local1, Local0)
            M600 (Arg0, 0x0E, Local0, 0xD650A284)
            Divide (B60A, AUIK, Local1, Local0)
            M600 (Arg0, 0x0F, Local0, 0x01)
            If (Y078)
            {
                Divide (B60A, DerefOf (RefOf (AUI6)), Local1, Local0)
                M600 (Arg0, 0x10, Local0, 0xD650A284)
                Divide (B60A, DerefOf (RefOf (AUIK)), Local1, Local0)
                M600 (Arg0, 0x11, Local0, 0x01)
            }

            Divide (B60A, DerefOf (PAUI [0x06]), Local1, Local0)
            M600 (Arg0, 0x12, Local0, 0xD650A284)
            Divide (B60A, DerefOf (PAUI [0x14]), Local1, Local0)
            M600 (Arg0, 0x13, Local0, 0x01)
            /* Method returns Integer */

            Divide (B60A, M601 (0x01, 0x06), Local1, Local0)
            M600 (Arg0, 0x14, Local0, 0xD650A284)
            Divide (B60A, M601 (0x01, 0x14), Local1, Local0)
            M600 (Arg0, 0x15, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Divide (B60A, DerefOf (M602 (0x01, 0x06, 0x01)), Local1, Local0)
                M600 (Arg0, 0x16, Local0, 0xD650A284)
                Divide (B60A, DerefOf (M602 (0x01, 0x14, 0x01)), Local1, Local0)
                M600 (Arg0, 0x17, Local0, 0x01)
            }

            /* Conversion of the second operand */

            Store ((0x01 / B60A), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xD650A284 / B60A), Local0)
            M600 (Arg0, 0x19, Local0, 0x01)
            Store ((AUI6 / B60A), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUIK / B60A), Local0)
            M600 (Arg0, 0x1B, Local0, 0x01)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI6)) / B60A), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUIK)) / B60A), Local0)
                M600 (Arg0, 0x1D, Local0, 0x01)
            }

            Store ((DerefOf (PAUI [0x06]) / B60A), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x14]) / B60A), Local0)
            M600 (Arg0, 0x1F, Local0, 0x01)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x06) / B60A), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x14) / B60A), Local0)
            M600 (Arg0, 0x21, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) / B60A), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x14, 0x01)) / B60A), Local0)
                M600 (Arg0, 0x23, Local0, 0x01)
            }

            Divide (0x01, B60A, Local1, Local0)
            M600 (Arg0, 0x24, Local0, 0x00)
            Divide (0xD650A284, B60A, Local1, Local0)
            M600 (Arg0, 0x25, Local0, 0x01)
            Divide (AUI6, B60A, Local1, Local0)
            M600 (Arg0, 0x26, Local0, 0x00)
            Divide (AUIK, B60A, Local1, Local0)
            M600 (Arg0, 0x27, Local0, 0x01)
            If (Y078)
            {
                Divide (DerefOf (RefOf (AUI6)), B60A, Local1, Local0)
                M600 (Arg0, 0x28, Local0, 0x00)
                Divide (DerefOf (RefOf (AUIK)), B60A, Local1, Local0)
                M600 (Arg0, 0x29, Local0, 0x01)
            }

            Divide (DerefOf (PAUI [0x06]), B60A, Local1, Local0)
            M600 (Arg0, 0x2A, Local0, 0x00)
            Divide (DerefOf (PAUI [0x14]), B60A, Local1, Local0)
            M600 (Arg0, 0x2B, Local0, 0x01)
            /* Method returns Integer */

            Divide (M601 (0x01, 0x06), B60A, Local1, Local0)
            M600 (Arg0, 0x2C, Local0, 0x00)
            Divide (M601 (0x01, 0x14), B60A, Local1, Local0)
            M600 (Arg0, 0x2D, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Divide (DerefOf (M602 (0x01, 0x06, 0x01)), B60A, Local1, Local0)
                M600 (Arg0, 0x2E, Local0, 0x00)
                Divide (DerefOf (M602 (0x01, 0x14, 0x01)), B60A, Local1, Local0)
                M600 (Arg0, 0x2F, Local0, 0x01)
            }

            /* Conversion of the both operands */

            Store ((B606 / B60A), Local0)
            M600 (Arg0, 0x30, Local0, 0x00)
            Store ((B60A / B606), Local0)
            M600 (Arg0, 0x31, Local0, 0x00447EC3)
            Divide (B606, B60A, Local1, Local0)
            M600 (Arg0, 0x32, Local0, 0x00)
            Divide (B60A, B606, Local1, Local0)
            M600 (Arg0, 0x33, Local0, 0x00447EC3)
        }

        /* Mod, common 32-bit/64-bit test */

        Method (M044, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            /* Conversion of the first operand */

            Store ((B606 % 0x0322), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((B606 % 0x0320), Local0)
            M600 (Arg0, 0x01, Local0, 0x01)
            Store ((B606 % AUIG), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((B606 % AUIH), Local0)
            M600 (Arg0, 0x03, Local0, 0x01)
            If (Y078)
            {
                Store ((B606 % DerefOf (RefOf (AUIG))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((B606 % DerefOf (RefOf (AUIH))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01)
            }

            Store ((B606 % DerefOf (PAUI [0x10])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((B606 % DerefOf (PAUI [0x11])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01)
            /* Method returns Integer */

            Store ((B606 % M601 (0x01, 0x10)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((B606 % M601 (0x01, 0x11)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B606 % DerefOf (M602 (0x01, 0x10, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((B606 % DerefOf (M602 (0x01, 0x11, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01)
            }

            Local0 = (B606 % 0x0322)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (B606 % 0x0320)
            M600 (Arg0, 0x0D, Local0, 0x01)
            Local0 = (B606 % AUIG) /* \AUIG */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (B606 % AUIH) /* \AUIH */
            M600 (Arg0, 0x0F, Local0, 0x01)
            If (Y078)
            {
                Local0 = (B606 % DerefOf (RefOf (AUIG)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (B606 % DerefOf (RefOf (AUIH)))
                M600 (Arg0, 0x11, Local0, 0x01)
            }

            Local0 = (B606 % DerefOf (PAUI [0x10]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (B606 % DerefOf (PAUI [0x11]))
            M600 (Arg0, 0x13, Local0, 0x01)
            /* Method returns Integer */

            Local0 = (B606 % M601 (0x01, 0x10))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (B606 % M601 (0x01, 0x11))
            M600 (Arg0, 0x15, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B606 % DerefOf (M602 (0x01, 0x10, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (B606 % DerefOf (M602 (0x01, 0x11, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x01)
            }

            /* Conversion of the second operand */

            Store ((0x0322 % B606), Local0)
            M600 (Arg0, 0x18, Local0, 0x01)
            Store ((0x0320 % B606), Local0)
            M600 (Arg0, 0x19, Local0, 0x0320)
            Store ((AUIG % B606), Local0)
            M600 (Arg0, 0x1A, Local0, 0x01)
            Store ((AUIH % B606), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0320)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUIG)) % B606), Local0)
                M600 (Arg0, 0x1C, Local0, 0x01)
                Store ((DerefOf (RefOf (AUIH)) % B606), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0320)
            }

            Store ((DerefOf (PAUI [0x10]) % B606), Local0)
            M600 (Arg0, 0x1E, Local0, 0x01)
            Store ((DerefOf (PAUI [0x11]) % B606), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0320)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x10) % B606), Local0)
            M600 (Arg0, 0x20, Local0, 0x01)
            Store ((M601 (0x01, 0x11) % B606), Local0)
            M600 (Arg0, 0x21, Local0, 0x0320)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x10, 0x01)) % B606), Local0)
                M600 (Arg0, 0x22, Local0, 0x01)
                Store ((DerefOf (M602 (0x01, 0x11, 0x01)) % B606), Local0)
                M600 (Arg0, 0x23, Local0, 0x0320)
            }

            Local0 = (0x0322 % B606) /* \M613.M044.B606 */
            M600 (Arg0, 0x24, Local0, 0x01)
            Local0 = (0x0320 % B606) /* \M613.M044.B606 */
            M600 (Arg0, 0x25, Local0, 0x0320)
            Local0 = (AUIG % B606) /* \M613.M044.B606 */
            M600 (Arg0, 0x26, Local0, 0x01)
            Local0 = (AUIH % B606) /* \M613.M044.B606 */
            M600 (Arg0, 0x27, Local0, 0x0320)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUIG)) % B606) /* \M613.M044.B606 */
                M600 (Arg0, 0x28, Local0, 0x01)
                Local0 = (DerefOf (RefOf (AUIH)) % B606) /* \M613.M044.B606 */
                M600 (Arg0, 0x29, Local0, 0x0320)
            }

            Local0 = (DerefOf (PAUI [0x10]) % B606) /* \M613.M044.B606 */
            M600 (Arg0, 0x2A, Local0, 0x01)
            Local0 = (DerefOf (PAUI [0x11]) % B606) /* \M613.M044.B606 */
            M600 (Arg0, 0x2B, Local0, 0x0320)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x10) % B606) /* \M613.M044.B606 */
            M600 (Arg0, 0x2C, Local0, 0x01)
            Local0 = (M601 (0x01, 0x11) % B606) /* \M613.M044.B606 */
            M600 (Arg0, 0x2D, Local0, 0x0320)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) % B606) /* \M613.M044.B606 */
                M600 (Arg0, 0x2E, Local0, 0x01)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) % B606) /* \M613.M044.B606 */
                M600 (Arg0, 0x2F, Local0, 0x0320)
            }
        }

        /* Mod, 64-bit */

        Method (M045, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A % 0xFE7CB391D650A285), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((B60A % 0xFE7CB391D650A283), Local0)
            M600 (Arg0, 0x01, Local0, 0x01)
            Store ((B60A % AUID), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((B60A % AUIF), Local0)
            M600 (Arg0, 0x03, Local0, 0x01)
            If (Y078)
            {
                Store ((B60A % DerefOf (RefOf (AUID))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((B60A % DerefOf (RefOf (AUIF))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01)
            }

            Store ((B60A % DerefOf (PAUI [0x0D])), Local0)
            M600 (Arg0, 0x0D, Local0, 0xFE7CB391D650A284)
            Store ((B60A % DerefOf (PAUI [0x0F])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01)
            /* Method returns Integer */

            Store ((B60A % M601 (0x01, 0x0D)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((B60A % M601 (0x01, 0x0F)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A % DerefOf (M602 (0x01, 0x0D, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((B60A % DerefOf (M602 (0x01, 0x0F, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01)
            }

            Local0 = (B60A % 0xFE7CB391D650A285)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A % 0xFE7CB391D650A283)
            M600 (Arg0, 0x0D, Local0, 0x01)
            Local0 = (B60A % AUID) /* \AUID */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A % AUIF) /* \AUIF */
            M600 (Arg0, 0x0F, Local0, 0x01)
            If (Y078)
            {
                Local0 = (B60A % DerefOf (RefOf (AUID)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (B60A % DerefOf (RefOf (AUIF)))
                M600 (Arg0, 0x11, Local0, 0x01)
            }

            Local0 = (B60A % DerefOf (PAUI [0x0D]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A % DerefOf (PAUI [0x0F]))
            M600 (Arg0, 0x13, Local0, 0x01)
            /* Method returns Integer */

            Local0 = (B60A % M601 (0x01, 0x0D))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A % M601 (0x01, 0x0F))
            M600 (Arg0, 0x15, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A % DerefOf (M602 (0x01, 0x0D, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (B60A % DerefOf (M602 (0x01, 0x0F, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x01)
            }

            /* Conversion of the second operand */

            Store ((0xFE7CB391D650A285 % B60A), Local0)
            M600 (Arg0, 0x18, Local0, 0x01)
            Store ((0xFE7CB391D650A283 % B60A), Local0)
            M600 (Arg0, 0x19, Local0, 0xFE7CB391D650A283)
            Store ((AUID % B60A), Local0)
            M600 (Arg0, 0x1A, Local0, 0x01)
            Store ((AUIF % B60A), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFE7CB391D650A283)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUID)) % B60A), Local0)
                M600 (Arg0, 0x1C, Local0, 0x01)
                Store ((DerefOf (RefOf (AUIF)) % B60A), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFE7CB391D650A283)
            }

            Store ((DerefOf (PAUI [0x0D]) % B60A), Local0)
            M600 (Arg0, 0x1E, Local0, 0x01)
            Store ((DerefOf (PAUI [0x0F]) % B60A), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFE7CB391D650A283)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x0D) % B60A), Local0)
            M600 (Arg0, 0x20, Local0, 0x01)
            Store ((M601 (0x01, 0x0F) % B60A), Local0)
            M600 (Arg0, 0x21, Local0, 0xFE7CB391D650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x0D, 0x01)) % B60A), Local0)
                M600 (Arg0, 0x22, Local0, 0x01)
                Store ((DerefOf (M602 (0x01, 0x0F, 0x01)) % B60A), Local0)
                M600 (Arg0, 0x23, Local0, 0xFE7CB391D650A283)
            }

            Local0 = (0xFE7CB391D650A285 % B60A) /* \M613.M045.B60A */
            M600 (Arg0, 0x24, Local0, 0x01)
            Local0 = (0xFE7CB391D650A283 % B60A) /* \M613.M045.B60A */
            M600 (Arg0, 0x25, Local0, 0xFE7CB391D650A283)
            Local0 = (AUID % B60A) /* \M613.M045.B60A */
            M600 (Arg0, 0x26, Local0, 0x01)
            Local0 = (AUIF % B60A) /* \M613.M045.B60A */
            M600 (Arg0, 0x27, Local0, 0xFE7CB391D650A283)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUID)) % B60A) /* \M613.M045.B60A */
                M600 (Arg0, 0x28, Local0, 0x01)
                Local0 = (DerefOf (RefOf (AUIF)) % B60A) /* \M613.M045.B60A */
                M600 (Arg0, 0x29, Local0, 0xFE7CB391D650A283)
            }

            Local0 = (DerefOf (PAUI [0x0D]) % B60A) /* \M613.M045.B60A */
            M600 (Arg0, 0x2A, Local0, 0x01)
            Local0 = (DerefOf (PAUI [0x0F]) % B60A) /* \M613.M045.B60A */
            M600 (Arg0, 0x2B, Local0, 0xFE7CB391D650A283)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x0D) % B60A) /* \M613.M045.B60A */
            M600 (Arg0, 0x2C, Local0, 0x01)
            Local0 = (M601 (0x01, 0x0F) % B60A) /* \M613.M045.B60A */
            M600 (Arg0, 0x2D, Local0, 0xFE7CB391D650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) % B60A) /* \M613.M045.B60A */
                M600 (Arg0, 0x2E, Local0, 0x01)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) % B60A) /* \M613.M045.B60A */
                M600 (Arg0, 0x2F, Local0, 0xFE7CB391D650A283)
            }

            /* Conversion of the both operands */

            Store ((B606 % B60A), Local0)
            M600 (Arg0, 0x30, Local0, 0x0321)
            Store ((B60A % B606), Local0)
            M600 (Arg0, 0x31, Local0, 0x02FD)
            Local0 = (B606 % B60A) /* \M613.M045.B60A */
            M600 (Arg0, 0x32, Local0, 0x0321)
            Local0 = (B60A % B606) /* \M613.M045.B606 */
            M600 (Arg0, 0x33, Local0, 0x02FD)
        }

        /* Mod, 32-bit */

        Method (M046, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A % 0xD650A285), Local0)
            M600 (Arg0, 0x00, Local0, 0xD650A284)
            Store ((B60A % 0xD650A283), Local0)
            M600 (Arg0, 0x01, Local0, 0x01)
            Store ((B60A % AUIL), Local0)
            M600 (Arg0, 0x02, Local0, 0xD650A284)
            Store ((B60A % AUIM), Local0)
            M600 (Arg0, 0x0E, Local0, 0x01)
            If (Y078)
            {
                Store ((B60A % DerefOf (RefOf (AUIL))), Local0)
                M600 (Arg0, 0x04, Local0, 0xD650A284)
                Store ((B60A % DerefOf (RefOf (AUIM))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01)
            }

            Store ((B60A % DerefOf (PAUI [0x15])), Local0)
            M600 (Arg0, 0x0C, Local0, 0xD650A284)
            Store ((B60A % DerefOf (PAUI [0x16])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01)
            /* Method returns Integer */

            Store ((B60A % M601 (0x01, 0x15)), Local0)
            M600 (Arg0, 0x08, Local0, 0xD650A284)
            Store ((B60A % M601 (0x01, 0x16)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A % DerefOf (M602 (0x01, 0x15, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xD650A284)
                Store ((B60A % DerefOf (M602 (0x01, 0x16, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01)
            }

            Local0 = (B60A % 0xD650A285)
            M600 (Arg0, 0x0C, Local0, 0xD650A284)
            Local0 = (B60A % 0xD650A283)
            M600 (Arg0, 0x0D, Local0, 0x01)
            Local0 = (B60A % AUIL) /* \AUIL */
            M600 (Arg0, 0x0E, Local0, 0xD650A284)
            Local0 = (B60A % AUIM) /* \AUIM */
            M600 (Arg0, 0x0F, Local0, 0x01)
            If (Y078)
            {
                Local0 = (B60A % DerefOf (RefOf (AUIL)))
                M600 (Arg0, 0x10, Local0, 0xD650A284)
                Local0 = (B60A % DerefOf (RefOf (AUIM)))
                M600 (Arg0, 0x11, Local0, 0x01)
            }

            Local0 = (B60A % DerefOf (PAUI [0x15]))
            M600 (Arg0, 0x12, Local0, 0xD650A284)
            Local0 = (B60A % DerefOf (PAUI [0x16]))
            M600 (Arg0, 0x13, Local0, 0x01)
            /* Method returns Integer */

            Local0 = (B60A % M601 (0x01, 0x15))
            M600 (Arg0, 0x14, Local0, 0xD650A284)
            Local0 = (B60A % M601 (0x01, 0x16))
            M600 (Arg0, 0x15, Local0, 0x01)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A % DerefOf (M602 (0x01, 0x15, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xD650A284)
                Local0 = (B60A % DerefOf (M602 (0x01, 0x16, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x01)
            }

            /* Conversion of the second operand */

            Store ((0xD650A285 % B60A), Local0)
            M600 (Arg0, 0x18, Local0, 0x01)
            Store ((0xD650A283 % B60A), Local0)
            M600 (Arg0, 0x19, Local0, 0xD650A283)
            Store ((AUIL % B60A), Local0)
            M600 (Arg0, 0x1A, Local0, 0x01)
            Store ((AUIM % B60A), Local0)
            M600 (Arg0, 0x1B, Local0, 0xD650A283)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUIL)) % B60A), Local0)
                M600 (Arg0, 0x1C, Local0, 0x01)
                Store ((DerefOf (RefOf (AUIM)) % B60A), Local0)
                M600 (Arg0, 0x1D, Local0, 0xD650A283)
            }

            Store ((DerefOf (PAUI [0x15]) % B60A), Local0)
            M600 (Arg0, 0x1E, Local0, 0x01)
            Store ((DerefOf (PAUI [0x16]) % B60A), Local0)
            M600 (Arg0, 0x1F, Local0, 0xD650A283)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x15) % B60A), Local0)
            M600 (Arg0, 0x20, Local0, 0x01)
            Store ((M601 (0x01, 0x16) % B60A), Local0)
            M600 (Arg0, 0x21, Local0, 0xD650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x15, 0x01)) % B60A), Local0)
                M600 (Arg0, 0x22, Local0, 0x01)
                Store ((DerefOf (M602 (0x01, 0x16, 0x01)) % B60A), Local0)
                M600 (Arg0, 0x23, Local0, 0xD650A283)
            }

            Local0 = (0xD650A285 % B60A) /* \M613.M046.B60A */
            M600 (Arg0, 0x24, Local0, 0x01)
            Local0 = (0xD650A283 % B60A) /* \M613.M046.B60A */
            M600 (Arg0, 0x25, Local0, 0xD650A283)
            Local0 = (AUIL % B60A) /* \M613.M046.B60A */
            M600 (Arg0, 0x26, Local0, 0x01)
            Local0 = (AUIM % B60A) /* \M613.M046.B60A */
            M600 (Arg0, 0x27, Local0, 0xD650A283)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUIL)) % B60A) /* \M613.M046.B60A */
                M600 (Arg0, 0x28, Local0, 0x01)
                Local0 = (DerefOf (RefOf (AUIM)) % B60A) /* \M613.M046.B60A */
                M600 (Arg0, 0x29, Local0, 0xD650A283)
            }

            Local0 = (DerefOf (PAUI [0x15]) % B60A) /* \M613.M046.B60A */
            M600 (Arg0, 0x2A, Local0, 0x01)
            Local0 = (DerefOf (PAUI [0x16]) % B60A) /* \M613.M046.B60A */
            M600 (Arg0, 0x2B, Local0, 0xD650A283)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x15) % B60A) /* \M613.M046.B60A */
            M600 (Arg0, 0x2C, Local0, 0x01)
            Local0 = (M601 (0x01, 0x16) % B60A) /* \M613.M046.B60A */
            M600 (Arg0, 0x2D, Local0, 0xD650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x15, 0x01)) % B60A) /* \M613.M046.B60A */
                M600 (Arg0, 0x2E, Local0, 0x01)
                Local0 = (DerefOf (M602 (0x01, 0x16, 0x01)) % B60A) /* \M613.M046.B60A */
                M600 (Arg0, 0x2F, Local0, 0xD650A283)
            }

            /* Conversion of the both operands */

            Store ((B606 % B60A), Local0)
            M600 (Arg0, 0x30, Local0, 0x0321)
            Store ((B60A % B606), Local0)
            M600 (Arg0, 0x31, Local0, 0x0261)
            Local0 = (B606 % B60A) /* \M613.M046.B60A */
            M600 (Arg0, 0x32, Local0, 0x0321)
            Local0 = (B60A % B606) /* \M613.M046.B606 */
            M600 (Arg0, 0x33, Local0, 0x0261)
        }

        /* Multiply, common 32-bit/64-bit test */

        Method (M047, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            /* Conversion of the first operand */

            Store ((B606 * 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x00)
            Store ((B606 * 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x0321)
            Store ((B606 * AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x00)
            Store ((B606 * AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x0321)
            If (Y078)
            {
                Store ((B606 * DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x00)
                Store ((B606 * DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x0321)
            }

            Store ((B606 * DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x00)
            Store ((B606 * DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x0321)
            /* Method returns Integer */

            Store ((B606 * M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x00)
            Store ((B606 * M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B606 * DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x00)
                Store ((B606 * DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x0321)
            }

            Local0 = (B606 * 0x00)
            M600 (Arg0, 0x0C, Local0, 0x00)
            Local0 = (B606 * 0x01)
            M600 (Arg0, 0x0D, Local0, 0x0321)
            Local0 = (B606 * AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x00)
            Local0 = (B606 * AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x0321)
            If (Y078)
            {
                Local0 = (B606 * DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x00)
                Local0 = (B606 * DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x0321)
            }

            Local0 = (B606 * DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x00)
            Local0 = (B606 * DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x0321)
            /* Method returns Integer */

            Local0 = (B606 * M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x00)
            Local0 = (B606 * M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B606 * DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x00)
                Local0 = (B606 * DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x0321)
            }

            /* Conversion of the second operand */

            Store ((0x00 * B606), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x01 * B606), Local0)
            M600 (Arg0, 0x19, Local0, 0x0321)
            Store ((AUI5 * B606), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI6 * B606), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0321)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) * B606), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI6)) * B606), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0321)
            }

            Store ((DerefOf (PAUI [0x05]) * B606), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x06]) * B606), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0321)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) * B606), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x06) * B606), Local0)
            M600 (Arg0, 0x21, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) * B606), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) * B606), Local0)
                M600 (Arg0, 0x23, Local0, 0x0321)
            }

            Local0 = (0x00 * B606) /* \M613.M047.B606 */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0x01 * B606) /* \M613.M047.B606 */
            M600 (Arg0, 0x25, Local0, 0x0321)
            Local0 = (AUI5 * B606) /* \M613.M047.B606 */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI6 * B606) /* \M613.M047.B606 */
            M600 (Arg0, 0x27, Local0, 0x0321)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) * B606) /* \M613.M047.B606 */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI6)) * B606) /* \M613.M047.B606 */
                M600 (Arg0, 0x29, Local0, 0x0321)
            }

            Local0 = (DerefOf (PAUI [0x05]) * B606) /* \M613.M047.B606 */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x06]) * B606) /* \M613.M047.B606 */
            M600 (Arg0, 0x2B, Local0, 0x0321)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) * B606) /* \M613.M047.B606 */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x06) * B606) /* \M613.M047.B606 */
            M600 (Arg0, 0x2D, Local0, 0x0321)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) * B606) /* \M613.M047.B606 */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) * B606) /* \M613.M047.B606 */
                M600 (Arg0, 0x2F, Local0, 0x0321)
            }
        }

        /* Multiply, 64-bit */

        Method (M048, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A * 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x00)
            Store ((B60A * 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xFE7CB391D650A284)
            Store ((B60A * AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x00)
            Store ((B60A * AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Store ((B60A * DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x00)
                Store ((B60A * DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFE7CB391D650A284)
            }

            Store ((B60A * DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x00)
            Store ((B60A * DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Store ((B60A * M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x00)
            Store ((B60A * M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A * DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x00)
                Store ((B60A * DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (B60A * 0x00)
            M600 (Arg0, 0x0C, Local0, 0x00)
            Local0 = (B60A * 0x01)
            M600 (Arg0, 0x0D, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A * AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x00)
            Local0 = (B60A * AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Local0 = (B60A * DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x00)
                Local0 = (B60A * DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (B60A * DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x00)
            Local0 = (B60A * DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Local0 = (B60A * M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x00)
            Local0 = (B60A * M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A * DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x00)
                Local0 = (B60A * DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFE7CB391D650A284)
            }

            /* Conversion of the second operand */

            Store ((0x00 * B60A), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x01 * B60A), Local0)
            M600 (Arg0, 0x19, Local0, 0xFE7CB391D650A284)
            Store ((AUI5 * B60A), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI6 * B60A), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) * B60A), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI6)) * B60A), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFE7CB391D650A284)
            }

            Store ((DerefOf (PAUI [0x05]) * B60A), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x06]) * B60A), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) * B60A), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x06) * B60A), Local0)
            M600 (Arg0, 0x21, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) * B60A), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) * B60A), Local0)
                M600 (Arg0, 0x23, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (0x00 * B60A) /* \M613.M048.B60A */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0x01 * B60A) /* \M613.M048.B60A */
            M600 (Arg0, 0x25, Local0, 0xFE7CB391D650A284)
            Local0 = (AUI5 * B60A) /* \M613.M048.B60A */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI6 * B60A) /* \M613.M048.B60A */
            M600 (Arg0, 0x27, Local0, 0xFE7CB391D650A284)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) * B60A) /* \M613.M048.B60A */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI6)) * B60A) /* \M613.M048.B60A */
                M600 (Arg0, 0x29, Local0, 0xFE7CB391D650A284)
            }

            Local0 = (DerefOf (PAUI [0x05]) * B60A) /* \M613.M048.B60A */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x06]) * B60A) /* \M613.M048.B60A */
            M600 (Arg0, 0x2B, Local0, 0xFE7CB391D650A284)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) * B60A) /* \M613.M048.B60A */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x06) * B60A) /* \M613.M048.B60A */
            M600 (Arg0, 0x2D, Local0, 0xFE7CB391D650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) * B60A) /* \M613.M048.B60A */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) * B60A) /* \M613.M048.B60A */
                M600 (Arg0, 0x2F, Local0, 0xFE7CB391D650A284)
            }

            /* Conversion of the both operands */

            Store ((B606 * B60A), Local0)
            M600 (Arg0, 0x30, Local0, 0x442DDB4F924C7F04)
            Store ((B60A * B606), Local0)
            M600 (Arg0, 0x31, Local0, 0x442DDB4F924C7F04)
            Local0 = (B606 * B60A) /* \M613.M048.B60A */
            M600 (Arg0, 0x32, Local0, 0x442DDB4F924C7F04)
            Local0 = (B60A * B606) /* \M613.M048.B606 */
            M600 (Arg0, 0x33, Local0, 0x442DDB4F924C7F04)
        }

        /* Multiply, 32-bit */

        Method (M049, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A * 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x00)
            Store ((B60A * 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xD650A284)
            Store ((B60A * AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x00)
            Store ((B60A * AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xD650A284)
            If (Y078)
            {
                Store ((B60A * DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x00)
                Store ((B60A * DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xD650A284)
            }

            Store ((B60A * DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x00)
            Store ((B60A * DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xD650A284)
            /* Method returns Integer */

            Store ((B60A * M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x00)
            Store ((B60A * M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xD650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A * DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x00)
                Store ((B60A * DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xD650A284)
            }

            Local0 = (B60A * 0x00)
            M600 (Arg0, 0x0C, Local0, 0x00)
            Local0 = (B60A * 0x01)
            M600 (Arg0, 0x0D, Local0, 0xD650A284)
            Local0 = (B60A * AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x00)
            Local0 = (B60A * AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xD650A284)
            If (Y078)
            {
                Local0 = (B60A * DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x00)
                Local0 = (B60A * DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xD650A284)
            }

            Local0 = (B60A * DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x00)
            Local0 = (B60A * DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xD650A284)
            /* Method returns Integer */

            Local0 = (B60A * M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x00)
            Local0 = (B60A * M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xD650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A * DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x00)
                Local0 = (B60A * DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xD650A284)
            }

            /* Conversion of the second operand */

            Store ((0x00 * B60A), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x01 * B60A), Local0)
            M600 (Arg0, 0x19, Local0, 0xD650A284)
            Store ((AUI5 * B60A), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI6 * B60A), Local0)
            M600 (Arg0, 0x1B, Local0, 0xD650A284)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) * B60A), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI6)) * B60A), Local0)
                M600 (Arg0, 0x1D, Local0, 0xD650A284)
            }

            Store ((DerefOf (PAUI [0x05]) * B60A), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x06]) * B60A), Local0)
            M600 (Arg0, 0x1F, Local0, 0xD650A284)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) * B60A), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x06) * B60A), Local0)
            M600 (Arg0, 0x21, Local0, 0xD650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) * B60A), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) * B60A), Local0)
                M600 (Arg0, 0x23, Local0, 0xD650A284)
            }

            Local0 = (0x00 * B60A) /* \M613.M049.B60A */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0x01 * B60A) /* \M613.M049.B60A */
            M600 (Arg0, 0x25, Local0, 0xD650A284)
            Local0 = (AUI5 * B60A) /* \M613.M049.B60A */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI6 * B60A) /* \M613.M049.B60A */
            M600 (Arg0, 0x27, Local0, 0xD650A284)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) * B60A) /* \M613.M049.B60A */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI6)) * B60A) /* \M613.M049.B60A */
                M600 (Arg0, 0x29, Local0, 0xD650A284)
            }

            Local0 = (DerefOf (PAUI [0x05]) * B60A) /* \M613.M049.B60A */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x06]) * B60A) /* \M613.M049.B60A */
            M600 (Arg0, 0x2B, Local0, 0xD650A284)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) * B60A) /* \M613.M049.B60A */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x06) * B60A) /* \M613.M049.B60A */
            M600 (Arg0, 0x2D, Local0, 0xD650A284)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) * B60A) /* \M613.M049.B60A */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) * B60A) /* \M613.M049.B60A */
                M600 (Arg0, 0x2F, Local0, 0xD650A284)
            }

            /* Conversion of the both operands */

            Store ((B606 * B60A), Local0)
            M600 (Arg0, 0x30, Local0, 0x924C7F04)
            Store ((B60A * B606), Local0)
            M600 (Arg0, 0x31, Local0, 0x924C7F04)
            Local0 = (B606 * B60A) /* \M613.M049.B60A */
            M600 (Arg0, 0x32, Local0, 0x924C7F04)
            Local0 = (B60A * B606) /* \M613.M049.B606 */
            M600 (Arg0, 0x33, Local0, 0x924C7F04)
        }

        /* NAnd, common 32-bit/64-bit test */

        Method (M04A, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            /* Conversion of the first operand */

            Local0 = NAnd (B606, 0x00)
            M600 (Arg0, 0x00, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (B606, 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x01, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NAnd (B606, AUI5)
            M600 (Arg0, 0x02, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (B606, AUIJ)
            M600 (Arg0, 0x03, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                Local0 = NAnd (B606, DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (B606, DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x05, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Local0 = NAnd (B606, DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (B606, DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x07, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            Local0 = NAnd (B606, M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (B606, M601 (0x01, 0x13))
            M600 (Arg0, 0x09, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NAnd (B606, DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (B606, DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x0B, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            NAnd (B606, 0x00, Local0)
            M600 (Arg0, 0x0C, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (B606, 0xFFFFFFFFFFFFFFFF, Local0)
            M600 (Arg0, 0x0D, Local0, 0xFFFFFFFFFFFFFCDE)
            NAnd (B606, AUI5, Local0)
            M600 (Arg0, 0x0E, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (B606, AUIJ, Local0)
            M600 (Arg0, 0x0F, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                NAnd (B606, DerefOf (RefOf (AUI5)), Local0)
                M600 (Arg0, 0x10, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (B606, DerefOf (RefOf (AUIJ)), Local0)
                M600 (Arg0, 0x11, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            NAnd (B606, DerefOf (PAUI [0x05]), Local0)
            M600 (Arg0, 0x12, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (B606, DerefOf (PAUI [0x13]), Local0)
            M600 (Arg0, 0x13, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            NAnd (B606, M601 (0x01, 0x05), Local0)
            M600 (Arg0, 0x14, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (B606, M601 (0x01, 0x13), Local0)
            M600 (Arg0, 0x15, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NAnd (B606, DerefOf (M602 (0x01, 0x05, 0x01)), Local0)
                M600 (Arg0, 0x16, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (B606, DerefOf (M602 (0x01, 0x13, 0x01)), Local0)
                M600 (Arg0, 0x17, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            /* Conversion of the second operand */

            Local0 = NAnd (0x00, B606)
            M600 (Arg0, 0x18, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (0xFFFFFFFFFFFFFFFF, B606)
            M600 (Arg0, 0x19, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NAnd (AUI5, B606)
            M600 (Arg0, 0x1A, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (AUIJ, B606)
            M600 (Arg0, 0x1B, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                Local0 = NAnd (DerefOf (RefOf (AUI5)), B606)
                M600 (Arg0, 0x1C, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (DerefOf (RefOf (AUIJ)), B606)
                M600 (Arg0, 0x1D, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Local0 = NAnd (DerefOf (PAUI [0x05]), B606)
            M600 (Arg0, 0x1E, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (DerefOf (PAUI [0x13]), B606)
            M600 (Arg0, 0x1F, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            Local0 = NAnd (M601 (0x01, 0x05), B606)
            M600 (Arg0, 0x20, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (M601 (0x01, 0x13), B606)
            M600 (Arg0, 0x21, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NAnd (DerefOf (M602 (0x01, 0x05, 0x01)), B606)
                M600 (Arg0, 0x22, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (DerefOf (M602 (0x01, 0x13, 0x01)), B606)
                M600 (Arg0, 0x23, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            NAnd (0x00, B606, Local0)
            M600 (Arg0, 0x24, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (0xFFFFFFFFFFFFFFFF, B606, Local0)
            M600 (Arg0, 0x25, Local0, 0xFFFFFFFFFFFFFCDE)
            NAnd (AUI5, B606, Local0)
            M600 (Arg0, 0x26, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (AUIJ, B606, Local0)
            M600 (Arg0, 0x27, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                NAnd (DerefOf (RefOf (AUI5)), B606, Local0)
                M600 (Arg0, 0x28, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (DerefOf (RefOf (AUIJ)), B606, Local0)
                M600 (Arg0, 0x29, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            NAnd (DerefOf (PAUI [0x05]), B606, Local0)
            M600 (Arg0, 0x2A, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (DerefOf (PAUI [0x13]), B606, Local0)
            M600 (Arg0, 0x2B, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            NAnd (M601 (0x01, 0x05), B606, Local0)
            M600 (Arg0, 0x2C, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (M601 (0x01, 0x13), B606, Local0)
            M600 (Arg0, 0x2D, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NAnd (DerefOf (M602 (0x01, 0x05, 0x01)), B606, Local0)
                M600 (Arg0, 0x2E, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (DerefOf (M602 (0x01, 0x13, 0x01)), B606, Local0)
                M600 (Arg0, 0x2F, Local0, 0xFFFFFFFFFFFFFCDE)
            }
        }

        /* NAnd, 64-bit */

        Method (M04B, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Local0 = NAnd (B60A, 0x00)
            M600 (Arg0, 0x00, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (B60A, 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x01, Local0, 0x01834C6E29AF5D7B)
            Local0 = NAnd (B60A, AUI5)
            M600 (Arg0, 0x02, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (B60A, AUIJ)
            M600 (Arg0, 0x03, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                Local0 = NAnd (B60A, DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (B60A, DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x05, Local0, 0x01834C6E29AF5D7B)
            }

            Local0 = NAnd (B60A, DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (B60A, DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x07, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            Local0 = NAnd (B60A, M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (B60A, M601 (0x01, 0x13))
            M600 (Arg0, 0x09, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NAnd (B60A, DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (B60A, DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x0B, Local0, 0x01834C6E29AF5D7B)
            }

            NAnd (B60A, 0x00, Local0)
            M600 (Arg0, 0x0C, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (B60A, 0xFFFFFFFFFFFFFFFF, Local0)
            M600 (Arg0, 0x0D, Local0, 0x01834C6E29AF5D7B)
            NAnd (B60A, AUI5, Local0)
            M600 (Arg0, 0x0E, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (B60A, AUIJ, Local0)
            M600 (Arg0, 0x0F, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                NAnd (B60A, DerefOf (RefOf (AUI5)), Local0)
                M600 (Arg0, 0x10, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (B60A, DerefOf (RefOf (AUIJ)), Local0)
                M600 (Arg0, 0x11, Local0, 0x01834C6E29AF5D7B)
            }

            NAnd (B60A, DerefOf (PAUI [0x05]), Local0)
            M600 (Arg0, 0x12, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (B60A, DerefOf (PAUI [0x13]), Local0)
            M600 (Arg0, 0x13, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            NAnd (B60A, M601 (0x01, 0x05), Local0)
            M600 (Arg0, 0x14, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (B60A, M601 (0x01, 0x13), Local0)
            M600 (Arg0, 0x15, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NAnd (B60A, DerefOf (M602 (0x01, 0x05, 0x01)), Local0)
                M600 (Arg0, 0x16, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (B60A, DerefOf (M602 (0x01, 0x13, 0x01)), Local0)
                M600 (Arg0, 0x17, Local0, 0x01834C6E29AF5D7B)
            }

            /* Conversion of the second operand */

            Local0 = NAnd (0x00, B60A)
            M600 (Arg0, 0x18, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (0xFFFFFFFFFFFFFFFF, B60A)
            M600 (Arg0, 0x19, Local0, 0x01834C6E29AF5D7B)
            Local0 = NAnd (AUI5, B60A)
            M600 (Arg0, 0x1A, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (AUIJ, B60A)
            M600 (Arg0, 0x1B, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                Local0 = NAnd (DerefOf (RefOf (AUI5)), B60A)
                M600 (Arg0, 0x1C, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (DerefOf (RefOf (AUIJ)), B60A)
                M600 (Arg0, 0x1D, Local0, 0x01834C6E29AF5D7B)
            }

            Local0 = NAnd (DerefOf (PAUI [0x05]), B60A)
            M600 (Arg0, 0x1E, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (DerefOf (PAUI [0x13]), B60A)
            M600 (Arg0, 0x1F, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            Local0 = NAnd (M601 (0x01, 0x05), B60A)
            M600 (Arg0, 0x20, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = NAnd (M601 (0x01, 0x13), B60A)
            M600 (Arg0, 0x21, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NAnd (DerefOf (M602 (0x01, 0x05, 0x01)), B60A)
                M600 (Arg0, 0x22, Local0, 0xFFFFFFFFFFFFFFFF)
                Local0 = NAnd (DerefOf (M602 (0x01, 0x13, 0x01)), B60A)
                M600 (Arg0, 0x23, Local0, 0x01834C6E29AF5D7B)
            }

            NAnd (0x00, B60A, Local0)
            M600 (Arg0, 0x24, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (0xFFFFFFFFFFFFFFFF, B60A, Local0)
            M600 (Arg0, 0x25, Local0, 0x01834C6E29AF5D7B)
            NAnd (AUI5, B60A, Local0)
            M600 (Arg0, 0x26, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (AUIJ, B60A, Local0)
            M600 (Arg0, 0x27, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                NAnd (DerefOf (RefOf (AUI5)), B60A, Local0)
                M600 (Arg0, 0x28, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (DerefOf (RefOf (AUIJ)), B60A, Local0)
                M600 (Arg0, 0x29, Local0, 0x01834C6E29AF5D7B)
            }

            NAnd (DerefOf (PAUI [0x05]), B60A, Local0)
            M600 (Arg0, 0x2A, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (DerefOf (PAUI [0x13]), B60A, Local0)
            M600 (Arg0, 0x2B, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            NAnd (M601 (0x01, 0x05), B60A, Local0)
            M600 (Arg0, 0x2C, Local0, 0xFFFFFFFFFFFFFFFF)
            NAnd (M601 (0x01, 0x13), B60A, Local0)
            M600 (Arg0, 0x2D, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NAnd (DerefOf (M602 (0x01, 0x05, 0x01)), B60A, Local0)
                M600 (Arg0, 0x2E, Local0, 0xFFFFFFFFFFFFFFFF)
                NAnd (DerefOf (M602 (0x01, 0x13, 0x01)), B60A, Local0)
                M600 (Arg0, 0x2F, Local0, 0x01834C6E29AF5D7B)
            }

            /* Conversion of the both operands */

            Local0 = NAnd (B606, B60A)
            M600 (Arg0, 0x30, Local0, 0xFFFFFFFFFFFFFDFF)
            Local0 = NAnd (B60A, B606)
            M600 (Arg0, 0x31, Local0, 0xFFFFFFFFFFFFFDFF)
            NAnd (B606, B60A, Local0)
            M600 (Arg0, 0x32, Local0, 0xFFFFFFFFFFFFFDFF)
            NAnd (B60A, B606, Local0)
            M600 (Arg0, 0x33, Local0, 0xFFFFFFFFFFFFFDFF)
        }

        /* NAnd, 32-bit */

        Method (M04C, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Local0 = NAnd (B60A, 0x00)
            M600 (Arg0, 0x00, Local0, 0xFFFFFFFF)
            Local0 = NAnd (B60A, 0xFFFFFFFF)
            M600 (Arg0, 0x01, Local0, 0x29AF5D7B)
            Local0 = NAnd (B60A, AUI5)
            M600 (Arg0, 0x02, Local0, 0xFFFFFFFF)
            Local0 = NAnd (B60A, AUII)
            M600 (Arg0, 0x03, Local0, 0x29AF5D7B)
            If (Y078)
            {
                Local0 = NAnd (B60A, DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, 0xFFFFFFFF)
                Local0 = NAnd (B60A, DerefOf (RefOf (AUII)))
                M600 (Arg0, 0x05, Local0, 0x29AF5D7B)
            }

            Local0 = NAnd (B60A, DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, 0xFFFFFFFF)
            Local0 = NAnd (B60A, DerefOf (PAUI [0x12]))
            M600 (Arg0, 0x07, Local0, 0x29AF5D7B)
            /* Method returns Integer */

            Local0 = NAnd (B60A, M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, 0xFFFFFFFF)
            Local0 = NAnd (B60A, M601 (0x01, 0x12))
            M600 (Arg0, 0x09, Local0, 0x29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NAnd (B60A, DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, 0xFFFFFFFF)
                Local0 = NAnd (B60A, DerefOf (M602 (0x01, 0x12, 0x01)))
                M600 (Arg0, 0x0B, Local0, 0x29AF5D7B)
            }

            NAnd (B60A, 0x00, Local0)
            M600 (Arg0, 0x0C, Local0, 0xFFFFFFFF)
            NAnd (B60A, 0xFFFFFFFF, Local0)
            M600 (Arg0, 0x0D, Local0, 0x29AF5D7B)
            NAnd (B60A, AUI5, Local0)
            M600 (Arg0, 0x0E, Local0, 0xFFFFFFFF)
            NAnd (B60A, AUII, Local0)
            M600 (Arg0, 0x0F, Local0, 0x29AF5D7B)
            If (Y078)
            {
                NAnd (B60A, DerefOf (RefOf (AUI5)), Local0)
                M600 (Arg0, 0x10, Local0, 0xFFFFFFFF)
                NAnd (B60A, DerefOf (RefOf (AUII)), Local0)
                M600 (Arg0, 0x11, Local0, 0x29AF5D7B)
            }

            NAnd (B60A, DerefOf (PAUI [0x05]), Local0)
            M600 (Arg0, 0x12, Local0, 0xFFFFFFFF)
            NAnd (B60A, DerefOf (PAUI [0x12]), Local0)
            M600 (Arg0, 0x13, Local0, 0x29AF5D7B)
            /* Method returns Integer */

            NAnd (B60A, M601 (0x01, 0x05), Local0)
            M600 (Arg0, 0x14, Local0, 0xFFFFFFFF)
            NAnd (B60A, M601 (0x01, 0x12), Local0)
            M600 (Arg0, 0x15, Local0, 0x29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NAnd (B60A, DerefOf (M602 (0x01, 0x05, 0x01)), Local0)
                M600 (Arg0, 0x16, Local0, 0xFFFFFFFF)
                NAnd (B60A, DerefOf (M602 (0x01, 0x12, 0x01)), Local0)
                M600 (Arg0, 0x17, Local0, 0x29AF5D7B)
            }

            /* Conversion of the second operand */

            Local0 = NAnd (0x00, B60A)
            M600 (Arg0, 0x18, Local0, 0xFFFFFFFF)
            Local0 = NAnd (0xFFFFFFFF, B60A)
            M600 (Arg0, 0x19, Local0, 0x29AF5D7B)
            Local0 = NAnd (AUI5, B60A)
            M600 (Arg0, 0x1A, Local0, 0xFFFFFFFF)
            Local0 = NAnd (AUII, B60A)
            M600 (Arg0, 0x1B, Local0, 0x29AF5D7B)
            If (Y078)
            {
                Local0 = NAnd (DerefOf (RefOf (AUI5)), B60A)
                M600 (Arg0, 0x1C, Local0, 0xFFFFFFFF)
                Local0 = NAnd (DerefOf (RefOf (AUII)), B60A)
                M600 (Arg0, 0x1D, Local0, 0x29AF5D7B)
            }

            Local0 = NAnd (DerefOf (PAUI [0x05]), B60A)
            M600 (Arg0, 0x1E, Local0, 0xFFFFFFFF)
            Local0 = NAnd (DerefOf (PAUI [0x12]), B60A)
            M600 (Arg0, 0x1F, Local0, 0x29AF5D7B)
            /* Method returns Integer */

            Local0 = NAnd (M601 (0x01, 0x05), B60A)
            M600 (Arg0, 0x20, Local0, 0xFFFFFFFF)
            Local0 = NAnd (M601 (0x01, 0x12), B60A)
            M600 (Arg0, 0x21, Local0, 0x29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NAnd (DerefOf (M602 (0x01, 0x05, 0x01)), B60A)
                M600 (Arg0, 0x22, Local0, 0xFFFFFFFF)
                Local0 = NAnd (DerefOf (M602 (0x01, 0x12, 0x01)), B60A)
                M600 (Arg0, 0x23, Local0, 0x29AF5D7B)
            }

            NAnd (0x00, B60A, Local0)
            M600 (Arg0, 0x24, Local0, 0xFFFFFFFF)
            NAnd (0xFFFFFFFF, B60A, Local0)
            M600 (Arg0, 0x25, Local0, 0x29AF5D7B)
            NAnd (AUI5, B60A, Local0)
            M600 (Arg0, 0x26, Local0, 0xFFFFFFFF)
            NAnd (AUII, B60A, Local0)
            M600 (Arg0, 0x27, Local0, 0x29AF5D7B)
            If (Y078)
            {
                NAnd (DerefOf (RefOf (AUI5)), B60A, Local0)
                M600 (Arg0, 0x28, Local0, 0xFFFFFFFF)
                NAnd (DerefOf (RefOf (AUII)), B60A, Local0)
                M600 (Arg0, 0x29, Local0, 0x29AF5D7B)
            }

            NAnd (DerefOf (PAUI [0x05]), B60A, Local0)
            M600 (Arg0, 0x2A, Local0, 0xFFFFFFFF)
            NAnd (DerefOf (PAUI [0x12]), B60A, Local0)
            M600 (Arg0, 0x2B, Local0, 0x29AF5D7B)
            /* Method returns Integer */

            NAnd (M601 (0x01, 0x05), B60A, Local0)
            M600 (Arg0, 0x2C, Local0, 0xFFFFFFFF)
            NAnd (M601 (0x01, 0x12), B60A, Local0)
            M600 (Arg0, 0x2D, Local0, 0x29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NAnd (DerefOf (M602 (0x01, 0x05, 0x01)), B60A, Local0)
                M600 (Arg0, 0x2E, Local0, 0xFFFFFFFF)
                NAnd (DerefOf (M602 (0x01, 0x12, 0x01)), B60A, Local0)
                M600 (Arg0, 0x2F, Local0, 0x29AF5D7B)
            }

            /* Conversion of the both operands */

            Local0 = NAnd (B606, B60A)
            M600 (Arg0, 0x30, Local0, 0xFFFFFDFF)
            Local0 = NAnd (B60A, B606)
            M600 (Arg0, 0x31, Local0, 0xFFFFFDFF)
            NAnd (B606, B60A, Local0)
            M600 (Arg0, 0x32, Local0, 0xFFFFFDFF)
            NAnd (B60A, B606, Local0)
            M600 (Arg0, 0x33, Local0, 0xFFFFFDFF)
        }

        /* NOr, common 32-bit/64-bit test */

        Method (M04D, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            /* Conversion of the first operand */

            Local0 = NOr (B606, 0x00)
            M600 (Arg0, 0x00, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (B606, 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x01, Local0, 0x00)
            Local0 = NOr (B606, AUI5)
            M600 (Arg0, 0x02, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (B606, AUIJ)
            M600 (Arg0, 0x03, Local0, 0x00)
            If (Y078)
            {
                Local0 = NOr (B606, DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, 0xFFFFFFFFFFFFFCDE)
                Local0 = NOr (B606, DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x05, Local0, 0x00)
            }

            Local0 = NOr (B606, DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (B606, DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x07, Local0, 0x00)
            /* Method returns Integer */

            Local0 = NOr (B606, M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (B606, M601 (0x01, 0x13))
            M600 (Arg0, 0x09, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NOr (B606, DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, 0xFFFFFFFFFFFFFCDE)
                Local0 = NOr (B606, DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x0B, Local0, 0x00)
            }

            NOr (B606, 0x00, Local0)
            M600 (Arg0, 0x0C, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (B606, 0xFFFFFFFFFFFFFFFF, Local0)
            M600 (Arg0, 0x0D, Local0, 0x00)
            NOr (B606, AUI5, Local0)
            M600 (Arg0, 0x0E, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (B606, AUIJ, Local0)
            M600 (Arg0, 0x0F, Local0, 0x00)
            If (Y078)
            {
                NOr (B606, DerefOf (RefOf (AUI5)), Local0)
                M600 (Arg0, 0x10, Local0, 0xFFFFFFFFFFFFFCDE)
                NOr (B606, DerefOf (RefOf (AUIJ)), Local0)
                M600 (Arg0, 0x11, Local0, 0x00)
            }

            NOr (B606, DerefOf (PAUI [0x05]), Local0)
            M600 (Arg0, 0x12, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (B606, DerefOf (PAUI [0x13]), Local0)
            M600 (Arg0, 0x13, Local0, 0x00)
            /* Method returns Integer */

            NOr (B606, M601 (0x01, 0x05), Local0)
            M600 (Arg0, 0x14, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (B606, M601 (0x01, 0x13), Local0)
            M600 (Arg0, 0x15, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NOr (B606, DerefOf (M602 (0x01, 0x05, 0x01)), Local0)
                M600 (Arg0, 0x16, Local0, 0xFFFFFFFFFFFFFCDE)
                NOr (B606, DerefOf (M602 (0x01, 0x13, 0x01)), Local0)
                M600 (Arg0, 0x17, Local0, 0x00)
            }

            /* Conversion of the second operand */

            Local0 = NOr (0x00, B606)
            M600 (Arg0, 0x18, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (0xFFFFFFFFFFFFFFFF, B606)
            M600 (Arg0, 0x19, Local0, 0x00)
            Local0 = NOr (AUI5, B606)
            M600 (Arg0, 0x1A, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (AUIJ, B606)
            M600 (Arg0, 0x1B, Local0, 0x00)
            If (Y078)
            {
                Local0 = NOr (DerefOf (RefOf (AUI5)), B606)
                M600 (Arg0, 0x1C, Local0, 0xFFFFFFFFFFFFFCDE)
                Local0 = NOr (DerefOf (RefOf (AUIJ)), B606)
                M600 (Arg0, 0x1D, Local0, 0x00)
            }

            Local0 = NOr (DerefOf (PAUI [0x05]), B606)
            M600 (Arg0, 0x1E, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (DerefOf (PAUI [0x13]), B606)
            M600 (Arg0, 0x1F, Local0, 0x00)
            /* Method returns Integer */

            Local0 = NOr (M601 (0x01, 0x05), B606)
            M600 (Arg0, 0x20, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = NOr (M601 (0x01, 0x13), B606)
            M600 (Arg0, 0x21, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NOr (DerefOf (M602 (0x01, 0x05, 0x01)), B606)
                M600 (Arg0, 0x22, Local0, 0xFFFFFFFFFFFFFCDE)
                Local0 = NOr (DerefOf (M602 (0x01, 0x13, 0x01)), B606)
                M600 (Arg0, 0x23, Local0, 0x00)
            }

            NOr (0x00, B606, Local0)
            M600 (Arg0, 0x24, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (0xFFFFFFFFFFFFFFFF, B606, Local0)
            M600 (Arg0, 0x25, Local0, 0x00)
            NOr (AUI5, B606, Local0)
            M600 (Arg0, 0x26, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (AUIJ, B606, Local0)
            M600 (Arg0, 0x27, Local0, 0x00)
            If (Y078)
            {
                NOr (DerefOf (RefOf (AUI5)), B606, Local0)
                M600 (Arg0, 0x28, Local0, 0xFFFFFFFFFFFFFCDE)
                NOr (DerefOf (RefOf (AUIJ)), B606, Local0)
                M600 (Arg0, 0x29, Local0, 0x00)
            }

            NOr (DerefOf (PAUI [0x05]), B606, Local0)
            M600 (Arg0, 0x2A, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (DerefOf (PAUI [0x13]), B606, Local0)
            M600 (Arg0, 0x2B, Local0, 0x00)
            /* Method returns Integer */

            NOr (M601 (0x01, 0x05), B606, Local0)
            M600 (Arg0, 0x2C, Local0, 0xFFFFFFFFFFFFFCDE)
            NOr (M601 (0x01, 0x13), B606, Local0)
            M600 (Arg0, 0x2D, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NOr (DerefOf (M602 (0x01, 0x05, 0x01)), B606, Local0)
                M600 (Arg0, 0x2E, Local0, 0xFFFFFFFFFFFFFCDE)
                NOr (DerefOf (M602 (0x01, 0x13, 0x01)), B606, Local0)
                M600 (Arg0, 0x2F, Local0, 0x00)
            }
        }

        /* NOr, 64-bit */

        Method (M04E, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Local0 = NOr (B60A, 0x00)
            M600 (Arg0, 0x00, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (B60A, 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x01, Local0, 0x00)
            Local0 = NOr (B60A, AUI5)
            M600 (Arg0, 0x02, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (B60A, AUIJ)
            M600 (Arg0, 0x03, Local0, 0x00)
            If (Y078)
            {
                Local0 = NOr (B60A, DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, 0x01834C6E29AF5D7B)
                Local0 = NOr (B60A, DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x05, Local0, 0x00)
            }

            Local0 = NOr (B60A, DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (B60A, DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x07, Local0, 0x00)
            /* Method returns Integer */

            Local0 = NOr (B60A, M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (B60A, M601 (0x01, 0x13))
            M600 (Arg0, 0x09, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NOr (B60A, DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, 0x01834C6E29AF5D7B)
                Local0 = NOr (B60A, DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x0B, Local0, 0x00)
            }

            NOr (B60A, 0x00, Local0)
            M600 (Arg0, 0x0C, Local0, 0x01834C6E29AF5D7B)
            NOr (B60A, 0xFFFFFFFFFFFFFFFF, Local0)
            M600 (Arg0, 0x0D, Local0, 0x00)
            NOr (B60A, AUI5, Local0)
            M600 (Arg0, 0x0E, Local0, 0x01834C6E29AF5D7B)
            NOr (B60A, AUIJ, Local0)
            M600 (Arg0, 0x0F, Local0, 0x00)
            If (Y078)
            {
                NOr (B60A, DerefOf (RefOf (AUI5)), Local0)
                M600 (Arg0, 0x10, Local0, 0x01834C6E29AF5D7B)
                NOr (B60A, DerefOf (RefOf (AUIJ)), Local0)
                M600 (Arg0, 0x11, Local0, 0x00)
            }

            NOr (B60A, DerefOf (PAUI [0x05]), Local0)
            M600 (Arg0, 0x12, Local0, 0x01834C6E29AF5D7B)
            NOr (B60A, DerefOf (PAUI [0x13]), Local0)
            M600 (Arg0, 0x13, Local0, 0x00)
            /* Method returns Integer */

            NOr (B60A, M601 (0x01, 0x05), Local0)
            M600 (Arg0, 0x14, Local0, 0x01834C6E29AF5D7B)
            NOr (B60A, M601 (0x01, 0x13), Local0)
            M600 (Arg0, 0x15, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NOr (B60A, DerefOf (M602 (0x01, 0x05, 0x01)), Local0)
                M600 (Arg0, 0x16, Local0, 0x01834C6E29AF5D7B)
                NOr (B60A, DerefOf (M602 (0x01, 0x13, 0x01)), Local0)
                M600 (Arg0, 0x17, Local0, 0x00)
            }

            /* Conversion of the second operand */

            Local0 = NOr (0x00, B60A)
            M600 (Arg0, 0x18, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (0xFFFFFFFFFFFFFFFF, B60A)
            M600 (Arg0, 0x19, Local0, 0x00)
            Local0 = NOr (AUI5, B60A)
            M600 (Arg0, 0x1A, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (AUIJ, B60A)
            M600 (Arg0, 0x1B, Local0, 0x00)
            If (Y078)
            {
                Local0 = NOr (DerefOf (RefOf (AUI5)), B60A)
                M600 (Arg0, 0x1C, Local0, 0x01834C6E29AF5D7B)
                Local0 = NOr (DerefOf (RefOf (AUIJ)), B60A)
                M600 (Arg0, 0x1D, Local0, 0x00)
            }

            Local0 = NOr (DerefOf (PAUI [0x05]), B60A)
            M600 (Arg0, 0x1E, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (DerefOf (PAUI [0x13]), B60A)
            M600 (Arg0, 0x1F, Local0, 0x00)
            /* Method returns Integer */

            Local0 = NOr (M601 (0x01, 0x05), B60A)
            M600 (Arg0, 0x20, Local0, 0x01834C6E29AF5D7B)
            Local0 = NOr (M601 (0x01, 0x13), B60A)
            M600 (Arg0, 0x21, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NOr (DerefOf (M602 (0x01, 0x05, 0x01)), B60A)
                M600 (Arg0, 0x22, Local0, 0x01834C6E29AF5D7B)
                Local0 = NOr (DerefOf (M602 (0x01, 0x13, 0x01)), B60A)
                M600 (Arg0, 0x23, Local0, 0x00)
            }

            NOr (0x00, B60A, Local0)
            M600 (Arg0, 0x24, Local0, 0x01834C6E29AF5D7B)
            NOr (0xFFFFFFFFFFFFFFFF, B60A, Local0)
            M600 (Arg0, 0x25, Local0, 0x00)
            NOr (AUI5, B60A, Local0)
            M600 (Arg0, 0x26, Local0, 0x01834C6E29AF5D7B)
            NOr (AUIJ, B60A, Local0)
            M600 (Arg0, 0x27, Local0, 0x00)
            If (Y078)
            {
                NOr (DerefOf (RefOf (AUI5)), B60A, Local0)
                M600 (Arg0, 0x28, Local0, 0x01834C6E29AF5D7B)
                NOr (DerefOf (RefOf (AUIJ)), B60A, Local0)
                M600 (Arg0, 0x29, Local0, 0x00)
            }

            NOr (DerefOf (PAUI [0x05]), B60A, Local0)
            M600 (Arg0, 0x2A, Local0, 0x01834C6E29AF5D7B)
            NOr (DerefOf (PAUI [0x13]), B60A, Local0)
            M600 (Arg0, 0x2B, Local0, 0x00)
            /* Method returns Integer */

            NOr (M601 (0x01, 0x05), B60A, Local0)
            M600 (Arg0, 0x2C, Local0, 0x01834C6E29AF5D7B)
            NOr (M601 (0x01, 0x13), B60A, Local0)
            M600 (Arg0, 0x2D, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NOr (DerefOf (M602 (0x01, 0x05, 0x01)), B60A, Local0)
                M600 (Arg0, 0x2E, Local0, 0x01834C6E29AF5D7B)
                NOr (DerefOf (M602 (0x01, 0x13, 0x01)), B60A, Local0)
                M600 (Arg0, 0x2F, Local0, 0x00)
            }

            /* Conversion of the both operands */

            Local0 = NOr (B606, B60A)
            M600 (Arg0, 0x30, Local0, 0x01834C6E29AF5C5A)
            Local0 = NOr (B60A, B606)
            M600 (Arg0, 0x31, Local0, 0x01834C6E29AF5C5A)
            NOr (B606, B60A, Local0)
            M600 (Arg0, 0x32, Local0, 0x01834C6E29AF5C5A)
            NOr (B60A, B606, Local0)
            M600 (Arg0, 0x33, Local0, 0x01834C6E29AF5C5A)
        }

        /* NOr, 32-bit */

        Method (M04F, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Local0 = NOr (B60A, 0x00)
            M600 (Arg0, 0x00, Local0, 0x29AF5D7B)
            Local0 = NOr (B60A, 0xFFFFFFFF)
            M600 (Arg0, 0x01, Local0, 0x00)
            Local0 = NOr (B60A, AUI5)
            M600 (Arg0, 0x02, Local0, 0x29AF5D7B)
            Local0 = NOr (B60A, AUII)
            M600 (Arg0, 0x03, Local0, 0x00)
            If (Y078)
            {
                Local0 = NOr (B60A, DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, 0x29AF5D7B)
                Local0 = NOr (B60A, DerefOf (RefOf (AUII)))
                M600 (Arg0, 0x05, Local0, 0x00)
            }

            Local0 = NOr (B60A, DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, 0x29AF5D7B)
            Local0 = NOr (B60A, DerefOf (PAUI [0x12]))
            M600 (Arg0, 0x07, Local0, 0x00)
            /* Method returns Integer */

            Local0 = NOr (B60A, M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, 0x29AF5D7B)
            Local0 = NOr (B60A, M601 (0x01, 0x12))
            M600 (Arg0, 0x09, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NOr (B60A, DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, 0x29AF5D7B)
                Local0 = NOr (B60A, DerefOf (M602 (0x01, 0x12, 0x01)))
                M600 (Arg0, 0x0B, Local0, 0x00)
            }

            NOr (B60A, 0x00, Local0)
            M600 (Arg0, 0x0C, Local0, 0x29AF5D7B)
            NOr (B60A, 0xFFFFFFFF, Local0)
            M600 (Arg0, 0x0D, Local0, 0x00)
            NOr (B60A, AUI5, Local0)
            M600 (Arg0, 0x0E, Local0, 0x29AF5D7B)
            NOr (B60A, AUII, Local0)
            M600 (Arg0, 0x0F, Local0, 0x00)
            If (Y078)
            {
                NOr (B60A, DerefOf (RefOf (AUI5)), Local0)
                M600 (Arg0, 0x10, Local0, 0x29AF5D7B)
                NOr (B60A, DerefOf (RefOf (AUII)), Local0)
                M600 (Arg0, 0x11, Local0, 0x00)
            }

            NOr (B60A, DerefOf (PAUI [0x05]), Local0)
            M600 (Arg0, 0x12, Local0, 0x29AF5D7B)
            NOr (B60A, DerefOf (PAUI [0x12]), Local0)
            M600 (Arg0, 0x13, Local0, 0x00)
            /* Method returns Integer */

            NOr (B60A, M601 (0x01, 0x05), Local0)
            M600 (Arg0, 0x14, Local0, 0x29AF5D7B)
            NOr (B60A, M601 (0x01, 0x12), Local0)
            M600 (Arg0, 0x15, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NOr (B60A, DerefOf (M602 (0x01, 0x05, 0x01)), Local0)
                M600 (Arg0, 0x16, Local0, 0x29AF5D7B)
                NOr (B60A, DerefOf (M602 (0x01, 0x12, 0x01)), Local0)
                M600 (Arg0, 0x17, Local0, 0x00)
            }

            /* Conversion of the second operand */

            Local0 = NOr (0x00, B60A)
            M600 (Arg0, 0x18, Local0, 0x29AF5D7B)
            Local0 = NOr (0xFFFFFFFF, B60A)
            M600 (Arg0, 0x19, Local0, 0x00)
            Local0 = NOr (AUI5, B60A)
            M600 (Arg0, 0x1A, Local0, 0x29AF5D7B)
            Local0 = NOr (AUII, B60A)
            M600 (Arg0, 0x1B, Local0, 0x00)
            If (Y078)
            {
                Local0 = NOr (DerefOf (RefOf (AUI5)), B60A)
                M600 (Arg0, 0x1C, Local0, 0x29AF5D7B)
                Local0 = NOr (DerefOf (RefOf (AUII)), B60A)
                M600 (Arg0, 0x1D, Local0, 0x00)
            }

            Local0 = NOr (DerefOf (PAUI [0x05]), B60A)
            M600 (Arg0, 0x1E, Local0, 0x29AF5D7B)
            Local0 = NOr (DerefOf (PAUI [0x12]), B60A)
            M600 (Arg0, 0x1F, Local0, 0x00)
            /* Method returns Integer */

            Local0 = NOr (M601 (0x01, 0x05), B60A)
            M600 (Arg0, 0x20, Local0, 0x29AF5D7B)
            Local0 = NOr (M601 (0x01, 0x12), B60A)
            M600 (Arg0, 0x21, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = NOr (DerefOf (M602 (0x01, 0x05, 0x01)), B60A)
                M600 (Arg0, 0x22, Local0, 0x29AF5D7B)
                Local0 = NOr (DerefOf (M602 (0x01, 0x12, 0x01)), B60A)
                M600 (Arg0, 0x23, Local0, 0x00)
            }

            NOr (0x00, B60A, Local0)
            M600 (Arg0, 0x24, Local0, 0x29AF5D7B)
            NOr (0xFFFFFFFF, B60A, Local0)
            M600 (Arg0, 0x25, Local0, 0x00)
            NOr (AUI5, B60A, Local0)
            M600 (Arg0, 0x26, Local0, 0x29AF5D7B)
            NOr (AUII, B60A, Local0)
            M600 (Arg0, 0x27, Local0, 0x00)
            If (Y078)
            {
                NOr (DerefOf (RefOf (AUI5)), B60A, Local0)
                M600 (Arg0, 0x28, Local0, 0x29AF5D7B)
                NOr (DerefOf (RefOf (AUII)), B60A, Local0)
                M600 (Arg0, 0x29, Local0, 0x00)
            }

            NOr (DerefOf (PAUI [0x05]), B60A, Local0)
            M600 (Arg0, 0x2A, Local0, 0x29AF5D7B)
            NOr (DerefOf (PAUI [0x12]), B60A, Local0)
            M600 (Arg0, 0x2B, Local0, 0x00)
            /* Method returns Integer */

            NOr (M601 (0x01, 0x05), B60A, Local0)
            M600 (Arg0, 0x2C, Local0, 0x29AF5D7B)
            NOr (M601 (0x01, 0x12), B60A, Local0)
            M600 (Arg0, 0x2D, Local0, 0x00)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                NOr (DerefOf (M602 (0x01, 0x05, 0x01)), B60A, Local0)
                M600 (Arg0, 0x2E, Local0, 0x29AF5D7B)
                NOr (DerefOf (M602 (0x01, 0x12, 0x01)), B60A, Local0)
                M600 (Arg0, 0x2F, Local0, 0x00)
            }

            /* Conversion of the both operands */

            Local0 = NOr (B606, B60A)
            M600 (Arg0, 0x30, Local0, 0x29AF5C5A)
            Local0 = NOr (B60A, B606)
            M600 (Arg0, 0x31, Local0, 0x29AF5C5A)
            NOr (B606, B60A, Local0)
            M600 (Arg0, 0x32, Local0, 0x29AF5C5A)
            NOr (B60A, B606, Local0)
            M600 (Arg0, 0x33, Local0, 0x29AF5C5A)
        }

        /* Or, common 32-bit/64-bit test */

        Method (M050, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            /* Conversion of the first operand */

            Store ((B606 | 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((B606 | 0xFFFFFFFFFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0xFFFFFFFFFFFFFFFF)
            Store ((B606 | AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((B606 | AUIJ), Local0)
            M600 (Arg0, 0x03, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Store ((B606 | DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((B606 | DerefOf (RefOf (AUIJ))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Store ((B606 | DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((B606 | DerefOf (PAUI [0x13])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Store ((B606 | M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((B606 | M601 (0x01, 0x13)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B606 | DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((B606 | DerefOf (M602 (0x01, 0x13, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (B606 | 0x00)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (B606 | 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = (B606 | AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (B606 | AUIJ) /* \AUIJ */
            M600 (Arg0, 0x0F, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Local0 = (B606 | DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (B606 | DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x11, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (B606 | DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (B606 | DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x13, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Local0 = (B606 | M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (B606 | M601 (0x01, 0x13))
            M600 (Arg0, 0x15, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B606 | DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (B606 | DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            /* Conversion of the second operand */

            Store ((0x00 | B606), Local0)
            M600 (Arg0, 0x18, Local0, 0x0321)
            Store ((0xFFFFFFFFFFFFFFFF | B606), Local0)
            M600 (Arg0, 0x19, Local0, 0xFFFFFFFFFFFFFFFF)
            Store ((AUI5 | B606), Local0)
            M600 (Arg0, 0x1A, Local0, 0x0321)
            Store ((AUIJ | B606), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) | B606), Local0)
                M600 (Arg0, 0x1C, Local0, 0x0321)
                Store ((DerefOf (RefOf (AUIJ)) | B606), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Store ((DerefOf (PAUI [0x05]) | B606), Local0)
            M600 (Arg0, 0x1E, Local0, 0x0321)
            Store ((DerefOf (PAUI [0x13]) | B606), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) | B606), Local0)
            M600 (Arg0, 0x20, Local0, 0x0321)
            Store ((M601 (0x01, 0x13) | B606), Local0)
            M600 (Arg0, 0x21, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) | B606), Local0)
                M600 (Arg0, 0x22, Local0, 0x0321)
                Store ((DerefOf (M602 (0x01, 0x13, 0x01)) | B606), Local0)
                M600 (Arg0, 0x23, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (0x00 | B606) /* \M613.M050.B606 */
            M600 (Arg0, 0x24, Local0, 0x0321)
            Local0 = (0xFFFFFFFFFFFFFFFF | B606) /* \M613.M050.B606 */
            M600 (Arg0, 0x25, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = (AUI5 | B606) /* \M613.M050.B606 */
            M600 (Arg0, 0x26, Local0, 0x0321)
            Local0 = (AUIJ | B606) /* \M613.M050.B606 */
            M600 (Arg0, 0x27, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) | B606) /* \M613.M050.B606 */
                M600 (Arg0, 0x28, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (AUIJ)) | B606) /* \M613.M050.B606 */
                M600 (Arg0, 0x29, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (DerefOf (PAUI [0x05]) | B606) /* \M613.M050.B606 */
            M600 (Arg0, 0x2A, Local0, 0x0321)
            Local0 = (DerefOf (PAUI [0x13]) | B606) /* \M613.M050.B606 */
            M600 (Arg0, 0x2B, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) | B606) /* \M613.M050.B606 */
            M600 (Arg0, 0x2C, Local0, 0x0321)
            Local0 = (M601 (0x01, 0x13) | B606) /* \M613.M050.B606 */
            M600 (Arg0, 0x2D, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) | B606) /* \M613.M050.B606 */
                M600 (Arg0, 0x2E, Local0, 0x0321)
                Local0 = (DerefOf (M602 (0x01, 0x13, 0x01)) | B606) /* \M613.M050.B606 */
                M600 (Arg0, 0x2F, Local0, 0xFFFFFFFFFFFFFFFF)
            }
        }

        /* Or, 64-bit */

        Method (M051, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A | 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((B60A | 0xFFFFFFFFFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0xFFFFFFFFFFFFFFFF)
            Store ((B60A | AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((B60A | AUIJ), Local0)
            M600 (Arg0, 0x03, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Store ((B60A | DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((B60A | DerefOf (RefOf (AUIJ))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Store ((B60A | DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((B60A | DerefOf (PAUI [0x13])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Store ((B60A | M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((B60A | M601 (0x01, 0x13)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A | DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((B60A | DerefOf (M602 (0x01, 0x13, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (B60A | 0x00)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A | 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = (B60A | AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A | AUIJ) /* \AUIJ */
            M600 (Arg0, 0x0F, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Local0 = (B60A | DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (B60A | DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x11, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (B60A | DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A | DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x13, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Local0 = (B60A | M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A | M601 (0x01, 0x13))
            M600 (Arg0, 0x15, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A | DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (B60A | DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            /* Conversion of the second operand */

            Store ((0x00 | B60A), Local0)
            M600 (Arg0, 0x18, Local0, 0xFE7CB391D650A284)
            Store ((0xFFFFFFFFFFFFFFFF | B60A), Local0)
            M600 (Arg0, 0x19, Local0, 0xFFFFFFFFFFFFFFFF)
            Store ((AUI5 | B60A), Local0)
            M600 (Arg0, 0x1A, Local0, 0xFE7CB391D650A284)
            Store ((AUIJ | B60A), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) | B60A), Local0)
                M600 (Arg0, 0x1C, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (AUIJ)) | B60A), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Store ((DerefOf (PAUI [0x05]) | B60A), Local0)
            M600 (Arg0, 0x1E, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (PAUI [0x13]) | B60A), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) | B60A), Local0)
            M600 (Arg0, 0x20, Local0, 0xFE7CB391D650A284)
            Store ((M601 (0x01, 0x13) | B60A), Local0)
            M600 (Arg0, 0x21, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) | B60A), Local0)
                M600 (Arg0, 0x22, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (M602 (0x01, 0x13, 0x01)) | B60A), Local0)
                M600 (Arg0, 0x23, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (0x00 | B60A) /* \M613.M051.B60A */
            M600 (Arg0, 0x24, Local0, 0xFE7CB391D650A284)
            Local0 = (0xFFFFFFFFFFFFFFFF | B60A) /* \M613.M051.B60A */
            M600 (Arg0, 0x25, Local0, 0xFFFFFFFFFFFFFFFF)
            Local0 = (AUI5 | B60A) /* \M613.M051.B60A */
            M600 (Arg0, 0x26, Local0, 0xFE7CB391D650A284)
            Local0 = (AUIJ | B60A) /* \M613.M051.B60A */
            M600 (Arg0, 0x27, Local0, 0xFFFFFFFFFFFFFFFF)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) | B60A) /* \M613.M051.B60A */
                M600 (Arg0, 0x28, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (AUIJ)) | B60A) /* \M613.M051.B60A */
                M600 (Arg0, 0x29, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = (DerefOf (PAUI [0x05]) | B60A) /* \M613.M051.B60A */
            M600 (Arg0, 0x2A, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (PAUI [0x13]) | B60A) /* \M613.M051.B60A */
            M600 (Arg0, 0x2B, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) | B60A) /* \M613.M051.B60A */
            M600 (Arg0, 0x2C, Local0, 0xFE7CB391D650A284)
            Local0 = (M601 (0x01, 0x13) | B60A) /* \M613.M051.B60A */
            M600 (Arg0, 0x2D, Local0, 0xFFFFFFFFFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) | B60A) /* \M613.M051.B60A */
                M600 (Arg0, 0x2E, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (M602 (0x01, 0x13, 0x01)) | B60A) /* \M613.M051.B60A */
                M600 (Arg0, 0x2F, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            /* Conversion of the both operands */

            Store ((B606 | B60A), Local0)
            M600 (Arg0, 0x30, Local0, 0xFE7CB391D650A3A5)
            Store ((B60A | B606), Local0)
            M600 (Arg0, 0x31, Local0, 0xFE7CB391D650A3A5)
            Local0 = (B606 | B60A) /* \M613.M051.B60A */
            M600 (Arg0, 0x32, Local0, 0xFE7CB391D650A3A5)
            Local0 = (B60A | B606) /* \M613.M051.B606 */
            M600 (Arg0, 0x33, Local0, 0xFE7CB391D650A3A5)
        }

        /* Or, 32-bit */

        Method (M052, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A | 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xD650A284)
            Store ((B60A | 0xFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0xFFFFFFFF)
            Store ((B60A | AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xD650A284)
            Store ((B60A | AUII), Local0)
            M600 (Arg0, 0x03, Local0, 0xFFFFFFFF)
            If (Y078)
            {
                Store ((B60A | DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xD650A284)
                Store ((B60A | DerefOf (RefOf (AUII))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFFFFFFFF)
            }

            Store ((B60A | DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xD650A284)
            Store ((B60A | DerefOf (PAUI [0x12])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFFFFFFFF)
            /* Method returns Integer */

            Store ((B60A | M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xD650A284)
            Store ((B60A | M601 (0x01, 0x12)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A | DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xD650A284)
                Store ((B60A | DerefOf (M602 (0x01, 0x12, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFFFFFFFF)
            }

            Local0 = (B60A | 0x00)
            M600 (Arg0, 0x0C, Local0, 0xD650A284)
            Local0 = (B60A | 0xFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0xFFFFFFFF)
            Local0 = (B60A | AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xD650A284)
            Local0 = (B60A | AUII) /* \AUII */
            M600 (Arg0, 0x0F, Local0, 0xFFFFFFFF)
            If (Y078)
            {
                Local0 = (B60A | DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xD650A284)
                Local0 = (B60A | DerefOf (RefOf (AUII)))
                M600 (Arg0, 0x11, Local0, 0xFFFFFFFF)
            }

            Local0 = (B60A | DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xD650A284)
            Local0 = (B60A | DerefOf (PAUI [0x12]))
            M600 (Arg0, 0x13, Local0, 0xFFFFFFFF)
            /* Method returns Integer */

            Local0 = (B60A | M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xD650A284)
            Local0 = (B60A | M601 (0x01, 0x12))
            M600 (Arg0, 0x15, Local0, 0xFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A | DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xD650A284)
                Local0 = (B60A | DerefOf (M602 (0x01, 0x12, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFFFFFFFF)
            }

            /* Conversion of the second operand */

            Store ((0x00 | B60A), Local0)
            M600 (Arg0, 0x18, Local0, 0xD650A284)
            Store ((0xFFFFFFFF | B60A), Local0)
            M600 (Arg0, 0x19, Local0, 0xFFFFFFFF)
            Store ((AUI5 | B60A), Local0)
            M600 (Arg0, 0x1A, Local0, 0xD650A284)
            Store ((AUII | B60A), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFFFFFFFF)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) | B60A), Local0)
                M600 (Arg0, 0x1C, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (AUII)) | B60A), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFFFFFFFF)
            }

            Store ((DerefOf (PAUI [0x05]) | B60A), Local0)
            M600 (Arg0, 0x1E, Local0, 0xD650A284)
            Store ((DerefOf (PAUI [0x12]) | B60A), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFFFFFFFF)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) | B60A), Local0)
            M600 (Arg0, 0x20, Local0, 0xD650A284)
            Store ((M601 (0x01, 0x12) | B60A), Local0)
            M600 (Arg0, 0x21, Local0, 0xFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) | B60A), Local0)
                M600 (Arg0, 0x22, Local0, 0xD650A284)
                Store ((DerefOf (M602 (0x01, 0x12, 0x01)) | B60A), Local0)
                M600 (Arg0, 0x23, Local0, 0xFFFFFFFF)
            }

            Local0 = (0x00 | B60A) /* \M613.M052.B60A */
            M600 (Arg0, 0x24, Local0, 0xD650A284)
            Local0 = (0xFFFFFFFF | B60A) /* \M613.M052.B60A */
            M600 (Arg0, 0x25, Local0, 0xFFFFFFFF)
            Local0 = (AUI5 | B60A) /* \M613.M052.B60A */
            M600 (Arg0, 0x26, Local0, 0xD650A284)
            Local0 = (AUII | B60A) /* \M613.M052.B60A */
            M600 (Arg0, 0x27, Local0, 0xFFFFFFFF)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) | B60A) /* \M613.M052.B60A */
                M600 (Arg0, 0x28, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (AUII)) | B60A) /* \M613.M052.B60A */
                M600 (Arg0, 0x29, Local0, 0xFFFFFFFF)
            }

            Local0 = (DerefOf (PAUI [0x05]) | B60A) /* \M613.M052.B60A */
            M600 (Arg0, 0x2A, Local0, 0xD650A284)
            Local0 = (DerefOf (PAUI [0x12]) | B60A) /* \M613.M052.B60A */
            M600 (Arg0, 0x2B, Local0, 0xFFFFFFFF)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) | B60A) /* \M613.M052.B60A */
            M600 (Arg0, 0x2C, Local0, 0xD650A284)
            Local0 = (M601 (0x01, 0x12) | B60A) /* \M613.M052.B60A */
            M600 (Arg0, 0x2D, Local0, 0xFFFFFFFF)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) | B60A) /* \M613.M052.B60A */
                M600 (Arg0, 0x2E, Local0, 0xD650A284)
                Local0 = (DerefOf (M602 (0x01, 0x12, 0x01)) | B60A) /* \M613.M052.B60A */
                M600 (Arg0, 0x2F, Local0, 0xFFFFFFFF)
            }

            /* Conversion of the both operands */

            Store ((B606 | B60A), Local0)
            M600 (Arg0, 0x30, Local0, 0xD650A3A5)
            Store ((B60A | B606), Local0)
            M600 (Arg0, 0x31, Local0, 0xD650A3A5)
            Local0 = (B606 | B60A) /* \M613.M052.B60A */
            M600 (Arg0, 0x32, Local0, 0xD650A3A5)
            Local0 = (B60A | B606) /* \M613.M052.B606 */
            M600 (Arg0, 0x33, Local0, 0xD650A3A5)
        }

        /* ShiftLeft, common 32-bit/64-bit test */

        Method (M053, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60E, Buffer (0x01)
            {
                 0x0B                                             // .
            })
            /* Conversion of the first operand */

            Store ((B606 << 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((B606 << 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x0642)
            Store ((B606 << AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((B606 << AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x0642)
            If (Y078)
            {
                Store ((B606 << DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((B606 << DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x0642)
            }

            Store ((B606 << DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((B606 << DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x0642)
            /* Method returns Integer */

            Store ((B606 << M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((B606 << M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x0642)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B606 << DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((B606 << DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x0642)
            }

            Local0 = (B606 << 0x00)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (B606 << 0x01)
            M600 (Arg0, 0x0D, Local0, 0x0642)
            Local0 = (B606 << AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (B606 << AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x0642)
            If (Y078)
            {
                Local0 = (B606 << DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (B606 << DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x0642)
            }

            Local0 = (B606 << DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (B606 << DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x0642)
            /* Method returns Integer */

            Local0 = (B606 << M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (B606 << M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x0642)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B606 << DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (B606 << DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x0642)
            }

            /* Conversion of the second operand */

            Store ((0x00 << B60E), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x01 << B60E), Local0)
            M600 (Arg0, 0x19, Local0, 0x0800)
            Store ((AUI5 << B60E), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI6 << B60E), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0800)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) << B60E), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI6)) << B60E), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0800)
            }

            Store ((DerefOf (PAUI [0x05]) << B60E), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x06]) << B60E), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0800)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) << B60E), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x06) << B60E), Local0)
            M600 (Arg0, 0x21, Local0, 0x0800)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) << B60E), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) << B60E), Local0)
                M600 (Arg0, 0x23, Local0, 0x0800)
            }

            Local0 = (0x00 << B60E) /* \M613.M053.B60E */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0x01 << B60E) /* \M613.M053.B60E */
            M600 (Arg0, 0x25, Local0, 0x0800)
            Local0 = (AUI5 << B60E) /* \M613.M053.B60E */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI6 << B60E) /* \M613.M053.B60E */
            M600 (Arg0, 0x27, Local0, 0x0800)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) << B60E) /* \M613.M053.B60E */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI6)) << B60E) /* \M613.M053.B60E */
                M600 (Arg0, 0x29, Local0, 0x0800)
            }

            Local0 = (DerefOf (PAUI [0x05]) << B60E) /* \M613.M053.B60E */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x06]) << B60E) /* \M613.M053.B60E */
            M600 (Arg0, 0x2B, Local0, 0x0800)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) << B60E) /* \M613.M053.B60E */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x06) << B60E) /* \M613.M053.B60E */
            M600 (Arg0, 0x2D, Local0, 0x0800)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) << B60E) /* \M613.M053.B60E */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) << B60E) /* \M613.M053.B60E */
                M600 (Arg0, 0x2F, Local0, 0x0800)
            }
        }

        /* ShiftLeft, 64-bit */

        Method (M054, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            Name (B60E, Buffer (0x01)
            {
                 0x0B                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A << 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((B60A << 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xFCF96723ACA14508)
            Store ((B60A << AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((B60A << AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xFCF96723ACA14508)
            If (Y078)
            {
                Store ((B60A << DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((B60A << DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFCF96723ACA14508)
            }

            Store ((B60A << DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((B60A << DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFCF96723ACA14508)
            /* Method returns Integer */

            Store ((B60A << M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((B60A << M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFCF96723ACA14508)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A << DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((B60A << DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFCF96723ACA14508)
            }

            Local0 = (B60A << 0x00)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A << 0x01)
            M600 (Arg0, 0x0D, Local0, 0xFCF96723ACA14508)
            Local0 = (B60A << AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A << AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xFCF96723ACA14508)
            If (Y078)
            {
                Local0 = (B60A << DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (B60A << DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xFCF96723ACA14508)
            }

            Local0 = (B60A << DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A << DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xFCF96723ACA14508)
            /* Method returns Integer */

            Local0 = (B60A << M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A << M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xFCF96723ACA14508)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A << DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (B60A << DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFCF96723ACA14508)
            }

            /* Conversion of the second operand */

            Store ((0x00 << B60E), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x01 << B60E), Local0)
            M600 (Arg0, 0x19, Local0, 0x0800)
            Store ((AUI5 << B60E), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI6 << B60E), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0800)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) << B60E), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI6)) << B60E), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0800)
            }

            Store ((DerefOf (PAUI [0x05]) << B60E), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x06]) << B60E), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0800)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) << B60E), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x06) << B60E), Local0)
            M600 (Arg0, 0x21, Local0, 0x0800)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) << B60E), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) << B60E), Local0)
                M600 (Arg0, 0x23, Local0, 0x0800)
            }

            Local0 = (0x00 << B60E) /* \M613.M054.B60E */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0x01 << B60E) /* \M613.M054.B60E */
            M600 (Arg0, 0x25, Local0, 0x0800)
            Local0 = (AUI5 << B60E) /* \M613.M054.B60E */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI6 << B60E) /* \M613.M054.B60E */
            M600 (Arg0, 0x27, Local0, 0x0800)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) << B60E) /* \M613.M054.B60E */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI6)) << B60E) /* \M613.M054.B60E */
                M600 (Arg0, 0x29, Local0, 0x0800)
            }

            Local0 = (DerefOf (PAUI [0x05]) << B60E) /* \M613.M054.B60E */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x06]) << B60E) /* \M613.M054.B60E */
            M600 (Arg0, 0x2B, Local0, 0x0800)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) << B60E) /* \M613.M054.B60E */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x06) << B60E) /* \M613.M054.B60E */
            M600 (Arg0, 0x2D, Local0, 0x0800)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) << B60E) /* \M613.M054.B60E */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) << B60E) /* \M613.M054.B60E */
                M600 (Arg0, 0x2F, Local0, 0x0800)
            }

            /* Conversion of the both operands */

            Store ((B606 << B60E), Local0)
            M600 (Arg0, 0x30, Local0, 0x00190800)
            Store ((B60A << B60E), Local0)
            M600 (Arg0, 0x31, Local0, 0xE59C8EB285142000)
            Local0 = (B606 << B60E) /* \M613.M054.B60E */
            M600 (Arg0, 0x32, Local0, 0x00190800)
            Local0 = (B60A << B60E) /* \M613.M054.B60E */
            M600 (Arg0, 0x33, Local0, 0xE59C8EB285142000)
        }

        /* ShiftLeft, 32-bit */

        Method (M055, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            Name (B60E, Buffer (0x01)
            {
                 0x0B                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A << 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xD650A284)
            Store ((B60A << 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xACA14508)
            Store ((B60A << AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xD650A284)
            Store ((B60A << AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xACA14508)
            If (Y078)
            {
                Store ((B60A << DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xD650A284)
                Store ((B60A << DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xACA14508)
            }

            Store ((B60A << DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xD650A284)
            Store ((B60A << DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xACA14508)
            /* Method returns Integer */

            Store ((B60A << M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xD650A284)
            Store ((B60A << M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xACA14508)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A << DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xD650A284)
                Store ((B60A << DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xACA14508)
            }

            Local0 = (B60A << 0x00)
            M600 (Arg0, 0x0C, Local0, 0xD650A284)
            Local0 = (B60A << 0x01)
            M600 (Arg0, 0x0D, Local0, 0xACA14508)
            Local0 = (B60A << AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xD650A284)
            Local0 = (B60A << AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xACA14508)
            If (Y078)
            {
                Local0 = (B60A << DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xD650A284)
                Local0 = (B60A << DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xACA14508)
            }

            Local0 = (B60A << DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xD650A284)
            Local0 = (B60A << DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xACA14508)
            /* Method returns Integer */

            Local0 = (B60A << M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xD650A284)
            Local0 = (B60A << M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xACA14508)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A << DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xD650A284)
                Local0 = (B60A << DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xACA14508)
            }

            /* Conversion of the second operand */

            Store ((0x00 << B60E), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0x01 << B60E), Local0)
            M600 (Arg0, 0x19, Local0, 0x0800)
            Store ((AUI5 << B60E), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI6 << B60E), Local0)
            M600 (Arg0, 0x1B, Local0, 0x0800)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) << B60E), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI6)) << B60E), Local0)
                M600 (Arg0, 0x1D, Local0, 0x0800)
            }

            Store ((DerefOf (PAUI [0x05]) << B60E), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x06]) << B60E), Local0)
            M600 (Arg0, 0x1F, Local0, 0x0800)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) << B60E), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x06) << B60E), Local0)
            M600 (Arg0, 0x21, Local0, 0x0800)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) << B60E), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) << B60E), Local0)
                M600 (Arg0, 0x23, Local0, 0x0800)
            }

            Local0 = (0x00 << B60E) /* \M613.M055.B60E */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0x01 << B60E) /* \M613.M055.B60E */
            M600 (Arg0, 0x25, Local0, 0x0800)
            Local0 = (AUI5 << B60E) /* \M613.M055.B60E */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI6 << B60E) /* \M613.M055.B60E */
            M600 (Arg0, 0x27, Local0, 0x0800)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) << B60E) /* \M613.M055.B60E */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI6)) << B60E) /* \M613.M055.B60E */
                M600 (Arg0, 0x29, Local0, 0x0800)
            }

            Local0 = (DerefOf (PAUI [0x05]) << B60E) /* \M613.M055.B60E */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x06]) << B60E) /* \M613.M055.B60E */
            M600 (Arg0, 0x2B, Local0, 0x0800)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) << B60E) /* \M613.M055.B60E */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x06) << B60E) /* \M613.M055.B60E */
            M600 (Arg0, 0x2D, Local0, 0x0800)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) << B60E) /* \M613.M055.B60E */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) << B60E) /* \M613.M055.B60E */
                M600 (Arg0, 0x2F, Local0, 0x0800)
            }

            /* Conversion of the both operands */

            Store ((B606 << B60E), Local0)
            M600 (Arg0, 0x30, Local0, 0x00190800)
            Store ((B60A << B60E), Local0)
            M600 (Arg0, 0x31, Local0, 0x85142000)
            Local0 = (B606 << B60E) /* \M613.M055.B60E */
            M600 (Arg0, 0x32, Local0, 0x00190800)
            Local0 = (B60A << B60E) /* \M613.M055.B60E */
            M600 (Arg0, 0x33, Local0, 0x85142000)
        }

        /* ShiftRight, common 32-bit/64-bit test */

        Method (M056, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60E, Buffer (0x01)
            {
                 0x0B                                             // .
            })
            /* Conversion of the first operand */

            Store ((B606 >> 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((B606 >> 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x0190)
            Store ((B606 >> AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((B606 >> AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x0190)
            If (Y078)
            {
                Store ((B606 >> DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((B606 >> DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x0190)
            }

            Store ((B606 >> DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((B606 >> DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x0190)
            /* Method returns Integer */

            Store ((B606 >> M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((B606 >> M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x0190)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B606 >> DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((B606 >> DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x0190)
            }

            Local0 = (B606 >> 0x00)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (B606 >> 0x01)
            M600 (Arg0, 0x0D, Local0, 0x0190)
            Local0 = (B606 >> AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (B606 >> AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x0190)
            If (Y078)
            {
                Local0 = (B606 >> DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (B606 >> DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x0190)
            }

            Local0 = (B606 >> DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (B606 >> DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x0190)
            /* Method returns Integer */

            Local0 = (B606 >> M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (B606 >> M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x0190)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B606 >> DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (B606 >> DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x0190)
            }

            /* Conversion of the second operand */

            Store ((0x0321 >> B60E), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xD650A284 >> B60E), Local0)
            M600 (Arg0, 0x19, Local0, 0x001ACA14)
            Store ((AUI1 >> B60E), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUIK >> B60E), Local0)
            M600 (Arg0, 0x1B, Local0, 0x001ACA14)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI1)) >> B60E), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUIK)) >> B60E), Local0)
                M600 (Arg0, 0x1D, Local0, 0x001ACA14)
            }

            Store ((DerefOf (PAUI [0x01]) >> B60E), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x14]) >> B60E), Local0)
            M600 (Arg0, 0x1F, Local0, 0x001ACA14)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x01) >> B60E), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x14) >> B60E), Local0)
            M600 (Arg0, 0x21, Local0, 0x001ACA14)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x01, 0x01)) >> B60E), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x14, 0x01)) >> B60E), Local0)
                M600 (Arg0, 0x23, Local0, 0x001ACA14)
            }

            Local0 = (0x0321 >> B60E) /* \M613.M056.B60E */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0xD650A284 >> B60E) /* \M613.M056.B60E */
            M600 (Arg0, 0x25, Local0, 0x001ACA14)
            Local0 = (AUI1 >> B60E) /* \M613.M056.B60E */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUIK >> B60E) /* \M613.M056.B60E */
            M600 (Arg0, 0x27, Local0, 0x001ACA14)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) >> B60E) /* \M613.M056.B60E */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUIK)) >> B60E) /* \M613.M056.B60E */
                M600 (Arg0, 0x29, Local0, 0x001ACA14)
            }

            Local0 = (DerefOf (PAUI [0x01]) >> B60E) /* \M613.M056.B60E */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x14]) >> B60E) /* \M613.M056.B60E */
            M600 (Arg0, 0x2B, Local0, 0x001ACA14)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) >> B60E) /* \M613.M056.B60E */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x14) >> B60E) /* \M613.M056.B60E */
            M600 (Arg0, 0x2D, Local0, 0x001ACA14)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) >> B60E) /* \M613.M056.B60E */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x14, 0x01)) >> B60E) /* \M613.M056.B60E */
                M600 (Arg0, 0x2F, Local0, 0x001ACA14)
            }
        }

        /* ShiftRight, 64-bit */

        Method (M057, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            Name (B60E, Buffer (0x01)
            {
                 0x0B                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A >> 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((B60A >> 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x7F3E59C8EB285142)
            Store ((B60A >> AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((B60A >> AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x7F3E59C8EB285142)
            If (Y078)
            {
                Store ((B60A >> DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((B60A >> DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x7F3E59C8EB285142)
            }

            Store ((B60A >> DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((B60A >> DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x7F3E59C8EB285142)
            /* Method returns Integer */

            Store ((B60A >> M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((B60A >> M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x7F3E59C8EB285142)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A >> DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((B60A >> DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x7F3E59C8EB285142)
            }

            Local0 = (B60A >> 0x00)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A >> 0x01)
            M600 (Arg0, 0x0D, Local0, 0x7F3E59C8EB285142)
            Local0 = (B60A >> AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A >> AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x7F3E59C8EB285142)
            If (Y078)
            {
                Local0 = (B60A >> DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (B60A >> DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x7F3E59C8EB285142)
            }

            Local0 = (B60A >> DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A >> DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x7F3E59C8EB285142)
            /* Method returns Integer */

            Local0 = (B60A >> M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A >> M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x7F3E59C8EB285142)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A >> DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (B60A >> DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x7F3E59C8EB285142)
            }

            /* Conversion of the second operand */

            Store ((0x0321 >> B60E), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xFE7CB391D650A284 >> B60E), Local0)
            M600 (Arg0, 0x19, Local0, 0x001FCF96723ACA14)
            Store ((AUI1 >> B60E), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUI4 >> B60E), Local0)
            M600 (Arg0, 0x1B, Local0, 0x001FCF96723ACA14)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI1)) >> B60E), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUI4)) >> B60E), Local0)
                M600 (Arg0, 0x1D, Local0, 0x001FCF96723ACA14)
            }

            Store ((DerefOf (PAUI [0x01]) >> B60E), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x04]) >> B60E), Local0)
            M600 (Arg0, 0x1F, Local0, 0x001FCF96723ACA14)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x01) >> B60E), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x04) >> B60E), Local0)
            M600 (Arg0, 0x21, Local0, 0x001FCF96723ACA14)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x01, 0x01)) >> B60E), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x04, 0x01)) >> B60E), Local0)
                M600 (Arg0, 0x23, Local0, 0x001FCF96723ACA14)
            }

            Local0 = (0x0321 >> B60E) /* \M613.M057.B60E */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0xFE7CB391D650A284 >> B60E) /* \M613.M057.B60E */
            M600 (Arg0, 0x25, Local0, 0x001FCF96723ACA14)
            Local0 = (AUI1 >> B60E) /* \M613.M057.B60E */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUI4 >> B60E) /* \M613.M057.B60E */
            M600 (Arg0, 0x27, Local0, 0x001FCF96723ACA14)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) >> B60E) /* \M613.M057.B60E */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUI4)) >> B60E) /* \M613.M057.B60E */
                M600 (Arg0, 0x29, Local0, 0x001FCF96723ACA14)
            }

            Local0 = (DerefOf (PAUI [0x01]) >> B60E) /* \M613.M057.B60E */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x04]) >> B60E) /* \M613.M057.B60E */
            M600 (Arg0, 0x2B, Local0, 0x001FCF96723ACA14)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) >> B60E) /* \M613.M057.B60E */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x04) >> B60E) /* \M613.M057.B60E */
            M600 (Arg0, 0x2D, Local0, 0x001FCF96723ACA14)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) >> B60E) /* \M613.M057.B60E */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) >> B60E) /* \M613.M057.B60E */
                M600 (Arg0, 0x2F, Local0, 0x001FCF96723ACA14)
            }

            /* Conversion of the both operands */

            Store ((B606 >> B60E), Local0)
            M600 (Arg0, 0x30, Local0, 0x00)
            Store ((B60A >> B60E), Local0)
            M600 (Arg0, 0x31, Local0, 0x001FCF96723ACA14)
            Local0 = (B606 >> B60E) /* \M613.M057.B60E */
            M600 (Arg0, 0x32, Local0, 0x00)
            Local0 = (B60A >> B60E) /* \M613.M057.B60E */
            M600 (Arg0, 0x33, Local0, 0x001FCF96723ACA14)
        }

        /* ShiftRight, 32-bit */

        Method (M058, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            Name (B60E, Buffer (0x01)
            {
                 0x0B                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A >> 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xD650A284)
            Store ((B60A >> 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x6B285142)
            Store ((B60A >> AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xD650A284)
            Store ((B60A >> AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x6B285142)
            If (Y078)
            {
                Store ((B60A >> DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xD650A284)
                Store ((B60A >> DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x6B285142)
            }

            Store ((B60A >> DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xD650A284)
            Store ((B60A >> DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x6B285142)
            /* Method returns Integer */

            Store ((B60A >> M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xD650A284)
            Store ((B60A >> M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x6B285142)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A >> DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xD650A284)
                Store ((B60A >> DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x6B285142)
            }

            Local0 = (B60A >> 0x00)
            M600 (Arg0, 0x0C, Local0, 0xD650A284)
            Local0 = (B60A >> 0x01)
            M600 (Arg0, 0x0D, Local0, 0x6B285142)
            Local0 = (B60A >> AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xD650A284)
            Local0 = (B60A >> AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x6B285142)
            If (Y078)
            {
                Local0 = (B60A >> DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xD650A284)
                Local0 = (B60A >> DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x6B285142)
            }

            Local0 = (B60A >> DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xD650A284)
            Local0 = (B60A >> DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x6B285142)
            /* Method returns Integer */

            Local0 = (B60A >> M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xD650A284)
            Local0 = (B60A >> M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x6B285142)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A >> DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xD650A284)
                Local0 = (B60A >> DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x6B285142)
            }

            /* Conversion of the second operand */

            Store ((0x0321 >> B60E), Local0)
            M600 (Arg0, 0x18, Local0, 0x00)
            Store ((0xD650A284 >> B60E), Local0)
            M600 (Arg0, 0x19, Local0, 0x001ACA14)
            Store ((AUI1 >> B60E), Local0)
            M600 (Arg0, 0x1A, Local0, 0x00)
            Store ((AUIK >> B60E), Local0)
            M600 (Arg0, 0x1B, Local0, 0x001ACA14)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI1)) >> B60E), Local0)
                M600 (Arg0, 0x1C, Local0, 0x00)
                Store ((DerefOf (RefOf (AUIK)) >> B60E), Local0)
                M600 (Arg0, 0x1D, Local0, 0x001ACA14)
            }

            Store ((DerefOf (PAUI [0x01]) >> B60E), Local0)
            M600 (Arg0, 0x1E, Local0, 0x00)
            Store ((DerefOf (PAUI [0x14]) >> B60E), Local0)
            M600 (Arg0, 0x1F, Local0, 0x001ACA14)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x01) >> B60E), Local0)
            M600 (Arg0, 0x20, Local0, 0x00)
            Store ((M601 (0x01, 0x14) >> B60E), Local0)
            M600 (Arg0, 0x21, Local0, 0x001ACA14)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x01, 0x01)) >> B60E), Local0)
                M600 (Arg0, 0x22, Local0, 0x00)
                Store ((DerefOf (M602 (0x01, 0x14, 0x01)) >> B60E), Local0)
                M600 (Arg0, 0x23, Local0, 0x001ACA14)
            }

            Local0 = (0x0321 >> B60E) /* \M613.M058.B60E */
            M600 (Arg0, 0x24, Local0, 0x00)
            Local0 = (0xD650A284 >> B60E) /* \M613.M058.B60E */
            M600 (Arg0, 0x25, Local0, 0x001ACA14)
            Local0 = (AUI1 >> B60E) /* \M613.M058.B60E */
            M600 (Arg0, 0x26, Local0, 0x00)
            Local0 = (AUIK >> B60E) /* \M613.M058.B60E */
            M600 (Arg0, 0x27, Local0, 0x001ACA14)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) >> B60E) /* \M613.M058.B60E */
                M600 (Arg0, 0x28, Local0, 0x00)
                Local0 = (DerefOf (RefOf (AUIK)) >> B60E) /* \M613.M058.B60E */
                M600 (Arg0, 0x29, Local0, 0x001ACA14)
            }

            Local0 = (DerefOf (PAUI [0x01]) >> B60E) /* \M613.M058.B60E */
            M600 (Arg0, 0x2A, Local0, 0x00)
            Local0 = (DerefOf (PAUI [0x14]) >> B60E) /* \M613.M058.B60E */
            M600 (Arg0, 0x2B, Local0, 0x001ACA14)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) >> B60E) /* \M613.M058.B60E */
            M600 (Arg0, 0x2C, Local0, 0x00)
            Local0 = (M601 (0x01, 0x14) >> B60E) /* \M613.M058.B60E */
            M600 (Arg0, 0x2D, Local0, 0x001ACA14)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) >> B60E) /* \M613.M058.B60E */
                M600 (Arg0, 0x2E, Local0, 0x00)
                Local0 = (DerefOf (M602 (0x01, 0x14, 0x01)) >> B60E) /* \M613.M058.B60E */
                M600 (Arg0, 0x2F, Local0, 0x001ACA14)
            }

            /* Conversion of the both operands */

            Store ((B606 >> B60E), Local0)
            M600 (Arg0, 0x30, Local0, 0x00)
            Store ((B60A >> B60E), Local0)
            M600 (Arg0, 0x31, Local0, 0x001ACA14)
            Local0 = (B606 >> B60E) /* \M613.M058.B60E */
            M600 (Arg0, 0x32, Local0, 0x00)
            Local0 = (B60A >> B60E) /* \M613.M058.B60E */
            M600 (Arg0, 0x33, Local0, 0x001ACA14)
        }

        /* Subtract, common 32-bit/64-bit test */

        Method (M059, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            /* Conversion of the first operand */

            Store ((B606 - 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((B606 - 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0x0320)
            Store ((B606 - AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((B606 - AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0x0320)
            If (Y078)
            {
                Store ((B606 - DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((B606 - DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0x0320)
            }

            Store ((B606 - DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((B606 - DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0x0320)
            /* Method returns Integer */

            Store ((B606 - M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((B606 - M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0x0320)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B606 - DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((B606 - DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x0320)
            }

            Local0 = (B606 - 0x00)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (B606 - 0x01)
            M600 (Arg0, 0x0D, Local0, 0x0320)
            Local0 = (B606 - AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (B606 - AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0x0320)
            If (Y078)
            {
                Local0 = (B606 - DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (B606 - DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0x0320)
            }

            Local0 = (B606 - DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (B606 - DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0x0320)
            /* Method returns Integer */

            Local0 = (B606 - M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (B606 - M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0x0320)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B606 - DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (B606 - DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x0320)
            }

            /* Conversion of the second operand */

            Store ((0x00 - B606), Local0)
            M600 (Arg0, 0x18, Local0, 0xFFFFFFFFFFFFFCDF)
            Store ((0x01 - B606), Local0)
            M600 (Arg0, 0x19, Local0, 0xFFFFFFFFFFFFFCE0)
            Store ((AUI5 - B606), Local0)
            M600 (Arg0, 0x1A, Local0, 0xFFFFFFFFFFFFFCDF)
            Store ((AUI6 - B606), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFFFFFFFFFFFFFCE0)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) - B606), Local0)
                M600 (Arg0, 0x1C, Local0, 0xFFFFFFFFFFFFFCDF)
                Store ((DerefOf (RefOf (AUI6)) - B606), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFFFFFFFFFFFFFCE0)
            }

            Store ((DerefOf (PAUI [0x05]) - B606), Local0)
            M600 (Arg0, 0x1E, Local0, 0xFFFFFFFFFFFFFCDF)
            Store ((DerefOf (PAUI [0x06]) - B606), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFFFFFFFFFFFFFCE0)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) - B606), Local0)
            M600 (Arg0, 0x20, Local0, 0xFFFFFFFFFFFFFCDF)
            Store ((M601 (0x01, 0x06) - B606), Local0)
            M600 (Arg0, 0x21, Local0, 0xFFFFFFFFFFFFFCE0)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) - B606), Local0)
                M600 (Arg0, 0x22, Local0, 0xFFFFFFFFFFFFFCDF)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) - B606), Local0)
                M600 (Arg0, 0x23, Local0, 0xFFFFFFFFFFFFFCE0)
            }

            Local0 = (0x00 - B606) /* \M613.M059.B606 */
            M600 (Arg0, 0x24, Local0, 0xFFFFFFFFFFFFFCDF)
            Local0 = (0x01 - B606) /* \M613.M059.B606 */
            M600 (Arg0, 0x25, Local0, 0xFFFFFFFFFFFFFCE0)
            Local0 = (AUI5 - B606) /* \M613.M059.B606 */
            M600 (Arg0, 0x26, Local0, 0xFFFFFFFFFFFFFCDF)
            Local0 = (AUI6 - B606) /* \M613.M059.B606 */
            M600 (Arg0, 0x27, Local0, 0xFFFFFFFFFFFFFCE0)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) - B606) /* \M613.M059.B606 */
                M600 (Arg0, 0x28, Local0, 0xFFFFFFFFFFFFFCDF)
                Local0 = (DerefOf (RefOf (AUI6)) - B606) /* \M613.M059.B606 */
                M600 (Arg0, 0x29, Local0, 0xFFFFFFFFFFFFFCE0)
            }

            Local0 = (DerefOf (PAUI [0x05]) - B606) /* \M613.M059.B606 */
            M600 (Arg0, 0x2A, Local0, 0xFFFFFFFFFFFFFCDF)
            Local0 = (DerefOf (PAUI [0x06]) - B606) /* \M613.M059.B606 */
            M600 (Arg0, 0x2B, Local0, 0xFFFFFFFFFFFFFCE0)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) - B606) /* \M613.M059.B606 */
            M600 (Arg0, 0x2C, Local0, 0xFFFFFFFFFFFFFCDF)
            Local0 = (M601 (0x01, 0x06) - B606) /* \M613.M059.B606 */
            M600 (Arg0, 0x2D, Local0, 0xFFFFFFFFFFFFFCE0)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) - B606) /* \M613.M059.B606 */
                M600 (Arg0, 0x2E, Local0, 0xFFFFFFFFFFFFFCDF)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) - B606) /* \M613.M059.B606 */
                M600 (Arg0, 0x2F, Local0, 0xFFFFFFFFFFFFFCE0)
            }
        }

        /* Subtract, 64-bit */

        Method (M05A, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A - 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((B60A - 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xFE7CB391D650A283)
            Store ((B60A - AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((B60A - AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xFE7CB391D650A283)
            If (Y078)
            {
                Store ((B60A - DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((B60A - DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFE7CB391D650A283)
            }

            Store ((B60A - DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((B60A - DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFE7CB391D650A283)
            /* Method returns Integer */

            Store ((B60A - M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((B60A - M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFE7CB391D650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A - DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((B60A - DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFE7CB391D650A283)
            }

            Local0 = (B60A - 0x00)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A - 0x01)
            M600 (Arg0, 0x0D, Local0, 0xFE7CB391D650A283)
            Local0 = (B60A - AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A - AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xFE7CB391D650A283)
            If (Y078)
            {
                Local0 = (B60A - DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (B60A - DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xFE7CB391D650A283)
            }

            Local0 = (B60A - DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A - DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xFE7CB391D650A283)
            /* Method returns Integer */

            Local0 = (B60A - M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A - M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xFE7CB391D650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A - DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (B60A - DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFE7CB391D650A283)
            }

            /* Conversion of the second operand */

            Store ((0x00 - B60A), Local0)
            M600 (Arg0, 0x18, Local0, 0x01834C6E29AF5D7C)
            Store ((0x01 - B60A), Local0)
            M600 (Arg0, 0x19, Local0, 0x01834C6E29AF5D7D)
            Store ((AUI5 - B60A), Local0)
            M600 (Arg0, 0x1A, Local0, 0x01834C6E29AF5D7C)
            Store ((AUI6 - B60A), Local0)
            M600 (Arg0, 0x1B, Local0, 0x01834C6E29AF5D7D)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) - B60A), Local0)
                M600 (Arg0, 0x1C, Local0, 0x01834C6E29AF5D7C)
                Store ((DerefOf (RefOf (AUI6)) - B60A), Local0)
                M600 (Arg0, 0x1D, Local0, 0x01834C6E29AF5D7D)
            }

            Store ((DerefOf (PAUI [0x05]) - B60A), Local0)
            M600 (Arg0, 0x1E, Local0, 0x01834C6E29AF5D7C)
            Store ((DerefOf (PAUI [0x06]) - B60A), Local0)
            M600 (Arg0, 0x1F, Local0, 0x01834C6E29AF5D7D)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) - B60A), Local0)
            M600 (Arg0, 0x20, Local0, 0x01834C6E29AF5D7C)
            Store ((M601 (0x01, 0x06) - B60A), Local0)
            M600 (Arg0, 0x21, Local0, 0x01834C6E29AF5D7D)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) - B60A), Local0)
                M600 (Arg0, 0x22, Local0, 0x01834C6E29AF5D7C)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) - B60A), Local0)
                M600 (Arg0, 0x23, Local0, 0x01834C6E29AF5D7D)
            }

            Local0 = (0x00 - B60A) /* \M613.M05A.B60A */
            M600 (Arg0, 0x24, Local0, 0x01834C6E29AF5D7C)
            Local0 = (0x01 - B60A) /* \M613.M05A.B60A */
            M600 (Arg0, 0x25, Local0, 0x01834C6E29AF5D7D)
            Local0 = (AUI5 - B60A) /* \M613.M05A.B60A */
            M600 (Arg0, 0x26, Local0, 0x01834C6E29AF5D7C)
            Local0 = (AUI6 - B60A) /* \M613.M05A.B60A */
            M600 (Arg0, 0x27, Local0, 0x01834C6E29AF5D7D)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) - B60A) /* \M613.M05A.B60A */
                M600 (Arg0, 0x28, Local0, 0x01834C6E29AF5D7C)
                Local0 = (DerefOf (RefOf (AUI6)) - B60A) /* \M613.M05A.B60A */
                M600 (Arg0, 0x29, Local0, 0x01834C6E29AF5D7D)
            }

            Local0 = (DerefOf (PAUI [0x05]) - B60A) /* \M613.M05A.B60A */
            M600 (Arg0, 0x2A, Local0, 0x01834C6E29AF5D7C)
            Local0 = (DerefOf (PAUI [0x06]) - B60A) /* \M613.M05A.B60A */
            M600 (Arg0, 0x2B, Local0, 0x01834C6E29AF5D7D)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) - B60A) /* \M613.M05A.B60A */
            M600 (Arg0, 0x2C, Local0, 0x01834C6E29AF5D7C)
            Local0 = (M601 (0x01, 0x06) - B60A) /* \M613.M05A.B60A */
            M600 (Arg0, 0x2D, Local0, 0x01834C6E29AF5D7D)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) - B60A) /* \M613.M05A.B60A */
                M600 (Arg0, 0x2E, Local0, 0x01834C6E29AF5D7C)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) - B60A) /* \M613.M05A.B60A */
                M600 (Arg0, 0x2F, Local0, 0x01834C6E29AF5D7D)
            }

            /* Conversion of the both operands */

            Store ((B606 - B60A), Local0)
            M600 (Arg0, 0x30, Local0, 0x01834C6E29AF609D)
            Store ((B60A - B606), Local0)
            M600 (Arg0, 0x31, Local0, 0xFE7CB391D6509F63)
            Local0 = (B606 - B60A) /* \M613.M05A.B60A */
            M600 (Arg0, 0x32, Local0, 0x01834C6E29AF609D)
            Local0 = (B60A - B606) /* \M613.M05A.B606 */
            M600 (Arg0, 0x33, Local0, 0xFE7CB391D6509F63)
        }

        /* Subtract, 32-bit */

        Method (M05B, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A - 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xD650A284)
            Store ((B60A - 0x01), Local0)
            M600 (Arg0, 0x01, Local0, 0xD650A283)
            Store ((B60A - AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xD650A284)
            Store ((B60A - AUI6), Local0)
            M600 (Arg0, 0x03, Local0, 0xD650A283)
            If (Y078)
            {
                Store ((B60A - DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xD650A284)
                Store ((B60A - DerefOf (RefOf (AUI6))), Local0)
                M600 (Arg0, 0x05, Local0, 0xD650A283)
            }

            Store ((B60A - DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xD650A284)
            Store ((B60A - DerefOf (PAUI [0x06])), Local0)
            M600 (Arg0, 0x07, Local0, 0xD650A283)
            /* Method returns Integer */

            Store ((B60A - M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xD650A284)
            Store ((B60A - M601 (0x01, 0x06)), Local0)
            M600 (Arg0, 0x09, Local0, 0xD650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A - DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xD650A284)
                Store ((B60A - DerefOf (M602 (0x01, 0x06, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xD650A283)
            }

            Local0 = (B60A - 0x00)
            M600 (Arg0, 0x0C, Local0, 0xD650A284)
            Local0 = (B60A - 0x01)
            M600 (Arg0, 0x0D, Local0, 0xD650A283)
            Local0 = (B60A - AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xD650A284)
            Local0 = (B60A - AUI6) /* \AUI6 */
            M600 (Arg0, 0x0F, Local0, 0xD650A283)
            If (Y078)
            {
                Local0 = (B60A - DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xD650A284)
                Local0 = (B60A - DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x11, Local0, 0xD650A283)
            }

            Local0 = (B60A - DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xD650A284)
            Local0 = (B60A - DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x13, Local0, 0xD650A283)
            /* Method returns Integer */

            Local0 = (B60A - M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xD650A284)
            Local0 = (B60A - M601 (0x01, 0x06))
            M600 (Arg0, 0x15, Local0, 0xD650A283)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A - DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xD650A284)
                Local0 = (B60A - DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xD650A283)
            }

            /* Conversion of the second operand */

            Store ((0x00 - B60A), Local0)
            M600 (Arg0, 0x18, Local0, 0x29AF5D7C)
            Store ((0x01 - B60A), Local0)
            M600 (Arg0, 0x19, Local0, 0x29AF5D7D)
            Store ((AUI5 - B60A), Local0)
            M600 (Arg0, 0x1A, Local0, 0x29AF5D7C)
            Store ((AUI6 - B60A), Local0)
            M600 (Arg0, 0x1B, Local0, 0x29AF5D7D)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) - B60A), Local0)
                M600 (Arg0, 0x1C, Local0, 0x29AF5D7C)
                Store ((DerefOf (RefOf (AUI6)) - B60A), Local0)
                M600 (Arg0, 0x1D, Local0, 0x29AF5D7D)
            }

            Store ((DerefOf (PAUI [0x05]) - B60A), Local0)
            M600 (Arg0, 0x1E, Local0, 0x29AF5D7C)
            Store ((DerefOf (PAUI [0x06]) - B60A), Local0)
            M600 (Arg0, 0x1F, Local0, 0x29AF5D7D)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) - B60A), Local0)
            M600 (Arg0, 0x20, Local0, 0x29AF5D7C)
            Store ((M601 (0x01, 0x06) - B60A), Local0)
            M600 (Arg0, 0x21, Local0, 0x29AF5D7D)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) - B60A), Local0)
                M600 (Arg0, 0x22, Local0, 0x29AF5D7C)
                Store ((DerefOf (M602 (0x01, 0x06, 0x01)) - B60A), Local0)
                M600 (Arg0, 0x23, Local0, 0x29AF5D7D)
            }

            Local0 = (0x00 - B60A) /* \M613.M05B.B60A */
            M600 (Arg0, 0x24, Local0, 0x29AF5D7C)
            Local0 = (0x01 - B60A) /* \M613.M05B.B60A */
            M600 (Arg0, 0x25, Local0, 0x29AF5D7D)
            Local0 = (AUI5 - B60A) /* \M613.M05B.B60A */
            M600 (Arg0, 0x26, Local0, 0x29AF5D7C)
            Local0 = (AUI6 - B60A) /* \M613.M05B.B60A */
            M600 (Arg0, 0x27, Local0, 0x29AF5D7D)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) - B60A) /* \M613.M05B.B60A */
                M600 (Arg0, 0x28, Local0, 0x29AF5D7C)
                Local0 = (DerefOf (RefOf (AUI6)) - B60A) /* \M613.M05B.B60A */
                M600 (Arg0, 0x29, Local0, 0x29AF5D7D)
            }

            Local0 = (DerefOf (PAUI [0x05]) - B60A) /* \M613.M05B.B60A */
            M600 (Arg0, 0x2A, Local0, 0x29AF5D7C)
            Local0 = (DerefOf (PAUI [0x06]) - B60A) /* \M613.M05B.B60A */
            M600 (Arg0, 0x2B, Local0, 0x29AF5D7D)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) - B60A) /* \M613.M05B.B60A */
            M600 (Arg0, 0x2C, Local0, 0x29AF5D7C)
            Local0 = (M601 (0x01, 0x06) - B60A) /* \M613.M05B.B60A */
            M600 (Arg0, 0x2D, Local0, 0x29AF5D7D)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) - B60A) /* \M613.M05B.B60A */
                M600 (Arg0, 0x2E, Local0, 0x29AF5D7C)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) - B60A) /* \M613.M05B.B60A */
                M600 (Arg0, 0x2F, Local0, 0x29AF5D7D)
            }

            /* Conversion of the both operands */

            Store ((B606 - B60A), Local0)
            M600 (Arg0, 0x30, Local0, 0x29AF609D)
            Store ((B60A - B606), Local0)
            M600 (Arg0, 0x31, Local0, 0xD6509F63)
            Local0 = (B606 - B60A) /* \M613.M05B.B60A */
            M600 (Arg0, 0x32, Local0, 0x29AF609D)
            Local0 = (B60A - B606) /* \M613.M05B.B606 */
            M600 (Arg0, 0x33, Local0, 0xD6509F63)
        }

        /* XOr, common 32-bit/64-bit test */

        Method (M05C, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            /* Conversion of the first operand */

            Store ((B606 ^ 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0x0321)
            Store ((B606 ^ 0xFFFFFFFFFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0xFFFFFFFFFFFFFCDE)
            Store ((B606 ^ AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0x0321)
            Store ((B606 ^ AUIJ), Local0)
            M600 (Arg0, 0x03, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                Store ((B606 ^ DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0x0321)
                Store ((B606 ^ DerefOf (RefOf (AUIJ))), Local0)
                M600 (Arg0, 0x05, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Store ((B606 ^ DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0x0321)
            Store ((B606 ^ DerefOf (PAUI [0x13])), Local0)
            M600 (Arg0, 0x07, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            Store ((B606 ^ M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0x0321)
            Store ((B606 ^ M601 (0x01, 0x13)), Local0)
            M600 (Arg0, 0x09, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B606 ^ DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0x0321)
                Store ((B606 ^ DerefOf (M602 (0x01, 0x13, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Local0 = (B606 ^ 0x00)
            M600 (Arg0, 0x0C, Local0, 0x0321)
            Local0 = (B606 ^ 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = (B606 ^ AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0x0321)
            Local0 = (B606 ^ AUIJ) /* \AUIJ */
            M600 (Arg0, 0x0F, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                Local0 = (B606 ^ DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0x0321)
                Local0 = (B606 ^ DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x11, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Local0 = (B606 ^ DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0x0321)
            Local0 = (B606 ^ DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x13, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            Local0 = (B606 ^ M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0x0321)
            Local0 = (B606 ^ M601 (0x01, 0x13))
            M600 (Arg0, 0x15, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B606 ^ DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0x0321)
                Local0 = (B606 ^ DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x17, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            /* Conversion of the second operand */

            Store ((0x00 ^ B606), Local0)
            M600 (Arg0, 0x18, Local0, 0x0321)
            Store ((0xFFFFFFFFFFFFFFFF ^ B606), Local0)
            M600 (Arg0, 0x19, Local0, 0xFFFFFFFFFFFFFCDE)
            Store ((AUI5 ^ B606), Local0)
            M600 (Arg0, 0x1A, Local0, 0x0321)
            Store ((AUIJ ^ B606), Local0)
            M600 (Arg0, 0x1B, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) ^ B606), Local0)
                M600 (Arg0, 0x1C, Local0, 0x0321)
                Store ((DerefOf (RefOf (AUIJ)) ^ B606), Local0)
                M600 (Arg0, 0x1D, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Store ((DerefOf (PAUI [0x05]) ^ B606), Local0)
            M600 (Arg0, 0x1E, Local0, 0x0321)
            Store ((DerefOf (PAUI [0x13]) ^ B606), Local0)
            M600 (Arg0, 0x1F, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) ^ B606), Local0)
            M600 (Arg0, 0x20, Local0, 0x0321)
            Store ((M601 (0x01, 0x13) ^ B606), Local0)
            M600 (Arg0, 0x21, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) ^ B606), Local0)
                M600 (Arg0, 0x22, Local0, 0x0321)
                Store ((DerefOf (M602 (0x01, 0x13, 0x01)) ^ B606), Local0)
                M600 (Arg0, 0x23, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Local0 = (0x00 ^ B606) /* \M613.M05C.B606 */
            M600 (Arg0, 0x24, Local0, 0x0321)
            Local0 = (0xFFFFFFFFFFFFFFFF ^ B606) /* \M613.M05C.B606 */
            M600 (Arg0, 0x25, Local0, 0xFFFFFFFFFFFFFCDE)
            Local0 = (AUI5 ^ B606) /* \M613.M05C.B606 */
            M600 (Arg0, 0x26, Local0, 0x0321)
            Local0 = (AUIJ ^ B606) /* \M613.M05C.B606 */
            M600 (Arg0, 0x27, Local0, 0xFFFFFFFFFFFFFCDE)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) ^ B606) /* \M613.M05C.B606 */
                M600 (Arg0, 0x28, Local0, 0x0321)
                Local0 = (DerefOf (RefOf (AUIJ)) ^ B606) /* \M613.M05C.B606 */
                M600 (Arg0, 0x29, Local0, 0xFFFFFFFFFFFFFCDE)
            }

            Local0 = (DerefOf (PAUI [0x05]) ^ B606) /* \M613.M05C.B606 */
            M600 (Arg0, 0x2A, Local0, 0x0321)
            Local0 = (DerefOf (PAUI [0x13]) ^ B606) /* \M613.M05C.B606 */
            M600 (Arg0, 0x2B, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) ^ B606) /* \M613.M05C.B606 */
            M600 (Arg0, 0x2C, Local0, 0x0321)
            Local0 = (M601 (0x01, 0x13) ^ B606) /* \M613.M05C.B606 */
            M600 (Arg0, 0x2D, Local0, 0xFFFFFFFFFFFFFCDE)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) ^ B606) /* \M613.M05C.B606 */
                M600 (Arg0, 0x2E, Local0, 0x0321)
                Local0 = (DerefOf (M602 (0x01, 0x13, 0x01)) ^ B606) /* \M613.M05C.B606 */
                M600 (Arg0, 0x2F, Local0, 0xFFFFFFFFFFFFFCDE)
            }
        }

        /* XOr, 64-bit */

        Method (M05D, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A ^ 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xFE7CB391D650A284)
            Store ((B60A ^ 0xFFFFFFFFFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0x01834C6E29AF5D7B)
            Store ((B60A ^ AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xFE7CB391D650A284)
            Store ((B60A ^ AUIJ), Local0)
            M600 (Arg0, 0x03, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                Store ((B60A ^ DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xFE7CB391D650A284)
                Store ((B60A ^ DerefOf (RefOf (AUIJ))), Local0)
                M600 (Arg0, 0x05, Local0, 0x01834C6E29AF5D7B)
            }

            Store ((B60A ^ DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xFE7CB391D650A284)
            Store ((B60A ^ DerefOf (PAUI [0x13])), Local0)
            M600 (Arg0, 0x07, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            Store ((B60A ^ M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xFE7CB391D650A284)
            Store ((B60A ^ M601 (0x01, 0x13)), Local0)
            M600 (Arg0, 0x09, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A ^ DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xFE7CB391D650A284)
                Store ((B60A ^ DerefOf (M602 (0x01, 0x13, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x01834C6E29AF5D7B)
            }

            Local0 = (B60A ^ 0x00)
            M600 (Arg0, 0x0C, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A ^ 0xFFFFFFFFFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0x01834C6E29AF5D7B)
            Local0 = (B60A ^ AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A ^ AUIJ) /* \AUIJ */
            M600 (Arg0, 0x0F, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                Local0 = (B60A ^ DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xFE7CB391D650A284)
                Local0 = (B60A ^ DerefOf (RefOf (AUIJ)))
                M600 (Arg0, 0x11, Local0, 0x01834C6E29AF5D7B)
            }

            Local0 = (B60A ^ DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A ^ DerefOf (PAUI [0x13]))
            M600 (Arg0, 0x13, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            Local0 = (B60A ^ M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xFE7CB391D650A284)
            Local0 = (B60A ^ M601 (0x01, 0x13))
            M600 (Arg0, 0x15, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A ^ DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xFE7CB391D650A284)
                Local0 = (B60A ^ DerefOf (M602 (0x01, 0x13, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x01834C6E29AF5D7B)
            }

            /* Conversion of the second operand */

            Store ((0x00 ^ B60A), Local0)
            M600 (Arg0, 0x18, Local0, 0xFE7CB391D650A284)
            Store ((0xFFFFFFFFFFFFFFFF ^ B60A), Local0)
            M600 (Arg0, 0x19, Local0, 0x01834C6E29AF5D7B)
            Store ((AUI5 ^ B60A), Local0)
            M600 (Arg0, 0x1A, Local0, 0xFE7CB391D650A284)
            Store ((AUIJ ^ B60A), Local0)
            M600 (Arg0, 0x1B, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) ^ B60A), Local0)
                M600 (Arg0, 0x1C, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (RefOf (AUIJ)) ^ B60A), Local0)
                M600 (Arg0, 0x1D, Local0, 0x01834C6E29AF5D7B)
            }

            Store ((DerefOf (PAUI [0x05]) ^ B60A), Local0)
            M600 (Arg0, 0x1E, Local0, 0xFE7CB391D650A284)
            Store ((DerefOf (PAUI [0x13]) ^ B60A), Local0)
            M600 (Arg0, 0x1F, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) ^ B60A), Local0)
            M600 (Arg0, 0x20, Local0, 0xFE7CB391D650A284)
            Store ((M601 (0x01, 0x13) ^ B60A), Local0)
            M600 (Arg0, 0x21, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) ^ B60A), Local0)
                M600 (Arg0, 0x22, Local0, 0xFE7CB391D650A284)
                Store ((DerefOf (M602 (0x01, 0x13, 0x01)) ^ B60A), Local0)
                M600 (Arg0, 0x23, Local0, 0x01834C6E29AF5D7B)
            }

            Local0 = (0x00 ^ B60A) /* \M613.M05D.B60A */
            M600 (Arg0, 0x24, Local0, 0xFE7CB391D650A284)
            Local0 = (0xFFFFFFFFFFFFFFFF ^ B60A) /* \M613.M05D.B60A */
            M600 (Arg0, 0x25, Local0, 0x01834C6E29AF5D7B)
            Local0 = (AUI5 ^ B60A) /* \M613.M05D.B60A */
            M600 (Arg0, 0x26, Local0, 0xFE7CB391D650A284)
            Local0 = (AUIJ ^ B60A) /* \M613.M05D.B60A */
            M600 (Arg0, 0x27, Local0, 0x01834C6E29AF5D7B)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) ^ B60A) /* \M613.M05D.B60A */
                M600 (Arg0, 0x28, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (RefOf (AUIJ)) ^ B60A) /* \M613.M05D.B60A */
                M600 (Arg0, 0x29, Local0, 0x01834C6E29AF5D7B)
            }

            Local0 = (DerefOf (PAUI [0x05]) ^ B60A) /* \M613.M05D.B60A */
            M600 (Arg0, 0x2A, Local0, 0xFE7CB391D650A284)
            Local0 = (DerefOf (PAUI [0x13]) ^ B60A) /* \M613.M05D.B60A */
            M600 (Arg0, 0x2B, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) ^ B60A) /* \M613.M05D.B60A */
            M600 (Arg0, 0x2C, Local0, 0xFE7CB391D650A284)
            Local0 = (M601 (0x01, 0x13) ^ B60A) /* \M613.M05D.B60A */
            M600 (Arg0, 0x2D, Local0, 0x01834C6E29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) ^ B60A) /* \M613.M05D.B60A */
                M600 (Arg0, 0x2E, Local0, 0xFE7CB391D650A284)
                Local0 = (DerefOf (M602 (0x01, 0x13, 0x01)) ^ B60A) /* \M613.M05D.B60A */
                M600 (Arg0, 0x2F, Local0, 0x01834C6E29AF5D7B)
            }

            /* Conversion of the both operands */

            Store ((B606 ^ B60A), Local0)
            M600 (Arg0, 0x30, Local0, 0xFE7CB391D650A1A5)
            Store ((B60A ^ B606), Local0)
            M600 (Arg0, 0x31, Local0, 0xFE7CB391D650A1A5)
            Local0 = (B606 ^ B60A) /* \M613.M05D.B60A */
            M600 (Arg0, 0x32, Local0, 0xFE7CB391D650A1A5)
            Local0 = (B60A ^ B606) /* \M613.M05D.B606 */
            M600 (Arg0, 0x33, Local0, 0xFE7CB391D650A1A5)
        }

        /* XOr, 32-bit */

        Method (M05E, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Store ((B60A ^ 0x00), Local0)
            M600 (Arg0, 0x00, Local0, 0xD650A284)
            Store ((B60A ^ 0xFFFFFFFF), Local0)
            M600 (Arg0, 0x01, Local0, 0x29AF5D7B)
            Store ((B60A ^ AUI5), Local0)
            M600 (Arg0, 0x02, Local0, 0xD650A284)
            Store ((B60A ^ AUII), Local0)
            M600 (Arg0, 0x03, Local0, 0x29AF5D7B)
            If (Y078)
            {
                Store ((B60A ^ DerefOf (RefOf (AUI5))), Local0)
                M600 (Arg0, 0x04, Local0, 0xD650A284)
                Store ((B60A ^ DerefOf (RefOf (AUII))), Local0)
                M600 (Arg0, 0x05, Local0, 0x29AF5D7B)
            }

            Store ((B60A ^ DerefOf (PAUI [0x05])), Local0)
            M600 (Arg0, 0x06, Local0, 0xD650A284)
            Store ((B60A ^ DerefOf (PAUI [0x12])), Local0)
            M600 (Arg0, 0x07, Local0, 0x29AF5D7B)
            /* Method returns Integer */

            Store ((B60A ^ M601 (0x01, 0x05)), Local0)
            M600 (Arg0, 0x08, Local0, 0xD650A284)
            Store ((B60A ^ M601 (0x01, 0x12)), Local0)
            M600 (Arg0, 0x09, Local0, 0x29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((B60A ^ DerefOf (M602 (0x01, 0x05, 0x01))), Local0)
                M600 (Arg0, 0x0A, Local0, 0xD650A284)
                Store ((B60A ^ DerefOf (M602 (0x01, 0x12, 0x01))), Local0)
                M600 (Arg0, 0x0B, Local0, 0x29AF5D7B)
            }

            Local0 = (B60A ^ 0x00)
            M600 (Arg0, 0x0C, Local0, 0xD650A284)
            Local0 = (B60A ^ 0xFFFFFFFF)
            M600 (Arg0, 0x0D, Local0, 0x29AF5D7B)
            Local0 = (B60A ^ AUI5) /* \AUI5 */
            M600 (Arg0, 0x0E, Local0, 0xD650A284)
            Local0 = (B60A ^ AUII) /* \AUII */
            M600 (Arg0, 0x0F, Local0, 0x29AF5D7B)
            If (Y078)
            {
                Local0 = (B60A ^ DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x10, Local0, 0xD650A284)
                Local0 = (B60A ^ DerefOf (RefOf (AUII)))
                M600 (Arg0, 0x11, Local0, 0x29AF5D7B)
            }

            Local0 = (B60A ^ DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x12, Local0, 0xD650A284)
            Local0 = (B60A ^ DerefOf (PAUI [0x12]))
            M600 (Arg0, 0x13, Local0, 0x29AF5D7B)
            /* Method returns Integer */

            Local0 = (B60A ^ M601 (0x01, 0x05))
            M600 (Arg0, 0x14, Local0, 0xD650A284)
            Local0 = (B60A ^ M601 (0x01, 0x12))
            M600 (Arg0, 0x15, Local0, 0x29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A ^ DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x16, Local0, 0xD650A284)
                Local0 = (B60A ^ DerefOf (M602 (0x01, 0x12, 0x01)))
                M600 (Arg0, 0x17, Local0, 0x29AF5D7B)
            }

            /* Conversion of the second operand */

            Store ((0x00 ^ B60A), Local0)
            M600 (Arg0, 0x18, Local0, 0xD650A284)
            Store ((0xFFFFFFFF ^ B60A), Local0)
            M600 (Arg0, 0x19, Local0, 0x29AF5D7B)
            Store ((AUI5 ^ B60A), Local0)
            M600 (Arg0, 0x1A, Local0, 0xD650A284)
            Store ((AUII ^ B60A), Local0)
            M600 (Arg0, 0x1B, Local0, 0x29AF5D7B)
            If (Y078)
            {
                Store ((DerefOf (RefOf (AUI5)) ^ B60A), Local0)
                M600 (Arg0, 0x1C, Local0, 0xD650A284)
                Store ((DerefOf (RefOf (AUII)) ^ B60A), Local0)
                M600 (Arg0, 0x1D, Local0, 0x29AF5D7B)
            }

            Store ((DerefOf (PAUI [0x05]) ^ B60A), Local0)
            M600 (Arg0, 0x1E, Local0, 0xD650A284)
            Store ((DerefOf (PAUI [0x12]) ^ B60A), Local0)
            M600 (Arg0, 0x1F, Local0, 0x29AF5D7B)
            /* Method returns Integer */

            Store ((M601 (0x01, 0x05) ^ B60A), Local0)
            M600 (Arg0, 0x20, Local0, 0xD650A284)
            Store ((M601 (0x01, 0x12) ^ B60A), Local0)
            M600 (Arg0, 0x21, Local0, 0x29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Store ((DerefOf (M602 (0x01, 0x05, 0x01)) ^ B60A), Local0)
                M600 (Arg0, 0x22, Local0, 0xD650A284)
                Store ((DerefOf (M602 (0x01, 0x12, 0x01)) ^ B60A), Local0)
                M600 (Arg0, 0x23, Local0, 0x29AF5D7B)
            }

            Local0 = (0x00 ^ B60A) /* \M613.M05E.B60A */
            M600 (Arg0, 0x24, Local0, 0xD650A284)
            Local0 = (0xFFFFFFFF ^ B60A) /* \M613.M05E.B60A */
            M600 (Arg0, 0x25, Local0, 0x29AF5D7B)
            Local0 = (AUI5 ^ B60A) /* \M613.M05E.B60A */
            M600 (Arg0, 0x26, Local0, 0xD650A284)
            Local0 = (AUII ^ B60A) /* \M613.M05E.B60A */
            M600 (Arg0, 0x27, Local0, 0x29AF5D7B)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) ^ B60A) /* \M613.M05E.B60A */
                M600 (Arg0, 0x28, Local0, 0xD650A284)
                Local0 = (DerefOf (RefOf (AUII)) ^ B60A) /* \M613.M05E.B60A */
                M600 (Arg0, 0x29, Local0, 0x29AF5D7B)
            }

            Local0 = (DerefOf (PAUI [0x05]) ^ B60A) /* \M613.M05E.B60A */
            M600 (Arg0, 0x2A, Local0, 0xD650A284)
            Local0 = (DerefOf (PAUI [0x12]) ^ B60A) /* \M613.M05E.B60A */
            M600 (Arg0, 0x2B, Local0, 0x29AF5D7B)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) ^ B60A) /* \M613.M05E.B60A */
            M600 (Arg0, 0x2C, Local0, 0xD650A284)
            Local0 = (M601 (0x01, 0x12) ^ B60A) /* \M613.M05E.B60A */
            M600 (Arg0, 0x2D, Local0, 0x29AF5D7B)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) ^ B60A) /* \M613.M05E.B60A */
                M600 (Arg0, 0x2E, Local0, 0xD650A284)
                Local0 = (DerefOf (M602 (0x01, 0x12, 0x01)) ^ B60A) /* \M613.M05E.B60A */
                M600 (Arg0, 0x2F, Local0, 0x29AF5D7B)
            }

            /* Conversion of the both operands */

            Store ((B606 ^ B60A), Local0)
            M600 (Arg0, 0x30, Local0, 0xD650A1A5)
            Store ((B60A ^ B606), Local0)
            M600 (Arg0, 0x31, Local0, 0xD650A1A5)
            Local0 = (B606 ^ B60A) /* \M613.M05E.B60A */
            M600 (Arg0, 0x32, Local0, 0xD650A1A5)
            Local0 = (B60A ^ B606) /* \M613.M05E.B606 */
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

        /* Buffer to Integer conversion of each Buffer operand */
        /* of the 2-parameter Logical Integer operators LAnd and LOr */
        /* LAnd, common 32-bit/64-bit test */
        Method (M05F, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            /* Conversion of the first operand */

            Local0 = (B606 && 0x00)
            M600 (Arg0, 0x00, Local0, Zero)
            Local0 = (B606 && 0x01)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = (B606 && AUI5)
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (B606 && AUI6)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = (B606 && DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, Zero)
                Local0 = (B606 && DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = (B606 && DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, Zero)
            Local0 = (B606 && DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Integer */

            Local0 = (B606 && M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, Zero)
            Local0 = (B606 && M601 (0x01, 0x06))
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B606 && DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, Zero)
                Local0 = (B606 && DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x0B, Local0, Ones)
            }

            /* Conversion of the second operand */

            Local0 = (0x00 && B606)
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = (0x01 && B606)
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (AUI5 && B606)
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = (AUI6 && B606)
            M600 (Arg0, 0x0F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) && B606)
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUI6)) && B606)
                M600 (Arg0, 0x11, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x05]) && B606)
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x06]) && B606)
            M600 (Arg0, 0x13, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) && B606)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (M601 (0x01, 0x06) && B606)
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) && B606)
                M600 (Arg0, 0x16, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) && B606)
                M600 (Arg0, 0x17, Local0, Ones)
            }
        }

        /* LAnd, 64-bit */

        Method (M060, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Local0 = (B60A && 0x00)
            M600 (Arg0, 0x00, Local0, Zero)
            Local0 = (B60A && 0x01)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = (B60A && AUI5)
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (B60A && AUI6)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = (B60A && DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, Zero)
                Local0 = (B60A && DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = (B60A && DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, Zero)
            Local0 = (B60A && DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Integer */

            Local0 = (B60A && M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, Zero)
            Local0 = (B60A && M601 (0x01, 0x06))
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A && DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, Zero)
                Local0 = (B60A && DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x0B, Local0, Ones)
            }

            /* Conversion of the second operand */

            Local0 = (0x00 && B60A)
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = (0x01 && B60A)
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (AUI5 && B60A)
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = (AUI6 && B60A)
            M600 (Arg0, 0x0F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) && B60A)
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUI6)) && B60A)
                M600 (Arg0, 0x11, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x05]) && B60A)
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x06]) && B60A)
            M600 (Arg0, 0x13, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) && B60A)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (M601 (0x01, 0x06) && B60A)
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) && B60A)
                M600 (Arg0, 0x16, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) && B60A)
                M600 (Arg0, 0x17, Local0, Ones)
            }

            /* Conversion of the both operands */

            Local0 = (B606 && B60A)
            M600 (Arg0, 0x18, Local0, Ones)
            Local0 = (B60A && B606)
            M600 (Arg0, 0x19, Local0, Ones)
        }

        /* LAnd, 32-bit */

        Method (M061, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Local0 = (B60A && 0x00)
            M600 (Arg0, 0x00, Local0, Zero)
            Local0 = (B60A && 0x01)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = (B60A && AUI5)
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (B60A && AUI6)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = (B60A && DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, Zero)
                Local0 = (B60A && DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = (B60A && DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, Zero)
            Local0 = (B60A && DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Integer */

            Local0 = (B60A && M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, Zero)
            Local0 = (B60A && M601 (0x01, 0x06))
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A && DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, Zero)
                Local0 = (B60A && DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x0B, Local0, Ones)
            }

            /* Conversion of the second operand */

            Local0 = (0x00 && B60A)
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = (0x01 && B60A)
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (AUI5 && B60A)
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = (AUI6 && B60A)
            M600 (Arg0, 0x0F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) && B60A)
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUI6)) && B60A)
                M600 (Arg0, 0x11, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x05]) && B60A)
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x06]) && B60A)
            M600 (Arg0, 0x13, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) && B60A)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (M601 (0x01, 0x06) && B60A)
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) && B60A)
                M600 (Arg0, 0x16, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) && B60A)
                M600 (Arg0, 0x17, Local0, Ones)
            }

            /* Conversion of the both operands */

            Local0 = (B606 && B60A)
            M600 (Arg0, 0x18, Local0, Ones)
            Local0 = (B60A && B606)
            M600 (Arg0, 0x19, Local0, Ones)
        }

        /* Lor, common 32-bit/64-bit test */

        Method (M062, 1, Serialized)
        {
            Name (B600, Buffer (0x01)
            {
                 0x00                                             // .
            })
            /* Conversion of the first operand */

            Local0 = (B600 || 0x00)
            M600 (Arg0, 0x00, Local0, Zero)
            Local0 = (B600 || 0x01)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = (B600 || AUI5)
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (B600 || AUI6)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = (B600 || DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, Zero)
                Local0 = (B600 || DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = (B600 || DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, Zero)
            Local0 = (B600 || DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Integer */

            Local0 = (B600 || M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, Zero)
            Local0 = (B600 || M601 (0x01, 0x06))
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B600 || DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, Zero)
                Local0 = (B600 || DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x0B, Local0, Ones)
            }

            /* Conversion of the second operand */

            Local0 = (0x00 || B600)
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = (0x01 || B600)
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (AUI5 || B600)
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = (AUI6 || B600)
            M600 (Arg0, 0x0F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) || B600)
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUI6)) || B600)
                M600 (Arg0, 0x11, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x05]) || B600)
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x06]) || B600)
            M600 (Arg0, 0x13, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) || B600)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (M601 (0x01, 0x06) || B600)
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) || B600)
                M600 (Arg0, 0x16, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) || B600)
                M600 (Arg0, 0x17, Local0, Ones)
            }
        }

        /* Lor, 64-bit */

        Method (M063, 1, Serialized)
        {
            Name (B600, Buffer (0x01)
            {
                 0x00                                             // .
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Local0 = (B60A || 0x00)
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (B60A || 0x01)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = (B60A || AUI5)
            M600 (Arg0, 0x02, Local0, Ones)
            Local0 = (B60A || AUI6)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = (B60A || DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, Ones)
                Local0 = (B60A || DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = (B60A || DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, Ones)
            Local0 = (B60A || DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Integer */

            Local0 = (B60A || M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, Ones)
            Local0 = (B60A || M601 (0x01, 0x06))
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A || DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, Ones)
                Local0 = (B60A || DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x0B, Local0, Ones)
            }

            /* Conversion of the second operand */

            Local0 = (0x00 || B60A)
            M600 (Arg0, 0x0C, Local0, Ones)
            Local0 = (0x01 || B60A)
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (AUI5 || B60A)
            M600 (Arg0, 0x0E, Local0, Ones)
            Local0 = (AUI6 || B60A)
            M600 (Arg0, 0x0F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) || B60A)
                M600 (Arg0, 0x10, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUI6)) || B60A)
                M600 (Arg0, 0x11, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x05]) || B60A)
            M600 (Arg0, 0x12, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x06]) || B60A)
            M600 (Arg0, 0x13, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) || B60A)
            M600 (Arg0, 0x14, Local0, Ones)
            Local0 = (M601 (0x01, 0x06) || B60A)
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) || B60A)
                M600 (Arg0, 0x16, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) || B60A)
                M600 (Arg0, 0x17, Local0, Ones)
            }

            /* Conversion of the both operands */

            Local0 = (B600 || B60A)
            M600 (Arg0, 0x18, Local0, Ones)
            Local0 = (B60A || B600)
            M600 (Arg0, 0x19, Local0, Ones)
        }

        /* Lor, 32-bit */

        Method (M064, 1, Serialized)
        {
            Name (B600, Buffer (0x01)
            {
                 0x00                                             // .
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* Conversion of the first operand */

            Local0 = (B60A || 0x00)
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (B60A || 0x01)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = (B60A || AUI5)
            M600 (Arg0, 0x02, Local0, Ones)
            Local0 = (B60A || AUI6)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = (B60A || DerefOf (RefOf (AUI5)))
                M600 (Arg0, 0x04, Local0, Ones)
                Local0 = (B60A || DerefOf (RefOf (AUI6)))
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = (B60A || DerefOf (PAUI [0x05]))
            M600 (Arg0, 0x06, Local0, Ones)
            Local0 = (B60A || DerefOf (PAUI [0x06]))
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Integer */

            Local0 = (B60A || M601 (0x01, 0x05))
            M600 (Arg0, 0x08, Local0, Ones)
            Local0 = (B60A || M601 (0x01, 0x06))
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (B60A || DerefOf (M602 (0x01, 0x05, 0x01)))
                M600 (Arg0, 0x0A, Local0, Ones)
                Local0 = (B60A || DerefOf (M602 (0x01, 0x06, 0x01)))
                M600 (Arg0, 0x0B, Local0, Ones)
            }

            /* Conversion of the second operand */

            Local0 = (0x00 || B60A)
            M600 (Arg0, 0x0C, Local0, Ones)
            Local0 = (0x01 || B60A)
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = (AUI5 || B60A)
            M600 (Arg0, 0x0E, Local0, Ones)
            Local0 = (AUI6 || B60A)
            M600 (Arg0, 0x0F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI5)) || B60A)
                M600 (Arg0, 0x10, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUI6)) || B60A)
                M600 (Arg0, 0x11, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x05]) || B60A)
            M600 (Arg0, 0x12, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x06]) || B60A)
            M600 (Arg0, 0x13, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x05) || B60A)
            M600 (Arg0, 0x14, Local0, Ones)
            Local0 = (M601 (0x01, 0x06) || B60A)
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x05, 0x01)) || B60A)
                M600 (Arg0, 0x16, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x06, 0x01)) || B60A)
                M600 (Arg0, 0x17, Local0, Ones)
            }

            /* Conversion of the both operands */

            Local0 = (B600 || B60A)
            M600 (Arg0, 0x18, Local0, Ones)
            Local0 = (B60A || B600)
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

        /* Buffer to Integer conversion of the Buffer second operand of */
        /* Logical operators when the first operand is evaluated as Integer */
        /* (LEqual, LGreater, LGreaterEqual, LLess, LLessEqual, LNotEqual) */
        Method (M64P, 1, Serialized)
        {
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* LEqual */

            Local0 = (0xFE7CB391D650A284 == B60A)
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (0xFE7CB391D650A285 == B60A)
            M600 (Arg0, 0x01, Local0, Zero)
            Local0 = (0xFE7CB391D650A283 == B60A)
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (AUI4 == B60A)
            M600 (Arg0, 0x03, Local0, Ones)
            Local0 = (AUID == B60A)
            M600 (Arg0, 0x04, Local0, Zero)
            Local0 = (AUIF == B60A)
            M600 (Arg0, 0x05, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI4)) == B60A)
                M600 (Arg0, 0x06, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUID)) == B60A)
                M600 (Arg0, 0x07, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIF)) == B60A)
                M600 (Arg0, 0x08, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x04]) == B60A)
            M600 (Arg0, 0x09, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0D]) == B60A)
            M600 (Arg0, 0x0A, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0F]) == B60A)
            M600 (Arg0, 0x0B, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x04) == B60A)
            M600 (Arg0, 0x0C, Local0, Ones)
            Local0 = (M601 (0x01, 0x0D) == B60A)
            M600 (Arg0, 0x0D, Local0, Zero)
            Local0 = (M601 (0x01, 0x0F) == B60A)
            M600 (Arg0, 0x0E, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) == B60A)
                M600 (Arg0, 0x0F, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) == B60A)
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) == B60A)
                M600 (Arg0, 0x11, Local0, Zero)
            }

            /* LGreater */

            Local0 = (0xFE7CB391D650A284 > B60A)
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (0xFE7CB391D650A285 > B60A)
            M600 (Arg0, 0x13, Local0, Ones)
            Local0 = (0xFE7CB391D650A283 > B60A)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (AUI4 > B60A)
            M600 (Arg0, 0x15, Local0, Zero)
            Local0 = (AUID > B60A)
            M600 (Arg0, 0x16, Local0, Ones)
            Local0 = (AUIF > B60A)
            M600 (Arg0, 0x17, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI4)) > B60A)
                M600 (Arg0, 0x18, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUID)) > B60A)
                M600 (Arg0, 0x19, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIF)) > B60A)
                M600 (Arg0, 0x1A, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x04]) > B60A)
            M600 (Arg0, 0x1B, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0D]) > B60A)
            M600 (Arg0, 0x1C, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0F]) > B60A)
            M600 (Arg0, 0x1D, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x04) > B60A)
            M600 (Arg0, 0x1E, Local0, Zero)
            Local0 = (M601 (0x01, 0x0D) > B60A)
            M600 (Arg0, 0x1F, Local0, Ones)
            Local0 = (M601 (0x01, 0x0F) > B60A)
            M600 (Arg0, 0x20, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) > B60A)
                M600 (Arg0, 0x21, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) > B60A)
                M600 (Arg0, 0x22, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) > B60A)
                M600 (Arg0, 0x23, Local0, Zero)
            }

            /* LGreaterEqual */

            Local0 = (0xFE7CB391D650A284 >= B60A)
            M600 (Arg0, 0x24, Local0, Ones)
            Local0 = (0xFE7CB391D650A285 >= B60A)
            M600 (Arg0, 0x25, Local0, Ones)
            Local0 = (0xFE7CB391D650A283 >= B60A)
            M600 (Arg0, 0x26, Local0, Zero)
            Local0 = (AUI4 >= B60A)
            M600 (Arg0, 0x27, Local0, Ones)
            Local0 = (AUID >= B60A)
            M600 (Arg0, 0x28, Local0, Ones)
            Local0 = (AUIF >= B60A)
            M600 (Arg0, 0x29, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI4)) >= B60A)
                M600 (Arg0, 0x2A, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUID)) >= B60A)
                M600 (Arg0, 0x2B, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIF)) >= B60A)
                M600 (Arg0, 0x2C, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x04]) >= B60A)
            M600 (Arg0, 0x2D, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0D]) >= B60A)
            M600 (Arg0, 0x2E, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0F]) >= B60A)
            M600 (Arg0, 0x2F, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x04) >= B60A)
            M600 (Arg0, 0x30, Local0, Ones)
            Local0 = (M601 (0x01, 0x0D) >= B60A)
            M600 (Arg0, 0x31, Local0, Ones)
            Local0 = (M601 (0x01, 0x0F) >= B60A)
            M600 (Arg0, 0x32, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) >= B60A)
                M600 (Arg0, 0x33, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) >= B60A)
                M600 (Arg0, 0x34, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) >= B60A)
                M600 (Arg0, 0x35, Local0, Zero)
            }

            /* LLess */

            Local0 = (0xFE7CB391D650A284 < B60A)
            M600 (Arg0, 0x36, Local0, Zero)
            Local0 = (0xFE7CB391D650A285 < B60A)
            M600 (Arg0, 0x37, Local0, Zero)
            Local0 = (0xFE7CB391D650A283 < B60A)
            M600 (Arg0, 0x38, Local0, Ones)
            Local0 = (AUI4 < B60A)
            M600 (Arg0, 0x39, Local0, Zero)
            Local0 = (AUID < B60A)
            M600 (Arg0, 0x3A, Local0, Zero)
            Local0 = (AUIF < B60A)
            M600 (Arg0, 0x3B, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI4)) < B60A)
                M600 (Arg0, 0x3C, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUID)) < B60A)
                M600 (Arg0, 0x3D, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIF)) < B60A)
                M600 (Arg0, 0x3E, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x04]) < B60A)
            M600 (Arg0, 0x3F, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0D]) < B60A)
            M600 (Arg0, 0x40, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0F]) < B60A)
            M600 (Arg0, 0x41, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x04) < B60A)
            M600 (Arg0, 0x42, Local0, Zero)
            Local0 = (M601 (0x01, 0x0D) < B60A)
            M600 (Arg0, 0x43, Local0, Zero)
            Local0 = (M601 (0x01, 0x0F) < B60A)
            M600 (Arg0, 0x44, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) < B60A)
                M600 (Arg0, 0x45, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) < B60A)
                M600 (Arg0, 0x46, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) < B60A)
                M600 (Arg0, 0x47, Local0, Ones)
            }

            /* LLessEqual */

            Local0 = (0xFE7CB391D650A284 <= B60A)
            M600 (Arg0, 0x48, Local0, Ones)
            Local0 = (0xFE7CB391D650A285 <= B60A)
            M600 (Arg0, 0x49, Local0, Zero)
            Local0 = (0xFE7CB391D650A283 <= B60A)
            M600 (Arg0, 0x4A, Local0, Ones)
            Local0 = (AUI4 <= B60A)
            M600 (Arg0, 0x4B, Local0, Ones)
            Local0 = (AUID <= B60A)
            M600 (Arg0, 0x4C, Local0, Zero)
            Local0 = (AUIF <= B60A)
            M600 (Arg0, 0x4D, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI4)) <= B60A)
                M600 (Arg0, 0x4E, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUID)) <= B60A)
                M600 (Arg0, 0x4F, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIF)) <= B60A)
                M600 (Arg0, 0x50, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x04]) <= B60A)
            M600 (Arg0, 0x51, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0D]) <= B60A)
            M600 (Arg0, 0x52, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0F]) <= B60A)
            M600 (Arg0, 0x53, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x04) <= B60A)
            M600 (Arg0, 0x54, Local0, Ones)
            Local0 = (M601 (0x01, 0x0D) <= B60A)
            M600 (Arg0, 0x55, Local0, Zero)
            Local0 = (M601 (0x01, 0x0F) <= B60A)
            M600 (Arg0, 0x56, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) <= B60A)
                M600 (Arg0, 0x57, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) <= B60A)
                M600 (Arg0, 0x58, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) <= B60A)
                M600 (Arg0, 0x59, Local0, Ones)
            }

            /* LNotEqual */

            Local0 = (0xFE7CB391D650A284 != B60A)
            M600 (Arg0, 0x5A, Local0, Zero)
            Local0 = (0xFE7CB391D650A285 != B60A)
            M600 (Arg0, 0x5B, Local0, Ones)
            Local0 = (0xFE7CB391D650A283 != B60A)
            M600 (Arg0, 0x5C, Local0, Ones)
            Local0 = (AUI4 != B60A)
            M600 (Arg0, 0x5D, Local0, Zero)
            Local0 = (AUID != B60A)
            M600 (Arg0, 0x5E, Local0, Ones)
            Local0 = (AUIF != B60A)
            M600 (Arg0, 0x5F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI4)) != B60A)
                M600 (Arg0, 0x60, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUID)) != B60A)
                M600 (Arg0, 0x61, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIF)) != B60A)
                M600 (Arg0, 0x62, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x04]) != B60A)
            M600 (Arg0, 0x63, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x0D]) != B60A)
            M600 (Arg0, 0x64, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x0F]) != B60A)
            M600 (Arg0, 0x65, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x04) != B60A)
            M600 (Arg0, 0x66, Local0, Zero)
            Local0 = (M601 (0x01, 0x0D) != B60A)
            M600 (Arg0, 0x67, Local0, Ones)
            Local0 = (M601 (0x01, 0x0F) != B60A)
            M600 (Arg0, 0x68, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x04, 0x01)) != B60A)
                M600 (Arg0, 0x69, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x0D, 0x01)) != B60A)
                M600 (Arg0, 0x6A, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x0F, 0x01)) != B60A)
                M600 (Arg0, 0x6B, Local0, Ones)
            }
        }

        Method (M32P, 1, Serialized)
        {
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            /* LEqual */

            Local0 = (0xD650A284 == B60A)
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (0xD650A285 == B60A)
            M600 (Arg0, 0x01, Local0, Zero)
            Local0 = (0xD650A283 == B60A)
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (AUIK == B60A)
            M600 (Arg0, 0x03, Local0, Ones)
            Local0 = (AUIL == B60A)
            M600 (Arg0, 0x04, Local0, Zero)
            Local0 = (AUIM == B60A)
            M600 (Arg0, 0x05, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUIK)) == B60A)
                M600 (Arg0, 0x06, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIL)) == B60A)
                M600 (Arg0, 0x07, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIM)) == B60A)
                M600 (Arg0, 0x08, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x14]) == B60A)
            M600 (Arg0, 0x09, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x15]) == B60A)
            M600 (Arg0, 0x0A, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x16]) == B60A)
            M600 (Arg0, 0x0B, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x14) == B60A)
            M600 (Arg0, 0x0C, Local0, Ones)
            Local0 = (M601 (0x01, 0x15) == B60A)
            M600 (Arg0, 0x0D, Local0, Zero)
            Local0 = (M601 (0x01, 0x16) == B60A)
            M600 (Arg0, 0x0E, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x14, 0x01)) == B60A)
                M600 (Arg0, 0x0F, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x15, 0x01)) == B60A)
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x16, 0x01)) == B60A)
                M600 (Arg0, 0x11, Local0, Zero)
            }

            /* LGreater */

            Local0 = (0xD650A284 > B60A)
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (0xD650A285 > B60A)
            M600 (Arg0, 0x13, Local0, Ones)
            Local0 = (0xD650A283 > B60A)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (AUIK > B60A)
            M600 (Arg0, 0x15, Local0, Zero)
            Local0 = (AUIL > B60A)
            M600 (Arg0, 0x16, Local0, Ones)
            Local0 = (AUIM > B60A)
            M600 (Arg0, 0x17, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUIK)) > B60A)
                M600 (Arg0, 0x18, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIL)) > B60A)
                M600 (Arg0, 0x19, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIM)) > B60A)
                M600 (Arg0, 0x1A, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x14]) > B60A)
            M600 (Arg0, 0x1B, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x15]) > B60A)
            M600 (Arg0, 0x1C, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x16]) > B60A)
            M600 (Arg0, 0x1D, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x14) > B60A)
            M600 (Arg0, 0x1E, Local0, Zero)
            Local0 = (M601 (0x01, 0x15) > B60A)
            M600 (Arg0, 0x1F, Local0, Ones)
            Local0 = (M601 (0x01, 0x16) > B60A)
            M600 (Arg0, 0x20, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x14, 0x01)) > B60A)
                M600 (Arg0, 0x21, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x15, 0x01)) > B60A)
                M600 (Arg0, 0x22, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x16, 0x01)) > B60A)
                M600 (Arg0, 0x23, Local0, Zero)
            }

            /* LGreaterEqual */

            Local0 = (0xD650A284 >= B60A)
            M600 (Arg0, 0x24, Local0, Ones)
            Local0 = (0xD650A285 >= B60A)
            M600 (Arg0, 0x25, Local0, Ones)
            Local0 = (0xD650A283 >= B60A)
            M600 (Arg0, 0x26, Local0, Zero)
            Local0 = (AUIK >= B60A)
            M600 (Arg0, 0x27, Local0, Ones)
            Local0 = (AUIL >= B60A)
            M600 (Arg0, 0x28, Local0, Ones)
            Local0 = (AUIM >= B60A)
            M600 (Arg0, 0x29, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUIK)) >= B60A)
                M600 (Arg0, 0x2A, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIL)) >= B60A)
                M600 (Arg0, 0x2B, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIM)) >= B60A)
                M600 (Arg0, 0x2C, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x14]) >= B60A)
            M600 (Arg0, 0x2D, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x15]) >= B60A)
            M600 (Arg0, 0x2E, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x16]) >= B60A)
            M600 (Arg0, 0x2F, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x14) >= B60A)
            M600 (Arg0, 0x30, Local0, Ones)
            Local0 = (M601 (0x01, 0x15) >= B60A)
            M600 (Arg0, 0x31, Local0, Ones)
            Local0 = (M601 (0x01, 0x16) >= B60A)
            M600 (Arg0, 0x32, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x14, 0x01)) >= B60A)
                M600 (Arg0, 0x33, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x15, 0x01)) >= B60A)
                M600 (Arg0, 0x34, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x16, 0x01)) >= B60A)
                M600 (Arg0, 0x35, Local0, Zero)
            }

            /* LLess */

            Local0 = (0xD650A284 < B60A)
            M600 (Arg0, 0x36, Local0, Zero)
            Local0 = (0xD650A285 < B60A)
            M600 (Arg0, 0x37, Local0, Zero)
            Local0 = (0xD650A283 < B60A)
            M600 (Arg0, 0x38, Local0, Ones)
            Local0 = (AUIK < B60A)
            M600 (Arg0, 0x39, Local0, Zero)
            Local0 = (AUIL < B60A)
            M600 (Arg0, 0x3A, Local0, Zero)
            Local0 = (AUIM < B60A)
            M600 (Arg0, 0x3B, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUIK)) < B60A)
                M600 (Arg0, 0x3C, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIL)) < B60A)
                M600 (Arg0, 0x3D, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIM)) < B60A)
                M600 (Arg0, 0x3E, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x14]) < B60A)
            M600 (Arg0, 0x3F, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x15]) < B60A)
            M600 (Arg0, 0x40, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x16]) < B60A)
            M600 (Arg0, 0x41, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x14) < B60A)
            M600 (Arg0, 0x42, Local0, Zero)
            Local0 = (M601 (0x01, 0x15) < B60A)
            M600 (Arg0, 0x43, Local0, Zero)
            Local0 = (M601 (0x01, 0x16) < B60A)
            M600 (Arg0, 0x44, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x14, 0x01)) < B60A)
                M600 (Arg0, 0x45, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x15, 0x01)) < B60A)
                M600 (Arg0, 0x46, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x16, 0x01)) < B60A)
                M600 (Arg0, 0x47, Local0, Ones)
            }

            /* LLessEqual */

            Local0 = (0xD650A284 <= B60A)
            M600 (Arg0, 0x48, Local0, Ones)
            Local0 = (0xD650A285 <= B60A)
            M600 (Arg0, 0x49, Local0, Zero)
            Local0 = (0xD650A283 <= B60A)
            M600 (Arg0, 0x4A, Local0, Ones)
            Local0 = (AUIK <= B60A)
            M600 (Arg0, 0x4B, Local0, Ones)
            Local0 = (AUIL <= B60A)
            M600 (Arg0, 0x4C, Local0, Zero)
            Local0 = (AUIM <= B60A)
            M600 (Arg0, 0x4D, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUIK)) <= B60A)
                M600 (Arg0, 0x4E, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIL)) <= B60A)
                M600 (Arg0, 0x4F, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIM)) <= B60A)
                M600 (Arg0, 0x50, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x14]) <= B60A)
            M600 (Arg0, 0x51, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x15]) <= B60A)
            M600 (Arg0, 0x52, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x16]) <= B60A)
            M600 (Arg0, 0x53, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x14) <= B60A)
            M600 (Arg0, 0x54, Local0, Ones)
            Local0 = (M601 (0x01, 0x15) <= B60A)
            M600 (Arg0, 0x55, Local0, Zero)
            Local0 = (M601 (0x01, 0x16) <= B60A)
            M600 (Arg0, 0x56, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x14, 0x01)) <= B60A)
                M600 (Arg0, 0x57, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x15, 0x01)) <= B60A)
                M600 (Arg0, 0x58, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x16, 0x01)) <= B60A)
                M600 (Arg0, 0x59, Local0, Ones)
            }

            /* LNotEqual */

            Local0 = (0xD650A284 != B60A)
            M600 (Arg0, 0x5A, Local0, Zero)
            Local0 = (0xD650A285 != B60A)
            M600 (Arg0, 0x5B, Local0, Ones)
            Local0 = (0xD650A283 != B60A)
            M600 (Arg0, 0x5C, Local0, Ones)
            Local0 = (AUIK != B60A)
            M600 (Arg0, 0x5D, Local0, Zero)
            Local0 = (AUIL != B60A)
            M600 (Arg0, 0x5E, Local0, Ones)
            Local0 = (AUIM != B60A)
            M600 (Arg0, 0x5F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUIK)) != B60A)
                M600 (Arg0, 0x60, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIL)) != B60A)
                M600 (Arg0, 0x61, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIM)) != B60A)
                M600 (Arg0, 0x62, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x14]) != B60A)
            M600 (Arg0, 0x63, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x15]) != B60A)
            M600 (Arg0, 0x64, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x16]) != B60A)
            M600 (Arg0, 0x65, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x14) != B60A)
            M600 (Arg0, 0x66, Local0, Zero)
            Local0 = (M601 (0x01, 0x15) != B60A)
            M600 (Arg0, 0x67, Local0, Ones)
            Local0 = (M601 (0x01, 0x16) != B60A)
            M600 (Arg0, 0x68, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x14, 0x01)) != B60A)
                M600 (Arg0, 0x69, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x15, 0x01)) != B60A)
                M600 (Arg0, 0x6A, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x16, 0x01)) != B60A)
                M600 (Arg0, 0x6B, Local0, Ones)
            }
        }

        Method (M065, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            /* LEqual */

            Local0 = (0x0321 == B606)
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = (0x0322 == B606)
            M600 (Arg0, 0x01, Local0, Zero)
            Local0 = (0x0320 == B606)
            M600 (Arg0, 0x02, Local0, Zero)
            Local0 = (AUI1 == B606)
            M600 (Arg0, 0x03, Local0, Ones)
            Local0 = (AUIG == B606)
            M600 (Arg0, 0x04, Local0, Zero)
            Local0 = (AUIH == B606)
            M600 (Arg0, 0x05, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) == B606)
                M600 (Arg0, 0x06, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIG)) == B606)
                M600 (Arg0, 0x07, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIH)) == B606)
                M600 (Arg0, 0x08, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x01]) == B606)
            M600 (Arg0, 0x09, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x10]) == B606)
            M600 (Arg0, 0x0A, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x11]) == B606)
            M600 (Arg0, 0x0B, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) == B606)
            M600 (Arg0, 0x0C, Local0, Ones)
            Local0 = (M601 (0x01, 0x10) == B606)
            M600 (Arg0, 0x0D, Local0, Zero)
            Local0 = (M601 (0x01, 0x11) == B606)
            M600 (Arg0, 0x0E, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) == B606)
                M600 (Arg0, 0x0F, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) == B606)
                M600 (Arg0, 0x10, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) == B606)
                M600 (Arg0, 0x11, Local0, Zero)
            }

            /* LGreater */

            Local0 = (0x0321 > B606)
            M600 (Arg0, 0x12, Local0, Zero)
            Local0 = (0x0322 > B606)
            M600 (Arg0, 0x13, Local0, Ones)
            Local0 = (0x0320 > B606)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (AUI1 > B606)
            M600 (Arg0, 0x15, Local0, Zero)
            Local0 = (AUIG > B606)
            M600 (Arg0, 0x16, Local0, Ones)
            Local0 = (AUIH > B606)
            M600 (Arg0, 0x17, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) > B606)
                M600 (Arg0, 0x18, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIG)) > B606)
                M600 (Arg0, 0x19, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIH)) > B606)
                M600 (Arg0, 0x1A, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x01]) > B606)
            M600 (Arg0, 0x1B, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x10]) > B606)
            M600 (Arg0, 0x1C, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x11]) > B606)
            M600 (Arg0, 0x1D, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) > B606)
            M600 (Arg0, 0x1E, Local0, Zero)
            Local0 = (M601 (0x01, 0x10) > B606)
            M600 (Arg0, 0x1F, Local0, Ones)
            Local0 = (M601 (0x01, 0x11) > B606)
            M600 (Arg0, 0x20, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) > B606)
                M600 (Arg0, 0x21, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) > B606)
                M600 (Arg0, 0x22, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) > B606)
                M600 (Arg0, 0x23, Local0, Zero)
            }

            /* LGreaterEqual */

            Local0 = (0x0321 >= B606)
            M600 (Arg0, 0x24, Local0, Ones)
            Local0 = (0x0322 >= B606)
            M600 (Arg0, 0x25, Local0, Ones)
            Local0 = (0x0320 >= B606)
            M600 (Arg0, 0x26, Local0, Zero)
            Local0 = (AUI1 >= B606)
            M600 (Arg0, 0x27, Local0, Ones)
            Local0 = (AUIG >= B606)
            M600 (Arg0, 0x28, Local0, Ones)
            Local0 = (AUIH >= B606)
            M600 (Arg0, 0x29, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) >= B606)
                M600 (Arg0, 0x2A, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIG)) >= B606)
                M600 (Arg0, 0x2B, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIH)) >= B606)
                M600 (Arg0, 0x2C, Local0, Zero)
            }

            Local0 = (DerefOf (PAUI [0x01]) >= B606)
            M600 (Arg0, 0x2D, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x10]) >= B606)
            M600 (Arg0, 0x2E, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x11]) >= B606)
            M600 (Arg0, 0x2F, Local0, Zero)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) >= B606)
            M600 (Arg0, 0x30, Local0, Ones)
            Local0 = (M601 (0x01, 0x10) >= B606)
            M600 (Arg0, 0x31, Local0, Ones)
            Local0 = (M601 (0x01, 0x11) >= B606)
            M600 (Arg0, 0x32, Local0, Zero)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) >= B606)
                M600 (Arg0, 0x33, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) >= B606)
                M600 (Arg0, 0x34, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) >= B606)
                M600 (Arg0, 0x35, Local0, Zero)
            }

            /* LLess */

            Local0 = (0x0321 < B606)
            M600 (Arg0, 0x36, Local0, Zero)
            Local0 = (0x0322 < B606)
            M600 (Arg0, 0x37, Local0, Zero)
            Local0 = (0x0320 < B606)
            M600 (Arg0, 0x38, Local0, Ones)
            Local0 = (AUI1 < B606)
            M600 (Arg0, 0x39, Local0, Zero)
            Local0 = (AUIG < B606)
            M600 (Arg0, 0x3A, Local0, Zero)
            Local0 = (AUIH < B606)
            M600 (Arg0, 0x3B, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) < B606)
                M600 (Arg0, 0x3C, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIG)) < B606)
                M600 (Arg0, 0x3D, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIH)) < B606)
                M600 (Arg0, 0x3E, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x01]) < B606)
            M600 (Arg0, 0x3F, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x10]) < B606)
            M600 (Arg0, 0x40, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x11]) < B606)
            M600 (Arg0, 0x41, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) < B606)
            M600 (Arg0, 0x42, Local0, Zero)
            Local0 = (M601 (0x01, 0x10) < B606)
            M600 (Arg0, 0x43, Local0, Zero)
            Local0 = (M601 (0x01, 0x11) < B606)
            M600 (Arg0, 0x44, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) < B606)
                M600 (Arg0, 0x45, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) < B606)
                M600 (Arg0, 0x46, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) < B606)
                M600 (Arg0, 0x47, Local0, Ones)
            }

            /* LLessEqual */

            Local0 = (0x0321 <= B606)
            M600 (Arg0, 0x48, Local0, Ones)
            Local0 = (0x0322 <= B606)
            M600 (Arg0, 0x49, Local0, Zero)
            Local0 = (0x0320 <= B606)
            M600 (Arg0, 0x4A, Local0, Ones)
            Local0 = (AUI1 <= B606)
            M600 (Arg0, 0x4B, Local0, Ones)
            Local0 = (AUIG <= B606)
            M600 (Arg0, 0x4C, Local0, Zero)
            Local0 = (AUIH <= B606)
            M600 (Arg0, 0x4D, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) <= B606)
                M600 (Arg0, 0x4E, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIG)) <= B606)
                M600 (Arg0, 0x4F, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIH)) <= B606)
                M600 (Arg0, 0x50, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x01]) <= B606)
            M600 (Arg0, 0x51, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x10]) <= B606)
            M600 (Arg0, 0x52, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x11]) <= B606)
            M600 (Arg0, 0x53, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) <= B606)
            M600 (Arg0, 0x54, Local0, Ones)
            Local0 = (M601 (0x01, 0x10) <= B606)
            M600 (Arg0, 0x55, Local0, Zero)
            Local0 = (M601 (0x01, 0x11) <= B606)
            M600 (Arg0, 0x56, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) <= B606)
                M600 (Arg0, 0x57, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) <= B606)
                M600 (Arg0, 0x58, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) <= B606)
                M600 (Arg0, 0x59, Local0, Ones)
            }

            /* LNotEqual */

            Local0 = (0x0321 != B606)
            M600 (Arg0, 0x5A, Local0, Zero)
            Local0 = (0x0322 != B606)
            M600 (Arg0, 0x5B, Local0, Ones)
            Local0 = (0x0320 != B606)
            M600 (Arg0, 0x5C, Local0, Ones)
            Local0 = (AUI1 != B606)
            M600 (Arg0, 0x5D, Local0, Zero)
            Local0 = (AUIG != B606)
            M600 (Arg0, 0x5E, Local0, Ones)
            Local0 = (AUIH != B606)
            M600 (Arg0, 0x5F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUI1)) != B606)
                M600 (Arg0, 0x60, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUIG)) != B606)
                M600 (Arg0, 0x61, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUIH)) != B606)
                M600 (Arg0, 0x62, Local0, Ones)
            }

            Local0 = (DerefOf (PAUI [0x01]) != B606)
            M600 (Arg0, 0x63, Local0, Zero)
            Local0 = (DerefOf (PAUI [0x10]) != B606)
            M600 (Arg0, 0x64, Local0, Ones)
            Local0 = (DerefOf (PAUI [0x11]) != B606)
            M600 (Arg0, 0x65, Local0, Ones)
            /* Method returns Integer */

            Local0 = (M601 (0x01, 0x01) != B606)
            M600 (Arg0, 0x66, Local0, Zero)
            Local0 = (M601 (0x01, 0x10) != B606)
            M600 (Arg0, 0x67, Local0, Ones)
            Local0 = (M601 (0x01, 0x11) != B606)
            M600 (Arg0, 0x68, Local0, Ones)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x01, 0x01, 0x01)) != B606)
                M600 (Arg0, 0x69, Local0, Zero)
                Local0 = (DerefOf (M602 (0x01, 0x10, 0x01)) != B606)
                M600 (Arg0, 0x6A, Local0, Ones)
                Local0 = (DerefOf (M602 (0x01, 0x11, 0x01)) != B606)
                M600 (Arg0, 0x6B, Local0, Ones)
            }
        }

        /* Buffer to Integer intermediate conversion of the Buffer second */
        /* operand of Concatenate operator in case the first one is Integer */
        Method (M64Q, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            Local0 = Concatenate (0x0321, B606)
            M600 (Arg0, 0x00, Local0, BB26)
            Local0 = Concatenate (0x0321, B60A)
            M600 (Arg0, 0x01, Local0, BB21)
            Local0 = Concatenate (AUI1, B606)
            M600 (Arg0, 0x02, Local0, BB26)
            Local0 = Concatenate (AUI1, B60A)
            M600 (Arg0, 0x03, Local0, BB21)
            If (Y078)
            {
                Local0 = Concatenate (DerefOf (RefOf (AUI1)), B606)
                M600 (Arg0, 0x04, Local0, BB26)
                Local0 = Concatenate (DerefOf (RefOf (AUI1)), B60A)
                M600 (Arg0, 0x05, Local0, BB21)
            }

            Local0 = Concatenate (DerefOf (PAUI [0x01]), B606)
            M600 (Arg0, 0x06, Local0, BB26)
            Local0 = Concatenate (DerefOf (PAUI [0x01]), B60A)
            M600 (Arg0, 0x07, Local0, BB21)
            /* Method returns Integer */

            Local0 = Concatenate (M601 (0x01, 0x01), B606)
            M600 (Arg0, 0x08, Local0, BB26)
            Local0 = Concatenate (M601 (0x01, 0x01), B60A)
            M600 (Arg0, 0x09, Local0, BB21)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), B606)
                M600 (Arg0, 0x0A, Local0, BB26)
                Local0 = Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), B60A)
                M600 (Arg0, 0x0B, Local0, BB21)
            }

            Concatenate (0x0321, B606, Local0)
            M600 (Arg0, 0x0C, Local0, BB26)
            Concatenate (0x0321, B60A, Local0)
            M600 (Arg0, 0x0D, Local0, BB21)
            Concatenate (AUI1, B606, Local0)
            M600 (Arg0, 0x0E, Local0, BB26)
            Concatenate (AUI1, B60A, Local0)
            M600 (Arg0, 0x0F, Local0, BB21)
            If (Y078)
            {
                Concatenate (DerefOf (RefOf (AUI1)), B606, Local0)
                M600 (Arg0, 0x10, Local0, BB26)
                Concatenate (DerefOf (RefOf (AUI1)), B60A, Local0)
                M600 (Arg0, 0x11, Local0, BB21)
            }

            Concatenate (DerefOf (PAUI [0x01]), B606, Local0)
            M600 (Arg0, 0x12, Local0, BB26)
            Concatenate (DerefOf (PAUI [0x01]), B60A, Local0)
            M600 (Arg0, 0x13, Local0, BB21)
            /* Method returns Integer */

            Concatenate (M601 (0x01, 0x01), B606, Local0)
            M600 (Arg0, 0x14, Local0, BB26)
            Concatenate (M601 (0x01, 0x01), B60A, Local0)
            M600 (Arg0, 0x15, Local0, BB21)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), B606, Local0)
                M600 (Arg0, 0x16, Local0, BB26)
                Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), B60A, Local0)
                M600 (Arg0, 0x17, Local0, BB21)
            }
        }

        Method (M32Q, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            Local0 = Concatenate (0x0321, B606)
            M600 (Arg0, 0x00, Local0, BB27)
            Local0 = Concatenate (0x0321, B60A)
            M600 (Arg0, 0x01, Local0, BB28)
            Local0 = Concatenate (AUI1, B606)
            M600 (Arg0, 0x02, Local0, BB27)
            Local0 = Concatenate (AUI1, B60A)
            M600 (Arg0, 0x03, Local0, BB28)
            If (Y078)
            {
                Local0 = Concatenate (DerefOf (RefOf (AUI1)), B606)
                M600 (Arg0, 0x04, Local0, BB27)
                Local0 = Concatenate (DerefOf (RefOf (AUI1)), B60A)
                M600 (Arg0, 0x05, Local0, BB28)
            }

            Local0 = Concatenate (DerefOf (PAUI [0x01]), B606)
            M600 (Arg0, 0x06, Local0, BB27)
            Local0 = Concatenate (DerefOf (PAUI [0x01]), B60A)
            M600 (Arg0, 0x07, Local0, BB28)
            /* Method returns Integer */

            Local0 = Concatenate (M601 (0x01, 0x01), B606)
            M600 (Arg0, 0x08, Local0, BB27)
            Local0 = Concatenate (M601 (0x01, 0x01), B60A)
            M600 (Arg0, 0x09, Local0, BB28)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Local0 = Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), B606)
                M600 (Arg0, 0x0A, Local0, BB27)
                Local0 = Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), B60A)
                M600 (Arg0, 0x0B, Local0, BB28)
            }

            Concatenate (0x0321, B606, Local0)
            M600 (Arg0, 0x0C, Local0, BB27)
            Concatenate (0x0321, B60A, Local0)
            M600 (Arg0, 0x0D, Local0, BB28)
            Concatenate (AUI1, B606, Local0)
            M600 (Arg0, 0x0E, Local0, BB27)
            Concatenate (AUI1, B60A, Local0)
            M600 (Arg0, 0x0F, Local0, BB28)
            If (Y078)
            {
                Concatenate (DerefOf (RefOf (AUI1)), B606, Local0)
                M600 (Arg0, 0x10, Local0, BB27)
                Concatenate (DerefOf (RefOf (AUI1)), B60A, Local0)
                M600 (Arg0, 0x11, Local0, BB28)
            }

            Concatenate (DerefOf (PAUI [0x01]), B606, Local0)
            M600 (Arg0, 0x12, Local0, BB27)
            Concatenate (DerefOf (PAUI [0x01]), B60A, Local0)
            M600 (Arg0, 0x14, Local0, BB28)
            /* Method returns Integer */

            Concatenate (M601 (0x01, 0x01), B606, Local0)
            M600 (Arg0, 0x15, Local0, BB27)
            Concatenate (M601 (0x01, 0x01), B60A, Local0)
            M600 (Arg0, 0x16, Local0, BB28)
            /* Method returns Reference to Integer */

            If (Y500)
            {
                Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), B606, Local0)
                M600 (Arg0, 0x17, Local0, BB27)
                Concatenate (DerefOf (M602 (0x01, 0x01, 0x01)), B60A, Local0)
                M600 (Arg0, 0x18, Local0, BB28)
            }
        }

        /* Buffer to Integer conversion of the Buffer Length (second) */
        /* operand of the ToString operator */
        /* Common 32-bit/64-bit test */
        Method (M066, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60E, Buffer (0x01)
            {
                 0x0B                                             // .
            })
            Local0 = ToString (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, B60E)
            M600 (Arg0, 0x00, Local0, BS1B)
            Local0 = ToString (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, B606)
            M600 (Arg0, 0x01, Local0, BS1C)
            Local0 = ToString (AUB6, B60E)
            M600 (Arg0, 0x02, Local0, BS1B)
            Local0 = ToString (AUB6, B606)
            M600 (Arg0, 0x03, Local0, BS1C)
            If (Y078)
            {
                Local0 = ToString (DerefOf (RefOf (AUB6)), B60E)
                M600 (Arg0, 0x04, Local0, BS1B)
                Local0 = ToString (DerefOf (RefOf (AUB6)), B606)
                M600 (Arg0, 0x05, Local0, BS1C)
            }

            Local0 = ToString (DerefOf (PAUB [0x06]), B60E)
            M600 (Arg0, 0x06, Local0, BS1B)
            Local0 = ToString (DerefOf (PAUB [0x06]), B606)
            M600 (Arg0, 0x07, Local0, BS1C)
            /* Method returns Buffer */

            Local0 = ToString (M601 (0x03, 0x06), B60E)
            M600 (Arg0, 0x08, Local0, BS1B)
            Local0 = ToString (M601 (0x03, 0x06), B606)
            M600 (Arg0, 0x09, Local0, BS1C)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = ToString (DerefOf (M602 (0x03, 0x06, 0x01)), B60E)
                M600 (Arg0, 0x0A, Local0, BS1B)
                Local0 = ToString (DerefOf (M602 (0x03, 0x06, 0x01)), B606)
                M600 (Arg0, 0x0B, Local0, BS1C)
            }

            ToString (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, B60E, Local0)
            M600 (Arg0, 0x0C, Local0, BS1B)
            ToString (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, B606, Local0)
            M600 (Arg0, 0x0D, Local0, BS1C)
            ToString (AUB6, B60E, Local0)
            M600 (Arg0, 0x0E, Local0, BS1B)
            ToString (AUB6, B606, Local0)
            M600 (Arg0, 0x0F, Local0, BS1C)
            If (Y078)
            {
                ToString (DerefOf (RefOf (AUB6)), B60E, Local0)
                M600 (Arg0, 0x10, Local0, BS1B)
                ToString (DerefOf (RefOf (AUB6)), B606, Local0)
                M600 (Arg0, 0x11, Local0, BS1C)
            }

            ToString (DerefOf (PAUB [0x06]), B60E, Local0)
            M600 (Arg0, 0x12, Local0, BS1B)
            ToString (DerefOf (PAUB [0x06]), B606, Local0)
            M600 (Arg0, 0x13, Local0, BS1C)
            /* Method returns Buffer */

            ToString (M601 (0x03, 0x06), B60E, Local0)
            M600 (Arg0, 0x14, Local0, BS1B)
            ToString (M601 (0x03, 0x06), B606, Local0)
            M600 (Arg0, 0x15, Local0, BS1C)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                ToString (DerefOf (M602 (0x03, 0x06, 0x01)), B60E, Local0)
                M600 (Arg0, 0x16, Local0, BS1B)
                ToString (DerefOf (M602 (0x03, 0x06, 0x01)), B606, Local0)
                M600 (Arg0, 0x17, Local0, BS1C)
            }
        }

        Method (M64R, 1, Serialized)
        {
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            Local0 = ToString (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, B60A)
            M600 (Arg0, 0x00, Local0, BS1C)
            Local0 = ToString (AUB6, B60A)
            M600 (Arg0, 0x01, Local0, BS1C)
            If (Y078)
            {
                Local0 = ToString (DerefOf (RefOf (AUB6)), B60A)
                M600 (Arg0, 0x02, Local0, BS1C)
            }

            Local0 = ToString (DerefOf (PAUB [0x06]), B60A)
            M600 (Arg0, 0x03, Local0, BS1C)
            /* Method returns Buffer */

            Local0 = ToString (M601 (0x03, 0x06), B60A)
            M600 (Arg0, 0x04, Local0, BS1C)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = ToString (DerefOf (M602 (0x03, 0x06, 0x01)), B60A)
                M600 (Arg0, 0x05, Local0, BS1C)
            }

            ToString (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, B60A, Local0)
            M600 (Arg0, 0x06, Local0, BS1C)
            ToString (AUB6, B60A, Local0)
            M600 (Arg0, 0x07, Local0, BS1C)
            If (Y078)
            {
                ToString (DerefOf (RefOf (AUB6)), B60A, Local0)
                M600 (Arg0, 0x08, Local0, BS1C)
            }

            ToString (DerefOf (PAUB [0x06]), B60A, Local0)
            M600 (Arg0, 0x09, Local0, BS1C)
            /* Method returns Buffer */

            ToString (M601 (0x03, 0x06), B60A, Local0)
            M600 (Arg0, 0x0A, Local0, BS1C)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                ToString (DerefOf (M602 (0x03, 0x06, 0x01)), B60A, Local0)
                M600 (Arg0, 0x0B, Local0, BS1C)
            }
        }

        Method (M32R, 1, Serialized)
        {
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            Local0 = ToString (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, B60A)
            M600 (Arg0, 0x00, Local0, BS1C)
            Local0 = ToString (AUB6, B60A)
            M600 (Arg0, 0x01, Local0, BS1C)
            If (Y078)
            {
                Local0 = ToString (DerefOf (RefOf (AUB6)), B60A)
                M600 (Arg0, 0x02, Local0, BS1C)
            }

            Local0 = ToString (DerefOf (PAUB [0x06]), B60A)
            M600 (Arg0, 0x03, Local0, BS1C)
            /* Method returns Buffer */

            Local0 = ToString (M601 (0x03, 0x06), B60A)
            M600 (Arg0, 0x04, Local0, BS1C)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                Local0 = ToString (DerefOf (M602 (0x03, 0x06, 0x01)), B60A)
                M600 (Arg0, 0x05, Local0, BS1C)
            }

            ToString (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, B60A, Local0)
            M600 (Arg0, 0x06, Local0, BS1C)
            ToString (AUB6, B60A, Local0)
            M600 (Arg0, 0x07, Local0, BS1C)
            If (Y078)
            {
                ToString (DerefOf (RefOf (AUB6)), B60A, Local0)
                M600 (Arg0, 0x08, Local0, BS1C)
            }

            ToString (DerefOf (PAUB [0x06]), B60A, Local0)
            M600 (Arg0, 0x09, Local0, BS1C)
            /* Method returns Buffer */

            ToString (M601 (0x03, 0x06), B60A, Local0)
            M600 (Arg0, 0x0A, Local0, BS1C)
            /* Method returns Reference to Buffer */

            If (Y500)
            {
                ToString (DerefOf (M602 (0x03, 0x06, 0x01)), B60A, Local0)
                M600 (Arg0, 0x0B, Local0, BS1C)
            }
        }

        /* Buffer to Integer conversion of the Buffer Index (second) */
        /* operand of the Index operator */
        Method (M067, 1, Serialized)
        {
            Name (B60E, Buffer (0x01)
            {
                 0x0B                                             // .
            })
            Store (AUS6 [B60E], Local0)
            M600 (Arg0, 0x00, DerefOf (Local0), BI10)
            Store (AUB6 [B60E], Local0)
            M600 (Arg0, 0x01, DerefOf (Local0), BI10)
            Store (AUP0 [B60E], Local0)
            M600 (Arg0, 0x02, DerefOf (Local0), BI11)
            If (Y078)
            {
                Store (DerefOf (RefOf (AUS6)) [B60E], Local0)
                M600 (Arg0, 0x03, DerefOf (Local0), BI10)
                Store (DerefOf (RefOf (AUB6)) [B60E], Local0)
                M600 (Arg0, 0x04, DerefOf (Local0), BI10)
                Store (DerefOf (RefOf (AUP0)) [B60E], Local0)
                M600 (Arg0, 0x05, DerefOf (Local0), BI11)
            }

            Store (DerefOf (PAUS [0x06]) [B60E], Local0)
            M600 (Arg0, 0x06, DerefOf (Local0), BI10)
            Store (DerefOf (PAUB [0x06]) [B60E], Local0)
            M600 (Arg0, 0x07, DerefOf (Local0), BI10)
            Store (DerefOf (PAUP [0x00]) [B60E], Local0)
            M600 (Arg0, 0x08, DerefOf (Local0), BI11)
            /* Method returns Object */

            If (Y900)
            {
                Store (M601 (0x02, 0x06) [B60E], Local0)
                M600 (Arg0, 0x09, DerefOf (Local0), BI10)
                Store (M601 (0x03, 0x06) [B60E], Local0)
                M600 (Arg0, 0x0A, DerefOf (Local0), BI10)
                Store (M601 (0x04, 0x00) [B60E], Local0)
                M600 (Arg0, 0x0B, DerefOf (Local0), BI11)
            }
            Else
            {
                CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
                Store (M601 (0x02, 0x06) [B60E], Local3)
                CH04 (Arg0, 0x00, 0x55, Z088, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
                Store (M601 (0x03, 0x06) [B60E], Local3)
                CH04 (Arg0, 0x00, 0x55, Z088, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
                Store (M601 (0x04, 0x00) [B60E], Local3)
                CH04 (Arg0, 0x00, 0x55, Z088, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
            }

            /* Method returns Reference */

            If (Y500)
            {
                Store (DerefOf (M602 (0x02, 0x06, 0x01)) [B60E], Local0)
                M600 (Arg0, 0x0C, DerefOf (Local0), BI10)
                Store (DerefOf (M602 (0x03, 0x06, 0x01)) [B60E], Local0)
                M600 (Arg0, 0x0D, DerefOf (Local0), BI10)
                Store (DerefOf (M602 (0x04, 0x00, 0x01)) [B60E], Local0)
                M600 (Arg0, 0x0E, DerefOf (Local0), BI11)
            }

            Local0 = AUS6 [B60E] /* \M613.M067.B60E */
            M600 (Arg0, 0x0F, DerefOf (Local0), BI10)
            Local0 = AUB6 [B60E] /* \M613.M067.B60E */
            M600 (Arg0, 0x10, DerefOf (Local0), BI10)
            Local0 = AUP0 [B60E] /* \M613.M067.B60E */
            M600 (Arg0, 0x11, DerefOf (Local0), BI11)
            If (Y078)
            {
                Local0 = DerefOf (RefOf (AUS6)) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x12, DerefOf (Local0), BI10)
                Local0 = DerefOf (RefOf (AUB6)) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x13, DerefOf (Local0), BI10)
                Local0 = DerefOf (RefOf (AUP0)) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x14, DerefOf (Local0), BI11)
            }

            Local0 = DerefOf (PAUS [0x06]) [B60E] /* \M613.M067.B60E */
            M600 (Arg0, 0x15, DerefOf (Local0), BI10)
            Local0 = DerefOf (PAUB [0x06]) [B60E] /* \M613.M067.B60E */
            M600 (Arg0, 0x16, DerefOf (Local0), BI10)
            Local0 = DerefOf (PAUP [0x00]) [B60E] /* \M613.M067.B60E */
            M600 (Arg0, 0x17, DerefOf (Local0), BI11)
            /* Method returns Object */

            If (Y900)
            {
                Local0 = M601 (0x02, 0x06) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x18, DerefOf (Local0), BI10)
                Local0 = M601 (0x03, 0x06) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x19, DerefOf (Local0), BI10)
                Local0 = M601 (0x04, 0x00) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x1A, DerefOf (Local0), BI11)
            }
            Else
            {
                CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
                Local0 = M601 (0x02, 0x06) [B60E] /* \M613.M067.B60E */
                CH04 (Arg0, 0x00, 0x55, Z088, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
                Local0 = M601 (0x03, 0x06) [B60E] /* \M613.M067.B60E */
                CH04 (Arg0, 0x00, 0x55, Z088, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
                Local0 = M601 (0x04, 0x00) [B60E] /* \M613.M067.B60E */
                CH04 (Arg0, 0x00, 0x55, Z088, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
            }

            /* Method returns Reference */

            If (Y500)
            {
                Local0 = DerefOf (M602 (0x02, 0x06, 0x01)) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x1B, DerefOf (Local0), BI10)
                Local0 = DerefOf (M602 (0x03, 0x06, 0x01)) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x1C, DerefOf (Local0), BI10)
                Local0 = DerefOf (M602 (0x04, 0x00, 0x01)) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x1D, DerefOf (Local0), BI11)
            }

            If (Y098)
            {
                Local0 = Local1 = AUS6 [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x1E, DerefOf (Local0), BI10)
                Local0 = Local1 = AUB6 [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x1F, DerefOf (Local0), BI10)
                Local0 = Local1 = AUP0 [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x20, DerefOf (Local0), BI11)
            }

            If (Y078)
            {
                Local0 = Local1 = DerefOf (RefOf (AUS6)) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x21, DerefOf (Local0), BI10)
                Local0 = Local1 = DerefOf (RefOf (AUB6)) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x22, DerefOf (Local0), BI10)
                Local0 = Local1 = DerefOf (RefOf (AUP0)) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x23, DerefOf (Local0), BI11)
            }

            If (Y098)
            {
                Local0 = Local1 = DerefOf (PAUS [0x06]) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x24, DerefOf (Local0), BI10)
                Local0 = Local1 = DerefOf (PAUB [0x06]) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x25, DerefOf (Local0), BI10)
                Local0 = Local1 = DerefOf (PAUP [0x00]) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x26, DerefOf (Local0), BI11)
            }

            /* Method returns Object */

            If ((Y900 && Y098))
            {
                Local0 = Local1 = M601 (0x02, 0x06) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x27, DerefOf (Local0), BI10)
                Local0 = Local1 = M601 (0x03, 0x06) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x28, DerefOf (Local0), BI10)
                Local0 = Local1 = M601 (0x04, 0x00) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x29, DerefOf (Local0), BI11)
            }

            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Local1 = DerefOf (M602 (0x02, 0x06, 0x01)) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x2A, DerefOf (Local0), BI10)
                Local0 = Local1 = DerefOf (M602 (0x03, 0x06, 0x01)) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x2B, DerefOf (Local0), BI10)
                Local0 = Local1 = DerefOf (M602 (0x04, 0x00, 0x01)) [B60E] /* \M613.M067.B60E */
                M600 (Arg0, 0x2C, DerefOf (Local0), BI11)
            }
        }

        /* Buffer to Integer conversion of the String Arg (third) */
        /* operand of the Fatal operator */
        /* (it can only be checked an exception does not occur) */
        Method (M068, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
            Fatal (0xFF, 0xFFFFFFFF, B606)
            If (F64)
            {
                Fatal (0xFF, 0xFFFFFFFF, B60A)
            }
            Else
            {
                Fatal (0xFF, 0xFFFFFFFF, B60A)
            }

            CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
        }

        /* Buffer to Integer conversion of the Buffer Index and Length */
        /* operands of the Mid operator */
        /* Common 32-bit/64-bit test */
        Method (M069, 1, Serialized)
        {
            Name (B60E, Buffer (0x01)
            {
                 0x0B                                             // .
            })
            /* String to Integer conversion of the String Index operand */

            Local0 = Mid ("This is auxiliary String", B60E, 0x0A)
            M600 (Arg0, 0x00, Local0, BS1D)
            Local0 = Mid (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, B60E, 0x0A)
            M600 (Arg0, 0x01, Local0, BB32)
            Local0 = Mid (AUS6, B60E, 0x0A)
            M600 (Arg0, 0x02, Local0, BS1D)
            Local0 = Mid (AUB6, B60E, 0x0A)
            M600 (Arg0, 0x03, Local0, BB32)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (AUS6)), B60E, 0x0A)
                M600 (Arg0, 0x04, Local0, BS1D)
                Local0 = Mid (DerefOf (RefOf (AUB6)), B60E, 0x0A)
                M600 (Arg0, 0x05, Local0, BB32)
            }

            Local0 = Mid (DerefOf (PAUS [0x06]), B60E, 0x0A)
            M600 (Arg0, 0x06, Local0, BS1D)
            Local0 = Mid (DerefOf (PAUB [0x06]), B60E, 0x0A)
            M600 (Arg0, 0x07, Local0, BB32)
            /* Method returns Object */

            Local0 = Mid (M601 (0x02, 0x06), B60E, 0x0A)
            M600 (Arg0, 0x08, Local0, BS1D)
            Local0 = Mid (M601 (0x03, 0x06), B60E, 0x0A)
            M600 (Arg0, 0x09, Local0, BB32)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Mid (DerefOf (M602 (0x02, 0x06, 0x01)), B60E, 0x0A)
                M600 (Arg0, 0x0A, Local0, BS1D)
                Local0 = Mid (DerefOf (M602 (0x03, 0x06, 0x01)), B60E, 0x0A)
                M600 (Arg0, 0x0B, Local0, BB32)
            }

            Mid ("This is auxiliary String", B60E, 0x0A, Local0)
            M600 (Arg0, 0x0C, Local0, BS1D)
            Mid (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, B60E, 0x0A, Local0)
            M600 (Arg0, 0x0D, Local0, BB32)
            Mid (AUS6, B60E, 0x0A, Local0)
            M600 (Arg0, 0x0E, Local0, BS1D)
            Mid (AUB6, B60E, 0x0A, Local0)
            M600 (Arg0, 0x0F, Local0, BB32)
            If (Y078)
            {
                Mid (DerefOf (RefOf (AUS6)), B60E, 0x0A, Local0)
                M600 (Arg0, 0x10, Local0, BS1D)
                Mid (DerefOf (RefOf (AUB6)), B60E, 0x0A, Local0)
                M600 (Arg0, 0x11, Local0, BB32)
            }

            Mid (DerefOf (PAUS [0x06]), B60E, 0x0A, Local0)
            M600 (Arg0, 0x12, Local0, BS1D)
            Mid (DerefOf (PAUB [0x06]), B60E, 0x0A, Local0)
            M600 (Arg0, 0x13, Local0, BB32)
            /* Method returns Object */

            Mid (M601 (0x02, 0x06), B60E, 0x0A, Local0)
            M600 (Arg0, 0x14, Local0, BS1D)
            Mid (M601 (0x03, 0x06), B60E, 0x0A, Local0)
            M600 (Arg0, 0x15, Local0, BB32)
            /* Method returns Reference */

            If (Y500)
            {
                Mid (DerefOf (M602 (0x02, 0x06, 0x01)), B60E, 0x0A, Local0)
                M600 (Arg0, 0x16, Local0, BS1D)
                Mid (DerefOf (M602 (0x03, 0x06, 0x01)), B60E, 0x0A, Local0)
                M600 (Arg0, 0x17, Local0, BB32)
            }

            /* String to Integer conversion of the String Length operand */

            Local0 = Mid ("This is auxiliary String", 0x00, B60E)
            M600 (Arg0, 0x18, Local0, BS1B)
            Local0 = Mid (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, 0x00, B60E)
            M600 (Arg0, 0x19, Local0, BB33)
            Local0 = Mid (AUS6, 0x00, B60E)
            M600 (Arg0, 0x1A, Local0, BS1B)
            Local0 = Mid (AUB6, 0x00, B60E)
            M600 (Arg0, 0x1B, Local0, BB33)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (AUS6)), 0x00, B60E)
                M600 (Arg0, 0x1C, Local0, BS1B)
                Local0 = Mid (DerefOf (RefOf (AUB6)), 0x00, B60E)
                M600 (Arg0, 0x1D, Local0, BB33)
            }

            Local0 = Mid (DerefOf (PAUS [0x06]), 0x00, B60E)
            M600 (Arg0, 0x1E, Local0, BS1B)
            Local0 = Mid (DerefOf (PAUB [0x06]), 0x00, B60E)
            M600 (Arg0, 0x1F, Local0, BB33)
            /* Method returns Object */

            Local0 = Mid (M601 (0x02, 0x06), 0x00, B60E)
            M600 (Arg0, 0x20, Local0, BS1B)
            Local0 = Mid (M601 (0x03, 0x06), 0x00, B60E)
            M600 (Arg0, 0x21, Local0, BB33)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Mid (DerefOf (M602 (0x02, 0x06, 0x01)), 0x00, B60E)
                M600 (Arg0, 0x22, Local0, BS1B)
                Local0 = Mid (DerefOf (M602 (0x03, 0x06, 0x01)), 0x00, B60E)
                M600 (Arg0, 0x23, Local0, BB33)
            }

            Mid ("This is auxiliary String", 0x00, B60E, Local0)
            M600 (Arg0, 0x24, Local0, BS1B)
            Mid (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, 0x00, B60E, Local0)
            M600 (Arg0, 0x25, Local0, BB33)
            Mid (AUS6, 0x00, B60E, Local0)
            M600 (Arg0, 0x25, Local0, BS1B)
            Mid (AUB6, 0x00, B60E, Local0)
            M600 (Arg0, 0x27, Local0, BB33)
            If (Y078)
            {
                Mid (DerefOf (RefOf (AUS6)), 0x00, B60E, Local0)
                M600 (Arg0, 0x28, Local0, BS1B)
                Mid (DerefOf (RefOf (AUB6)), 0x00, B60E, Local0)
                M600 (Arg0, 0x29, Local0, BB33)
            }

            Mid (DerefOf (PAUS [0x06]), 0x00, B60E, Local0)
            M600 (Arg0, 0x2A, Local0, BS1B)
            Mid (DerefOf (PAUB [0x06]), 0x00, B60E, Local0)
            M600 (Arg0, 0x2B, Local0, BB33)
            /* Method returns Object */

            Mid (M601 (0x02, 0x06), 0x00, B60E, Local0)
            M600 (Arg0, 0x2C, Local0, BS1B)
            Mid (M601 (0x03, 0x06), 0x00, B60E, Local0)
            M600 (Arg0, 0x2D, Local0, BB33)
            /* Method returns Reference */

            If (Y500)
            {
                Mid (DerefOf (M602 (0x02, 0x06, 0x01)), 0x00, B60E, Local0)
                M600 (Arg0, 0x2E, Local0, BS1B)
                Mid (DerefOf (M602 (0x03, 0x06, 0x01)), 0x00, B60E, Local0)
                M600 (Arg0, 0x2F, Local0, BB33)
            }
        }

        Method (M64S, 1, Serialized)
        {
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            Name (B60E, Buffer (0x01)
            {
                 0x0B                                             // .
            })
            /* String to Integer conversion of the String Length operand */

            Local0 = Mid ("This is auxiliary String", 0x00, B60A)
            M600 (Arg0, 0x00, Local0, BS1E)
            Local0 = Mid (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, 0x00, B60A)
            M600 (Arg0, 0x01, Local0, BB34)
            Local0 = Mid (AUS6, 0x00, B60A)
            M600 (Arg0, 0x02, Local0, BS1E)
            Local0 = Mid (AUB6, 0x00, B60A)
            M600 (Arg0, 0x03, Local0, BB34)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (AUS6)), 0x00, B60A)
                M600 (Arg0, 0x04, Local0, BS1E)
                Local0 = Mid (DerefOf (RefOf (AUB6)), 0x00, B60A)
                M600 (Arg0, 0x05, Local0, BB34)
            }

            Local0 = Mid (DerefOf (PAUS [0x06]), 0x00, B60A)
            M600 (Arg0, 0x06, Local0, BS1E)
            Local0 = Mid (DerefOf (PAUB [0x06]), 0x00, B60A)
            M600 (Arg0, 0x07, Local0, BB34)
            /* Method returns Object */

            Local0 = Mid (M601 (0x02, 0x06), 0x00, B60A)
            M600 (Arg0, 0x08, Local0, BS1E)
            Local0 = Mid (M601 (0x03, 0x06), 0x00, B60A)
            M600 (Arg0, 0x09, Local0, BB34)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Mid (DerefOf (M602 (0x02, 0x06, 0x01)), 0x00, B60A)
                M600 (Arg0, 0x0A, Local0, BS1E)
                Local0 = Mid (DerefOf (M602 (0x03, 0x06, 0x01)), 0x00, B60A)
                M600 (Arg0, 0x0B, Local0, BB34)
            }

            Mid ("This is auxiliary String", 0x00, B60A, Local0)
            M600 (Arg0, 0x0C, Local0, BS1E)
            Mid (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, 0x00, B60A, Local0)
            M600 (Arg0, 0x0D, Local0, BB34)
            Mid (AUS6, 0x00, B60A, Local0)
            M600 (Arg0, 0x0E, Local0, BS1E)
            Mid (AUB6, 0x00, B60A, Local0)
            M600 (Arg0, 0x0F, Local0, BB34)
            If (Y078)
            {
                Mid (DerefOf (RefOf (AUS6)), 0x00, B60A, Local0)
                M600 (Arg0, 0x10, Local0, BS1E)
                Mid (DerefOf (RefOf (AUB6)), 0x00, B60A, Local0)
                M600 (Arg0, 0x11, Local0, BB34)
            }

            Mid (DerefOf (PAUS [0x06]), 0x00, B60A, Local0)
            M600 (Arg0, 0x12, Local0, BS1E)
            Mid (DerefOf (PAUB [0x06]), 0x00, B60A, Local0)
            M600 (Arg0, 0x13, Local0, BB34)
            /* Method returns Object */

            Mid (M601 (0x02, 0x06), 0x00, B60A, Local0)
            M600 (Arg0, 0x14, Local0, BS1E)
            Mid (M601 (0x03, 0x06), 0x00, B60A, Local0)
            M600 (Arg0, 0x15, Local0, BB34)
            /* Method returns Reference */

            If (Y500)
            {
                Mid (DerefOf (M602 (0x02, 0x06, 0x01)), 0x00, B60A, Local0)
                M600 (Arg0, 0x16, Local0, BS1E)
                Mid (DerefOf (M602 (0x03, 0x06, 0x01)), 0x00, B60A, Local0)
                M600 (Arg0, 0x17, Local0, BB34)
            }

            /* String to Integer conversion of the both String operands */

            Local0 = Mid ("This is auxiliary String", B60E, B60A)
            M600 (Arg0, 0x18, Local0, BS1F)
            Local0 = Mid (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, B60E, B60A)
            M600 (Arg0, 0x19, Local0, BB35)
            Local0 = Mid (AUS6, B60E, B60A)
            M600 (Arg0, 0x1A, Local0, BS1F)
            Local0 = Mid (AUB6, B60E, B60A)
            M600 (Arg0, 0x1B, Local0, BB35)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (AUS6)), B60E, B60A)
                M600 (Arg0, 0x1C, Local0, BS1F)
                Local0 = Mid (DerefOf (RefOf (AUB6)), B60E, B60A)
                M600 (Arg0, 0x1D, Local0, BB35)
            }

            Local0 = Mid (DerefOf (PAUS [0x06]), B60E, B60A)
            M600 (Arg0, 0x1E, Local0, BS1F)
            Local0 = Mid (DerefOf (PAUB [0x06]), B60E, B60A)
            M600 (Arg0, 0x1F, Local0, BB35)
            /* Method returns Object */

            Local0 = Mid (M601 (0x02, 0x06), B60E, B60A)
            M600 (Arg0, 0x20, Local0, BS1F)
            Local0 = Mid (M601 (0x03, 0x06), B60E, B60A)
            M600 (Arg0, 0x21, Local0, BB35)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Mid (DerefOf (M602 (0x02, 0x06, 0x01)), B60E, B60A)
                M600 (Arg0, 0x22, Local0, BS1F)
                Local0 = Mid (DerefOf (M602 (0x03, 0x06, 0x01)), B60E, B60A)
                M600 (Arg0, 0x23, Local0, BB35)
            }

            Mid ("This is auxiliary String", B60E, B60A, Local0)
            M600 (Arg0, 0x24, Local0, BS1F)
            Mid (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, B60E, B60A, Local0)
            M600 (Arg0, 0x25, Local0, BB35)
            Mid (AUS6, B60E, B60A, Local0)
            M600 (Arg0, 0x26, Local0, BS1F)
            Mid (AUB6, B60E, B60A, Local0)
            M600 (Arg0, 0x27, Local0, BB35)
            If (Y078)
            {
                Mid (DerefOf (RefOf (AUS6)), B60E, B60A, Local0)
                M600 (Arg0, 0x28, Local0, BS1F)
                Mid (DerefOf (RefOf (AUB6)), B60E, B60A, Local0)
                M600 (Arg0, 0x29, Local0, BB35)
            }

            Mid (DerefOf (PAUS [0x06]), B60E, B60A, Local0)
            M600 (Arg0, 0x2A, Local0, BS1F)
            Mid (DerefOf (PAUB [0x06]), B60E, B60A, Local0)
            M600 (Arg0, 0x2B, Local0, BB35)
            /* Method returns Object */

            Mid (M601 (0x02, 0x06), B60E, B60A, Local0)
            M600 (Arg0, 0x2C, Local0, BS1F)
            Mid (M601 (0x03, 0x06), B60E, B60A, Local0)
            M600 (Arg0, 0x2D, Local0, BB35)
            /* Method returns Reference */

            If (Y500)
            {
                Mid (DerefOf (M602 (0x02, 0x06, 0x01)), B60E, B60A, Local0)
                M600 (Arg0, 0x2E, Local0, BS1F)
                Mid (DerefOf (M602 (0x03, 0x06, 0x01)), B60E, B60A, Local0)
                M600 (Arg0, 0x2F, Local0, BB35)
            }
        }

        Method (M32S, 1, Serialized)
        {
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            Name (B60E, Buffer (0x01)
            {
                 0x0B                                             // .
            })
            /* String to Integer conversion of the String Length operand */

            Local0 = Mid ("This is auxiliary String", 0x00, B60A)
            M600 (Arg0, 0x00, Local0, BS1E)
            Local0 = Mid (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, 0x00, B60A)
            M600 (Arg0, 0x01, Local0, BB34)
            Local0 = Mid (AUS6, 0x00, B60A)
            M600 (Arg0, 0x02, Local0, BS1E)
            Local0 = Mid (AUB6, 0x00, B60A)
            M600 (Arg0, 0x03, Local0, BB34)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (AUS6)), 0x00, B60A)
                M600 (Arg0, 0x04, Local0, BS1E)
                Local0 = Mid (DerefOf (RefOf (AUB6)), 0x00, B60A)
                M600 (Arg0, 0x05, Local0, BB34)
            }

            Local0 = Mid (DerefOf (PAUS [0x06]), 0x00, B60A)
            M600 (Arg0, 0x06, Local0, BS1E)
            Local0 = Mid (DerefOf (PAUB [0x06]), 0x00, B60A)
            M600 (Arg0, 0x07, Local0, BB34)
            /* Method returns Object */

            Local0 = Mid (M601 (0x02, 0x06), 0x00, B60A)
            M600 (Arg0, 0x08, Local0, BS1E)
            Local0 = Mid (M601 (0x03, 0x06), 0x00, B60A)
            M600 (Arg0, 0x09, Local0, BB34)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Mid (DerefOf (M602 (0x02, 0x06, 0x01)), 0x00, B60A)
                M600 (Arg0, 0x0A, Local0, BS1E)
                Local0 = Mid (DerefOf (M602 (0x03, 0x06, 0x01)), 0x00, B60A)
                M600 (Arg0, 0x0B, Local0, BB34)
            }

            Mid ("This is auxiliary String", 0x00, B60A, Local0)
            M600 (Arg0, 0x0C, Local0, BS1E)
            Mid (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, 0x00, B60A, Local0)
            M600 (Arg0, 0x0D, Local0, BB34)
            Mid (AUS6, 0x00, B60A, Local0)
            M600 (Arg0, 0x0E, Local0, BS1E)
            Mid (AUB6, 0x00, B60A, Local0)
            M600 (Arg0, 0x0F, Local0, BB34)
            If (Y078)
            {
                Mid (DerefOf (RefOf (AUS6)), 0x00, B60A, Local0)
                M600 (Arg0, 0x10, Local0, BS1E)
                Mid (DerefOf (RefOf (AUB6)), 0x00, B60A, Local0)
                M600 (Arg0, 0x11, Local0, BB34)
            }

            Mid (DerefOf (PAUS [0x06]), 0x00, B60A, Local0)
            M600 (Arg0, 0x12, Local0, BS1E)
            Mid (DerefOf (PAUB [0x06]), 0x00, B60A, Local0)
            M600 (Arg0, 0x13, Local0, BB34)
            /* Method returns Object */

            Mid (M601 (0x02, 0x06), 0x00, B60A, Local0)
            M600 (Arg0, 0x14, Local0, BS1E)
            Mid (M601 (0x03, 0x06), 0x00, B60A, Local0)
            M600 (Arg0, 0x15, Local0, BB34)
            /* Method returns Reference */

            If (Y500)
            {
                Mid (DerefOf (M602 (0x02, 0x06, 0x01)), 0x00, B60A, Local0)
                M600 (Arg0, 0x16, Local0, BS1E)
                Mid (DerefOf (M602 (0x03, 0x06, 0x01)), 0x00, B60A, Local0)
                M600 (Arg0, 0x17, Local0, BB34)
            }

            /* String to Integer conversion of the both String operands */

            Local0 = Mid ("This is auxiliary String", B60E, B60A)
            M600 (Arg0, 0x18, Local0, BS1F)
            Local0 = Mid (Buffer (0x19)
                    {
                        "This is auxiliary Buffer"
                    }, B60E, B60A)
            M600 (Arg0, 0x19, Local0, BB35)
            Local0 = Mid (AUS6, B60E, B60A)
            M600 (Arg0, 0x1A, Local0, BS1F)
            Local0 = Mid (AUB6, B60E, B60A)
            M600 (Arg0, 0x1B, Local0, BB35)
            If (Y078)
            {
                Local0 = Mid (DerefOf (RefOf (AUS6)), B60E, B60A)
                M600 (Arg0, 0x1C, Local0, BS1F)
                Local0 = Mid (DerefOf (RefOf (AUB6)), B60E, B60A)
                M600 (Arg0, 0x1D, Local0, BB35)
            }

            Local0 = Mid (DerefOf (PAUS [0x06]), B60E, B60A)
            M600 (Arg0, 0x1E, Local0, BS1F)
            Local0 = Mid (DerefOf (PAUB [0x06]), B60E, B60A)
            M600 (Arg0, 0x1F, Local0, BB35)
            /* Method returns Object */

            Local0 = Mid (M601 (0x02, 0x06), B60E, B60A)
            M600 (Arg0, 0x20, Local0, BS1F)
            Local0 = Mid (M601 (0x03, 0x06), B60E, B60A)
            M600 (Arg0, 0x21, Local0, BB35)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Mid (DerefOf (M602 (0x02, 0x06, 0x01)), B60E, B60A)
                M600 (Arg0, 0x22, Local0, BS1F)
                Local0 = Mid (DerefOf (M602 (0x03, 0x06, 0x01)), B60E, B60A)
                M600 (Arg0, 0x23, Local0, BB35)
            }

            Mid ("This is auxiliary String", B60E, B60A, Local0)
            M600 (Arg0, 0x24, Local0, BS1F)
            Mid (Buffer (0x19)
                {
                    "This is auxiliary Buffer"
                }, B60E, B60A, Local0)
            M600 (Arg0, 0x25, Local0, BB35)
            Mid (AUS6, B60E, B60A, Local0)
            M600 (Arg0, 0x26, Local0, BS1F)
            Mid (AUB6, B60E, B60A, Local0)
            M600 (Arg0, 0x27, Local0, BB35)
            If (Y078)
            {
                Mid (DerefOf (RefOf (AUS6)), B60E, B60A, Local0)
                M600 (Arg0, 0x28, Local0, BS1F)
                Mid (DerefOf (RefOf (AUB6)), B60E, B60A, Local0)
                M600 (Arg0, 0x29, Local0, BB35)
            }

            Mid (DerefOf (PAUS [0x06]), B60E, B60A, Local0)
            M600 (Arg0, 0x2A, Local0, BS1F)
            Mid (DerefOf (PAUB [0x06]), B60E, B60A, Local0)
            M600 (Arg0, 0x2B, Local0, BB35)
            /* Method returns Object */

            Mid (M601 (0x02, 0x06), B60E, B60A, Local0)
            M600 (Arg0, 0x2C, Local0, BS1F)
            Mid (M601 (0x03, 0x06), B60E, B60A, Local0)
            M600 (Arg0, 0x2D, Local0, BB35)
            /* Method returns Reference */

            If (Y500)
            {
                Mid (DerefOf (M602 (0x02, 0x06, 0x01)), B60E, B60A, Local0)
                M600 (Arg0, 0x2E, Local0, BS1F)
                Mid (DerefOf (M602 (0x03, 0x06, 0x01)), B60E, B60A, Local0)
                M600 (Arg0, 0x2F, Local0, BB35)
            }
        }

        /* Buffer to Integer conversion of the Buffer StartIndex */
        /* operand of the Match operator */
        Method (M06A, 1, Serialized)
        {
            Name (B60E, Buffer (0x01)
            {
                 0x0B                                             // .
            })
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
                    }, MEQ, 0x0A5D, MTR, 0x00, B60E)
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
                    }, MEQ, 0x0A5A, MTR, 0x00, B60E)
            M600 (Arg0, 0x01, Local0, Ones)
            Local0 = Match (AUP0, MEQ, 0x0A5D, MTR, 0x00, B60E)
            M600 (Arg0, 0x02, Local0, 0x0D)
            Local0 = Match (AUP0, MEQ, 0x0A5A, MTR, 0x00, B60E)
            M600 (Arg0, 0x03, Local0, Ones)
            If (Y078)
            {
                Local0 = Match (DerefOf (RefOf (AUP0)), MEQ, 0x0A5D, MTR, 0x00, B60E)
                M600 (Arg0, 0x04, Local0, 0x0D)
                Local0 = Match (DerefOf (RefOf (AUP0)), MEQ, 0x0A5A, MTR, 0x00, B60E)
                M600 (Arg0, 0x05, Local0, Ones)
            }

            Local0 = Match (DerefOf (PAUP [0x00]), MEQ, 0x0A5D, MTR, 0x00,
                B60E)
            M600 (Arg0, 0x06, Local0, 0x0D)
            Local0 = Match (DerefOf (PAUP [0x00]), MEQ, 0x0A5A, MTR, 0x00,
                B60E)
            M600 (Arg0, 0x07, Local0, Ones)
            /* Method returns Object */

            Local0 = Match (M601 (0x04, 0x00), MEQ, 0x0A5D, MTR, 0x00, B60E)
            M600 (Arg0, 0x08, Local0, 0x0D)
            Local0 = Match (M601 (0x04, 0x00), MEQ, 0x0A5A, MTR, 0x00, B60E)
            M600 (Arg0, 0x09, Local0, Ones)
            /* Method returns Reference */

            If (Y500)
            {
                Local0 = Match (DerefOf (M602 (0x04, 0x00, 0x01)), MEQ, 0x0A5D, MTR, 0x00,
                    B60E)
                M600 (Arg0, 0x0A, Local0, 0x0D)
                Local0 = Match (DerefOf (M602 (0x04, 0x00, 0x01)), MEQ, 0x0A5A, MTR, 0x00,
                    B60E)
                M600 (Arg0, 0x0B, Local0, Ones)
            }
        }

        /*	Method(m64t, 1) */
        /*	Method(m32t, 1) */
        /* Buffer to Integer conversion of the Buffer sole operand */
        /* of the Method execution control operators (Sleep, Stall) */
        Method (M06B, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B613, Buffer (0x01)
            {
                 0x3F                                             // ?
            })
            CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
            /* Sleep */

            Local0 = Timer
            Sleep (B606)
            CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
            Local1 = Timer
            Local2 = (Local1 - Local0)
            If ((Local2 < C08C))
            {
                ERR (Arg0, Z088, __LINE__, 0x00, 0x00, Local2, C08C)
            }

            /* Stall */

            Local0 = Timer
            Stall (B613)
            CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
            Local1 = Timer
            Local2 = (Local1 - Local0)
            If ((Local2 < 0x03DE))
            {
                ERR (Arg0, Z088, __LINE__, 0x00, 0x00, Local2, 0x03DE)
            }
        }

        /* Buffer to Integer conversion of the Buffer TimeoutValue */
        /* (second) operand of the Acquire operator */
        Method (M06C, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Mutex (MTX0, 0x00)
            Acquire (MTX0, 0x0000)
            CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
            Local0 = Timer
            /* Compiler allows only Integer constant as TimeoutValue (Bug 1)
             Acquire(MTX0, b606)
             */
            CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
            Local1 = Timer
            Local2 = (Local1 - Local0)
            If ((Local2 < C08C))
            {
                ERR (Arg0, Z088, __LINE__, 0x00, 0x00, Local2, C08C)
            }
        }

        /* Buffer to Integer conversion of the Buffer TimeoutValue */
        /* (second) operand of the Wait operator */
        Method (M06D, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Event (EVT0)
            CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
            Local0 = Timer
            Wait (EVT0, B606)
            CH03 (Arg0, Z088, __LINE__, 0x00, 0x00)
            Local1 = Timer
            Local2 = (Local1 - Local0)
            If ((Local2 < C08C))
            {
                ERR (Arg0, Z088, __LINE__, 0x00, 0x00, Local2, C08C)
            }
        }

        /* Buffer to Integer conversion of the Buffer value */
        /* of Predicate of the Method execution control statements */
        /* (If, ElseIf, While) */
        Method (M06E, 1, Serialized)
        {
            Name (B600, Buffer (0x01)
            {
                 0x00                                             // .
            })
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60A, Buffer (0x09)
            {
                /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                /* 0008 */  0xA5                                             // .
            })
            Name (IST0, 0x00)
            Method (M001, 0, NotSerialized)
            {
                If (B600)
                {
                    IST0 = 0x00
                }
            }

            Method (M002, 0, NotSerialized)
            {
                If (B606)
                {
                    IST0 = 0x02
                }
            }

            Method (M003, 0, NotSerialized)
            {
                If (B60A)
                {
                    IST0 = 0x03
                }
            }

            Method (M004, 0, NotSerialized)
            {
                If (B60A)
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
                ElseIf (B600)
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
                ElseIf (B606)
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
                ElseIf (B60A)
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
                ElseIf (B60A)
                {
                    IST0 = 0x08
                }
            }

            Method (M009, 0, NotSerialized)
            {
                While (B600)
                {
                    IST0 = 0x00
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

        /*	Method(m64u, 1) */
        /*	Method(m32u, 1) */
        /* Buffer to String implicit conversion Cases. */
        /* Buffer to String conversion of the Buffer second operand of */
        /* Logical operators when the first operand is evaluated as String. */
        /* LEqual LGreater LGreaterEqual LLess LLessEqual LNotEqual */
        Method (M06F, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60C, Buffer (0x43)
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
            /* LEqual */

            Local0 = ("21 03 00" == B606)
            M600 (Arg0, 0x00, Local0, Ones)
            Local0 = ("21 03 01" == B606)
            M600 (Arg0, 0x01, Local0, Zero)
            Local0 = (AUS9 == B606)
            M600 (Arg0, 0x02, Local0, Ones)
            Local0 = (AUSA == B606)
            M600 (Arg0, 0x03, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUS9)) == B606)
                M600 (Arg0, 0x04, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUSA)) == B606)
                M600 (Arg0, 0x05, Local0, Zero)
            }

            Local0 = (DerefOf (PAUS [0x09]) == B606)
            M600 (Arg0, 0x06, Local0, Ones)
            Local0 = (DerefOf (PAUS [0x0A]) == B606)
            M600 (Arg0, 0x07, Local0, Zero)
            /* Method returns String */

            Local0 = (M601 (0x02, 0x09) == B606)
            M600 (Arg0, 0x08, Local0, Ones)
            Local0 = (M601 (0x02, 0x0A) == B606)
            M600 (Arg0, 0x09, Local0, Zero)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x02, 0x09, 0x01)) == B606)
                M600 (Arg0, 0x0A, Local0, Ones)
                Local0 = (DerefOf (M602 (0x02, 0x0A, 0x01)) == B606)
                M600 (Arg0, 0x0B, Local0, Zero)
            }

            /* LGreater */

            Local0 = ("21 03 00" > B606)
            M600 (Arg0, 0x0C, Local0, Zero)
            Local0 = ("21 03 01" > B606)
            M600 (Arg0, 0x0D, Local0, Ones)
            Local0 = ("21 03 0 " > B606)
            M600 (Arg0, 0x0E, Local0, Zero)
            Local0 = ("21 03 00q" > B606)
            M600 (Arg0, 0x0F, Local0, Ones)
            Local0 = (AUS9 > B606)
            M600 (Arg0, 0x10, Local0, Zero)
            Local0 = (AUSA > B606)
            M600 (Arg0, 0x11, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUS9)) > B606)
                M600 (Arg0, 0x12, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUSA)) > B606)
                M600 (Arg0, 0x13, Local0, Ones)
            }

            Local0 = (DerefOf (PAUS [0x09]) > B606)
            M600 (Arg0, 0x14, Local0, Zero)
            Local0 = (DerefOf (PAUS [0x0A]) > B606)
            M600 (Arg0, 0x15, Local0, Ones)
            /* Method returns String */

            Local0 = (M601 (0x02, 0x09) > B606)
            M600 (Arg0, 0x16, Local0, Zero)
            Local0 = (M601 (0x02, 0x0A) > B606)
            M600 (Arg0, 0x17, Local0, Ones)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x02, 0x09, 0x01)) > B606)
                M600 (Arg0, 0x18, Local0, Zero)
                Local0 = (DerefOf (M602 (0x02, 0x0A, 0x01)) > B606)
                M600 (Arg0, 0x19, Local0, Ones)
            }

            /* LGreaterEqual */

            Local0 = ("21 03 00" >= B606)
            M600 (Arg0, 0x1A, Local0, Ones)
            Local0 = ("21 03 01" >= B606)
            M600 (Arg0, 0x1B, Local0, Ones)
            Local0 = ("21 03 0 " >= B606)
            M600 (Arg0, 0x1C, Local0, Zero)
            Local0 = ("21 03 00q" >= B606)
            M600 (Arg0, 0x1D, Local0, Ones)
            Local0 = (AUS9 >= B606)
            M600 (Arg0, 0x1E, Local0, Ones)
            Local0 = (AUSA >= B606)
            M600 (Arg0, 0x1F, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUS9)) >= B606)
                M600 (Arg0, 0x20, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUSA)) >= B606)
                M600 (Arg0, 0x21, Local0, Ones)
            }

            Local0 = (DerefOf (PAUS [0x09]) >= B606)
            M600 (Arg0, 0x22, Local0, Ones)
            Local0 = (DerefOf (PAUS [0x0A]) >= B606)
            M600 (Arg0, 0x23, Local0, Ones)
            /* Method returns String */

            Local0 = (M601 (0x02, 0x09) >= B606)
            M600 (Arg0, 0x24, Local0, Ones)
            Local0 = (M601 (0x02, 0x0A) >= B606)
            M600 (Arg0, 0x25, Local0, Ones)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x02, 0x09, 0x01)) >= B606)
                M600 (Arg0, 0x26, Local0, Ones)
                Local0 = (DerefOf (M602 (0x02, 0x0A, 0x01)) >= B606)
                M600 (Arg0, 0x27, Local0, Ones)
            }

            /* LLess */

            Local0 = ("21 03 00" < B606)
            M600 (Arg0, 0x28, Local0, Zero)
            Local0 = ("21 03 01" < B606)
            M600 (Arg0, 0x29, Local0, Zero)
            Local0 = ("21 03 0 " < B606)
            M600 (Arg0, 0x2A, Local0, Ones)
            Local0 = ("21 03 00q" < B606)
            M600 (Arg0, 0x2B, Local0, Zero)
            Local0 = (AUS9 < B606)
            M600 (Arg0, 0x2C, Local0, Zero)
            Local0 = (AUSA < B606)
            M600 (Arg0, 0x2D, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUS9)) < B606)
                M600 (Arg0, 0x2E, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUSA)) < B606)
                M600 (Arg0, 0x2F, Local0, Zero)
            }

            Local0 = (DerefOf (PAUS [0x09]) < B606)
            M600 (Arg0, 0x30, Local0, Zero)
            Local0 = (DerefOf (PAUS [0x0A]) < B606)
            M600 (Arg0, 0x31, Local0, Zero)
            /* Method returns String */

            Local0 = (M601 (0x02, 0x09) < B606)
            M600 (Arg0, 0x32, Local0, Zero)
            Local0 = (M601 (0x02, 0x0A) < B606)
            M600 (Arg0, 0x33, Local0, Zero)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x02, 0x09, 0x01)) < B606)
                M600 (Arg0, 0x34, Local0, Zero)
                Local0 = (DerefOf (M602 (0x02, 0x0A, 0x01)) < B606)
                M600 (Arg0, 0x35, Local0, Zero)
            }

            /* LLessEqual */

            Local0 = ("21 03 00" <= B606)
            M600 (Arg0, 0x36, Local0, Ones)
            Local0 = ("21 03 01" <= B606)
            M600 (Arg0, 0x37, Local0, Zero)
            Local0 = ("21 03 0 " <= B606)
            M600 (Arg0, 0x38, Local0, Ones)
            Local0 = ("21 03 00q" <= B606)
            M600 (Arg0, 0x39, Local0, Zero)
            Local0 = (AUS9 <= B606)
            M600 (Arg0, 0x3A, Local0, Ones)
            Local0 = (AUSA <= B606)
            M600 (Arg0, 0x3B, Local0, Zero)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUS9)) <= B606)
                M600 (Arg0, 0x3C, Local0, Ones)
                Local0 = (DerefOf (RefOf (AUSA)) <= B606)
                M600 (Arg0, 0x3D, Local0, Zero)
            }

            Local0 = (DerefOf (PAUS [0x09]) <= B606)
            M600 (Arg0, 0x3E, Local0, Ones)
            Local0 = (DerefOf (PAUS [0x0A]) <= B606)
            M600 (Arg0, 0x3F, Local0, Zero)
            /* Method returns String */

            Local0 = (M601 (0x02, 0x09) <= B606)
            M600 (Arg0, 0x40, Local0, Ones)
            Local0 = (M601 (0x02, 0x0A) <= B606)
            M600 (Arg0, 0x41, Local0, Zero)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x02, 0x09, 0x01)) <= B606)
                M600 (Arg0, 0x42, Local0, Ones)
                Local0 = (DerefOf (M602 (0x02, 0x0A, 0x01)) <= B606)
                M600 (Arg0, 0x43, Local0, Zero)
            }

            /* LNotEqual */

            Local0 = ("21 03 00" != B606)
            M600 (Arg0, 0x44, Local0, Zero)
            Local0 = ("21 03 01" != B606)
            M600 (Arg0, 0x45, Local0, Ones)
            Local0 = ("21 03 0 " != B606)
            M600 (Arg0, 0x46, Local0, Ones)
            Local0 = ("21 03 00q" != B606)
            M600 (Arg0, 0x47, Local0, Ones)
            Local0 = (AUS9 != B606)
            M600 (Arg0, 0x48, Local0, Zero)
            Local0 = (AUSA != B606)
            M600 (Arg0, 0x49, Local0, Ones)
            If (Y078)
            {
                Local0 = (DerefOf (RefOf (AUS9)) != B606)
                M600 (Arg0, 0x4A, Local0, Zero)
                Local0 = (DerefOf (RefOf (AUSA)) != B606)
                M600 (Arg0, 0x4B, Local0, Ones)
            }

            Local0 = (DerefOf (PAUS [0x09]) != B606)
            M600 (Arg0, 0x4C, Local0, Zero)
            Local0 = (DerefOf (PAUS [0x0A]) != B606)
            M600 (Arg0, 0x4D, Local0, Ones)
            /* Method returns String */

            Local0 = (M601 (0x02, 0x09) != B606)
            M600 (Arg0, 0x4E, Local0, Zero)
            Local0 = (M601 (0x02, 0x0A) != B606)
            M600 (Arg0, 0x4F, Local0, Ones)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = (DerefOf (M602 (0x02, 0x09, 0x01)) != B606)
                M600 (Arg0, 0x50, Local0, Zero)
                Local0 = (DerefOf (M602 (0x02, 0x0A, 0x01)) != B606)
                M600 (Arg0, 0x51, Local0, Ones)
            }

            /* Boundary Cases */

            Local0 = ("21 22 23 24 25 26 27 28 29 2A 2B 2C 2D 2E 2F 30 31 32 33 34 35 36 37 38 39 3A 3B 3C 3D 3E 3F 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F 50 51 52 53 54 55 56 57 58 59 5A 5B 5C 5D 5E 5F 60 61 62 63" == B60C)
            M600 (Arg0, 0x52, Local0, Ones)
            Local0 = ("21 22 23 24 25 26 27 28 29 2A 2B 2C 2D 2E 2F 30 31 32 33 34 35 36 37 38 39 3A 3B 3C 3D 3E 3F 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F 50 51 52 53 54 55 56 57 58 59 5A 5B 5C 5D 5E 5F 60 61 62 64" == B60C)
            M600 (Arg0, 0x53, Local0, Zero)
            Local0 = ("21 22 23 24 25 26 27 28 29 2A 2B 2C 2D 2E 2F 30 31 32 33 34 35 36 37 38 39 3A 3B 3C 3D 3E 3F 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F 50 51 52 53 54 55 56 57 58 59 5A 5B 5C 5D 5E 5F 60 61 62 63" > B60C)
            M600 (Arg0, 0x54, Local0, Zero)
            Local0 = ("21 22 23 24 25 26 27 28 29 2A 2B 2C 2D 2E 2F 30 31 32 33 34 35 36 37 38 39 3A 3B 3C 3D 3E 3F 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F 50 51 52 53 54 55 56 57 58 59 5A 5B 5C 5D 5E 5F 60 61 62 64" > B60C)
            M600 (Arg0, 0x55, Local0, Ones)
            Local0 = ("21 22 23 24 25 26 27 28 29 2A 2B 2C 2D 2E 2F 30 31 32 33 34 35 36 37 38 39 3A 3B 3C 3D 3E 3F 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F 50 51 52 53 54 55 56 57 58 59 5A 5B 5C 5D 5E 5F 60 61 62 63" >= B60C)
            M600 (Arg0, 0x56, Local0, Ones)
            Local0 = ("21 22 23 24 25 26 27 28 29 2A 2B 2C 2D 2E 2F 30 31 32 33 34 35 36 37 38 39 3A 3B 3C 3D 3E 3F 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F 50 51 52 53 54 55 56 57 58 59 5A 5B 5C 5D 5E 5F 60 61 62 64" >= B60C)
            M600 (Arg0, 0x57, Local0, Ones)
            Local0 = ("21 22 23 24 25 26 27 28 29 2A 2B 2C 2D 2E 2F 30 31 32 33 34 35 36 37 38 39 3A 3B 3C 3D 3E 3F 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F 50 51 52 53 54 55 56 57 58 59 5A 5B 5C 5D 5E 5F 60 61 62 63" < B60C)
            M600 (Arg0, 0x58, Local0, Zero)
            Local0 = ("21 22 23 24 25 26 27 28 29 2A 2B 2C 2D 2E 2F 30 31 32 33 34 35 36 37 38 39 3A 3B 3C 3D 3E 3F 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F 50 51 52 53 54 55 56 57 58 59 5A 5B 5C 5D 5E 5F 60 61 62 64" < B60C)
            M600 (Arg0, 0x59, Local0, Zero)
            Local0 = ("21 22 23 24 25 26 27 28 29 2A 2B 2C 2D 2E 2F 30 31 32 33 34 35 36 37 38 39 3A 3B 3C 3D 3E 3F 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F 50 51 52 53 54 55 56 57 58 59 5A 5B 5C 5D 5E 5F 60 61 62 63" <= B60C)
            M600 (Arg0, 0x5A, Local0, Ones)
            Local0 = ("21 22 23 24 25 26 27 28 29 2A 2B 2C 2D 2E 2F 30 31 32 33 34 35 36 37 38 39 3A 3B 3C 3D 3E 3F 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F 50 51 52 53 54 55 56 57 58 59 5A 5B 5C 5D 5E 5F 60 61 62 64" <= B60C)
            M600 (Arg0, 0x5B, Local0, Zero)
            Local0 = ("21 22 23 24 25 26 27 28 29 2A 2B 2C 2D 2E 2F 30 31 32 33 34 35 36 37 38 39 3A 3B 3C 3D 3E 3F 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F 50 51 52 53 54 55 56 57 58 59 5A 5B 5C 5D 5E 5F 60 61 62 63" != B60C)
            M600 (Arg0, 0x5C, Local0, Zero)
            Local0 = ("21 22 23 24 25 26 27 28 29 2A 2B 2C 2D 2E 2F 30 31 32 33 34 35 36 37 38 39 3A 3B 3C 3D 3E 3F 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F 50 51 52 53 54 55 56 57 58 59 5A 5B 5C 5D 5E 5F 60 61 62 64" != B60C)
            M600 (Arg0, 0x5D, Local0, Ones)
        }

        /* Buffer to String conversion of the Buffer second operand of */
        /* Concatenate operator when the first operand is evaluated as String */
        Method (M070, 1, Serialized)
        {
            Name (B606, Buffer (0x03)
            {
                 0x21, 0x03, 0x00                                 // !..
            })
            Name (B60C, Buffer (0x43)
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
            Local0 = Concatenate ("", B606)
            M600 (Arg0, 0x00, Local0, BS25)
            Local0 = Concatenate ("1234q", B606)
            M600 (Arg0, 0x01, Local0, BS26)
            Local0 = Concatenate (AUS0, B606)
            M600 (Arg0, 0x02, Local0, BS25)
            Local0 = Concatenate (AUS1, B606)
            M600 (Arg0, 0x03, Local0, BS26)
            If (Y078)
            {
                Local0 = Concatenate (DerefOf (RefOf (AUS0)), B606)
                M600 (Arg0, 0x04, Local0, BS25)
                Local0 = Concatenate (DerefOf (RefOf (AUS1)), B606)
                M600 (Arg0, 0x05, Local0, BS26)
            }

            Local0 = Concatenate (DerefOf (PAUS [0x00]), B606)
            M600 (Arg0, 0x06, Local0, BS25)
            Local0 = Concatenate (DerefOf (PAUS [0x01]), B606)
            M600 (Arg0, 0x07, Local0, BS26)
            /* Method returns String */

            Local0 = Concatenate (M601 (0x02, 0x00), B606)
            M600 (Arg0, 0x08, Local0, BS25)
            Local0 = Concatenate (M601 (0x02, 0x01), B606)
            M600 (Arg0, 0x09, Local0, BS26)
            /* Method returns Reference to String */

            If (Y500)
            {
                Local0 = Concatenate (DerefOf (M602 (0x02, 0x00, 0x01)), B606)
                M600 (Arg0, 0x0A, Local0, BS25)
                Local0 = Concatenate (DerefOf (M602 (0x02, 0x01, 0x01)), B606)
                M600 (Arg0, 0x0B, Local0, BS26)
            }

            Concatenate ("", B606, Local0)
            M600 (Arg0, 0x0C, Local0, BS25)
            Concatenate ("1234q", B606, Local0)
            M600 (Arg0, 0x0D, Local0, BS26)
            Concatenate (AUS0, B606, Local0)
            M600 (Arg0, 0x0E, Local0, BS25)
            Concatenate (AUS1, B606, Local0)
            M600 (Arg0, 0x0F, Local0, BS26)
            If (Y078)
            {
                Concatenate (DerefOf (RefOf (AUS0)), B606, Local0)
                M600 (Arg0, 0x10, Local0, BS25)
                Concatenate (DerefOf (RefOf (AUS1)), B606, Local0)
                M600 (Arg0, 0x11, Local0, BS26)
            }

            Concatenate (DerefOf (PAUS [0x00]), B606, Local0)
            M600 (Arg0, 0x12, Local0, BS25)
            Concatenate (DerefOf (PAUS [0x01]), B606, Local0)
            M600 (Arg0, 0x13, Local0, BS26)
            /* Method returns String */

            Concatenate (M601 (0x02, 0x00), B606, Local0)
            M600 (Arg0, 0x14, Local0, BS25)
            Concatenate (M601 (0x02, 0x01), B606, Local0)
            M600 (Arg0, 0x15, Local0, BS26)
            /* Method returns Reference to String */

            If (Y500)
            {
                Concatenate (DerefOf (M602 (0x02, 0x00, 0x01)), B606, Local0)
                M600 (Arg0, 0x16, Local0, BS25)
                Concatenate (DerefOf (M602 (0x02, 0x01, 0x01)), B606, Local0)
                M600 (Arg0, 0x17, Local0, BS26)
            }

            /* Boundary Cases */

            Local0 = Concatenate ("", B60C)
            M600 (Arg0, 0x18, Local0, BS27)
        }

        /*	Method(m071, 1) */
        /*	Method(m072, 1) */
        /*
         * Begin of the test body
         */
        /* Integer to String implicit conversion Cases. */
        /* Integer to String conversion of the Integer second operand of */
        /* Logical operators when the first operand is evaluated as String. */
        /* LEqual LGreater LGreaterEqual LLess LLessEqual LNotEqual */
        If (F64)
        {
            Concatenate (__METHOD__, "-m640", Local0)
            SRMT (Local0)
            M640 (Local0)
        }
        Else
        {
            Concatenate (__METHOD__, "-m320", Local0)
            SRMT (Local0)
            M320 (Local0)
        }

        /* Integer to String conversion of the Integer second operand of */
        /* Concatenate operator when the first operand is evaluated as String */
        If (F64)
        {
            Concatenate (__METHOD__, "-m641", Local0)
            SRMT (Local0)
            M641 (Local0)
        }
        Else
        {
            Concatenate (__METHOD__, "-m321", Local0)
            SRMT (Local0)
            M321 (Local0)
        }

        /* Integer to String conversion of the Integer value */
        /* of Expression of Case statement when Expression in */
        /* Switch is either static String data or explicitly */
        /* converted to String by ToDecimalString, ToHexString */
        /* or ToString */
        /* */
        /* Note: Expression of Case can be only static data */
        /* Integer to Buffer implicit conversion Cases. */
        /* Integer to Buffer conversion of the Integer second operand of */
        /* Logical operators when the first operand is evaluated as Buffer */
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

        /* Integer to Buffer conversion of the both Integer operands of */
        /* Concatenate operator */
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

        /* Integer to Buffer conversion of the Integer second operand of */
        /* Concatenate operator when the first operand is evaluated as Buffer */
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

        /* Integer to Buffer conversion of the Integer Source operand of */
        /* ToString operator */
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

        /* Integer to Buffer conversion of the Integer Source operand of */
        /* Mid operator */
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

        /* Integer to Buffer conversion of the Integer value of */
        /* Expression of Case statement when Expression in Switch */
        /* is either static Buffer data or explicitly converted to */
        /* Buffer by ToBuffer */
        /* */
        /* Note: Expression of Case can be only static data */
        /* String to Integer implicit conversion Cases. */
        /* String to Integer conversion of the String sole operand */
        /* of the 1-parameter Integer arithmetic operators */
        /* (Decrement, Increment, FindSetLeftBit, FindSetRightBit, Not) */
        If (F64)
        {
            Concatenate (__METHOD__, "-m64b", Local0)
            SRMT (Local0)
            M64B (Local0)
        }
        Else
        {
            Concatenate (__METHOD__, "-m32b", Local0)
            SRMT (Local0)
            M32B (Local0)
        }

        /* String to Integer conversion of the String sole operand */
        /* of the LNot Logical Integer operator */
        Concatenate (__METHOD__, "-m000", Local0)
        SRMT (Local0)
        M000 (Local0)
        /* String to Integer conversion of the String sole operand */
        /* of the FromBCD and ToBCD conversion operators */
        If (F64)
        {
            Concatenate (__METHOD__, "-m64c", Local0)
            SRMT (Local0)
            M64C (Local0)
        }
        Else
        {
            Concatenate (__METHOD__, "-m32c", Local0)
            SRMT (Local0)
            M32C (Local0)
        }

        /* String to Integer conversion of each String operand */
        /* of the 2-parameter Integer arithmetic operators */
        /* Add, And, Divide, Mod, Multiply, NAnd, NOr, Or, */
        /* ShiftLeft, ShiftRight, Subtract, Xor */
        If (F64)
        {
            M64D (Concatenate (__METHOD__, "-m64d"))
        }
        Else
        {
            M32D (Concatenate (__METHOD__, "-m32d"))
        }

        /* String to Integer conversion of each String operand */
        /* of the 2-parameter Logical Integer operators LAnd and LOr */
        If (F64)
        {
            M64E (Concatenate (__METHOD__, "-m64e"))
        }
        Else
        {
            M32E (Concatenate (__METHOD__, "-m32e"))
        }

        /* String to Integer conversion of the String second operand of */
        /* Logical operators when the first operand is evaluated as Integer */
        /* (LEqual, LGreater, LGreaterEqual, LLess, LLessEqual, LNotEqual) */
        Concatenate (__METHOD__, "-m02b", Local0)
        SRMT (Local0)
        M02B (Local0)
        If (F64)
        {
            Concatenate (__METHOD__, "-m64f", Local0)
            SRMT (Local0)
            M64F (Local0)
        }
        Else
        {
            Concatenate (__METHOD__, "-m32f", Local0)
            SRMT (Local0)
            M32F (Local0)
        }

        /* String to Integer intermediate conversion of the String second */
        /* operand of Concatenate operator in case the first one is Integer */
        If (F64)
        {
            Concatenate (__METHOD__, "-m64g", Local0)
            SRMT (Local0)
            M64G (Local0)
        }
        Else
        {
            Concatenate (__METHOD__, "-m32g", Local0)
            SRMT (Local0)
            M32G (Local0)
        }

        /* String to Integer conversion of the String Length (second) */
        /* operand of the ToString operator */
        Concatenate (__METHOD__, "-m02c", Local0)
        SRMT (Local0)
        M02C (Local0)
        If (F64)
        {
            Concatenate (__METHOD__, "-m64h", Local0)
            SRMT (Local0)
            M64H (Local0)
        }
        Else
        {
            Concatenate (__METHOD__, "-m32h", Local0)
            SRMT (Local0)
            M32H (Local0)
        }

        /* String to Integer conversion of the String Index (second) */
        /* operand of the Index operator */
        Concatenate (__METHOD__, "-m02d", Local0)
        SRMT (Local0)
        M02D (Local0)
        /* String to Integer conversion of the String Arg (third) */
        /* operand of the Fatal operator */
        /* (it can only be checked an exception does not occur) */
        Concatenate (__METHOD__, "-m02e", Local0)
        SRMT (Local0)
        M02E (Local0)
        /* String to Integer conversion of the String Index and Length */
        /* operands of the Mid operator */
        Concatenate (__METHOD__, "-m02f", Local0)
        SRMT (Local0)
        M02F (Local0)
        If (F64)
        {
            Concatenate (__METHOD__, "-m64i", Local0)
            SRMT (Local0)
            M64I (Local0)
        }
        Else
        {
            Concatenate (__METHOD__, "-m32i", Local0)
            SRMT (Local0)
            M32I (Local0)
        }

        /* String to Integer conversion of the String StartIndex */
        /* operand of the Match operator */
        Concatenate (__METHOD__, "-m030", Local0)
        SRMT (Local0)
        M030 (Local0)
        /* String to Integer conversion of the String sole operand */
        /* of the Method execution control operators (Sleep, Stall) */
        Concatenate (__METHOD__, "-m031", Local0)
        SRMT (Local0)
        M031 (Local0)
        /* String to Integer conversion of the String TimeoutValue */
        /* (second) operand of the Acquire operator */
        /* Compiler allows only Integer constant as TimeoutValue (Bug 1)
         Concatenate(ts, "-m032", Local0)
         SRMT(Local0)
         m032(Local0)
         */
        /* String to Integer conversion of the String TimeoutValue */
        /* (second) operand of the Wait operator */
        Concatenate (__METHOD__, "-m033", Local0)
        SRMT (Local0)
        M033 (Local0)
        /* String to Integer conversion of the String value */
        /* of Predicate of the Method execution control statements */
        /* (If, ElseIf, While) */
        Concatenate (__METHOD__, "-m034", Local0)
        SRMT (Local0)
        If (Y111)
        {
            M034 (Local0)
        }
        Else
        {
            BLCK ()
        }

        /* String to Integer conversion of the String value */
        /* of Expression of Case statement when Expression in */
        /* Switch is evaluated as Integer */
        /* */
        /* Note: Expression of Case can be only static data */
        /* String to Buffer implicit conversion Cases. */
        /* String to Buffer conversion of the String second operand of */
        /* Logical operators when the first operand is evaluated as Buffer */
        /* (LEqual, LGreater, LGreaterEqual, LLess, LLessEqual, LNotEqual) */
        Concatenate (__METHOD__, "-m035", Local0)
        SRMT (Local0)
        M035 (Local0)
        /* String to Buffer conversion of the String second operand of */
        /* Concatenate operator when the first operand is evaluated as Buffer */
        Concatenate (__METHOD__, "-m036", Local0)
        SRMT (Local0)
        M036 (Local0)
        /* String to Buffer conversion of the String Source operand of */
        /* ToString operator (has a visual effect in shortening of the */
        /* String taken the null character) */
        Concatenate (__METHOD__, "-m037", Local0)
        SRMT (Local0)
        M037 (Local0)
        /* Buffer to Integer implicit conversion Cases. */
        /* Buffer to Integer conversion of the Buffer sole operand */
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

        /* Buffer to Integer conversion of the Buffer sole operand */
        /* of the LNot Logical Integer operator */
        Concatenate (__METHOD__, "-m03a", Local0)
        SRMT (Local0)
        M03A (Local0)
        /* Buffer to Integer conversion of the Buffer sole operand */
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

        /* Buffer to Integer conversion of each Buffer operand */
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

        /* Buffer to Integer conversion of each Buffer operand */
        /* of the 2-parameter Logical Integer operators LAnd and LOr */
        If (F64)
        {
            M64O (Concatenate (__METHOD__, "-m64o"))
        }
        Else
        {
            M32O (Concatenate (__METHOD__, "-m32o"))
        }

        /* Buffer to Integer conversion of the Buffer second operand of */
        /* Logical operators when the first operand is evaluated as Integer */
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

        /* Buffer to Integer intermediate conversion of the Buffer second */
        /* operand of Concatenate operator in case the first one is Integer */
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

        /* Buffer to Integer conversion of the Buffer Length (second) */
        /* operand of the ToString operator */
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

        /* Buffer to Integer conversion of the Buffer Index (second) */
        /* operand of the Index operator */
        Concatenate (__METHOD__, "-m067", Local0)
        SRMT (Local0)
        M067 (Local0)
        /* Buffer to Integer conversion of the String Arg (third) */
        /* operand of the Fatal operator */
        /* (it can only be checked an exception does not occur) */
        Concatenate (__METHOD__, "-m068", Local0)
        SRMT (Local0)
        M068 (Local0)
        /* Buffer to Integer conversion of the Buffer Index and Length */
        /* operands of the Mid operator */
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

        /* Buffer to Integer conversion of the Buffer StartIndex */
        /* operand of the Match operator */
        Concatenate (__METHOD__, "-m06a", Local0)
        SRMT (Local0)
        M06A (Local0)
        /* Buffer to Integer conversion of the Buffer sole operand */
        /* of the Method execution control operators (Sleep, Stall) */
        Concatenate (__METHOD__, "-m06b", Local0)
        SRMT (Local0)
        M06B (Local0)
        /* Buffer to Integer conversion of the Buffer TimeoutValue */
        /* (second) operand of the Acquire operator */
        /* Compiler allows only Integer constant as TimeoutValue (Bug 1)
         Concatenate(ts, "-m06c", Local0)
         SRMT(Local0)
         m06c(Local0)
         */
        /* Buffer to Integer conversion of the Buffer TimeoutValue */
        /* (second) operand of the Wait operator */
        Concatenate (__METHOD__, "-m06d", Local0)
        SRMT (Local0)
        M06D (Local0)
        /* Buffer to Integer conversion of the Buffer value */
        /* of Predicate of the Method execution control statements */
        /* (If, ElseIf, While) */
        Concatenate (__METHOD__, "-m06e", Local0)
        SRMT (Local0)
        If (Y111)
        {
            M06E (Local0)
        }
        Else
        {
            BLCK ()
        }

        /* Buffer to Integer conversion of the Buffer value */
        /* of Expression of Case statement when Expression in */
        /* Switch is evaluated as Integer */
        /* */
        /* Note: Expression of Case can be only static data */
        /* Buffer to String implicit conversion Cases. */
        /* Buffer to String conversion of the Buffer second operand of */
        /* Logical operators when the first operand is evaluated as String. */
        /* LEqual LGreater LGreaterEqual LLess LLessEqual LNotEqual */
        Concatenate (__METHOD__, "-m06f", Local0)
        SRMT (Local0)
        M06F (Local0)
        /* Buffer to String conversion of the Buffer second operand of */
        /* Concatenate operator when the first operand is evaluated as String */
        Concatenate (__METHOD__, "-m070", Local0)
        SRMT (Local0)
        M070 (Local0)
    }
