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
     * Implicit Source Operand Conversion, complex test
     *
     *
     * Integer to String implicit conversion Cases.
     * There are following cases when this type of conversion is applied:
     * - to the Integer second operand of Logical operators when the first
     *   operand is evaluated as String (LEqual, LGreater, LGreaterEqual,
     *   LLess, LLessEqual, LNotEqual)
     * - to the Integer second operand of Concatenate operator when the first
     *   operand is evaluated as String
     * - to the Integer elements of a search package of Match operator
     *   when some MatchObject is evaluated as String
     * - to the Integer value of Expression of Case statement when
     *   Expression in Switch is either static String data or explicitly
     *   converted to String by ToDecimalString, ToHexString or ToString
     *
     * Integer to Buffer implicit conversion Cases.
     * There are following cases when this type of conversion is applied:
     * - to the Integer second operand of Logical operators when the first
     *   operand is evaluated as Buffer (LEqual, LGreater, LGreaterEqual,
     *   LLess, LLessEqual, LNotEqual)
     * - to both Integer operands of Concatenate operator
     * - to the Integer second operand of Concatenate operator when the first
     *   operand is evaluated as Buffer
     * - to the Integer Source operand of ToString operator
     * - to the Integer Source operand of Mid operator
     * - to the Integer elements of a search package of Match operator
     *   when some MatchObject is evaluated as Buffer
     * - to the Integer value of Expression of Case statement when
     *   Expression in Switch is either static Buffer data or explicitly
     *   converted to Buffer by ToBuffer
     *
     * String to Integer implicit conversion Cases.
     * There are following cases when this type of conversion is applied:
     * - to the String sole operand of the 1-parameter Integer arithmetic
     *   operators (Decrement, Increment, FindSetLeftBit, FindSetRightBit, Not)
     * - to the String sole operand of the LNot Logical Integer operator
     * - to the String sole operand of the FromBCD and ToBCD conversion operators
     * - to each String operand of the 2-parameter Integer arithmetic
     *   operators (Add, And, Divide, Mod, Multiply, NAnd, NOr, Or,
     *   ShiftLeft, ShiftRight, Subtract, Xor)
     * - to each String operand of the 2-parameter Logical Integer
     *   operators LAnd and LOr
     * - to the String second operand of Logical operators when the first
     *   operand is evaluated as Integer (LEqual, LGreater, LGreaterEqual,
     *   LLess, LLessEqual, LNotEqual)
     * - intermediately to the String second operand of Concatenate operator
     *   in case the first one is Integer
     * - to the String Length (second) operand of ToString operator
     * - to the String Index (second) operand of Index operator
     * - to the String Arg (third) operand of Fatal operator
     *   (it can only be checked an exception does not occur)
     * - to the String Index and Length operands of Mid operator
     * - to the String StartIndex operand of Match operator
     * - to the String elements of a search package of Match operator
     *   when some MatchObject is evaluated as Integer
     * - to the String sole operand of the Method execution control operators
     *   (Sleep, Stall)
     * - to the String TimeoutValue (second) operand of the Acquire operator ???
     * - to the String TimeoutValue (second) operand of the Wait operator
     * - to the String value of Predicate of the Method execution control
     *   statements (If, ElseIf, While)
     * - to the String value of Expression of Case statement when
     *   Expression in Switch is evaluated as Integer
     *
     * String to Buffer implicit conversion Cases.
     * There are following cases when this type of conversion is applied:
     * - to the String second operand of Logical operators when the first
     *   operand is evaluated as Buffer (LEqual, LGreater, LGreaterEqual,
     *   LLess, LLessEqual, LNotEqual)
     * - to the String second operand of Concatenate operator when the first
     *   operand is evaluated as Buffer
     * - to the String Source operand of ToString operator (has a visual
     *   effect in shortening of the String taken the null character.
     * - to the String elements of a search package of Match operator
     *   when some MatchObject is evaluated as Buffer
     * - to the String value of Expression of Case statement when
     *   Expression in Switch is either static Buffer data or explicitly
     *   converted to Buffer by ToBuffer
     *
     * Buffer to Integer implicit conversion Cases.
     * There are following cases when this type of conversion is applied:
     * - to the Buffer sole operand of the 1-parameter Integer arithmetic
     *   operators (Decrement, Increment, FindSetLeftBit, FindSetRightBit, Not)
     * - to the Buffer sole operand of the LNot Logical Integer operator
     * - to the Buffer sole operand of the FromBCD and ToBCD conversion operators
     * - to each Buffer operand of the 2-parameter Integer arithmetic
     *   operators (Add, And, Divide, Mod, Multiply, NAnd, NOr, Or,
     *   ShiftLeft, ShiftRight, Subtract, Xor)
     * - to each Buffer operand of the 2-parameter Logical Integer
     *   operators LAnd and LOr
     * - to the Buffer second operand of Logical operators when the first
     *   operand is evaluated as Integer (LEqual, LGreater, LGreaterEqual,
     *   LLess, LLessEqual, LNotEqual)
     * - intermediately to the Buffer second operand of Concatenate operator
     *   in case the first one is Integer
     * - to the Buffer Length (second) operand of ToString operator
     * - to the Buffer Index (second) operand of Index operator
     * - to the Buffer Arg (third) operand of Fatal operator
     *   (it can only be checked an exception does not occur)
     * - to the Buffer Index and Length operands of Mid operator
     * - to the Buffer StartIndex operand of Match operator
     * - to the Buffer elements of a search package of Match operator
     *   when some MatchObject is evaluated as Integer
     * - to the Buffer sole operand of the Method execution control operators
     *   (Sleep, Stall)
     * - to the Buffer TimeoutValue (second) operand of the Acquire operator ???
     * - to the Buffer TimeoutValue (second) operand of the Wait operator
     * - to the Buffer value of Predicate of the Method execution control
     *   statements (If, ElseIf, While)
     * - to the Buffer value of Expression of Case statement when
     *   Expression in Switch is evaluated as Integer
     *
     * Buffer to String implicit conversion Cases.
     * There are following cases when this type of conversion is applied:
     * - to the Buffer second operand of Logical operators when the first
     *   operand is evaluated as String (LEqual, LGreater, LGreaterEqual,
     *   LLess, LLessEqual, LNotEqual)
     * - to the Buffer second operand of Concatenate operator when the first
     *   operand is evaluated as String
     * - to the Buffer elements of a search package of Match operator
     *   when some MatchObject is evaluated as String
     * - to the Buffer value of Expression of Case statement when
     *   Expression in Switch is either static String data or explicitly
     *   converted to String by ToDecimalString, ToHexString or ToString
     *
     * Note 1: Only an expression that is evaluated to a constant
     *         can be used as the Expression of Case
     *
     * Note 2: So as initial elements of a package are either constant
     *         data or name strings then check of implicit conversion
     *         applied to the elements of the search package of Match
     *         operator is limited to a data images case.
     *
     * Buffer field to Integer implicit conversion Cases.
     * First, Buffer field is evaluated either as Integer or as Buffer.
     * Conversion only takes place for Buffer in which case
     * Buffer to Integer test constructions should be used.
     *
     * Buffer field to Buffer implicit conversion Cases.
     * First, Buffer field is evaluated either as Integer or as Buffer.
     * Conversion only takes place for Integer in which case
     * Integer to Buffer test constructions should be used.
     *
     * Buffer field to String implicit conversion Cases.
     * First, Buffer field is evaluated either as Integer or as Buffer
     * For Integer case Integer to String test constructions should be used.
     * For Buffer case Buffer to String test constructions should be used.
     *
     * Field unit implicit conversion is considered similar to
     * Buffer field one.
     *
     *
     * Cases when there are more than one operand for implicit conversion
     * - when the  first operand of Concatenate operator is Integer,
     *   there are additional conversions besides this Integer to Buffer:
     *    = String to Integer conversion if second operand is String
     *    = Buffer to Integer conversion if second operand is Buffer
     *    = Integer to Buffer conversion of the converted second operand
     *
     *
     * EXCEPTIONAL Conditions during implicit conversion
     *
     * String to Integer implicit conversion Cases.
     *
     * Buffer to String implicit conversion Cases.
     *
     * Buffer field to String implicit conversion Cases.
     *
     * Field unit to String implicit conversion Cases.
     *
     */
    Name (Z084, 0x54)
    Name (TERR, "Test error")
    /* Test Data by types */
    /* Test Integers */
    Name (I601, 0xD1)
    Name (I602, 0x000000024CB016EA)
    Name (I603, 0xC179B3FE)
    Name (I604, 0xFE7CB391D650A284)
    Name (I605, 0x00)
    Name (I606, 0xFFFFFFFF)
    Name (I607, 0xFFFFFFFFFFFFFFFF)
    Name (I608, 0x00ABCDEF)
    Name (I609, 0x00ABCDEF)
    Name (I60A, 0xFF)
    Name (I60B, 0x000000FFFFFFFFFF)
    Name (I60C, 0x6179534E)
    Name (I60D, 0x6E7C534136502214)
    Name (I60E, 0x6E00534136002214)
    Name (I60F, 0x6E7C534136002214)
    Name (PI60, Package (0x10)
    {
        0x01,
        0xD1,
        0x000000024CB016EA,
        0xC179B3FE,
        0xFE7CB391D650A284,
        0x00,
        0xFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0x00ABCDEF,
        0x00ABCDEF,
        0xFF,
        0x000000FFFFFFFFFF,
        0x6179534E,
        0x6E7C534136502214,
        0x6E00534136002214,
        0x6E7C534136002214
    })
    /* Test Strings */

    Name (S600, "0")
    Name (S601, "0321")
    Name (S602, "321")
    Name (S603, "ba9876")
    Name (S604, "C179B3FE")
    Name (S605, "FE7CB391D650A284")
    Name (S606, "ffffffff")
    Name (S607, "ffffffffffffffff")
    Name (S608, "fe7cb391d650a2841")
    Name (S609, "9876543210")
    Name (S60A, "0xfe7cb3")
    Name (S60B, "1234q")
    Name (S60C, "")
    Name (S60D, " ")
    /* of size 200 chars */

    Name (S60E, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*")
    /* all symbols 0x01-0x7f */

    Name (S60F, "\x01\x02\x03\x04\x05\x06\a\b\t\n\v\f\r\x0E\x0F\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1A\x1B\x1C\x1D\x1E\x1F !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~\x7F")
    Name (S610, "abcdef")
    Name (S611, "ABCDEF")
    Name (S612, "ff")
    Name (S613, "ffffffffff")
    Name (S614, "B")
    Name (S615, "3789012345678901")
    Name (S616, "D76162EE9EC35")
    Name (S617, "90123456")
    Name (S618, "55F2CC0")
    Name (S619, "c179B3FE")
    Name (S61A, "fE7CB391D650A284")
    Name (S61B, "63")
    Name (PS60, Package (0x1C)
    {
        "0",
        "0321",
        "321",
        "ba9876",
        "C179B3FE",
        "FE7CB391D650A284",
        "ffffffff",
        "ffffffffffffffff",
        "fe7cb391d650a2841",
        "9876543210",
        "0xfe7cb3",
        "1234q",
        "",
        " ",
        /* of size 200 chars */

        "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*",
        /* all symbols 0x01-0x7f */

        "\x01\x02\x03\x04\x05\x06\a\b\t\n\v\f\r\x0E\x0F\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1A\x1B\x1C\x1D\x1E\x1F !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~\x7F",
        "abcdef",
        "ABCDEF",
        "ff",
        "ffffffffff",
        "B",
        "3789012345678901",
        "D76162EE9EC35",
        "90123456",
        "55F2CC0",
        "c179B3FE",
        "fE7CB391D650A284",
        "63"
    })
    /* Test Buffers */

    Name (B600, Buffer (0x01)
    {
         0x00                                             // .
    })
    Name (B601, Buffer (0x01)
    {
         0xA5                                             // .
    })
    Name (B602, Buffer (0x02)
    {
         0x21, 0x03                                       // !.
    })
    Name (B603, Buffer (0x03)
    {
         0x21, 0x03, 0x5A                                 // !.Z
    })
    Name (B604, Buffer (0x03)
    {
         0x21, 0x03, 0x5A                                 // !.Z
    })
    Name (B605, Buffer (0x03)
    {
         0x21, 0x03                                       // !.
    })
    Name (B606, Buffer (0x03)
    {
         0x21, 0x03, 0x00                                 // !..
    })
    Name (B607, Buffer (0x04)
    {
         0xFE, 0xB3, 0x79, 0xC1                           // ..y.
    })
    Name (B608, Buffer (0x05)
    {
         0xFE, 0xB3, 0x79, 0xC1, 0xA5                     // ..y..
    })
    Name (B609, Buffer (0x08)
    {
         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
    })
    Name (B60A, Buffer (0x09)
    {
        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
        /* 0008 */  0xA5                                             // .
    })
    Name (B60B, Buffer (0x0101)
    {
         0x00                                             // .
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
    Name (B60D, Buffer (0x44)
    {
        "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abc"
    })
    Name (B60E, Buffer (0x01)
    {
         0x0B                                             // .
    })
    Name (B60F, Buffer (0x08)
    {
         0x01, 0x89, 0x67, 0x45, 0x23, 0x01, 0x89, 0x37   // ..gE#..7
    })
    Name (B610, Buffer (0x07)
    {
         0x35, 0xEC, 0xE9, 0x2E, 0x16, 0x76, 0x0D         // 5....v.
    })
    Name (B611, Buffer (0x04)
    {
         0x56, 0x34, 0x12, 0x90                           // V4..
    })
    Name (B612, Buffer (0x04)
    {
         0xC0, 0x2C, 0x5F, 0x05                           // .,_.
    })
    Name (B613, Buffer (0x01)
    {
         0x3F                                             // ?
    })
    Name (PB60, Package (0x14)
    {
        Buffer (0x01)
        {
             0x00                                             // .
        },

        Buffer (0x01)
        {
             0xA5                                             // .
        },

        Buffer (0x02)
        {
             0x21, 0x03                                       // !.
        },

        Buffer (0x03)
        {
             0x21, 0x03, 0x5A                                 // !.Z
        },

        Buffer (0x03)
        {
             0x21, 0x03, 0x5A                                 // !.Z
        },

        Buffer (0x03)
        {
             0x21, 0x03                                       // !.
        },

        Buffer (0x03)
        {
             0x21, 0x03, 0x00                                 // !..
        },

        Buffer (0x04)
        {
             0xFE, 0xB3, 0x79, 0xC1                           // ..y.
        },

        Buffer (0x05)
        {
             0xFE, 0xB3, 0x79, 0xC1, 0xA5                     // ..y..
        },

        Buffer (0x08)
        {
             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
        },

        Buffer (0x09)
        {
            /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
            /* 0008 */  0xA5                                             // .
        },

        Buffer (0x0101)
        {
             0x00                                             // .
        },

        Buffer (0x43)
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
        },

        Buffer (0x44)
        {
            "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abc"
        },

        Buffer (0x01)
        {
             0x0B                                             // .
        },

        Buffer (0x08)
        {
             0x01, 0x89, 0x67, 0x45, 0x23, 0x01, 0x89, 0x37   // ..gE#..7
        },

        Buffer (0x07)
        {
             0x35, 0xEC, 0xE9, 0x2E, 0x16, 0x76, 0x0D         // 5....v.
        },

        Buffer (0x04)
        {
             0x56, 0x34, 0x12, 0x90                           // V4..
        },

        Buffer (0x04)
        {
             0xC0, 0x2C, 0x5F, 0x05                           // .,_.
        },

        Buffer (0x01)
        {
             0x3F                                             // ?
        }
    })
    /* Test Buffer Fields */
    /*Name(b630, Buffer(428){}) */
    Name (B630, Buffer (0x01C4){})
    CreateField (B630, 0x00, 0x1F, BF61)
    CreateField (B630, 0x1F, 0x20, BF62)
    CreateField (B630, 0x3F, 0x21, BF63)
    CreateField (B630, 0x60, 0x3F, BF64)
    CreateField (B630, 0x9F, 0x40, BF65)
    CreateField (B630, 0xDF, 0x41, BF66)
    CreateField (B630, 0x0120, 0x0218, BF69)
    CreateField (B630, 0x0338, 0x0220, BF6A)
    CreateField (B630, 0x0558, 0x0808, BF6B)
    /* 3424 */

    CreateField (B630, 0x0D60, 0x1F, BF91)
    CreateField (B630, 0x0D7F, 0x40, BF95)
    CreateField (B630, 0x0DBF, 0x1F, BFA1)
    CreateField (B630, 0x0DDE, 0x40, BFA5)
    /* 3614 */

    Name (B631, Buffer (0x45){})
    CreateField (B631, 0x00, 0x41, BF6C)
    CreateField (B631, 0x41, 0x41, BF6D)
    CreateField (B631, 0x82, 0x21, BF6E)
    CreateField (B631, 0xA3, 0x21, BF6F)
    CreateField (B631, 0xC4, 0x20, BF70)
    CreateField (B631, 0xE4, 0x40, BF71)
    CreateField (B631, 0x0124, 0x40, BF72)
    CreateField (B631, 0x0164, 0x40, BF73)
    CreateField (B631, 0x01A4, 0x21, BF74)
    CreateField (B631, 0x01C5, 0x21, BF75)
    CreateField (B631, 0x01E6, 0x21, BF76)
    CreateField (B631, 0x0207, 0x20, BF77)
    /* 551 */
    /* Test Packages */
    Name (P601, Package (0x01)
    {
        0xC179B3FE
    })
    Name (P602, Package (0x01)
    {
        0xFE7CB391D650A284
    })
    /* Auxiliary agents triggering implicit conversion */
    /* Auxiliary Integers */
    Name (AUI0, Ones)
    Name (AUI1, 0x0321)
    Name (AUI2, 0x000000024CB016EA)
    Name (AUI3, 0xC179B3FE)
    Name (AUI4, 0xFE7CB391D650A284)
    Name (AUI5, 0x00)
    Name (AUI6, 0x01)
    Name (AUI7, 0x03)
    Name (AUI8, 0x04)
    Name (AUI9, 0x05)
    Name (AUIA, 0x08)
    Name (AUIB, 0x09)
    Name (AUIC, 0xC179B3FF)
    Name (AUID, 0xFE7CB391D650A285)
    Name (AUIE, 0xC179B3FD)
    Name (AUIF, 0xFE7CB391D650A283)
    Name (AUIG, 0x0322)
    Name (AUIH, 0x0320)
    Name (AUII, 0xFFFFFFFF)
    Name (AUIJ, 0xFFFFFFFFFFFFFFFF)
    Name (AUIK, 0xD650A284)
    Name (AUIL, 0xD650A285)
    Name (AUIM, 0xD650A283)
    Name (PAUI, Package (0x17)
    {
        Ones,
        0x0321,
        0x000000024CB016EA,
        0xC179B3FE,
        0xFE7CB391D650A284,
        0x00,
        0x01,
        0x03,
        0x04,
        0x05,
        0x08,
        0x09,
        0xC179B3FF,
        0xFE7CB391D650A285,
        0xC179B3FD,
        0xFE7CB391D650A283,
        0x0322,
        0x0320,
        0xFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0xD650A284,
        0xD650A285,
        0xD650A283
    })
    /* Auxiliary Strings */

    Name (AUS0, "")
    Name (AUS1, "1234q")
    Name (AUS2, "c179B3FE")
    Name (AUS3, "C179B3FE")
    Name (AUS4, "FE7CB391D650A284")
    Name (AUS5, "fE7CB391D650A284")
    Name (AUS6, "This is auxiliary String")
    Name (AUS7, "0321")
    Name (AUS8, "321")
    Name (AUS9, "21 03 00")
    Name (AUSA, "21 03 01")
    Name (AUSB, "21 22 23 24 25 26 27 28 29 2A 2B 2C 2D 2E 2F 30 31 32 33 34 35 36 37 38 39 3A 3B 3C 3D 3E 3F 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F 50 51 52 53 54 55 56 57 58 59 5A 5B 5C 5D 5E 5F 60 61 62 63")
    Name (AUSC, "21 22 23 24 25 26 27 28 29 2A 2B 2C 2D 2E 2F 30 31 32 33 34 35 36 37 38 39 3A 3B 3C 3D 3E 3F 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F 50 51 52 53 54 55 56 57 58 59 5A 5B 5C 5D 5E 5F 60 61 62 64")
    Name (PAUS, Package (0x0D)
    {
        "",
        "1234q",
        "c179B3FE",
        "C179B3FE",
        "FE7CB391D650A284",
        "fE7CB391D650A284",
        "This is auxiliary String",
        "0321",
        "321",
        "21 03 00",
        "21 03 01",
        "21 22 23 24 25 26 27 28 29 2A 2B 2C 2D 2E 2F 30 31 32 33 34 35 36 37 38 39 3A 3B 3C 3D 3E 3F 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F 50 51 52 53 54 55 56 57 58 59 5A 5B 5C 5D 5E 5F 60 61 62 63",
        "21 22 23 24 25 26 27 28 29 2A 2B 2C 2D 2E 2F 30 31 32 33 34 35 36 37 38 39 3A 3B 3C 3D 3E 3F 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F 50 51 52 53 54 55 56 57 58 59 5A 5B 5C 5D 5E 5F 60 61 62 64"
    })
    /* Auxiliary Buffers */

    Name (AUB0, Buffer (0x01)
    {
         0x5A                                             // Z
    })
    Name (AUB1, Buffer (0x02)
    {
        "Z"
    })
    Name (AUB2, Buffer (0x04)
    {
         0xFE, 0xB3, 0x79, 0xC2                           // ..y.
    })
    Name (AUB3, Buffer (0x04)
    {
         0xFE, 0xB3, 0x79, 0xC1                           // ..y.
    })
    Name (AUB4, Buffer (0x08)
    {
         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
    })
    Name (AUB5, Buffer (0x08)
    {
         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFF   // ..P...|.
    })
    Name (AUB6, Buffer (0x19)
    {
        "This is auxiliary Buffer"
    })
    Name (AUB7, Buffer (0x05)
    {
        "0321"
    })
    Name (AUB8, Buffer (0x05)
    {
         0x30, 0x33, 0x32, 0x31, 0x01                     // 0321.
    })
    Name (AUB9, Buffer (0x01)
    {
         0x00                                             // .
    })
    Name (AUBA, Buffer (0x01)
    {
         0x01                                             // .
    })
    Name (AUBB, Buffer (0xC9)
    {
        "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*"
    })
    Name (AUBC, Buffer (0xC9)
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
    })
    Name (PAUB, Package (0x0D)
    {
        Buffer (0x01)
        {
             0x5A                                             // Z
        },

        Buffer (0x02)
        {
            "Z"
        },

        Buffer (0x04)
        {
             0xFE, 0xB3, 0x79, 0xC2                           // ..y.
        },

        Buffer (0x04)
        {
             0xFE, 0xB3, 0x79, 0xC1                           // ..y.
        },

        Buffer (0x08)
        {
             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
        },

        Buffer (0x08)
        {
             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFF   // ..P...|.
        },

        Buffer (0x19)
        {
            "This is auxiliary Buffer"
        },

        Buffer (0x05)
        {
            "0321"
        },

        Buffer (0x05)
        {
             0x30, 0x33, 0x32, 0x31, 0x01                     // 0321.
        },

        Buffer (0x01)
        {
             0x00                                             // .
        },

        Buffer (0x01)
        {
             0x01                                             // .
        },

        Buffer (0xC9)
        {
            "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*"
        },

        Buffer (0xC9)
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
        }
    })
    /* Auxiliary Packages */

    Name (AUP0, Package (0x0F)
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
    })
    Name (AUP1, Package (0x01)
    {
        0xFE7CB391D650A284
    })
    Name (AUP2, Package (0x01)
    {
        0xC179B3FE
    })
    Name (PAUP, Package (0x03)
    {
        Package (0x0F)
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
        },

        Package (0x01)
        {
            0xFE7CB391D650A284
        },

        Package (0x01)
        {
            0xC179B3FE
        }
    })
    /* Benchmark Data */
    /* Benchmark Integer Values in case conversion */
    /* Derefof(Index(..., String->Integer)) */
    Name (BI10, 0x69)
    Name (BI11, 0x0A5B)
    /* Benchmark Integer Values in case conversion */
    /* Decrement/Increment(String/Buffer->Integer)) */
    Name (BI12, 0x0320)
    Name (BI13, 0x0321)
    Name (BI14, 0xC179B3FD)
    Name (BI15, 0xC179B3FE)
    Name (BI16, 0xFE7CB391D650A283)
    Name (BI17, 0xFE7CB391D650A284)
    Name (BI18, 0xD650A283)
    Name (BI19, 0xD650A284)
    Name (BI23, 0x0322)
    Name (BI27, 0xFE7CB391D650A285)
    Name (BI29, 0xD650A285)
    /* Benchmark Strings in case conversion */
    /* Concatenate(String, Integer->String) */
    Name (BS10, "FE7CB391D650A284")
    Name (BS11, "1234qFE7CB391D650A284")
    Name (BS12, "C179B3FE")
    Name (BS13, "1234qC179B3FE")
    Name (BS14, "D650A284")
    Name (BS15, "1234qD650A284")
    /* Benchmark Strings in case conversion */
    /* ToString(Integer->Buffer, ...) */
    Name (BS16, "NSya")
    Name (BS17, "NSy")
    Name (BS18, "\x14\"P6AS|n")
    Name (BS19, "\x14\"P")
    Name (BS1A, "\x14\"")
    /* Benchmark Strings in case conversion */
    /* ToString(..., String->Integer) */
    Name (BS1B, "This is aux")
    Name (BS1C, "This is auxiliary Buffer")
    /* Benchmark Strings in case conversion */
    /* Mid(String, String->Integer, Integer) */
    Name (BS1D, "iliary Str")
    Name (BS1E, "This is auxiliary String")
    Name (BS1F, "iliary String")
    /* Benchmark Strings in case conversion */
    /* ToString(String->Buffer, ...) */
    Name (BS20, "0321")
    Name (BS21, "032")
    Name (BS22, "")
    Name (BS23, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*")
    Name (BS24, "!\"#")
    /* Benchmark Strings in case conversion */
    /* Concatenate(String, Buffer->String) */
    Name (BS25, "21 03 00")
    Name (BS26, "1234q21 03 00")
    Name (BS27, "21 22 23 24 25 26 27 28 29 2A 2B 2C 2D 2E 2F 30 31 32 33 34 35 36 37 38 39 3A 3B 3C 3D 3E 3F 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F 50 51 52 53 54 55 56 57 58 59 5A 5B 5C 5D 5E 5F 60 61 62 63")
    /* Benchmark Buffers in case conversion */
    /* Concatenate(Buffer, Integer->Buffer) */
    Name (BB10, Buffer (0x09)
    {
        /* 0000 */  0x5A, 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C,  // Z..P...|
        /* 0008 */  0xFE                                             // .
    })
    Name (BB11, Buffer (0x0A)
    {
        /* 0000 */  0x5A, 0x00, 0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3,  // Z...P...
        /* 0008 */  0x7C, 0xFE                                       // |.
    })
    Name (BB12, Buffer (0x05)
    {
         0x5A, 0xFE, 0xB3, 0x79, 0xC1                     // Z..y.
    })
    Name (BB13, Buffer (0x06)
    {
         0x5A, 0x00, 0xFE, 0xB3, 0x79, 0xC1               // Z...y.
    })
    Name (BB14, Buffer (0x05)
    {
         0x5A, 0x84, 0xA2, 0x50, 0xD6                     // Z..P.
    })
    Name (BB15, Buffer (0x06)
    {
         0x5A, 0x00, 0x84, 0xA2, 0x50, 0xD6               // Z...P.
    })
    Name (BB16, Buffer (0x10)
    {
        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
        /* 0008 */  0x5A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // Z.......
    })
    Name (BB17, Buffer (0x10)
    {
        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
        /* 0008 */  0x5A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // Z.......
    })
    Name (BB18, Buffer (0x08)
    {
         0xFE, 0xB3, 0x79, 0xC1, 0x5A, 0x00, 0x00, 0x00   // ..y.Z...
    })
    Name (BB19, Buffer (0x08)
    {
         0xFE, 0xB3, 0x79, 0xC1, 0x5A, 0x00, 0x00, 0x00   // ..y.Z...
    })
    Name (BB1A, Buffer (0x08)
    {
         0x84, 0xA2, 0x50, 0xD6, 0x5A, 0x00, 0x00, 0x00   // ..P.Z...
    })
    Name (BB1B, Buffer (0x08)
    {
         0x84, 0xA2, 0x50, 0xD6, 0x5A, 0x00, 0x00, 0x00   // ..P.Z...
    })
    /* Benchmark Integer->Buffer Buffers */
    /* If no buffer object exists, a new buffer */
    /* object is created based on the size of */
    /* the integer (4 bytes for 32-bit integers */
    /* and 8 bytes for 64-bit integers). */
    Name (BB1C, Buffer (0x04)
    {
         0xFE, 0xB3, 0x79, 0xC1                           // ..y.
    })
    Name (BB1D, Buffer (0x08)
    {
         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
    })
    /* Benchmark Buffers in case conversion */
    /* Mid(Buffer Field->Integer->Buffer, 0, n, ...) */
    Name (BB1E, Buffer (0x05)
    {
         0xFE, 0xB3, 0x79, 0xC1, 0x01                     // ..y..
    })
    Name (BB1F, Buffer (0x09)
    {
        /* 0000 */  0x21, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // !.......
        /* 0008 */  0x01                                             // .
    })
    /* Benchmark Buffers in case conversion */
    /* Concatenate(Integer->Buffer, Integer->Buffer) */
    Name (BB20, Buffer (0x10)
    {
        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
        /* 0008 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
    })
    Name (BB21, Buffer (0x10)
    {
        /* 0000 */  0x21, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // !.......
        /* 0008 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
    })
    Name (BB22, Buffer (0x10)
    {
        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
        /* 0008 */  0x21, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // !.......
    })
    Name (BB23, Buffer (0x08)
    {
         0xFE, 0xB3, 0x79, 0xC1, 0xFE, 0xB3, 0x79, 0xC1   // ..y...y.
    })
    Name (BB24, Buffer (0x08)
    {
         0x21, 0x03, 0x00, 0x00, 0xFE, 0xB3, 0x79, 0xC1   // !.....y.
    })
    Name (BB25, Buffer (0x08)
    {
         0xFE, 0xB3, 0x79, 0xC1, 0x21, 0x03, 0x00, 0x00   // ..y.!...
    })
    /* Benchmark Buffers in case conversion */
    /* Concatenate(Integer->Buffer, String->Integer->Buffer) */
    /* Concatenate(Integer->Buffer, Buffer->Integer->Buffer) */
    Name (BB26, Buffer (0x10)
    {
        /* 0000 */  0x21, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // !.......
        /* 0008 */  0x21, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // !.......
    })
    Name (BB27, Buffer (0x08)
    {
         0x21, 0x03, 0x00, 0x00, 0x21, 0x03, 0x00, 0x00   // !...!...
    })
    Name (BB28, Buffer (0x08)
    {
         0x21, 0x03, 0x00, 0x00, 0x84, 0xA2, 0x50, 0xD6   // !.....P.
    })
    /* Benchmark Buffers in case conversion */
    /* Concatenate(Buffer, String->Buffer) */
    Name (BB29, Buffer (0x06)
    {
        "Z0321"
    })
    Name (BB2A, Buffer (0x07)
    {
         0x5A, 0x00, 0x30, 0x33, 0x32, 0x31, 0x00         // Z.0321.
    })
    Name (BB2B, Buffer (0x02)
    {
        "Z"
    })
    Name (BB2C, Buffer (0x03)
    {
         0x5A, 0x00, 0x00                                 // Z..
    })
    Name (BB2D, Buffer (0xC9)
    {
        "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*"
    })
    /* Benchmark Buffers in case conversion */
    /* Mid(Integer->Buffer, 1, n, ...) */
    Name (BB30, Buffer (0x07)
    {
         0x22, 0x00, 0x36, 0x41, 0x53, 0x7C, 0x6E         // ".6AS|n
    })
    Name (BB31, Buffer (0x03)
    {
         0x22, 0x00, 0x36                                 // ".6
    })
    /* Benchmark Buffers in case conversion */
    /* Mid(Buffer, String->Integer, Integer) */
    Name (BB32, Buffer (0x0A)
    {
        /* 0000 */  0x69, 0x6C, 0x69, 0x61, 0x72, 0x79, 0x20, 0x42,  // iliary B
        /* 0008 */  0x75, 0x66                                       // uf
    })
    Name (BB33, Buffer (0x0B)
    {
        /* 0000 */  0x54, 0x68, 0x69, 0x73, 0x20, 0x69, 0x73, 0x20,  // This is
        /* 0008 */  0x61, 0x75, 0x78                                 // aux
    })
    Name (BB34, Buffer (0x19)
    {
        "This is auxiliary Buffer"
    })
    Name (BB35, Buffer (0x0E)
    {
        "iliary Buffer"
    })
    /* Check Result of operation on equal to Benchmark value */
    /* m600(<method name>, */
    /*	<internal type of error if it occurs>, */
    /*	<Result>, */
    /*	<Benchmark value>) */
    Method (M600, 4, NotSerialized)
    {
        Local0 = ObjectType (Arg2)
        Local1 = ObjectType (Arg3)
        If ((Local0 != Local1))
        {
            ERR (Concatenate (Arg0, "-OType"), Z084, __LINE__, 0x00, 0x00, Local0, Local1)
        }
        ElseIf ((Arg2 != Arg3))
        {
            ERR (Arg0, Z084, __LINE__, 0x00, 0x00, Arg2, Arg3)
        }
    }

    /* Obtain specified Constant Auxiliary Object */
    /* as result of a Method invocation (by Return) */
    /* m601(<type>, */
    /*	<opcode>) */
    Method (M601, 2, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x01)
            {
                /* Integer */

                Switch (ToInteger (Arg1))
                {
                    Case (0x00)
                    {
                        Local0 = 0x00
                        Return (Ones)
                    }
                    Case (0x01)
                    {
                        Return (0x0321)
                    }
                    Case (0x02)
                    {
                        Return (0x000000024CB016EA)
                    }
                    Case (0x03)
                    {
                        Return (0xC179B3FE)
                    }
                    Case (0x04)
                    {
                        Return (0xFE7CB391D650A284)
                    }
                    Case (0x05)
                    {
                        Return (0x00)
                    }
                    Case (0x06)
                    {
                        Return (0x01)
                    }
                    Case (0x07)
                    {
                        Return (0x03)
                    }
                    Case (0x08)
                    {
                        Return (0x04)
                    }
                    Case (0x09)
                    {
                        Return (0x05)
                    }
                    Case (0x0A)
                    {
                        Return (0x08)
                    }
                    Case (0x0B)
                    {
                        Return (0x09)
                    }
                    Case (0x0C)
                    {
                        Return (0xC179B3FF)
                    }
                    Case (0x0D)
                    {
                        Return (0xFE7CB391D650A285)
                    }
                    Case (0x0E)
                    {
                        Return (0xC179B3FD)
                    }
                    Case (0x0F)
                    {
                        Return (0xFE7CB391D650A283)
                    }
                    Case (0x10)
                    {
                        Return (0x0322)
                    }
                    Case (0x11)
                    {
                        Return (0x0320)
                    }
                    Case (0x12)
                    {
                        Return (0xFFFFFFFF)
                    }
                    Case (0x13)
                    {
                        Return (0xFFFFFFFFFFFFFFFF)
                    }
                    Case (0x14)
                    {
                        Return (0xD650A284)
                    }
                    Case (0x15)
                    {
                        Return (0xD650A285)
                    }
                    Case (0x16)
                    {
                        Return (0xD650A283)
                    }
                    Default
                    {
                        ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg0, Arg1)
                    }

                }
            }
            Case (0x02)
            {
                /* String */

                Switch (ToInteger (Arg1))
                {
                    Case (0x00)
                    {
                        Return ("")
                    }
                    Case (0x01)
                    {
                        Return ("1234q")
                    }
                    Case (0x02)
                    {
                        Return ("c179B3FE")
                    }
                    Case (0x03)
                    {
                        Return ("C179B3FE")
                    }
                    Case (0x04)
                    {
                        Return ("FE7CB391D650A284")
                    }
                    Case (0x05)
                    {
                        Return ("fE7CB391D650A284")
                    }
                    Case (0x06)
                    {
                        Return ("This is auxiliary String")
                    }
                    Case (0x07)
                    {
                        Return ("0321")
                    }
                    Case (0x08)
                    {
                        Return ("321")
                    }
                    Case (0x09)
                    {
                        Return ("21 03 00")
                    }
                    Case (0x0A)
                    {
                        Return ("21 03 01")
                    }
                    Default
                    {
                        ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg0, Arg1)
                    }

                }
            }
            Case (0x03)
            {
                /* Buffer */

                Switch (ToInteger (Arg1))
                {
                    Case (0x00)
                    {
                        Return (Buffer (0x01)
                        {
                             0x5A                                             // Z
                        })
                    }
                    Case (0x01)
                    {
                        Return (Buffer (0x02)
                        {
                            "Z"
                        })
                    }
                    Case (0x02)
                    {
                        Return (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC2                           // ..y.
                        })
                    }
                    Case (0x03)
                    {
                        Return (Buffer (0x04)
                        {
                             0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                        })
                    }
                    Case (0x04)
                    {
                        Return (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                        })
                    }
                    Case (0x05)
                    {
                        Return (Buffer (0x08)
                        {
                             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFF   // ..P...|.
                        })
                    }
                    Case (0x06)
                    {
                        Return (Buffer (0x19)
                        {
                            "This is auxiliary Buffer"
                        })
                    }
                    Case (0x07)
                    {
                        Return (Buffer (0x05)
                        {
                            "0321"
                        })
                    }
                    Case (0x08)
                    {
                        Return (Buffer (0x05)
                        {
                             0x30, 0x33, 0x32, 0x31, 0x01                     // 0321.
                        })
                    }
                    Default
                    {
                        ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg0, Arg1)
                    }

                }
            }
            Case (0x04)
            {
                /* Package */

                Switch (ToInteger (Arg1))
                {
                    Case (0x00)
                    {
                        Return (Package (0x0F)
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
                        })
                    }
                    Default
                    {
                        ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg0, Arg1)
                    }

                }
            }
            Default
            {
                ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg0, Arg1)
            }

        }

        Return (Local0)
    }

    /* Obtain specified Auxiliary Global Named Object */
    /* or reference to it as result of a Method invocation */
    /* (by Return) */
    /* m602(<type>, */
    /*	<opcode>, */
    /*	<ref_key>) */
    Method (M602, 3, Serialized)
    {
        If ((Arg2 < 0x03))
        {
            Switch (ToInteger (Arg0))
            {
                Case (0x01)
                {
                    /* Integer */

                    Switch (ToInteger (Arg1))
                    {
                        Case (0x00)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUI0) /* \AUI0 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUI0))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUI0, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x01)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUI1) /* \AUI1 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUI1))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUI1, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x02)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUI2) /* \AUI2 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUI2))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUI2, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x03)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUI3) /* \AUI3 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUI3))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUI3, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x04)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUI4) /* \AUI4 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUI4))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUI4, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x05)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUI5) /* \AUI5 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUI5))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUI5, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x06)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUI6) /* \AUI6 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUI6))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUI6, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x07)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUI7) /* \AUI7 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUI7))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUI7, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x08)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUI8) /* \AUI8 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUI8))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUI8, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x09)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUI9) /* \AUI9 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUI9))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUI9, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x0A)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUIA) /* \AUIA */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUIA))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUIA, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x0B)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUIB) /* \AUIB */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUIB))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUIB, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x0C)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUIC) /* \AUIC */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUIC))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUIC, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x0D)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUID) /* \AUID */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUID))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUID, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x0E)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUIE) /* \AUIE */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUIE))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUIE, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x0F)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUIF) /* \AUIF */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUIF))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUIF, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x10)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUIG) /* \AUIG */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUIG))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUIG, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x11)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUIH) /* \AUIH */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUIH))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUIH, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x12)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUII) /* \AUII */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUII))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUII, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x13)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUIJ) /* \AUIJ */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUIJ))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUIJ, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x14)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUIK) /* \AUIK */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUIK))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUIK, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x15)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUIL) /* \AUIL */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUIL))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUIL, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x16)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUIM) /* \AUIM */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUIM))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUIM, Local0)
                                Return (Local0)
                            }
                        }
                        Default
                        {
                            ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg0, Arg1)
                        }

                    }
                }
                Case (0x02)
                {
                    /* String */

                    Switch (ToInteger (Arg1))
                    {
                        Case (0x00)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUS0) /* \AUS0 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUS0))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUS0, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x01)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUS1) /* \AUS1 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUS1))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUS1, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x02)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUS2) /* \AUS2 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUS2))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUS2, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x03)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUS3) /* \AUS3 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUS3))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUS3, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x04)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUS4) /* \AUS4 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUS4))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUS4, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x05)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUS5) /* \AUS5 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUS5))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUS5, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x06)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUS6) /* \AUS6 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUS6))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUS6, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x07)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUS7) /* \AUS7 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUS7))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUS7, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x08)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUS8) /* \AUS8 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUS8))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUS8, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x09)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUS9) /* \AUS9 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUS9))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUS9, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x0A)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUSA) /* \AUSA */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUSA))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUSA, Local0)
                                Return (Local0)
                            }
                        }
                        Default
                        {
                            ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg0, Arg1)
                        }

                    }
                }
                Case (0x03)
                {
                    /* Buffer */

                    Switch (ToInteger (Arg1))
                    {
                        Case (0x00)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUB0) /* \AUB0 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUB0))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUB0, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x01)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUB1) /* \AUB1 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUB1))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUB1, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x02)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUB2) /* \AUB2 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUB2))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUB2, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x03)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUB3) /* \AUB3 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUB3))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUB3, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x04)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUB4) /* \AUB4 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUB4))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUB4, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x05)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUB5) /* \AUB5 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUB5))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUB5, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x06)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUB6) /* \AUB6 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUB6))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUB6, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x07)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUB7) /* \AUB7 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUB7))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUB7, Local0)
                                Return (Local0)
                            }
                        }
                        Case (0x08)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUB8) /* \AUB8 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUB8))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUB8, Local0)
                                Return (Local0)
                            }
                        }
                        Default
                        {
                            ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg0, Arg1)
                        }

                    }
                }
                Case (0x04)
                {
                    /* Package */

                    Switch (ToInteger (Arg1))
                    {
                        Case (0x00)
                        {
                            If ((Arg2 == 0x00))
                            {
                                Return (AUP0) /* \AUP0 */
                            }
                            ElseIf ((Arg2 == 0x01))
                            {
                                Return (RefOf (AUP0))
                            }
                            ElseIf ((Arg2 == 0x02))
                            {
                                CondRefOf (AUP0, Local0)
                                Return (Local0)
                            }
                        }
                        Default
                        {
                            ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg0, Arg1)
                        }

                    }
                }
                Default
                {
                    ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg0, Arg1)
                }

            }
        }
        Else
        {
            ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg1, Arg2)
        }

        Return (Local0)
    }

    /* Obtain specified Auxiliary Element of Package */
    /* or reference to it as result of a Method invocation */
    /* (by Return) */
    /* m603(<type>, */
    /*	<opcode>, */
    /*	<ref_key>) */
    Method (M603, 3, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x01)
            {
                /* Integer */

                If ((Arg1 < 0x17))
                {
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x00)
                        {
                            Return (DerefOf (PAUI [Arg1]))
                        }
                        Case (0x01)
                        {
                            Return (PAUI [Arg1])
                        }
                        Case (0x02)
                        {
                            Local0 = PAUI [Arg1]
                            Return (Local0)
                        }
                        Default
                        {
                            ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        }

                    }
                }
                Else
                {
                    ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg0, Arg1)
                }
            }
            Case (0x02)
            {
                /* String */

                If ((Arg1 < 0x0B))
                {
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x00)
                        {
                            Return (DerefOf (PAUS [Arg1]))
                        }
                        Case (0x01)
                        {
                            Return (PAUS [Arg1])
                        }
                        Case (0x02)
                        {
                            Local0 = PAUS [Arg1]
                            Return (Local0)
                        }
                        Default
                        {
                            ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        }

                    }
                }
                Else
                {
                    ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg0, Arg1)
                }
            }
            Case (0x03)
            {
                /* Buffer */

                If ((Arg1 < 0x09))
                {
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x00)
                        {
                            Return (DerefOf (PAUB [Arg1]))
                        }
                        Case (0x01)
                        {
                            Return (PAUB [Arg1])
                        }
                        Case (0x02)
                        {
                            Local0 = PAUB [Arg1]
                            Return (Local0)
                        }
                        Default
                        {
                            ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        }

                    }
                }
                Else
                {
                    ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg0, Arg1)
                }
            }
            Case (0x04)
            {
                /* Package */

                If ((Arg1 < 0x06))
                {
                    Switch (ToInteger (Arg2))
                    {
                        Case (0x00)
                        {
                            Return (DerefOf (PAUP [Arg1]))
                        }
                        Case (0x01)
                        {
                            Return (PAUP [Arg1])
                        }
                        Case (0x02)
                        {
                            Local0 = PAUP [Arg1]
                            Return (Local0)
                        }
                        Default
                        {
                            ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        }

                    }
                }
                Else
                {
                    ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg0, Arg1)
                }
            }
            Default
            {
                ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg0, Arg1)
            }

        }

        Return (Local0)
    }

    /* Obtain specified Test Object or reference to it by Return */
    /* m604(<carrier> */
    /*  <type>, */
    /*	<opcode>, */
    /*	<ref_key>) */
    Method (M604, 4, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x00)
            {
                /* Constant */

                If (Arg3)
                {
                    ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg1, Arg2)
                }

                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        Switch (ToInteger (Arg2))
                        {
                            Case (0x03)
                            {
                                Return (0xC179B3FE)
                            }
                            Case (0x04)
                            {
                                Return (0xFE7CB391D650A284)
                            }
                            Case (0x0C)
                            {
                                Return (0x6179534E)
                            }
                            Case (0x0D)
                            {
                                Return (0x6E7C534136502214)
                            }
                            Case (0x0E)
                            {
                                Return (0x6E00534136002214)
                            }
                            Case (0x0F)
                            {
                                Return (0x6E7C534136002214)
                            }
                            Default
                            {
                                ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            }

                        }
                    }
                    Case (0x02)
                    {
                        /* String */

                        Switch (ToInteger (Arg2))
                        {
                            Case (0x00)
                            {
                                Return ("0")
                            }
                            Case (0x01)
                            {
                                Return ("0321")
                            }
                            Case (0x04)
                            {
                                Return ("C179B3FE")
                            }
                            Case (0x05)
                            {
                                Return ("FE7CB391D650A284")
                            }
                            Case (0x0C)
                            {
                                Return ("")
                            }
                            Case (0x0E)
                            {
                                Return ("!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*")
                            }
                            Case (0x14)
                            {
                                Return ("B")
                            }
                            Case (0x15)
                            {
                                Return ("3789012345678901")
                            }
                            Case (0x16)
                            {
                                Return ("D76162EE9EC35")
                            }
                            Case (0x17)
                            {
                                Return ("90123456")
                            }
                            Case (0x18)
                            {
                                Return ("55F2CC0")
                            }
                            Case (0x1B)
                            {
                                Return ("63")
                            }
                            Default
                            {
                                ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            }

                        }
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        Switch (ToInteger (Arg2))
                        {
                            Case (0x00)
                            {
                                Return (Buffer (0x01)
                                {
                                     0x00                                             // .
                                })
                            }
                            Case (0x06)
                            {
                                Return (Buffer (0x03)
                                {
                                     0x21, 0x03, 0x00                                 // !..
                                })
                            }
                            Case (0x0A)
                            {
                                Return (Buffer (0x09)
                                {
                                    /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                                    /* 0008 */  0xA5                                             // .
                                })
                            }
                            Case (0x0C)
                            {
                                Return (Buffer (0x43)
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
                            }
                            Case (0x0E)
                            {
                                Return (Buffer (0x01)
                                {
                                     0x0B                                             // .
                                })
                            }
                            Case (0x0F)
                            {
                                Return (Buffer (0x08)
                                {
                                     0x01, 0x89, 0x67, 0x45, 0x23, 0x01, 0x89, 0x37   // ..gE#..7
                                })
                            }
                            Case (0x10)
                            {
                                Return (Buffer (0x07)
                                {
                                     0x35, 0xEC, 0xE9, 0x2E, 0x16, 0x76, 0x0D         // 5....v.
                                })
                            }
                            Case (0x11)
                            {
                                Return (Buffer (0x04)
                                {
                                     0x56, 0x34, 0x12, 0x90                           // V4..
                                })
                            }
                            Case (0x12)
                            {
                                Return (Buffer (0x04)
                                {
                                     0xC0, 0x2C, 0x5F, 0x05                           // .,_.
                                })
                            }
                            Case (0x13)
                            {
                                Return (Buffer (0x01)
                                {
                                     0x3F                                             // ?
                                })
                            }
                            Default
                            {
                                ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            }

                        }
                    }
                    Default
                    {
                        ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg1, Arg2)
                    }

                }
            }
            Case (0x01)
            {
                /* Global Named Object */

                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        Switch (ToInteger (Arg2))
                        {
                            Case (0x03)
                            {
                                Switch (ToInteger (Arg3))
                                {
                                    Case (0x00)
                                    {
                                        Return (I603) /* \I603 */
                                    }
                                    Case (0x01)
                                    {
                                        Return (RefOf (I603))
                                    }
                                    Case (0x02)
                                    {
                                        CondRefOf (I603, Local0)
                                        Return (Local0)
                                    }
                                    Default
                                    {
                                        ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg2, Arg3)
                                    }

                                }
                            }
                            Case (0x04)
                            {
                                Switch (ToInteger (Arg3))
                                {
                                    Case (0x00)
                                    {
                                        Return (I604) /* \I604 */
                                    }
                                    Case (0x01)
                                    {
                                        Return (RefOf (I604))
                                    }
                                    Case (0x02)
                                    {
                                        CondRefOf (I604, Local0)
                                        Return (Local0)
                                    }
                                    Default
                                    {
                                        ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg2, Arg3)
                                    }

                                }
                            }
                            Default
                            {
                                ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg1, Arg2)
                            }

                        }
                    }
                    Default
                    {
                        ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg1, Arg2)
                    }

                }
            }
            Case (0x02)
            {
                /* Element of Package */

                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        /* Integer */

                        If ((Arg2 < 0x10))
                        {
                            Switch (ToInteger (Arg3))
                            {
                                Case (0x00)
                                {
                                    Return (DerefOf (PI60 [Arg2]))
                                }
                                Case (0x01)
                                {
                                    Return (PI60 [Arg2])
                                }
                                Case (0x02)
                                {
                                    Local0 = PI60 [Arg2]
                                    Return (Local0)
                                }
                                Default
                                {
                                    ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg2, Arg3)
                                }

                            }
                        }
                        Else
                        {
                            ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        }
                    }
                    Case (0x02)
                    {
                        /* String */

                        If ((Arg2 < 0x1C))
                        {
                            Switch (ToInteger (Arg3))
                            {
                                Case (0x00)
                                {
                                    Return (DerefOf (PS60 [Arg2]))
                                }
                                Case (0x01)
                                {
                                    Return (PS60 [Arg2])
                                }
                                Case (0x02)
                                {
                                    Local0 = PS60 [Arg2]
                                    Return (Local0)
                                }
                                Default
                                {
                                    ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg2, Arg3)
                                }

                            }
                        }
                        Else
                        {
                            ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        }
                    }
                    Case (0x03)
                    {
                        /* Buffer */

                        If ((Arg2 < 0x14))
                        {
                            Switch (ToInteger (Arg3))
                            {
                                Case (0x00)
                                {
                                    Return (DerefOf (PB60 [Arg2]))
                                }
                                Case (0x01)
                                {
                                    Return (PB60 [Arg2])
                                }
                                Case (0x02)
                                {
                                    Local0 = PB60 [Arg2]
                                    Return (Local0)
                                }
                                Default
                                {
                                    ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg2, Arg3)
                                }

                            }
                        }
                        Else
                        {
                            ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg1, Arg2)
                        }
                    }
                    Default
                    {
                        ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg1, Arg2)
                    }

                }
            }
            Default
            {
                ERR (TERR, Z084, __LINE__, 0x00, 0x00, Arg0, Arg1)
            }

        }

        Return (Local0)
    }

    /* Check consistency of the test Named Objects */
    /* in the root Scope of the Global ACPI namespace */
    /* m605(<msg>, */
    /*	<type>, */
    /*	<pack_flag>) */
    Method (M605, 3, NotSerialized)
    {
        If ((Arg1 == 0x01))
        {
            If (Arg2)
            {
                /* Test Integers Package */

                M600 (Arg0, 0x01, DerefOf (PI60 [0x01]), 0xD1)
                M600 (Arg0, 0x02, DerefOf (PI60 [0x02]), 0x000000024CB016EA)
                M600 (Arg0, 0x03, DerefOf (PI60 [0x03]), 0xC179B3FE)
                M600 (Arg0, 0x04, DerefOf (PI60 [0x04]), 0xFE7CB391D650A284)
                M600 (Arg0, 0x05, DerefOf (PI60 [0x05]), 0x00)
                M600 (Arg0, 0x06, DerefOf (PI60 [0x06]), 0xFFFFFFFF)
                M600 (Arg0, 0x07, DerefOf (PI60 [0x07]), 0xFFFFFFFFFFFFFFFF)
                M600 (Arg0, 0x08, DerefOf (PI60 [0x08]), 0x00ABCDEF)
                M600 (Arg0, 0x09, DerefOf (PI60 [0x09]), 0x00ABCDEF)
                M600 (Arg0, 0x0A, DerefOf (PI60 [0x0A]), 0xFF)
                M600 (Arg0, 0x0B, DerefOf (PI60 [0x0B]), 0x000000FFFFFFFFFF)
                M600 (Arg0, 0x0C, DerefOf (PI60 [0x0C]), 0x6179534E)
                M600 (Arg0, 0x0D, DerefOf (PI60 [0x0D]), 0x6E7C534136502214)
                M600 (Arg0, 0x0E, DerefOf (PI60 [0x0E]), 0x6E00534136002214)
                M600 (Arg0, 0x0F, DerefOf (PI60 [0x0F]), 0x6E7C534136002214)
            }
            Else
            {
                /* Test Integers */

                M600 (Arg0, 0x10, I601, 0xD1)
                M600 (Arg0, 0x11, I602, 0x000000024CB016EA)
                M600 (Arg0, 0x12, I603, 0xC179B3FE)
                M600 (Arg0, 0x13, I604, 0xFE7CB391D650A284)
                M600 (Arg0, 0x14, I605, 0x00)
                M600 (Arg0, 0x15, I606, 0xFFFFFFFF)
                M600 (Arg0, 0x16, I607, 0xFFFFFFFFFFFFFFFF)
                M600 (Arg0, 0x17, I608, 0x00ABCDEF)
                M600 (Arg0, 0x18, I609, 0x00ABCDEF)
                M600 (Arg0, 0x19, I60A, 0xFF)
                M600 (Arg0, 0x1A, I60B, 0x000000FFFFFFFFFF)
                M600 (Arg0, 0x1B, I60C, 0x6179534E)
                M600 (Arg0, 0x1C, I60D, 0x6E7C534136502214)
                M600 (Arg0, 0x1D, I60E, 0x6E00534136002214)
                M600 (Arg0, 0x1E, I60F, 0x6E7C534136002214)
            }
        }
        ElseIf ((Arg1 == 0x02))
        {
            If (Arg2)
            {
                /* Test Strings Package */

                M600 (Arg0, 0x1F, DerefOf (PS60 [0x00]), "0")
                M600 (Arg0, 0x20, DerefOf (PS60 [0x01]), "0321")
                M600 (Arg0, 0x21, DerefOf (PS60 [0x02]), "321")
                M600 (Arg0, 0x22, DerefOf (PS60 [0x03]), "ba9876")
                M600 (Arg0, 0x23, DerefOf (PS60 [0x04]), "C179B3FE")
                M600 (Arg0, 0x24, DerefOf (PS60 [0x05]), "FE7CB391D650A284")
                M600 (Arg0, 0x25, DerefOf (PS60 [0x06]), "ffffffff")
                M600 (Arg0, 0x26, DerefOf (PS60 [0x07]), "ffffffffffffffff")
                M600 (Arg0, 0x27, DerefOf (PS60 [0x08]), "fe7cb391d650a2841")
                M600 (Arg0, 0x28, DerefOf (PS60 [0x09]), "9876543210")
                M600 (Arg0, 0x29, DerefOf (PS60 [0x0A]), "0xfe7cb3")
                M600 (Arg0, 0x2A, DerefOf (PS60 [0x0B]), "1234q")
                M600 (Arg0, 0x2B, DerefOf (PS60 [0x0C]), "")
                M600 (Arg0, 0x2C, DerefOf (PS60 [0x0D]), " ")
                M600 (Arg0, 0x2D, DerefOf (PS60 [0x0E]), "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*")
                M600 (Arg0, 0x2E, DerefOf (PS60 [0x0F]), "\x01\x02\x03\x04\x05\x06\a\b\t\n\v\f\r\x0E\x0F\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1A\x1B\x1C\x1D\x1E\x1F !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~\x7F")
                M600 (Arg0, 0x2F, DerefOf (PS60 [0x10]), "abcdef")
                M600 (Arg0, 0x30, DerefOf (PS60 [0x11]), "ABCDEF")
                M600 (Arg0, 0x31, DerefOf (PS60 [0x12]), "ff")
                M600 (Arg0, 0x32, DerefOf (PS60 [0x13]), "ffffffffff")
                M600 (Arg0, 0x33, DerefOf (PS60 [0x14]), "B")
                M600 (Arg0, 0x34, DerefOf (PS60 [0x15]), "3789012345678901")
                M600 (Arg0, 0x35, DerefOf (PS60 [0x16]), "D76162EE9EC35")
                M600 (Arg0, 0x36, DerefOf (PS60 [0x17]), "90123456")
                M600 (Arg0, 0x37, DerefOf (PS60 [0x18]), "55F2CC0")
                M600 (Arg0, 0x38, DerefOf (PS60 [0x19]), "c179B3FE")
                M600 (Arg0, 0x39, DerefOf (PS60 [0x1A]), "fE7CB391D650A284")
                M600 (Arg0, 0x3A, DerefOf (PS60 [0x1B]), "63")
            }
            Else
            {
                /* Test Strings */

                M600 (Arg0, 0x3B, S600, "0")
                M600 (Arg0, 0x3C, S601, "0321")
                M600 (Arg0, 0x3D, S602, "321")
                M600 (Arg0, 0x3E, S603, "ba9876")
                M600 (Arg0, 0x3F, S604, "C179B3FE")
                M600 (Arg0, 0x40, S605, "FE7CB391D650A284")
                M600 (Arg0, 0x41, S606, "ffffffff")
                M600 (Arg0, 0x42, S607, "ffffffffffffffff")
                M600 (Arg0, 0x43, S608, "fe7cb391d650a2841")
                M600 (Arg0, 0x44, S609, "9876543210")
                M600 (Arg0, 0x45, S60A, "0xfe7cb3")
                M600 (Arg0, 0x46, S60B, "1234q")
                M600 (Arg0, 0x47, S60C, "")
                M600 (Arg0, 0x48, S60D, " ")
                M600 (Arg0, 0x49, S60E, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*")
                M600 (Arg0, 0x4A, S60F, "\x01\x02\x03\x04\x05\x06\a\b\t\n\v\f\r\x0E\x0F\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1A\x1B\x1C\x1D\x1E\x1F !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~\x7F")
                M600 (Arg0, 0x4B, S610, "abcdef")
                M600 (Arg0, 0x4C, S611, "ABCDEF")
                M600 (Arg0, 0x4D, S612, "ff")
                M600 (Arg0, 0x4E, S613, "ffffffffff")
                M600 (Arg0, 0x4F, S614, "B")
                M600 (Arg0, 0x50, S615, "3789012345678901")
                M600 (Arg0, 0x51, S616, "D76162EE9EC35")
                M600 (Arg0, 0x52, S617, "90123456")
                M600 (Arg0, 0x53, S618, "55F2CC0")
                M600 (Arg0, 0x54, S619, "c179B3FE")
                M600 (Arg0, 0x55, S61A, "fE7CB391D650A284")
                M600 (Arg0, 0x56, S61B, "63")
            }
        }
        ElseIf ((Arg1 == 0x03))
        {
            If (Arg2)
            {
                /* Test Buffers Package */

                M600 (Arg0, 0x57, DerefOf (PB60 [0x00]), Buffer (0x01)
                    {
                         0x00                                             // .
                    })
                M600 (Arg0, 0x58, DerefOf (PB60 [0x01]), Buffer (0x01)
                    {
                         0xA5                                             // .
                    })
                M600 (Arg0, 0x59, DerefOf (PB60 [0x02]), Buffer (0x02)
                    {
                         0x21, 0x03                                       // !.
                    })
                M600 (Arg0, 0x5A, DerefOf (PB60 [0x03]), Buffer (0x03)
                    {
                         0x21, 0x03, 0x5A                                 // !.Z
                    })
                M600 (Arg0, 0x5B, DerefOf (PB60 [0x04]), Buffer (0x03)
                    {
                         0x21, 0x03, 0x5A                                 // !.Z
                    })
                M600 (Arg0, 0x5C, DerefOf (PB60 [0x05]), Buffer (0x03)
                    {
                         0x21, 0x03                                       // !.
                    })
                M600 (Arg0, 0x5D, DerefOf (PB60 [0x06]), Buffer (0x03)
                    {
                         0x21, 0x03, 0x00                                 // !..
                    })
                M600 (Arg0, 0x5E, DerefOf (PB60 [0x07]), Buffer (0x04)
                    {
                         0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                    })
                M600 (Arg0, 0x5F, DerefOf (PB60 [0x08]), Buffer (0x05)
                    {
                         0xFE, 0xB3, 0x79, 0xC1, 0xA5                     // ..y..
                    })
                M600 (Arg0, 0x60, DerefOf (PB60 [0x09]), Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                    })
                M600 (Arg0, 0x61, DerefOf (PB60 [0x0A]), Buffer (0x09)
                    {
                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                        /* 0008 */  0xA5                                             // .
                    })
                M600 (Arg0, 0x62, DerefOf (PB60 [0x0B]), Buffer (0x0101)
                    {
                         0x00                                             // .
                    })
                M600 (Arg0, 0x63, DerefOf (PB60 [0x0C]), Buffer (0x43)
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
                M600 (Arg0, 0x64, DerefOf (PB60 [0x0D]), Buffer (0x44)
                    {
                        "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abc"
                    })
                M600 (Arg0, 0x65, DerefOf (PB60 [0x0E]), Buffer (0x01)
                    {
                         0x0B                                             // .
                    })
                M600 (Arg0, 0x66, DerefOf (PB60 [0x0F]), Buffer (0x08)
                    {
                         0x01, 0x89, 0x67, 0x45, 0x23, 0x01, 0x89, 0x37   // ..gE#..7
                    })
                M600 (Arg0, 0x67, DerefOf (PB60 [0x10]), Buffer (0x07)
                    {
                         0x35, 0xEC, 0xE9, 0x2E, 0x16, 0x76, 0x0D         // 5....v.
                    })
                M600 (Arg0, 0x68, DerefOf (PB60 [0x11]), Buffer (0x04)
                    {
                         0x56, 0x34, 0x12, 0x90                           // V4..
                    })
                M600 (Arg0, 0x69, DerefOf (PB60 [0x12]), Buffer (0x04)
                    {
                         0xC0, 0x2C, 0x5F, 0x05                           // .,_.
                    })
                M600 (Arg0, 0x6A, DerefOf (PB60 [0x13]), Buffer (0x01)
                    {
                         0x3F                                             // ?
                    })
            }
            Else
            {
                /* Test Buffers */

                M600 (Arg0, 0x6B, B600, Buffer (0x01)
                    {
                         0x00                                             // .
                    })
                M600 (Arg0, 0x6C, B601, Buffer (0x01)
                    {
                         0xA5                                             // .
                    })
                M600 (Arg0, 0x6D, B602, Buffer (0x02)
                    {
                         0x21, 0x03                                       // !.
                    })
                M600 (Arg0, 0x6E, B603, Buffer (0x03)
                    {
                         0x21, 0x03, 0x5A                                 // !.Z
                    })
                M600 (Arg0, 0x6F, B604, Buffer (0x03)
                    {
                         0x21, 0x03, 0x5A                                 // !.Z
                    })
                M600 (Arg0, 0x70, B605, Buffer (0x03)
                    {
                         0x21, 0x03                                       // !.
                    })
                M600 (Arg0, 0x71, B606, Buffer (0x03)
                    {
                         0x21, 0x03, 0x00                                 // !..
                    })
                M600 (Arg0, 0x72, B607, Buffer (0x04)
                    {
                         0xFE, 0xB3, 0x79, 0xC1                           // ..y.
                    })
                M600 (Arg0, 0x73, B608, Buffer (0x05)
                    {
                         0xFE, 0xB3, 0x79, 0xC1, 0xA5                     // ..y..
                    })
                M600 (Arg0, 0x74, B609, Buffer (0x08)
                    {
                         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
                    })
                M600 (Arg0, 0x75, B60A, Buffer (0x09)
                    {
                        /* 0000 */  0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE,  // ..P...|.
                        /* 0008 */  0xA5                                             // .
                    })
                M600 (Arg0, 0x76, B60B, Buffer (0x0101)
                    {
                         0x00                                             // .
                    })
                M600 (Arg0, 0x77, B60C, Buffer (0x43)
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
                M600 (Arg0, 0x78, B60D, Buffer (0x44)
                    {
                        "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abc"
                    })
                M600 (Arg0, 0x79, B60E, Buffer (0x01)
                    {
                         0x0B                                             // .
                    })
                M600 (Arg0, 0x7A, B60F, Buffer (0x08)
                    {
                         0x01, 0x89, 0x67, 0x45, 0x23, 0x01, 0x89, 0x37   // ..gE#..7
                    })
                M600 (Arg0, 0x7B, B610, Buffer (0x07)
                    {
                         0x35, 0xEC, 0xE9, 0x2E, 0x16, 0x76, 0x0D         // 5....v.
                    })
                M600 (Arg0, 0x7C, B611, Buffer (0x04)
                    {
                         0x56, 0x34, 0x12, 0x90                           // V4..
                    })
                M600 (Arg0, 0x7D, B612, Buffer (0x04)
                    {
                         0xC0, 0x2C, 0x5F, 0x05                           // .,_.
                    })
                M600 (Arg0, 0x7E, B613, Buffer (0x01)
                    {
                         0x3F                                             // ?
                    })
            }
        }
    }

    /* Check consistency of the test Named Objects */
    /* in the root Scope of the Global ACPI namespace */
    Method (M606, 1, NotSerialized)
    {
        M605 (Arg0, 0x01, 0x00)
        M605 (Arg0, 0x01, 0x01)
        M605 (Arg0, 0x02, 0x00)
        M605 (Arg0, 0x02, 0x01)
        M605 (Arg0, 0x03, 0x00)
        M605 (Arg0, 0x03, 0x01)
    }
