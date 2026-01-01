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
     * Check implicit conversion being applied to data images
     */
    Name (Z122, 0x7A)
    /* Flags of types can be used in Index Operator */

    Name (B66F, Buffer (0x12)
    {
        /* 0000 */  0x00, 0x00, 0x01, 0x01, 0x01, 0x00, 0x00, 0x00,  // ........
        /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0010 */  0x00, 0x00                                       // ..
    })
    /* Not invalid types for testing to store in, */
    /* excluded: Field Unit, Op.Region, Thermal Zone, */
    /*           DDB handle, Debug, Reference */
    Name (B670, Buffer (0x12)
    {
        /* 0000 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x00, 0x01, 0x01,  // ........
        /* 0008 */  0x01, 0x01, 0x00, 0x01, 0x01, 0x00, 0x01, 0x00,  // ........
        /* 0010 */  0x00, 0x00                                       // ..
    })
    /* Not invalid types for testing to be stored, */
    /* excluded: Field Unit, Op.Region, Thermal Zone, */
    /*           DDB handle, Debug, Reference */
    Name (B671, Buffer (0x12)
    {
        /* 0000 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x00, 0x01, 0x01,  // ........
        /* 0008 */  0x01, 0x01, 0x00, 0x01, 0x01, 0x00, 0x01, 0x00,  // ........
        /* 0010 */  0x00, 0x00                                       // ..
    })
    /* Flags of types of non-Computational Data Objects */

    Name (B674, Buffer (0x12)
    {
        /* 0000 */  0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x01, 0x01,  // ........
        /* 0008 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x00, 0x01,  // ........
        /* 0010 */  0x01, 0x01                                       // ..
    })
    /* Possible types of the Named Object */

    Name (B676, Buffer (0x12)
    {
        /* 0000 */  0x00, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
        /* 0008 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
        /* 0010 */  0x00, 0x01                                       // ..
    })
    /* Possible types of the LocalX Object */

    Name (B677, Buffer (0x12)
    {
        /* 0000 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x00, 0x01, 0x01,  // ........
        /* 0008 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x00, 0x01,  // ........
        /* 0010 */  0x00, 0x01                                       // ..
    })
    /* Flags of types of Fixed type Data Objects (Fields) */

    Name (B678, Buffer (0x12)
    {
        /* 0000 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00,  // ........
        /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00,  // ........
        /* 0010 */  0x00, 0x00                                       // ..
    })
    /* Flags of types of Computational Data Objects */
    /* (Fields and Integer, String, Buffer) */
    Name (B679, Buffer (0x12)
    {
        /* 0000 */  0x00, 0x01, 0x01, 0x01, 0x00, 0x01, 0x00, 0x00,  // ........
        /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00,  // ........
        /* 0010 */  0x00, 0x00                                       // ..
    })
    /* Type group numbers according with the type of an Object */

    Name (B67A, Buffer (0x12)
    {
        /* 0000 */  0x00, 0x02, 0x02, 0x02, 0x03, 0x01, 0x05, 0x05,  // ........
        /* 0008 */  0x04, 0x05, 0x05, 0x05, 0x05, 0x05, 0x01, 0x00,  // ........
        /* 0010 */  0x00, 0x06                                       // ..
    })
    /* Flags of types not causing exceptions on Increment/Decrement */
    /* (~ Computational Data Objects) */
    Name (B67B, Buffer (0x12)
    {
        /* 0000 */  0x00, 0x01, 0x01, 0x01, 0x00, 0x01, 0x00, 0x00,  // ........
        /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00,  // ........
        /* 0010 */  0x00, 0x00                                       // ..
    })
    /* Flags of types that can be verified only by ObjectType */
    /* (Not Computational Data, Package and Method Objects) */
    Name (B67C, Buffer (0x12)
    {
        /* 0000 */  0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x01,  // ........
        /* 0008 */  0x00, 0x01, 0x01, 0x01, 0x01, 0x01, 0x00, 0x01,  // ........
        /* 0010 */  0x01, 0x01                                       // ..
    })
    /* Possible types of Package Elements */

    Name (B67D, Buffer (0x12)
    {
        /* 0000 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x00, 0x00, 0x00,  // ........
        /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
        /* 0010 */  0x00, 0x01                                       // ..
    })
    /* Not invalid types for Store taking into */
    /* account the ACPICA exresop restriction: */
    /* Needed Integer/Buffer/String/Package/Ref/Ddb */
    Name (B67F, Buffer (0x12)
    {
        /* 0000 */  0x00, 0x01, 0x01, 0x01, 0x01, 0x01, 0x00, 0x00,  // ........
        /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00,  // ........
        /* 0010 */  0x00, 0x01                                       // ..
    })
    /* Testing Destination Named Objects */
    /* Integers */
    Name (I680, 0xA0A1A2A35F5E5D80)
    Name (I681, 0xA0A1A2A35F5E5D81)
    Name (I682, 0xA0A1A2A35F5E5D82)
    Name (I683, 0xA0A1A2A35F5E5D83)
    Name (I684, 0xA0A1A2A35F5E5D84)
    Name (I685, 0xA0A1A2A35F5E5D85)
    Name (I686, 0xA0A1A2A35F5E5D86)
    Name (I687, 0xA0A1A2A35F5E5D87)
    Name (I688, 0xA0A1A2A35F5E5D88)
    Name (I689, 0xA0A1A2A35F5E5D89)
    Name (I68A, 0xA0A1A2A35F5E5D8A)
    Name (I68B, 0xA0A1A2A35F5E5D8B)
    Name (I68C, 0xA0A1A2A35F5E5D8C)
    Name (I68D, 0xA0A1A2A35F5E5D8D)
    Name (I68E, 0xA0A1A2A35F5E5D8E)
    Name (I68F, 0xA0A1A2A35F5E5D8F)
    Name (I690, 0xA0A1A2A35F5E5D90)
    Name (I691, 0xA0A1A2A35F5E5D91)
    Name (I692, 0xA0A1A2A35F5E5D92)
    Name (I693, 0xA0A1A2A35F5E5D93)
    Name (I694, 0xA0A1A2A35F5E5D94)
    Name (I695, 0xA0A1A2A35F5E5D95)
    Name (I696, 0xA0A1A2A35F5E5D96)
    Name (I697, 0xA0A1A2A35F5E5D97)
    Name (I698, 0xA0A1A2A35F5E5D98)
    Name (I699, 0xA0A1A2A35F5E5D99)
    Name (I69A, 0xA0A1A2A35F5E5D9A)
    Name (I69B, 0xA0A1A2A35F5E5D9B)
    Name (I69C, 0xA0A1A2A35F5E5D9C)
    Name (I69D, 0xA0A1A2A35F5E5D9D)
    Name (I69E, 0xA0A1A2A35F5E5D9E)
    Name (I69F, 0xA0A1A2A35F5E5D9F)
    /* Strings */

    Name (S680, "initial named string80")
    Name (S681, "initial named string81")
    Name (S682, "initial named string82")
    Name (S683, "initial named string83")
    Name (S684, "initial named string84")
    Name (S685, "initial named string85")
    Name (S686, "initial named string86")
    Name (S687, "initial named string87")
    Name (S688, "initial named string88")
    Name (S689, "initial named string89")
    Name (S68A, "initial named string8a")
    Name (S68B, "initial named string8b")
    Name (S68C, "initial named string8c")
    Name (S68D, "initial named string8d")
    Name (S68E, "initial named string8e")
    Name (S68F, "initial named string8f")
    Name (S690, "initial named string90")
    Name (S691, "initial named string91")
    Name (S692, "initial named string92")
    Name (S693, "initial named string93")
    Name (S694, "initial named string94")
    Name (S695, "initial named string95")
    Name (S696, "initial named string96")
    Name (S697, "initial named string97")
    Name (S698, "initial named string98")
    Name (S699, "initial named string99")
    Name (S69A, "initial named string9a")
    Name (S69B, "initial named string9b")
    Name (S69C, "initial named string9c")
    Name (S69D, "initial named string9d")
    Name (S69E, "initial named string9e")
    Name (S69F, "initial named string9f")
    /* Buffers */

    Name (B680, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x80                                             // .
    })
    Name (B681, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x81                                             // .
    })
    Name (B682, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x82                                             // .
    })
    Name (B683, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x83                                             // .
    })
    Name (B684, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x84                                             // .
    })
    Name (B685, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x85                                             // .
    })
    Name (B686, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x86                                             // .
    })
    Name (B687, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x87                                             // .
    })
    Name (B688, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x88                                             // .
    })
    Name (B689, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x89                                             // .
    })
    Name (B68A, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x8A                                             // .
    })
    Name (B68B, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x8B                                             // .
    })
    Name (B68C, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x8C                                             // .
    })
    Name (B68D, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x8D                                             // .
    })
    Name (B68E, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x8E                                             // .
    })
    Name (B68F, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x8F                                             // .
    })
    Name (B690, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x90                                             // .
    })
    Name (B691, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x91                                             // .
    })
    Name (B692, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x92                                             // .
    })
    Name (B693, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x93                                             // .
    })
    Name (B694, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x94                                             // .
    })
    Name (B695, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x95                                             // .
    })
    Name (B696, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x96                                             // .
    })
    Name (B697, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x97                                             // .
    })
    Name (B698, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x98                                             // .
    })
    Name (B699, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x99                                             // .
    })
    Name (B69A, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x9A                                             // .
    })
    Name (B69B, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x9B                                             // .
    })
    Name (B69C, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x9C                                             // .
    })
    Name (B69D, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x9D                                             // .
    })
    Name (B69E, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x9E                                             // .
    })
    Name (B69F, Buffer (0x09)
    {
        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
        /* 0008 */  0x9F                                             // .
    })
    /* Packages */

    Name (P680, Package (0x01)
    {
        0x00
    })
    /* Buffer Fields */

    Name (B675, Buffer (0x17){})
    CreateField (B675, 0x00, 0x1F, BF80)
    CreateField (B675, 0x23, 0x3F, BF81)
    CreateField (B675, 0x6E, 0x45, BF82)
    /* Auxiliary Source Named Objects */

    Name (I6E0, 0xFE7CB391D650A284)
    Name (I6E1, 0xFE7CB391D650A284)
    Name (I6E2, 0xFE7CB391D650A284)
    Name (I6E3, 0xFE7CB391D650A284)
    Name (I6E4, 0xFE7CB391D650A284)
    Name (I6E5, 0xFE7CB391D650A284)
    Name (I6E6, 0xFE7CB391D650A284)
    Name (I6E7, 0xFE7CB391D650A284)
    Name (I6E8, 0xFE7CB391D650A284)
    Name (I6E9, 0xFE7CB391D650A284)
    Name (P690, Package (0x12)
    {
        0xFE7CB391D650A284,
        "FE7CB391D650A284",
        Buffer (0x08)
        {
             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
        },

        0xFE7CB391D650A284,
        "FE7CB391D650A284",
        Buffer (0x08)
        {
             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
        },

        0xFE7CB391D650A284,
        "FE7CB391D650A284",
        Buffer (0x08)
        {
             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
        },

        0xFE7CB391D650A284,
        "FE7CB391D650A284",
        Buffer (0x08)
        {
             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
        },

        0xFE7CB391D650A284,
        "FE7CB391D650A284",
        Buffer (0x08)
        {
             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
        },

        0xFE7CB391D650A284,
        "FE7CB391D650A284",
        Buffer (0x08)
        {
             0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
        }
    })
    Name (P691, Package (0x01){})
    Name (S6E0, "FE7CB391D650A284")
    Name (S6E1, "FE7CB391D650A284")
    Name (S6E2, "FE7CB391D650A284")
    Name (S6E3, "FE7CB391D650A284")
    Name (S6E4, "FE7CB391D650A284")
    Name (S6E5, "FE7CB391D650A284")
    Name (S6E6, "FE7CB391D650A284")
    Name (S6E7, "FE7CB391D650A284")
    Name (S6E8, "FE7CB391D650A284")
    Name (S6E9, "FE7CB391D650A284")
    Name (B6E0, Buffer (0x08)
    {
         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
    })
    Name (B6E1, Buffer (0x08)
    {
         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
    })
    Name (B6E2, Buffer (0x08)
    {
         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
    })
    Name (B6E3, Buffer (0x08)
    {
         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
    })
    Name (B6E4, Buffer (0x08)
    {
         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
    })
    Name (B6E5, Buffer (0x08)
    {
         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
    })
    Name (B6E6, Buffer (0x08)
    {
         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
    })
    Name (B6E7, Buffer (0x08)
    {
         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
    })
    Name (B6E8, Buffer (0x08)
    {
         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
    })
    Name (B6E9, Buffer (0x08)
    {
         0x84, 0xA2, 0x50, 0xD6, 0x91, 0xB3, 0x7C, 0xFE   // ..P...|.
    })
    /* Matrixes of exceptions expected during an attempt to make */
    /* a copy of the Result Object by some storing operator, */
    /* a raw relies to the type group of a Target Object, */
    /* a column relies to the type group of a Result Object */
    /* (uninitialized, fixed, other computational data types, */
    /* Package, Method, others, reference) */
    /* Store to Named Object */
    Name (P6A0, Package (0x07)
    {
        Buffer (0x07)
        {
             0x01, 0x00, 0x00, 0x00, 0x01, 0x01, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x01, 0x00, 0x00, 0x01, 0x01, 0x01, 0x01         // .......
        },

        Buffer (0x07)
        {
             0x01, 0x00, 0x00, 0x01, 0x01, 0x01, 0x01         // .......
        },

        Buffer (0x07)
        {
             0x01, 0x01, 0x01, 0x00, 0x01, 0x01, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x01, 0x00, 0x00, 0x00, 0x01, 0x01, 0x00         // .......
        }
    })
    /* Store in other cases and CopyObject */

    Name (P6A1, Package (0x07)
    {
        Buffer (0x07)
        {
             0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x01, 0x00, 0x00, 0x01, 0x01, 0x01, 0x01         // .......
        },

        Buffer (0x07)
        {
             0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00         // .......
        }
    })
    /* Matrixes of saving Target type storings */
    /* (have sense in absence of exceptions) */
    /* Store to Named Object */
    Name (P6A2, Package (0x07)
    {
        Buffer (0x07)
        {
             0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x00, 0x01, 0x01, 0x00, 0x01, 0x00, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x00, 0x01, 0x01, 0x00, 0x01, 0x00, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00         // .......
        }
    })
    /* Store in other cases and CopyObject */

    Name (P6A3, Package (0x07)
    {
        Buffer (0x07)
        {
             0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x00, 0x01, 0x01, 0x00, 0x00, 0x00, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00         // .......
        },

        Buffer (0x07)
        {
             0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00         // .......
        }
    })
    /* Check Result of operation on equal to Benchmark value */
    /* m680(<method name>, */
    /*	<internal type of error if it occurs>, */
    /*	<internal subtype>, */
    /*	<Result>, */
    /*	<Benchmark value>) */
    Method (M680, 5, NotSerialized)
    {
        Local0 = ObjectType (Arg3)
        Local1 = ObjectType (Arg4)
        If ((Local0 != Local1))
        {
            ERR (Concatenate (Arg0, "-OType"), Z122, __LINE__, Arg2, 0x00, Local0, Local1)
            Return (0x01)
        }
        ElseIf (DerefOf (B679 [Local0]))
        {
            If ((Arg3 != Arg4))
            {
                ERR (Arg0, Z122, __LINE__, Arg2, 0x00, Arg3, Arg4)
                Return (0x01)
            }
        }

        Return (0x00)
    }

    /* Return Indexed reference */
    /* m681(<source>, <index>) */
    Method (M681, 2, NotSerialized)
    {
        Return (Arg0 [Arg1])
    }

    /* Return the value of an Auxiliary Source Named Object */
    /* m682(<type>, <index>) */
    Method (M682, 2, Serialized)
    {
        Switch (ToInteger (Arg0))
        {
            Case (0x01)
            {
                Switch (ToInteger (Arg1))
                {
                    Case (0x00)
                    {
                        Return (I6E0) /* \I6E0 */
                    }
                    Case (0x01)
                    {
                        Return (I6E1) /* \I6E1 */
                    }
                    Case (0x02)
                    {
                        Return (I6E2) /* \I6E2 */
                    }
                    Case (0x03)
                    {
                        Return (I6E3) /* \I6E3 */
                    }
                    Case (0x04)
                    {
                        Return (I6E4) /* \I6E4 */
                    }
                    Case (0x05)
                    {
                        Return (I6E5) /* \I6E5 */
                    }
                    Case (0x06)
                    {
                        Return (I6E6) /* \I6E6 */
                    }
                    Case (0x07)
                    {
                        Return (I6E7) /* \I6E7 */
                    }
                    Case (0x08)
                    {
                        Return (I6E8) /* \I6E8 */
                    }
                    Case (0x09)
                    {
                        Return (I6E9) /* \I6E9 */
                    }

                }
            }
            Case (0x02)
            {
                Switch (ToInteger (Arg1))
                {
                    Case (0x00)
                    {
                        Return (S6E0) /* \S6E0 */
                    }
                    Case (0x01)
                    {
                        Return (S6E1) /* \S6E1 */
                    }
                    Case (0x02)
                    {
                        Return (S6E2) /* \S6E2 */
                    }
                    Case (0x03)
                    {
                        Return (S6E3) /* \S6E3 */
                    }
                    Case (0x04)
                    {
                        Return (S6E4) /* \S6E4 */
                    }
                    Case (0x05)
                    {
                        Return (S6E5) /* \S6E5 */
                    }
                    Case (0x06)
                    {
                        Return (S6E6) /* \S6E6 */
                    }
                    Case (0x07)
                    {
                        Return (S6E7) /* \S6E7 */
                    }
                    Case (0x08)
                    {
                        Return (S6E8) /* \S6E8 */
                    }
                    Case (0x09)
                    {
                        Return (S6E9) /* \S6E9 */
                    }

                }
            }
            Case (0x03)
            {
                Switch (ToInteger (Arg1))
                {
                    Case (0x00)
                    {
                        Return (B6E0) /* \B6E0 */
                    }
                    Case (0x01)
                    {
                        Return (B6E1) /* \B6E1 */
                    }
                    Case (0x02)
                    {
                        Return (B6E2) /* \B6E2 */
                    }
                    Case (0x03)
                    {
                        Return (B6E3) /* \B6E3 */
                    }
                    Case (0x04)
                    {
                        Return (B6E4) /* \B6E4 */
                    }
                    Case (0x05)
                    {
                        Return (B6E5) /* \B6E5 */
                    }
                    Case (0x06)
                    {
                        Return (B6E6) /* \B6E6 */
                    }
                    Case (0x07)
                    {
                        Return (B6E7) /* \B6E7 */
                    }
                    Case (0x08)
                    {
                        Return (B6E8) /* \B6E8 */
                    }
                    Case (0x09)
                    {
                        Return (B6E9) /* \B6E9 */
                    }

                }
            }
            Case (0xFF)
            {
                Local0 = 0x00
            }

        }

        Return (Local0)
    }

    /* Initialize the bytes of the buffer in the range of bits */
    /* m683(<buffer>, <bit1>, <length>, <byte>) */
    Method (M683, 4, NotSerialized)
    {
        /* First byte */

        Local1 = (Arg1 / 0x08)
        /*Last byte */

        Local2 = (((Arg1 + Arg2) - 0x01) / 0x08)
        Local0 = ((Local2 + 0x01) - Local1)
        While (Local0)
        {
            Arg0 [Local1] = Arg3
            Local1++
            Local0--
        }
    }

    /* Return the number of the type group */

    Method (M684, 1, NotSerialized)
    {
        Return (DerefOf (B67A [Arg0]))
    }

    /* Return flag of exception on storing */
    /* m685(<opcode>, <target type>, <result type>, */
    /*      <flag of being Named Source>, <flag of being Named Target>) */
    Method (M685, 5, NotSerialized)
    {
        If (Arg0)
        {
            /* CopyObject issue */

            Return (DerefOf (DerefOf (P6A1 [M684 (Arg1)]) [M684 (Arg2)]))
        }
        Else
        {
            /* Store issue */

            If ((Arg3 && (Arg2 == 0x08)))
            {
                /* Store Named of type Method causes invocation of the Method */
                /* which returns a String in the test */
                Arg2 = 0x02
            }

            If (DerefOf (B67F [Arg2]))
            {
                /* Data can be stored */

                If ((Arg4 || DerefOf (B678 [Arg1])))
                {
                    /* Store to Named or to Fixed Type */
                    /* Result Object Conversion issue */
                    Return (DerefOf (DerefOf (P6A0 [M684 (Arg1)]) [M684 (Arg2)]))
                }
                Else
                {
                    Return (0x00)
                }
            }
            Else
            {
                Return (0x01)
            }
        }
    }

    /* Return flag of type saving on storing */
    /* m686(<opcode>, <target type>, <result type>) */
    Method (M686, 3, NotSerialized)
    {
        If (Arg0)
        {
            If ((Arg0 == 0x02))
            {
                /* CopyObject to Named Object issue */

                Return (DerefOf (DerefOf (P6A3 [M684 (Arg1)]) [M684 (Arg2)]))
            }
            Else
            {
                Return (0x00)
            }
        }
        Else
        {
            /* Store to Named Object issue */

            Return (DerefOf (DerefOf (P6A2 [M684 (Arg1)]) [M684 (Arg2)]))
        }
    }

    /* Store the Object by the reference */
    /* m687(<source>, <reference>) */
    Method (M687, 2, NotSerialized)
    {
        Arg1 = Arg0
    }

    /* Gathers simple statistics of Store/CopyObject operators */
    /* m688(<name>) */
    Method (M688, 1, Serialized)
    {
        /* Objects are used as Source */
        /* Integer */
        Name (INT0, 0xFEDCBA9876543210)
        /* String */

        Name (STR0, "source string")
        /* Buffer */

        Name (BUF0, Buffer (0x09)
        {
            /* 0000 */  0x09, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02,  // ........
            /* 0008 */  0x01                                             // .
        })
        /* Base of Buffer Fields */

        Name (BUFZ, Buffer (0x14){})
        /* Package */

        Name (PAC0, Package (0x03)
        {
            0xFEDCBA987654321F,
            "test package",
            Buffer (0x09)
            {
                /* 0000 */  0x13, 0x12, 0x11, 0x10, 0x0F, 0x0E, 0x0D, 0x0C,  // ........
                /* 0008 */  0x0B                                             // .
            }
        })
        If (Y361)
        {
            /* Field Unit */

            Field (OPR0, ByteAcc, NoLock, Preserve)
            {
                FLU0,   69
            }
        }

        /* Device */

        Device (DEV0)
        {
            Name (S000, "DEV0")
        }

        /* Event */

        Event (EVE0)
        /* Method */

        Name (MM00, "ff0X")  /* Value, returned from MMMX */
        Method (MMM0, 0, NotSerialized)
        {
            Return (MM00) /* \M688.MM00 */
        }

        /* Mutex */

        Mutex (MTX0, 0x00)
        If (Y361)
        {
            /* Operation Region */

            OperationRegion (OPR0, SystemMemory, 0x00, 0x14)
        }

        /* Power Resource */

        PowerResource (PWR0, 0x00, 0x0000)
        {
            Name (S000, "PWR0")
        }

        /* Processor */

        Processor (CPU0, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (S000, "CPU0")
        }

        /* Thermal Zone */

        ThermalZone (TZN0)
        {
            Name (S000, "TZN0")
        }

        /* Buffer Field */

        CreateField (BUFZ, 0x00, 0x45, BFL0)
        /* Data to gather statistics */

        Name (STCS, 0x00)
        Name (INDM, 0xFF)
        Name (PAC2, Package (0x01){})
        Name (IND2, 0x00)
        Name (PAC3, Package (0x01){})
        Name (IND3, 0x00)
        /* Update statistics */
        /* m000(<type>, <shift>, <low>, <up>) */
        Method (M000, 4, NotSerialized)
        {
            If ((Arg0 == 0x02))
            {
                If ((IND2 < INDM))
                {
                    Store (((Arg3 * Arg1) + Arg2), PAC2 [IND2])
                    IND2++
                }
            }
            ElseIf ((Arg0 == 0x03))
            {
                If ((IND3 < INDM))
                {
                    Store (((Arg3 * Arg1) + Arg2), PAC3 [IND3])
                    IND3++
                }
            }
        }

        /* Initialize statistics */

        Method (M001, 0, NotSerialized)
        {
            If (STCS)
            {
                PAC2 = Package (0xFF){}
                IND2 = 0x00
                PAC3 = Package (0xFF){}
                IND3 = 0x00
            }
        }

        /* Output statistics */

        Method (M002, 1, Serialized)
        {
            Name (LPN0, 0x00)
            Name (LPC0, 0x00)
            If (STCS)
            {
                Debug = Arg0
                If (IND2)
                {
                    Debug = "Run-time exceptions:"
                    Debug = IND2 /* \M688.IND2 */
                    Debug = "Types:"
                    LPN0 = IND2 /* \M688.IND2 */
                    LPC0 = 0x00
                    While (LPN0)
                    {
                        Debug = DerefOf (PAC2 [LPC0])
                        LPN0--
                        LPC0++
                    }
                }

                If (IND3)
                {
                    Debug = "Type mismatch:"
                    Debug = IND3 /* \M688.IND3 */
                    LPN0 = IND3 /* \M688.IND3 */
                    LPC0 = 0x00
                    While (LPN0)
                    {
                        Debug = DerefOf (PAC3 [LPC0])
                        LPN0--
                        LPC0++
                    }
                }
            }
        }

        /* Check exceptions */

        Method (M003, 1, NotSerialized)
        {
            If (CH03 (Arg0, Z122, __LINE__, 0x00, 0x00))
            {
                If (STCS)
                {
                    If ((IND2 < INDM))
                    {
                        PAC2 [IND2] = Arg0
                        IND2++
                    }
                }
            }
        }

        /* Check equality */

        Method (M004, 3, NotSerialized)
        {
            If ((Arg0 != Arg1))
            {
                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Arg0, Arg1)
                If (STCS)
                {
                    M000 (0x03, 0x0100, Arg2, Arg1)
                }
            }
        }

        /* Gathers statistics of Store to Local */

        Method (M010, 2, NotSerialized)
        {
            /* Initialize statistics */

            M001 ()
            If (Arg1)
            {
                Local1 = 0x00
            }

            Local0 = Local1
            M003 (ObjectType (Local1))
            Local0 = INT0 /* \M688.INT0 */
            M003 (ObjectType (INT0))
            Local0 = STR0 /* \M688.STR0 */
            M003 (ObjectType (STR0))
            Local0 = BUF0 /* \M688.BUF0 */
            M003 (ObjectType (BUF0))
            Local0 = PAC0 /* \M688.PAC0 */
            M003 (ObjectType (PAC0))
            Local0 = FLU0 /* \M688.FLU0 */
            M003 (ObjectType (FLU0))
            /*
             // Removed 09/2015: iASL now disallows stores to these objects
             Store(DEV0, Local0)
             m003(ObjectType(DEV0))
             Store(EVE0, Local0)
             m003(ObjectType(EVE0))
             Store(MTX0, Local0)
             m003(ObjectType(MTX0))
             Store(OPR0, Local0)
             m003(ObjectType(OPR0))
             Store(PWR0, Local0)
             m003(ObjectType(PWR0))
             Store(CPU0, Local0)
             m003(ObjectType(CPU0))
             Store(TZN0, Local0)
             m003(ObjectType(TZN0))
             */
            Local0 = BFL0 /* \M688.BFL0 */
            M003 (ObjectType (BFL0))
            /* Output statistics */

            M002 ("Store to LocalX")
        }

        /* Gathers statistics of CopyObject to Local */

        Method (M011, 2, NotSerialized)
        {
            /* Initialize statistics */

            M001 ()
            If (Arg1)
            {
                Local1 = 0x00
            }

            CopyObject (Local1, Local0)
            M003 (ObjectType (Local1))
            CopyObject (INT0, Local0)
            M003 (ObjectType (INT0))
            CopyObject (STR0, Local0)
            M003 (ObjectType (STR0))
            CopyObject (BUF0, Local0)
            M003 (ObjectType (BUF0))
            CopyObject (PAC0, Local0)
            M003 (ObjectType (PAC0))
            CopyObject (FLU0, Local0)
            M003 (ObjectType (FLU0))
            CopyObject (DEV0, Local0)
            M003 (ObjectType (DEV0))
            CopyObject (EVE0, Local0)
            M003 (ObjectType (EVE0))
            CopyObject (MMM0 (), Local0)
            M003 (ObjectType (MMM0))
            CopyObject (MTX0, Local0)
            M003 (ObjectType (MTX0))
            CopyObject (OPR0, Local0)
            M003 (ObjectType (OPR0))
            CopyObject (PWR0, Local0)
            M003 (ObjectType (PWR0))
            CopyObject (CPU0, Local0)
            M003 (ObjectType (CPU0))
            CopyObject (TZN0, Local0)
            M003 (ObjectType (TZN0))
            CopyObject (BFL0, Local0)
            M003 (ObjectType (BFL0))
            /* Output statistics */

            M002 ("CopyObject to LocalX")
        }

        /* Gathers statistics of CopyObject to Integer */

        Method (M012, 2, Serialized)
        {
            /* Integer */

            Name (INT1, 0xFEDCBA9876543211)
            Name (INT2, 0xFEDCBA9876543212)
            Name (INT3, 0xFEDCBA9876543213)
            Name (INT4, 0xFEDCBA9876543214)
            Name (INT5, 0xFEDCBA9876543215)
            Name (INT6, 0xFEDCBA9876543216)
            Name (INT7, 0xFEDCBA9876543217)
            Name (INT8, 0xFEDCBA9876543218)
            Name (INT9, 0xFEDCBA9876543219)
            Name (INTA, 0xFEDCBA987654321A)
            Name (INTB, 0xFEDCBA987654321B)
            Name (INTC, 0xFEDCBA987654321C)
            Name (INTD, 0xFEDCBA987654321D)
            Name (INTE, 0xFEDCBA987654321E)
            Name (INTF, 0xFEDCBA987654321F)
            /* Initialize statistics */

            M001 ()
            If (Arg1)
            {
                Local1 = 0x00
            }

            CopyObject (Local1, INTF) /* \M688.M012.INTF */
            M003 (ObjectType (Local1))
            M004 (Arg0, ObjectType (INTF), 0x00)
            CopyObject (INT0, INT1) /* \M688.M012.INT1 */
            M003 (ObjectType (INT0))
            M004 (Arg0, ObjectType (INT1), 0x01)
            CopyObject (STR0, INT2) /* \M688.M012.INT2 */
            M003 (ObjectType (STR0))
            M004 (Arg0, ObjectType (INT2), 0x02)
            CopyObject (BUF0, INT3) /* \M688.M012.INT3 */
            M003 (ObjectType (BUF0))
            M004 (Arg0, ObjectType (INT3), 0x03)
            CopyObject (PAC0, INT4) /* \M688.M012.INT4 */
            M003 (ObjectType (PAC0))
            M004 (Arg0, ObjectType (INT4), 0x04)
            CopyObject (FLU0, INT5) /* \M688.M012.INT5 */
            M003 (ObjectType (FLU0))
            M004 (Arg0, ObjectType (INT5), 0x05)
            CopyObject (DEV0, INT6) /* \M688.M012.INT6 */
            M003 (ObjectType (DEV0))
            M004 (Arg0, ObjectType (INT6), 0x06)
            CopyObject (EVE0, INT7) /* \M688.M012.INT7 */
            M003 (ObjectType (EVE0))
            M004 (Arg0, ObjectType (INT7), 0x07)
            CopyObject (MMM0 (), INT8) /* \M688.M012.INT8 */
            M003 (ObjectType (MMM0))
            M004 (Arg0, ObjectType (INT8), 0x08)
            CopyObject (MTX0, INT9) /* \M688.M012.INT9 */
            M003 (ObjectType (MTX0))
            M004 (Arg0, ObjectType (INT9), 0x09)
            CopyObject (OPR0, INTA) /* \M688.M012.INTA */
            M003 (ObjectType (OPR0))
            M004 (Arg0, ObjectType (INTA), 0x0A)
            CopyObject (PWR0, INTB) /* \M688.M012.INTB */
            M003 (ObjectType (PWR0))
            M004 (Arg0, ObjectType (INTB), 0x0B)
            CopyObject (CPU0, INTC) /* \M688.M012.INTC */
            M003 (ObjectType (CPU0))
            M004 (Arg0, ObjectType (INTC), 0x0C)
            CopyObject (TZN0, INTD) /* \M688.M012.INTD */
            M003 (ObjectType (TZN0))
            M004 (Arg0, ObjectType (INTD), 0x0D)
            CopyObject (BFL0, INTE) /* \M688.M012.INTE */
            M003 (ObjectType (BFL0))
            M004 (Arg0, ObjectType (INTE), 0x0E)
            /* Output statistics */

            M002 ("CopyObject to Integer Named Object")
        }

        M010 (Concatenate (Arg0, "-m010"), 0x00)
        M011 (Concatenate (Arg0, "-m011"), 0x00)
        M012 (Concatenate (Arg0, "-m012"), 0x00)
    }

    /* Verify storing of an immediate Source Object into different kinds */
    /* of Target Objects by means of the specified operator (Store/CopyObject) */
    /* m689(<name>, <store op>, <exc. conditions>) */
    Method (M689, 3, Serialized)
    {
        /* Object-initializers are used either with Source or Target */
        /* (names ended by 0 and 1 respectively) */
        /* Integer */
        Name (INT0, 0xFEDCBA9876543210)
        Name (INT1, 0xFEDCBA9876543211)
        /* String */

        Name (STR0, "source string")
        Name (STR1, "target string")
        /* Buffer */

        Name (BUF0, Buffer (0x09)
        {
            /* 0000 */  0x09, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02,  // ........
            /* 0008 */  0x01                                             // .
        })
        Name (BUF1, Buffer (0x11)
        {
             0xC3                                             // .
        })
        /* Initializer of Fields */

        Name (BUF2, Buffer (0x09)
        {
            /* 0000 */  0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25,  // ..ueUE5%
            /* 0008 */  0x15                                             // .
        })
        /* Base of Buffer Fields */

        Name (BUFZ, Buffer (0x30){})
        /* Package */

        Name (PAC0, Package (0x03)
        {
            0xFEDCBA987654321F,
            "test package",
            Buffer (0x09)
            {
                /* 0000 */  0x13, 0x12, 0x11, 0x10, 0x0F, 0x0E, 0x0D, 0x0C,  // ........
                /* 0008 */  0x0B                                             // .
            }
        })
        Name (PAC1, Package (0x01)
        {
            "target package"
        })
        If (Y361)
        {
            /* Field Unit */

            Field (OPR0, ByteAcc, NoLock, Preserve)
            {
                FLU0,   69,
                FLU2,   64,
                FLU4,   32
            }
        }

        /* Device */

        Device (DEV0)
        {
            Name (S000, "DEV0")
        }

        Device (DEV1)
        {
            Name (S000, "DEV1")
        }

        /* Event */

        Event (EVE0)
        Event (EVE1)
        /* Method */

        Name (MM00, "ff0X")  /* Value, returned from MMMX */
        Name (MM01, "ff1Y")  /* Value, returned from MMMY */
        Name (MMM0, 0x00)   /* Method as Source Object */
        Name (MMM1, 0x00)   /* Method as Target Object */
        Method (MMMX, 0, NotSerialized)
        {
            Return (MM00) /* \M689.MM00 */
        }

        Method (MMMY, 0, NotSerialized)
        {
            Return (MM01) /* \M689.MM01 */
        }

        /* Mutex */

        Mutex (MTX0, 0x00)
        Mutex (MTX1, 0x00)
        If (Y361)
        {
            /* Operation Region */

            OperationRegion (OPR0, SystemMemory, 0x00, 0x30)
            OperationRegion (OPR1, SystemMemory, 0x00, 0x18)
        }

        /* Power Resource */

        PowerResource (PWR0, 0x00, 0x0000)
        {
            Name (S000, "PWR0")
        }

        PowerResource (PWR1, 0x00, 0x0000)
        {
            Name (S000, "PWR1")
        }

        /* Processor */

        Processor (CPU0, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (S000, "CPU0")
        }

        Processor (CPU1, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (S000, "CPU1")
        }

        /* Thermal Zone */

        ThermalZone (TZN0)
        {
            Name (S000, "TZN0")
        }

        ThermalZone (TZN1)
        {
            Name (S000, "TZN1")
        }

        /* Buffer Field */

        CreateField (BUFZ, 0x00, 0x45, BFL0)
        CreateField (BUFZ, 0x50, 0x40, BFL2)
        CreateField (BUFZ, 0xA0, 0x20, BFL4)
        /* Reference */

        Name (ORF0, "ORF0")
        Name (REF0, Package (0x01){})
        Name (ORF1, "ORF0")
        Name (REF1, Package (0x01){})
        /* Data to gather statistics */

        Name (STCS, 0x00)
        Name (INDM, 0xFF)
        Name (PAC2, Package (0x01){})
        Name (IND2, 0x00)
        Name (PAC3, Package (0x01){})
        Name (IND3, 0x00)
        Name (PAC4, Package (0x02)
        {
            "Store",
            "Copyobject"
        })
        Name (PAC5, Package (0x07)
        {
            "Storing Named-Named with ",
            "Storing Named-LocalX with ",
            "Storing LocalX-Named with ",
            "Storing LocalX-LocalX with ",
            "Storing Named-ArgX(Named on read-only argument rule) with ",
            "Storing Named-ArgX(Named by reference) with ",
            "Storing LocalX-Element of Package with "
        })
        Name (TERR, "-test error")
        /* Update statistics */
        /* m000(<type>, <shift>, <low>, <up>) */
        Method (M000, 4, NotSerialized)
        {
            If ((Arg0 == 0x02))
            {
                If ((IND2 < INDM))
                {
                    Store (((Arg3 * Arg1) + Arg2), PAC2 [IND2])
                    IND2++
                }
            }
            ElseIf ((Arg0 == 0x03))
            {
                If ((IND3 < INDM))
                {
                    Store (((Arg3 * Arg1) + Arg2), PAC3 [IND3])
                    IND3++
                }
            }
        }

        /* Initialize statistics */

        Method (M001, 0, NotSerialized)
        {
            If (STCS)
            {
                PAC2 = Package (INDM){}
                IND2 = 0x00
                PAC3 = Package (INDM){}
                IND3 = 0x00
            }
        }

        /* Output statistics */

        Method (M002, 1, Serialized)
        {
            Name (LPN0, 0x00)
            Name (LPC0, 0x00)
            If (STCS)
            {
                Debug = Arg0
                If (IND2)
                {
                    Debug = "Run-time exceptions:"
                    Debug = IND2 /* \M689.IND2 */
                    Debug = "Types:"
                    LPN0 = IND2 /* \M689.IND2 */
                    LPC0 = 0x00
                    While (LPN0)
                    {
                        Debug = DerefOf (PAC2 [LPC0])
                        LPN0--
                        LPC0++
                    }
                }

                If (IND3)
                {
                    Debug = "Type mismatch:"
                    Debug = IND3 /* \M689.IND3 */
                    LPN0 = IND3 /* \M689.IND3 */
                    LPC0 = 0x00
                    While (LPN0)
                    {
                        Debug = DerefOf (PAC3 [LPC0])
                        LPN0--
                        LPC0++
                    }
                }
            }
        }

        /* Prepare Target of specified type */

        Method (M003, 4, Serialized)
        {
            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                                /* Only check */
                }
                Case (0x01)
                {
                    CopyObject (DerefOf (Arg3), INT1) /* \M689.INT1 */
                    CopyObject (INT1, Arg2)
                }
                Case (0x02)
                {
                    CopyObject (DerefOf (Arg3), STR1) /* \M689.STR1 */
                    CopyObject (STR1, Arg2)
                }
                Case (0x03)
                {
                    If (Y136)
                    {
                        CopyObject (DerefOf (Arg3), BUF1) /* \M689.BUF1 */
                    }
                    Else
                    {
                        M687 (DerefOf (Arg3), RefOf (BUF1))
                    }

                    CopyObject (BUF1, Arg2)
                }
                Case (0x04)
                {
                    CopyObject (DerefOf (Arg3), PAC1) /* \M689.PAC1 */
                    CopyObject (PAC1, Arg2)
                }
                Case (0x05)
                {
                                /* Check only */
                }
                Case (0x06)
                {
                    CopyObject (DEV1, Arg2)
                }
                Case (0x07)
                {
                    CopyObject (EVE1, Arg2)
                }
                Case (0x08)
                {
                    CopyObject (DerefOf (DerefOf (Arg3) [0x00]), MMM1) /* \M689.MMM1 */
                    CopyObject (DerefOf (DerefOf (Arg3) [0x01]), MM01) /* \M689.MM01 */
                    CopyObject (DerefOf (RefOf (MMM1)), Arg2)
                }
                Case (0x09)
                {
                    CopyObject (MTX1, Arg2)
                }
                Case (0x0A)
                {
                    CopyObject (OPR1, Arg2)
                }
                Case (0x0B)
                {
                    CopyObject (PWR1, Arg2)
                }
                Case (0x0C)
                {
                    CopyObject (CPU1, Arg2)
                }
                Case (0x0D)
                {
                    CopyObject (TZN1, Arg2)
                }
                Case (0x0E)
                {
                                /* Check only */
                }
                Case (0x11)
                {
                    CopyObject (RefOf (ORF1), REF1) /* \M689.REF1 */
                    /*if (y522) { */

                    CopyObject (REF1, Arg2)
                                /*} else { */
                /*	CopyObject(DeRefof(REF1), arg2) */
                /*} */
                }
                /* Unexpected Target Type */

                Default
                {
                    ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg1, 0x00)
                    Return (0x01)
                }

            }

            If (CH03 (Arg0, Z122, __LINE__, 0x00, 0x00))
            {
                /*Exception during preparing of Target Object */

                Return (0x01)
            }

            If ((Arg1 == 0x11))
            {
                /* Reference */

                Return (0x00)
            }

            Local0 = ObjectType (Arg2)
            If ((Local0 != Arg1))
            {
                /* ObjectType of Target can not be set up */

                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Local0, Arg1)
                Return (0x01)
            }

            Return (0x00)
        }

        /* Prepare Source of specified type */

        Method (M004, 4, Serialized)
        {
            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                }
                Case (0x01)
                {
                    CopyObject (DerefOf (Arg3), INT0) /* \M689.INT0 */
                    CopyObject (INT0, Arg2)
                }
                Case (0x02)
                {
                    CopyObject (DerefOf (Arg3), STR0) /* \M689.STR0 */
                    CopyObject (STR0, Arg2)
                }
                Case (0x03)
                {
                    If (Y136)
                    {
                        CopyObject (DerefOf (Arg3), BUF0) /* \M689.BUF0 */
                    }
                    Else
                    {
                        M687 (DerefOf (Arg3), RefOf (BUF0))
                    }

                    CopyObject (BUF0, Arg2)
                }
                Case (0x04)
                {
                    CopyObject (DerefOf (Arg3), PAC0) /* \M689.PAC0 */
                    CopyObject (PAC0, Arg2)
                }
                Case (0x05)
                {
                    Local0 = DerefOf (DerefOf (Arg3) [0x00])
                    If ((Local0 == 0x00))
                    {
                        FLU0 = DerefOf (DerefOf (Arg3) [0x01])
                    }
                    ElseIf ((Local0 == 0x01))
                    {
                        FLU2 = DerefOf (DerefOf (Arg3) [0x01])
                    }
                    Else
                    {
                        FLU4 = DerefOf (DerefOf (Arg3) [0x01])
                    }
                }
                Case (0x06)
                {
                    CopyObject (DEV0, Arg2)
                }
                Case (0x07)
                {
                    CopyObject (EVE0, Arg2)
                }
                Case (0x08)
                {
                    CopyObject (DerefOf (DerefOf (Arg3) [0x00]), MMM0) /* \M689.MMM0 */
                    CopyObject (DerefOf (DerefOf (Arg3) [0x01]), MM00) /* \M689.MM00 */
                    CopyObject (DerefOf (RefOf (MMM0)), Arg2)
                }
                Case (0x09)
                {
                    CopyObject (MTX0, Arg2)
                }
                Case (0x0A)
                {
                    CopyObject (OPR0, Arg2)
                }
                Case (0x0B)
                {
                    CopyObject (PWR0, Arg2)
                }
                Case (0x0C)
                {
                    CopyObject (CPU0, Arg2)
                }
                Case (0x0D)
                {
                    CopyObject (TZN0, Arg2)
                }
                Case (0x0E)
                {
                    Local0 = DerefOf (DerefOf (Arg3) [0x00])
                    If ((Local0 == 0x00))
                    {
                        BFL0 = DerefOf (DerefOf (Arg3) [0x01])
                    }
                    ElseIf ((Local0 == 0x01))
                    {
                        BFL2 = DerefOf (DerefOf (Arg3) [0x01])
                    }
                    Else
                    {
                        BFL4 = DerefOf (DerefOf (Arg3) [0x01])
                    }
                }
                Case (0x11)
                {
                    CopyObject (RefOf (ORF0), REF0) /* \M689.REF0 */
                    /*if (y522) { */

                    CopyObject (REF0, Arg2)
                                /*} else { */
                /*	CopyObject(DeRefof(REF0), arg2) */
                /*} */
                }
                /* Unexpected Source Type */

                Default
                {
                    ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg1, 0x00)
                    Return (0x01)
                }

            }

            If (CH03 (Arg0, Z122, __LINE__, 0x00, 0x00))
            {
                /* Exception during preparing of Source Object */

                Return (0x01)
            }

            If ((Arg1 == 0x11))
            {
                /* Reference */

                Return (0x00)
            }

            Local0 = ObjectType (Arg2)
            If ((Local0 != Arg1))
            {
                /* ObjectType of Source can not be set up */

                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Local0, Arg1)
                Return (0x01)
            }

            Return (0x00)
        }

        /* Check Source Object type is not corrupted after storing, */
        /* for the computational data types verify its value against */
        /* the Object-initializer value */
        Method (M005, 4, Serialized)
        {
            Name (MMM2, 0x00) /* An auxiliary Object to invoke Method */
            If ((Arg1 == 0x11))
            {
                /* Source object is a reference */
                /* Check that it can be used as reference */
                Local0 = DerefOf (Arg2)
                Local3 = DerefOf (Local0)
                If (CH03 (Arg0, Z122, __LINE__, 0x00, Local0))
                {
                    /* Derefof caused unexpected exception */

                    Return (0x01)
                }

                Return (0x00)
            }

            Local0 = ObjectType (Arg2)
            If ((Local0 != Arg1))
            {
                /* ObjectType of Source object is corrupted */

                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Local0, Arg1)
                Return (0x01)
            }

            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    Return (0x00)
                }
                Case (0x01)
                {
                    Local0 = ObjectType (INT0)
                }
                Case (0x02)
                {
                    Local0 = ObjectType (STR0)
                }
                Case (0x03)
                {
                    Local0 = ObjectType (BUF0)
                }
                Case (0x04)
                {
                    Local0 = ObjectType (PAC0)
                }
                Case (0x05)
                {
                    Local0 = DerefOf (DerefOf (Arg3) [0x00])
                    If ((Local0 == 0x00))
                    {
                        Local0 = ObjectType (FLU0)
                    }
                    ElseIf ((Local0 == 0x01))
                    {
                        Local0 = ObjectType (FLU2)
                    }
                    Else
                    {
                        Local0 = ObjectType (FLU4)
                    }
                }
                Case (0x06)
                {
                    Local0 = ObjectType (DEV0)
                }
                Case (0x07)
                {
                    Local0 = ObjectType (EVE0)
                }
                Case (0x08)
                {
                    Local0 = ObjectType (MMM0)
                }
                Case (0x09)
                {
                    Local0 = ObjectType (MTX0)
                }
                Case (0x0A)
                {
                    Local0 = ObjectType (OPR0)
                }
                Case (0x0B)
                {
                    Local0 = ObjectType (PWR0)
                }
                Case (0x0C)
                {
                    Local0 = ObjectType (CPU0)
                }
                Case (0x0D)
                {
                    Local0 = ObjectType (TZN0)
                }
                Case (0x0E)
                {
                    Local0 = DerefOf (DerefOf (Arg3) [0x00])
                    If ((Local0 == 0x00))
                    {
                        Local0 = ObjectType (BFL0)
                    }
                    ElseIf ((Local0 == 0x01))
                    {
                        Local0 = ObjectType (BFL2)
                    }
                    Else
                    {
                        Local0 = ObjectType (BFL4)
                    }
                }
                /* Unexpected Result Type */

                Default
                {
                    ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Arg1, 0x00)
                    Return (0x01)
                }

            }

            If ((Local0 != Arg1))
            {
                /* Mismatch of Source Type against specified Result Type */

                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Local0, Arg1)
                If (STCS)
                {
                    M000 (0x03, 0x01000000, Local0, Arg1)
                }

                Return (0x01)
            }
            Else
            {
                /* Check equality of the Source value to the Object-initializer one */

                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        If ((INT0 != DerefOf (Arg3)))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, INT0, DerefOf (Arg3))
                            Return (0x01)
                        }

                        If ((DerefOf (Arg2) != INT0))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (Arg2), INT0)
                            Return (0x01)
                        }
                    }
                    Case (0x02)
                    {
                        If ((STR0 != DerefOf (Arg3)))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, STR0, DerefOf (Arg3))
                            Return (0x01)
                        }

                        If ((DerefOf (Arg2) != STR0))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (Arg2), STR0)
                            Return (0x01)
                        }
                    }
                    Case (0x03)
                    {
                        If ((BUF0 != DerefOf (Arg3)))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, BUF0, DerefOf (Arg3))
                            Return (0x01)
                        }

                        If ((DerefOf (Arg2) != BUF0))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (Arg2), BUF0)
                            Return (0x01)
                        }
                    }
                    Case (0x04)
                    {
                        Local0 = SizeOf (PAC0)
                        If ((SizeOf (Arg3) != Local0))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, SizeOf (Arg3), Local0)
                            Return (0x01)
                        }

                        While (Local0)
                        {
                            Local0--
                            Local1 = ObjectType (DerefOf (DerefOf (Arg3) [Local0]))
                            Local2 = ObjectType (DerefOf (PAC0 [Local0]))
                            If ((Local1 != Local2))
                            {
                                /* ObjectType is corrupted */

                                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Local1, Local2)
                                Return (0x01)
                            }
                            ElseIf (DerefOf (B679 [Local1]))
                            {
                                /* the computational data type */

                                If ((DerefOf (DerefOf (Arg3) [Local0]) != DerefOf (PAC0 [
                                    Local0])))
                                {
                                    /* The value is corrupted */

                                    ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (DerefOf (Arg3) [Local0]),
                                        Local0)
                                    Return (0x01)
                                }
                            }
                        }

                        Local0 = SizeOf (PAC0)
                        If ((SizeOf (Arg2) != Local0))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, SizeOf (Arg2), Local0)
                            Return (0x01)
                        }

                        While (Local0)
                        {
                            Local0--
                            Local1 = ObjectType (DerefOf (DerefOf (Arg2) [Local0]))
                            Local2 = ObjectType (DerefOf (PAC0 [Local0]))
                            If ((Local1 != Local2))
                            {
                                /* ObjectType is corrupted */

                                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Local1, Local2)
                                Return (0x01)
                            }
                            ElseIf (DerefOf (B679 [Local1]))
                            {
                                /* the computational data type */

                                If ((DerefOf (DerefOf (Arg2) [Local0]) != DerefOf (PAC0 [
                                    Local0])))
                                {
                                    /* The value is corrupted */

                                    ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (DerefOf (Arg2) [Local0]),
                                        Local0)
                                    Return (0x01)
                                }
                            }
                        }
                    }
                    Case (0x05)
                    {
                        Local0 = DerefOf (DerefOf (Arg3) [0x00])
                        If ((Local0 == 0x00))
                        {
                            If ((FLU0 != DerefOf (DerefOf (Arg3) [0x01])))
                            {
                                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, FLU0, DerefOf (DerefOf (Arg3) [0x01]
                                    ))
                                Return (0x01)
                            }

                            If ((DerefOf (Arg2) != FLU0))
                            {
                                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (Arg2), FLU0)
                                Return (0x01)
                            }
                        }
                        ElseIf ((Local0 == 0x01))
                        {
                            If ((FLU2 != DerefOf (DerefOf (Arg3) [0x01])))
                            {
                                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, FLU2, DerefOf (DerefOf (Arg3) [0x01]
                                    ))
                                Return (0x01)
                            }

                            If ((DerefOf (Arg2) != FLU2))
                            {
                                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (Arg2), FLU2)
                                Return (0x01)
                            }
                        }
                        Else
                        {
                            If ((FLU4 != DerefOf (DerefOf (Arg3) [0x01])))
                            {
                                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, FLU4, DerefOf (DerefOf (Arg3) [0x01]
                                    ))
                                Return (0x01)
                            }

                            If ((DerefOf (Arg2) != FLU4))
                            {
                                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (Arg2), FLU4)
                                Return (0x01)
                            }
                        }
                    }
                    Case (0x08)
                    {
                        CopyObject (DerefOf (Arg2), MMM2) /* \M689.M005.MMM2 */
                        If ((MMM2 != MMM0))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, MMM2, MMM0)
                            Return (0x01)
                        }
                    }
                    Case (0x0E)
                    {
                        Local0 = DerefOf (DerefOf (Arg3) [0x00])
                        If ((Local0 == 0x00))
                        {
                            If ((BFL0 != DerefOf (DerefOf (Arg3) [0x01])))
                            {
                                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, BFL0, DerefOf (DerefOf (Arg3) [0x01]
                                    ))
                                Return (0x01)
                            }

                            If ((DerefOf (Arg2) != BFL0))
                            {
                                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (Arg2), BFL0)
                                Return (0x01)
                            }
                        }
                        ElseIf ((Local0 == 0x01))
                        {
                            If ((BFL2 != DerefOf (DerefOf (Arg3) [0x01])))
                            {
                                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, BFL2, DerefOf (DerefOf (Arg3) [0x01]
                                    ))
                                Return (0x01)
                            }

                            If ((DerefOf (Arg2) != BFL2))
                            {
                                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (Arg2), BFL2)
                                Return (0x01)
                            }
                        }
                        Else
                        {
                            If ((BFL4 != DerefOf (DerefOf (Arg3) [0x01])))
                            {
                                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, BFL4, DerefOf (DerefOf (Arg3) [0x01]
                                    ))
                                Return (0x01)
                            }

                            If ((DerefOf (Arg2) != BFL4))
                            {
                                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (Arg2), BFL4)
                                Return (0x01)
                            }
                        }
                    }

                }
            }

            Return (0x00)
        }

        /* Check Target Object to have the expected type and value */
        /* m006(<msg>, <ref to target>, <target type>, <result object type>, */
        /*      <op>, <target save type>, <test data package>) */
        Method (M006, 7, Serialized)
        {
            Name (MMM2, 0x00) /* An auxiliary Object to invoke Method */
            Local2 = ObjectType (Arg1)
            If ((Local2 != Arg2))
            {
                If (STCS)
                {
                    M000 (0x03, 0x00010000, Arg2, Local2)
                }
            }

            If (M686 (Arg5, Arg2, Arg3))
            {
                /* Target must save type */

                If ((Local2 != Arg2))
                {
                    /* Types mismatch Target/Target on storing */

                    If ((Arg2 == C016))
                    {
                        If (X170){                        /*this sentence is for m00d and invalid, removed. */
                        /*err(arg0, z122, __LINE__, 0, 0, Local2, arg2) */
                        }
                    }
                    Else
                    {
                        ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Local2, Arg2)
                    }

                    If (STCS)
                    {
                        M000 (0x03, 0x0100, Arg2, Local2)
                    }

                    Return (0x01)
                }
            }
            ElseIf            /* Target if it is not of fixed type */
            /* must accept type of the Result Object */
 ((Local2 != Arg3))
            {
                If ((M684 (Arg3) == 0x06))
                {
                    /* Result object is a reference */
                    /* Check that Target can be used as reference */
                    Local0 = DerefOf (Arg1)
                    Local3 = DerefOf (Local0)
                    If (CH03 (Arg0, Z122, __LINE__, 0x00, Arg3))
                    {
                        /* Derefof caused unexpected exception */

                        Return (0x01)
                    }
                }
                ElseIf ((M684 (Arg3) != 0x01))
                {
                    /* Types mismatch Result/Target on storing */

                    ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Local2, Arg3)
                    Return (0x01)
                }
                ElseIf ((Local2 != 0x03))
                {
                    /* Types mismatch Result/Target on storing */
                    /* Test fixed type Objects are converted to Buffer */
                    ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Local2, 0x03)
                    Return (0x01)
                }

                If (STCS)
                {
                    M000 (0x03, 0x0100, Arg3, Local2)
                }
            }

            /* Retrieve the benchmark value */

            If (M686 (Arg5, Arg2, Arg3))
            {
                /* Save type of Target */

                If (DerefOf (B67C [Arg2]))
                {
                    /* Types that can be verified only by ObjectType */

                    Return (0x00)
                }

                /* Retrieve the benchmark value */

                Local7 = DerefOf (DerefOf (Arg6 [0x05]) [Arg2])
            }
            Else
            {
                /* Accept type of Result */

                If (DerefOf (B67C [Arg3]))
                {
                    /* Types that can be verified only by ObjectType */

                    Return (0x00)
                }

                Local7 = DerefOf (Arg6 [0x04])
            }

            If ((Arg3 == 0x08))
            {
                /* Method */

                CopyObject (DerefOf (Arg1), MMM2) /* \M689.M006.MMM2 */
                If ((MMM2 != Local7))
                {
                    ERR (Arg0, Z122, __LINE__, 0x00, 0x00, MMM2, Local7)
                    Return (0x01)
                }
            }
            ElseIf ((Arg3 != 0x04))
            {
                /* Not Package */

                If ((DerefOf (Arg1) != Local7))
                {
                    ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (Arg1), Local7)
                    Return (0x01)
                }
            }
            Else
            {
                /* Package */

                Local0 = SizeOf (Local7)
                If ((SizeOf (Arg1) != Local0))
                {
                    ERR (Arg0, Z122, __LINE__, 0x00, 0x00, SizeOf (Arg1), Local0)
                    Return (0x01)
                }

                While (Local0)
                {
                    Local0--
                    Local1 = ObjectType (DerefOf (DerefOf (Arg1) [Local0]))
                    Local2 = ObjectType (DerefOf (Local7 [Local0]))
                    If ((Local1 != Local2))
                    {
                        /* ObjectType is corrupted */

                        ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Local1, Local2)
                        Return (0x01)
                    }
                    ElseIf (DerefOf (B679 [Local1]))
                    {
                        /* the computational data type */

                        If ((DerefOf (DerefOf (Arg1) [Local0]) != DerefOf (Local7 [
                            Local0])))
                        {
                            /* The value is corrupted */

                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (DerefOf (Arg1) [Local0]),
                                DerefOf (Local7 [Local0]))
                            Return (0x01)
                        }
                    }
                }
            }

            Return (0x00)
        }

        /* Update specified Object */
        /* m007(<msg>, <ref to target>) */
        Method (M007, 2, NotSerialized)
        {
            Local0 = ObjectType (Arg1)
            If (DerefOf (B66F [Local0]))
            {
                /* Can be used in Index Operator */

                Local1 = SizeOf (Arg1)
                If (Local1)
                {
                    /* Update the last Member Object */

                    Local1--
                    Local2 = DerefOf (Arg1) [Local1]
                    Local3 = RefOf (Local2)
                    Local4 = DerefOf (Local2)
                    If ((ObjectType (Local4) == 0x01))
                    {
                        /* Integer */

                        Store (~Local4, DerefOf (Local3))
                    }
                    Else
                    {
                        DerefOf (Local3) = Ones
                        If (CH03 (Arg0, Z122, __LINE__, 0x00, Arg1))
                        {
                            /* Store caused unexpected exception */

                            Return (0x01)
                        }
                    }

                    If (Local1)
                    {
                        /* Update the First Member Object */

                        Local2 = DerefOf (Arg1) [0x00]
                        Local4 = DerefOf (Local2)
                        If ((ObjectType (Local4) == 0x01))
                        {
                            /* Integer */

                            Store (~Local4, DerefOf (Local3))
                        }
                        Else
                        {
                            DerefOf (Local3) = Ones
                            If (CH03 (Arg0, Z122, __LINE__, 0x00, Arg1))
                            {
                                /* Store caused unexpected exception */

                                Return (0x01)
                            }
                        }
                    }
                }
                ElseIf ((Local0 == 0x04))
                {
                    /* Empty Package */

                    Arg1 = Package (0x01)
                        {
                            "update string"
                        }
                }
                Else
                {
                    /* Empty String/Buffer */

                    Arg1 = "update string"
                }
            }
            ElseIf (DerefOf (B674 [Local0]))
            {
                /* Non-Computational Data Objects */

                CopyObject ("update string", Arg1)
            }
            Else
            {
                Store (~ToInteger (DerefOf (Arg1)), Arg1)
            }

            If (CH03 (Arg0, Z122, __LINE__, 0x00, Arg1))
            {
                /* Update caused unexpected exception */

                Return (0x01)
            }

            Return (0x00)
        }

        /* Check processing of an Source Named Object of the specified type */
        /* on immediate storing to a Target Named Object of the specified type */
        /* m008(<msg>, <aux>, <target type>, <source type>, */
        /*      <op>, <exc. condition>, <test data package>) */
        Method (M008, 7, Serialized)
        {
            /* Source Named Object */

            Name (SRC0, 0x00)
            /* Target Named Object */

            Name (DST0, 0x00)
            Name (SCL0, Buffer (0x12)
            {
                /* 0000 */  0x00, 0x00, 0x01, 0x01, 0x01, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0010 */  0x00, 0x00                                       // ..
            })
            Name (SCL1, Buffer (0x12)
            {
                /* 0000 */  0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x01, 0x01,  // ........
                /* 0008 */  0x01, 0x01, 0x00, 0x01, 0x01, 0x00, 0x00, 0x00,  // ........
                /* 0010 */  0x00, 0x00                                       // ..
            })
            Concatenate (Arg0, "-", Arg0)
            Concatenate (Arg0, Concatenate (Mid (Arg4, 0x00, 0x02), Concatenate (Mid (Arg2, 0x00,
                0x02), Mid (Arg3, 0x00, 0x02))), Arg0)
            If (STCS)
            {
                Debug = Arg0
            }

            /* Choose expected Result Object type */
            /*		if (LAnd(LEqual(arg4, 0), LEqual(arg3, 8))) { */
            If ((Arg3 == 0x08))
            {
                /* Method expected to be invoked and result in String */

                Local5 = 0x02
            }
            Else
            {
                Local5 = Arg3
            }

            /* Prepare Source of specified type */

            Store (Arg6 [0x02], Local7)
            If ((Arg3 == 0x05))
            {
                /* Field Unit Source */

                Local0 = DerefOf (DerefOf (Local7) [0x00])
                If ((Local0 == 0x00))
                {
                    Local6 = RefOf (FLU0)
                    Local5 = 0x03
                }
                ElseIf ((Local0 == 0x01))
                {
                    Local6 = RefOf (FLU2)
                    If (F64)
                    {
                        Local5 = 0x01
                    }
                    Else
                    {
                        Local5 = 0x03
                    }
                }
                Else
                {
                    Local6 = RefOf (FLU4)
                    Local5 = 0x01
                }
            }
            ElseIf ((Arg3 == 0x0E))
            {
                /* Buffer Field Source */

                Local0 = DerefOf (DerefOf (Local7) [0x00])
                If ((Local0 == 0x00))
                {
                    Local6 = RefOf (BFL0)
                }
                ElseIf ((Local0 == 0x01))
                {
                    Local6 = RefOf (BFL2)
                }
                Else
                {
                    Local6 = RefOf (BFL4)
                }
                Local5 = 0x03
            }
            Else
            {
                Local6 = RefOf (SRC0)
            }

            If (M004 (Concatenate (Arg0, "-m004"), Arg3, Local6, Local7))
            {
                /* Source Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg3, 0x00)
                Return (0x01)
            }

            /* Prepare Target of specified type */

            Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
            If ((Arg2 == 0x05))
            {
                /* Field Unit Target */

                Field (OPR0, ByteAcc, NoLock, Preserve)
                {
                    FLUX,   192,
                    FLU1,   69
                }

                Local1 = RefOf (FLU1)
            }
            ElseIf ((Arg2 == 0x0E))
            {
                /* Buffer Field Target */

                CreateField (BUFZ, 0xC0, 0x45, BFL1)
                Local1 = RefOf (BFL1)
            }
            Else
            {
                Local1 = RefOf (DST0)
            }

            If (M003 (Concatenate (Arg0, "-m003"), Arg2, Local1, Local7))
            {
                /* Target Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg2, 0x00)
                Return (0x01)
            }

            If (CH03 (Arg0, Z122, __LINE__, 0x00, Arg2))
            {
                /* Unexpected exception during preparation */

                Return (0x01)
            }

            /* Use a Source Object to immediately store into the Target */

            Store (Arg6 [0x02], Local7)
            If ((Arg2 == 0x05))
            {
                /* Field Unit Target */

                If ((Arg4 == 0x00))
                {
                    /* Store */

                    If ((Arg3 == 0x05))
                    {
                        /* Field Unit Source */

                        Local0 = DerefOf (DerefOf (Local7) [0x00])
                        If ((Local0 == 0x00))
                        {
                            FLU1 = FLU0 /* \M689.FLU0 */
                        }
                        ElseIf ((Local0 == 0x01))
                        {
                            FLU1 = FLU2 /* \M689.FLU2 */
                        }
                        Else
                        {
                            FLU1 = FLU4 /* \M689.FLU4 */
                        }
                    }
                    ElseIf ((Arg3 == 0x0E))
                    {
                        /* Buffer Field Source */

                        Local0 = DerefOf (DerefOf (Local7) [0x00])
                        If ((Local0 == 0x00))
                        {
                            FLU1 = BFL0 /* \M689.BFL0 */
                        }
                        ElseIf ((Local0 == 0x01))
                        {
                            FLU1 = BFL2 /* \M689.BFL2 */
                        }
                        Else
                        {
                            FLU1 = BFL4 /* \M689.BFL4 */
                        }
                    }
                    Else
                    {
                        FLU1 = SRC0 /* \M689.M008.SRC0 */
                    }
                }
                ElseIf ((Arg4 == 0x01))
                {
                    /* CopyObject */

                    If ((Arg3 == 0x05))
                    {
                        /* Field Unit Source */

                        Local0 = DerefOf (DerefOf (Local7) [0x00])
                        If ((Local0 == 0x00))
                        {
                            CopyObject (FLU0, FLU1) /* \M689.M008.FLU1 */
                        }
                        ElseIf ((Local0 == 0x01))
                        {
                            CopyObject (FLU2, FLU1) /* \M689.M008.FLU1 */
                        }
                        Else
                        {
                            CopyObject (FLU4, FLU1) /* \M689.M008.FLU1 */
                        }
                    }
                    ElseIf ((Arg3 == 0x0E))
                    {
                        /* Buffer Field Source */

                        Local0 = DerefOf (DerefOf (Local7) [0x00])
                        If ((Local0 == 0x00))
                        {
                            CopyObject (BFL0, FLU1) /* \M689.M008.FLU1 */
                        }
                        ElseIf ((Local0 == 0x01))
                        {
                            CopyObject (BFL2, FLU1) /* \M689.M008.FLU1 */
                        }
                        Else
                        {
                            CopyObject (BFL4, FLU1) /* \M689.M008.FLU1 */
                        }
                    }
                    Else
                    {
                        CopyObject (SRC0, FLU1) /* \M689.M008.FLU1 */
                    }
                }
                Else
                {
                    /* Unexpected Kind of Op (0 - Store, ...) */

                    ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg4, 0x00)
                    Return (0x01)
                }
            }
            ElseIf ((Arg2 == 0x0E))
            {
                /* Buffer Field Target */

                If ((Arg4 == 0x00))
                {
                    /* Store */

                    If ((Arg3 == 0x05))
                    {
                        /* Field Unit Source */

                        Local0 = DerefOf (DerefOf (Local7) [0x00])
                        If ((Local0 == 0x00))
                        {
                            BFL1 = FLU0 /* \M689.FLU0 */
                        }
                        ElseIf ((Local0 == 0x01))
                        {
                            BFL1 = FLU2 /* \M689.FLU2 */
                        }
                        Else
                        {
                            BFL1 = FLU4 /* \M689.FLU4 */
                        }
                    }
                    ElseIf ((Arg3 == 0x0E))
                    {
                        /* Buffer Field Source */

                        Local0 = DerefOf (DerefOf (Local7) [0x00])
                        If ((Local0 == 0x00))
                        {
                            BFL1 = BFL0 /* \M689.BFL0 */
                        }
                        ElseIf ((Local0 == 0x01))
                        {
                            BFL1 = BFL2 /* \M689.BFL2 */
                        }
                        Else
                        {
                            BFL1 = BFL4 /* \M689.BFL4 */
                        }
                    }
                    Else
                    {
                        BFL1 = SRC0 /* \M689.M008.SRC0 */
                    }
                }
                ElseIf ((Arg4 == 0x01))
                {
                    /* CopyObject */

                    If ((Arg3 == 0x05))
                    {
                        /* Field Unit Source */

                        Local0 = DerefOf (DerefOf (Local7) [0x00])
                        If ((Local0 == 0x00))
                        {
                            CopyObject (FLU0, BFL1) /* \M689.M008.BFL1 */
                        }
                        ElseIf ((Local0 == 0x01))
                        {
                            CopyObject (FLU2, BFL1) /* \M689.M008.BFL1 */
                        }
                        Else
                        {
                            CopyObject (FLU4, BFL1) /* \M689.M008.BFL1 */
                        }
                    }
                    ElseIf ((Arg3 == 0x0E))
                    {
                        /* Buffer Field Source */

                        Local0 = DerefOf (DerefOf (Local7) [0x00])
                        If ((Local0 == 0x00))
                        {
                            CopyObject (BFL0, BFL1) /* \M689.M008.BFL1 */
                        }
                        ElseIf ((Local0 == 0x01))
                        {
                            CopyObject (BFL2, BFL1) /* \M689.M008.BFL1 */
                        }
                        Else
                        {
                            CopyObject (BFL4, BFL1) /* \M689.M008.BFL1 */
                        }
                    }
                    Else
                    {
                        CopyObject (SRC0, BFL1) /* \M689.M008.BFL1 */
                    }
                }
                Else
                {
                    /* Unexpected Kind of Op (0 - Store, ...) */

                    ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg4, 0x00)
                    Return (0x01)
                }
            }
            ElseIf ((Arg4 == 0x00))
            {
                /* Store */

                If ((Arg3 == 0x05))
                {
                    /* Field Unit Source */

                    Local0 = DerefOf (DerefOf (Local7) [0x00])
                    If ((Local0 == 0x00))
                    {
                        DST0 = FLU0 /* \M689.FLU0 */
                    }
                    ElseIf ((Local0 == 0x01))
                    {
                        DST0 = FLU2 /* \M689.FLU2 */
                    }
                    Else
                    {
                        DST0 = FLU4 /* \M689.FLU4 */
                    }
                }
                ElseIf ((Arg3 == 0x0E))
                {
                    /* Buffer Field Source */

                    Local0 = DerefOf (DerefOf (Local7) [0x00])
                    If ((Local0 == 0x00))
                    {
                        DST0 = BFL0 /* \M689.BFL0 */
                    }
                    ElseIf ((Local0 == 0x01))
                    {
                        DST0 = BFL2 /* \M689.BFL2 */
                    }
                    Else
                    {
                        DST0 = BFL4 /* \M689.BFL4 */
                    }
                }
                Else
                {
                    DST0 = SRC0 /* \M689.M008.SRC0 */
                }
            }
            ElseIf ((Arg4 == 0x01))
            {
                /* CopyObject */

                If ((Arg3 == 0x05))
                {
                    /* Field Unit Source */

                    Local0 = DerefOf (DerefOf (Local7) [0x00])
                    If ((Local0 == 0x00))
                    {
                        CopyObject (FLU0, DST0) /* \M689.M008.DST0 */
                    }
                    ElseIf ((Local0 == 0x01))
                    {
                        CopyObject (FLU2, DST0) /* \M689.M008.DST0 */
                    }
                    Else
                    {
                        CopyObject (FLU4, DST0) /* \M689.M008.DST0 */
                    }
                }
                ElseIf ((Arg3 == 0x0E))
                {
                    /* Buffer Field Source */

                    Local0 = DerefOf (DerefOf (Local7) [0x00])
                    If ((Local0 == 0x00))
                    {
                        CopyObject (BFL0, DST0) /* \M689.M008.DST0 */
                    }
                    ElseIf ((Local0 == 0x01))
                    {
                        CopyObject (BFL2, DST0) /* \M689.M008.DST0 */
                    }
                    Else
                    {
                        CopyObject (BFL4, DST0) /* \M689.M008.DST0 */
                    }
                }
                Else
                {
                    CopyObject (SRC0, DST0) /* \M689.M008.DST0 */
                }
            }
            Else
            {
                /* Unexpected Kind of Op (0 - Store, ...) */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg4, 0x00)
                Return (0x01)
            }

            If (Arg5)
            {
                /* Exception is expected */

                If (((Arg4 == 0x01) && (Arg2 == C016)))
                {
                    If (X170)
                    {
                        If (!CH06 (Arg0, 0x39, 0xFF))
                        {
                            If (STCS)
                            {
                                M000 (0x02, 0x0100, Arg2, Arg3)
                            }
                        }
                    }
                    Else
                    {
                        CH03 (Arg0, Z122, __LINE__, 0x00, Arg2)
                    }
                }
                ElseIf (!CH06 (Arg0, 0x39, 0xFF))
                {
                    If (STCS)
                    {
                        M000 (0x02, 0x0100, Arg2, Arg3)
                    }
                }

                /* No further test if exception is expected */

                Return (0x00)
            }
            ElseIf (CH03 (Arg0, Z122, __LINE__, 0x00, Arg2))
            {
                /* Storing caused unexpected exception */

                If (STCS)
                {
                    M000 (0x02, 0x0100, Arg2, Arg3)
                }
            }
            Else
            {
                /* Check Target Object to have the expected type and value */
                /* Target accept type on storing to Named by Store operator is 0 */
                If (Arg4)
                {
                    Local0 = 0x02
                }
                Else
                {
                    Local0 = 0x00
                }

                M006 (Concatenate (Arg0, "-m006"), Local1, Arg2, Local5, Arg4, Local0, Arg6)
            }

            /* Check Source Object value and type is not corrupted after storing */

            Store (Arg6 [0x02], Local7)
            If (M005 (Concatenate (Arg0, "-m005"), Arg3, Local6, Local7))
            {
                If (STCS)
                {
                    Debug = "m008, Source Object has been corrupted during storing"
                }

                Return (0x01)
            }

            /* Check auxiliary Target Object to have the initial type and value */

            Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
            If (M016 (Concatenate (Arg0, "-m016"), Arg2, 0x00, Local7))
            {
                If (STCS)
                {
                    Debug = "m008, auxiliary Target Object has been corrupted during storing"
                }

                Return (0x01)
            }

            /* Update Target Object */

            If (M007 (Concatenate (Arg0, "-m007"), Local1))
            {
                If (STCS)
                {
                    Debug = "m008, Error during update of Target"
                }

                Return (0x01)
            }

            /* Check Source Object value and type is not corrupted after updating the copy */

            Store (Arg6 [0x02], Local7)
            If (Y900)
            {
                If (((Arg4 == 0x00) &&                         /* Source type is 2-4 */

(DerefOf (Index (Buffer (0x12)
                                    {
                                        /* 0000 */  0x00, 0x00, 0x01, 0x01, 0x01, 0x00, 0x00, 0x00,  // ........
                                        /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                                        /* 0010 */  0x00, 0x00                                       // ..
                                    }, Arg3
                    )) &&                             /* Target type is 4, 6-9, 11-12 */

DerefOf (Index (Buffer (0x12)
                                    {
                                        /* 0000 */  0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x01, 0x01,  // ........
                                        /* 0008 */  0x01, 0x01, 0x00, 0x01, 0x01, 0x00, 0x00, 0x00,  // ........
                                        /* 0010 */  0x00, 0x00                                       // ..
                                    }, Arg2))) /* Store */))
                {
                    If (X153)
                    {
                        If (M005 (Concatenate (Arg0, "-m005"), Arg3, Local6, Local7))
                        {
                            If (STCS)
                            {
                                Debug = "m008, Source Object has been corrupted during update of Target"
                            }
                        }
                    }
                }
                ElseIf (M005 (Concatenate (Arg0, "-m005"), Arg3, Local6, Local7))
                {
                    If (STCS)
                    {
                        Debug = "m008, Source Object has been corrupted during update of Target"
                    }
                }
            }
            ElseIf (((Arg4 == 0x00) &&                     /* Source type is 2-4 */

(DerefOf (SCL0 [Arg3]) &&                         /* Target type is 4, 6-9, 11-12 */


                DerefOf (SCL1 [Arg2])) /* Store */))
            {
                If (X153)
                {
                    If (M005 (Concatenate (Arg0, "-m005"), Arg3, Local6, Local7))
                    {
                        If (STCS)
                        {
                            Debug = "m008, Source Object has been corrupted during update of Target"
                        }
                    }
                }
            }
            ElseIf (M005 (Concatenate (Arg0, "-m005"), Arg3, Local6, Local7))
            {
                If (STCS)
                {
                    Debug = "m008, Source Object has been corrupted during update of Target"
                }
            }

            /* Check auxiliary Target Object to have the initial type and value */

            Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
            If (M016 (Concatenate (Arg0, "-m016"), Arg2, 0x00, Local7))
            {
                If (STCS)
                {
                    Debug = "m008, auxiliary Target Object has been corrupted during update of Target"
                }

                Return (0x01)
            }

            Return (0x00)
        }

        /* Check processing of an Source Named Object of the specified type */
        /* on immediate storing to a Target LocalX Object of the specified type */
        /* m009(<msg>, <aux>, <target type>, <source type>, */
        /*      <op>, <exc. condition>, <test data package>) */
        Method (M009, 7, Serialized)
        {
            /* Source Named Object */

            Name (SRC0, 0x00)
            /* Target LocalX Object: Local4 */

            Concatenate (Arg0, "-", Arg0)
            Concatenate (Arg0, Concatenate (Mid (Arg4, 0x00, 0x02), Concatenate (Mid (Arg2, 0x00,
                0x02), Mid (Arg3, 0x00, 0x02))), Arg0)
            If (STCS)
            {
                Debug = Arg0
            }

            /* Choose expected Result Object type */
            /*		if (LAnd(LEqual(arg4, 0), LEqual(arg3, 8))) { */
            If ((Arg3 == 0x08))
            {
                /* Method expected to be invoked and result in String */

                Local5 = 0x02
            }
            Else
            {
                Local5 = Arg3
            }

            /* Prepare Source of specified type */

            Store (Arg6 [0x02], Local7)
            If ((Arg3 == 0x05))
            {
                /* Field Unit Source */

                Local0 = DerefOf (DerefOf (Local7) [0x00])
                If ((Local0 == 0x00))
                {
                    Local6 = RefOf (FLU0)
                }
                ElseIf ((Local0 == 0x01))
                {
                    Local6 = RefOf (FLU2)
                    Local5 = 0x03
                    If (F64)
                    {
                        Local5 = 0x01
                    }
                    Else
                    {
                        Local5 = 0x03
                    }
                }
                Else
                {
                    Local6 = RefOf (FLU4)
                    Local5 = 0x01
                }
            }
            ElseIf ((Arg3 == 0x0E))
            {
                /* Buffer Field Source */

                Local0 = DerefOf (DerefOf (Local7) [0x00])
                If ((Local0 == 0x00))
                {
                    Local6 = RefOf (BFL0)
                }
                ElseIf ((Local0 == 0x01))
                {
                    Local6 = RefOf (BFL2)
                }
                Else
                {
                    Local6 = RefOf (BFL4)
                }
                Local5 = 0x03
            }
            Else
            {
                Local6 = RefOf (SRC0)
            }

            If (M004 (Concatenate (Arg0, "-m004"), Arg3, Local6, Local7))
            {
                /* Source Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg3, 0x00)
                Return (0x01)
            }

            /* Prepare Target of specified type */

            Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
            If (M003 (Concatenate (Arg0, "-m003"), Arg2, RefOf (Local4), Local7))
            {
                /* Target Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg2, 0x00)
                Return (0x01)
            }

            If (CH03 (Arg0, Z122, __LINE__, 0x00, Arg2))
            {
                /* Unexpected exception during preparation */

                Return (0x01)
            }

            /* Use a Source Object to immediately store into the Target */

            Store (Arg6 [0x02], Local7)
            If ((Arg4 == 0x00))
            {
                /* Store */

                If ((Arg3 == 0x05))
                {
                    /* Field Unit Source */

                    Local0 = DerefOf (DerefOf (Local7) [0x00])
                    If ((Local0 == 0x00))
                    {
                        Local4 = FLU0 /* \M689.FLU0 */
                    }
                    ElseIf ((Local0 == 0x01))
                    {
                        Local4 = FLU2 /* \M689.FLU2 */
                    }
                    Else
                    {
                        Local4 = FLU4 /* \M689.FLU4 */
                    }
                }
                ElseIf ((Arg3 == 0x0E))
                {
                    /* Buffer Field Source */

                    Local0 = DerefOf (DerefOf (Local7) [0x00])
                    If ((Local0 == 0x00))
                    {
                        Local4 = BFL0 /* \M689.BFL0 */
                    }
                    ElseIf ((Local0 == 0x01))
                    {
                        Local4 = BFL2 /* \M689.BFL2 */
                    }
                    Else
                    {
                        Local4 = BFL4 /* \M689.BFL4 */
                    }
                }
                Else
                {
                    Local4 = SRC0 /* \M689.M009.SRC0 */
                }
            }
            ElseIf ((Arg4 == 0x01))
            {
                /* CopyObject */

                If ((Arg3 == 0x05))
                {
                    /* Field Unit Source */

                    Local0 = DerefOf (DerefOf (Local7) [0x00])
                    If ((Local0 == 0x00))
                    {
                        CopyObject (FLU0, Local4)
                    }
                    ElseIf ((Local0 == 0x01))
                    {
                        CopyObject (FLU2, Local4)
                    }
                    Else
                    {
                        CopyObject (FLU4, Local4)
                    }
                }
                ElseIf ((Arg3 == 0x0E))
                {
                    /* Buffer Field Source */

                    Local0 = DerefOf (DerefOf (Local7) [0x00])
                    If ((Local0 == 0x00))
                    {
                        CopyObject (BFL0, Local4)
                    }
                    ElseIf ((Local0 == 0x01))
                    {
                        CopyObject (BFL2, Local4)
                    }
                    Else
                    {
                        CopyObject (BFL4, Local4)
                    }
                }
                Else
                {
                    CopyObject (SRC0, Local4)
                }
            }
            Else
            {
                /* Unexpected Kind of Op (0 - Store, ...) */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg4, 0x00)
                Return (0x01)
            }

            If (Arg5)
            {
                /* Exception is expected */

                If (!CH06 (Arg0, 0x0F, 0xFF))
                {
                    If (STCS)
                    {
                        M000 (0x02, 0x0100, Arg2, Arg3)
                    }
                }
            }
            ElseIf (CH03 (Arg0, Z122, __LINE__, 0x00, Arg2))
            {
                /* Storing caused unexpected exception */

                If (STCS)
                {
                    M000 (0x02, 0x0100, Arg2, Arg3)
                }
            }
            Else
            {
                /* Check Target Object to have the expected type and value */
                /* Target accept type on storing to LocalX is 1 */
                Local0 = 0x01
                M006 (Concatenate (Arg0, "-m006"), RefOf (Local4), Arg2, Local5, Arg4, Local0, Arg6)
            }

            /* Check Source Object value and type is not corrupted after storing */

            Store (Arg6 [0x02], Local7)
            If (M005 (Concatenate (Arg0, "-m005"), Arg3, Local6, Local7))
            {
                If (STCS)
                {
                    Debug = "m009, Source Object has been corrupted during storing"
                }
            }

            /* Check auxiliary Target Object to have the initial type and value */

            Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
            If (M016 (Concatenate (Arg0, "-m016"), Arg2, 0x00, Local7))
            {
                If (STCS)
                {
                    Debug = "m009, auxiliary Target Object has been corrupted during storing"
                }

                Return (0x01)
            }

            /* Update Target Object */

            If (M007 (Concatenate (Arg0, "-m007"), RefOf (Local4)))
            {
                If (STCS)
                {
                    Debug = "m009, Error during update of Target"
                }

                Return (0x01)
            }

            /* Check Source Object value and type is not corrupted after updating the copy */

            Store (Arg6 [0x02], Local7)
            If (M005 (Concatenate (Arg0, "-m005"), Arg3, Local6, Local7))
            {
                If (STCS)
                {
                    Debug = "m009, Source Object has been corrupted during update of Target"
                }
            }

            /* Check auxiliary Target Object to have the initial type and value */

            Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
            If (M016 (Concatenate (Arg0, "-m016"), Arg2, 0x00, Local7))
            {
                If (STCS)
                {
                    Debug = "m009, auxiliary Target Object has been corrupted during update of Target"
                }

                Return (0x01)
            }

            Return (0x00)
        }

        /* Check processing of an Source LocalX Object of the specified type */
        /* on immediate storing to a Target Named Object of the specified type */
        /* m00a(<msg>, <aux>, <target type>, <source type>, */
        /*      <op>, <exc. condition>, <test data package>) */
        Method (M00A, 7, Serialized)
        {
            /* Source Object: Local1 */
            /* Target Named Object (or the reference to it in case of Fields) */
            Name (DST0, 0x00)
            Name (SCL0, Buffer (0x12)
            {
                /* 0000 */  0x00, 0x00, 0x01, 0x01, 0x01, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0010 */  0x00, 0x00                                       // ..
            })
            Name (SCL1, Buffer (0x12)
            {
                /* 0000 */  0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x01, 0x01,  // ........
                /* 0008 */  0x01, 0x01, 0x00, 0x01, 0x01, 0x00, 0x00, 0x00,  // ........
                /* 0010 */  0x00, 0x00                                       // ..
            })
            Concatenate (Arg0, "-", Arg0)
            Concatenate (Arg0, Concatenate (Mid (Arg4, 0x00, 0x02), Concatenate (Mid (Arg2, 0x00,
                0x02), Mid (Arg3, 0x00, 0x02))), Arg0)
            If (STCS)
            {
                Debug = Arg0
            }

            /* Prepare Source of specified type */

            Store (Arg6 [0x02], Local7)
            If (M004 (Concatenate (Arg0, "-m004"), Arg3, RefOf (Local1), Local7))
            {
                /* Source Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg3, 0x00)
                Return (0x01)
            }

            /* Prepare Target of specified type */

            Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
            If ((Arg2 == 0x05))
            {
                /* Field Unit Target */

                Field (OPR0, ByteAcc, NoLock, Preserve)
                {
                    FLUX,   192,
                    FLU1,   69
                }

                Local4 = RefOf (FLU1)
            }
            ElseIf ((Arg2 == 0x0E))
            {
                /* Buffer Field Target */

                CreateField (BUFZ, 0xC0, 0x45, BFL1)
                Local4 = RefOf (BFL1)
            }
            Else
            {
                Local4 = RefOf (DST0)
            }

            If (M003 (Concatenate (Arg0, "-m003"), Arg2, Local4, Local7))
            {
                /* Target Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg2, 0x00)
                Return (0x01)
            }

            If (CH03 (Arg0, Z122, __LINE__, 0x00, Arg2))
            {
                /* Unexpected exception during preparation */

                Return (0x01)
            }

            /* Use a Source Object to immediately store into the Target */

            If ((Arg2 == 0x05))
            {
                /* Field Unit Target */

                If ((Arg4 == 0x00))
                {
                    /* Store */

                    FLU1 = Local1
                }
                ElseIf ((Arg4 == 0x01))
                {
                    /* CopyObject */

                    CopyObject (Local1, FLU1) /* \M689.M00A.FLU1 */
                }
                Else
                {
                    /* Unexpected Kind of Op (0 - Store, ...) */

                    ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg4, 0x00)
                    Return (0x01)
                }
            }
            ElseIf ((Arg2 == 0x0E))
            {
                /* Buffer Field Target */

                If ((Arg4 == 0x00))
                {
                    /* Store */

                    BFL1 = Local1
                }
                ElseIf ((Arg4 == 0x01))
                {
                    /* CopyObject */

                    CopyObject (Local1, BFL1) /* \M689.M00A.BFL1 */
                }
                Else
                {
                    /* Unexpected Kind of Op (0 - Store, ...) */

                    ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg4, 0x00)
                    Return (0x01)
                }
            }
            ElseIf ((Arg4 == 0x00))
            {
                /* Store */

                DST0 = Local1
            }
            ElseIf ((Arg4 == 0x01))
            {
                /* CopyObject */

                CopyObject (Local1, DST0) /* \M689.M00A.DST0 */
            }
            Else
            {
                /* Unexpected Kind of Op (0 - Store, ...) */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg4, 0x00)
                Return (0x01)
            }

            If (Arg5)
            {
                /* Exception is expected */

                If (((Arg4 == 0x01) && ((Arg2 == C016) && (Arg3 !=
                    C008))))
                {
                    If (X170)
                    {
                        If (!CH06 (Arg0, 0x46, 0xFF))
                        {
                            If (STCS)
                            {
                                M000 (0x02, 0x0100, Arg2, Arg3)
                            }
                        }
                    }
                    Else
                    {
                        CH03 (Arg0, Z122, __LINE__, 0x00, Arg2)
                    }
                }
                ElseIf (!CH06 (Arg0, 0x46, 0xFF))
                {
                    If (STCS)
                    {
                        M000 (0x02, 0x0100, Arg2, Arg3)
                    }
                }

                /* No further test if exception is expected */

                Return (0x00)
            }
            ElseIf (CH03 (Arg0, Z122, __LINE__, 0x00, Arg2))
            {
                /* Storing caused unexpected exception */

                If (STCS)
                {
                    M000 (0x02, 0x0100, Arg2, Arg3)
                }
            }
            Else
            {
                /* Check Target Object to have the expected type and value */
                /* Target accept type on storing to Named of Store operator is 0 */
                If (Arg4)
                {
                    Local0 = 0x02
                }
                Else
                {
                    Local0 = 0x00
                }

                M006 (Concatenate (Arg0, "-m006"), Local4, Arg2, Arg3, Arg4, Local0, Arg6)
            }

            /* Check Source Object value and type is not corrupted after storing */

            Store (Arg6 [0x02], Local7)
            If (M005 (Concatenate (Arg0, "-m005"), Arg3, RefOf (Local1), Local7))
            {
                If (STCS)
                {
                    Debug = "m00a, Source Object has been corrupted during storing"
                }
            }

            /* Check auxiliary Target Object to have the initial type and value */

            Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
            If (M016 (Concatenate (Arg0, "-m016"), Arg2, 0x00, Local7))
            {
                If (STCS)
                {
                    Debug = "m00a, auxiliary Target Object has been corrupted during storing"
                }

                Return (0x01)
            }

            /* Update Target Object */

            If (M007 (Concatenate (Arg0, "-m007"), Local4))
            {
                If (STCS)
                {
                    Debug = "m00a, Error during update of Target"
                }

                Return (0x01)
            }

            /* Check Source Object value and type is not corrupted after updating the copy */

            Store (Arg6 [0x02], Local7)
            If (Y900)
            {
                If (((Arg4 == 0x00) &&                         /* Source type is 2-4 */

(DerefOf (Index (Buffer (0x12)
                                    {
                                        /* 0000 */  0x00, 0x00, 0x01, 0x01, 0x01, 0x00, 0x00, 0x00,  // ........
                                        /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                                        /* 0010 */  0x00, 0x00                                       // ..
                                    }, Arg3
                    )) &&                             /* Target type is 4, 6-9, 11-12 */

DerefOf (Index (Buffer (0x12)
                                    {
                                        /* 0000 */  0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x01, 0x01,  // ........
                                        /* 0008 */  0x01, 0x01, 0x00, 0x01, 0x01, 0x00, 0x00, 0x00,  // ........
                                        /* 0010 */  0x00, 0x00                                       // ..
                                    }, Arg2))) /* Store */))
                {
                    If (X153)
                    {
                        If (M005 (Concatenate (Arg0, "-m005"), Arg3, RefOf (Local1), Local7))
                        {
                            If (STCS)
                            {
                                Debug = "m00a, Source Object has been corrupted during update of Target"
                            }
                        }
                    }
                }
                ElseIf (M005 (Concatenate (Arg0, "-m005"), Arg3, RefOf (Local1), Local7))
                {
                    If (STCS)
                    {
                        Debug = "m00a, Source Object has been corrupted during update of Target"
                    }
                }
            }
            ElseIf            /* if (y900) */

 (((Arg4 == 0x00) &&                     /* Source type is 2-4 */

(DerefOf (SCL0 [Arg3]) &&                         /* Target type is 4, 6-9, 11-12 */


                DerefOf (SCL1 [Arg2])) /* Store */))
            {
                If (X153)
                {
                    If (M005 (Concatenate (Arg0, "-m005"), Arg3, RefOf (Local1), Local7))
                    {
                        If (STCS)
                        {
                            Debug = "m00a, Source Object has been corrupted during update of Target"
                        }
                    }
                }
            }
            ElseIf (M005 (Concatenate (Arg0, "-m005"), Arg3, RefOf (Local1), Local7))
            {
                If (STCS)
                {
                    Debug = "m00a, Source Object has been corrupted during update of Target"
                }
            }

            /* Check auxiliary Target Object to have the initial type and value */

            Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
            If (M016 (Concatenate (Arg0, "-m016"), Arg2, 0x00, Local7))
            {
                If (STCS)
                {
                    Debug = "m00a, auxiliary Target Object has been corrupted during update of Target"
                }

                Return (0x01)
            }

            Return (0x00)
        }

        /* Check processing of an Source LocalX Object of the specified type */
        /* on immediate storing to a Target LocalX Object of the specified type */
        /* m00b(<msg>, <aux>, <target type>, <source type>, */
        /*      <op>, <exc. condition>, <test data package>) */
        Method (M00B, 7, NotSerialized)
        {
            /* Source LocalX Object: Local1 */
            /* Target LocalX Object: Local4 */
            Concatenate (Arg0, "-", Arg0)
            Concatenate (Arg0, Concatenate (Mid (Arg4, 0x00, 0x02), Concatenate (Mid (Arg2, 0x00,
                0x02), Mid (Arg3, 0x00, 0x02))), Arg0)
            If (STCS)
            {
                Debug = Arg0
            }

            /* Prepare Source of specified type */

            Store (Arg6 [0x02], Local7)
            If (M004 (Concatenate (Arg0, "-m004"), Arg3, RefOf (Local1), Local7))
            {
                /* Source Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg3, 0x00)
                Return (0x01)
            }

            /* Prepare Target of specified type */

            Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
            If (M003 (Concatenate (Arg0, "-m003"), Arg2, RefOf (Local4), Local7))
            {
                /* Target Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg2, 0x00)
                Return (0x01)
            }

            If (CH03 (Arg0, Z122, __LINE__, 0x00, Arg2))
            {
                /* Unexpected exception during preparation */

                Return (0x01)
            }

            /* Use a Source Object to immediately store into the Target */

            If ((Arg4 == 0x00))
            {
                /* Store */

                Local4 = Local1
            }
            ElseIf ((Arg4 == 0x01))
            {
                /* CopyObject */

                CopyObject (Local1, Local4)
            }
            Else
            {
                /* Unexpected Kind of Op (0 - Store, ...) */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg4, 0x00)
                Return (0x01)
            }

            If (Arg5)
            {
                /* Exception is expected */

                If (!CH06 (Arg0, 0x0F, 0xFF))
                {
                    If (STCS)
                    {
                        M000 (0x02, 0x0100, Arg2, Arg3)
                    }
                }
            }
            ElseIf (CH03 (Arg0, Z122, __LINE__, 0x00, Arg2))
            {
                /* Storing caused unexpected exception */

                If (STCS)
                {
                    M000 (0x02, 0x0100, Arg2, Arg3)
                }
            }
            Else
            {
                /* Check Target Object to have the expected type and value */
                /* Target accept type on storing to LocalX is 1 */
                Local0 = 0x01
                M006 (Concatenate (Arg0, "-m006"), RefOf (Local4), Arg2, Arg3, Arg4, Local0, Arg6)
            }

            /* Check Source Object value and type is not corrupted after storing */

            Store (Arg6 [0x02], Local7)
            If (M005 (Concatenate (Arg0, "-m005"), Arg3, RefOf (Local1), Local7))
            {
                If (STCS)
                {
                    Debug = "m00b, Source Object has been corrupted during storing"
                }
            }

            /* Check auxiliary Target Object to have the initial type and value */

            Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
            If (M016 (Concatenate (Arg0, "-m016"), Arg2, 0x00, Local7))
            {
                If (STCS)
                {
                    Debug = "m00b, auxiliary Target Object has been corrupted during storing"
                }

                Return (0x01)
            }

            /* Update Target Object */

            If (M007 (Concatenate (Arg0, "-m007"), RefOf (Local4)))
            {
                If (STCS)
                {
                    Debug = "m00b, Error during update of Target"
                }

                Return (0x01)
            }

            /* Check Source Object value and type is not corrupted after updating the copy */

            Store (Arg6 [0x02], Local7)
            If (M005 (Concatenate (Arg0, "-m005"), Arg3, RefOf (Local1), Local7))
            {
                If (STCS)
                {
                    Debug = "m00b, Source Object has been corrupted during update of Target"
                }
            }

            /* Check auxiliary Target Object to have the initial type and value */

            Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
            If (M016 (Concatenate (Arg0, "-m016"), Arg2, 0x00, Local7))
            {
                If (STCS)
                {
                    Debug = "m00b, auxiliary Target Object has been corrupted during update of Target"
                }

                Return (0x01)
            }

            Return (0x00)
        }

        /* Check processing of an Source Named Object of the specified type */
        /* on immediate storing to an argument of Method passed to as immediate */
        /* Named Object of another specified type */
        /* m00c(<msg>, <aux>, <target type>, <source type>, */
        /*      <op>, <exc. condition>, <test data package>) */
        Method (M00C, 7, Serialized)
        {
            Method (M10C, 7, Serialized)
            {
                /* Source Named Object */

                Name (SRC0, 0x00)
                /* Target Named Object: ARG1 */
                /* Choose expected Result Object type */
                /*			if (LAnd(LEqual(arg4, 0), LEqual(arg3, 8))) { */
                If ((Arg3 == 0x08))
                {
                    /* Method expected to be invoked and result in String */

                    Local5 = 0x02
                }
                Else
                {
                    Local5 = Arg3
                }

                /* Prepare Source of specified type */

                Store (Arg6 [0x02], Local7)
                If ((Arg3 == 0x05))
                {
                    /* Field Unit Source */

                    Local0 = DerefOf (DerefOf (Local7) [0x00])
                    If ((Local0 == 0x00))
                    {
                        Local6 = RefOf (FLU0)
                        Local5 = 0x03
                    }
                    ElseIf ((Local0 == 0x01))
                    {
                        Local6 = RefOf (FLU2)
                        If (F64)
                        {
                            Local5 = 0x01
                        }
                        Else
                        {
                            Local5 = 0x03
                        }
                    }
                    Else
                    {
                        Local6 = RefOf (FLU4)
                        Local5 = 0x01
                    }
                }
                ElseIf ((Arg3 == 0x0E))
                {
                    /* Buffer Field Source */

                    Local0 = DerefOf (DerefOf (Local7) [0x00])
                    If ((Local0 == 0x00))
                    {
                        Local6 = RefOf (BFL0)
                    }
                    ElseIf ((Local0 == 0x01))
                    {
                        Local6 = RefOf (BFL2)
                    }
                    Else
                    {
                        Local6 = RefOf (BFL4)
                    }
                    Local5 = 0x03
                }
                Else
                {
                    Local6 = RefOf (SRC0)
                }

                If (M004 (Concatenate (Arg0, "-m004"), Arg3, Local6, Local7))
                {
                    /* Source Object can not be prepared */

                    ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg3, 0x00)
                    Return (0x01)
                }

                Local1 = RefOf (Arg1)
                If (CH03 (Arg0, Z122, __LINE__, 0x00, Arg2))
                {
                    /* Unexpected exception during preparation */

                    Return (0x01)
                }

                /* Use a Source Object to immediately store into the Target */

                Store (Arg6 [0x02], Local7)
                If ((Arg4 == 0x00))
                {
                    /* Store */

                    If ((Arg3 == 0x05))
                    {
                        /* Field Unit Source */

                        Local0 = DerefOf (DerefOf (Local7) [0x00])
                        If ((Local0 == 0x00))
                        {
                            Arg1 = FLU0 /* \M689.FLU0 */
                        }
                        ElseIf ((Local0 == 0x01))
                        {
                            Arg1 = FLU2 /* \M689.FLU2 */
                        }
                        Else
                        {
                            Arg1 = FLU4 /* \M689.FLU4 */
                        }
                    }
                    ElseIf ((Arg3 == 0x0E))
                    {
                        /* Buffer Field Source */

                        Local0 = DerefOf (DerefOf (Local7) [0x00])
                        If ((Local0 == 0x00))
                        {
                            Arg1 = BFL0 /* \M689.BFL0 */
                        }
                        ElseIf ((Local0 == 0x01))
                        {
                            Arg1 = BFL2 /* \M689.BFL2 */
                        }
                        Else
                        {
                            Arg1 = BFL4 /* \M689.BFL4 */
                        }
                    }
                    Else
                    {
                        Arg1 = SRC0 /* \M689.M00C.M10C.SRC0 */
                    }
                }
                ElseIf ((Arg4 == 0x01))
                {
                    /* CopyObject */

                    If ((Arg3 == 0x05))
                    {
                        /* Field Unit Source */

                        Local0 = DerefOf (DerefOf (Local7) [0x00])
                        If ((Local0 == 0x00))
                        {
                            CopyObject (FLU0, Arg1)
                        }
                        ElseIf ((Local0 == 0x01))
                        {
                            CopyObject (FLU2, Arg1)
                        }
                        Else
                        {
                            CopyObject (FLU4, Arg1)
                        }
                    }
                    ElseIf ((Arg3 == 0x0E))
                    {
                        /* Buffer Field Source */

                        Local0 = DerefOf (DerefOf (Local7) [0x00])
                        If ((Local0 == 0x00))
                        {
                            CopyObject (BFL0, Arg1)
                        }
                        ElseIf ((Local0 == 0x01))
                        {
                            CopyObject (BFL2, Arg1)
                        }
                        Else
                        {
                            CopyObject (BFL4, Arg1)
                        }
                    }
                    Else
                    {
                        CopyObject (SRC0, Arg1)
                    }
                }
                Else
                {
                    /* Unexpected Kind of Op (0 - Store, ...) */

                    ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg4, 0x00)
                    Return (0x01)
                }

                If (Arg5)
                {
                    /* Exception is expected */

                    If ((((Arg4 == 0x00) && ((Arg2 == C016) && (Arg3 ==
                        C00C))) || ((Arg4 == 0x01) && ((Arg2 == C016) && (Arg3 != C008)))))
                    {
                        If (X170)
                        {
                            If (!CH06 (Arg0, 0x50, 0xFF))
                            {
                                If (STCS)
                                {
                                    M000 (0x02, 0x0100, Arg2, Arg3)
                                }
                            }
                        }
                        Else
                        {
                            CH03 (Arg0, Z122, __LINE__, 0x00, Arg2)
                        }
                    }
                    ElseIf (!CH06 (Arg0, 0x50, 0xFF))
                    {
                        If (STCS)
                        {
                            M000 (0x02, 0x0100, Arg2, Arg3)
                        }
                    }
                }
                ElseIf (CH03 (Arg0, Z122, __LINE__, 0x00, Arg2))
                {
                    /* Storing caused unexpected exception */

                    If (STCS)
                    {
                        M000 (0x02, 0x0100, Arg2, Arg3)
                    }
                }
                Else
                {
                    /* Check Target Object to have the expected type and value */
                    /* Target accept type on storing to read-only ArgX is 1 */
                    Local0 = 0x01
                    M006 (Concatenate (Arg0, "-m006"), Local1, Arg2, Local5, Arg4, Local0, Arg6)
                }

                /* Check Source Object value and type is not corrupted after storing */

                Store (Arg6 [0x02], Local7)
                If (M005 (Concatenate (Arg0, "-m005"), Arg3, Local6, Local7))
                {
                    If (STCS)
                    {
                        Debug = "m00c, Source Object has been corrupted during storing"
                    }

                    Return (0x01)
                }

                /* Check auxiliary Target Object to have the initial type and value */

                Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
                If (M016 (Concatenate (Arg0, "-m016"), Arg2, 0x00, Local7))
                {
                    If (STCS)
                    {
                        Debug = "m00c, auxiliary Target Object has been corrupted during storing"
                    }

                    Return (0x01)
                }

                /* Update Target Object */

                If (M007 (Concatenate (Arg0, "-m007"), Local1))
                {
                    If (STCS)
                    {
                        Debug = "m00c, Error during update of Target"
                    }

                    Return (0x01)
                }

                /* Check Source Object value and type is not corrupted after updating the copy */

                Store (Arg6 [0x02], Local7)
                If (M005 (Concatenate (Arg0, "-m005"), Arg3, Local6, Local7))
                {
                    If (STCS)
                    {
                        Debug = "m00c, Source Object has been corrupted during update of Target"
                    }
                }

                /* Check auxiliary Target Object to have the initial type and value */

                Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
                If (M016 (Concatenate (Arg0, "-m016"), Arg2, 0x00, Local7))
                {
                    If (STCS)
                    {
                        Debug = "m00c, auxiliary Target Object has been corrupted during update of Target"
                    }

                    Return (0x01)
                }

                Return (0x00)
            }

            /* Target Named Object */

            Name (DST0, 0x00)
            Concatenate (Arg0, "-", Arg0)
            Concatenate (Arg0, Concatenate (Mid (Arg4, 0x00, 0x02), Concatenate (Mid (Arg2, 0x00,
                0x02), Mid (Arg3, 0x00, 0x02))), Arg0)
            If (STCS)
            {
                Debug = Arg0
            }

            /* Prepare Target of specified type */

            Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
            If ((Arg2 == 0x05))
            {
                /* Field Unit Target */

                Field (OPR0, ByteAcc, NoLock, Preserve)
                {
                    FLUX,   192,
                    FLU1,   69
                }

                Local1 = RefOf (FLU1)
                FLU1 = DerefOf (Local7)
            }
            ElseIf ((Arg2 == 0x0E))
            {
                /* Buffer Field Target */

                CreateField (BUFZ, 0xC0, 0x45, BFL1)
                Local1 = RefOf (BFL1)
                BFL1 = DerefOf (Local7)
            }
            Else
            {
                Local1 = RefOf (DST0)
            }

            If (M003 (Concatenate (Arg0, "-m003"), Arg2, Local1, Local7))
            {
                /* Target Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg2, 0x00)
                Return (0x01)
            }

            If (CH03 (Arg0, Z122, __LINE__, 0x00, Arg2))
            {
                /* Unexpected exception during preparation */

                Return (0x01)
            }

            /* Use the Target Object to be the ArgX Object */

            If (M10C (Concatenate (Arg0, "-m10c"), DST0, Arg2, Arg3, Arg4, Arg5, Arg6))
            {
                If (STCS)
                {
                    Debug = "m00c, error on using the Target Object as the ArgX Object"
                }

                Return (0x01)
            }

            If (Arg5)
            {
                /* Exception is expected */

                Return (0x00)
            }

            /* Check Target Object to be saving the initial type and value */

            Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
            If (M015 (Concatenate (Arg0, "-m015"), Arg2, Local1, Local7))
            {
                If (STCS)
                {
                    Debug = "m00c, Target Object has been corrupted during storing to ArgX"
                }

                Return (0x01)
            }

            Return (0x00)
        }

        /* Check processing of an Source Named Object of the specified type */
        /* on immediate storing to an argument of Method passed to as reference */
        /* to the Named Object of another specified type */
        /* m00d(<msg>, <aux>, <target type>, <source type>, */
        /*      <op>, <exc. condition>, <test data package>) */
        Method (M00D, 7, Serialized)
        {
            Method (M10D, 7, Serialized)
            {
                /* Source Named Object */

                Name (SRC0, 0x00)
                /* Target Named Object: ARG1 */
                /* Choose expected Result Object type */
                /*			if (LAnd(LEqual(arg4, 0), LEqual(arg3, 8))) { */
                If ((Arg3 == 0x08))
                {
                    /* Method expected to be invoked and result in String */

                    Local5 = 0x02
                }
                Else
                {
                    Local5 = Arg3
                }

                /* Prepare Source of specified type */

                Store (Arg6 [0x02], Local7)
                If ((Arg3 == 0x05))
                {
                    /* Field Unit Source */

                    Local0 = DerefOf (DerefOf (Local7) [0x00])
                    If ((Local0 == 0x00))
                    {
                        Local6 = RefOf (FLU0)
                        Local5 = 0x03
                    }
                    ElseIf ((Local0 == 0x01))
                    {
                        Local6 = RefOf (FLU2)
                        If (F64)
                        {
                            Local5 = 0x01
                        }
                        Else
                        {
                            Local5 = 0x03
                        }
                    }
                    Else
                    {
                        Local6 = RefOf (FLU4)
                        Local5 = 0x01
                    }
                }
                ElseIf ((Arg3 == 0x0E))
                {
                    /* Buffer Field Source */

                    Local0 = DerefOf (DerefOf (Local7) [0x00])
                    If ((Local0 == 0x00))
                    {
                        Local6 = RefOf (BFL0)
                    }
                    ElseIf ((Local0 == 0x01))
                    {
                        Local6 = RefOf (BFL2)
                    }
                    Else
                    {
                        Local6 = RefOf (BFL4)
                    }
                    Local5 = 0x03
                }
                Else
                {
                    Local6 = RefOf (SRC0)
                }

                If (M004 (Concatenate (Arg0, "-m004"), Arg3, Local6, Local7))
                {
                    /* Source Object can not be prepared */

                    ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg3, 0x00)
                    Return (0x01)
                }

                If (CH03 (Arg0, Z122, __LINE__, 0x00, Arg2))
                {
                    /* Unexpected exception during preparation */

                    Return (0x01)
                }

                /* Use a Source Object to immediately store into the Target */

                Store (Arg6 [0x02], Local7)
                If ((Arg4 == 0x00))
                {
                    /* Store */

                    If ((Arg3 == 0x05))
                    {
                        /* Field Unit Source */

                        Local0 = DerefOf (DerefOf (Local7) [0x00])
                        If ((Local0 == 0x00))
                        {
                            Arg1 = FLU0 /* \M689.FLU0 */
                        }
                        ElseIf ((Local0 == 0x01))
                        {
                            Arg1 = FLU2 /* \M689.FLU2 */
                        }
                        Else
                        {
                            Arg1 = FLU4 /* \M689.FLU4 */
                        }
                    }
                    ElseIf ((Arg3 == 0x0E))
                    {
                        /* Buffer Field Source */

                        Local0 = DerefOf (DerefOf (Local7) [0x00])
                        If ((Local0 == 0x00))
                        {
                            Arg1 = BFL0 /* \M689.BFL0 */
                        }
                        ElseIf ((Local0 == 0x01))
                        {
                            Arg1 = BFL2 /* \M689.BFL2 */
                        }
                        Else
                        {
                            Arg1 = BFL4 /* \M689.BFL4 */
                        }
                    }
                    Else
                    {
                        Arg1 = SRC0 /* \M689.M00D.M10D.SRC0 */
                    }
                }
                ElseIf ((Arg4 == 0x01))
                {
                    /* CopyObject */

                    If ((Arg3 == 0x05))
                    {
                        /* Field Unit Source */

                        Local0 = DerefOf (DerefOf (Local7) [0x00])
                        If ((Local0 == 0x00))
                        {
                            CopyObject (FLU0, Arg1)
                        }
                        ElseIf ((Local0 == 0x01))
                        {
                            CopyObject (FLU2, Arg1)
                        }
                        Else
                        {
                            CopyObject (FLU4, Arg1)
                        }
                    }
                    ElseIf ((Arg3 == 0x0E))
                    {
                        /* Buffer Field Source */

                        Local0 = DerefOf (DerefOf (Local7) [0x00])
                        If ((Local0 == 0x00))
                        {
                            CopyObject (BFL0, Arg1)
                        }
                        ElseIf ((Local0 == 0x01))
                        {
                            CopyObject (BFL2, Arg1)
                        }
                        Else
                        {
                            CopyObject (BFL4, Arg1)
                        }
                    }
                    Else
                    {
                        CopyObject (SRC0, Arg1)
                    }
                }
                Else
                {
                    /* Unexpected Kind of Op (0 - Store, ...) */

                    ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg4, 0x00)
                    Return (0x01)
                }

                If (Arg5)
                {
                    /* Exception is expected */

                    If (((Arg4 == 0x01) && (Arg2 == C016)))
                    {
                        If (X170)
                        {
                            If (!CH06 (Arg0, 0x57, 0xFF))
                            {
                                If (STCS)
                                {
                                    M000 (0x02, 0x0100, Arg2, Arg3)
                                }
                            }
                        }
                        Else
                        {
                            CH03 (Arg0, Z122, __LINE__, 0x00, Arg2)
                        }
                    }
                    ElseIf (!CH06 (Arg0, 0x57, 0xFF))
                    {
                        If (STCS)
                        {
                            M000 (0x02, 0x0100, Arg2, Arg3)
                        }
                    }
                }
                ElseIf (CH03 (Arg0, Z122, __LINE__, 0x00, Arg2))
                {
                    /* Storing caused unexpected exception */

                    If (STCS)
                    {
                        M000 (0x02, 0x0100, Arg2, Arg3)
                    }
                }
                Else
                {
                    /* Check Target Object to have the expected type and value */
                    /* Target accept type on storing to ArgX containing reference is 1 */
                    /* (besides Store() to fixed types) */
                    If (((Arg4 == 0x00) && DerefOf (B678 [Arg2])))
                    {
                        Local0 = 0x00
                    }
                    Else
                    {
                        Local0 = 0x01
                    }

                    M006 (Concatenate (Arg0, "-m006"), Arg1, Arg2, Local5, Arg4, Local0, Arg6)
                }

                /* Check Source Object value and type is not corrupted after storing */

                Store (Arg6 [0x02], Local7)
                If (M005 (Concatenate (Arg0, "-m005"), Arg3, Local6, Local7))
                {
                    If (STCS)
                    {
                        Debug = "m00d, Source Object has been corrupted during storing"
                    }

                    Return (0x01)
                }

                /* Check auxiliary Target Object to have the initial type and value */

                Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
                If (M016 (Concatenate (Arg0, "-m016"), Arg2, 0x00, Local7))
                {
                    If (STCS)
                    {
                        Debug = "m00d, auxiliary Target Object has been corrupted during storing"
                    }

                    Return (0x01)
                }

                /* Update Target Object */

                If (M007 (Concatenate (Arg0, "-m007"), Arg1))
                {
                    If (STCS)
                    {
                        Debug = "m00d, Error during update of Target"
                    }

                    Return (0x01)
                }

                /* Check Source Object value and type is not corrupted after updating the copy */

                Store (Arg6 [0x02], Local7)
                If (M005 (Concatenate (Arg0, "-m005"), Arg3, Local6, Local7))
                {
                    If (STCS)
                    {
                        Debug = "m00d, Source Object has been corrupted during update of Target"
                    }
                }

                /* Check auxiliary Target Object to have the initial type and value */

                Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
                If (M016 (Concatenate (Arg0, "-m016"), Arg2, 0x00, Local7))
                {
                    If (STCS)
                    {
                        Debug = "m00d, auxiliary Target Object has been corrupted during update of Target"
                    }

                    Return (0x01)
                }

                Return (0x00)
            }

            /* Target Named Object */

            Name (DST0, 0x00)
            Concatenate (Arg0, "-", Arg0)
            Concatenate (Arg0, Concatenate (Mid (Arg4, 0x00, 0x02), Concatenate (Mid (Arg2, 0x00,
                0x02), Mid (Arg3, 0x00, 0x02))), Arg0)
            If (STCS)
            {
                Debug = Arg0
            }

            /* Prepare Target of specified type */

            Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
            If ((Arg2 == 0x05))
            {
                /* Field Unit Target */

                Field (OPR0, ByteAcc, NoLock, Preserve)
                {
                    FLUX,   192,
                    FLU1,   69
                }

                Local1 = RefOf (FLU1)
                FLU1 = DerefOf (Local7)
            }
            ElseIf ((Arg2 == 0x0E))
            {
                /* Buffer Field Target */

                CreateField (BUFZ, 0xC0, 0x45, BFL1)
                Local1 = RefOf (BFL1)
                BFL1 = DerefOf (Local7)
            }
            Else
            {
                Local1 = RefOf (DST0)
            }

            If (M003 (Concatenate (Arg0, "-m003"), Arg2, Local1, Local7))
            {
                /* Target Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg2, 0x00)
                Return (0x01)
            }

            If (CH03 (Arg0, Z122, __LINE__, 0x00, Arg2))
            {
                /* Unexpected exception during preparation */

                Return (0x01)
            }

            /* Use the reference to Target Object to be the ArgX Object */

            If (M10D (Concatenate (Arg0, "-m10d"), RefOf (DST0), Arg2, Arg3, Arg4, Arg5,
                Arg6))
            {
                If (STCS)
                {
                    Debug = "m00d, error on using the Target Object as the ArgX Object"
                }

                Return (0x01)
            }

            Return (0x00)
        }

        /* Check processing of an Source LocalX Object of the specified type */
        /* on immediate storing to an Element of Package of the specified type */
        /* m00e(<msg>, <aux>, <target type>, <source type>, */
        /*      <op>, <exc. condition>, <test data package>) */
        Method (M00E, 7, Serialized)
        {
            /* Source LocalX Object: Local1 */
            /* Target Package */
            Name (DST0, Package (0x01){})
            Concatenate (Arg0, "-", Arg0)
            Concatenate (Arg0, Concatenate (Mid (Arg4, 0x00, 0x02), Concatenate (Mid (Arg2, 0x00,
                0x02), Mid (Arg3, 0x00, 0x02))), Arg0)
            If (STCS)
            {
                Debug = Arg0
            }

            /* Prepare Source of specified type */

            Store (Arg6 [0x02], Local7)
            If (M004 (Concatenate (Arg0, "-m004"), Arg3, RefOf (Local1), Local7))
            {
                /* Source Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg3, 0x00)
                Return (0x01)
            }

            /* Prepare Target of specified type */

            Local4 = DST0 [0x00]
            Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
            If (M013 (Concatenate (Arg0, "-m003"), Arg2, DST0, Local7))
            {
                /* Target Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg2, 0x00)
                Return (0x01)
            }

            If (CH03 (Arg0, Z122, __LINE__, 0x00, Arg2))
            {
                /* Unexpected exception during preparation */

                Return (0x01)
            }

            /* Check Target Object to have the initial type and value */

            If (M015 (Concatenate (Arg0, "-m015"), Arg2, Local4, Local7))
            {
                /* Target Object can not be prepared */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg2, 0x00)
                Return (0x01)
            }

            /* Use a Source Object to immediately store into the Target */

            If ((Arg4 == 0x00))
            {
                /* Store */

                DST0 [0x00] = Local1
                        /*} elseif (LEqual(arg4, 1)) {	// CopyObject */
            /*		CopyObject(Local1, Index(DST0, 0)) */
            }
            Else
            {
                /* Unexpected Kind of Op (0 - Store, ...) */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg4, 0x00)
                Return (0x01)
            }

            If (Arg5)
            {
                /* Exception is expected */

                If (!CH06 (Arg0, 0x60, 0xFF))
                {
                    If (STCS)
                    {
                        M000 (0x02, 0x0100, Arg2, Arg3)
                    }
                }
            }
            ElseIf (CH03 (Arg0, Z122, __LINE__, 0x00, Arg2))
            {
                /* Storing caused unexpected exception */

                If (STCS)
                {
                    M000 (0x02, 0x0100, Arg2, Arg3)
                }
            }
            Else
            {
                /* Check Target Object to have the expected type and value */
                /* Target accept type on storing to an Element of Package is 1 */
                Local0 = 0x01
                M006 (Concatenate (Arg0, "-m006"), Local4, Arg2, Arg3, Arg4, Local0, Arg6)
            }

            /* Check Source Object value and type is not corrupted after storing */

            Store (Arg6 [0x02], Local7)
            If (M005 (Concatenate (Arg0, "-m005"), Arg3, RefOf (Local1), Local7))
            {
                If (STCS)
                {
                    Debug = "m00e, Source Object has been corrupted during storing"
                }
            }

            /* Check auxiliary Target Object to have the initial type and value */

            Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
            If (M016 (Concatenate (Arg0, "-m016"), Arg2, 0x00, Local7))
            {
                If (STCS)
                {
                    Debug = "m00e, auxiliary Target Object has been corrupted during storing"
                }

                Return (0x01)
            }

            /* Update Target Object */

            If (M017 (Concatenate (Arg0, "-m007"), DST0))
            {
                If (STCS)
                {
                    Debug = "m00e, Error during update of Target"
                }

                Return (0x01)
            }

            /* Check Source Object value and type is not corrupted after updating the copy */

            Store (Arg6 [0x02], Local7)
            If (M005 (Concatenate (Arg0, "-m005"), Arg3, RefOf (Local1), Local7))
            {
                If (STCS)
                {
                    Debug = "m00e, Source Object has been corrupted during update of Target"
                }
            }

            /* Check auxiliary Target Object to have the initial type and value */

            Store (DerefOf (Arg6 [0x03]) [Arg2], Local7)
            If (M016 (Concatenate (Arg0, "-m016"), Arg2, 0x00, Local7))
            {
                If (STCS)
                {
                    Debug = "m00e, auxiliary Target Object has been corrupted during update of Target"
                }

                Return (0x01)
            }

            Return (0x00)
        }

        /* Prepare Target as Package Element of specified type */

        Method (M013, 4, Serialized)
        {
            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                                /* Only check */
                }
                Case (0x01)
                {
                    CopyObject (DerefOf (Arg3), INT1) /* \M689.INT1 */
                    Arg2 [0x00] = INT1 /* \M689.INT1 */
                }
                Case (0x02)
                {
                    CopyObject (DerefOf (Arg3), STR1) /* \M689.STR1 */
                    Arg2 [0x00] = STR1 /* \M689.STR1 */
                }
                Case (0x03)
                {
                    If (Y136)
                    {
                        CopyObject (DerefOf (Arg3), BUF1) /* \M689.BUF1 */
                    }
                    Else
                    {
                        M687 (DerefOf (Arg3), RefOf (BUF1))
                    }

                    Arg2 [0x00] = BUF1 /* \M689.BUF1 */
                }
                Case (0x04)
                {
                    CopyObject (DerefOf (Arg3), PAC1) /* \M689.PAC1 */
                    Arg2 [0x00] = PAC1 /* \M689.PAC1 */
                }
                Case (0x11)
                {
                    CopyObject (RefOf (ORF1), REF1) /* \M689.REF1 */
                    /*if (y522) { */

                    Arg2 [0x00] = REF1 /* \M689.REF1 */
                                /*} else { */
                /*	Store(DeRefof(REF1), Index(arg2, 0)) */
                /*} */
                }
                /* Unexpected Target Type */

                Default
                {
                    ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg1, 0x00)
                    Return (0x01)
                }

            }

            If (CH03 (Arg0, Z122, __LINE__, 0x00, 0x00))
            {
                /*Exception during preparing of Target Object */

                Return (0x01)
            }

            If ((Arg1 == 0x11))
            {
                /* Reference */

                Return (0x00)
            }

            Local0 = ObjectType (Arg2 [0x00])
            If ((Local0 != Arg1))
            {
                /* ObjectType of Target can not be set up */

                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Local0, Arg1)
                Return (0x01)
            }

            Return (0x00)
        }

        /* Check Target Object type is not corrupted after storing, */
        /* for the computational data types verify its value against */
        /* the Object-initializer value */
        Method (M015, 4, Serialized)
        {
            Name (MMM2, 0x00) /* An auxiliary Object to invoke Method */
            If ((Arg1 == 0x11))
            {
                /* Target object is a reference */
                /* Check that it can be used as reference */
                Local0 = DerefOf (Arg2)
                Local3 = DerefOf (Local0)
                If (CH03 (Arg0, Z122, __LINE__, 0x00, Local0))
                {
                    /* Derefof caused unexpected exception */

                    Return (0x01)
                }
            }
            Else
            {
                Local0 = ObjectType (Arg2)
                If ((Local0 != Arg1))
                {
                    /* ObjectType of Target object is corrupted */

                    ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Local0, Arg1)
                    Return (0x01)
                }
            }

            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    Return (0x00)
                }
                Case (0x01)
                {
                    Local0 = ObjectType (INT1)
                }
                Case (0x02)
                {
                    Local0 = ObjectType (STR1)
                }
                Case (0x03)
                {
                    Local0 = ObjectType (BUF1)
                }
                Case (0x04)
                {
                    Local0 = ObjectType (PAC1)
                }
                Case (0x05)
                {
                    Local0 = 0x05
                }
                Case (0x06)
                {
                    Local0 = ObjectType (DEV1)
                }
                Case (0x07)
                {
                    Local0 = ObjectType (EVE1)
                }
                Case (0x08)
                {
                    Local0 = ObjectType (MMM1)
                }
                Case (0x09)
                {
                    Local0 = ObjectType (MTX1)
                }
                Case (0x0A)
                {
                    Local0 = ObjectType (OPR1)
                }
                Case (0x0B)
                {
                    Local0 = ObjectType (PWR1)
                }
                Case (0x0C)
                {
                    Local0 = ObjectType (CPU1)
                }
                Case (0x0D)
                {
                    Local0 = ObjectType (TZN1)
                }
                Case (0x0E)
                {
                    Local0 = 0x0E
                }
                Case (0x11)
                {
                    /*Store(Derefof(REF1), Local3) */

                    Local3 = REF1 /* \M689.REF1 */
                    If (CH03 (Arg0, Z122, __LINE__, 0x00, Local0))
                    {
                        /* Derefof caused unexpected exception */

                        Return (0x01)
                    }

                    Return (0x00)
                }
                /* Unexpected Result Type */

                Default
                {
                    ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Arg1, 0x00)
                    Return (0x01)
                }

            }

            If ((Local0 != Arg1))
            {
                /* Mismatch of Target Type against the specified one */

                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Local0, Arg1)
                If (STCS)
                {
                    M000 (0x03, 0x01000000, Local0, Arg1)
                }

                Return (0x01)
            }
            Else
            {
                /* Check equality of the Source value to the Object-initializer one */

                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        If ((INT1 != DerefOf (Arg3)))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, INT1, DerefOf (Arg3))
                            Return (0x01)
                        }

                        If ((DerefOf (Arg2) != INT1))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (Arg2), INT1)
                            Return (0x01)
                        }
                    }
                    Case (0x02)
                    {
                        If ((STR1 != DerefOf (Arg3)))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, STR1, DerefOf (Arg3))
                            Return (0x01)
                        }

                        If ((DerefOf (Arg2) != STR1))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (Arg2), STR1)
                            Return (0x01)
                        }
                    }
                    Case (0x03)
                    {
                        If ((BUF1 != DerefOf (Arg3)))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, BUF1, DerefOf (Arg3))
                            Return (0x01)
                        }

                        If ((DerefOf (Arg2) != BUF1))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (Arg2), BUF1)
                            Return (0x01)
                        }
                    }
                    Case (0x04)
                    {
                        Local0 = SizeOf (PAC1)
                        If ((SizeOf (Arg3) != Local0))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, SizeOf (Arg3), Local0)
                            Return (0x01)
                        }

                        While (Local0)
                        {
                            Local0--
                            Local1 = ObjectType (DerefOf (DerefOf (Arg3) [Local0]))
                            Local2 = ObjectType (DerefOf (PAC1 [Local0]))
                            If ((Local1 != Local2))
                            {
                                /* ObjectType is corrupted */

                                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Local1, Local2)
                                Return (0x01)
                            }
                            ElseIf (DerefOf (B679 [Local1]))
                            {
                                /* the computational data type */

                                If ((DerefOf (DerefOf (Arg3) [Local0]) != DerefOf (PAC1 [
                                    Local0])))
                                {
                                    /* The value is corrupted */

                                    ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (DerefOf (Arg3) [Local0]),
                                        Local0)
                                    Return (0x01)
                                }
                            }
                        }

                        Local0 = SizeOf (PAC1)
                        If ((SizeOf (Arg2) != Local0))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, SizeOf (Arg2), Local0)
                            Return (0x01)
                        }

                        While (Local0)
                        {
                            Local0--
                            Local1 = ObjectType (DerefOf (DerefOf (Arg2) [Local0]))
                            Local2 = ObjectType (DerefOf (PAC1 [Local0]))
                            If ((Local1 != Local2))
                            {
                                /* ObjectType is corrupted */

                                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Local1, Local2)
                                Return (0x01)
                            }
                            ElseIf (DerefOf (B679 [Local1]))
                            {
                                /* the computational data type */

                                If ((DerefOf (DerefOf (Arg2) [Local0]) != DerefOf (PAC1 [
                                    Local0])))
                                {
                                    /* The value is corrupted */

                                    ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (DerefOf (Arg2) [Local0]),
                                        Local0)
                                    Return (0x01)
                                }
                            }
                        }
                    }
                    Case (0x05)
                    {
                        If ((DerefOf (Arg2) != DerefOf (Arg3)))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (Arg2), DerefOf (Arg3))
                            Return (0x01)
                        }
                    }
                    Case (0x08)
                    {
                        CopyObject (DerefOf (Arg2), MMM2) /* \M689.M015.MMM2 */
                        If ((MMM2 != MMM1))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, MMM2, MMM1)
                            Return (0x01)
                        }
                    }
                    Case (0x0E)
                    {
                        If ((DerefOf (Arg2) != DerefOf (Arg3)))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (Arg2), DerefOf (Arg3))
                            Return (0x01)
                        }
                    }

                }
            }

            Return (0x00)
        }

        /* Check auxiliary Target Named Object type is not corrupted, */
        /* for the computational data types verify its value against */
        /* the Object-initializer value */
        Method (M016, 4, Serialized)
        {
            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    Return (0x00)
                }
                Case (0x01)
                {
                    Local0 = ObjectType (INT1)
                }
                Case (0x02)
                {
                    Local0 = ObjectType (STR1)
                }
                Case (0x03)
                {
                    Local0 = ObjectType (BUF1)
                }
                Case (0x04)
                {
                    Local0 = ObjectType (PAC1)
                }
                Case (0x05)
                {
                    Local0 = 0x05
                }
                Case (0x06)
                {
                    Local0 = ObjectType (DEV1)
                }
                Case (0x07)
                {
                    Local0 = ObjectType (EVE1)
                }
                Case (0x08)
                {
                    Local0 = ObjectType (MMM1)
                }
                Case (0x09)
                {
                    Local0 = ObjectType (MTX1)
                }
                Case (0x0A)
                {
                    Local0 = ObjectType (OPR1)
                }
                Case (0x0B)
                {
                    Local0 = ObjectType (PWR1)
                }
                Case (0x0C)
                {
                    Local0 = ObjectType (CPU1)
                }
                Case (0x0D)
                {
                    Local0 = ObjectType (TZN1)
                }
                Case (0x0E)
                {
                    Local0 = 0x0E
                }
                Case (0x11)
                {
                    /*Store(Derefof(REF1), Local3) */

                    Local3 = REF1 /* \M689.REF1 */
                    If (CH03 (Arg0, Z122, __LINE__, 0x00, 0x00))
                    {
                        /* Derefof caused unexpected exception */

                        Return (0x01)
                    }

                    Return (0x00)
                }
                /* Unexpected Result Type */

                Default
                {
                    ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Arg1, 0x00)
                    Return (0x01)
                }

            }

            If ((Local0 != Arg1))
            {
                /* Mismatch of Target Type against the specified one */

                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Local0, Arg1)
                If (STCS)
                {
                    M000 (0x03, 0x01000000, Local0, Arg1)
                }

                Return (0x01)
            }
            Else
            {
                /* Check equality of the Source value to the Object-initializer one */

                Switch (ToInteger (Arg1))
                {
                    Case (0x01)
                    {
                        If ((INT1 != DerefOf (Arg3)))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, INT1, DerefOf (Arg3))
                            Return (0x01)
                        }
                    }
                    Case (0x02)
                    {
                        If ((STR1 != DerefOf (Arg3)))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, STR1, DerefOf (Arg3))
                            Return (0x01)
                        }
                    }
                    Case (0x03)
                    {
                        If ((BUF1 != DerefOf (Arg3)))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, BUF1, DerefOf (Arg3))
                            Return (0x01)
                        }
                    }
                    Case (0x04)
                    {
                        Local0 = SizeOf (PAC1)
                        If ((SizeOf (Arg3) != Local0))
                        {
                            ERR (Arg0, Z122, __LINE__, 0x00, 0x00, SizeOf (Arg3), Local0)
                            Return (0x01)
                        }

                        While (Local0)
                        {
                            Local0--
                            Local1 = ObjectType (DerefOf (DerefOf (Arg3) [Local0]))
                            Local2 = ObjectType (DerefOf (PAC1 [Local0]))
                            If ((Local1 != Local2))
                            {
                                /* ObjectType is corrupted */

                                ERR (Arg0, Z122, __LINE__, 0x00, 0x00, Local1, Local2)
                                Return (0x01)
                            }
                            ElseIf (DerefOf (B679 [Local1]))
                            {
                                /* the computational data type */

                                If ((DerefOf (DerefOf (Arg3) [Local0]) != DerefOf (PAC1 [
                                    Local0])))
                                {
                                    /* The value is corrupted */

                                    ERR (Arg0, Z122, __LINE__, 0x00, 0x00, DerefOf (DerefOf (Arg3) [Local0]),
                                        Local0)
                                    Return (0x01)
                                }
                            }
                        }
                    }

                }
            }

            Return (0x00)
        }

        /* Update the first element of specified Package */
        /* m017(<msg>, <Package>) */
        Method (M017, 2, NotSerialized)
        {
            Local0 = ObjectType (Arg1 [0x00])
            If (DerefOf (B66F [Local0]))
            {
                /* Can be used in Index Operator */

                Local1 = SizeOf (Arg1 [0x00])
                If (Local1)
                {
                    /* Update the last Member Object */

                    Local1--
                    Local2 = DerefOf (Arg1 [0x00]) [Local1]
                    Local3 = RefOf (Local2)
                    Local4 = DerefOf (Local2)
                    If ((ObjectType (Local4) == 0x01))
                    {
                        /* Integer */

                        Store (~Local4, DerefOf (Local3))
                    }
                    Else
                    {
                        DerefOf (Local3) = Ones
                        If (CH03 (Arg0, Z122, __LINE__, 0x00, Arg1 [0x00]))
                        {
                            /* Store caused unexpected exception */

                            Return (0x01)
                        }
                    }

                    If (Local1)
                    {
                        /* Update the First Member Object */

                        Local2 = DerefOf (Arg1 [0x00]) [0x00]
                        Local4 = DerefOf (Local2)
                        If ((ObjectType (Local4) == 0x01))
                        {
                            /* Integer */

                            Store (~Local4, DerefOf (Local3))
                        }
                        Else
                        {
                            DerefOf (Local3) = Ones
                            If (CH03 (Arg0, Z122, __LINE__, 0x00, Arg1 [0x00]))
                            {
                                /* Store caused unexpected exception */

                                Return (0x01)
                            }
                        }
                    }
                }
                ElseIf ((Local0 == 0x04))
                {
                    /* Empty Package */

                    Arg1 [0x00] = Package (0x01)
                        {
                            "update string"
                        }
                }
                Else
                {
                    /* Empty String/Buffer */

                    Arg1 [0x00] = "update string"
                }
            }
            ElseIf (DerefOf (B674 [Local0]))
            {
                /* Non-Computational Data Objects */

                Arg1 [0x00] = "update string"
            }
            Else
            {
                Store (~ToInteger (DerefOf (Arg1 [0x00])), Arg1 [
                    0x00])
            }

            If (CH03 (Arg0, Z122, __LINE__, 0x00, Arg1 [0x00]))
            {
                /* Update caused unexpected exception */

                Return (0x01)
            }

            Return (0x00)
        }

        /* Test data packages for each type of the Result Object */
        /* Empty Package */
        Name (P000, Package (0x12){})
        /* Target Objects initial values for common use */

        Name (P001, Package (0x12)
        {
            0x00,
            0xFEDCBA9876543211,
            "target string",
            Buffer (0x11)
            {
                /* 0000 */  0xC3, 0xC4, 0xC5, 0x00, 0xC6, 0xC7, 0xC8, 0xC9,  // ........
                /* 0008 */  0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF, 0xC0, 0xC1,  // ........
                /* 0010 */  0xC2                                             // .
            },

            Package (0x02)
            {
                "target package",
                0xFEDCBA9876543210
            },

            Buffer (0x09)
            {
                /* 0000 */  0x9A, 0x8A, 0x7A, 0x6A, 0x5A, 0x4A, 0x3A, 0x2A,  // ..zjZJ:*
                /* 0008 */  0x1A                                             // .
            },

            0x00,
            0x00,
            Package (0x02)
            {
                MMMY,
                "ff0Y"
            },

            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            Buffer (0x09)
            {
                /* 0000 */  0x9A, 0x8A, 0x7A, 0x6A, 0x5A, 0x4A, 0x3A, 0x2A,  // ..zjZJ:*
                /* 0008 */  0x1A                                             // .
            },

            0x00,
            0x00,
            0x00
        })
        /* Uninitialized */

        Name (P002, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x00,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            0x00,
            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            0x00,
            /* Benchmark Result object converted to Target type values */

            P000
        })
        /* Integer */

        Name (P132, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x01,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            0xFEDCBA9876543210,
            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            0xFEDCBA9876543210,
            /* Benchmark Result object converted to Target type values */

            Package (0x12)
            {
                0x00,
                0xFEDCBA9876543210,
                "76543210",
                Buffer (0x11)
                {
                     0x10, 0x32, 0x54, 0x76                           // .2Tv
                },

                0x00,
                Buffer (0x09)
                {
                     0x10, 0x32, 0x54, 0x76                           // .2Tv
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                     0x10, 0x32, 0x54, 0x76                           // .2Tv
                },

                0x00,
                0x00,
                0x00
            }
        })
        Name (P164, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x01,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            0xFEDCBA9876543210,
            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            0xFEDCBA9876543210,
            /* Benchmark Result object converted to Target type values */

            Package (0x12)
            {
                0x00,
                0xFEDCBA9876543210,
                "FEDCBA9876543210",
                Buffer (0x11)
                {
                     0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE   // .2Tv....
                },

                0x00,
                Buffer (0x09)
                {
                     0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE   // .2Tv....
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                     0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE   // .2Tv....
                },

                0x00,
                0x00,
                0x00
            }
        })
        /* String */

        Name (P201, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x02,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            "\x01",
            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            "\x01",
            /* Benchmark Result object converted to Target type values */

            Package (0x12)
            {
                0x00,
                0x00,
                "\x01",
                Buffer (0x11)
                {
                     0x01                                             // .
                },

                0x00,
                Buffer (0x09)
                {
                     0x01                                             // .
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                     0x01                                             // .
                },

                0x00,
                0x00,
                0x00
            }
        })
        Name (P202, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x02,
            /* Number of different initial values */

            0x02,
            /* SRC0 initial value */

            "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*",
            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*",
            /* Benchmark Result object converted to Target type values */

            Package (0x12)
            {
                0x00,
                0x00,
                "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*",
                Buffer (0x11)
                {
                    /* 0000 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
                    /* 0008 */  0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30,  // )*+,-./0
                    /* 0010 */  0x31                                             // 1
                },

                0x00,
                Buffer (0x09)
                {
                    /* 0000 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
                    /* 0008 */  0x09                                             // .
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                    /* 0000 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
                    /* 0008 */  0x09                                             // .
                },

                0x00,
                0x00,
                0x00
            }
        })
        Name (P232, Package (0x05)
        {
            /* Type of the Result(Source) Object */

            0x02,
            /* Number of different initial values */

            0x02,
            Package (0x06)
            {
                /* Type of the Result(Source) Object */

                0x03,
                /* Number of different initial values */

                0x00,
                /* SRC0 initial value */

                "fedcba98 string",
                /* Target Objects initial values */

                P001,
                /* Benchmark Result object value */

                "fedcba98 string",
                /* Benchmark Result object converted to Target type values */

                Package (0x12)
                {
                    0x00,
                    0xFEDCBA98,
                    "fedcba98 string",
                    Buffer (0x11)
                    {
                        /* 0000 */  0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38,  // fedcba98
                        /* 0008 */  0x20, 0x73, 0x74, 0x72, 0x69, 0x6E, 0x67         //  string
                    },

                    0x00,
                    Buffer (0x09)
                    {
                         0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38   // fedcba98
                    },

                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    Buffer (0x09)
                    {
                         0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38   // fedcba98
                    },

                    0x00,
                    0x00,
                    0x00
                }
            },

            P201,
            P202
        })
        Name (P264, Package (0x05)
        {
            /* Type of the Result(Source) Object */

            0x02,
            /* Number of different initial values */

            0x03,
            Package (0x06)
            {
                /* Type of the Result(Source) Object */

                0x02,
                /* Number of different initial values */

                0x00,
                /* SRC0 initial value */

                "fedcba9876543210 string",
                /* Target Objects initial values */

                P001,
                /* Benchmark Result object value */

                "fedcba9876543210 string",
                /* Benchmark Result object converted to Target type values */

                Package (0x12)
                {
                    0x00,
                    0xFEDCBA9876543210,
                    "fedcba9876543210 string",
                    Buffer (0x11)
                    {
                        /* 0000 */  0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38,  // fedcba98
                        /* 0008 */  0x37, 0x36, 0x35, 0x34, 0x33, 0x32, 0x31, 0x30,  // 76543210
                        /* 0010 */  0x20                                             //
                    },

                    0x00,
                    Buffer (0x09)
                    {
                        /* 0000 */  0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38,  // fedcba98
                        /* 0008 */  0x17                                             // .
                    },

                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    Buffer (0x09)
                    {
                        /* 0000 */  0x66, 0x65, 0x64, 0x63, 0x62, 0x61, 0x39, 0x38,  // fedcba98
                        /* 0008 */  0x17                                             // .
                    },

                    0x00,
                    0x00,
                    0x00
                }
            },

            P201,
            P202
        })
        /* Buffer */

        Name (P301, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x03,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            Buffer (0x43)
            {
                /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                /* 0008 */  0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10,  // ........
                /* 0010 */  0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,  // ........
                /* 0018 */  0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20,  // .......
                /* 0020 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
                /* 0028 */  0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30,  // )*+,-./0
                /* 0030 */  0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38,  // 12345678
                /* 0038 */  0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40,  // 9:;<=>?@
                /* 0040 */  0x41, 0x42, 0x43                                 // ABC
            },

            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            Buffer (0x43)
            {
                /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                /* 0008 */  0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10,  // ........
                /* 0010 */  0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,  // ........
                /* 0018 */  0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20,  // .......
                /* 0020 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
                /* 0028 */  0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30,  // )*+,-./0
                /* 0030 */  0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38,  // 12345678
                /* 0038 */  0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40,  // 9:;<=>?@
                /* 0040 */  0x41, 0x42, 0x43                                 // ABC
            },

            /* Benchmark Result object converted to Target type values */

            Package (0x12)
            {
                0x00,
                0x0807060504030201,
                "01 02 03 04 05 06 07 08 09 0A 0B 0C 0D 0E 0F 10 11 12 13 14 15 16 17 18 19 1A 1B 1C 1D 1E 1F 20 21 22 23 24 25 26 27 28 29 2A 2B 2C 2D 2E 2F 30 31 32 33 34 35 36 37 38 39 3A 3B 3C 3D 3E 3F 40 41 42 43",
                Buffer (0x11)
                {
                    /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                    /* 0008 */  0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10,  // ........
                    /* 0010 */  0x11                                             // .
                },

                0x00,
                Buffer (0x09)
                {
                    /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                    /* 0008 */  0x09                                             // .
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                    /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                    /* 0008 */  0x09                                             // .
                },

                0x00,
                0x00,
                0x00
            }
        })
        Name (P300, Package (0x04)
        {
            /* Type of the Result(Source) Object */

            0x03,
            /* Number of different initial values */

            0x02,
            Package (0x06)
            {
                /* Type of the Result(Source) Object */

                0x03,
                /* Number of different initial values */

                0x00,
                /* SRC0 initial value */

                Buffer (0x09)
                {
                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                    /* 0008 */  0x88                                             // .
                },

                /* Target Objects initial values */

                P001,
                /* Benchmark Result object value */

                Buffer (0x09)
                {
                    /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                    /* 0008 */  0x88                                             // .
                },

                /* Benchmark Result object converted to Target type values */

                Package (0x12)
                {
                    0x00,
                    0xF1F2F3F4F5F6F7F8,
                    "F8 F7 F6 F5 F4 F3 F2 F1 88",
                    Buffer (0x11)
                    {
                        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                        /* 0008 */  0x88                                             // .
                    },

                    0x00,
                    Buffer (0x09)
                    {
                        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                        /* 0008 */  0x08                                             // .
                    },

                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    Buffer (0x09)
                    {
                        /* 0000 */  0xF8, 0xF7, 0xF6, 0xF5, 0xF4, 0xF3, 0xF2, 0xF1,  // ........
                        /* 0008 */  0x08                                             // .
                    },

                    0x00,
                    0x00,
                    0x00
                }
            },

            P301
        })
        /* Package */

        Name (P401, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x04,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            Package (0x01)
            {
                "test p401 package"
            },

            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            Package (0x01)
            {
                "test p401 package"
            },

            /* Benchmark Result object converted to Target type values */

            Package (0x12)
            {
                0x00,
                0x00,
                0x00,
                0x00,
                Package (0x01)
                {
                    "test p401 package"
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00
            }
        })
        Name (P400, Package (0x04)
        {
            /* Type of the Result(Source) Object */

            0x04,
            /* Number of different initial values */

            0x02,
            Package (0x06)
            {
                /* Type of the Result(Source) Object */

                0x04,
                /* Number of different initial values */

                0x00,
                /* SRC0 initial value */

                Package (0x03)
                {
                    0xFEDCBA987654321F,
                    "test package",
                    Buffer (0x09)
                    {
                        /* 0000 */  0x13, 0x12, 0x11, 0x10, 0x0F, 0x0E, 0x0D, 0x0C,  // ........
                        /* 0008 */  0x0B                                             // .
                    }
                },

                /* Target Objects initial values */

                P001,
                /* Benchmark Result object value */

                Package (0x03)
                {
                    0xFEDCBA987654321F,
                    "test package",
                    Buffer (0x09)
                    {
                        /* 0000 */  0x13, 0x12, 0x11, 0x10, 0x0F, 0x0E, 0x0D, 0x0C,  // ........
                        /* 0008 */  0x0B                                             // .
                    }
                },

                /* Benchmark Result object converted to Target type values */

                Package (0x12)
                {
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    Package (0x03)
                    {
                        0xFEDCBA987654321F,
                        "test package",
                        Buffer (0x09)
                        {
                            /* 0000 */  0x13, 0x12, 0x11, 0x10, 0x0F, 0x0E, 0x0D, 0x0C,  // ........
                            /* 0008 */  0x0B                                             // .
                        }
                    },

                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x00
                }
            },

            P401
        })
        /* Field Unit */

        Name (P500, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x05,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            Package (0x02)
            {
                0x00,
                Buffer (0x09)
                {
                    /* 0000 */  0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25,  // ..ueUE5%
                    /* 0008 */  0x15                                             // .
                }
            },

            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            Buffer (0x09)
            {
                /* 0000 */  0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25,  // ..ueUE5%
                /* 0008 */  0x15                                             // .
            },

            /* Benchmark Result object converted to Target type values */

            Package (0x12)
            {
                0x00,
                0x2535455565758595,
                "95 85 75 65 55 45 35 25 15",
                Buffer (0x11)
                {
                    /* 0000 */  0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25,  // ..ueUE5%
                    /* 0008 */  0x15                                             // .
                },

                0x00,
                Buffer (0x09)
                {
                    /* 0000 */  0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25,  // ..ueUE5%
                    /* 0008 */  0x15                                             // .
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                    /* 0000 */  0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25,  // ..ueUE5%
                    /* 0008 */  0x15                                             // .
                },

                0x00,
                0x00,
                0x00
            }
        })
        /* Device */

        Name (P600, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x06,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            Buffer (0x02)
            {
                 0x79, 0x00                                       // y.
            },

            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            0x00,
            /* Benchmark Result object converted to Target type values */

            P000
        })
        /* Event */

        Name (P700, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x07,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            0x00,
            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            0x00,
            /* Benchmark Result object converted to Target type values */

            P000
        })
        /* Method */

        Name (P800, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x08,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            Package (0x02)
            {
                MMMX,
                "ff0X"
            },

            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            "ff0X",
            /* Benchmark Result object converted to Target type values */

            Package (0x12)
            {
                0x00,
                0x0FF0,
                "ff0X",
                Buffer (0x11)
                {
                     0x66, 0x66, 0x30, 0x58                           // ff0X
                },

                0x00,
                Buffer (0x09)
                {
                     0x66, 0x66, 0x30, 0x58                           // ff0X
                },

                0x00,
                0x00,
                "ff0X",
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                     0x66, 0x66, 0x30, 0x58                           // ff0X
                },

                0x00,
                0x00,
                0x00
            }
        })
        /* Mutex */

        Name (P900, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x09,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            0x00,
            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            0x00,
            /* Benchmark Result object converted to Target type values */

            P000
        })
        /* Operation Region */

        Name (PA00, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x0A,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            0x00,
            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            0x00,
            /* Benchmark Result object converted to Target type values */

            P000
        })
        /* Power Resource */

        Name (PB00, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x0B,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            0x00,
            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            0x00,
            /* Benchmark Result object converted to Target type values */

            P000
        })
        /* Processor */

        Name (PC00, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x0C,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            0x00,
            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            0x00,
            /* Benchmark Result object converted to Target type values */

            P000
        })
        /* Thermal Zone */

        Name (PD00, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x0D,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            0x00,
            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            0x00,
            /* Benchmark Result object converted to Target type values */

            P000
        })
        /* Buffer Field */

        Name (PE00, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x0E,
            /* Number of different initial values */

            0x00,
            /* SRC0 initial value */

            Package (0x02)
            {
                0x00,
                Buffer (0x09)
                {
                    /* 0000 */  0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25,  // ..ueUE5%
                    /* 0008 */  0x15                                             // .
                }
            },

            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            Buffer (0x09)
            {
                /* 0000 */  0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25,  // ..ueUE5%
                /* 0008 */  0x15                                             // .
            },

            /* Benchmark Result object converted to Target type values */

            Package (0x12)
            {
                0x00,
                0x2535455565758595,
                "95 85 75 65 55 45 35 25 15",
                Buffer (0x11)
                {
                    /* 0000 */  0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25,  // ..ueUE5%
                    /* 0008 */  0x15                                             // .
                },

                0x00,
                Buffer (0x09)
                {
                    /* 0000 */  0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25,  // ..ueUE5%
                    /* 0008 */  0x15                                             // .
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                    /* 0000 */  0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25,  // ..ueUE5%
                    /* 0008 */  0x15                                             // .
                },

                0x00,
                0x00,
                0x00
            }
        })
        Name (PE01, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x0E,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            Package (0x02)
            {
                0x01,
                Buffer (0x08)
                {
                     0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25   // ..ueUE5%
                }
            },

            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            Buffer (0x08)
            {
                 0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25   // ..ueUE5%
            },

            /* Benchmark Result object converted to Target type values */

            Package (0x12)
            {
                0x00,
                0x2535455565758595,
                "95 85 75 65 55 45 35 25",
                Buffer (0x11)
                {
                     0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25   // ..ueUE5%
                },

                0x00,
                Buffer (0x09)
                {
                     0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25   // ..ueUE5%
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                     0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25   // ..ueUE5%
                },

                0x00,
                0x00,
                0x00
            }
        })
        Name (PE02, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x0E,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            Package (0x02)
            {
                0x01,
                Buffer (0x08)
                {
                     0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25   // ..ueUE5%
                }
            },

            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            0x2535455565758595,
            /* Benchmark Result object converted to Target type values */

            Package (0x12)
            {
                0x00,
                0x2535455565758595,
                "2535455565758595",
                Buffer (0x11)
                {
                     0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25   // ..ueUE5%
                },

                0x00,
                Buffer (0x09)
                {
                     0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25   // ..ueUE5%
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                     0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25   // ..ueUE5%
                },

                0x00,
                0x00,
                0x00
            }
        })
        Name (PE03, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x0E,
            /* Number of different initial values */

            0x02,
            /* SRC0 initial value */

            Package (0x02)
            {
                0x02,
                Buffer (0x04)
                {
                     0x95, 0x85, 0x75, 0x65                           // ..ue
                }
            },

            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            Buffer() {0x95, 0x85, 0x75, 0x65},
            /* Benchmark Result object converted to Target type values */

            Package (0x12)
            {
                0x00,
                Buffer() {0x95, 0x85, 0x75, 0x65},
                "65758595",
                Buffer (0x11)
                {
                     0x95, 0x85, 0x75, 0x65                           // ..ue
                },

                0x00,
                Buffer (0x09)
                {
                     0x95, 0x85, 0x75, 0x65                           // ..ue
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                     0x95, 0x85, 0x75, 0x65                           // ..ue
                },

                0x00,
                0x00,
                0x00
            }
        })
        Name (PE04, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x0E,
            /* Number of different initial values */

            0x02,
            /* SRC0 initial value */

            Package (0x02)
            {
                0x02,
                Buffer (0x04)
                {
                     0x95, 0x85, 0x75, 0x65                           // ..ue
                }
            },

            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            Buffer() {0x95, 0x85, 0x75, 0x65},
            /* Benchmark Result object converted to Target type values */

            Package (0x12)
            {
                0x00,
                Buffer() {0x95, 0x85, 0x75, 0x65},
                "0000000065758595",
                Buffer (0x11)
                {
                     0x95, 0x85, 0x75, 0x65                           // ..ue
                },

                0x00,
                Buffer (0x09)
                {
                     0x95, 0x85, 0x75, 0x65                           // ..ue
                },

                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                0x00,
                Buffer (0x09)
                {
                     0x95, 0x85, 0x75, 0x65                           // ..ue
                },

                0x00,
                0x00,
                0x00
            }
        })
        Name (PE32, Package (0x05)
        {
            /* Type of the Result(Source) Object */

            0x0E,
            /* Number of different initial values */

            0x03,
            /* Data */

            PE00,
            PE01,
            PE03
        })
        Name (PE64, Package (0x05)
        {
            /* Type of the Result(Source) Object */

            0x0E,
            /* Number of different initial values */

            0x03,
            /* Data */

            PE00,
            PE02,
            PE04
        })
        /* DDB Handle */

        Name (PF00, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x0F,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            0x00,
            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            0x00,
            /* Benchmark Result object converted to Target type values */

            P000
        })
        /* Debug */

        Name (PG00, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x10,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            0x00,
            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            0x00,
            /* Benchmark Result object converted to Target type values */

            P000
        })
        /* Reference */

        Name (PH00, Package (0x06)
        {
            /* Type of the Result(Source) Object */

            0x11,
            /* Number of different initial values */

            0x01,
            /* SRC0 initial value */

            0x00,
            /* Target Objects initial values */

            P001,
            /* Benchmark Result object value */

            0x00,
            /* Benchmark Result object converted to Target type values */

            P000
        })
        Name (P320, Package (0x12)
        {
            P002,
            P132,
            P232,
            P300,
            P400,
            P500,
            P600,
            P700,
            P800,
            P900,
            PA00,
            PB00,
            PC00,
            PD00,
            PE32,
            PF00,
            PG00,
            PH00
        })
        Name (P640, Package (0x12)
        {
            P002,
            P164,
            P264,
            P300,
            P400,
            P500,
            P600,
            P700,
            P800,
            P900,
            PA00,
            PB00,
            PC00,
            PD00,
            PE64,
            PF00,
            PG00,
            PH00
        })
        /* m020(<msg>, <store op>, <exc. conditions>, */
        /*      <Target scale>, <Result scale>, <kind of Source-Target pair>) */
        Method (M020, 6, Serialized)
        {
            /* Initialize statistics */

            M001 ()
            Name (SCL0, Buffer (0x12)
            {
                /* 0000 */  0x00, 0x01, 0x01, 0x01, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0010 */  0x00, 0x00                                       // ..
            })
            Name (LPN0, 0x12)
            Name (LPC0, 0x00)
            Name (LPN1, 0x00)
            Name (LPC1, 0x00)
            Name (LPN2, 0x00)
            Name (LPC2, 0x00)
            SRMT (Arg0)
            If ((Arg1 > 0x01))
            {
                /* Unexpected Kind of Op (0 - Store, ...) */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg1, 0x00)
                Return (0x01)
            }

            If ((Arg5 > 0x06))
            {
                /* Unexpected Kind of Source-Target pair */

                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg5, 0x00)
                Return (0x01)
            }

            /* Flags of Store from and to Named to check */
            /* exceptional conditions on storing */
            If (Arg1)
            {
                Local0 = 0x00
                Local1 = 0x00
            }
            Else
            {
                Local0 = ((Arg5 == 0x00) || (Arg5 == 0x01))
                Local0 = (Local0 || (Arg5 == 0x04))
                Local0 = (Local0 || (Arg5 == 0x05))
                Local1 = ((Arg5 == 0x00) || (Arg5 == 0x02))
            }

            /* Enumerate Target types */

            While (LPN0)
            {
                If ((DerefOf (B670 [LPC0]) && DerefOf (Arg3 [LPC0])))
                {
                    /* Not invalid type of the Target Object to store in */

                    LPN1 = 0x12
                    LPC1 = 0x00
                    /* Enumerate Source types */

                    While (LPN1)
                    {
                        If ((DerefOf (B671 [LPC1]) && DerefOf (Arg4 [LPC1])))
                        {
                            /* Not invalid type of the result Object to be stored */

                            If (Arg2)
                            {
                                /* Skip cases without exceptional conditions */

                                If (!M685 (Arg1, LPC0, LPC1, Local0, Local1))
                                {
                                    LPN1--
                                    LPC1++
                                    Continue
                                }
                            }
                            ElseIf                            /* Skip cases with exceptional conditions */

 (M685 (Arg1, LPC0, LPC1, Local0, Local1))
                            {
                                LPN1--
                                LPC1++
                                Continue
                            }

                            If (F64)
                            {
                                Local2 = DerefOf (P640 [LPC1])
                            }
                            Else
                            {
                                Local2 = DerefOf (P320 [LPC1])
                            }

                            Local3 = DerefOf (Local2 [0x00])
                            If ((Local3 != LPC1))
                            {
                                /* Unexpected data package */

                                ERR (Concatenate (Arg0, TERR), Z122, __LINE__, 0x00, 0x00, Arg1, LPC1)
                                Return (0x01)
                            }

                            Local3 = DerefOf (Local2 [0x01])
                            LPN2 = Local3
                            LPC2 = 0x00
                            /* Enumerate Result values */

                            While (LPN2)
                            {
                                If ((Local3 > 0x01))
                                {
                                    /* Complex test data */

                                    Local4 = Local2 [(LPC2 + 0x02)]
                                }
                                Else
                                {
                                    Local4 = RefOf (Local2)
                                }

                                If ((Arg5 == 0x00))
                                {
                                    /* Named-Named */

                                    M008 (Concatenate (Arg0, "-m008"), 0x00, LPC0, LPC1, Arg1, Arg2, DerefOf (Local4))
                                }
                                ElseIf ((Arg5 == 0x01))
                                {
                                    /* Named-LocalX */

                                    M009 (Concatenate (Arg0, "-m009"), 0x00, LPC0, LPC1, Arg1, Arg2, DerefOf (Local4))
                                }
                                ElseIf ((Arg5 == 0x02))
                                {
                                    /* LocalX-Named */

                                    M00A (Concatenate (Arg0, "-m00a"), 0x00, LPC0, LPC1, Arg1, Arg2, DerefOf (Local4))
                                }
                                ElseIf ((Arg5 == 0x03))
                                {
                                    /* LocalX-LocalX */

                                    M00B (Concatenate (Arg0, "-m00b"), 0x00, LPC0, LPC1, Arg1, Arg2, DerefOf (Local4))
                                }
                                ElseIf ((Arg5 == 0x04))
                                {
                                    /* Named-ArgX(Named read-only) */

                                    M00C (Concatenate (Arg0, "-m00c"), 0x00, LPC0, LPC1, Arg1, Arg2, DerefOf (Local4))
                                }
                                ElseIf ((Arg5 == 0x05))
                                {
                                    /* Named-ArgX(Named by reference) */

                                    If (Y900)
                                    {
                                        If (((LPC1 == 0x04) &&                                                 /* Target type is 1-3 */

DerefOf (Index (Buffer (0x12)
                                                        {
                                                            /* 0000 */  0x00, 0x01, 0x01, 0x01, 0x00, 0x00, 0x00, 0x00,  // ........
                                                            /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                                                            /* 0010 */  0x00, 0x00                                       // ..
                                                        }, LPC0))))
                                        {
                                            If (Y366)
                                            {
                                                M00D (Concatenate (Arg0, "-m00d"), 0x00, LPC0, LPC1, Arg1, Arg2, DerefOf (Local4))
                                            }
                                        }
                                        Else
                                        {
                                            M00D (Concatenate (Arg0, "-m00d"), 0x00, LPC0, LPC1, Arg1, Arg2, DerefOf (Local4))
                                        }
                                    }
                                    ElseIf                                    /* if (y900) */

 (((LPC1 == 0x04) &&                                             /* Target type is 1-3 */

DerefOf (SCL0 [LPC0])))
                                    {
                                        If (Y366)
                                        {
                                            M00D (Concatenate (Arg0, "-m00d"), 0x00, LPC0, LPC1, Arg1, Arg2, DerefOf (Local4))
                                        }
                                    }
                                    Else
                                    {
                                        M00D (Concatenate (Arg0, "-m00d"), 0x00, LPC0, LPC1, Arg1, Arg2, DerefOf (Local4))
                                    }
                                }
                                ElseIf ((Arg5 == 0x06))
                                {
                                    /* LocalX-Element of Package */

                                    M00E (Concatenate (Arg0, "-m00e"), 0x00, LPC0, LPC1, Arg1, Arg2, DerefOf (Local4))
                                }

                                LPN2--
                                LPC2++
                            }
                        }

                        LPN1--
                        LPC1++
                    }
                }

                LPN0--
                LPC0++
            }

            /* Output statistics */

            M002 (Concatenate (DerefOf (PAC5 [Arg5]), DerefOf (PAC4 [Arg1])
                ))
            Return (0x00)
        }

        Concatenate (Arg0, "-m020", Arg0)
        /* Named-Named */

        M020 (Concatenate (Arg0, "-NN"), Arg1, Arg2, B676, B676, 0x00) // TODO:
        /* Named-LocalX */

        M020 (Concatenate (Arg0, "-NL"), Arg1, Arg2, B677, B676, 0x01) // TODO:
        /* LocalX-Named */

        M020 (Concatenate (Arg0, "-LN"), Arg1, Arg2, B676, B677, 0x02)
        /* LocalX-LocalX */

        M020 (Concatenate (Arg0, "-LL"), Arg1, Arg2, B677, B677, 0x03)
        /* Named-ArgX(Named read-only) */

        M020 (Concatenate (Arg0, "-NA-RO"), Arg1, Arg2, B676, B676, 0x04) // TODO:
        /* Named-ArgX(Named by reference) */

        M020 (Concatenate (Arg0, "-NA-REF"), Arg1, Arg2, B676, B676, 0x05) // TODO:
        /* LocalX-Element of Package */

        If ((Arg1 == 0x00))
        {
            M020 (Concatenate (Arg0, "-LP"), Arg1, Arg2, B67D, B677, 0x06)
        }
    }
