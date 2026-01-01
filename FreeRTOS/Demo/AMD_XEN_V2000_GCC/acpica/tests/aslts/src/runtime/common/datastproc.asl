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
     * Methods applied to the Standard Data
     */
    Name (Z115, 0x73)
    /* Check original values */
    /* arg0 - test name */
    /* arg1 - Integer, original object */
    /* arg2 - absolute index of file initiating the checking */
    /* arg3 - line number of checking (inside the file) */
    Method (M380, 4, NotSerialized)
    {
        Local0 = ObjectType (Arg1)
        If ((Local0 != C009))
        {
            ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Local0, C009)
        }
        ElseIf ((Arg1 != 0x77))
        {
            ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Arg1, 0x77)
        }
    }

    /* arg0 - test name */
    /* arg1 - String, original object */
    /* arg2 - absolute index of file initiating the checking */
    /* arg3 - line number of checking (inside the file) */
    Method (M381, 4, NotSerialized)
    {
        Local0 = ObjectType (Arg1)
        If ((Local0 != C00A))
        {
            ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Local0, C00A)
        }
        ElseIf ((Arg1 != "qwer0000"))
        {
            ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Arg1, "qwer0000")
        }
    }

    /* arg0 - test name */
    /* arg1 - Buffer, original object */
    /* arg2 - absolute index of file initiating the checking */
    /* arg3 - line number of checking (inside the file) */
    Method (M382, 4, NotSerialized)
    {
        Local0 = ObjectType (Arg1)
        If ((Local0 != C00B))
        {
            ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Local0, C00B)
        }
        ElseIf ((Arg1 != Buffer (0x04)
                    {
                         0x01, 0x77, 0x03, 0x04                           // .w..
                    }))
        {
            ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Arg1, Buffer (0x04)
                {
                     0x01, 0x77, 0x03, 0x04                           // .w..
                })
        }
    }

    /* arg0 - test name */
    /* arg1 - Package, original object */
    /* arg2 - absolute index of file initiating the checking */
    /* arg3 - line number of checking (inside the file) */
    Method (M383, 4, NotSerialized)
    {
        Local0 = ObjectType (Arg1)
        If ((Local0 != C00C))
        {
            ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Local0, C00C)
        }
        Else
        {
            Local0 = Arg1 [0x00]
            Local1 = DerefOf (Local0)
            If ((Local1 != 0x05))
            {
                ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Local1, 0x05)
            }

            Local0 = Arg1 [0x01]
            Local1 = DerefOf (Local0)
            If ((Local1 != 0x77))
            {
                ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Local1, 0x77)
            }

            Local0 = Arg1 [0x02]
            Local1 = DerefOf (Local0)
            If ((Local1 != 0x07))
            {
                ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Local1, 0x07)
            }
        }
    }

    /* Check result of writing */
    /* arg0 - test name */
    /* arg1 - Integer, original object */
    /* arg2 - absolute index of file initiating the checking */
    /* arg3 - line number of checking (inside the file) */
    Method (M384, 4, NotSerialized)
    {
        Local0 = ObjectType (Arg1)
        If ((Local0 != C009))
        {
            ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Local0, C009)
        }
        ElseIf ((Arg1 != 0x2B))
        {
            ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Arg1, 0x2B)
        }
    }

    /* arg0 - test name */
    /* arg1 - String, original object */
    /* arg2 - absolute index of file initiating the checking */
    /* arg3 - line number of checking (inside the file) */
    Method (M385, 4, NotSerialized)
    {
        Local0 = ObjectType (Arg1)
        If ((Local0 != C00A))
        {
            ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Local0, C00A)
        }
        ElseIf ((Arg1 != "q+er0000"))
        {
            ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Arg1, "q+er0000")
        }
    }

    /* arg0 - test name */
    /* arg1 - Buffer, original object */
    /* arg2 - absolute index of file initiating the checking */
    /* arg3 - line number of checking (inside the file) */
    Method (M386, 4, NotSerialized)
    {
        Local0 = ObjectType (Arg1)
        If ((Local0 != C00B))
        {
            ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Local0, C00B)
        }
        ElseIf ((Arg1 != Buffer (0x04)
                    {
                         0x01, 0x2B, 0x03, 0x04                           // .+..
                    }))
        {
            ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Arg1, Buffer (0x04)
                {
                     0x01, 0x2B, 0x03, 0x04                           // .+..
                })
        }
    }

    /* arg0 - test name */
    /* arg1 - Package, original object */
    /* arg2 - absolute index of file initiating the checking */
    /* arg3 - line number of checking (inside the file) */
    Method (M387, 4, NotSerialized)
    {
        Local0 = ObjectType (Arg1)
        If ((Local0 != C00C))
        {
            ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Local0, C00C)
        }
        Else
        {
            Local0 = Arg1 [0x00]
            Local1 = DerefOf (Local0)
            If ((Local1 != 0x05))
            {
                ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Local1, 0x05)
            }

            Local0 = Arg1 [0x01]
            Local1 = DerefOf (Local0)
            If ((Local1 != 0x2B))
            {
                ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Local1, 0x2B)
            }

            Local0 = Arg1 [0x02]
            Local1 = DerefOf (Local0)
            If ((Local1 != 0x07))
            {
                ERR (Arg0, Z115, __LINE__, Arg2, Arg3, Local1, 0x07)
            }
        }
    }

    /* arg0 - original object */
    /* arg1 - type of it */
    /* arg2 - absolute index of file initiating the checking */
    /* arg3 - line number of checking (inside the file) */
    Method (M390, 4, Serialized)
    {
        Name (TS, "m390")
        If ((Arg1 == C009))
        {
            M380 (TS, Arg0, Arg2, __LINE__)
        }
        ElseIf ((Arg1 == C00A))
        {
            M381 (TS, Arg0, Arg2, __LINE__)
        }
        ElseIf ((Arg1 == C00B))
        {
            M382 (TS, Arg0, Arg2, __LINE__)
        }
        ElseIf ((Arg1 == C00C))
        {
            M383 (TS, Arg0, Arg2, __LINE__)
        }
    }

    /* arg0 - original object */
    /* arg1 - type of it */
    /* arg2 - absolute index of file initiating the checking */
    /* arg3 - line number of checking (inside the file) */
    Method (M391, 4, Serialized)
    {
        Name (TS, "m391")
        If ((Arg1 == C009))
        {
            M384 (TS, Arg0, Arg2, __LINE__)
        }
        ElseIf ((Arg1 == C00A))
        {
            M385 (TS, Arg0, Arg2, __LINE__)
        }
        ElseIf ((Arg1 == C00B))
        {
            M386 (TS, Arg0, Arg2, __LINE__)
        }
        ElseIf ((Arg1 == C00C))
        {
            M387 (TS, Arg0, Arg2, __LINE__)
        }
    }
