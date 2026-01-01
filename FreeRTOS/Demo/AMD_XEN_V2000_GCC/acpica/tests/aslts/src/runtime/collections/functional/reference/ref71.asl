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
     * References
     *
     * (exceptions)
     */
    Name (Z109, 0x6D)
    /*
     * Check exceptions for unavailable types of Store
     */
    Method (M1B3, 0, Serialized)
    {
        C081 = Z109 /* absolute index of file initiating the checking */ /* \Z109 */
        Method (M000, 1, NotSerialized)
        {
            If (Arg0)
            {
                Local7 = 0x00
            }

            CH03 (__METHOD__, Z109, __LINE__, 0x00, 0x00)
            Local0 = Local7
            If (!SLCK)
            {
                CH04 (__METHOD__, 0x00, 0xFF, Z109, __LINE__, 0x00, 0x00)
            }
        }

        Method (M901, 0, NotSerialized)
        {
            Return (0x0ABC0012)
        }

        M000 (0x00)
        Local0 = I900 /* \I900 */
        Local7 = ObjectType (Local0)
        If ((Local7 != C009))
        {
            ERR (__METHOD__, Z109, __LINE__, 0x00, 0x00, Local7, C009)
        }

        Local0 = S900 /* \S900 */
        Local7 = ObjectType (Local0)
        If ((Local7 != C00A))
        {
            ERR (__METHOD__, Z109, __LINE__, 0x00, 0x00, Local7, C00A)
        }

        Local0 = B900 /* \B900 */
        Local7 = ObjectType (Local0)
        If ((Local7 != C00B))
        {
            ERR (__METHOD__, Z109, __LINE__, 0x00, 0x00, Local7, C00B)
        }

        Local0 = P900 /* \P900 */
        Local7 = ObjectType (Local0)
        If ((Local7 != C00C))
        {
            ERR (__METHOD__, Z109, __LINE__, 0x00, 0x00, Local7, C00C)
        }

        Local0 = F900 /* \F900 */
        Local7 = ObjectType (Local0)
        If ((Local7 != C009))
        {
            ERR (__METHOD__, Z109, __LINE__, 0x00, 0x00, Local7, C009)
        }

        /*
         // Removed 09/2015. iASL now disallows these stores
         CH03(ts, z109, 7, __LINE__, 0)
         Store(d900, Local0)
         if (LNot(SLCK)){
         CH04(ts, 0, 0xff, z109, __LINE__, 0, 0)
         }
         CH03(ts, z109, 9, __LINE__, 0)
         Store(e900, Local0)
         if (LNot(SLCK)){
         CH04(ts, 0, 0xff, z109, __LINE__, 0, 0)
         }
         */
        /*
         * 21.12.2005.
         * No exception now.
         * Bug 114: could work improperly by the same reason as Bug 114.
         * MS compiler allow this situation, iASL compiler just allows this
         * for compatibility, iASL assume this is compiled to a method
         * invacation.
         */
        If (X114)
        {
            CH03 (__METHOD__, Z109, __LINE__, 0x00, 0x00)
            Local0 = M901 ()
                /*CH04(ts, 0, 0xff, z109, __LINE__, 0, 0) */
        }

        /*
         // Removed 09/2015. iASL now disallows these stores
         CH03(ts, z109, 13, __LINE__, 0)
         Store(mx90, Local0)
         if (LNot(SLCK)){
         CH04(ts, 0, 0xff, z109, __LINE__, 0, 0)
         }
         CH03(ts, z109, 15, __LINE__, 0)
         Store(r900, Local0)
         if (LNot(SLCK)){
         CH04(ts, 0, 0xff, z109, __LINE__, 0, 0)
         }
         CH03(ts, z109, 17, __LINE__, 0)
         Store(pw90, Local0)
         if (LNot(SLCK)){
         CH04(ts, 0, 0xff, z109, __LINE__, 0, 0)
         }
         CH03(ts, z109, 19, __LINE__, 0)
         Store(pr90, Local0)
         if (LNot(SLCK)){
         CH04(ts, 0, 0xff, z109, __LINE__, 0, 0)
         }
         CH03(ts, z109, 21, __LINE__, 0)
         Store(tz90, Local0)
         if (LNot(SLCK))
         {
         CH04(ts, 0, 0xff, z109, __LINE__, 0, 0)
         }
         */
        Local0 = BF90 /* \BF90 */
        Local7 = ObjectType (Local0)
        If ((Local7 != C00B))
        {
            ERR (__METHOD__, Z109, __LINE__, 0x00, 0x00, Local7, C009)
        }
    }
