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
     * Bug 68: CANCELED
     *
     * SUMMARY: FieldUnit type object should be returned by Methods without any conversion (to Buffer or Integer)
     *
     * EXAMPLES:
     *
     * ROOT CAUSE:
     *
     * SEE ALSO:     bugs 65,66,67,68,118
     */
    Method (MD87, 0, NotSerialized)
    {
        Return (FD00) /* \FD00 */
    }

    Method (MD88, 0, NotSerialized)
    {
        Return (FD01) /* \FD01 */
    }

    Method (MD89, 0, NotSerialized)
    {
        /* FiledUnit converted to Integer before return */

        Local7 = MD87 ()
        Local0 = ObjectType (Local7)
        If ((Local0 != C009))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, C009)
        }

        /* FiledUnit converted to Buffer before return */

        Local7 = MD88 ()
        Local0 = ObjectType (Local7)
        If ((Local0 != C00B))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, C00B)
        }
    }
