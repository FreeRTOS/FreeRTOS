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
     * Bug 128:
     *
     * SUMMARY: Copying the RefOf reference to Named object spoils that reference
     */
    Method (MF17, 0, Serialized)
    {
        Name (I000, 0x1234)
        CopyObject (RefOf (I000), Local0)
        Debug = Local0
        Local1 = DerefOf (Local0)
        Debug = Local1
        If ((Local1 != 0x1234))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, 0x1234)
        }
    }

    Method (MF18, 0, Serialized)
    {
        Name (REF0, 0x00)
        Name (I000, 0x1234)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CopyObject (RefOf (I000), REF0) /* \MF18.REF0 */
        Debug = "Before printing ref0"
        Debug = REF0 /* \MF18.REF0 */
        Debug = "Before DerefOf"
        Local1 = DerefOf (REF0)
        Debug = "Before printing Local1"
        Debug = Local1
        Debug = "Before LNotEqual"
        If ((Local1 != 0x1234))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, 0x1234)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }

    Method (MF9E, 0, Serialized)
    {
        Name (I000, 0xABBC0000)
        Name (II00, 0xABBC0000)
        Name (B000, Buffer (0x08)
        {
             0x01, 0x02, 0x03, 0x04, 0x95, 0x06, 0x07, 0x08   // ........
        })
        Name (BB00, Buffer (0x08)
        {
             0x01, 0x02, 0x03, 0x04, 0x95, 0x06, 0x07, 0x08   // ........
        })
        Name (S000, "String")
        Name (SS00, "String")
        Name (P000, Package (0x04)
        {
            0x01,
            0x02,
            0x03,
            0x04
        })
        Name (REF0, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CopyObject (RefOf (I000), REF0) /* \MF9E.REF0 */
        MF88 (DerefOf (REF0), C009, II00, 0x01, 0x02, 0x01)
        CopyObject (RefOf (B000), REF0) /* \MF9E.REF0 */
        MF88 (DerefOf (REF0), C00B, BB00, 0x03, 0x04, 0x01)
        CopyObject (RefOf (S000), REF0) /* \MF9E.REF0 */
        MF88 (DerefOf (REF0), C00A, SS00, 0x03, 0x04, 0x01)
        CopyObject (RefOf (P000), REF0) /* \MF9E.REF0 */
        MF88 (DerefOf (REF0), C00C, SS00, 0x05, 0x06, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }

    Method (MF9F, 0, Serialized)
    {
        Name (REF0, 0x00)
        Event (E000)
        Mutex (MX00, 0x00)
        Device (D000)
        {
            Name (I900, 0xABCD0017)
        }

        ThermalZone (TZ00)
        {
        }

        Processor (PR00, 0x00, 0xFFFFFFFF, 0x00){}
        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        PowerResource (PW00, 0x01, 0x0000)
        {
            Method (MMMM, 0, NotSerialized)
            {
                Return (0x00)
            }
        }

        /* Checkings */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CopyObject (RefOf (E000), REF0) /* \MF9F.REF0 */
        MF88 (DerefOf (REF0), C00F, 0x00, 0x27, 0x28, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CopyObject (RefOf (MX00), REF0) /* \MF9F.REF0 */
        MF88 (DerefOf (REF0), C011, 0x00, 0x2A, 0x2B, 0x00)
        If (Y511)
        {
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            CopyObject (RefOf (D000), REF0) /* \MF9F.REF0 */
            MF88 (DerefOf (REF0), C00E, 0x00, 0x2D, 0x2E, 0x00)
        }

        If (Y508)
        {
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            CopyObject (RefOf (TZ00), REF0) /* \MF9F.REF0 */
            MF88 (DerefOf (REF0), C015, 0x00, 0x30, 0x31, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CopyObject (RefOf (PR00), REF0) /* \MF9F.REF0 */
        MF88 (DerefOf (REF0), C014, 0x00, 0x33, 0x34, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CopyObject (RefOf (R000), REF0) /* \MF9F.REF0 */
        MF88 (DerefOf (REF0), C012, 0x00, 0x36, 0x37, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CopyObject (RefOf (PW00), REF0) /* \MF9F.REF0 */
        MF88 (DerefOf (REF0), C013, 0x00, 0x39, 0x3A, 0x00)
    }
