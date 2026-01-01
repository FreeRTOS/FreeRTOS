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
     * Bug 273:
     *
     * SUMMARY: Implementation of LoadTable operator should take into account its RootPathString parameter
     */
    Name (SSDT, Buffer (0x38)
    {
        /* 0000 */  0x4F, 0x45, 0x4D, 0x31, 0x38, 0x00, 0x00, 0x00,  // OEM18...
        /* 0008 */  0x01, 0x4B, 0x49, 0x6E, 0x74, 0x65, 0x6C, 0x00,  // .KIntel.
        /* 0010 */  0x4D, 0x61, 0x6E, 0x79, 0x00, 0x00, 0x00, 0x00,  // Many....
        /* 0018 */  0x01, 0x00, 0x00, 0x00, 0x49, 0x4E, 0x54, 0x4C,  // ....INTL
        /* 0020 */  0x18, 0x09, 0x03, 0x20, 0x08, 0x5F, 0x58, 0x54,  // ... ._XT
        /* 0028 */  0x32, 0x0A, 0x04, 0x14, 0x0C, 0x5F, 0x58, 0x54,  // 2...._XT
        /* 0030 */  0x31, 0x00, 0x70, 0x01, 0x5F, 0x58, 0x54, 0x32   // 1.p._XT2
    })
    DataTableRegion (DR73, "OEM1", "", "")
    Field (DR73, AnyAcc, NoLock, Preserve)
    {
        F273,   448
    }

    Device (D273)
    {
        Name (S000, "D273")
    }

    Name (RPST, "\\D273")
    Name (PLDT, 0x00)
    Name (PPST, "\\PLDT")
    External (\_XT2, UnknownObj)
    External (\D273._XT2, UnknownObj)
    Method (MC73, 0, Serialized)
    {
        Name (DDBH, 0x00)
        Method (LD, 0, NotSerialized)
        {
            DDBH = LoadTable ("OEM1", "", "", RPST, PPST, 0x01)
            Debug = "OEM1 loaded"
        }

        Method (UNLD, 0, NotSerialized)
        {
            Unload (DDBH)
            Debug = "OEM1 unloaded"
        }

        If ((F273 != SSDT))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, F273, SSDT)
        }

        If (CondRefOf (\_XT2, Local0))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
        }

        If (CondRefOf (\D273._XT2, Local0))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "\\D273._XT2", 0x01)
        }

        LD ()
        If (CondRefOf (\_XT2, Local0))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
        }

        If (CondRefOf (\D273._XT2, Local0)){}
        Else
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "\\D273._XT2", 0x00)
        }

        UNLD ()
        If (CondRefOf (\_XT2, Local0))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
        }

        If (CondRefOf (\D273._XT2, Local0))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "\\D273._XT2", 0x01)
        }
    }
