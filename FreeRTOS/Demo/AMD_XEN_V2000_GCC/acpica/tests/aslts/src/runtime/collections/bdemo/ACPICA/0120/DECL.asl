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
     * Bug 120:
     *
     * SUMMARY: Unexpected exception on Store of Device and ThermalZone elements of Package to Debug operation
     */
    Method (MF64, 0, Serialized)
    {
        Name (PP00, Package (0x01)
        {
            PRD2
        })
        Local0 = PP00 [0x00]
        Debug = ObjectType (Local0)
        Debug = DerefOf (Local0)
        Local1 = ObjectType (Local0)
        If ((Local1 != C014))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, C014)
        }
    }

    Method (MF65, 0, Serialized)
    {
        Name (PP00, Package (0x01)
        {
            RD07
        })
        Local0 = PP00 [0x00]
        Debug = ObjectType (Local0)
        Debug = DerefOf (Local0)
        Local1 = ObjectType (Local0)
        If ((Local1 != C012))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, C012)
        }
    }

    Method (MF66, 0, Serialized)
    {
        Name (PP00, Package (0x01)
        {
            PWD2
        })
        Local0 = PP00 [0x00]
        Debug = ObjectType (Local0)
        Debug = DerefOf (Local0)
        Local1 = ObjectType (Local0)
        If ((Local1 != C013))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, C013)
        }
    }

    Method (MF67, 0, Serialized)
    {
        Name (PP00, Package (0x01)
        {
            ED05
        })
        Local0 = PP00 [0x00]
        Debug = ObjectType (Local0)
        Debug = DerefOf (Local0)
        Local1 = ObjectType (Local0)
        If ((Local1 != C00F))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, C00F)
        }
    }

    Method (MF68, 0, Serialized)
    {
        Name (PP00, Package (0x01)
        {
            MXD3
        })
        Local0 = PP00 [0x00]
        Debug = ObjectType (Local0)
        Debug = DerefOf (Local0)
        Local1 = ObjectType (Local0)
        If ((Local1 != C011))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, C011)
        }
    }

    Method (MF69, 0, Serialized)
    {
        Name (PP00, Package (0x01)
        {
            DD0D
        })
        Local0 = PP00 [0x00]
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Debug = ObjectType (Local0)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Debug = DerefOf (Local0)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = ObjectType (Local0)
        If ((Local1 != C00E))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, C00E)
        }
    }

    Method (MF6A, 0, Serialized)
    {
        Name (PP00, Package (0x01)
        {
            TZD2
        })
        Local0 = PP00 [0x00]
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Debug = ObjectType (Local0)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Debug = DerefOf (Local0)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = ObjectType (Local0)
        If ((Local1 != C015))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, C015)
        }
    }
