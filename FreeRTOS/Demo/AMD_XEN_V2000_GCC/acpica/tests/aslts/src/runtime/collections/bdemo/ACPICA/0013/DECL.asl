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
     * Bug 0013:
     *
     * SUMMARY: The type returned by ObjectType for Object created by Create*Field operator is not BufferField
     */
    Method (MDAD, 0, NotSerialized)
    {
        Local0 = Buffer (0x64){}
        CreateBitField (Local0, 0x00, BF00)
        CreateByteField (Local0, 0x00, BF01)
        CreateDWordField (Local0, 0x00, BF02)
        CreateField (Local0, 0x00, 0x20, BF03)
        CreateField (Local0, 0x00, 0x40, BF04)
        CreateField (Local0, 0x00, 0x41, BF05)
        CreateQWordField (Local0, 0x00, BF06)
        CreateWordField (Local0, 0x00, BF07)
        Local7 = ObjectType (BF00)
        If ((Local7 != C016))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local7, C016)
        }

        Local7 = ObjectType (BF01)
        If ((Local7 != C016))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local7, C016)
        }

        Local7 = ObjectType (BF02)
        If ((Local7 != C016))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local7, C016)
        }

        Local7 = ObjectType (BF03)
        If ((Local7 != C016))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local7, C016)
        }

        Local7 = ObjectType (BF04)
        If ((Local7 != C016))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local7, C016)
        }

        Local7 = ObjectType (BF05)
        If ((Local7 != C016))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local7, C016)
        }

        Local7 = ObjectType (BF06)
        If ((Local7 != C016))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local7, C016)
        }

        Local7 = ObjectType (BF07)
        If ((Local7 != C016))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local7, C016)
        }
    }
