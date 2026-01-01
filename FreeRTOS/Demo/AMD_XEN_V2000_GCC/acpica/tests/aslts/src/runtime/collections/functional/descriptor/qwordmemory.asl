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
     * Resource Descriptor macros
     *
     * QWord Memory Resource Descriptor Macro
     */
    Name (P424, Package (0x59)
    {
        ResourceTemplate ()
        {
            QWordMemory (ResourceProducer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceProducer, PosDecode, MinNotFixed, MaxFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceProducer, PosDecode, MinFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceProducer, PosDecode, MinFixed, MaxFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceProducer, SubDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceProducer, SubDecode, MinNotFixed, MaxFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceProducer, SubDecode, MinFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceProducer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinFixed, MaxFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, SubDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, SubDecode, MinNotFixed, MaxFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0x01, "", , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0x0F, "P", , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xF0, "PATH", , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0x0000000000000000, // Granularity
                0x0000000000000000, // Range Minimum
                0x0000000000000000, // Range Maximum
                0x0000000000000000, // Translation Offset
                0x0000000000000000, // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0x0F,, , AddressRangeMemory, TypeStatic)
        }
    })
    /*
     ACPI Specification, Revision 3.0, September 2, 2004
     6.4.3.5.1   QWord Address Space Descriptor
     Memory QWord Address Space Descriptor layout:
     Byte 0 (Tag Bits): Value=10001010B (0x8a) (Type = 1, Large item name = 0xA)
     Byte 1 (Length, bits[7:0]): Variable: Value = 43 (minimum)
     Byte 2 (Length, bits[15:8]): Variable: Value = 0 (minimum)
     Byte 3 (Resource Type):
     0		Memory range
     Byte 4 (General Flags):
     Bits[7:4] 	Reserved (must be 0)
     Bit[3] 		Min Address Fixed, _MAF:
     1	The specified maximum address is fixed
     0	The specified maximum address is not fixed
     and can be changed
     Bit[2] 		Max Address Fixed,_MIF:
     1	The specified minimum address is fixed
     0	The specified minimum address is not fixed
     and can be changed
     Bit[1] 		Decode Type, _DEC:
     1	This bridge subtractively decodes this address
     (top level bridges only)
     0	This bridge positively decodes this address
     Bit[0] 		Consumer/Producer:
     1-This device consumes this resource
     0-This device produces and consumes this resource
     Byte 5 (Type Specific Flags):
     Flags that are specific to each resource type. The meaning of the flags
     in this field depends on the value of the Resource Type field (see above)
     Bits[7:6]	Reserved (must be 0)
     Bit[5]		Memory to I/O Translation, _TTP
     1	TypeTranslation: This resource, which is memory on the secondary
     side of the bridge, is I/O on the primary side of the bridge.
     0	TypeStatic: This resource, which is memory on the secondary side
     of the bridge, is also memory on the primary side of the bridge.
     Bits[4:3] 	Memory attributes, _MTP. These bits are only defined if this memory
     resource describes system RAM. For a definition of the labels described
     here, see section 15, "System Address Map Interfaces."
     0	AddressRangeMemory
     1	AddressRangeReserved
     2	AddressRangeACPI
     3	AddressRangeNVS
     Bits[2:1] 	Memory attributes, _MEM
     0	The memory is non-cacheable.
     1	The memory is cacheable.
     2	The memory is cacheable and supports write combining.
     3	The memory is cacheable and prefetchable.
     (Notice: OSPM ignores this field in the Extended address space descriptor.
     Instead it uses the Type Specific Attributes field to determine memory attributes)
     Bit[0]		Write status, _RW
     1	This memory range is read-write.
     0	This memory range is read-only.
     Byte 6 (Address space granularity, _GRA bits[7:0]):
     A set bit in this mask means that this bit is decoded. All bits less
     significant than the most significant set bit must be set. (in other
     words, the value of the full Address Space Granularity field (all 32
     bits) must be a number (2**n-1).
     Byte 7 (Address space granularity, _GRA bits[15:8])
     Byte 8 (Address space granularity, _GRA bits[23:16])
     Byte 9 (Address space granularity, _GRA bits[31:24])
     Byte 10 (Address space granularity, _GRA bits[39:32])
     Byte 11 (Address space granularity, _GRA bits[47:40])
     Byte 12 (Address space granularity, _GRA bits[55:48])
     Byte 13 (Address space granularity, _GRA bits[63:56])
     Byte 14 (Address range minimum, _MIN bits [7:0]):
     For bridges that translate addresses, this is the address space
     on the secondary side of the bridge
     Byte 15 (Address range minimum, _MIN bits[15:8])
     Byte 16 (Address range minimum, _MIN bits[23:16])
     Byte 17 (Address range minimum, _MIN bits[31:24])
     Byte 18 (Address range minimum, _MIN bits[39:32])
     Byte 19 (Address range minimum, _MIN bits[47:40])
     Byte 20 (Address range minimum, _MIN bits[55:48])
     Byte 21 (Address range minimum, _MIN bits[63:56])
     Byte 22 (Address range maximum, _MAX bits [7:0]): See comment for _MIN
     Byte 23 (Address range maximum, _MAX bits[15:8])
     Byte 24 (Address range maximum, _MAX bits[23:16])
     Byte 25 (Address range maximum, _MAX bits[31:24])
     Byte 26 (Address range maximum, _MAX bits[39:32])
     Byte 27 (Address range maximum, _MAX bits[47:40])
     Byte 28 (Address range maximum, _MAX bits[55:48])
     Byte 29 (Address range maximum, _MAX bits[63:56])
     Byte 30 (Address Translation offset, _TRA bits [7:0]):
     For bridges that translate addresses across the bridge, this is the
     offset that must be added to the address on the secondary side to obtain
     the address on the primary side. Non-bridge devices must list 0 for all
     Address Translation offset bits
     Byte 31 (Address Translation offset, _TRA bits[15:8])
     Byte 32 (Address Translation offset, _TRA bits[23:16])
     Byte 33 (Address Translation offset, _TRA bits[31:24])
     Byte 34 (Address Translation offset, _TRA bits[39:32])
     Byte 35 (Address Translation offset, _TRA bits[47:40])
     Byte 36 (Address Translation offset, _TRA bits[55:48])
     Byte 37 (Address Translation offset, _TRA bits[63:56])
     Byte 38 (Address Length, _LEN bits [7:0])
     Byte 39 (Address Length, _LEN bits[15:8])
     Byte 40 (Address Length, _LEN bits[23:16])
     Byte 41 (Address Length, _LEN bits[31:24])
     Byte 42 (Address Length, _LEN bits[39:32])
     Byte 43 (Address Length, _LEN bits[47:40])
     Byte 44 (Address Length, _LEN bits[55:48])
     Byte 45 (Address Length, _LEN bits[63:56])
     Byte 46 (Resource Source Index):
     (Optional) Only present if Resource Source (below) is present. This
     field gives an index to the specific resource descriptor that this
     device consumes from in the current resource template for the device
     object pointed to in Resource Source
     String (Resource Source):
     (Optional) If present, the device that uses this descriptor consumes
     its resources from the resources produced by the named device object.
     If not present, the device consumes its resources out of a global pool.
     If not present, the device consumes this resource from its hierarchical
     parent.
     */
    Name (P425, Package (0x59)
    {
        /* Byte 4 (General Flags) of QWord Address Space Descriptor */

        ResourceTemplate ()
        {
            QWordMemory (ResourceProducer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceProducer, PosDecode, MinNotFixed, MaxFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceProducer, PosDecode, MinFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceProducer, PosDecode, MinFixed, MaxFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceProducer, SubDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceProducer, SubDecode, MinNotFixed, MaxFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceProducer, SubDecode, MinFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceProducer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinFixed, MaxFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, SubDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, SubDecode, MinNotFixed, MaxFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        /* Byte 5 (Type Specific Flags) of QWord Address Space Descriptor */
        /* NonCacheable */
        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeTranslation)
        },

        /* Cacheable */

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Cacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeTranslation)
        },

        /* WriteCombining */

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, WriteCombining, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeTranslation)
        },

        /* Prefetchable */

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeReserved, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeACPI, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, Prefetchable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeNVS, TypeTranslation)
        },

        /* Particular cases */

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                ,, , AddressRangeMemory, TypeStatic)
        },

        /* Resource Source */

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0x01, "", , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0x0F, "P", , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xF0, "PATH", , AddressRangeMemory, TypeStatic)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", , AddressRangeMemory, TypeStatic)
        },

        /* Particular cases */

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
        },

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0x0000000000000000, // Granularity
                0x0000000000000000, // Range Minimum
                0x0000000000000000, // Range Maximum
                0x0000000000000000, // Translation Offset
                0x0000000000000000, // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
        },

        /* 20051021, relaxation for omitted ResourceSource (bug-fix 70 rejection) */

        ResourceTemplate ()
        {
            QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadWrite,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0x0F,, , AddressRangeMemory, TypeStatic)
        }
    })
    Method (RT10, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "QWordMemory Resource Descriptor Macro", "qwordmemory.asl")
        /* Main test case for packages above */

        M330 (__METHOD__, 0x59, "p424", P424, P425)
        /* Check resource descriptor tag offsets */

        Local0 = ResourceTemplate ()
            {
                QWordMemory (ResourceProducer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadOnly,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    ,, , AddressRangeMemory, TypeStatic)
                QWordMemory (ResourceConsumer, PosDecode, MinNotFixed, MaxNotFixed, NonCacheable, ReadOnly,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    ,, , AddressRangeMemory, TypeStatic)
            }
        M331 (__METHOD__, 0x01, 0x21, 0x21, 0x0191, 0x0191, "_DEC")
        M331 (__METHOD__, 0x02, 0x22, 0x22, 0x0192, 0x0192, "_MIF")
        M331 (__METHOD__, 0x03, 0x23, 0x23, 0x0193, 0x0193, "_MAF")
        M331 (__METHOD__, 0x04, 0x28, 0x28, 0x0198, 0x0198, "_RW")
        M331 (__METHOD__, 0x05, 0x29, 0x29, 0x0199, 0x0199, "_MEM")
        M331 (__METHOD__, 0x06, 0x2B, 0x2B, 0x019B, 0x019B, "_MTP")
        M331 (__METHOD__, 0x06, 0x2D, 0x2D, 0x019D, 0x019D, "_TTP")
        M331 (__METHOD__, 0x07, 0x30, 0x30, 0x01A0, 0x01A0, "_GRA")
        M331 (__METHOD__, 0x08, 0x70, 0x70, 0x01E0, 0x01E0, "_MIN")
        M331 (__METHOD__, 0x09, 0xB0, 0xB0, 0x0220, 0x0220, "_MAX")
        M331 (__METHOD__, 0x0A, 0xF0, 0xF0, 0x0260, 0x0260, "_TRA")
        M331 (__METHOD__, 0x0B, 0x0130, 0x0130, 0x02A0, 0x02A0, "_LEN")
    }
