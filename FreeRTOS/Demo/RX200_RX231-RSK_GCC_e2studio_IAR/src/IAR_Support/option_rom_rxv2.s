
        // This segment part is marked as ROOT, since it must
        // be preserved by the linker.
        MODULE  OPTION_ROM
        SECTION .option_rom:CONST:ROOT

#if __CORE__ == __CORE_V2__
        EXTERN __MDE
        EXTERN __OFS1
        EXTERN __OFS0
        EXTERN __SPCC
        EXTERN __TMEF
        EXTERN __TMINF
        EXTERN __OSIS_1
        EXTERN __OSIS_2
        EXTERN __OSIS_3
        EXTERN __OSIS_4
        PUBLIC __option_rom

// Special configuration registers for 64M

        DATA
__option_rom:
#if 0
        DC32    __SPCC      // 0x00120040 SPCC register
        DS32    1           // 0x00120044 reserved
        DC32    __TMEF      // 0x00120048 TMEF register
        DS32    1           // 0x0012004C reserved
;        DC32    __OSIS_1    // 0x00120050 OSIC register (ID codes)
;        DC32    __OSIS_2    // 0x00120054 OSIC register (ID codes)
;        DC32    __OSIS_3    // 0x00120058 OSIC register (ID codes)
;        DC32    __OSIS_4    // 0x0012005C OSIC register (ID codes)
        DC32    __TMINF     // 0x00120060 TMINF register
;        DC32    __MDE       // 0x00120064 MDE register (Single Chip Mode)
;        DC32    __OFS0      // 0x00120068 OFS0 register
;        DC32    __OFS1      // 0x0012006C OFS1 register
#endif
#endif

        END
