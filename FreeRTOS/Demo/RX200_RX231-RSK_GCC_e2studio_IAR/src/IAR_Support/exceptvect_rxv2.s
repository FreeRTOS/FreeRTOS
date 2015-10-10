;-----------------------------------------------------------------------------
; Exception vector table.  We install all fixed interrupts in
; a section called EXCEPTVECT.  All fixed interrupts have a
; hard coded name that is default handled in this file.
; See fixedint.c for information how to replace them with handlers written in C.
;
; $Revision: 6884 $
;

        // This segment part is marked as ROOT, since it must
        // be preserved by the linker.
        MODULE  EXCEPTVECT
        SECTION .exceptvect:CONST:ROOT
#if __CORE__ == __CORE_V2__
        EXTERN  ___excep_access_inst
        EXTERN  ___privileged_handler
        EXTERN  ___undefined_handler
        EXTERN  ___undefined_interrupt_source_handler
        EXTERN  ___NMI_handler
        EXTERN  __float_placeholder
        EXTERN __MDE
        EXTERN __OFS1
        EXTERN __OFS0
        EXTERN __ROM_CODE
        EXTERN __OSIS_1
        EXTERN __OSIS_2
        EXTERN __OSIS_3
        EXTERN __OSIS_4
        PUBLIC  __exceptvect

        DATA
__exceptvect:
        DC32    __MDE       // 0xFFFFFF80 MDE register (Single Chip Mode)
        DS32    1
        DC32    __OFS1      // 0xFFFFFF88 OFS1 register
        DC32    __OFS0      // 0xFFFFFF8C OFS0 register
        DS32    3
        DC32    __ROM_CODE  // 0xFFFFFF8C ROM code protection
        DC32    __OSIS_1    // 0xFFFFFFA0 OSIC register (ID codes)
        DC32    __OSIS_2    // 0xFFFFFFA4 OSIC register (ID codes)
        DC32    __OSIS_3    // 0xFFFFFFA8 OSIC register (ID codes)
        DC32    __OSIS_4    // 0xFFFFFFAC OSIC register (ID codes)
        DS32    8
        DC32    ___privileged_handler   // Exception(Supervisor Instruction)
        DC32    ___excep_access_inst    // Exception(Access Instruction)
        DC32    ___undefined_interrupt_source_handler
        DC32    ___undefined_handler    // Exception(Undefined Instruction)
        DC32    ___undefined_interrupt_source_handler
        DC32    __float_placeholder     // Exception(Floating Point)
        DC32    ___undefined_interrupt_source_handler
        DC32    ___undefined_interrupt_source_handler
        DC32    ___undefined_interrupt_source_handler
        DC32    ___undefined_interrupt_source_handler
        DC32    ___NMI_handler          // NMI
#endif
        END
