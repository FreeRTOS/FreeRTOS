/*---------------------------------------------------------------------------*/
/*                            - defaults.s -                                 */
/*                                                                           */
/*       This module contains default values for the following symbols       */
/*                                                                           */
/*       For RxV1 core:                                                      */
/*        __MDES            @ 0xFFFFFF80 to 0xFFFFFF83                       */
/*        __OFS1            @ 0xFFFFFF88 to 0xFFFFFF8B                       */
/*        __OFS0            @ 0xFFFFFF8C to 0xFFFFFF8F                       */
/*        __ROM_CODE        @ 0xFFFFFF9C                                     */
/*        __ID_BYTES_1_4    @ 0xFFFFFFA0 to 0xFFFFFFA3                       */
/*        __ID_BYTES_5_8    @ 0xFFFFFFA4 to 0xFFFFFFA7                       */
/*        __ID_BYTES_9_12   @ 0xFFFFFFA8 to 0xFFFFFFAB                       */
/*        __ID_BYTES_13_16  @ 0xFFFFFFAC to 0xFFFFFFAF                       */
/*                                                                           */
/*       For RxV1 core:                                                      */
/*        __MDES            @ 0xFFFFFF80 to 0xFFFFFF83                       */
/*        __OFS1            @ 0xFFFFFF88 to 0xFFFFFF8B                       */
/*        __OFS0            @ 0xFFFFFF8C to 0xFFFFFF8F                       */
/*        __ROM_CODE        @ 0xFFFFFF9C to 0xFFFFFF9F                       */
/*        __OSIS_1          @ 0xFFFFFFA0 to 0xFFFFFFA3                       */
/*        __OSIS_2          @ 0xFFFFFFA4 to 0xFFFFFFA7                       */
/*        __OSIS_3          @ 0xFFFFFFA8 to 0xFFFFFFAB                       */
/*        __OSIS_4          @ 0xFFFFFFAC to 0xFFFFFFAF                       */
/*                                                                           */
/*       For RxV2 core (RX64M):                                              */
/*        __SPCC            @ 0x00120040 to 0x00120043                       */
/*        __TMEF            @ 0x00120048 to 0x0012004B                       */
/*        __OSIS_1          @ 0x00120050 to 0x00120053                       */
/*        __OSIS_2          @ 0x00120054 to 0x00120057                       */
/*        __OSIS_3          @ 0x00120058 to 0x0012005D                       */
/*        __OSIS_4          @ 0x0012005C to 0x0012005F                       */
/*        __TMINF           @ 0x00120060 to 0x00120063                       */
/*        __MDE             @ 0x00120064 to 0x00120067                       */
/*        __OFS0            @ 0x00120068 to 0x0012006B                       */
/*        __OFS1            @ 0x0012006C to 0x0012006F                       */
/*                                                                           */
/*       To override default values in library add this file to your         */
/*       project and change the values.                                      */
/*                                                                           */
/*       Copyright 2014 IAR Systems AB.                                      */
/*                                                                           */
/*       $Revision: 6046 $                                                   */
/*                                                                           */
/*---------------------------------------------------------------------------*/

        MODULE  DEFAULTS
        SECTION .text:CONST:NOROOT

#if __CORE__ == __CORE_V1__
        PUBWEAK  __MDES
        PUBWEAK  __OFS1
        PUBWEAK  __OFS0
        PUBWEAK  __ROM_CODE
        PUBWEAK  __ID_BYTES_1_4
        PUBWEAK  __ID_BYTES_5_8
        PUBWEAK  __ID_BYTES_9_12
        PUBWEAK  __ID_BYTES_13_16
#if __LITTLE_ENDIAN__
__MDES           equ 0xffffffff
#else
__MDES           equ 0xfffffff8
#endif
__OFS0           equ 0xffffffff
__OFS1           equ 0xffffffff
__ROM_CODE       equ 0xffffffff
__ID_BYTES_1_4   equ 0xffffffff
__ID_BYTES_5_8   equ 0xffffffff
__ID_BYTES_9_12  equ 0xffffffff
__ID_BYTES_13_16 equ 0xffffffff

#else /* __CORE__ == __CORE_V2__ */
        PUBWEAK  __ROM_CODE
        PUBWEAK  __MDE
        PUBWEAK  __OFS1
        PUBWEAK  __OFS0
        PUBWEAK  __OSIS_1
        PUBWEAK  __OSIS_2
        PUBWEAK  __OSIS_3
        PUBWEAK  __OSIS_4
        PUBWEAK  __SPCC
        PUBWEAK  __TMEF
        PUBWEAK  __TMINF

__ROM_CODE       equ 0xffffffff

// 0x00120040 SPCC register
__SPCC           equ 0xffffffff

// 0x00120048 TMEF register
__TMEF           equ 0xffffffff

// 0x00120050 OSIC register (ID codes)
__OSIS_1         equ 0xffffffff
__OSIS_2         equ 0xffffffff
__OSIS_3         equ 0xffffffff
__OSIS_4         equ 0xffffffff

// 0x00120060 TMINF register
__TMINF          equ 0xffffffff

// 0x00120064 MDE register (Single Chip Mode)
#if __LITTLE_ENDIAN__
__MDE            equ 0xffffffff // little
#else
__MDE            equ 0xfffffff8 // big
#endif

// 0x00120068 OFS0 register
__OFS0           equ 0xffffffff

// 0x0012006c OFS1 register
__OFS1           equ 0xffffffff

#endif
        END
