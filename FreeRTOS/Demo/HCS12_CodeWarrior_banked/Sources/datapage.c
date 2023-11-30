/******************************************************************************
  FILE        : datapage.c
  PURPOSE     : paged data access runtime routines
  MACHINE     : Motorola 68HC12 (Target)
  LANGUAGE    : ANSI-C
  HISTORY     : 21.7.96 first version created
******************************************************************************/

/*
   According to the -Cp option of the compiler the
   __DPAGE__, __PPAGE__ and __EPAGE__ macros are defined.
   If none of them is given as argument, then no page accesses should occur and
   this runtime routine should not be used !
   To be on the save side, the runtime routines are created anyway.
   If some of the -Cp options are given an adapted versions which only covers the
   needed cases is produced.
*/

/* if no compiler option -Cp is given, it is assumed that all possible are given : */

/* Compile with option -DHCS12 to activate this code */
#if defined(HCS12) || defined(_HCS12) /* HCS12 family has PPAGE register only at 0x30 */
#define PPAGE_ADDR (0x30+REGISTER_BASE)
#ifndef __PPAGE__ /* may be set already by option -CPPPAGE */
#define __PPAGE__
#endif
/* Compile with option -DDG128 to activate this code */
#elif defined DG128 /* HC912DG128 derivative has PPAGE register only at 0xFF */
#define PPAGE_ADDR (0xFF+REGISTER_BASE)
#ifndef __PPAGE__ /* may be set already by option -CPPPAGE */
#define __PPAGE__
#endif
#elif defined(HC812A4)
/* all setting default to A4 already */
#endif


#if !defined(__EPAGE__) && !defined(__PPAGE__) && !defined(__DPAGE__)
/* as default use all page registers */
#define __DPAGE__
#define __EPAGE__
#define __PPAGE__
#endif

/* modify the following defines to your memory configuration */

#define EPAGE_LOW_BOUND   0x400u
#define EPAGE_HIGH_BOUND  0x7ffu

#define DPAGE_LOW_BOUND   0x7000u
#define DPAGE_HIGH_BOUND  0x7fffu

#define PPAGE_LOW_BOUND   (DPAGE_HIGH_BOUND+1)
#define PPAGE_HIGH_BOUND  0xBFFFu

#define REGISTER_BASE      0x0u
#ifndef DPAGE_ADDR
#define DPAGE_ADDR        (0x34u+REGISTER_BASE)
#endif
#ifndef EPAGE_ADDR
#define EPAGE_ADDR        (0x36u+REGISTER_BASE)
#endif
#ifndef PPAGE_ADDR
#define PPAGE_ADDR        (0x35u+REGISTER_BASE)
#endif

/*
  The following parts about the defines are assumed in the code of _GET_PAGE_REG :
  - the memory region controlled by DPAGE is above the area controlled by the EPAGE and
    below the area controlled by the PPAGE.
  - the lower bound of the PPAGE area is equal to be the higher bound of the DPAGE area + 1
*/
#if EPAGE_LOW_BOUND >= EPAGE_HIGH_BOUND || EPAGE_HIGH_BOUND >= DPAGE_LOW_BOUND || DPAGE_LOW_BOUND >= DPAGE_HIGH_BOUND || DPAGE_HIGH_BOUND >= PPAGE_LOW_BOUND || PPAGE_LOW_BOUND >= PPAGE_HIGH_BOUND
#error /* please adapt _GET_PAGE_REG for this non default page configuration */
#endif

#if DPAGE_HIGH_BOUND+1 != PPAGE_LOW_BOUND
#error /* please adapt _GET_PAGE_REG for this non default page configuration */
#endif

#include "hidef.h"
#include "non_bank.sgm"
#include "runtime.sgm"

/* this module does either control if any access is in the bounds of the specified page or */
/* ,if only one page is specified, just use this page. */
/* This behavior is controlled by the define USE_SEVERAL_PAGES. */
/* If !USE_SEVERAL_PAGES does increase the performance significantly */
/* NOTE : When !USE_SEVERAL_PAGES, the page is also set for accesses outside of the area controlled */
/*        by this single page. But this is usually no problem because the page is set again before any other access */

#if !defined(__DPAGE__) && !defined(__EPAGE__) && !defined(__PPAGE__)
/* no page at all is specified */
/* only specifing the right pages will speed up these functions a lot */
#define USE_SEVERAL_PAGES 1
#elif defined(__DPAGE__) && defined(__EPAGE__) || defined(__DPAGE__) && defined(__PPAGE__) || defined(__EPAGE__) && defined(__PPAGE__)
/* more than one page register is used */
#define USE_SEVERAL_PAGES 1
#else

#define USE_SEVERAL_PAGES 0

#if defined(__DPAGE__) /* check which pages are used  */
#define PAGE_ADDR PPAGE_ADDR
#elif defined(__EPAGE__)
#define PAGE_ADDR EPAGE_ADDR
#elif defined(__PPAGE__)
#define PAGE_ADDR PPAGE_ADDR
#else /* we dont know which page, decide it at runtime */
#error /* must not happen */
#endif

#endif


#if USE_SEVERAL_PAGES /* only needed for several pages support */
/*--------------------------- _GET_PAGE_REG --------------------------------
  Runtime routine to detect the right register depending on the 16 bit offset part
  of an address.
  This function is only used by the functions below.

  Depending on the compiler options -Cp different versions of _GET_PAGE_REG are produced.

  Arguments :
  - Y : offset part of an address

  Result :
  if address Y is controlled by a page register :
  - X : address of page register if Y is controlled by an page register
  - Zero flag cleared
  - all other registers remain unchanged

  if address Y is not controlled by a page register :
  - Zero flag is set
  - all registers remain unchanged

  --------------------------- _GET_PAGE_REG ----------------------------------*/

#if defined(__DPAGE__)

#ifdef __cplusplus
extern "C"
#endif
#pragma NO_ENTRY
#pragma NO_EXIT
#pragma NO_FRAME

static void NEAR _GET_PAGE_REG(void) { /*lint -esym(528, _GET_PAGE_REG) used in asm code */
  asm {
L_DPAGE:
        CPY  #DPAGE_LOW_BOUND     ; test of lower bound of DPAGE
#if defined(__EPAGE__)
        BLO  L_EPAGE              ; EPAGE accesses are possible
#else
        BLO  L_NOPAGE             ; no paged memory below accesses
#endif
        CPY  #DPAGE_HIGH_BOUND    ; test of higher bound DPAGE/lower bound PPAGE
#if defined(__PPAGE__)
        BHI  L_PPAGE              ; EPAGE accesses are possible
#else
        BHI  L_NOPAGE             ; no paged memory above accesses
#endif
FOUND_DPAGE:
        LDX  #DPAGE_ADDR          ; load page register address and clear zero flag
        RTS

#if defined(__PPAGE__)
L_PPAGE:
        CPY  #PPAGE_HIGH_BOUND    ; test of higher bound of PPAGE
        BHI  L_NOPAGE
FOUND_PPAGE:
        LDX  #PPAGE_ADDR          ; load page register address and clear zero flag
        RTS
#endif

#if defined(__EPAGE__)
L_EPAGE:
        CPY #EPAGE_LOW_BOUND      ; test of lower bound of EPAGE
        BLO L_NOPAGE
        CPY #EPAGE_HIGH_BOUND     ; test of higher bound of EPAGE
        BHI L_NOPAGE

FOUND_EPAGE:
        LDX #EPAGE_ADDR           ; load page register address and clear zero flag
        RTS
#endif

L_NOPAGE:
        ORCC #0x04                ; sets zero flag
        RTS
  }
}

#else /* !defined(__DPAGE__) */

#if defined( __PPAGE__ )

#ifdef __cplusplus
extern "C"
#endif
#pragma NO_ENTRY
#pragma NO_EXIT
#pragma NO_FRAME

static void NEAR _GET_PAGE_REG(void) {	/*lint -esym(528, _GET_PAGE_REG) used in asm code */
  asm {
L_PPAGE:
        CPY  #PPAGE_LOW_BOUND     ; test of lower bound of PPAGE
#if defined( __EPAGE__ )
        BLO  L_EPAGE
#else
        BLO  L_NOPAGE             ; no paged memory below
#endif
        CPY  #PPAGE_HIGH_BOUND    ; test of higher bound PPAGE
        BHI  L_NOPAGE
FOUND_PPAGE:
        LDX  #PPAGE_ADDR          ; load page register address and clear zero flag
        RTS
#if defined( __EPAGE__ )
L_EPAGE:
        CPY #EPAGE_LOW_BOUND      ; test of lower bound of EPAGE
        BLO L_NOPAGE
        CPY #EPAGE_HIGH_BOUND     ; test of higher bound of EPAGE
        BHI L_NOPAGE
FOUND_EPAGE:
        LDX #EPAGE_ADDR           ; load page register address and clear zero flag
        RTS
#endif

L_NOPAGE:                         ; not in any allowed page area
                                  ; its a far access to a non paged variable
        ORCC #0x04                ; sets zero flag
        RTS
  }
}

#else /* !defined(__DPAGE__ ) && !defined( __PPAGE__) */
#if defined(__EPAGE__)

#ifdef __cplusplus
extern "C"
#endif
#pragma NO_ENTRY
#pragma NO_EXIT
#pragma NO_FRAME

static void NEAR _GET_PAGE_REG(void) { /*lint -esym(528, _GET_PAGE_REG) used in asm code */
  asm {
L_EPAGE:
        CPY #EPAGE_LOW_BOUND      ; test of lower bound of EPAGE
        BLO L_NOPAGE
        CPY #EPAGE_HIGH_BOUND     ; test of higher bound of EPAGE
        BHI L_NOPAGE
FOUND_EPAGE:
        LDX #EPAGE_ADDR           ; load page register address and clear zero flag
        RTS

L_NOPAGE:                         ; not in any allowed page area
                                  ; its a far access to a non paged variable
        ORCC #0x04                ; sets zero flag
        RTS
  }
}

#endif /*  defined(__EPAGE__) */
#endif /*  defined(__PPAGE__) */
#endif /*  defined(__DPAGE__) */

#endif /* USE_SEVERAL_PAGES */

/*--------------------------- _SET_PAGE --------------------------------
  Runtime routine to set the right page register. This routine is used if the compiler
  does not know the right page register, i.e. if the option -Cp is used for more than
  one pageregister or if the runtime option is used for one of the -Cp options.

  Arguments :
  - offset part of an address in the Y register
  - page part of an address in the B register

  Result :
  - page part written into the correct page register.
  - the old page register content is destroyed
  - all processor registers remains unchanged
  --------------------------- _SET_PAGE ----------------------------------*/

#ifdef __cplusplus
extern "C"
#endif
#pragma NO_ENTRY
#pragma NO_EXIT
#pragma NO_FRAME

void NEAR _SET_PAGE(void) {
#if USE_SEVERAL_PAGES
  asm {
          PSHX                  ; save X register
          __PIC_JSR(_GET_PAGE_REG)
          BEQ    L_NOPAGE
          STAB   0,X            ; set page register
L_NOPAGE:
          PULX                  ; restore X register
          RTS
  }
#else /* USE_SEVERAL_PAGES */
  asm {
          STAB   PAGE_ADDR      ; set page register
          RTS
  }
#endif /* USE_SEVERAL_PAGES */
}

/*--------------------------- _LOAD_FAR_8 --------------------------------
  This runtime routine is used to access paged memory via a runtime function.
  It may also be used if the compiler  option -Cp is not used with the runtime argument.

  Arguments :
  - offset part of an address in the Y register
  - page part of an address in the B register

  Result :
  - value to be read in the B register
  - all other registers remains unchanged
  - all page register still contain the same value
  --------------------------- _LOAD_FAR_8 ----------------------------------*/

#ifdef __cplusplus
extern "C"
#endif
#pragma NO_ENTRY
#pragma NO_EXIT
#pragma NO_FRAME

void NEAR _LOAD_FAR_8(void) {
#if USE_SEVERAL_PAGES
  asm {
          PSHX                ; save X register
          __PIC_JSR(_GET_PAGE_REG)
          BEQ    L_NOPAGE
          PSHA                ; save A register
          LDAA   0,X          ; save page register
          STAB   0,X          ; set page register
          LDAB   0,Y          ; actual load, overwrites page
          STAA   0,X          ; restore page register
          PULA                ; restore A register
          PULX                ; restore X register
          RTS
L_NOPAGE:
          LDAB   0,Y          ; actual load, overwrites page
          PULX                ; restore X register
          RTS
  }
#else /* USE_SEVERAL_PAGES */
  asm {
          PSHA                ; save A register
          LDAA   PAGE_ADDR    ; save page register
          STAB   PAGE_ADDR    ; set page register
          LDAB   0,Y          ; actual load, overwrites page
          STAA   PAGE_ADDR    ; restore page register
          PULA                ; restore A register
          RTS
  }
#endif /* USE_SEVERAL_PAGES */
}

/*--------------------------- _LOAD_FAR_16 --------------------------------
  This runtime routine is used to access paged memory via a runtime function.
  It may also be used if the compiler  option -Cp is not used with the runtime argument.

  Arguments :
  - offset part of an address in the Y register
  - page part of an address in the B register

  Result :
  - value to be read in the Y register
  - all other registers remains unchanged
  - all page register still contain the same value
  --------------------------- _LOAD_FAR_16 ----------------------------------*/

#ifdef __cplusplus
extern "C"
#endif
#pragma NO_ENTRY
#pragma NO_EXIT
#pragma NO_FRAME

void NEAR _LOAD_FAR_16(void) {
#if USE_SEVERAL_PAGES
  asm {
          PSHX                 ; save X register
          __PIC_JSR(_GET_PAGE_REG)
          BEQ   L_NOPAGE
          PSHA                 ; save A register
          LDAA  0,X            ; save page register
          STAB  0,X            ; set page register
          LDY   0,Y            ; actual load, overwrites address
          STAA  0,X            ; restore page register
          PULA                 ; restore A register
          PULX                 ; restore X register
          RTS
L_NOPAGE:
          LDY   0,Y              ; actual load, overwrites address
          PULX                 ; restore X register
          RTS
  }
#else /* USE_SEVERAL_PAGES */
  asm {
          PSHA                ; save A register
          LDAA   PAGE_ADDR    ; save page register
          STAB   PAGE_ADDR    ; set page register
          LDY    0,Y          ; actual load, overwrites address
          STAA   PAGE_ADDR    ; restore page register
          PULA                ; restore A register
          RTS
  }
#endif /* USE_SEVERAL_PAGES */
}
/*--------------------------- _LOAD_FAR_24 --------------------------------
  This runtime routine is used to access paged memory via a runtime function.
  It may also be used if the compiler  option -Cp is not used with the runtime argument.

  Arguments :
  - offset part of an address in the Y register
  - page part of an address in the B register

  Result :
  - value to be read in the Y:B registers
  - all other registers remains unchanged
  - all page register still contain the same value
  --------------------------- _LOAD_FAR_24 ----------------------------------*/

#ifdef __cplusplus
extern "C"
#endif
#pragma NO_ENTRY
#pragma NO_EXIT
#pragma NO_FRAME

void NEAR _LOAD_FAR_24(void) {
#if USE_SEVERAL_PAGES
  asm {
          PSHX                 ; save X register
          __PIC_JSR(_GET_PAGE_REG)
          BEQ   L_NOPAGE
          PSHA                 ; save A register
          LDAA  0,X            ; save page register
          STAB  0,X            ; set page register
          LDAB  0,Y            ; actual load, overwrites page of address
          LDY   1,Y            ; actual load, overwrites offset of address
          STAA  0,X            ; restore page register
          PULA                 ; restore A register
          PULX                 ; restore X register
          RTS
L_NOPAGE:
          LDAB  0,Y            ; actual load, overwrites page of address
          LDY   1,Y            ; actual load, overwrites offset of address
          PULX                 ; restore X register
          RTS
  }
#else /* USE_SEVERAL_PAGES */
  asm {
          PSHA                 ; save A register
          LDAA   PAGE_ADDR     ; save page register
          STAB   PAGE_ADDR     ; set page register
          LDAB   0,Y           ; actual load, overwrites page of address
          LDY    1,Y           ; actual load, overwrites offset of address
          STAA   PAGE_ADDR     ; restore page register
          PULA                 ; restore A register
          RTS
  }
#endif /* USE_SEVERAL_PAGES */

}

/*--------------------------- _LOAD_FAR_32 --------------------------------
  This runtime routine is used to access paged memory via a runtime function.
  It may also be used if the compiler  option -Cp is not used with the runtime argument.

  Arguments :
  - offset part of an address in the Y register
  - page part of an address in the B register

  Result :
  - low 16 bit of value to be read in the D registers
  - high 16 bit of value to be read in the Y registers
  - all other registers remains unchanged
  - all page register still contain the same value
  --------------------------- _LOAD_FAR_32 ----------------------------------*/

#ifdef __cplusplus
extern "C"
#endif
#pragma NO_ENTRY
#pragma NO_EXIT
#pragma NO_FRAME

void NEAR _LOAD_FAR_32(void) {
#if USE_SEVERAL_PAGES
  asm {
          PSHX                 ; save X register
          __PIC_JSR(_GET_PAGE_REG)
          BEQ   L_NOPAGE
          LDAA  0,X            ; save page register
          PSHA                 ; put it onto the stack
          STAB  0,X            ; set page register
          LDD   2,Y            ; actual load, low word
          LDY   0,Y            ; actual load, high word
          MOVB  1,SP+,0,X      ; restore page register
          PULX                 ; restore X register
          RTS
L_NOPAGE:
          LDD   2,Y            ; actual load, low word
          LDY   0,Y            ; actual load, high word
          PULX                 ; restore X register
          RTS
  }
#else /* USE_SEVERAL_PAGES */
  asm {
          LDAA   PAGE_ADDR     ; save page register
          PSHA                 ; put it onto the stack
          STAB   PAGE_ADDR     ; set page register
          LDD   2,Y            ; actual load, low word
          LDY   0,Y            ; actual load, high word
          MOVB  1,SP+,PAGE_ADDR; restore page register
          RTS
  }
#endif /* USE_SEVERAL_PAGES */
}

/*--------------------------- _STORE_FAR_8 --------------------------------
  This runtime routine is used to access paged memory via a runtime function.
  It may also be used if the compiler  option -Cp is not used with the runtime argument.

  Arguments :
  - offset part of an address in the Y register
  - page part of an address in the B register
  - value to be stored in the B register

  Result :
  - value stored at the address
  - all registers remains unchanged
  - all page register still contain the same value
  --------------------------- _STORE_FAR_8 ----------------------------------*/

#ifdef __cplusplus
extern "C"
#endif
#pragma NO_ENTRY
#pragma NO_EXIT
#pragma NO_FRAME

void NEAR _STORE_FAR_8(void) {
#if USE_SEVERAL_PAGES
  asm {
          PSHX                   ; save X register
          __PIC_JSR(_GET_PAGE_REG)
          BEQ   L_NOPAGE
          PSHB                   ; save B register
          LDAB  0,X              ; save page register
          MOVB  0,SP, 0,X        ; set page register
          STAA  0,Y              ; store the value passed in A
          STAB  0,X              ; restore page register
          PULB                   ; restore B register
          PULX                   ; restore X register
          RTS
L_NOPAGE:
          STAA 0,Y               ; store the value passed in A
          PULX                   ; restore X register
          RTS
  }
#else /* USE_SEVERAL_PAGES */
  asm {
          PSHB                 ; save A register
          LDAB   PAGE_ADDR     ; save page register
          MOVB  0,SP,PAGE_ADDR ; set page register
          STAA  0,Y            ; store the value passed in A
          STAB   PAGE_ADDR     ; restore page register
          PULB                   ; restore B register
          RTS
  }
#endif /* USE_SEVERAL_PAGES */
}

/*--------------------------- _STORE_FAR_16 --------------------------------
  This runtime routine is used to access paged memory via a runtime function.
  It may also be used if the compiler  option -Cp is not used with the runtime argument.

  Arguments :
  - offset part of an address in the Y register
  - page part of an address in the B register
  - value to be stored in the X register

  Result :
  - value stored at the address
  - all registers remains unchanged
  - all page register still contain the same value
  --------------------------- _STORE_FAR_16 ----------------------------------*/

#ifdef __cplusplus
extern "C"
#endif
#pragma NO_ENTRY
#pragma NO_EXIT
#pragma NO_FRAME

void NEAR _STORE_FAR_16(void) {
#if USE_SEVERAL_PAGES
  asm {
          PSHX                  ; save X register
          __PIC_JSR(_GET_PAGE_REG)
          BEQ    L_NOPAGE

          PSHA
          LDAA   0,X            ; save page register
          STAB   0,X            ; set page register
          MOVW   1,SP, 0,Y      ; store the value passed in X
          STAA   0,X            ; restore page register
          PULA                  ; restore A register
          PULX                  ; restore X register
          RTS

L_NOPAGE:
          STX 0,Y               ; store the value passed in X
          PULX                  ; restore X register
          RTS
  }
#else /* USE_SEVERAL_PAGES */
  asm {
          PSHA                 ; save A register
          LDAA   PAGE_ADDR     ; save page register
          STAB   PAGE_ADDR     ; set page register
          STX    0,Y           ; store the value passed in X
          STAA   PAGE_ADDR     ; restore page register
          PULA                 ; restore A register
          RTS
  }
#endif /* USE_SEVERAL_PAGES */
}
/*--------------------------- _STORE_FAR_24 --------------------------------
  This runtime routine is used to access paged memory via a runtime function.
  It may also be used if the compiler  option -Cp is not used with the runtime argument.

  Arguments :
  - offset part of an address in the Y register
  - page part of an address in the B register
  - value to be stored in the X:A registers (X : low 16 bit, A : high 8 bit)

  Result :
  - value stored at the address
  - all registers remains unchanged
  - all page register still contain the same value
  --------------------------- _STORE_FAR_24 ----------------------------------*/

#ifdef __cplusplus
extern "C"
#endif
#pragma NO_ENTRY
#pragma NO_EXIT
#pragma NO_FRAME

void NEAR _STORE_FAR_24(void) {
#if USE_SEVERAL_PAGES
  asm {
          PSHX                  ; save X register
          __PIC_JSR(_GET_PAGE_REG)
          BEQ    L_NOPAGE

          PSHA
          LDAA   0,X            ; save page register
          STAB   0,X            ; set page register
          MOVW   1,SP, 1,Y      ; store the value passed in X
          MOVB   0,SP, 0,Y      ; store the value passed in A
          STAA   0,X            ; restore page register
          PULA                  ; restore A register
          PULX                  ; restore X register
          RTS

L_NOPAGE:
          STX    1,Y            ; store the value passed in X
          STAA   0,Y            ; store the value passed in X
          PULX                  ; restore X register
          RTS
  }
#else /* USE_SEVERAL_PAGES */
  asm {
          PSHA                 ; save A register
          LDAA   PAGE_ADDR     ; save page register
          STAB   PAGE_ADDR     ; set page register
          MOVB   0,SP, 0,Y     ; store the value passed in A
          STX    1,Y           ; store the value passed in X
          STAA   PAGE_ADDR     ; restore page register
          PULA                 ; restore A register
          RTS
  }
#endif /* USE_SEVERAL_PAGES */
}
/*--------------------------- _STORE_FAR_32 --------------------------------
  This runtime routine is used to access paged memory via a runtime function.
  It may also be used if the compiler  option -Cp is not used with the runtime argument.

  Arguments :
  - offset part of an address in the Y register
  - page part of an address is on the stack at 3,SP (just below the return address)
  - value to be stored in the X:D registers (D : low 16 bit, X : high 16 bit)

  Result :
  - value stored at the address
  - all registers remains unchanged
  - the page part is removed from the stack
  - all page register still contain the same value
  --------------------------- _STORE_FAR_32 ----------------------------------*/

#ifdef __cplusplus
extern "C"
#endif
#pragma NO_ENTRY
#pragma NO_EXIT
#pragma NO_FRAME

void NEAR _STORE_FAR_32(void) {
#if USE_SEVERAL_PAGES
  asm {
          PSHX                  ; save X register
          __PIC_JSR(_GET_PAGE_REG)
          BEQ    L_NOPAGE

          PSHD
          LDAA   0,X            ; save page register
          MOVB   6,SP, 0,X      ; set page register
          MOVW   2,SP, 0,Y      ; store the value passed in X (high word)
          MOVW   0,SP, 2,Y      ; store the value passed in D (low word)
          STAA   0,X            ; restore page register
          PULD                  ; restore A register
          BRA done

L_NOPAGE:
          MOVW   0,SP, 0,Y      ; store the value passed in X (high word)
          STD          2,Y      ; store the value passed in D (low word)
done:
          PULX                  ; restore X register
          MOVW   0,SP, 1,+SP    ; move return address
          RTS
  }
#else /* USE_SEVERAL_PAGES */
  asm {
          PSHD                    ; save D register
          LDAA   PAGE_ADDR        ; save page register
          LDAB   4,SP             ; load page part of address
          STAB   PAGE_ADDR        ; set page register
          STX    0,Y              ; store the value passed in X
          MOVW   0,SP, 2,Y        ; store the value passed in D (low word)
          STAA   PAGE_ADDR        ; restore page register
          PULD                    ; restore D register
          MOVW   0,SP, 1,+SP    ; move return address
          RTS
  }
#endif /* USE_SEVERAL_PAGES */
}

/*--------------------------- _FAR_COPY --------------------------------
  This runtime routine is used to access paged memory via a runtime function.
  It may also be used if the compiler  option -Cp is not used with the runtime argument.

  Arguments :
  - offset part of the source int the X register
  - page part of the source in the A register
  - offset part of the dest int the Y register
  - page part of the dest in the B register
  - number of bytes to be copied at 2,SP. The number of bytes is always > 0

  Result :
  - memory area copied
  - no registers are saved, i.e. all registers may be destroied
  - all page register still contain the same value


  stack-structure at the loop-label:
     0,SP : destination offset
     2,SP : source page
     3,SP : destination page
     4,SP : source offset
     6,SP : return address
     8,SP : counter, > 0
  --------------------------- _FAR_COPY ----------------------------------*/

#ifdef __cplusplus
extern "C"
#endif
#pragma NO_ENTRY
#pragma NO_EXIT
#pragma NO_FRAME

void NEAR _FAR_COPY(void) {
#if USE_SEVERAL_PAGES
  asm {
        DEX                   ; source addr-=1, because loop counter ends at 1
        PSHX                  ; save source offset
        PSHD                  ; save both pages
        DEY                   ; destination addr-=1, because loop counter ends at 1
        PSHY                  ; save destination offset
        LDX     8,SP          ; load counter, assuming counter > 0

loop:
        LDD     4,SP          ; load source offset
        LEAY    D,X           ; calcutate actual source address
        LDAB    2,SP          ; load source page
        __PIC_JSR (_LOAD_FAR_8); load 1 source byte
        PSHB                  ; save value
        LDD     0+1,SP        ; load destination offset
        LEAY    D,X           ; calcutate acual destination address
        PULA                  ; restore value
        LDAB    3,SP          ; load destination page
        __PIC_JSR (_STORE_FAR_8); store one byte
        DEX
        BNE     loop
        LDX     6,SP          ; load return address
        LEAS    10,SP         ; release stack
        JMP     0,X           ; return
  }
#else
  asm {
        PSHD                   ; store page registers
        TFR   X,D
        ADDD  4,SP             ; calculate source end address
        STD   4,SP
        PULB                   ; reload source page
        LDAA  PAGE_ADDR        ; save page register
        PSHA
loop:
        STAB  PAGE_ADDR        ; set source page
        LDAA  1,X+             ; load value
        MOVB  1,SP, PAGE_ADDR  ; set destination page
        STAA  1,Y+
        CPX   4,SP
        BNE   loop

        LDAA  2,SP+            ; restore old page value and release stack
        STAA  PAGE_ADDR        ; store it into page register
        LDX   4,SP+            ; release stack and load return address
        JMP   0,X              ; return
  }
#endif
}

