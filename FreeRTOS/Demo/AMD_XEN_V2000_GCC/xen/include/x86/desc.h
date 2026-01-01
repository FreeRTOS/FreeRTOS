/* -*-  Mode:C; c-basic-offset:4; tab-width:4 -*-
 *
 * (C) 2016 - Juergen Gross, SUSE Linux GmbH
 * based on some header files from Xen Test Framework by Andrew Cooper
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to
 * deal in the Software without restriction, including without limitation the
 * rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

#ifndef _DESC_H_
#define _DESC_H_

/*
 * Count the number of varadic arguments provided.
 *
 * <pre>
 *   VA_NARGS()     => 0
 *   VA_NARGS(x)    => 1
 *   VA_NARGS(x, y) => 2
 * </pre>
 *
 * Currently functions for 0 to 11 arguments.
 */
#define VA_NARGS_(_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, N, ...) N
#define VA_NARGS(...) \
    VA_NARGS_(X,##__VA_ARGS__, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0)

/*
 * Call a macro variation, based on the number of varadic arguments.
 *
 * @param macro Partial token to call a variation of.
 * @param c1    Constant parameter to pass through.
 * @param ...   Varadic arguments to pass through.
 *
 * Tokenises 'macro' with the count of varadic arguments, passing 'c1' and the
 * varadic arguments.
 *
 * <pre>
 *   VAR_MACRO_C1(m, c)          => m0(c)
 *   VAR_MACRO_C1(m, c, x)       => m1(c, x)
 *   VAR_MACRO_C1(m, c, x, y)    => m2(c, x, y)
 *   VAR_MACRO_C1(m, c, x, y, z) => m3(c, x, y, z)
 * </pre>
 */
#define VAR_MACRO_C1__(macro, c1, count, ...) macro##count(c1, ##__VA_ARGS__)
#define VAR_MACRO_C1_(macro, c1, count, ...)        \
    VAR_MACRO_C1__(macro, c1, count, ##__VA_ARGS__)
#define VAR_MACRO_C1(macro, c1, ...)                                \
    VAR_MACRO_C1_(macro, c1, VA_NARGS(__VA_ARGS__), ##__VA_ARGS__)

/*
 * GDT layout:
 *
 *  0 - null
 *  1 - 64bit supervisor code
 *  2 - 32bit supervisor code
 *  3 - 32bit supervisor data
 *  4 - 64bit userspace code
 *  5 - 32bit userspace code
 *  6 - 32bit userspace data
 *  7 - TSS (two slots in long mode)
 *
 *  9-12 - Available for test use
 */

#define GDTE_CS64_DPL0 1
#define GDTE_CS32_DPL0 2
#define GDTE_DS32_DPL0 3
#define GDTE_CS64_DPL3 4
#define GDTE_CS32_DPL3 5
#define GDTE_DS32_DPL3 6

#define GDTE_TSS 7

#define GDTE_AVAIL0     9
#define GDTE_AVAIL1    10
#define GDTE_AVAIL2    11
#define GDTE_AVAIL3    12

#define NR_GDT_ENTRIES 13

#ifdef __x86_64__

#define __KERN_CS (GDTE_CS64_DPL0 * 8)
#define __KERN_DS (0)
#define __USER_CS (GDTE_CS64_DPL3 * 8 + 3)
#define __USER_DS (GDTE_DS32_DPL3 * 8 + 3)

#else /* __x86_64__ */

#define __KERN_CS (GDTE_CS32_DPL0 * 8)
#define __KERN_DS (GDTE_DS32_DPL0 * 8)
#define __USER_CS (GDTE_CS32_DPL3 * 8 + 3)
#define __USER_DS (GDTE_DS32_DPL3 * 8 + 3)

#endif /* __x86_64__ */

#ifndef __ASSEMBLY__
/* 8 byte user segment descriptor (GDT/LDT entries with .s = 1) */
struct __attribute__ ((__packed__)) seg_desc32 {
    union {
        /* Raw backing integers. */
        struct {
            uint32_t lo, hi;
        };
        /* Common named fields. */
        struct {
            uint16_t limit0;
            uint16_t base0;
            uint8_t  base1;
            unsigned type: 4;
            unsigned s: 1, dpl: 2, p: 1;
            unsigned limit: 4;
            unsigned avl: 1, l: 1, d: 1, g: 1;
            uint8_t base2;
        };
        /* Code segment specific field names. */
        struct {
            uint16_t limit0;
            uint16_t base0;
            uint8_t  base1;
            unsigned a: 1, r: 1, c: 1, x: 1;
            unsigned s: 1, dpl: 2, p: 1;
            unsigned limit: 4;
            unsigned avl: 1, l: 1, d: 1, g: 1;
            uint8_t base2;
        } code;
        /* Data segment specific field names. */
        struct {
            uint16_t limit0;
            uint16_t base0;
            uint8_t  base1;
            unsigned a: 1, w: 1, e: 1, x: 1;
            unsigned s: 1, dpl: 2, p: 1;
            unsigned limit: 4;
            unsigned avl: 1, _r0: 1, b: 1, g: 1;
            uint8_t base2;
        } data;
    };
};

/* 8-byte gate - Protected mode IDT entry, GDT task/call gate. */
struct __attribute__ ((__packed__)) seg_gate32 {
    union {
        struct {
            uint32_t lo, hi;
        };
        struct {
            uint16_t offset0;
            uint16_t selector;
            uint8_t  _r0;
            unsigned type: 4, s: 1, dpl: 2, p: 1;
            uint16_t offset1;
        };
    };
};

/* 16-byte gate - Long mode IDT entry. */
struct __attribute__ ((__packed__)) seg_gate64 {
    union {
        struct {
            uint64_t lo, hi;
        };
        struct {
            uint16_t offset0;
            uint16_t selector;
            unsigned ist: 3, _r0: 5, type: 4, s: 1, dpl: 2, p: 1;
            uint16_t offset1;
            uint32_t offset2;
            uint32_t _r1;
        };
    };
};

/* GDT/LDT attribute flags for user segments */

/* Common */
#define SEG_ATTR_G      0x8000 /* Granularity of limit (0 = 1, 1 = 4K) */
#define SEG_ATTR_AVL    0x1000 /* Available for software use */
#define SEG_ATTR_P      0x0080 /* Present? */
#define SEG_ATTR_S      0x0010 /* !System desc (0 = system, 1 = user) */
#define SEG_ATTR_A      0x0001 /* Accessed? (set by hardware) */

#define SEG_ATTR_COMMON 0x8091 /* Commonly set bits (G P S A) */

#define SEG_ATTR_DPL0   0x0000 /* Descriptor privilege level 0 */
#define SEG_ATTR_DPL1   0x0020 /* Descriptor privilege level 1 */
#define SEG_ATTR_DPL2   0x0040 /* Descriptor privilege level 2 */
#define SEG_ATTR_DPL3   0x0060 /* Descriptor privilege level 3 */
#define SEG_ATTR_CODE   0x0008 /* Type (0 = data, 1 = code)    */
#define SEG_ATTR_DATA   0x0000 /* Type (0 = data, 1 = code)    */

/* Code segments */
#define SEG_ATTR_D      0x4000 /* Default operand size (0 = 16bit, 1 = 32bit) */
#define SEG_ATTR_L      0x2000 /* Long segment? (1 = 64bit) */
#define SEG_ATTR_C      0x0004 /* Conforming? (0 = non, 1 = conforming) */
#define SEG_ATTR_R      0x0002 /* Readable? (0 = XO seg, 1 = RX seg) */

/* Data segments */
#define SEG_ATTR_B      0x4000 /* 'Big' flag.
                                *    - For %ss, default operand size.
                                *    - For expand-down segment, sets upper bound. */
#define SEG_ATTR_E      0x0004 /* Expand-down? (0 = normal, 1 = expand-down) */
#define SEG_ATTR_W      0x0002 /* Writable? (0 = RO seg, 1 = RW seg) */

/*
 * Initialise an LDT/GDT entry using a raw attribute number.
 *
 * @param base  Segment base.
 * @param limit Segment limit.
 * @param attr  Segment attributes.
 */
#define INIT_GDTE(base, limit, attr) { { {                            \
     .lo = (((base) & 0xffff) << 16) | ((limit) & 0xffff),            \
     .hi = ((base) & 0xff000000) | ((limit) & 0xf0000) |              \
           (((attr) & 0xf0ff) << 8) | (((base) & 0xff0000) >> 16)     \
     } } }

/*
 * Tokenise and OR together.
 *
 * For each varadic parameter, tokenise with 't' and OR together.
 *
 * @param t   Common stem partial token.
 * @param ... Partial tokens.
 *
 * Example:
 * <pre>
 *   TOK_OR(t, x, y)    => (t ## x | t ## y)
 *   TOK_OR(t, x, y, z) => (t ## x | t ## y | t ## z)
 * </pre>
 */
#define TOK_OR0(t)         (0)
#define TOK_OR1(t, x)      (t ## x)
#define TOK_OR2(t, x, ...) (t ## x | TOK_OR1(t, ##__VA_ARGS__))
#define TOK_OR3(t, x, ...) (t ## x | TOK_OR2(t, ##__VA_ARGS__))
#define TOK_OR4(t, x, ...) (t ## x | TOK_OR3(t, ##__VA_ARGS__))
#define TOK_OR5(t, x, ...) (t ## x | TOK_OR4(t, ##__VA_ARGS__))
#define TOK_OR6(t, x, ...) (t ## x | TOK_OR5(t, ##__VA_ARGS__))
#define TOK_OR7(t, x, ...) (t ## x | TOK_OR6(t, ##__VA_ARGS__))
#define TOK_OR8(t, x, ...) (t ## x | TOK_OR7(t, ##__VA_ARGS__))
#define TOK_OR(t, ...)     VAR_MACRO_C1(TOK_OR, t, ##__VA_ARGS__)

/*
 * Initialise an LDT/GDT entry using SEG_ATTR_ mnemonics.
 *
 * @param base  Segment base.
 * @param limit Segment limit.
 * @param ...   Partial SEG_ATTR_ tokens for attributes.
 *
 * Example usage:
 * - INIT_GDTE_SYM(0, 0xfffff, P)
 *   - uses @ref SEG_ATTR_P
 *
 * - INIT_GDTE_SYM(0, 0xfffff, CODE, L)
 *   - uses @ref SEG_ATTR_CODE and @ref SEG_ATTR_L
 */
#define INIT_GDTE_SYM(base, limit, ...) \
    INIT_GDTE(base, limit, TOK_OR(SEG_ATTR_, ##__VA_ARGS__))

/* Long mode lgdt/lidt table pointer. */
struct __attribute__ ((__packed__)) desc_ptr64 {
    uint16_t limit;
    uint64_t base;
};

/* Protected mode lgdt/lidt table pointer. */
struct __attribute__ ((__packed__)) desc_ptr32 {
    uint16_t limit;
    uint32_t base;
};

struct __attribute__ ((__packed__)) hw_tss32 {
    uint16_t link; uint16_t _r0;

    uint32_t esp0;
    uint16_t ss0; uint16_t _r1;

    uint32_t esp1;
    uint16_t ss1; uint16_t _r2;

    uint32_t esp2;
    uint16_t ss2; uint16_t _r3;

    uint32_t cr3;
    uint32_t eip;
    uint32_t eflags;
    uint32_t eax;
    uint32_t ecx;
    uint32_t edx;
    uint32_t ebx;
    uint32_t esp;
    uint32_t ebp;
    uint32_t esi;
    uint32_t edi;

    uint16_t es; uint16_t _r4;
    uint16_t cs; uint16_t _r5;
    uint16_t ss; uint16_t _r6;
    uint16_t ds; uint16_t _r7;
    uint16_t fs; uint16_t _r8;
    uint16_t gs; uint16_t _r9;
    uint16_t ldtr; uint16_t _r10;
    uint16_t t; uint16_t iopb;
};

struct __attribute__ ((__packed__)) hw_tss64 {
    uint16_t link; uint16_t _r0;

    uint64_t rsp0;
    uint64_t rsp1;
    uint64_t rsp2;

    uint64_t _r1;

    uint64_t ist[7]; /* 1-based structure */

    uint64_t _r2;

    uint16_t t;
    uint16_t iopb;
};

#define X86_TSS_INVALID_IO_BITMAP 0x8000

#if defined(__x86_64__)

typedef struct desc_ptr64 desc_ptr;
typedef struct seg_desc32 user_desc;
typedef struct seg_gate64 gate_desc;
typedef struct hw_tss64 hw_tss;

#elif defined(__i386__)

typedef struct desc_ptr32 desc_ptr;
typedef struct seg_desc32 user_desc;
typedef struct seg_gate32 gate_desc;
typedef struct hw_tss32 hw_tss;

#endif

//extern user_desc gdt[NR_GDT_ENTRIES];
extern desc_ptr  gdt_ptr;

extern gate_desc idt[256];
extern desc_ptr  idt_ptr;

extern hw_tss tss;

#endif

#endif /* _DESC_H_ */
