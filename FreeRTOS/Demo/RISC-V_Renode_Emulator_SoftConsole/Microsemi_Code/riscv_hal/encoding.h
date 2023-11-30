/*******************************************************************************
 * (c) Copyright 2016-2018 Microsemi SoC Products Group.  All rights reserved.
 *
 * @file encodings.h
 * @author Microsemi SoC Products Group
 * @brief Mi-V soft processor register bit mask and shift constants encodings.
 *
 * SVN $Revision: 9825 $
 * SVN $Date: 2018-03-19 10:31:41 +0530 (Mon, 19 Mar 2018) $
 */
#ifndef RISCV_CSR_ENCODING_H
#define RISCV_CSR_ENCODING_H

#ifdef __cplusplus
extern "C" {
#endif

#define MSTATUS_UIE         0x00000001
#define MSTATUS_SIE         0x00000002
#define MSTATUS_HIE         0x00000004
#define MSTATUS_MIE         0x00000008
#define MSTATUS_UPIE        0x00000010
#define MSTATUS_SPIE        0x00000020
#define MSTATUS_HPIE        0x00000040
#define MSTATUS_MPIE        0x00000080
#define MSTATUS_SPP         0x00000100
#define MSTATUS_HPP         0x00000600
#define MSTATUS_MPP         0x00001800
#define MSTATUS_FS          0x00006000
#define MSTATUS_XS          0x00018000
#define MSTATUS_MPRV        0x00020000
#define MSTATUS_SUM         0x00040000      /*changed in v1.10*/
#define MSTATUS_MXR         0x00080000      /*changed in v1.10*/
#define MSTATUS_TVM         0x00100000      /*changed in v1.10*/
#define MSTATUS_TW          0x00200000      /*changed in v1.10*/
#define MSTATUS_TSR         0x00400000      /*changed in v1.10*/
#define MSTATUS_RES         0x7F800000      /*changed in v1.10*/
#define MSTATUS32_SD        0x80000000
#define MSTATUS64_SD        0x8000000000000000

#define MCAUSE32_CAUSE       0x7FFFFFFF
#define MCAUSE64_CAUSE       0x7FFFFFFFFFFFFFFF
#define MCAUSE32_INT         0x80000000
#define MCAUSE64_INT         0x8000000000000000

#define SSTATUS_UIE         0x00000001
#define SSTATUS_SIE         0x00000002
#define SSTATUS_UPIE        0x00000010
#define SSTATUS_SPIE        0x00000020
#define SSTATUS_SPP         0x00000100
#define SSTATUS_FS          0x00006000
#define SSTATUS_XS          0x00018000
#define SSTATUS_PUM         0x00040000
#define SSTATUS32_SD        0x80000000
#define SSTATUS64_SD        0x8000000000000000

#define MIP_SSIP            (1u << IRQ_S_SOFT)
#define MIP_HSIP            (1u << IRQ_H_SOFT)
#define MIP_MSIP            (1u << IRQ_M_SOFT)
#define MIP_STIP            (1u << IRQ_S_TIMER)
#define MIP_HTIP            (1u << IRQ_H_TIMER)
#define MIP_MTIP            (1u << IRQ_M_TIMER)
#define MIP_SEIP            (1u << IRQ_S_EXT)
#define MIP_HEIP            (1u << IRQ_H_EXT)
#define MIP_MEIP            (1u << IRQ_M_EXT)

#define SIP_SSIP            MIP_SSIP
#define SIP_STIP            MIP_STIP

#define PRV_U               0
#define PRV_S               1
#define PRV_H               2
#define PRV_M               3

#define VM_MBARE            0
#define VM_MBB              1
#define VM_MBBID            2
#define VM_SV32             8
#define VM_SV39             9
#define VM_SV48             10

#define IRQ_S_SOFT          1
#define IRQ_H_SOFT          2
#define IRQ_M_SOFT          3
#define IRQ_S_TIMER         5
#define IRQ_H_TIMER         6
#define IRQ_M_TIMER         7
#define IRQ_S_EXT           9
#define IRQ_H_EXT           10
#define IRQ_M_EXT           11

#define DEFAULT_RSTVEC      0x00001000
#define DEFAULT_NMIVEC      0x00001004
#define DEFAULT_MTVEC       0x00001010
#define CONFIG_STRING_ADDR  0x0000100C
#define EXT_IO_BASE         0x40000000
#define DRAM_BASE           0x80000000

/* page table entry (PTE) fields */
#define PTE_V               0x001       /* Valid */
#define PTE_TYPE            0x01E       /* Type  */
#define PTE_R               0x020       /* Referenced */
#define PTE_D               0x040       /* Dirty */
#define PTE_SOFT            0x380       /* Reserved for Software */

#define PTE_TYPE_TABLE        0x00
#define PTE_TYPE_TABLE_GLOBAL 0x02
#define PTE_TYPE_URX_SR       0x04
#define PTE_TYPE_URWX_SRW     0x06
#define PTE_TYPE_UR_SR        0x08
#define PTE_TYPE_URW_SRW      0x0A
#define PTE_TYPE_URX_SRX      0x0C
#define PTE_TYPE_URWX_SRWX    0x0E
#define PTE_TYPE_SR           0x10
#define PTE_TYPE_SRW          0x12
#define PTE_TYPE_SRX          0x14
#define PTE_TYPE_SRWX         0x16
#define PTE_TYPE_SR_GLOBAL    0x18
#define PTE_TYPE_SRW_GLOBAL   0x1A
#define PTE_TYPE_SRX_GLOBAL   0x1C
#define PTE_TYPE_SRWX_GLOBAL  0x1E

#define PTE_PPN_SHIFT 10

#define PTE_TABLE(PTE) ((0x0000000AU >> ((PTE) & 0x1F)) & 1)
#define PTE_UR(PTE)    ((0x0000AAA0U >> ((PTE) & 0x1F)) & 1)
#define PTE_UW(PTE)    ((0x00008880U >> ((PTE) & 0x1F)) & 1)
#define PTE_UX(PTE)    ((0x0000A0A0U >> ((PTE) & 0x1F)) & 1)
#define PTE_SR(PTE)    ((0xAAAAAAA0U >> ((PTE) & 0x1F)) & 1)
#define PTE_SW(PTE)    ((0x88888880U >> ((PTE) & 0x1F)) & 1)
#define PTE_SX(PTE)    ((0xA0A0A000U >> ((PTE) & 0x1F)) & 1)

#define PTE_CHECK_PERM(PTE, SUPERVISOR, STORE, FETCH) \
  ((STORE) ? ((SUPERVISOR) ? PTE_SW(PTE) : PTE_UW(PTE)) : \
   (FETCH) ? ((SUPERVISOR) ? PTE_SX(PTE) : PTE_UX(PTE)) : \
             ((SUPERVISOR) ? PTE_SR(PTE) : PTE_UR(PTE)))

#ifdef __riscv

#if __riscv_xlen == 64
# define MSTATUS_SD             MSTATUS64_SD
# define SSTATUS_SD             SSTATUS64_SD
# define MCAUSE_INT             MCAUSE64_INT
# define MCAUSE_CAUSE           MCAUSE64_CAUSE
# define RISCV_PGLEVEL_BITS     9
#else
# define MSTATUS_SD             MSTATUS32_SD
# define SSTATUS_SD             SSTATUS32_SD
# define RISCV_PGLEVEL_BITS     10
# define MCAUSE_INT             MCAUSE32_INT
# define MCAUSE_CAUSE           MCAUSE32_CAUSE
#endif

#define RISCV_PGSHIFT           12
#define RISCV_PGSIZE            (1 << RISCV_PGSHIFT)

#ifndef __ASSEMBLER__

#ifdef __GNUC__

#define read_csr(reg) ({ unsigned long __tmp; \
  asm volatile ("csrr %0, " #reg : "=r"(__tmp)); \
  __tmp; })

#define write_csr(reg, val) ({ \
  if (__builtin_constant_p(val) && (unsigned long)(val) < 32) \
    asm volatile ("csrw " #reg ", %0" :: "i"(val)); \
  else \
    asm volatile ("csrw " #reg ", %0" :: "r"(val)); })

#define swap_csr(reg, val) ({ unsigned long __tmp; \
  if (__builtin_constant_p(val) && (unsigned long)(val) < 32) \
    asm volatile ("csrrw %0, " #reg ", %1" : "=r"(__tmp) : "i"(val)); \
  else \
    asm volatile ("csrrw %0, " #reg ", %1" : "=r"(__tmp) : "r"(val)); \
  __tmp; })

#define set_csr(reg, bit) ({ unsigned long __tmp; \
  if (__builtin_constant_p(bit) && (unsigned long)(bit) < 32) \
    asm volatile ("csrrs %0, " #reg ", %1" : "=r"(__tmp) : "i"(bit)); \
  else \
    asm volatile ("csrrs %0, " #reg ", %1" : "=r"(__tmp) : "r"(bit)); \
  __tmp; })

#define clear_csr(reg, bit) ({ unsigned long __tmp; \
  if (__builtin_constant_p(bit) && (unsigned long)(bit) < 32) \
    asm volatile ("csrrc %0, " #reg ", %1" : "=r"(__tmp) : "i"(bit)); \
  else \
    asm volatile ("csrrc %0, " #reg ", %1" : "=r"(__tmp) : "r"(bit)); \
  __tmp; })

#define rdtime() read_csr(time)
#define rdcycle() read_csr(cycle)
#define rdinstret() read_csr(instret)

#ifdef __riscv_atomic

#define MASK(nr)                    (1UL << nr)
#define MASK_NOT(nr)                (~(1UL << nr))

/**
 * atomic_read - read atomic variable
 * @v: pointer of type int
 *
 * Atomically reads the value of @v.
 */
static inline int atomic_read(const int *v)
{
    return *((volatile int *)(v));
}

/**
 * atomic_set - set atomic variable
 * @v: pointer of type int
 * @i: required value
 *
 * Atomically sets the value of @v to @i.
 */
static inline void atomic_set(int *v, int i)
{
    *v = i;
}

/**
 * atomic_add - add integer to atomic variable
 * @i: integer value to add
 * @v: pointer of type int
 *
 * Atomically adds @i to @v.
 */
static inline void atomic_add(int i, int *v)
{
    __asm__ __volatile__ (
        "amoadd.w zero, %1, %0"
        : "+A" (*v)
        : "r" (i));
}

static inline int atomic_fetch_add(unsigned int mask, int *v)
{
    int out;

    __asm__ __volatile__ (
        "amoadd.w %2, %1, %0"
        : "+A" (*v), "=r" (out)
        : "r" (mask));
    return out;
}

/**
 * atomic_sub - subtract integer from atomic variable
 * @i: integer value to subtract
 * @v: pointer of type int
 *
 * Atomically subtracts @i from @v.
 */
static inline void atomic_sub(int i, int *v)
{
    atomic_add(-i, v);
}

static inline int atomic_fetch_sub(unsigned int mask, int *v)
{
    int out;

    __asm__ __volatile__ (
        "amosub.w %2, %1, %0"
        : "+A" (*v), "=r" (out)
        : "r" (mask));
    return out;
}

/**
 * atomic_add_return - add integer to atomic variable
 * @i: integer value to add
 * @v: pointer of type int
 *
 * Atomically adds @i to @v and returns the result
 */
static inline int atomic_add_return(int i, int *v)
{
    register int c;
    __asm__ __volatile__ (
        "amoadd.w %0, %2, %1"
        : "=r" (c), "+A" (*v)
        : "r" (i));
    return (c + i);
}

/**
 * atomic_sub_return - subtract integer from atomic variable
 * @i: integer value to subtract
 * @v: pointer of type int
 *
 * Atomically subtracts @i from @v and returns the result
 */
static inline int atomic_sub_return(int i, int *v)
{
    return atomic_add_return(-i, v);
}

/**
 * atomic_inc - increment atomic variable
 * @v: pointer of type int
 *
 * Atomically increments @v by 1.
 */
static inline void atomic_inc(int *v)
{
    atomic_add(1, v);
}

/**
 * atomic_dec - decrement atomic variable
 * @v: pointer of type int
 *
 * Atomically decrements @v by 1.
 */
static inline void atomic_dec(int *v)
{
    atomic_add(-1, v);
}

static inline int atomic_inc_return(int *v)
{
    return atomic_add_return(1, v);
}

static inline int atomic_dec_return(int *v)
{
    return atomic_sub_return(1, v);
}

/**
 * atomic_sub_and_test - subtract value from variable and test result
 * @i: integer value to subtract
 * @v: pointer of type int
 *
 * Atomically subtracts @i from @v and returns
 * true if the result is zero, or false for all
 * other cases.
 */
static inline int atomic_sub_and_test(int i, int *v)
{
    return (atomic_sub_return(i, v) == 0);
}

/**
 * atomic_inc_and_test - increment and test
 * @v: pointer of type int
 *
 * Atomically increments @v by 1
 * and returns true if the result is zero, or false for all
 * other cases.
 */
static inline int atomic_inc_and_test(int *v)
{
    return (atomic_inc_return(v) == 0);
}

/**
 * atomic_dec_and_test - decrement and test
 * @v: pointer of type int
 *
 * Atomically decrements @v by 1 and
 * returns true if the result is 0, or false for all other
 * cases.
 */
static inline int atomic_dec_and_test(int *v)
{
    return (atomic_dec_return(v) == 0);
}

/**
 * atomic_add_negative - add and test if negative
 * @i: integer value to add
 * @v: pointer of type int
 *
 * Atomically adds @i to @v and returns true
 * if the result is negative, or false when
 * result is greater than or equal to zero.
 */
static inline int atomic_add_negative(int i, int *v)
{
    return (atomic_add_return(i, v) < 0);
}

static inline int atomic_xchg(int *v, int n)
{
    register int c;
    __asm__ __volatile__ (
        "amoswap.w %0, %2, %1"
        : "=r" (c), "+A" (*v)
        : "r" (n));
    return c;
}

/**
 * atomic_and - Atomically clear bits in atomic variable
 * @mask: Mask of the bits to be retained
 * @v: pointer of type int
 *
 * Atomically retains the bits set in @mask from @v
 */
static inline void atomic_and(unsigned int mask, int *v)
{
    __asm__ __volatile__ (
        "amoand.w zero, %1, %0"
        : "+A" (*v)
        : "r" (mask));
}

static inline int atomic_fetch_and(unsigned int mask, int *v)
{
    int out;
    __asm__ __volatile__ (
        "amoand.w %2, %1, %0"
        : "+A" (*v), "=r" (out)
        : "r" (mask));
    return out;
}

/**
 * atomic_or - Atomically set bits in atomic variable
 * @mask: Mask of the bits to be set
 * @v: pointer of type int
 *
 * Atomically sets the bits set in @mask in @v
 */
static inline void atomic_or(unsigned int mask, int *v)
{
    __asm__ __volatile__ (
        "amoor.w zero, %1, %0"
        : "+A" (*v)
        : "r" (mask));
}

static inline int atomic_fetch_or(unsigned int mask, int *v)
{
    int out;
    __asm__ __volatile__ (
        "amoor.w %2, %1, %0"
        : "+A" (*v), "=r" (out)
        : "r" (mask));
    return out;
}

/**
 * atomic_xor - Atomically flips bits in atomic variable
 * @mask: Mask of the bits to be flipped
 * @v: pointer of type int
 *
 * Atomically flips the bits set in @mask in @v
 */
static inline void atomic_xor(unsigned int mask, int *v)
{
    __asm__ __volatile__ (
        "amoxor.w zero, %1, %0"
        : "+A" (*v)
        : "r" (mask));
}

static inline int atomic_fetch_xor(unsigned int mask, int *v)
{
    int out;
    __asm__ __volatile__ (
        "amoxor.w %2, %1, %0"
        : "+A" (*v), "=r" (out)
        : "r" (mask));
    return out;
}

/*----------------------------------------------------*/

/**
 * test_and_set_bit - Set a bit and return its old value
 * @nr: Bit to set
 * @addr: Address to count from
 *
 * This operation is atomic and cannot be reordered.
 * It also implies a memory barrier.
 */
static inline int test_and_set_bit(int nr, volatile unsigned long *addr)
{
    unsigned long __res, __mask;
    __mask = MASK(nr);
    __asm__ __volatile__ (                \
        "amoor.w %0, %2, %1"            \
        : "=r" (__res), "+A" (*addr)    \
        : "r" (__mask));                \

        return ((__res & __mask) != 0);
}


/**
 * test_and_clear_bit - Clear a bit and return its old value
 * @nr: Bit to clear
 * @addr: Address to count from
 *
 * This operation is atomic and cannot be reordered.
 * It also implies a memory barrier.
 */
static inline int test_and_clear_bit(int nr, volatile unsigned long *addr)
{
    unsigned long __res, __mask;
    __mask = MASK_NOT(nr);
    __asm__ __volatile__ (                \
        "amoand.w %0, %2, %1"            \
        : "=r" (__res), "+A" (*addr)    \
        : "r" (__mask));                \

        return ((__res & __mask) != 0);
}

/**
 * test_and_change_bit - Change a bit and return its old value
 * @nr: Bit to change
 * @addr: Address to count from
 *
 * This operation is atomic and cannot be reordered.
 * It also implies a memory barrier.
 */
static inline int test_and_change_bit(int nr, volatile unsigned long *addr)
{

    unsigned long __res, __mask;
    __mask = MASK(nr);
    __asm__ __volatile__ (                \
        "amoxor.w %0, %2, %1"            \
        : "=r" (__res), "+A" (*addr)    \
        : "r" (__mask));                \

        return ((__res & __mask) != 0);
}

/**
 * set_bit - Atomically set a bit in memory
 * @nr: the bit to set
 * @addr: the address to start counting from
 *
 * This function is atomic and may not be reordered. 
 */

static inline void set_bit(int nr, volatile unsigned long *addr)
{
    __asm__ __volatile__ (                    \
        "AMOOR.w zero, %1, %0"            \
        : "+A" (*addr)            \
        : "r" (MASK(nr)));
}

/**
 * clear_bit - Clears a bit in memory
 * @nr: Bit to clear
 * @addr: Address to start counting from
 *
 * clear_bit() is atomic and may not be reordered.  
 */
static inline void clear_bit(int nr, volatile unsigned long *addr)
{
    __asm__ __volatile__ (                    \
        "AMOAND.w zero, %1, %0"            \
        : "+A" (*addr)            \
        : "r" (MASK_NOT(nr)));
}

/**
 * change_bit - Toggle a bit in memory
 * @nr: Bit to change
 * @addr: Address to start counting from
 *
 * change_bit() is atomic and may not be reordered.
 */
static inline void change_bit(int nr, volatile unsigned long *addr)
{
    __asm__ __volatile__ (                    \
            "AMOXOR.w zero, %1, %0"            \
            : "+A" (*addr)            \
            : "r" (MASK(nr)));
}

#endif /* __riscv_atomic */

#endif  /*__GNUC__*/

#endif  /*__ASSEMBLER__*/

#endif  /*__riscv*/

#ifdef __cplusplus
}
#endif

#endif    /*RISCV_CSR_ENCODING_H*/

