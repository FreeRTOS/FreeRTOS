/* os
 *
 * Copyright (C) 2025 Advanced Micro Devices, Inc. or its affiliates. All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 *
 */



#ifndef _OS_H_
#define _OS_H_

#define smp_processor_id() 0


#ifndef __ASSEMBLY
#include <hypervisor.h>
#include <xen/xsm/flask_op.h>

#define USED    __attribute__ ((used))

void do_exit(void);

#define BUG do_exit

#endif
#include <xen/xen.h>

#define MSR_EFER          0xc0000080
#define _EFER_LME         8             /* Long mode enable */

#define X86_CR0_WP        0x00010000    /* Write protect */
#define X86_CR0_PG        0x80000000    /* Paging */
#define X86_CR4_PAE       0x00000020    /* enable physical address extensions */
#define X86_CR4_OSFXSR    0x00000200    /* enable fast FPU save and restore */

#define X86_EFLAGS_IF     0x00000200

#define __KERNEL_CS  FLAT_KERNEL_CS
#define __KERNEL_DS  FLAT_KERNEL_DS
#define __KERNEL_SS  FLAT_KERNEL_SS

#define TRAP_divide_error      0
#define TRAP_debug             1
#define TRAP_nmi               2
#define TRAP_int3              3
#define TRAP_overflow          4
#define TRAP_bounds            5
#define TRAP_invalid_op        6
#define TRAP_no_device         7
#define TRAP_double_fault      8
#define TRAP_copro_seg         9
#define TRAP_invalid_tss      10
#define TRAP_no_segment       11
#define TRAP_stack_error      12
#define TRAP_gp_fault         13
#define TRAP_page_fault       14
#define TRAP_spurious_int     15
#define TRAP_copro_error      16
#define TRAP_alignment_check  17
#define TRAP_machine_check    18
#define TRAP_simd_error       19
#define TRAP_deferred_nmi     31
#define TRAP_xen_callback     32

#if defined(__i386__)
#define __SZ    "l"
#define __REG   "e"
#else
#define __SZ    "q"
#define __REG   "r"
#endif

#define ASM_SP  __REG"sp"

/* Everything below this point is not included by assembler (.S) files. */
#ifndef __ASSEMBLY__

extern shared_info_t *HYPERVISOR_shared_info;

void trap_init(void);
void trap_fini(void);
#ifndef CONFIG_PARAVIRT
void xen_callback_vector(void);
#endif

void arch_pre_suspend(void);
int  arch_suspend(void);
void arch_post_suspend(int canceled);
void arch_fini(void);

#ifdef CONFIG_PARAVIRT

/* 
 * The use of 'barrier' in the following reflects their use as local-lock
 * operations. Reentrancy must be prevented (e.g., __cli()) /before/ following
 * critical operations are executed. All critical operations must complete
 * /before/ reentrancy is permitted (e.g., __sti()). Alpha architecture also
 * includes these barriers, for example.
 */

#define __cli()								\
do {									\
	vcpu_info_t *_vcpu;						\
	_vcpu = &HYPERVISOR_shared_info->vcpu_info[smp_processor_id()];	\
	_vcpu->evtchn_upcall_mask = 1;					\
	barrier();							\
} while (0)

#define __sti()								\
do {									\
	vcpu_info_t *_vcpu;						\
	barrier();							\
	_vcpu = &HYPERVISOR_shared_info->vcpu_info[smp_processor_id()];	\
	_vcpu->evtchn_upcall_mask = 0;					\
	barrier(); /* unmask then check (avoid races) */		\
	if ( unlikely(_vcpu->evtchn_upcall_pending) )			\
		force_evtchn_callback();				\
} while (0)

#define __save_flags(x)							\
do {									\
	vcpu_info_t *_vcpu;						\
	_vcpu = &HYPERVISOR_shared_info->vcpu_info[smp_processor_id()];	\
	(x) = _vcpu->evtchn_upcall_mask;				\
} while (0)

#define __restore_flags(x)						\
do {									\
	vcpu_info_t *_vcpu;						\
	barrier();							\
	_vcpu = &HYPERVISOR_shared_info->vcpu_info[smp_processor_id()];	\
	if ((_vcpu->evtchn_upcall_mask = (x)) == 0) {			\
		barrier(); /* unmask then check (avoid races) */	\
		if ( unlikely(_vcpu->evtchn_upcall_pending) )		\
			force_evtchn_callback();			\
	}\
} while (0)

#define safe_halt()		((void)0)

#define __save_and_cli(x)						\
do {									\
	vcpu_info_t *_vcpu;						\
	_vcpu = &HYPERVISOR_shared_info->vcpu_info[smp_processor_id()];	\
	(x) = _vcpu->evtchn_upcall_mask;				\
	_vcpu->evtchn_upcall_mask = 1;					\
	barrier();							\
} while (0)

#define irqs_disabled()			\
    HYPERVISOR_shared_info->vcpu_info[smp_processor_id()].evtchn_upcall_mask

#else

#define __cli() asm volatile ( "cli" : : : "memory" )
#define __sti() asm volatile ( "sti" : : : "memory" )

#define __save_flags(x)                                                 \
do {                                                                    \
    unsigned long __f;                                                  \
    asm volatile ( "pushf" __SZ " ; pop" __SZ " %0" : "=g" (__f));      \
    x = (__f & X86_EFLAGS_IF) ? 1 : 0;                                  \
} while (0)

#define __restore_flags(x)                                              \
do {                                                                    \
    if (x) __sti();                                                     \
    else __cli();                                                       \
} while (0)

#define __save_and_cli(x)                                               \
do {                                                                    \
    __save_flags(x);                                                    \
    __cli();                                                            \
} while (0)

static inline int irqs_disabled(void)
{
    int flag;

    __save_flags(flag);
    return !flag;
}

#endif

#ifdef __INSIDE_MINIOS__
#define local_irq_save(x)	__save_and_cli(x)
#define local_irq_restore(x)	__restore_flags(x)
#define local_save_flags(x)	__save_flags(x)
#define local_irq_disable()	__cli()
#define local_irq_enable()	__sti()
#else
unsigned long __local_irq_save(void);
void __local_irq_restore(unsigned long flags);
unsigned long __local_save_flags(void);
void __local_irq_disable(void);
void __local_irq_enable(void);
#define local_irq_save(x)       x = __local_irq_save()
#define local_irq_restore(x)    __local_irq_restore(x)
#define local_save_flags(x)     x = __local_save_flags()
#define local_irq_disable()     __local_irq_disable()
#define local_irq_enable()      __local_irq_enable()
#endif

/* This is a barrier for the compiler only, NOT the processor! */
#define barrier() __asm__ __volatile__("": : :"memory")

#if defined(__i386__)
#define mb()    __asm__ __volatile__ ("lock; addl $0,0(%%esp)": : :"memory")
#define rmb()   __asm__ __volatile__ ("lock; addl $0,0(%%esp)": : :"memory")
#define wmb()	__asm__ __volatile__ ("": : :"memory")
#elif defined(__x86_64__)
#define mb()    __asm__ __volatile__ ("mfence":::"memory")
#define rmb()   __asm__ __volatile__ ("lfence":::"memory")
#define wmb()	__asm__ __volatile__ ("sfence" ::: "memory") /* From CONFIG_UNORDERED_IO (linux) */
#endif


#define LOCK_PREFIX ""
#define LOCK ""
#define ADDR (*(volatile long *) addr)
/*
 * Make sure gcc doesn't try to be clever and move things around
 * on us. We need to use _exactly_ the address the user gave us,
 * not some alias that contains the same information.
 */
typedef struct { volatile int counter; } atomic_t;

static inline void write_cr3(unsigned long cr3)
{
    asm volatile( "mov %0, %%cr3" : : "r" (cr3) : "memory" );
}

static inline void invlpg(unsigned long va)
{
    asm volatile ( "invlpg %0": : "m" (*(const char *)(va)) : "memory" );
}

/************************** i386 *******************************/
#ifdef __INSIDE_MINIOS__
#if defined (__i386__)

#define xchg(ptr,v) ((__typeof__(*(ptr)))__xchg((unsigned long)(v),(ptr),sizeof(*(ptr))))
struct __xchg_dummy { unsigned long a[100]; };
#define __xg(x) ((struct __xchg_dummy *)(x))
static inline unsigned long __xchg(unsigned long x, volatile void * ptr, int size)
{
	switch (size) {
		case 1:
			__asm__ __volatile__("xchgb %b0,%1"
				:"=q" (x)
				:"m" (*__xg(ptr)), "0" (x)
				:"memory");
			break;
		case 2:
			__asm__ __volatile__("xchgw %w0,%1"
				:"=r" (x)
				:"m" (*__xg(ptr)), "0" (x)
				:"memory");
			break;
		case 4:
			__asm__ __volatile__("xchgl %0,%1"
				:"=r" (x)
				:"m" (*__xg(ptr)), "0" (x)
				:"memory");
			break;
	}
	return x;
}

/**
 * test_and_clear_bit - Clear a bit and return its old value
 * @nr: Bit to clear
 * @addr: Address to count from
 *
 * This operation is atomic and cannot be reordered.
 * It can be reorderdered on other architectures other than x86.
 * It also implies a memory barrier.
 */
static inline int test_and_clear_bit(int nr, volatile unsigned long * addr)
{
	int oldbit;

	__asm__ __volatile__( LOCK
		"btrl %2,%1\n\tsbbl %0,%0"
		:"=r" (oldbit),"=m" (ADDR)
		:"Ir" (nr) : "memory");
	return oldbit;
}

static inline int constant_test_bit(int nr, const volatile unsigned long *addr)
{
	return ((1UL << (nr & 31)) & (addr[nr >> 5])) != 0;
}

static inline int variable_test_bit(int nr, const volatile unsigned long * addr)
{
	int oldbit;

	__asm__ __volatile__(
		"btl %2,%1\n\tsbbl %0,%0"
		:"=r" (oldbit)
		:"m" (ADDR),"Ir" (nr));
	return oldbit;
}

#define test_bit(nr,addr) \
(__builtin_constant_p(nr) ? \
 constant_test_bit((nr),(addr)) : \
 variable_test_bit((nr),(addr)))

/**
 * set_bit - Atomically set a bit in memory
 * @nr: the bit to set
 * @addr: the address to start counting from
 *
 * This function is atomic and may not be reordered.  See __set_bit()
 * if you do not require the atomic guarantees.
 *
 * Note: there are no guarantees that this function will not be reordered
 * on non x86 architectures, so if you are writting portable code,
 * make sure not to rely on its reordering guarantees.
 *
 * Note that @nr may be almost arbitrarily large; this function is not
 * restricted to acting on a single-word quantity.
 */
static inline void set_bit(int nr, volatile unsigned long * addr)
{
	__asm__ __volatile__( LOCK
		"btsl %1,%0"
		:"=m" (ADDR)
		:"Ir" (nr));
}

/**
 * clear_bit - Clears a bit in memory
 * @nr: Bit to clear
 * @addr: Address to start counting from
 *
 * clear_bit() is atomic and may not be reordered.  However, it does
 * not contain a memory barrier, so if it is used for locking purposes,
 * you should call smp_mb__before_clear_bit() and/or smp_mb__after_clear_bit()
 * in order to ensure changes are visible on other processors.
 */
static inline void clear_bit(int nr, volatile unsigned long * addr)
{
	__asm__ __volatile__( LOCK
		"btrl %1,%0"
		:"=m" (ADDR)
		:"Ir" (nr));
}

/**
 * __ffs - find first bit in word.
 * @word: The word to search
 *
 * Undefined if no bit exists, so code should check against 0 first.
 */
static inline unsigned long __ffs(unsigned long word)
{
	__asm__("bsfl %1,%0"
		:"=r" (word)
		:"rm" (word));
	return word;
}


/*
 * These have to be done with inline assembly: that way the bit-setting
 * is guaranteed to be atomic. All bit operations return 0 if the bit
 * was cleared before the operation and != 0 if it was not.
 *
 * bit 0 is the LSB of addr; bit 32 is the LSB of (addr+1).
 */
#define ADDR (*(volatile long *) addr)

#define rdtscll(val) \
     __asm__ __volatile__("rdtsc" : "=A" (val))



#elif defined(__x86_64__)/* ifdef __i386__ */
/************************** x86_84 *******************************/

#define xchg(ptr,v) ((__typeof__(*(ptr)))__xchg((unsigned long)(v),(ptr),sizeof(*(ptr))))
#define __xg(x) ((volatile long *)(x))
static inline unsigned long __xchg(unsigned long x, volatile void * ptr, int size)
{
	switch (size) {
		case 1:
			__asm__ __volatile__("xchgb %b0,%1"
				:"=q" (x)
				:"m" (*__xg(ptr)), "0" (x)
				:"memory");
			break;
		case 2:
			__asm__ __volatile__("xchgw %w0,%1"
				:"=r" (x)
				:"m" (*__xg(ptr)), "0" (x)
				:"memory");
			break;
		case 4:
			__asm__ __volatile__("xchgl %k0,%1"
				:"=r" (x)
				:"m" (*__xg(ptr)), "0" (x)
				:"memory");
			break;
		case 8:
			__asm__ __volatile__("xchgq %0,%1"
				:"=r" (x)
				:"m" (*__xg(ptr)), "0" (x)
				:"memory");
			break;
	}
	return x;
}

/**
 * test_and_clear_bit - Clear a bit and return its old value
 * @nr: Bit to clear
 * @addr: Address to count from
 *
 * This operation is atomic and cannot be reordered.  
 * It also implies a memory barrier.
 */
static __inline__ int test_and_clear_bit(int nr, volatile void * addr)
{
	int oldbit;

	__asm__ __volatile__( LOCK_PREFIX
		"btrl %2,%1\n\tsbbl %0,%0"
		:"=r" (oldbit),"=m" (ADDR)
		:"dIr" (nr) : "memory");
	return oldbit;
}

static __inline__ int constant_test_bit(int nr, const volatile void * addr)
{
	return ((1UL << (nr & 31)) & (((const volatile unsigned int *) addr)[nr >> 5])) != 0;
}

static __inline__ int variable_test_bit(int nr, volatile const void * addr)
{
	int oldbit;

	__asm__ __volatile__(
		"btl %2,%1\n\tsbbl %0,%0"
		:"=r" (oldbit)
		:"m" (ADDR),"dIr" (nr));
	return oldbit;
}

#define test_bit(nr,addr) \
(__builtin_constant_p(nr) ? \
 constant_test_bit((nr),(addr)) : \
 variable_test_bit((nr),(addr)))


/**
 * set_bit - Atomically set a bit in memory
 * @nr: the bit to set
 * @addr: the address to start counting from
 *
 * This function is atomic and may not be reordered.  See __set_bit()
 * if you do not require the atomic guarantees.
 * Note that @nr may be almost arbitrarily large; this function is not
 * restricted to acting on a single-word quantity.
 */
static __inline__ void set_bit(int nr, volatile void * addr)
{
	__asm__ __volatile__( LOCK_PREFIX
		"btsl %1,%0"
		:"=m" (ADDR)
		:"dIr" (nr) : "memory");
}

/**
 * clear_bit - Clears a bit in memory
 * @nr: Bit to clear
 * @addr: Address to start counting from
 *
 * clear_bit() is atomic and may not be reordered.  However, it does
 * not contain a memory barrier, so if it is used for locking purposes,
 * you should call smp_mb__before_clear_bit() and/or smp_mb__after_clear_bit()
 * in order to ensure changes are visible on other processors.
 */
static __inline__ void clear_bit(int nr, volatile void * addr)
{
	__asm__ __volatile__( LOCK_PREFIX
		"btrl %1,%0"
		:"=m" (ADDR)
		:"dIr" (nr));
}

/**
 * __ffs - find first bit in word.
 * @word: The word to search
 *
 * Undefined if no bit exists, so code should check against 0 first.
 */
static __inline__ unsigned long __ffs(unsigned long word)
{
	__asm__("bsfq %1,%0"
		:"=r" (word)
		:"rm" (word));
	return word;
}

#define ADDR (*(volatile long *) addr)

#define rdtscll(val) do { \
     unsigned int __a,__d; \
     asm volatile("rdtsc" : "=a" (__a), "=d" (__d)); \
     (val) = ((unsigned long)__a) | (((unsigned long)__d)<<32); \
} while(0)

#else /* ifdef __x86_64__ */
#error "Unsupported architecture"
#endif

/********************* common i386 and x86_64  ****************************/
#define xen_mb()  mb()
#define xen_rmb() rmb()
#define xen_wmb() wmb()
#define xen_barrier() asm volatile ( "" : : : "memory")

#endif /* ifdef __INSIDE_MINIOS */

#define wrmsr(msr,val1,val2) \
      __asm__ __volatile__("wrmsr" \
                           : /* no outputs */ \
                           : "c" (msr), "a" (val1), "d" (val2))

static inline void wrmsrl(unsigned msr, uint64_t val)
{
    wrmsr(msr, (uint32_t)(val & 0xffffffffULL), (uint32_t)(val >> 32));
}

struct __synch_xchg_dummy { unsigned long a[100]; };
#define __synch_xg(x) ((struct __synch_xchg_dummy *)(x))

#define synch_cmpxchg(ptr, old, new) \
((__typeof__(*(ptr)))__synch_cmpxchg((ptr),\
                                     (unsigned long)(old), \
                                     (unsigned long)(new), \
                                     sizeof(*(ptr))))

static inline unsigned long __synch_cmpxchg(volatile void *ptr,
        unsigned long old,
        unsigned long new, int size)
{
    unsigned long prev;
    switch (size) {
        case 1:
            __asm__ __volatile__("lock; cmpxchgb %b1,%2"
                    : "=a"(prev)
                    : "q"(new), "m"(*__synch_xg(ptr)),
                    "0"(old)
                    : "memory");
            return prev;
        case 2:
            __asm__ __volatile__("lock; cmpxchgw %w1,%2"
                    : "=a"(prev)
                    : "r"(new), "m"(*__synch_xg(ptr)),
                    "0"(old)
                    : "memory");
            return prev;
#ifdef __x86_64__
        case 4:
            __asm__ __volatile__("lock; cmpxchgl %k1,%2"
                    : "=a"(prev)
                    : "r"(new), "m"(*__synch_xg(ptr)),
                    "0"(old)
                    : "memory");
            return prev;
        case 8:
            __asm__ __volatile__("lock; cmpxchgq %1,%2"
                    : "=a"(prev)
                    : "r"(new), "m"(*__synch_xg(ptr)),
                    "0"(old)
                    : "memory");
            return prev;
#else
        case 4:
            __asm__ __volatile__("lock; cmpxchgl %1,%2"
                    : "=a"(prev)
                    : "r"(new), "m"(*__synch_xg(ptr)),
                    "0"(old)
                    : "memory");
            return prev;
#endif
    }
    return old;
}


static __inline__ void synch_set_bit(int nr, volatile void * addr)
{
    __asm__ __volatile__ ( 
        "lock btsl %1,%0"
        : "=m" (ADDR) : "Ir" (nr) : "memory" );
}

static __inline__ void synch_clear_bit(int nr, volatile void * addr)
{
    __asm__ __volatile__ (
        "lock btrl %1,%0"
        : "=m" (ADDR) : "Ir" (nr) : "memory" );
}

static __inline__ int synch_test_and_set_bit(int nr, volatile void * addr)
{
    int oldbit;
    __asm__ __volatile__ (
        "lock btsl %2,%1\n\tsbbl %0,%0"
        : "=r" (oldbit), "=m" (ADDR) : "Ir" (nr) : "memory");
    return oldbit;
}

static __inline__ int synch_test_and_clear_bit(int nr, volatile void * addr)
{
    int oldbit;
    __asm__ __volatile__ (
        "lock btrl %2,%1\n\tsbbl %0,%0"
        : "=r" (oldbit), "=m" (ADDR) : "Ir" (nr) : "memory");
    return oldbit;
}

static __inline__ int synch_const_test_bit(int nr, const volatile void * addr)
{
    return ((1UL << (nr & 31)) & 
            (((const volatile unsigned int *) addr)[nr >> 5])) != 0;
}

static __inline__ int synch_var_test_bit(int nr, volatile void * addr)
{
    int oldbit;
    __asm__ __volatile__ (
        "btl %2,%1\n\tsbbl %0,%0"
        : "=r" (oldbit) : "m" (ADDR), "Ir" (nr) );
    return oldbit;
}

#define synch_test_bit(nr,addr) \
(__builtin_constant_p(nr) ? \
 synch_const_test_bit((nr),(addr)) : \
 synch_var_test_bit((nr),(addr)))

static inline int
HYPERVISOR_xsm_op(
        struct xen_flask_op *op)
{
    return _hypercall1(int, xsm_op, op);
}

static inline void cpuid(uint32_t leaf,
                         uint32_t *eax, uint32_t *ebx,
                         uint32_t *ecx, uint32_t *edx)
{
    asm volatile ("cpuid"
                  : "=a" (*eax), "=b" (*ebx), "=c" (*ecx), "=d" (*edx)
                  : "0" (leaf));
}

#undef ADDR

#ifdef CONFIG_PARAVIRT
static inline unsigned long read_cr2(void)
{
    return HYPERVISOR_shared_info->vcpu_info[smp_processor_id()].arch.cr2;
}
#else
static inline unsigned long read_cr2(void)
{
    unsigned long cr2;

    asm volatile ( "mov %%cr2,%0\n\t" : "=r" (cr2) );
    return cr2;
}
#endif

#endif /* not assembly */
#endif /* _OS_H_ */
