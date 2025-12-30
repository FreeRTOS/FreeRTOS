/* arch_spinlock 
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



#ifndef __ARCH_ASM_SPINLOCK_H
#define __ARCH_ASM_SPINLOCK_H

#include <lib.h>
#include "os.h"


#define ARCH_SPIN_LOCK_UNLOCKED { 1 }

/*
 * Simple spin lock operations.  There are two variants, one clears IRQ's
 * on the local processor, one does not.
 *
 * We make no fairness assumptions. They have a cost.
 */

#define arch_spin_is_locked(x)	(*(volatile signed char *)(&(x)->slock) <= 0)
#define arch_spin_unlock_wait(x) do { barrier(); } while(spin_is_locked(x))

#define spin_lock_string \
        "1:\n" \
	LOCK \
	"decb %0\n\t" \
	"jns 3f\n" \
	"2:\t" \
	"rep;nop\n\t" \
	"cmpb $0,%0\n\t" \
	"jle 2b\n\t" \
	"jmp 1b\n" \
	"3:\n\t"

#define spin_lock_string_flags \
        "1:\n" \
	LOCK \
	"decb %0\n\t" \
	"jns 4f\n\t" \
	"2:\t" \
	"testl $0x200, %1\n\t" \
	"jz 3f\n\t" \
	"#sti\n\t" \
	"3:\t" \
	"rep;nop\n\t" \
	"cmpb $0, %0\n\t" \
	"jle 3b\n\t" \
	"#cli\n\t" \
	"jmp 1b\n" \
	"4:\n\t"

/*
 * This works. Despite all the confusion.
 * (except on PPro SMP or if we are using OOSTORE)
 * (PPro errata 66, 92)
 */

#define spin_unlock_string \
	"xchgb %b0, %1" \
		:"=q" (oldval), "=m" (lock->slock) \
		:"0" (oldval) : "memory"

static inline void _raw_spin_unlock(spinlock_t *lock)
{
	char oldval = ARCH_SPIN_LOCK_UNLOCKED;
	__asm__ __volatile__(
		spin_unlock_string
	);
}

static inline int _raw_spin_trylock(spinlock_t *lock)
{
	char oldval;
	__asm__ __volatile__(
		"xchgb %b0,%1\n"
		:"=q" (oldval), "=m" (lock->slock)
		:"0" (0) : "memory");
	return oldval > 0;
}

static inline void _raw_spin_lock(spinlock_t *lock)
{
	__asm__ __volatile__(
		spin_lock_string
		:"=m" (lock->slock) : : "memory");
}

static inline void _raw_spin_lock_flags (spinlock_t *lock, unsigned long flags)
{
	__asm__ __volatile__(
		spin_lock_string_flags
		:"=m" (lock->slock) : "r" (flags) : "memory");
}

#endif
