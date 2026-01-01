/* -*-  Mode:C; c-basic-offset:4; tab-width:4 -*-
 ****************************************************************************
 * (C) 2003 - Rolf Neugebauer - Intel Research Cambridge
 * (C) 2002-2003 - Keir Fraser - University of Cambridge
 * (C) 2005 - Grzegorz Milos - Intel Research Cambridge
 * (C) 2006 - Robert Kaiser - FH Wiesbaden
 ****************************************************************************
 *
 *        File: time.c
 *      Author: Rolf Neugebauer and Keir Fraser
 *     Changes: Grzegorz Milos
 *
 * Description: Simple time and timer functions
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

#include <hypervisor.h>
#include <time.h>
#include <events.h>
#include <lib.h>

/************************************************************************
 * Time functions
 *************************************************************************/

/* These are peridically updated in shared_info, and then copied here. */
static struct timespec shadow_ts;
static uint32_t shadow_ts_version;

static struct vcpu_time_info shadow;

static inline int wc_values_up_to_date(void)
{
    shared_info_t *s = HYPERVISOR_shared_info;

    return shadow_ts_version == s->wc_version;
}

/*
 * Scale a 64-bit delta by scaling and multiplying by a 32-bit fraction,
 * yielding a 64-bit result.
 */
static inline uint64_t scale_delta(uint64_t delta, uint32_t mul_frac, int shift)
{
    uint64_t product;
#ifdef __i386__
    uint32_t tmp1, tmp2;
#endif

    if ( shift < 0 )
        delta >>= -shift;
    else
        delta <<= shift;

#ifdef __i386__
    __asm__ (
        "mul  %5       ; "
        "mov  %4,%%eax ; "
        "mov  %%edx,%4 ; "
        "mul  %5       ; "
        "add  %4,%%eax ; "
        "xor  %5,%5    ; "
        "adc  %5,%%edx ; "
        : "=A" (product), "=r" (tmp1), "=r" (tmp2)
        : "a" ((uint32_t)delta), "1" ((uint32_t)(delta >> 32)), "2" (mul_frac) );
#else
    __asm__ (
        "mul %%rdx ; shrd $32,%%rdx,%%rax"
        : "=a" (product) : "0" (delta), "d" ((uint64_t)mul_frac) );
#endif

    return product;
}

static unsigned long get_nsec_offset(void)
{
    uint64_t now, delta;

    rdtscll(now);
    delta = now - shadow.tsc_timestamp;

    return scale_delta(delta, shadow.tsc_to_system_mul, shadow.tsc_shift);
}

/*
 * monotonic_clock(): returns # of nanoseconds passed since time_init()
 *        Note: This function is required to return accurate
 *        time even in the absence of multiple timer ticks.
 */
uint64_t monotonic_clock(void)
{
    struct vcpu_time_info *src = &HYPERVISOR_shared_info->vcpu_info[0].time;

    if ( shadow.version != src->version )
    {
        do {
            shadow.version = src->version;
            rmb();
            shadow.tsc_timestamp     = src->tsc_timestamp;
            shadow.system_time       = src->system_time;
            shadow.tsc_to_system_mul = src->tsc_to_system_mul;
            shadow.tsc_shift         = src->tsc_shift;
            rmb();
        } while ( (src->version & 1) || (shadow.version != src->version) );
    }

    return shadow.system_time + get_nsec_offset();
}

static void update_wallclock(void)
{
    shared_info_t *s = HYPERVISOR_shared_info;

    do {
        shadow_ts_version = s->wc_version;
        rmb();
        shadow_ts.tv_sec  = s->wc_sec;
        shadow_ts.tv_nsec = s->wc_nsec;
        rmb();
    } while ( (s->wc_version & 1) | (shadow_ts_version ^ s->wc_version) );
}

int gettimeofday(struct timeval *tv, void *tz)
{
    uint64_t nsec = monotonic_clock();

    if ( !wc_values_up_to_date() )
        update_wallclock();

    nsec += shadow_ts.tv_nsec;

    tv->tv_sec = shadow_ts.tv_sec;
    tv->tv_sec += NSEC_TO_SEC(nsec);
    tv->tv_usec = NSEC_TO_USEC(nsec % 1000000000UL);

    return 0;
}

void block_domain(s_time_t until)
{
    ASSERT(irqs_disabled());
    if ( monotonic_clock() < until )
    {
        HYPERVISOR_set_timer_op(until);
#ifdef CONFIG_PARAVIRT
        HYPERVISOR_sched_op(SCHEDOP_block, 0);
#else
        local_irq_enable();
        asm volatile ( "hlt" : : : "memory" );
#endif
        local_irq_disable();
        HYPERVISOR_set_timer_op(0);
    }
}

// ankush: Latency calculation test pending.
s_time_t last_timer_start;

static void timer_handler(evtchn_port_t ev, void *regs, void *ign)
{
    s_time_t current_timer = last_timer_start + MILLISECS(1);
    HYPERVISOR_set_timer_op(current_timer);
    last_timer_start = current_timer;
    __asm volatile ( "int $0x32" );
}

static evtchn_port_t port;
void init_time(void)
{
    port = bind_virq(VIRQ_TIMER, &timer_handler, NULL);
    unmask_evtchn(port);
    last_timer_start = monotonic_clock() + MILLISECS(1);
    HYPERVISOR_set_timer_op(last_timer_start);
}

void fini_time(void)
{
    /* Clear any pending timer */
    HYPERVISOR_set_timer_op(0);
    unbind_evtchn(port);
}
