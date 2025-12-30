/* main
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


#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "queue.h"
#include "stdio.h"
#include "xen/memory.h"
#include "e820.h"
#include "freertos_acpica.h"
#include "application.h"
#if defined(__x86_64__)
#include "x86_64.h"
#endif
#include "hypervisor.h"
#include "console.h"
#include "events.h"
#include "xen/hvm/params.h"
#include "xenbus.h"
#include "gnttab.h"
#include "gntmap.h"
#include "argo_module.h"

struct e820entry e820_map[E820_MAX];
unsigned e820_entries;

#define barrier() __asm__ __volatile__("": : :"memory")

#define wrmsr(msr,val1,val2) \
      __asm__ __volatile__("wrmsr" \
                           : /* no outputs */ \
                           : "c" (msr), "a" (val1), "d" (val2))


extern char hypercall_page[4096];
shared_info_t *HYPERVISOR_shared_info;
struct gntmap map;

/* If error is detected the configASSERT is called */
void do_exit(void) {
    configASSERT(0);
}

void xen_callback_vector(void)
{
    uint64_t value;
    uint64_t callback_number = (uint64_t)((2ULL << 56) | 37);
    hvm_get_parameter(HVM_PARAM_CALLBACK_IRQ, &value);
    if (hvm_set_parameter(HVM_PARAM_CALLBACK_IRQ,callback_number))
    {
        printk("Failed to set XEN Call back to %zu\n",callback_number);
        do_exit();
    }
    hvm_get_parameter(HVM_PARAM_CALLBACK_IRQ, &value);
}

#define XEN_CPUID_FIRST_LEAF 0x40000000
#define XEN_CPUID_LEAF(i)    (XEN_CPUID_FIRST_LEAF + (i))
#define XEN_CPUID_SIGNATURE_EBX 0x566e6558 /* "XenV" */
#define XEN_CPUID_SIGNATURE_ECX 0x65584d4d /* "MMXe" */
#define XEN_CPUID_SIGNATURE_EDX 0x4d4d566e /* "nVMM" */

static void hpc_init(void)
{
    uint32_t eax, ebx, ecx, edx, base;

    for ( base = XEN_CPUID_FIRST_LEAF;
          base < XEN_CPUID_FIRST_LEAF + 0x10000; base += 0x100 )
    {
        cpuid(base, &eax, &ebx, &ecx, &edx);

        if ( (ebx == XEN_CPUID_SIGNATURE_EBX) &&
             (ecx == XEN_CPUID_SIGNATURE_ECX) &&
             (edx == XEN_CPUID_SIGNATURE_EDX) &&
             ((eax - base) >= 2) )
            break;
    }

    cpuid(base + 2, &eax, &ebx, &ecx, &edx);
    wrmsrl((unsigned)ebx, (uint64_t)&hypercall_page);
    barrier();
}

extern uint32_t rdtsc_low;
extern uint32_t rdtsc_high;

uint32_t is_pvh=0;
extern void cliTask( void * pvParameters );
void main(uint64_t multiboot_info_addr)
{
    uint64_t rdtsc_begin = (rdtsc_high << 32) | rdtsc_low;
    hpc_init();

    init_events();

#if defined(__x86_64__)
    vx86_64Init(multiboot_info_addr);
#endif

    uint64_t* val = (uint64_t*) multiboot_info_addr;
    uint32_t magic = *((uint64_t *)val);
    if (magic == XEN_HVM_START_MAGIC_VALUE) {
        is_pvh=1;
        struct hvm_start_info *hsi = (struct hvm_start_info *)val;
        extern void *rsdp;
        rsdp = (void *)hsi->rsdp_paddr;
    }

    HYPERVISOR_shared_info = map_shared_info(0);

    get_console(0);
    init_console();
    
    xen_callback_vector();

    init_gnttab();
    gntmap_init(&map);

    get_xenbus(0);
    init_xenbus();

    int ret = argo_init();
    if (ret == -1) {
	    printk("ERROR: Failed to Bind ARGO VIRQ to the ARGO event channel.\n");
    }

    main_acpica();
    
    BaseType_t xReturn = xTaskCreate( cliTask,
                 "cli",
                 configMINIMAL_STACK_SIZE,
                 0,
                 2|portPRIVILEGE_BIT,
                 NULL);
    
    app_main();


    uint64_t rdtsc_now = rdtsc();
    uint64_t boot_time = rdtsc_now - rdtsc_begin;
    printk("Starting Scheduler\n");
    printk("Boot Time: %u cycles\n",boot_time);
    /* Start the tasks and timer running. */
    vTaskStartScheduler();
    printk("main: ERROR: returned from FreeRTOS scheduler\n");
    return;
}
