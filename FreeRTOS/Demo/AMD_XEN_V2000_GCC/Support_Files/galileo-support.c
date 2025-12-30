/*--------------------------------------------------------------------
 Copyright(c) 2015 Intel Corporation. All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions
 are met:

 * Redistributions of source code must retain the above copyright
 notice, this list of conditions and the following disclaimer.
 * Redistributions in binary form must reproduce the above copyright
 notice, this list of conditions and the following disclaimer in
 the documentation and/or other materials provided with the
 distribution.
 * Neither the name of Intel Corporation nor the names of its
 contributors may be used to endorse or promote products derived
 from this software without specific prior written permission.

 THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 --------------------------------------------------------------------*/

/*-----------------------------------------------------------------------
 * Any required includes
 *------------------------------------------------------------------------
 */
#include "multiboot.h"
#include "galileo_support.h"
#include "serial.h"
#include "stdlib.h"
#include "string.h"
#include "desc.h"

/*-----------------------------------------------------------------------
 * Any required local definitions
 *------------------------------------------------------------------------
 */


#if defined(__i386__)
uint32_t bootinfo = 1UL;
uint32_t bootsign = 1UL;


#define INTR_STACK_SIZE PAGE_SIZE
static uint8_t intr_stack[INTR_STACK_SIZE] __attribute__((aligned(16)));

hw_tss tss __attribute__((aligned(16))) =
{
#if defined(__i386__)
    .esp0 = (unsigned long)&intr_stack[INTR_STACK_SIZE],
    .ss0  = __KERN_DS,
#elif defined(__x86_64__)
    .rsp0 = (unsigned long)&intr_stack[INTR_STACK_SIZE],
#endif
    .iopb = X86_TSS_INVALID_IO_BITMAP,
};


/*------------------------------------------------------------------------
 * GDT default entries (used in GDT setup code)
 *------------------------------------------------------------------------
 */
static struct sd gdt_default[NGDE] =
{
        /*   sd_lolimit  sd_lobase   sd_midbase  sd_access   sd_hilim_fl sd_hibase */
        /* 0th entry NULL */
        {            0,          0,           0,         0,            0,        0, },
        /* 1st, Kernel Code Segment */
        {       0xffff,          0,           0,      0x9a,         0xcf,        0, },
        /* 2nd, Kernel Data Segment */
        {       0xffff,          0,           0,      0x92,         0xcf,        0, },
        /* 3rd, Kernel Stack Segment */
        {       0xffff,          0,           0,      0x92,         0xcf,        0, },
        /* 4st, Boot Code Segment */
        {       0xffff,          0,           0,      0x9a,         0xcf,        0, },
        /* 5th, Code Segment for BIOS32 request */
        {       0xffff,          0,           0,      0x9a,         0xcf,        0, },
        /* 6th, Data Segment for BIOS32 request */
        {       0xffff,          0,           0,      0x92,         0xcf,        0, },
};

extern struct sd gdt[]; /* Global segment table (defined in startup.S) */

/*------------------------------------------------------------------------
 * Set segment registers (used in GDT setup code)
 *------------------------------------------------------------------------
 */
void setsegs()
{
        extern int      __text_end;
        struct sd       *psd;
        uint32_t        np, ds_end;

        ds_end = 0xffffffff/PAGE_SIZE;          /* End page number */

        psd = &gdt_default[1];                          /* Kernel code segment */
        np = ((int)&__text_end - 0 + PAGE_SIZE-1) / PAGE_SIZE;  /* Number of code pages */
        psd->sd_lolimit = np;
        psd->sd_hilim_fl = FLAGS_SETTINGS | ((np >> 16) & 0xff);

        psd = &gdt_default[2];                          /* Kernel data segment */
        psd->sd_lolimit = ds_end;
        psd->sd_hilim_fl = FLAGS_SETTINGS | ((ds_end >> 16) & 0xff);

        psd = &gdt_default[3];                          /* Kernel stack segment */
        psd->sd_lolimit = ds_end;
        psd->sd_hilim_fl = FLAGS_SETTINGS | ((ds_end >> 16) & 0xff);

        psd = &gdt_default[4];                          /* Boot code segment */
        psd->sd_lolimit = ds_end;
        psd->sd_hilim_fl = FLAGS_SETTINGS | ((ds_end >> 16) & 0xff);

#if 0
        extern hw_tss tss;
        psd = &gdt_default[7];                          /* Boot code segment */
        uint32_t base=&tss;
        uint32_t limit=0x67;
        uint32_t attr=0x89;
        psd->sd_lolimit = limit&0xffff;
        psd->sd_lobase = base&0xffff;
        psd->sd_midbase = (base&0x00ff0000)>>16;
        psd->sd_access = attr;
        psd->sd_hilim_fl = 0;
        psd->sd_hibase = (base&0xff000000)>>24;
        printf("base: %x\n",base);
        printf("%x %x %x %x %x %x\n",psd->sd_lolimit,psd->sd_lobase,psd->sd_midbase,psd->sd_access,psd->sd_hilim_fl,psd->sd_hibase);
#endif
        memcpy(gdt, gdt_default, sizeof(gdt_default));

}
#endif
