/* run-gnt-test
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
#include "FreeRTOS_CLI.h"
#include "stdint.h"
#include "string.h"
#include "stdio.h"
#include "cli.h"
#include "task.h"
#include "register_tests.h"
#include <memory.h>
#include <xen/xen.h>
#include <xen/event_channel.h>
#include <hypervisor.h>
#include <events.h>
#include <xenbus.h>
#include <gnttab.h>
#include <gntmap.h>
#include <e820.h>
#include <stdlib.h>

static inline domid_t str_to_domid_t(const char *str)
{
        char *endptr = NULL;
        domid_t val = (domid_t)strtoul(str, &endptr, 10);
        return val;
}

unsigned long VIRTtoMFN(uint8_t *shared_page) {
	return ((unsigned long)shared_page >> 12);
}

static BaseType_t  prvRunGnttest( char * pcWriteBuffer,
                                  size_t xWriteBufferLen,
                                  const char * pcCommandString )
{
    memset(pcWriteBuffer, 0x00, xWriteBufferLen );
#if defined(__x86_64__)
   domid_t myId = xenbus_get_self_id();
#else
   char *dom;
   xenbus_read(XBT_NIL, "domid", &dom);
   domid_t myId = str_to_domid_t(dom);
#endif
    uint8_t *shared_page = (uint8_t *)pvAlignedMalloc(sizeof(uint8_t) * PAGE_SIZE, 4096);
    memset(shared_page, 0, PAGE_SIZE);

    grant_ref_t gref = gnttab_grant_access(myId, VIRTtoMFN(shared_page), 1);
    if (gref < 0) {
	    printk("ERROR: Page access unsuccessful.\n");
	    return 0;
    }

    printk("Page shared successfully with gref: %u.\n", gref);
    
    return 0;
}

extern struct gntmap map;
extern uint8_t grant_table;

static BaseType_t  prvRunGntMaptest( char * pcWriteBuffer,
                                  size_t xWriteBufferLen,
                                  const char * pcCommandString )
{
    memset(pcWriteBuffer, 0x00, xWriteBufferLen );
    const char *pcParameter;
    BaseType_t xParameterStringLength;
    grant_ref_t grant_ref[1];
#if defined(__x86_64__)
   domid_t myId = xenbus_get_self_id();
#else
   char *dom;
   xenbus_read(XBT_NIL, "domid", &dom);
   domid_t myId = str_to_domid_t(dom);
#endif
    domid_t domid[1];
    void *addr = NULL;

    pcParameter = FreeRTOS_CLIGetParameter(pcCommandString, 1, &xParameterStringLength);
    grant_ref[0] = (grant_ref_t) strtoul(pcParameter, NULL, 0);
    domid[0] = myId;

    addr = (void *)gntmap_map_grant_refs(&map, 1, domid, 1, grant_ref, 0);
    if (addr == NULL)
	    printk("FREERTOS: Mapping Failed.\n");
    else
	    printk("FREERTOS: Mapped to 0x%p\n", addr);

    return 0;
}

static const CLI_Command_Definition_t run_gnt_test =
{
    "run-gnt-test",
    "\r\nrun-gnt-test:\r\n Run grant test\r\n\r\n",
    prvRunGnttest, /* The function to run. */
    0
};

static const CLI_Command_Definition_t run_gntmap_test =
{
    "run-gntmap-test",
    "\r\nrun-gntmap-test <grant reference>:\r\n Maps a granted page. Please provide the grant reference number generated after running run-gnt-test\r\n\r\n",
    prvRunGntMaptest, /* The function to run. */
    1
};

void register_gnt_test(void) {
    FreeRTOS_CLIRegisterCommand( &run_gnt_test );
}

void register_gntmap_test(void) {
    FreeRTOS_CLIRegisterCommand( &run_gntmap_test );
}
