/* xenbus-watch
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


#include <os.h>
#include <events.h>
#include <lib.h>
#include <xenbus.h>
#include <xmalloc.h>
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "semphr.h"

static xenbus_event_queue events = NULL;

void process_sci(void);

void xsWatchTask(void)
{
    char *domid_str;
    char path[128];
    char *shutdown_reason = NULL;
    char *err;
    int sleep_stat = 0;

    if ((err = xenbus_read(XBT_NIL, "domid", &domid_str))) {
        printk("Error reading domid: %s\n", err);
        free(err);
        return;
    }

    snprintf(path, sizeof(path), "/local/domain/%s/control/shutdown", domid_str);
    //printk("Watching for shutdown/reboot at path: %s\n", path);
    free(domid_str);

    err = xenbus_watch_path_token(XBT_NIL, path, "shutdown-watch", &events);
    if (err != NULL) {
        printk("Failed to watch path: %s\n", err);
        free(err);
        return;
    }

    while (1) {
        xenbus_wait_for_watch(&events);

        if ((err = xenbus_read(XBT_NIL, path, &shutdown_reason))) {
            printk("Failed to read shutdown reason: %s\n", err);
            free(err);
            continue;
        }

	if (strcmp(shutdown_reason, "") == 0) {
            continue;
        }

        //printk("Received shutdown command: %s\n", shutdown_reason);

        if (strcmp(shutdown_reason, "poweroff") == 0) {
            printk("Powering off...\n");
	    HYPERVISOR_shutdown(SHUTDOWN_poweroff);
        } else if (strcmp(shutdown_reason, "reboot") == 0) {
            printk("Rebooting...\n");
	    HYPERVISOR_shutdown(SHUTDOWN_reboot);
        } else if (strcmp(shutdown_reason, "sleep") == 0) {
                if (sleep_stat == 1) {
                        printk("Already sleeping\n");
                        continue;
                }
                sleep_stat = 1;
                process_sci();
        } else if (strcmp(shutdown_reason, "wake") == 0) {
                if (sleep_stat == 0) {
                        printk("Already awake\n");
                        continue;
                }
                sleep_stat = 0;
                process_sci();
        } else {
            printk("Unknown shutdown reason: %s\n", shutdown_reason);
        }

        free(shutdown_reason);
    }
}
