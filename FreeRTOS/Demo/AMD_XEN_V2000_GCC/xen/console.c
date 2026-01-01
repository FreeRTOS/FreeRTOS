/*
 ****************************************************************************
 * (C) 2006 - Grzegorz Milos - Cambridge University
 ****************************************************************************
 *
 *        File: console.c
 *      Author: Grzegorz Milos
 *     Changes:
 *
 *        Date: Mar 2006
 *
 * Environment: Xen Minimal OS
 * Description: Console interface.
 *
 * Handles console I/O. Defines printk.
 *
 ****************************************************************************
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
#include <events.h>
#include <lib.h>
#include <xen/io/console.h>
#include <xen/io/protocols.h>
#include <xen/io/ring.h>
#include <xen/hvm/params.h>

static struct consfront_dev* xen_console = NULL;
static int console_initialised = 0;

void *malloc(size_t);
void free(void *);

void vSendConsoleInputToCli(char);

__attribute__((weak)) void console_input(char *buf, unsigned int len)
{
    if ( len > 0 )
    {
        for (int i=0;i<len;i++)
            vSendConsoleInputToCli(buf[i]);
    }
}

#ifndef HAVE_LIBC
void xencons_rx(char *buf, unsigned int len, void *regs)
{
    console_input(buf, len);
}

void xencons_tx(void)
{
    /* Do nothing, handled by _rx */
}
#endif

void console_print(struct consfront_dev *dev, const char *data, int length)
{
    char *curr_char, saved_char;
    char copied_str[length+1];
    char *copied_ptr;
    int part_len;
    int (*ring_send_fn)(struct consfront_dev *dev, const char *data,
                        unsigned int length);

    if ( !console_initialised )
        ring_send_fn = xencons_ring_send_no_notify;
    else
        ring_send_fn = xencons_ring_send;

    if ( dev && dev->is_raw )
    {
        ring_send_fn(dev, data, length);
        return;
    }

    copied_ptr = copied_str;
    memcpy(copied_ptr, data, length);
    for ( curr_char = copied_ptr; curr_char < copied_ptr + length - 1;
          curr_char++ )
    {
        if ( *curr_char == '\n' )
        {
            *curr_char = '\r';
            saved_char = *(curr_char + 1);
            *(curr_char + 1) = '\n';
            part_len = curr_char - copied_ptr + 2;
            ring_send_fn(dev, copied_ptr, part_len);
            *(curr_char + 1) = saved_char;
            copied_ptr = curr_char + 1;
            length -= part_len - 1;
        }
    }

    if ( copied_ptr[length - 1] == '\n')
    {
        copied_ptr[length - 1] = '\r';
        copied_ptr[length] = '\n';
        length++;
    }

    ring_send_fn(dev, copied_ptr, length);
}

void print(int direct, const char *fmt, va_list args)
{
    static char __print_buf[1024];

    (void)vsnprintf(__print_buf, sizeof(__print_buf), fmt, args);

    if ( direct )
    {
        (void)HYPERVISOR_console_io(CONSOLEIO_write, strlen(__print_buf),
                                    __print_buf);
        return;
    }
#ifndef CONFIG_USE_XEN_CONSOLE
    if ( !console_initialised )
#endif
        (void)HYPERVISOR_console_io(CONSOLEIO_write, strlen(__print_buf),
                                    __print_buf);

    console_print(NULL, __print_buf, strlen(__print_buf));
}

void printk(const char *fmt, ...)
{
    va_list args;

    va_start(args, fmt);
    print(0, fmt, args);
    va_end(args);
}

void xprintk(const char *fmt, ...)
{
    va_list args;

    va_start(args, fmt);
    print(1, fmt, args);
    va_end(args);
}

void init_console(void)
{
    printk("Initialising console ... ");
    xen_console = xencons_ring_init();
    console_initialised = 1;
    /* This is also required to notify the daemon */
    printk("done.\n");
}

void suspend_console(void)
{
    console_initialised = 0;
    xencons_ring_fini(xen_console);
}

void resume_console(void)
{
    xencons_ring_resume(xen_console);
    console_initialised = 1;
}


static struct xencons_interface *console_ring;
uint32_t console_evtchn;

static struct consfront_dev* resume_xen_console(struct consfront_dev *dev);

#ifdef CONFIG_PARAVIRT
void get_console(void *p)
{
    start_info_t *si = p;

    console_ring = mfn_to_virt(si->console.domU.mfn);
    console_evtchn = si->console.domU.evtchn;
}
#else
void get_console(void *p)
{
    uint64_t v = -1;

    if ( hvm_get_parameter(HVM_PARAM_CONSOLE_EVTCHN, &v) )
        BUG();
    console_evtchn = v;

    if ( hvm_get_parameter(HVM_PARAM_CONSOLE_PFN, &v) )
        BUG();
    console_ring = (struct xencons_interface *)(v<<12);
}
#endif

static inline void notify_daemon(struct consfront_dev *dev)
{
    /* Use evtchn: this is called early, before irq is set up. */
    if ( !dev )
        notify_remote_via_evtchn(console_evtchn);
    else
        notify_remote_via_evtchn(dev->evtchn);
}

static inline struct xencons_interface *xencons_interface(void)
{
    return console_evtchn ? console_ring : NULL;
}

int xencons_ring_send_no_notify(struct consfront_dev *dev, const char *data,
                                unsigned int len)
{
    int sent = 0;
    struct xencons_interface *intf;
    XENCONS_RING_IDX cons, prod;

    if ( !dev )
        intf = xencons_interface();
    else
        intf = dev->ring;
    if ( !intf )
        return sent;

    cons = intf->out_cons;
    prod = intf->out_prod;
    mb();
    BUG_ON((prod - cons) > sizeof(intf->out));

    while ( (sent < len) && ((prod - cons) < sizeof(intf->out)) )
        intf->out[MASK_XENCONS_IDX(prod++, intf->out)] = data[sent++];

    wmb();
    intf->out_prod = prod;

    return sent;
}

int xencons_ring_send(struct consfront_dev *dev, const char *data,
                      unsigned int len)
{
    int sent;

    sent = xencons_ring_send_no_notify(dev, data, len);
    notify_daemon(dev);

    return sent;
}

void console_handle_input(evtchn_port_t port, void *regs, void *data)
{
    struct consfront_dev *dev = (struct consfront_dev *) data;
    struct xencons_interface *intf = xencons_interface();
    XENCONS_RING_IDX cons, prod;

    cons = intf->in_cons;
    prod = intf->in_prod;
    mb();
    BUG_ON((prod - cons) > sizeof(intf->in));

    while ( cons != prod )
    {
        xencons_rx(intf->in + MASK_XENCONS_IDX(cons, intf->in), 1, regs);
        cons++;
    }

    mb();
    intf->in_cons = cons;

    notify_daemon(dev);

    xencons_tx();
}

struct consfront_dev *xencons_ring_init(void)
{
    struct consfront_dev *dev;

    if ( !console_evtchn )
        return 0;

    dev = malloc(sizeof(struct consfront_dev));
    memset(dev, 0, sizeof(struct consfront_dev));
    dev->nodename = "device/console";
    dev->dom = 0;
    dev->backend = 0;
    dev->ring_ref = 0;

#ifdef HAVE_LIBC
    dev->fd = -1;
#endif

    return resume_xen_console(dev);
}

static struct consfront_dev *resume_xen_console(struct consfront_dev *dev)
{
    int err;

    dev->evtchn = console_evtchn;
    dev->ring = xencons_interface();

    err = bind_evtchn(dev->evtchn, console_handle_input, dev);
    if ( err <= 0 )
    {
        printk("XEN console request chn bind failed %i\n", err);
        free(dev);
        return NULL;
    }
    unmask_evtchn(dev->evtchn);

    /* In case we have in-flight data after save/restore... */
    notify_daemon(dev);

    return dev;
}

void xencons_ring_fini(struct consfront_dev *dev)
{
    if ( dev )
        mask_evtchn(dev->evtchn);
}

void xencons_ring_resume(struct consfront_dev *dev)
{
    if ( dev )
    {
#if CONFIG_PARAVIRT
        get_console(&start_info);
#else
        get_console(0);
#endif
        resume_xen_console(dev);
    }
}
