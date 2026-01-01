/* -*-  Mode:C; c-basic-offset:4; tab-width:4 -*-
 ****************************************************************************
 * (C) 2003 - Rolf Neugebauer - Intel Research Cambridge
 ****************************************************************************
 *
 *        File: lib.h
 *      Author: Rolf Neugebauer (neugebar@dcs.gla.ac.uk)
 *     Changes: 
 *              
 *        Date: Aug 2003
 * 
 * Environment: Xen Minimal OS
 * Description: Random useful library functions, contains some freebsd stuff
 *
 ****************************************************************************
 * $Id: h-insert.h,v 1.4 2002/11/08 16:03:55 rn Exp $
 ****************************************************************************
 *
 * Copyright (c) 1992, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 */

#ifndef _LIB_H_
#define _LIB_H_

#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <xen/xen.h>
#include <xen/event_channel.h>

#if __GNUC__ > 4 || (__GNUC__ == 4 && __GNUC_MINOR__ >= 6)
#define BUILD_BUG_ON(cond) ({ _Static_assert(!(cond), "!(" #cond ")"); })
#define BUILD_BUG_ON_ZERO(cond) \
    sizeof(struct { _Static_assert(!(cond), "!(" #cond ")"); })
#else
#define BUILD_BUG_ON_ZERO(cond) sizeof(struct { int:-!!(cond); })
#define BUILD_BUG_ON(cond) ((void)BUILD_BUG_ON_ZERO(cond))
#endif

#ifdef HAVE_LIBC
#include <sys/queue.h>
#include <sys/stat.h>
#include <stdio.h>
#include <string.h>
#else
/* string and memory manipulation */

/*
 * From:
 *	@(#)libkern.h	8.1 (Berkeley) 6/10/93
 * $FreeBSD$
 */
int	 memcmp(const void *b1, const void *b2, size_t len);

char	*strcat(char * __restrict, const char * __restrict);
int	 strcmp(const char *, const char *);
char	*strcpy(char * __restrict, const char * __restrict);

char	*strdup(const char *__restrict);

size_t	 strlen(const char *);

int	 strncmp(const char *, const char *, size_t);
char	*strncpy(char * __restrict, const char * __restrict, size_t);

char	*strstr(const char *, const char *);

void *memset(void *, int, size_t);

char *strchr(const char *p, int ch);
char *strrchr(const char *p, int ch);

/* From:
 *	@(#)systm.h	8.7 (Berkeley) 3/29/95
 * $FreeBSD$
 */
void	*memcpy(void *to, const void *from, size_t len);

size_t strnlen(const char *, size_t);

unsigned long strtoul(const char *nptr, char **endptr, int base);
int64_t strtoq(const char *nptr, char **endptr, int base);
uint64_t strtouq(const char *nptr, char **endptr, int base);

extern int sprintf(char * buf, const char * fmt, ...)
        __attribute__ ((format (printf, 2, 3)));
extern int vsprintf(char *buf, const char *, va_list)
        __attribute__ ((format (printf, 2, 0)));
extern int snprintf(char * buf, size_t size, const char * fmt, ...)
        __attribute__ ((format (printf, 3, 4)));
extern int vsnprintf(char *buf, size_t size, const char *fmt, va_list args)
        __attribute__ ((format (printf, 3, 0)));
extern int scnprintf(char * buf, size_t size, const char * fmt, ...)
        __attribute__ ((format (printf, 3, 4)));
extern int vscnprintf(char *buf, size_t size, const char *fmt, va_list args)
        __attribute__ ((format (printf, 3, 0)));
extern int sscanf(const char *, const char *, ...)
        __attribute__ ((format (scanf, 2, 3)));
extern int vsscanf(const char *, const char *, va_list)
        __attribute__ ((format (scanf, 2, 0)));

#endif

#include <console.h>

#define RAND_MIX 2654435769U

int rand(void);


#define ARRAY_SIZE(x) (sizeof(x) / sizeof((x)[0]))

#define ASSERT(x)                                              \
do {                                                           \
	if (!(x)) {                                                \
		printk("ASSERTION FAILED: %s at %s:%d.\n",             \
			   # x ,                                           \
			   __FILE__,                                       \
			   __LINE__);                                      \
        BUG();                                                 \
	}                                                          \
} while(0)

#define BUG_ON(x) ASSERT(!(x))

#ifdef CONFIG_TEST
/* Consistency check as much as possible. */
void sanity_check(void);
#endif

/* Get own domid. */
domid_t get_domid(void);

#ifdef HAVE_LIBC
extern struct wait_queue_head event_queue;

#define FTYPE_NONE       0
#define FTYPE_CONSOLE    1
#define FTYPE_FILE       2
#define FTYPE_SOCKET     3
#define FTYPE_MEM        4
#define FTYPE_N          5
#define FTYPE_SPARE     16

struct file {
    unsigned int type;
    bool read;	/* maybe available for read */
    off_t offset;
    union {
        int fd; /* Any fd from an upper layer. */
        void *dev;
        void *filedata;
    };
};

struct file_ops {
    const char *name;
    int (*read)(struct file *file, void *buf, size_t nbytes);
    int (*write)(struct file *file, const void *buf, size_t nbytes);
    off_t (*lseek)(struct file *file, off_t offset, int whence);
    int (*close)(struct file *file);
    int (*fstat)(struct file *file, struct stat *buf);
    int (*fcntl)(struct file *file, int cmd, va_list args);
    bool (*select_rd)(struct file *file);
    bool (*select_wr)(struct file *file);
};

struct mount_point {
    const char *path;
    int (*open)(struct mount_point *mnt, const char *pathname, int flags,
                mode_t mode);
    void *dev;
};

int mount(const char *path, void *dev,
          int (*open)(struct mount_point *, const char *, int, mode_t));
void umount(const char *path);

unsigned int alloc_file_type(const struct file_ops *ops);

off_t lseek_default(struct file *file, off_t offset, int whence);
bool select_yes(struct file *file);
bool select_read_flag(struct file *file);

struct file *get_file_from_fd(int fd);
int alloc_fd(unsigned int type);
void close_all_files(void);
extern struct thread *main_thread;
void sparse(unsigned long data, size_t size);

int close(int fd);
#endif

#endif /* _LIB_H_ */
