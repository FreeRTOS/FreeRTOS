/**
 * \addtogroup httpd
 * @{
 */

/**
 * \file
 * HTTP server read-only file system header file.
 * \author Adam Dunkels <adam@dunkels.com>
 */
 
/*
 * Copyright (c) 2001, Swedish Institute of Computer Science.
 * All rights reserved. 
 *
 * Redistribution and use in source and binary forms, with or without 
 * modification, are permitted provided that the following conditions 
 * are met: 
 * 1. Redistributions of source code must retain the above copyright 
 *    notice, this list of conditions and the following disclaimer. 
 * 2. Redistributions in binary form must reproduce the above copyright 
 *    notice, this list of conditions and the following disclaimer in the 
 *    documentation and/or other materials provided with the distribution. 
 * 3. Neither the name of the Institute nor the names of its contributors 
 *    may be used to endorse or promote products derived from this software 
 *    without specific prior written permission. 
 *
 * THIS SOFTWARE IS PROVIDED BY THE INSTITUTE AND CONTRIBUTORS ``AS IS'' AND 
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE 
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE 
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE INSTITUTE OR CONTRIBUTORS BE LIABLE 
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL 
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS 
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) 
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT 
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY 
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF 
 * SUCH DAMAGE. 
 *
 * This file is part of the lwIP TCP/IP stack.
 * 
 * Author: Adam Dunkels <adam@sics.se>
 *
 * $Id: fs.h,v 1.6.2.3 2003/10/07 13:22:27 adam Exp $
 */
#ifndef __FS_H__
#define __FS_H__

#include "uip.h"

/**
 * An open file in the read-only file system.
 */
struct fs_file {
  char *data;  /**< The actual file data. */
  int len;     /**< The length of the file data. */
};

/**
 * Open a file in the read-only file system.
 *
 * \param name The name of the file.
 *
 * \param file The file pointer, which must be allocated by caller and
 * will be filled in by the function.
 */
int fs_open(const char *name, struct fs_file *file);

#ifdef FS_STATISTICS
#if FS_STATISTICS == 1  
u16_t fs_count(char *name);
#endif /* FS_STATISTICS */
#endif /* FS_STATISTICS */

/**
 * Initialize the read-only file system.
 */
void fs_init(void);

#endif /* __FS_H__ */
