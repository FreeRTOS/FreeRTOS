/* SPDX-License-Identifier: BSD-3-Clause */
/*
 * Copyright (c) 1995 Danny Gasparovski.
 */

#ifndef SBUF_H
#define SBUF_H

#define sbspace(sb) ((sb)->sb_datalen - (sb)->sb_cc)

struct sbuf {
    uint32_t sb_cc; /* actual chars in buffer */
    uint32_t sb_datalen; /* Length of data  */
    char *sb_wptr; /* write pointer. points to where the next
                    * bytes should be written in the sbuf */
    char *sb_rptr; /* read pointer. points to where the next
                    * byte should be read from the sbuf */
    char *sb_data; /* Actual data */
};

void sbfree(struct sbuf *sb);
bool sbdrop(struct sbuf *sb, size_t len);
void sbreserve(struct sbuf *sb, size_t size);
void sbappend(struct socket *sb, struct mbuf *mb);
void sbcopy(struct sbuf *sb, size_t off, size_t len, char *p);

#endif
