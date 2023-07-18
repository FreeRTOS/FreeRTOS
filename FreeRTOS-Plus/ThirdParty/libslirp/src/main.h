/* SPDX-License-Identifier: BSD-3-Clause */
/*
 * Copyright (c) 1995 Danny Gasparovski.
 */

#ifndef SLIRP_MAIN_H
#define SLIRP_MAIN_H

#include "libslirp.h"

extern unsigned curtime;
extern struct in_addr loopback_addr;
extern unsigned long loopback_mask;

int if_encap(Slirp *slirp, struct mbuf *ifm);
slirp_ssize_t slirp_send(struct socket *so, const void *buf, size_t len, int flags);

#endif
