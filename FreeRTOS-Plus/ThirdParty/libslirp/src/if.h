/* SPDX-License-Identifier: BSD-3-Clause */
/*
 * Copyright (c) 1995 Danny Gasparovski.
 */

#ifndef IF_H
#define IF_H

#define IF_COMPRESS 0x01 /* We want compression */
#define IF_NOCOMPRESS 0x02 /* Do not do compression */
#define IF_AUTOCOMP 0x04 /* Autodetect (default) */
#define IF_NOCIDCOMP 0x08 /* CID compression */

#define IF_MTU_DEFAULT 1500
#define IF_MTU_MIN 68
#define IF_MTU_MAX 65521
#define IF_MRU_DEFAULT 1500
#define IF_MRU_MIN 68
#define IF_MRU_MAX 65521
#define IF_COMP IF_AUTOCOMP /* Flags for compression */

/* 2 for alignment, 14 for ethernet */
#define IF_MAXLINKHDR (2 + ETH_HLEN)

#endif
