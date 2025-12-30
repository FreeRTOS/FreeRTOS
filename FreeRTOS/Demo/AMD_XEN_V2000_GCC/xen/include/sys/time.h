/* -*-  Mode:C; c-basic-offset:4; tab-width:4 -*-
 ****************************************************************************
 * (C) 2003 - Rolf Neugebauer - Intel Research Cambridge
 * (C) 2005 - Grzegorz Milos - Intel Research Cambridge
 ****************************************************************************
 *
 *        File: time.h
 *      Author: Rolf Neugebauer (neugebar@dcs.gla.ac.uk)
 *     Changes: Grzegorz Milos (gm281@cam.ac.uk)
 *              Robert Kaiser (kaiser@informatik.fh-wiesbaden.de)
 *              
 *        Date: Jul 2003, changes: Jun 2005, Sep 2006
 * 
 * Environment: Xen Minimal OS
 * Description: Time and timer functions
 *
 ****************************************************************************
 */

#ifndef _MINIOS_SYS_TIME_H_
#define _MINIOS_SYS_TIME_H_

#ifdef HAVE_LIBC
#include_next <sys/time.h>

#else
struct timespec {
    time_t      tv_sec;
    long        tv_nsec;
};

struct timezone {
};

struct timeval {
	time_t		tv_sec;		/* seconds */
	suseconds_t	tv_usec;	/* microseconds */
};

int      gettimeofday(struct timeval *tv, void *tz);

#endif
#ifdef HAVE_LIBC
#include <sys/select.h>
#endif

#endif /* _MINIOS_SYS_TIME_H_ */
