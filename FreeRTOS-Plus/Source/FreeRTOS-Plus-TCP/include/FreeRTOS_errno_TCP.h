/*
 * FreeRTOS+TCP Labs Build 160919 (C) 2016 Real Time Engineers ltd.
 * Authors include Hein Tibosch and Richard Barry
 *
 *******************************************************************************
 ***** NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ***
 ***                                                                         ***
 ***                                                                         ***
 ***   FREERTOS+TCP IS STILL IN THE LAB (mainly because the FTP and HTTP     ***
 ***   demos have a dependency on FreeRTOS+FAT, which is only in the Labs    ***
 ***   download):                                                            ***
 ***                                                                         ***
 ***   FreeRTOS+TCP is functional and has been used in commercial products   ***
 ***   for some time.  Be aware however that we are still refining its       ***
 ***   design, the source code does not yet quite conform to the strict      ***
 ***   coding and style standards mandated by Real Time Engineers ltd., and  ***
 ***   the documentation and testing is not necessarily complete.            ***
 ***                                                                         ***
 ***   PLEASE REPORT EXPERIENCES USING THE SUPPORT RESOURCES FOUND ON THE    ***
 ***   URL: http://www.FreeRTOS.org/contact  Active early adopters may, at   ***
 ***   the sole discretion of Real Time Engineers Ltd., be offered versions  ***
 ***   under a license other than that described below.                      ***
 ***                                                                         ***
 ***                                                                         ***
 ***** NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ***
 *******************************************************************************
 *
 * FreeRTOS+TCP can be used under two different free open source licenses.  The
 * license that applies is dependent on the processor on which FreeRTOS+TCP is
 * executed, as follows:
 *
 * If FreeRTOS+TCP is executed on one of the processors listed under the Special 
 * License Arrangements heading of the FreeRTOS+TCP license information web 
 * page, then it can be used under the terms of the FreeRTOS Open Source 
 * License.  If FreeRTOS+TCP is used on any other processor, then it can be used
 * under the terms of the GNU General Public License V2.  Links to the relevant
 * licenses follow:
 * 
 * The FreeRTOS+TCP License Information Page: http://www.FreeRTOS.org/tcp_license 
 * The FreeRTOS Open Source License: http://www.FreeRTOS.org/license
 * The GNU General Public License Version 2: http://www.FreeRTOS.org/gpl-2.0.txt
 *
 * FreeRTOS+TCP is distributed in the hope that it will be useful.  You cannot
 * use FreeRTOS+TCP unless you agree that you use the software 'as is'.
 * FreeRTOS+TCP is provided WITHOUT ANY WARRANTY; without even the implied
 * warranties of NON-INFRINGEMENT, MERCHANTABILITY or FITNESS FOR A PARTICULAR
 * PURPOSE. Real Time Engineers Ltd. disclaims all conditions and terms, be they
 * implied, expressed, or statutory.
 *
 * 1 tab == 4 spaces!
 *
 * http://www.FreeRTOS.org
 * http://www.FreeRTOS.org/plus
 * http://www.FreeRTOS.org/labs
 *
 */

#ifndef FREERTOS_ERRNO_TCP
#define FREERTOS_ERRNO_TCP

/* The following definitions will be included in the core FreeRTOS code in
future versions of FreeRTOS - hence the 'pd' (ProjDefs) prefix - at which time
this file will be removed. */

/* The following errno values are used by FreeRTOS+ components, not FreeRTOS
itself. */

/* For future compatibility (see comment above), check the definitions have not
already been made. */
#ifndef pdFREERTOS_ERRNO_NONE
	#define pdFREERTOS_ERRNO_NONE			0	/* No errors */
	#define	pdFREERTOS_ERRNO_ENOENT			2	/* No such file or directory */
	#define	pdFREERTOS_ERRNO_EINTR			4	/* Interrupted system call */
	#define	pdFREERTOS_ERRNO_EIO			5	/* I/O error */
	#define	pdFREERTOS_ERRNO_ENXIO			6	/* No such device or address */
	#define	pdFREERTOS_ERRNO_EBADF			9	/* Bad file number */
	#define	pdFREERTOS_ERRNO_EAGAIN			11	/* No more processes */
	#define	pdFREERTOS_ERRNO_EWOULDBLOCK	11	/* Operation would block */
	#define	pdFREERTOS_ERRNO_ENOMEM			12	/* Not enough memory */
	#define	pdFREERTOS_ERRNO_EACCES			13	/* Permission denied */
	#define	pdFREERTOS_ERRNO_EFAULT			14	/* Bad address */
	#define	pdFREERTOS_ERRNO_EBUSY			16	/* Mount device busy */
	#define	pdFREERTOS_ERRNO_EEXIST			17	/* File exists */
	#define	pdFREERTOS_ERRNO_EXDEV			18	/* Cross-device link */
	#define	pdFREERTOS_ERRNO_ENODEV			19	/* No such device */
	#define	pdFREERTOS_ERRNO_ENOTDIR		20	/* Not a directory */
	#define	pdFREERTOS_ERRNO_EISDIR			21	/* Is a directory */
	#define	pdFREERTOS_ERRNO_EINVAL			22	/* Invalid argument */
	#define	pdFREERTOS_ERRNO_ENOSPC			28	/* No space left on device */
	#define	pdFREERTOS_ERRNO_ESPIPE			29	/* Illegal seek */
	#define	pdFREERTOS_ERRNO_EROFS			30	/* Read only file system */
	#define	pdFREERTOS_ERRNO_EUNATCH		42	/* Protocol driver not attached */
	#define	pdFREERTOS_ERRNO_EBADE			50	/* Invalid exchange */
	#define	pdFREERTOS_ERRNO_EFTYPE			79	/* Inappropriate file type or format */
	#define	pdFREERTOS_ERRNO_ENMFILE		89	/* No more files */
	#define	pdFREERTOS_ERRNO_ENOTEMPTY		90	/* Directory not empty */
	#define	pdFREERTOS_ERRNO_ENAMETOOLONG 	91	/* File or path name too long */
	#define	pdFREERTOS_ERRNO_EOPNOTSUPP		95	/* Operation not supported on transport endpoint */
	#define	pdFREERTOS_ERRNO_ENOBUFS		105	/* No buffer space available */
	#define	pdFREERTOS_ERRNO_ENOPROTOOPT	109	/* Protocol not available */
	#define	pdFREERTOS_ERRNO_EADDRINUSE		112	/* Address already in use */
	#define	pdFREERTOS_ERRNO_ETIMEDOUT		116	/* Connection timed out */
	#define	pdFREERTOS_ERRNO_EINPROGRESS	119	/* Connection already in progress */
	#define	pdFREERTOS_ERRNO_EALREADY		120	/* Socket already connected */
	#define	pdFREERTOS_ERRNO_EADDRNOTAVAIL 	125	/* Address not available */
	#define	pdFREERTOS_ERRNO_EISCONN		127	/* Socket is already connected */
	#define	pdFREERTOS_ERRNO_ENOTCONN		128	/* Socket is not connected */
	#define	pdFREERTOS_ERRNO_ENOMEDIUM		135	/* No medium inserted */
	#define	pdFREERTOS_ERRNO_EILSEQ			138	/* An invalid UTF-16 sequence was encountered. */
	#define	pdFREERTOS_ERRNO_ECANCELED		140	/* Operation canceled. */

	/* The following endian values are used by FreeRTOS+ components, not FreeRTOS
	itself. */
	#define pdFREERTOS_LITTLE_ENDIAN	0
	#define pdFREERTOS_BIG_ENDIAN		1

#endif /* pdFREERTOS_ERRNO_NONE */

#endif /* FREERTOS_ERRNO_TCP */



