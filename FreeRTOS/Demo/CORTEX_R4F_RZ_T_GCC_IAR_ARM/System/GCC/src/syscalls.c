/* Support files for GNU libc.  Files in the system namespace go here.
   Files in the C namespace (ie those that do not start with an
   underscore) go in .c.  */

#include <_ansi.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/fcntl.h>
#include <stdio.h>
#include <time.h>
#include <sys/time.h>
#include <sys/times.h>
#include <errno.h>
#include <reent.h>
#include <signal.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>
#include "r_typedefs.h"
#include "siochar.h"
#include "swi.h"


#ifndef NULL
#define NULL (0)
#endif

/* Forward prototypes.  */
int     _system     _PARAMS ((const char *));
int     _rename     _PARAMS ((const char *, const char *));
int     _isatty		_PARAMS ((int));
clock_t _times		_PARAMS ((struct tms *));
int     _gettimeofday	_PARAMS ((struct timeval *, void *));
void    _raise 		_PARAMS ((void));
int     _unlink		_PARAMS ((const char *));
int     _link 		_PARAMS ((void));
int     _stat 		_PARAMS ((const char *, struct stat *));
int     _fstat 		_PARAMS ((int, struct stat *));
caddr_t _sbrk		_PARAMS ((int));
int     _getpid		_PARAMS ((int));
int     _kill		_PARAMS ((int, int));
void    _exit		_PARAMS ((int));
int     _close		_PARAMS ((int));
int     _swiclose	_PARAMS ((int));
int     _open		_PARAMS ((const char *, int, ...));
int     _swiopen	_PARAMS ((const char *, int));
int 	_write		_PARAMS ((int, const char *, unsigned int));

int     _swiwrite	_PARAMS ((int, char *, int));
int     _lseek		_PARAMS ((int, int, int));
int     _swilseek	_PARAMS ((int, int, int));
int 	_read		_PARAMS ((int, char *, unsigned int));

int     _swiread	_PARAMS ((int, char *, int));
void    initialise_monitor_handles _PARAMS ((void));

static int	wrap		_PARAMS ((int));
static int	error		_PARAMS ((int));
static int	get_errno	_PARAMS ((void));
static int	remap_handle	_PARAMS ((int));

#ifdef ARM_RDI_MONITOR
static int	do_AngelSWI	_PARAMS ((int, void *));
#endif

static int 	findslot	_PARAMS ((int));

/* Register name faking - works in collusion with the linker.  */
register char * stack_ptr __asm ("sp");


/* following is copied from libc/stdio/local.h to check std streams */
extern void   _EXFUN(__sinit,(struct _reent *));
#define CHECK_INIT(ptr) \
        do						\
            {						\
              if ((ptr) && !(ptr)->__sdidinit)		\
            __sinit (ptr);				\
            }						\
          while (0)

/* Adjust our internal handles to stay away from std* handles.  */
#define FILE_HANDLE_OFFSET (0x20)

static int monitor_stdin;
static int monitor_stdout;
static int monitor_stderr;

/* Struct used to keep track of the file position, just so we
   can implement fseek(fh,x,SEEK_CUR).  */
typedef struct
{
  int handle;
  int pos;
}
poslog;

#define MAX_OPEN_FILES (20)
static poslog openfiles [MAX_OPEN_FILES];

static int
findslot (int fh)
{
  int i;
  for (i = 0; i < MAX_OPEN_FILES; i ++)
    if (openfiles[i].handle == fh)
    {
        break;
    }
  return (i);
}

#ifdef ARM_RDI_MONITOR

static inline int
do_AngelSWI (int reason, void * arg)
{
  int value;
  asm volatile ("mov r0, %1; mov r1, %2; " AngelSWIInsn " %a3; mov %0, r0"
       : "=r" (value) /* Outputs */
       : "r" (reason), "r" (arg), "i" (AngelSWI) /* Inputs */
       : "r0", "r1", "r2", "r3", "ip", "lr", "memory", "cc"
		/* Clobbers r0 and r1, and lr if in supervisor mode */);
                /* Accordingly to page 13-77 of ARM DUI 0040D other registers
                   can also be clobbered.  Some memory positions may also be
                   changed by a system call, so they should not be kept in
                   registers. Note: we are assuming the manual is right and
                   Angel is respecting the APCS.  */
  return value;
}
#endif /* ARM_RDI_MONITOR */

/* Function to convert std(in|out|err) handles to internal versions.  */
static int
remap_handle (int fh)
{
    CHECK_INIT(_REENT);

    if (STDIN_FILENO == fh)
    {
        return (monitor_stdin);
    }
    if (STDOUT_FILENO == fh)
    {
        return (monitor_stdout);
    }
    if (STDERR_FILENO == fh)
    {
        return (monitor_stderr);
    }

  return (fh - FILE_HANDLE_OFFSET);
}

void
initialise_monitor_handles (void)
{
  int i;
  
#ifdef ARM_RDI_MONITOR
  int volatile block[3];
  
  block[0] = (int) ":tt";
  block[2] = 3;     /* length of filename */
  block[1] = 0;     /* mode "r" */
  monitor_stdin = do_AngelSWI (AngelSWI_Reason_Open, (void *) block);

  block[0] = (int) ":tt";
  block[2] = 3;     /* length of filename */
  block[1] = 4;     /* mode "w" */
  monitor_stdout = monitor_stderr = do_AngelSWI (AngelSWI_Reason_Open, (void *) block);
#else
  int fh;
  const char * pname;

  pname = ":tt";
  __asm ("mov r0,%2; mov r1, #0; swi %a1; mov %0, r0"
       : "=r"(fh)
       : "i" (SWI_Open),"r"(pname)
       : "r0","r1");
  monitor_stdin = fh;

  pname = ":tt";
  __asm ("mov r0,%2; mov r1, #4; swi %a1; mov %0, r0"
       : "=r"(fh)
       : "i" (SWI_Open),"r"(pname)
       : "r0","r1");
  monitor_stdout = (monitor_stderr = fh);
#endif

    for (i = 0; i < MAX_OPEN_FILES; i ++)
    {
        openfiles[i].handle = (-1);
    }

    openfiles[0].handle = monitor_stdin;
    openfiles[0].pos = 0;
    openfiles[1].handle = monitor_stdout;
    openfiles[1].pos = 0;
}

static int
get_errno (void)
{
#ifdef ARM_RDI_MONITOR
  return do_AngelSWI (AngelSWI_Reason_Errno, NULL);
#else
  __asm ("swi %a0" :: "i" (SWI_GetErrno));
  return (0);
#endif
}

static int
error (int result)
{
  errno = get_errno ();
  return (result);
}

static int
wrap (int result)
{
    if ((-1) == result)
    {
        return (error(-1));
    }
    return (result);
}

/* Returns # chars not! written.  */
int
_swiread (int file,
	  char * ptr,
	  int len)
{
  int fh = remap_handle (file);
#ifdef ARM_RDI_MONITOR
  int block[3];
  
  block[0] = fh;
  block[1] = (int) ptr;
  block[2] = len;
  
  return do_AngelSWI (AngelSWI_Reason_Read, block);
#else
  __asm ("mov r0, %1; mov r1, %2;mov r2, %3; swi %a0"
       : /* No outputs */
       : "i"(SWI_Read), "r"(fh), "r"(ptr), "r"(len)
       : "r0","r1","r2");
  return (0);
#endif
}

/******************************************************************************
* Function Name: _read
* Description  : GNU interface to low-level I/O read
* Arguments    : int file_no
*              : const char *buffer
*              : unsigned int n
* Return Value : none
******************************************************************************/
int _read(int file_no , char *buffer , unsigned int n)
{
    return (sio_read(file_no , buffer , n));
}

int
_swilseek (int file,
	   int ptr,
	   int dir)
{
  int res;
  int fh = remap_handle (file);
  int slot = findslot (fh);
#ifdef ARM_RDI_MONITOR
  int block[2];
#endif

  if (SEEK_CUR == dir)
    {
        if (MAX_OPEN_FILES == slot)
        {
            return (-1);
        }
        ptr = (openfiles[slot].pos + ptr);
        dir = SEEK_SET;
    }
  
#ifdef ARM_RDI_MONITOR
  if (dir == SEEK_END)
    {
      block[0] = fh;
      ptr += do_AngelSWI (AngelSWI_Reason_FLen, block);
    }
  
  /* This code only does absolute seeks.  */
  block[0] = remap_handle (file);
  block[1] = ptr;
  res = do_AngelSWI (AngelSWI_Reason_Seek, block);
#else
  if (SEEK_END == dir)
    {
      __asm ("mov r0, %2; swi %a1; mov %0, r0"
	   : "=r" (res)
	   : "i" (SWI_Flen), "r" (fh)
	   : "r0");
      ptr += res;
    }

  /* This code only does absolute seeks.  */
  __asm ("mov r0, %2; mov r1, %3; swi %a1; mov %0, r0"
       : "=r" (res)
       : "i" (SWI_Seek), "r" (fh), "r" (ptr)
       : "r0", "r1");
#endif

    if ((MAX_OPEN_FILES != slot) && (0 == res))
    {
        openfiles[slot].pos = ptr;
    }

  /* This is expected to return the position in the file.  */
    return ((0 == res) ? ptr : (-1));
}

int
_lseek (int file,
	int ptr,
	int dir)
{
  return (wrap (_swilseek (file, ptr, dir)));
}

/* Returns #chars not! written.  */
int
_swiwrite (
	   int    file,
	   char * ptr,
	   int    len)
{
  int fh = remap_handle (file);
#ifdef ARM_RDI_MONITOR
  int block[3];
  
  block[0] = fh;
  block[1] = (int) ptr;
  block[2] = len;
  
  return do_AngelSWI (AngelSWI_Reason_Write, block);
#else
  __asm ("mov r0, %1; mov r1, %2;mov r2, %3; swi %a0"
       : /* No outputs */
       : "i"(SWI_Write), "r"(fh), "r"(ptr), "r"(len)
       : "r0","r1","r2");
  return (0);
#endif
}

/******************************************************************************
* Function Name: _write
* Description  : GNU interface to low-level I/O write
* Arguments    : int file_no
*              : const char *buffer
*              : unsigned int n
* Return Value : none
******************************************************************************/
int _write(int file_no , const char *buffer , unsigned int n)
{
    return (sio_write(file_no , buffer , n));
}

int
_swiopen (const char * path,
	  int          flags)
{
  int aflags = 0, fh;
#ifdef ARM_RDI_MONITOR
  int block[3];
#endif
  
  int i = findslot (-1);
  
  if (MAX_OPEN_FILES == i)
    {
        return (-1);
    }

  /* The flags are Unix-style, so we need to convert them.  */
#ifdef O_BINARY
  if (flags & O_BINARY)
    {
        aflags |= 1;
    }
#endif

  if (flags & O_RDWR)
    {
        aflags |= 2;
    }

  if (flags & O_CREAT)
    {
        aflags |= 4;
    }

  if (flags & O_TRUNC)
    {
        aflags |= 4;
    }

  if (flags & O_APPEND)
    {
      aflags &= (~4);     /* Can't ask for w AND a; means just 'a'.  */
      aflags |= 8;
    }
  
#ifdef ARM_RDI_MONITOR
  block[0] = (int) path;
  block[2] = strlen (path);
  block[1] = aflags;
  
  fh = do_AngelSWI (AngelSWI_Reason_Open, block);
  
#else
  __asm ("mov r0,%2; mov r1, %3; swi %a1; mov %0, r0"
       : "=r"(fh)
       : "i" (SWI_Open),"r"(path),"r"(aflags)
       : "r0","r1");
#endif
  
  if (fh >= 0)
    {
      openfiles[i].handle = fh;
      openfiles[i].pos = 0;
    }

  return ((fh >= 0) ? (fh + FILE_HANDLE_OFFSET) : error (fh));
}

int
_open (const char * path,
       int          flags,
       ...)
{
  return (wrap (_swiopen (path, flags)));
}

int
_swiclose (int file)
{
  int myhan = remap_handle (file);
  int slot = findslot (myhan);
  
  if (MAX_OPEN_FILES != slot)
    {
        openfiles[slot].handle = (-1);
    }

#ifdef ARM_RDI_MONITOR
  return do_AngelSWI (AngelSWI_Reason_Close, & myhan);
#else
  __asm ("mov r0, %1; swi %a0" :: "i" (SWI_Close),"r"(myhan):"r0");
  return (0);
#endif
}

int
_close (int file)
{
  return (wrap (_swiclose (file)));
}

int
_kill (int pid, int sig)
{
  (void)pid; (void)sig;
#ifdef ARM_RDI_MONITOR
  /* Note: The pid argument is thrown away.  */
  switch (sig) {
	  case SIGABRT:
		  return do_AngelSWI (AngelSWI_Reason_ReportException,
				  (void *) ADP_Stopped_RunTimeError);
	  default:
		  return do_AngelSWI (AngelSWI_Reason_ReportException,
				  (void *) ADP_Stopped_ApplicationExit);
  }
#else
  __asm ("swi %a0" :: "i" (SWI_Exit));
  return (0);
#endif
}

void
_exit (int status)
{
  /* There is only one SWI for both _exit and _kill. For _exit, call
     the SWI with the second argument set to -1, an invalid value for
     signum, so that the SWI handler can distinguish the two calls.
     Note: The RDI implementation of _kill throws away both its
     arguments.  */
  _kill(status, -1);
  while(1)
  {
      /* exit occurred */
  };
}

int
_getpid (int n)
{
  (void)(n);
  return (1);
}

caddr_t
_sbrk (int incr)
{
  extern char   end __asm ("end");	/* Defined by the linker.  */
  static char * pheap_end;
  char *        prev_heap_end;

    if (NULL == pheap_end)
    {
        pheap_end = (&end);
    }
  
  prev_heap_end = pheap_end;
  
  if ((pheap_end + incr) > stack_ptr)
    {
      /* Some of the libstdc++-v3 tests rely upon detecting
	 out of memory errors, so do not abort here.  */
#if 0
      extern void abort (void);

      _write (1, "_sbrk: Heap and stack collision\n", 32);
      
      abort ();
#else
      errno = ENOMEM;
      return ((caddr_t) (-1));
#endif
    }
  
  pheap_end += incr;

  return ((caddr_t) prev_heap_end);
}

int
_fstat (int file, struct stat * st)
{
  (void)file;
  memset (st, 0, sizeof (* st));
  st->st_mode = S_IFCHR;
  st->st_blksize = 1024;
  return (0);
}

int _stat (const char *fname, struct stat *st)
{
  int file;

  /* The best we can do is try to open the file read-only.  If it exists,
     then we can guess a few things about it.  */
  if ((file = _open (fname, O_RDONLY)) < 0)
    {
        return (-1);
    }

  memset (st, 0, sizeof (* st));
  st->st_mode = (S_IFREG | S_IREAD);
  st->st_blksize = 1024;
  _swiclose (file); /* Not interested in the error.  */
  return (0);
}

int
_link (void)
{
  return (-1);
}

int
_unlink (const char *path)
{
#ifdef ARM_RDI_MONITOR
  int block[2];
  block[0] = path;
  block[1] = strlen(path);
  return wrap (do_AngelSWI (AngelSWI_Reason_Remove, block)) ? -1 : 0;
#else  
  return -1;
#endif
}

void
_raise (void)
{
  return;
}

int
_gettimeofday (struct timeval * tp, void * tzvp)
{
  struct timezone * ptzp = tzvp;
  if (tp)
    {
    /* Ask the host for the seconds since the Unix epoch.  */
#ifdef ARM_RDI_MONITOR
      tp->tv_sec = do_AngelSWI (AngelSWI_Reason_Time,NULL);
#else
      {
        int value;
        __asm ("swi %a1; mov %0, r0" : "=r" (value): "i" (SWI_Time) : "r0");
        tp->tv_sec = value;
      }
#endif
      tp->tv_usec = 0;
    }

  /* Return fixed data for the time-zone.  */
  if (ptzp)
    {
      ptzp->tz_minuteswest = 0;
      ptzp->tz_dsttime = 0;
    }

  return (0);
}

/* Return a clock that ticks at 100Hz.  */
clock_t 
_times (struct tms * tp)
{
  clock_t timeval;

#ifdef ARM_RDI_MONITOR
  timeval = do_AngelSWI (AngelSWI_Reason_Clock,NULL);
#else
  __asm ("swi %a1; mov %0, r0" : "=r" (timeval): "i" (SWI_Clock) : "r0");
#endif

  if (tp)
    {
      tp->tms_utime  = timeval;	/* user time */
      tp->tms_stime  = 0;	/* system time */
      tp->tms_cutime = 0;	/* user time, children */
      tp->tms_cstime = 0;	/* system time, children */
    }
  
  return (timeval);
};


int
_isatty (int fd)
{
#ifdef ARM_RDI_MONITOR
  int fh = remap_handle (fd);
  return wrap (do_AngelSWI (AngelSWI_Reason_IsTTY, &fh));
#else
  return ((fd <= 2) ? 1 : 0);  /* one of stdin, stdout, stderr */
#endif
}

int
_system (const char *s)
{
#ifdef ARM_RDI_MONITOR
  int block[2];
  int e;

  /* Hmmm.  The ARM debug interface specification doesn't say whether
     SYS_SYSTEM does the right thing with a null argument, or assign any
     meaning to its return value.  Try to do something reasonable....  */
  if (!s)
    return 1;  /* maybe there is a shell available? we can hope. :-P */
  block[0] = s;
  block[1] = strlen (s);
  e = wrap (do_AngelSWI (AngelSWI_Reason_System, block));
  if ((e >= 0) && (e < 256))
    {
      /* We have to convert e, an exit status to the encoded status of
         the command.  To avoid hard coding the exit status, we simply
	 loop until we find the right position.  */
      int exit_code;

      for (exit_code = e; e && WEXITSTATUS (e) != exit_code; e <<= 1)
	continue;
    }
  return e;
#else
  if (NULL == s)
    {
        return (0);
    }
  errno = ENOSYS;
  return (-1);
#endif
}

int
_rename (const char * oldpath, const char * newpath)
{
#ifdef ARM_RDI_MONITOR
  int block[4];
  block[0] = oldpath;
  block[1] = strlen(oldpath);
  block[2] = newpath;
  block[3] = strlen(newpath);
  return wrap (do_AngelSWI (AngelSWI_Reason_Rename, block)) ? -1 : 0;
#else  
  errno = ENOSYS;
  return (-1);
#endif
}
