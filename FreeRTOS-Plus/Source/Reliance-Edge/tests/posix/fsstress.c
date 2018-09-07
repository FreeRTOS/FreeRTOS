/*
 * Copyright (c) 2000 Silicon Graphics, Inc.  All Rights Reserved.
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of version 2 of the GNU General Public License as
 * published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it would be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 * Further, this software is distributed without any warranty that it is
 * free of the rightful claim of any third person regarding infringement
 * or the like.  Any license provided herein, whether implied or
 * otherwise, applies only to this software file.  Patent licenses, if
 * any, provided herein do not apply to combinations of this program with
 * other software, or any other product whatsoever.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Contact information: Silicon Graphics, Inc., 1600 Amphitheatre Pkwy,
 * Mountain View, CA  94043, or:
 *
 * http://www.sgi.com
 *
 * For further information regarding this notice, see:
 *
 * http://oss.sgi.com/projects/GenInfo/SGIGPLNoticeExplan/
 */
/** @file
    @brief File system stress test.

    This version of SGI fsstress has been modified to be single-threaded and to
    work with the Reliance Edge POSIX-like API.
*/
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <string.h>
#include <stdarg.h>
#include <time.h>

#include <redposix.h>
#include <redtests.h>

#if FSSTRESS_SUPPORTED

#include "redposixcompat.h"

#include <redosserv.h>
#include <redutils.h>
#include <redmacs.h>
#include <redvolume.h>
#include <redgetopt.h>
#include <redtoolcmn.h>

#if REDCONF_CHECKER == 1
#include <redcoreapi.h>
#endif


/*  Create POSIX types.  Use #define to avoid name conflicts in those
    environments where the type names already exist.
*/
#define off_t int64_t
#define off64_t off_t
#define ino_t uint32_t
#define mode_t uint16_t
#define __int64_t int64_t


/** @brief Generate a random number.

    @return A nonnegative random number.
*/
#define random() ((int)(RedRand32(NULL) & 0x7FFFFFFF))


/** @brief Seed the random number generator.
*/
#define srandom(seed) RedRandSeed(seed)


#define _exit(status) exit(status)
#define getpagesize() 4096U
#define getpid() 1


/** @brief Determine the maximum file size.

    This is used for the MAXFSSIZE macro.
*/
static uint64_t MaxFileSize(void)
{
    REDSTATFS   info;
    int32_t     iStatus;
    REDSTATUS   errnoSave = errno;
    uint64_t    ullMaxFileSize;

    iStatus = red_statvfs("", &info);
    if(iStatus == 0)
    {
        ullMaxFileSize = info.f_maxfsize;
    }
    else
    {
        /*  This function does not change errno.
        */
        errno = errnoSave;

        ullMaxFileSize = 0x7FFFFFFFU;
    }

    return ullMaxFileSize;
}


/*-------------------------------------------------------------------
    Simulated current working directory support
-------------------------------------------------------------------*/


/*  Forward declaration for red_chdir().
*/
static int red_stat(const char *pszPath, REDSTAT *pStat);

/*  The simulated CWD functions.
*/
#undef chdir
#undef getcwd
#define chdir(path) red_chdir(path)
#define getcwd(buf, size) red_getcwd(buf, size)


/*  Redefine the path-based APIs to call MakeFullPath() on their arguments
    since there is no CWD support in the red_*() APIs.
*/
#undef open
#undef unlink
#undef mkdir
#undef rmdir
#undef rename
#undef link
#undef opendir
#define open(path, oflag) red_open(MakeFullPath(path), oflag)
#define unlink(path) red_unlink(MakeFullPath(path))
#define mkdir(path) red_mkdir(MakeFullPath(path))
#define rmdir(path) red_rmdir(MakeFullPath(path))
#define rename(old, new) red_rename(MakeFullPath(old), MakeFullPath(new))
#define link(path, hardlink) red_link(MakeFullPath(path), MakeFullPath(hardlink))
#define opendir(path) red_opendir(MakeFullPath(path))

#define FSSTRESS_BUF_SIZE 1024U

/*  Stores the simulated current working directory.
*/
static char szLocalCwd[FSSTRESS_BUF_SIZE] = "/";


/** @brief Change the current working directory.

    This function only supports a subset of what is possible with POSIX chdir().

    @param pszPath  The new current working directory.

    @return Upon successful completion, 0 shall be returned.  Otherwise, -1
            shall be returned, and errno shall be set to indicate the error.
*/
static int red_chdir(
    const char *pszPath)
{
    uint32_t    ulIdx;
    int         iErrno = 0;

    if(strcmp(pszPath, "..") == 0)
    {
        uint32_t ulLastSlashIdx = 0U;

        /*  Chop off the last path separator and everything after it, so that
            "/foo/bar/baz" becomes "/foo/bar", moving the CWD up one directory.
        */
        for(ulIdx = 0U; szLocalCwd[ulIdx] != '\0'; ulIdx++)
        {
            if(szLocalCwd[ulIdx] == '/')
            {
                ulLastSlashIdx = ulIdx;
            }
        }

        if(ulLastSlashIdx != 0U)
        {
            szLocalCwd[ulLastSlashIdx] = '\0';
        }
    }
    else
    {
        char    szOldCwd[FSSTRESS_BUF_SIZE];

        /*  chdir() must have no effect on the CWD if it fails, so save the CWD
            so we can revert it if necessary.
        */
        strcpy(szOldCwd, szLocalCwd);

        if(pszPath[0U] == '/')
        {
            if(strlen(pszPath) >= sizeof(szLocalCwd))
            {
                iErrno = RED_ENAMETOOLONG;
            }
            else
            {
                strcpy(szLocalCwd, pszPath);
            }
        }
        else
        {
            ulIdx = strlen(szLocalCwd);

            if((ulIdx + 1U + strlen(pszPath)) >= sizeof(szLocalCwd))
            {
                iErrno = RED_ENAMETOOLONG;
            }
            else
            {
                if(szLocalCwd[1U] != '\0')
                {
                    szLocalCwd[ulIdx] = '/';
                    ulIdx++;
                }

                strcpy(&szLocalCwd[ulIdx], pszPath);
            }
        }

        if(iErrno == 0)
        {
            REDSTAT s;
            int     iStatus;

            iStatus = red_stat(szLocalCwd, &s);
            if(iStatus != 0)
            {
                iErrno = errno;
            }
            else if(!S_ISDIR(s.st_mode))
            {
                iErrno = RED_ENOTDIR;
            }
            else
            {
                /*  No error, new CWD checks out.
                */
            }
        }

        if(iErrno != 0)
        {
            strcpy(szLocalCwd, szOldCwd);
        }
    }

    if(iErrno != 0)
    {
        errno = iErrno;
    }

    return iErrno == 0 ? 0 : -1;
}


/** @brief Retrieve the current working directory.

    @param pszBuf   On successful return, populated with the current working
                    directory.  If NULL, memory will be allocated for the CWD
                    and returned by this function.
    @param nSize    The size of @p pszBuf.

    @return On success, if @p pszBuf was non-NULL, returns @p pszBuf; if
            @p pszBuf was NULL, returns an allocated buffer populated with the
            CWD which must be freed by the caller.  On failure, returns NULL
            and errno will be set.
*/
static char *red_getcwd(
    char   *pszBuf,
    size_t  nSize)
{
    char   *pszRet;

    if(pszBuf == NULL)
    {
        pszRet = malloc(strlen(szLocalCwd) + 1U);
        if(pszRet == NULL)
        {
            errno = RED_ENOMEM;
        }
        else
        {
            strcpy(pszRet, szLocalCwd);
        }
    }
    else if(nSize < strlen(szLocalCwd) + 1U)
    {
        errno = RED_ERANGE;
        pszRet = NULL;
    }
    else
    {
        strcpy(pszBuf, szLocalCwd);
        pszRet = pszBuf;
    }

    return pszRet;
}


/** @brief Make a relative path into a fully qualified path.

    @param pszName  The relative path.

    @return On success, a pointer to a fully qualified path.  On error, NULL.
*/
static const char *MakeFullPath(
    const char     *pszName)
{
    #define         MAXVOLNAME 64U /* Enough for most configs. */
    static char     aszFullPath[2U][MAXVOLNAME + 1U + FSSTRESS_BUF_SIZE];
    static uint32_t ulWhich = 0U;

    char           *pszFullPath = aszFullPath[ulWhich];
    const char     *pszVolume = gpRedVolConf->pszPathPrefix;
    int32_t         iLen;

    if(pszName[0U] == '/')
    {
        iLen = RedSNPrintf(pszFullPath, sizeof(aszFullPath[0U]), "%s%s", pszVolume, pszName);
    }
    else if(strcmp(pszName, ".") == 0U)
    {
        iLen = RedSNPrintf(pszFullPath, sizeof(aszFullPath[0U]), "%s%s", pszVolume, szLocalCwd);
    }
    else if((szLocalCwd[0U] == '/') && (szLocalCwd[1U] == '\0'))
    {
        iLen = RedSNPrintf(pszFullPath, sizeof(aszFullPath[0U]), "%s/%s", pszVolume, pszName);
    }
    else
    {
        iLen = RedSNPrintf(pszFullPath, sizeof(aszFullPath[0U]), "%s%s/%s", pszVolume, szLocalCwd, pszName);
    }

    if(iLen == -1)
    {
        /*  Insufficient path buffer space.
        */
        pszFullPath = NULL;
    }
    else
    {
        /*  Toggle between two full path arrays; a kluge to make rename() and
            link() work correctly.
        */
        ulWhich ^= 1U;
    }

    return pszFullPath;
}


/*-------------------------------------------------------------------
    POSIX functions not implemented by the RED POSIX-like API
-------------------------------------------------------------------*/

#define stat(p, s) red_stat(p, s)
#define stat64(p, s) stat(p, s)
#define lstat(p, s) stat(p, s)
#define lstat64(p, s) stat(p, s)
#define truncate(p, s) red_truncate(p, s)
#define truncate64(p, s) truncate(p, s)


/** @brief Get the status of a file or directory.
*/
static int red_stat(
    const char *pszPath,
    REDSTAT    *pStat)
{
    int         iFd;
    int         iRet;

    iFd = open(pszPath, O_RDONLY);
    iRet = iFd;
    if(iFd != -1)
    {
        iRet = fstat(iFd, pStat);

        (void)close(iFd);
    }

    return iRet;
}


/** @brief Truncate a file to a specified length.
*/
static int red_truncate(
    const char *pszPath,
    off_t       llSize)
{
    int         iFd;
    int         iRet;

    iFd = open(pszPath, O_WRONLY);
    iRet = iFd;
    if(iFd != -1)
    {
        iRet = ftruncate(iFd, llSize);

        (void)close(iFd);
    }

    return iRet;
}


/*-------------------------------------------------------------------
    Begin ported fsstress code
-------------------------------------------------------------------*/

/* Stuff from xfscompat.h */

#define MAXNAMELEN (REDCONF_NAME_MAX+1U) /* Assumed to include NUL */

struct dioattr {
    int d_miniosz, d_maxiosz, d_mem;
};

#define MIN(a,b) ((a)<(b) ? (a):(b))
#define MAX(a,b) ((a)>(b) ? (a):(b))

/* End xfscompat.h */


typedef enum {
    OP_CREAT,
    OP_FDATASYNC,
    OP_FSYNC,
    OP_GETDENTS,
    OP_LINK,
    OP_MKDIR,
    OP_READ,
    OP_RENAME,
    OP_RMDIR,
    OP_STAT,
    OP_TRUNCATE,
    OP_UNLINK,
    OP_WRITE,
  #if REDCONF_CHECKER == 1
    OP_CHECK,
  #endif
    OP_LAST
} opty_t;

typedef void (*opfnc_t) (int, long);

typedef struct opdesc {
    opty_t op;
    const char *name;
    opfnc_t func;
    int freq;
    int iswrite;
} opdesc_t;

typedef struct fent {
    int id;
    int parent;
} fent_t;

typedef struct flist {
    int nfiles;
    int nslots;
    int tag;
    fent_t *fents;
} flist_t;

typedef struct pathname {
    int len;
    char *path;
} pathname_t;

#define FT_DIR      0
#define FT_DIRm     (1 << FT_DIR)
#define FT_REG      1
#define FT_REGm     (1 << FT_REG)
#define FT_SYM      2
#define FT_SYMm     (1 << FT_SYM)
#define FT_DEV      3
#define FT_DEVm     (1 << FT_DEV)
#define FT_RTF      4
#define FT_RTFm     (1 << FT_RTF)
#define FT_nft      5
#define FT_ANYm     ((1 << FT_nft) - 1)
#define FT_REGFILE  (FT_REGm | FT_RTFm)
#define FT_NOTDIR   (FT_ANYm & ~FT_DIRm)

#define FLIST_SLOT_INCR 16
#define NDCACHE 64

#define MAXFSIZE MaxFileSize()

static void creat_f(int opno, long r);
static void fdatasync_f(int opno, long r);
static void fsync_f(int opno, long r);
static void getdents_f(int opno, long r);
static void link_f(int opno, long r);
static void mkdir_f(int opno, long r);
static void read_f(int opno, long r);
static void rename_f(int opno, long r);
static void rmdir_f(int opno, long r);
static void stat_f(int opno, long r);
static void truncate_f(int opno, long r);
static void unlink_f(int opno, long r);
static void write_f(int opno, long r);
#if REDCONF_CHECKER == 1
static void check_f(int opno, long r);
#endif

static opdesc_t ops[] = {
    {OP_CREAT, "creat", creat_f, 4, 1},
    {OP_FDATASYNC, "fdatasync", fdatasync_f, 1, 1},
    {OP_FSYNC, "fsync", fsync_f, 1, 1},
    {OP_GETDENTS, "getdents", getdents_f, 1, 0},
    {OP_LINK, "link", link_f, 1, 1},
    {OP_MKDIR, "mkdir", mkdir_f, 2, 1},
    {OP_READ, "read", read_f, 1, 0},
    {OP_RENAME, "rename", rename_f, 2, 1},
    {OP_RMDIR, "rmdir", rmdir_f, 1, 1},
    {OP_STAT, "stat", stat_f, 1, 0},
    {OP_TRUNCATE, "truncate", truncate_f, 2, 1},
    {OP_UNLINK, "unlink", unlink_f, 1, 1},
    {OP_WRITE, "write", write_f, 4, 1},
  #if REDCONF_CHECKER == 1
    {OP_CHECK, "check", check_f, 1, 1},
  #endif
}, *ops_end;

static flist_t flist[FT_nft] = {
    {0, 0, 'd', NULL},
    {0, 0, 'f', NULL},
    {0, 0, 'l', NULL},
    {0, 0, 'c', NULL},
    {0, 0, 'r', NULL},
};

static int dcache[NDCACHE];
static opty_t *freq_table;
static int freq_table_size;
static char *homedir;
static int *ilist;
static int ilistlen;
static off64_t maxfsize;
static int namerand;
static int nameseq;
static int nops;
static int operations = 1;
static int procid;
static int rtpct;
static unsigned long seed = 0;
static ino_t top_ino;
static int verbose = 0;

static int delete_tree(const char *path);
static void add_to_flist(int fd, int it, int parent);
static void append_pathname(pathname_t *name, const char *str);
static void check_cwd(void);
static int creat_path(pathname_t *name, mode_t mode);
static void dcache_enter(int dirid, int slot);
static void dcache_init(void);
static fent_t *dcache_lookup(int dirid);
static void dcache_purge(int dirid);
static void del_from_flist(int ft, int slot);
static void doproc(void);
static void fent_to_name(pathname_t *name, flist_t *flp, fent_t *fep);
static void fix_parent(int oldid, int newid);
static void free_pathname(pathname_t *name);
static int generate_fname(fent_t *fep, int ft, pathname_t *name, int *idp, int *v);
static int get_fname(int which, long r, pathname_t *name, flist_t **flpp, fent_t **fepp, int *v);
static void init_pathname(pathname_t *name);
static int link_path(pathname_t *name1, pathname_t *name2);
static int lstat64_path(pathname_t *name, REDSTAT *sbuf);
static void make_freq_table(void);
static int mkdir_path(pathname_t *name, mode_t mode);
static void namerandpad(int id, char *buf, int len);
static int open_path(pathname_t *name, int oflag);
static DIR *opendir_path(pathname_t *name);
static int rename_path(pathname_t *name1, pathname_t *name2);
static int rmdir_path(pathname_t *name);
static void separate_pathname(pathname_t *name, char *buf, pathname_t *newname);
static int stat64_path(pathname_t *name, REDSTAT *sbuf);
static int truncate64_path(pathname_t *name, off64_t length);
static int unlink_path(pathname_t *name);
static void usage(const char *progname);


/** @brief Parse parameters for fsstress.

    @param argc         The number of arguments from main().
    @param argv         The vector of arguments from main().
    @param pParam       Populated with the fsstress parameters.
    @param pbVolNum     If non-NULL, populated with the volume number.
    @param ppszDevice   If non-NULL, populated with the device name argument or
                        NULL if no device argument is provided.

    @return The result of parsing the parameters.
*/
PARAMSTATUS FsstressParseParams(
    int             argc,
    char           *argv[],
    FSSTRESSPARAM  *pParam,
    uint8_t        *pbVolNum,
    const char    **ppszDevice)
{
    int             c;
    uint8_t         bVolNum;
    const REDOPTION aLongopts[] =
    {
        { "no-cleanup", red_no_argument, NULL, 'c' },
        { "loops", red_required_argument, NULL, 'l' },
        { "nops", red_required_argument, NULL, 'n' },
        { "namepad", red_no_argument, NULL, 'r' },
        { "seed", red_required_argument, NULL, 's' },
        { "verbose", red_no_argument, NULL, 'v' },
        { "dev", red_required_argument, NULL, 'D' },
        { "help", red_no_argument, NULL, 'H' },
        { NULL }
    };

    /*  If run without parameters, treat as a help request.
    */
    if(argc <= 1)
    {
        goto Help;
    }

    /*  Assume no device argument to start with.
    */
    if(ppszDevice != NULL)
    {
        *ppszDevice = NULL;
    }

    /*  Set default parameters.
    */
    FsstressDefaultParams(pParam);

    while((c = RedGetoptLong(argc, argv, "cl:n:rs:vD:H", aLongopts, NULL)) != -1)
    {
        switch(c)
        {
            case 'c': /* --no-cleanup */
                pParam->fNoCleanup = true;
                break;
            case 'l': /* --loops */
                pParam->ulLoops = RedAtoI(red_optarg);
                break;
            case 'n': /* --nops */
                pParam->ulNops = RedAtoI(red_optarg);
                break;
            case 'r': /* --namepad */
                pParam->fNamePad = true;
                break;
            case 's': /* --seed */
                pParam->ulSeed = RedAtoI(red_optarg);
                break;
            case 'v': /* --verbose */
                pParam->fVerbose = true;
                break;
            case 'D': /* --dev */
                if(ppszDevice != NULL)
                {
                    *ppszDevice = red_optarg;
                }
                break;
            case 'H': /* --help */
                goto Help;
            case '?': /* Unknown or ambiguous option */
            case ':': /* Option missing required argument */
            default:
                goto BadOpt;
        }
    }

    /*  RedGetoptLong() has permuted argv to move all non-option arguments to
        the end.  We expect to find a volume identifier.
    */
    if(red_optind >= argc)
    {
        RedPrintf("Missing volume argument\n");
        goto BadOpt;
    }

    bVolNum = RedFindVolumeNumber(argv[red_optind]);
    if(bVolNum == REDCONF_VOLUME_COUNT)
    {
        RedPrintf("Error: \"%s\" is not a valid volume identifier.\n", argv[red_optind]);
        goto BadOpt;
    }

    if(pbVolNum != NULL)
    {
        *pbVolNum = bVolNum;
    }

    red_optind++; /* Move past volume parameter. */
    if(red_optind < argc)
    {
        int32_t ii;

        for(ii = red_optind; ii < argc; ii++)
        {
            RedPrintf("Error: Unexpected command-line argument \"%s\".\n", argv[ii]);
        }

        goto BadOpt;
    }

    return PARAMSTATUS_OK;

  BadOpt:

    RedPrintf("%s - invalid parameters\n", argv[0U]);
    usage(argv[0U]);
    return PARAMSTATUS_BAD;

  Help:

    usage(argv[0U]);
    return PARAMSTATUS_HELP;
}


/** @brief Set default fsstress parameters.

    @param pParam   Populated with the default fsstress parameters.
*/
void FsstressDefaultParams(
    FSSTRESSPARAM *pParam)
{
    RedMemSet(pParam, 0U, sizeof(*pParam));
    pParam->ulLoops = 1U;
    pParam->ulNops = 10000U;
}


/** @brief Start fsstress.

    @param pParam   fsstress parameters, either from FsstressParseParams() or
                    constructed programatically.

    @return Zero on success, otherwise nonzero.
*/
int FsstressStart(
    const FSSTRESSPARAM *pParam)
{
    char buf[10];
    int fd;
    int i;
    int cleanup;
    int loops;
    int loopcntr = 1;

    nops = sizeof(ops) / sizeof(ops[0]);
    ops_end = &ops[nops];

    /*  Copy the already-parsed parameters into the traditional variables.
    */
    cleanup = pParam->fNoCleanup ? 1 : 0;
    loops = pParam->ulLoops;
    operations = pParam->ulNops;
    namerand = pParam->fNamePad ? 1 : 0;
    seed = pParam->ulSeed;
    verbose = pParam->fVerbose ? 1 : 0;

    make_freq_table();

    while ((loopcntr <= loops) || (loops == 0)) {
        RedSNPrintf(buf, sizeof(buf), "fss%x", getpid());
        fd = creat(buf, 0666);
        maxfsize = (off64_t) MAXFSIZE;
        dcache_init();
        if (!seed) {
            seed = (unsigned long)RedOsClockGetTime();
            RedPrintf("seed = %ld\n", seed);
        }
        close(fd);
        unlink(buf);
        procid = 0;
        doproc();
        if (cleanup == 0) {
            delete_tree("/");
            for (i = 0; i < FT_nft; i++) {
                flist[i].nslots = 0;
                flist[i].nfiles = 0;
                free(flist[i].fents);
                flist[i].fents = NULL;
            }
        }
        loopcntr++;
    }
    return 0;
}

static int delete_tree(const char *path)
{
    REDSTAT sb;
    DIR *dp;
    REDDIRENT *dep;
    char *childpath;
    size_t len;
    int e;

    e = stat(path, &sb);
    if (e)
        return errno;

    if (!S_ISDIR(sb.st_mode))
        return unlink(path) ? errno : 0;

    dp = opendir(path);
    if (dp == NULL)
        return errno;

    while((dep = readdir(dp)) != NULL) {
        len = strlen(path) + 1 + strlen(dep->d_name) + 1;
        childpath = malloc(len);

        strcpy(childpath, path);
        if (childpath[strlen(childpath) - 1] != '/')
            strcat(childpath, "/");
        strcat(childpath, dep->d_name);

        e = delete_tree(childpath);

        free(childpath);

        if (e)
            break;
    }

    if (e == 0 && strcmp(path, "/") != 0) {
        e = rmdir(path) ? errno : 0;
    }
    closedir(dp);
    return e;
}

static void add_to_flist(int ft, int id, int parent)
{
    fent_t *fep;
    flist_t *ftp;

    ftp = &flist[ft];
    if (ftp->nfiles == ftp->nslots) {
        ftp->nslots += FLIST_SLOT_INCR;
        ftp->fents = realloc(ftp->fents, ftp->nslots * sizeof(fent_t));
    }
    fep = &ftp->fents[ftp->nfiles++];
    fep->id = id;
    fep->parent = parent;
}

static void append_pathname(pathname_t *name, const char *str)
{
    int len;

    len = strlen(str);
#ifdef DEBUG
    if (len && *str == '/' && name->len == 0) {
        RedPrintf("fsstress: append_pathname failure\n");
        chdir(homedir);
        abort();

    }
#endif
    name->path = realloc(name->path, name->len + 1 + len);
    strcpy(&name->path[name->len], str);
    name->len += len;
}

static void check_cwd(void)
{
#ifdef DEBUG
    REDSTAT statbuf;

    if (stat64(".", &statbuf) == 0 && statbuf.st_ino == top_ino)
        return;
    chdir(homedir);
    RedPrintf("fsstress: check_cwd failure\n");
    abort();

#endif
}

static int creat_path(pathname_t *name, mode_t mode)
{
    char buf[MAXNAMELEN];
    pathname_t newname;
    int rval;

    rval = creat(name->path, mode);
    if (rval >= 0 || errno != RED_ENAMETOOLONG)
        return rval;
    separate_pathname(name, buf, &newname);
    if (chdir(buf) == 0) {
        rval = creat_path(&newname, mode);
        chdir("..");
    }
    free_pathname(&newname);
    return rval;
}

static void dcache_enter(int dirid, int slot)
{
    dcache[dirid % NDCACHE] = slot;
}

static void dcache_init(void)
{
    int i;

    for (i = 0; i < NDCACHE; i++)
        dcache[i] = -1;
}

static fent_t *dcache_lookup(int dirid)
{
    fent_t *fep;
    int i;

    i = dcache[dirid % NDCACHE];
    if (i >= 0 && (fep = &flist[FT_DIR].fents[i])->id == dirid)
        return fep;
    return NULL;
}

static void dcache_purge(int dirid)
{
    int *dcp;

    dcp = &dcache[dirid % NDCACHE];
    if (*dcp >= 0 && flist[FT_DIR].fents[*dcp].id == dirid)
        *dcp = -1;
}

static void del_from_flist(int ft, int slot)
{
    flist_t *ftp;

    ftp = &flist[ft];
    if (ft == FT_DIR)
        dcache_purge(ftp->fents[slot].id);
    if (slot != ftp->nfiles - 1) {
        if (ft == FT_DIR)
            dcache_purge(ftp->fents[ftp->nfiles - 1].id);
        ftp->fents[slot] = ftp->fents[--ftp->nfiles];
    } else
        ftp->nfiles--;
}

static fent_t *dirid_to_fent(int dirid)
{
    fent_t *efep;
    fent_t *fep;
    flist_t *flp;

    if ((fep = dcache_lookup(dirid)))
        return fep;
    flp = &flist[FT_DIR];
    for (fep = flp->fents, efep = &fep[flp->nfiles]; fep < efep; fep++) {
        if (fep->id == dirid) {
            dcache_enter(dirid, (int)(fep - flp->fents));
            return fep;
        }
    }
    return NULL;
}

static void doproc(void)
{
    REDSTAT statbuf;
    char buf[10];
    int opno;
    opdesc_t *p;

    RedSNPrintf(buf, sizeof(buf), "p%x", procid);
    (void)mkdir(buf);
    if (chdir(buf) < 0 || stat64(".", &statbuf) < 0) {
        perror(buf);
        _exit(1);
    }
    top_ino = statbuf.st_ino;
    homedir = getcwd(NULL, 0);
    seed += procid;
    srandom(seed);
    if (namerand)
        namerand = random();
    for (opno = 0; opno < operations; opno++) {
        p = &ops[freq_table[random() % freq_table_size]];
        if ((unsigned long)p->func < 4096)
            abort();

        p->func(opno, random());
    }
    free(homedir);
}

static void fent_to_name(pathname_t *name, flist_t *flp, fent_t *fep)
{
    char buf[MAXNAMELEN];
    int i;
    fent_t *pfep;

    if (fep == NULL)
        return;
    if (fep->parent != -1) {
        pfep = dirid_to_fent(fep->parent);
        fent_to_name(name, &flist[FT_DIR], pfep);
        append_pathname(name, "/");
    }
    i = RedSNPrintf(buf, sizeof(buf), "%c%x", flp->tag, fep->id);
    namerandpad(fep->id, buf, i);
    append_pathname(name, buf);
}

static void fix_parent(int oldid, int newid)
{
    fent_t *fep;
    flist_t *flp;
    int i;
    int j;

    for (i = 0, flp = flist; i < FT_nft; i++, flp++) {
        for (j = 0, fep = flp->fents; j < flp->nfiles; j++, fep++) {
            if (fep->parent == oldid)
                fep->parent = newid;
        }
    }
}

static void free_pathname(pathname_t *name)
{
    if (name->path) {
        free(name->path);
        name->path = NULL;
        name->len = 0;
    }
}

static int generate_fname(fent_t *fep, int ft, pathname_t *name, int *idp, int *v)
{
    char buf[MAXNAMELEN];
    flist_t *flp;
    int id;
    int j;
    int len;

    flp = &flist[ft];
    len = RedSNPrintf(buf, sizeof(buf), "%c%x", flp->tag, id = nameseq++);
    namerandpad(id, buf, len);
    if (fep) {
        fent_to_name(name, &flist[FT_DIR], fep);
        append_pathname(name, "/");
    }
    append_pathname(name, buf);
    *idp = id;
    *v = verbose;
    for (j = 0; !*v && j < ilistlen; j++) {
        if (ilist[j] == id) {
            *v = 1;
            break;
        }
    }
    return 1;
}

static int
get_fname(int which, long r, pathname_t *name, flist_t **flpp, fent_t **fepp, int *v)
{
    int c;
    fent_t *fep;
    flist_t *flp;
    int i;
    int j;
    int x;

    for (i = 0, c = 0, flp = flist; i < FT_nft; i++, flp++) {
        if (which & (1 << i))
            c += flp->nfiles;
    }
    if (c == 0) {
        if (flpp)
            *flpp = NULL;
        if (fepp)
            *fepp = NULL;
        *v = verbose;
        return 0;
    }
    x = (int)(r % c);
    for (i = 0, c = 0, flp = flist; i < FT_nft; i++, flp++) {
        if (which & (1 << i)) {
            if (x < c + flp->nfiles) {
                fep = &flp->fents[x - c];
                if (name)
                    fent_to_name(name, flp, fep);
                if (flpp)
                    *flpp = flp;
                if (fepp)
                    *fepp = fep;
                *v = verbose;
                for (j = 0; !*v && j < ilistlen; j++) {
                    if (ilist[j] == fep->id) {
                        *v = 1;
                        break;
                    }
                }
                return 1;
            }
            c += flp->nfiles;
        }
    }
#ifdef DEBUG
    RedPrintf("fsstress: get_fname failure\n");
    abort();
#endif
    return -1;

}

static void init_pathname(pathname_t *name)
{
    name->len = 0;
    name->path = NULL;
}

static int link_path(pathname_t *name1, pathname_t *name2)
{
    char buf1[MAXNAMELEN];
    char buf2[MAXNAMELEN];
    int down1;
    pathname_t newname1;
    pathname_t newname2;
    int rval;

    rval = link(name1->path, name2->path);
    if (rval >= 0 || errno != RED_ENAMETOOLONG)
        return rval;
    separate_pathname(name1, buf1, &newname1);
    separate_pathname(name2, buf2, &newname2);
    if (strcmp(buf1, buf2) == 0) {
        if (chdir(buf1) == 0) {
            rval = link_path(&newname1, &newname2);
            chdir("..");
        }
    } else {
        if (strcmp(buf1, "..") == 0)
            down1 = 0;
        else if (strcmp(buf2, "..") == 0)
            down1 = 1;
        else if (strlen(buf1) == 0)
            down1 = 0;
        else if (strlen(buf2) == 0)
            down1 = 1;
        else
            down1 = MAX(newname1.len, 3 + name2->len) <=
                MAX(3 + name1->len, newname2.len);
        if (down1) {
            free_pathname(&newname2);
            append_pathname(&newname2, "../");
            append_pathname(&newname2, name2->path);
            if (chdir(buf1) == 0) {
                rval = link_path(&newname1, &newname2);
                chdir("..");
            }
        } else {
            free_pathname(&newname1);
            append_pathname(&newname1, "../");
            append_pathname(&newname1, name1->path);
            if (chdir(buf2) == 0) {
                rval = link_path(&newname1, &newname2);
                chdir("..");
            }
        }
    }
    free_pathname(&newname1);
    free_pathname(&newname2);
    return rval;
}

static int lstat64_path(pathname_t *name, REDSTAT *sbuf)
{
    char buf[MAXNAMELEN];
    pathname_t newname;
    int rval;

    rval = lstat64(name->path, sbuf);
    if (rval >= 0 || errno != RED_ENAMETOOLONG)
        return rval;
    separate_pathname(name, buf, &newname);
    if (chdir(buf) == 0) {
        rval = lstat64_path(&newname, sbuf);
        chdir("..");
    }
    free_pathname(&newname);
    return rval;
}

static void make_freq_table(void)
{
    int f;
    int i;
    opdesc_t *p;

    for (p = ops, f = 0; p < ops_end; p++)
        f += p->freq;
    freq_table = malloc(f * sizeof(*freq_table));
    freq_table_size = f;
    for (p = ops, i = 0; p < ops_end; p++) {
        for (f = 0; f < p->freq; f++, i++)
            freq_table[i] = p->op;
    }
}

static int mkdir_path(pathname_t *name, mode_t mode)
{
    char buf[MAXNAMELEN];
    pathname_t newname;
    int rval;

    rval = mkdir(name->path);
    if (rval >= 0 || errno != RED_ENAMETOOLONG)
        return rval;
    separate_pathname(name, buf, &newname);
    if (chdir(buf) == 0) {
        rval = mkdir_path(&newname, mode);
        chdir("..");
    }
    free_pathname(&newname);
    return rval;
}

static void namerandpad(int id, char *buf, int len)
{
    int bucket;
    static int buckets[8] = {0};
    static int bucket_count = 0;
    int bucket_value;
    int i;
    int padlen;
    int padmod;

    if (namerand == 0)
        return;

    /*  buckets[] used to be a statically initialized array with the following
        initializer: { 2, 4, 8, 16, 32, 64, 128, MAXNAMELEN - 1 }

        The problem is that with Reliance Edge, the maximum name length might be
        less than 128.  So the below code populates buckets[] in a similar
        fashion but avoids name lengths longer than the maximum.  For example,
        if the max name is 20, the resulting array is { 2, 4, 8, 16, 20 }.
    */
    if (!bucket_count) {
        bucket_count = sizeof(buckets) / sizeof(buckets[0]);
        bucket_value = 2;
        for (i = 0; i < bucket_count; i++) {
            if (bucket_value > 128 || bucket_value >= (int)MAXNAMELEN - 1)
                break;
            buckets[i] = bucket_value;
            bucket_value *= 2;
        }
        if (i < bucket_count) {
            buckets[i] = MAXNAMELEN - 1;
            i++;
        }
        bucket_count = i;
    }

    bucket = (id ^ namerand) % bucket_count;
    padmod = buckets[bucket] + 1 - len;
    if (padmod <= 0)
        return;
    padlen = (id ^ namerand) % padmod;
    if (padlen) {
        memset(&buf[len], 'X', padlen);
        buf[len + padlen] = '\0';
    }
}

static int open_path(pathname_t *name, int oflag)
{
    char buf[MAXNAMELEN];
    pathname_t newname;
    int rval;

    rval = open(name->path, oflag);
    if (rval >= 0 || errno != RED_ENAMETOOLONG)
        return rval;
    separate_pathname(name, buf, &newname);
    if (chdir(buf) == 0) {
        rval = open_path(&newname, oflag);
        chdir("..");
    }
    free_pathname(&newname);
    return rval;
}

static DIR *opendir_path(pathname_t *name)
{
    char buf[MAXNAMELEN];
    pathname_t newname;
    DIR *rval;

    rval = opendir(name->path);
    if (rval || errno != RED_ENAMETOOLONG)
        return rval;
    separate_pathname(name, buf, &newname);
    if (chdir(buf) == 0) {
        rval = opendir_path(&newname);
        chdir("..");
    }
    free_pathname(&newname);
    return rval;
}

static int rename_path(pathname_t *name1, pathname_t *name2)
{
    char buf1[MAXNAMELEN];
    char buf2[MAXNAMELEN];
    int down1;
    pathname_t newname1;
    pathname_t newname2;
    int rval;

    rval = rename(name1->path, name2->path);
    if (rval >= 0 || errno != RED_ENAMETOOLONG)
        return rval;
    separate_pathname(name1, buf1, &newname1);
    separate_pathname(name2, buf2, &newname2);
    if (strcmp(buf1, buf2) == 0) {
        if (chdir(buf1) == 0) {
            rval = rename_path(&newname1, &newname2);
            chdir("..");
        }
    } else {
        if (strcmp(buf1, "..") == 0)
            down1 = 0;
        else if (strcmp(buf2, "..") == 0)
            down1 = 1;
        else if (strlen(buf1) == 0)
            down1 = 0;
        else if (strlen(buf2) == 0)
            down1 = 1;
        else
            down1 = MAX(newname1.len, 3 + name2->len) <=
                MAX(3 + name1->len, newname2.len);
        if (down1) {
            free_pathname(&newname2);
            append_pathname(&newname2, "../");
            append_pathname(&newname2, name2->path);
            if (chdir(buf1) == 0) {
                rval = rename_path(&newname1, &newname2);
                chdir("..");
            }
        } else {
            free_pathname(&newname1);
            append_pathname(&newname1, "../");
            append_pathname(&newname1, name1->path);
            if (chdir(buf2) == 0) {
                rval = rename_path(&newname1, &newname2);
                chdir("..");
            }
        }
    }
    free_pathname(&newname1);
    free_pathname(&newname2);
    return rval;
}

static int rmdir_path(pathname_t *name)
{
    char buf[MAXNAMELEN];
    pathname_t newname;
    int rval;

    rval = rmdir(name->path);
    if (rval >= 0 || errno != RED_ENAMETOOLONG)
        return rval;
    separate_pathname(name, buf, &newname);
    if (chdir(buf) == 0) {
        rval = rmdir_path(&newname);
        chdir("..");
    }
    free_pathname(&newname);
    return rval;
}

static void separate_pathname(pathname_t *name, char *buf, pathname_t *newname)
{
    char *slash;

    init_pathname(newname);
    slash = strchr(name->path, '/');
    if (slash == NULL) {
        buf[0] = '\0';
        return;
    }
    *slash = '\0';
    strcpy(buf, name->path);
    *slash = '/';
    append_pathname(newname, slash + 1);
}

static int stat64_path(pathname_t *name, REDSTAT *sbuf)
{
    char buf[MAXNAMELEN];
    pathname_t newname;
    int rval;

    rval = stat64(name->path, sbuf);
    if (rval >= 0 || errno != RED_ENAMETOOLONG)
        return rval;
    separate_pathname(name, buf, &newname);
    if (chdir(buf) == 0) {
        rval = stat64_path(&newname, sbuf);
        chdir("..");
    }
    free_pathname(&newname);
    return rval;
}

static int truncate64_path(pathname_t *name, off64_t length)
{
    char buf[MAXNAMELEN];
    pathname_t newname;
    int rval;

    rval = truncate64(name->path, length);
    if (rval >= 0 || errno != RED_ENAMETOOLONG)
        return rval;
    separate_pathname(name, buf, &newname);
    if (chdir(buf) == 0) {
        rval = truncate64_path(&newname, length);
        chdir("..");
    }
    free_pathname(&newname);
    return rval;
}

static int unlink_path(pathname_t *name)
{
    char buf[MAXNAMELEN];
    pathname_t newname;
    int rval;

    rval = unlink(name->path);
    if (rval >= 0 || errno != RED_ENAMETOOLONG)
        return rval;
    separate_pathname(name, buf, &newname);
    if (chdir(buf) == 0) {
        rval = unlink_path(&newname);
        chdir("..");
    }
    free_pathname(&newname);
    return rval;
}

static void usage(const char *progname)
{
    RedPrintf("usage: %s VolumeID [Options]\n", progname);
    RedPrintf("File system stress test.\n\n");
    RedPrintf("Where:\n");
    RedPrintf("  VolumeID\n");
    RedPrintf("      A volume number (e.g., 2) or a volume path prefix (e.g., VOL1: or /data)\n");
    RedPrintf("      of the volume to test.\n");
    RedPrintf("And 'Options' are any of the following:\n");
    RedPrintf("  --no-cleanup, -c\n");
    RedPrintf("      Specifies not to remove files (cleanup) after execution\n");
    RedPrintf("  --loops=count, -l count\n");
    RedPrintf("      Specifies the number of times the entire test should loop.  Use 0 for\n");
    RedPrintf("      infinite.  Default 1.\n");
    RedPrintf("  --nops=count, -n count\n");
    RedPrintf("      Specifies the number of operations to run (default 10000).\n");
    RedPrintf("  --namepad, -r\n");
    RedPrintf("      Specifies to use random name padding (resulting in longer names).\n");
    RedPrintf("  --seed=value, -s value\n");
    RedPrintf("      Specifies the seed for the random number generator (default timestamp).\n");
    RedPrintf("  --verbose, -v\n");
    RedPrintf("      Specifies verbose mode (without this, test is very quiet).\n");
    RedPrintf("  --dev=devname, -D devname\n");
    RedPrintf("      Specifies the device name.  This is typically only meaningful when\n");
    RedPrintf("      running the test on a host machine.  This can be \"ram\" to test on a RAM\n");
    RedPrintf("      disk, the path and name of a file disk (e.g., red.bin); or an OS-specific\n");
    RedPrintf("      reference to a device (on Windows, a drive letter like G: or a device name\n");
    RedPrintf("      like \\\\.\\PhysicalDrive7).\n");
    RedPrintf("  --help, -H\n");
    RedPrintf("      Prints this usage text and exits.\n\n");
    RedPrintf("Warning: This test will format the volume -- destroying all existing data.\n\n");
}

static void creat_f(int opno, long r)
{
    int e;
    int e1;
    pathname_t f;
    int fd;
    fent_t *fep;
    int id;
    int parid;
    int type;
    int v;
    int v1;
    int esz = 0;

    if (!get_fname(FT_DIRm, r, NULL, NULL, &fep, &v1))
        parid = -1;
    else
        parid = fep->id;
    init_pathname(&f);
    type = rtpct ? ((int)(random() % 100) > rtpct ? FT_REG : FT_RTF) : FT_REG;
    e = generate_fname(fep, type, &f, &id, &v);
    v |= v1;
    if (!e) {
        if (v) {
            fent_to_name(&f, &flist[FT_DIR], fep);
            RedPrintf("%d/%d: creat - no filename from %s\n",
                   procid, opno, f.path);
        }
        free_pathname(&f);
        return;
    }
    fd = creat_path(&f, 0666);
    e = fd < 0 ? errno : 0;
    e1 = 0;
    check_cwd();
    esz = 0;
    if (fd >= 0) {
        add_to_flist(type, id, parid);
        close(fd);
    }
    if (v)
        RedPrintf("%d/%d: creat %s x:%d %d %d\n", procid, opno, f.path,
               esz, e, e1);
    free_pathname(&f);
}

static void fdatasync_f(int opno, long r)
{
    int e;
    pathname_t f;
    int fd;
    int v;

    init_pathname(&f);
    if (!get_fname(FT_REGFILE, r, &f, NULL, NULL, &v)) {
        if (v)
            RedPrintf("%d/%d: fdatasync - no filename\n",
                   procid, opno);
        free_pathname(&f);
        return;
    }
    fd = open_path(&f, O_WRONLY);
    e = fd < 0 ? errno : 0;
    check_cwd();
    if (fd < 0) {
        if (v)
            RedPrintf("%d/%d: fdatasync - open %s failed %d\n",
                   procid, opno, f.path, e);
        free_pathname(&f);
        return;
    }
    e = fdatasync(fd) < 0 ? errno : 0;
    if (v)
        RedPrintf("%d/%d: fdatasync %s %d\n", procid, opno, f.path, e);
    free_pathname(&f);
    close(fd);
}

static void fsync_f(int opno, long r)
{
    int e;
    pathname_t f;
    int fd;
    int v;

    init_pathname(&f);
    if (!get_fname(FT_REGFILE, r, &f, NULL, NULL, &v)) {
        if (v)
            RedPrintf("%d/%d: fsync - no filename\n", procid, opno);
        free_pathname(&f);
        return;
    }
    fd = open_path(&f, O_WRONLY);
    e = fd < 0 ? errno : 0;
    check_cwd();
    if (fd < 0) {
        if (v)
            RedPrintf("%d/%d: fsync - open %s failed %d\n",
                   procid, opno, f.path, e);
        free_pathname(&f);
        return;
    }
    e = fsync(fd) < 0 ? errno : 0;
    if (v)
        RedPrintf("%d/%d: fsync %s %d\n", procid, opno, f.path, e);
    free_pathname(&f);
    close(fd);
}

static void getdents_f(int opno, long r)
{
    DIR *dir;
    pathname_t f;
    int v;

    init_pathname(&f);
    if (!get_fname(FT_DIRm, r, &f, NULL, NULL, &v))
        append_pathname(&f, ".");
    dir = opendir_path(&f);
    check_cwd();
    if (dir == NULL) {
        if (v)
            RedPrintf("%d/%d: getdents - can't open %s\n",
                   procid, opno, f.path);
        free_pathname(&f);
        return;
    }
    while (readdir64(dir) != NULL)
        continue;
    if (v)
        RedPrintf("%d/%d: getdents %s 0\n", procid, opno, f.path);
    free_pathname(&f);
    closedir(dir);
}

static void link_f(int opno, long r)
{
    int e;
    pathname_t f;
    fent_t *fep;
    flist_t *flp;
    int id;
    pathname_t l;
    int parid;
    int v;
    int v1;

    init_pathname(&f);
    if (!get_fname(FT_NOTDIR, r, &f, &flp, NULL, &v1)) {
        if (v1)
            RedPrintf("%d/%d: link - no file\n", procid, opno);
        free_pathname(&f);
        return;
    }
    if (!get_fname(FT_DIRm, random(), NULL, NULL, &fep, &v))
        parid = -1;
    else
        parid = fep->id;
    v |= v1;
    init_pathname(&l);
    e = generate_fname(fep, (int)(flp - flist), &l, &id, &v1);
    v |= v1;
    if (!e) {
        if (v) {
            fent_to_name(&l, &flist[FT_DIR], fep);
            RedPrintf("%d/%d: link - no filename from %s\n",
                   procid, opno, l.path);
        }
        free_pathname(&l);
        free_pathname(&f);
        return;
    }
    e = link_path(&f, &l) < 0 ? errno : 0;
    check_cwd();
    if (e == 0)
        add_to_flist((int)(flp - flist), id, parid);
    if (v)
        RedPrintf("%d/%d: link %s %s %d\n", procid, opno, f.path, l.path,
               e);
    free_pathname(&l);
    free_pathname(&f);
}

static void mkdir_f(int opno, long r)
{
    int e;
    pathname_t f;
    fent_t *fep;
    int id;
    int parid;
    int v;
    int v1;

    if (!get_fname(FT_DIRm, r, NULL, NULL, &fep, &v))
        parid = -1;
    else
        parid = fep->id;
    init_pathname(&f);
    e = generate_fname(fep, FT_DIR, &f, &id, &v1);
    v |= v1;
    if (!e) {
        if (v) {
            fent_to_name(&f, &flist[FT_DIR], fep);
            RedPrintf("%d/%d: mkdir - no filename from %s\n",
                   procid, opno, f.path);
        }
        free_pathname(&f);
        return;
    }
    e = mkdir_path(&f, 0777) < 0 ? errno : 0;
    check_cwd();
    if (e == 0)
        add_to_flist(FT_DIR, id, parid);
    if (v)
        RedPrintf("%d/%d: mkdir %s %d\n", procid, opno, f.path, e);
    free_pathname(&f);
}

static void read_f(int opno, long r)
{
    char *buf;
    int e;
    pathname_t f;
    int fd;
    uint32_t len;
    __int64_t lr;
    off64_t off;
    REDSTAT stb;
    int v;

    init_pathname(&f);
    if (!get_fname(FT_REGFILE, r, &f, NULL, NULL, &v)) {
        if (v)
            RedPrintf("%d/%d: read - no filename\n", procid, opno);
        free_pathname(&f);
        return;
    }
    fd = open_path(&f, O_RDONLY);
    e = fd < 0 ? errno : 0;
    check_cwd();
    if (fd < 0) {
        if (v)
            RedPrintf("%d/%d: read - open %s failed %d\n",
                   procid, opno, f.path, e);
        free_pathname(&f);
        return;
    }
    if (fstat64(fd, &stb) < 0) {
        if (v)
            RedPrintf("%d/%d: read - fstat64 %s failed %d\n",
                   procid, opno, f.path, errno);
        free_pathname(&f);
        close(fd);
        return;
    }
    if (stb.st_size == 0) {
        if (v)
            RedPrintf("%d/%d: read - %s zero size\n", procid, opno,
                   f.path);
        free_pathname(&f);
        close(fd);
        return;
    }
    lr = ((__int64_t) random() << 32) + random();
    off = (off64_t) (lr % stb.st_size);
    lseek64(fd, off, SEEK_SET);
    len = (random() % (getpagesize() * 4)) + 1;
    buf = malloc(len);
    e = read(fd, buf, len) < 0 ? errno : 0;
    free(buf);
    if (v)
        RedPrintf("%d/%d: read %s [%lld,%ld] %d\n",
               procid, opno, f.path, (long long)off, (long int)len, e);
    free_pathname(&f);
    close(fd);
}

static void rename_f(int opno, long r)
{
    fent_t *dfep;
    int e;
    pathname_t f;
    fent_t *fep;
    flist_t *flp;
    int id;
    pathname_t newf;
    int oldid;
    int parid;
    int v;
    int v1;

    init_pathname(&f);
    if (!get_fname(FT_ANYm, r, &f, &flp, &fep, &v1)) {
        if (v1)
            RedPrintf("%d/%d: rename - no filename\n", procid, opno);
        free_pathname(&f);
        return;
    }
    if (!get_fname(FT_DIRm, random(), NULL, NULL, &dfep, &v))
        parid = -1;
    else
        parid = dfep->id;
    v |= v1;
    init_pathname(&newf);
    e = generate_fname(dfep, (int)(flp - flist), &newf, &id, &v1);
    v |= v1;
    if (!e) {
        if (v) {
            fent_to_name(&f, &flist[FT_DIR], dfep);
            RedPrintf("%d/%d: rename - no filename from %s\n",
                   procid, opno, f.path);
        }
        free_pathname(&newf);
        free_pathname(&f);
        return;
    }
    e = rename_path(&f, &newf) < 0 ? errno : 0;
    check_cwd();
    if (e == 0) {
        if (flp - flist == FT_DIR) {
            oldid = fep->id;
            fix_parent(oldid, id);
        }
        del_from_flist((int)(flp - flist), (int)(fep - flp->fents));
        add_to_flist((int)(flp - flist), id, parid);
    }
    if (v)
        RedPrintf("%d/%d: rename %s to %s %d\n", procid, opno, f.path,
               newf.path, e);
    free_pathname(&newf);
    free_pathname(&f);
}

static void rmdir_f(int opno, long r)
{
    int e;
    pathname_t f;
    fent_t *fep;
    int v;

    init_pathname(&f);
    if (!get_fname(FT_DIRm, r, &f, NULL, &fep, &v)) {
        if (v)
            RedPrintf("%d/%d: rmdir - no directory\n", procid, opno);
        free_pathname(&f);
        return;
    }
    e = rmdir_path(&f) < 0 ? errno : 0;
    check_cwd();
    if (e == 0)
        del_from_flist(FT_DIR, (int)(fep - flist[FT_DIR].fents));
    if (v)
        RedPrintf("%d/%d: rmdir %s %d\n", procid, opno, f.path, e);
    free_pathname(&f);
}

static void stat_f(int opno, long r)
{
    int e;
    pathname_t f;
    REDSTAT stb;
    int v;

    init_pathname(&f);
    if (!get_fname(FT_ANYm, r, &f, NULL, NULL, &v)) {
        if (v)
            RedPrintf("%d/%d: stat - no entries\n", procid, opno);
        free_pathname(&f);
        return;
    }
    e = lstat64_path(&f, &stb) < 0 ? errno : 0;
    check_cwd();
    if (v)
        RedPrintf("%d/%d: stat %s %d\n", procid, opno, f.path, e);
    free_pathname(&f);
}

static void truncate_f(int opno, long r)
{
    int e;
    pathname_t f;
    __int64_t lr;
    off64_t off;
    REDSTAT stb;
    int v;

    init_pathname(&f);
    if (!get_fname(FT_REGFILE, r, &f, NULL, NULL, &v)) {
        if (v)
            RedPrintf("%d/%d: truncate - no filename\n", procid, opno);
        free_pathname(&f);
        return;
    }
    e = stat64_path(&f, &stb) < 0 ? errno : 0;
    check_cwd();
    if (e > 0) {
        if (v)
            RedPrintf("%d/%d: truncate - stat64 %s failed %d\n",
                   procid, opno, f.path, e);
        free_pathname(&f);
        return;
    }
    lr = ((__int64_t) random() << 32) + random();
    off = lr % MIN(stb.st_size + (1024 * 1024), MAXFSIZE);
    off %= maxfsize;
    e = truncate64_path(&f, off) < 0 ? errno : 0;
    check_cwd();
    if (v)
        RedPrintf("%d/%d: truncate %s %lld %d\n", procid, opno, f.path,
               (long long)off, e);
    free_pathname(&f);
}

static void unlink_f(int opno, long r)
{
    int e;
    pathname_t f;
    fent_t *fep;
    flist_t *flp;
    int v;

    init_pathname(&f);
    if (!get_fname(FT_NOTDIR, r, &f, &flp, &fep, &v)) {
        if (v)
            RedPrintf("%d/%d: unlink - no file\n", procid, opno);
        free_pathname(&f);
        return;
    }
    e = unlink_path(&f) < 0 ? errno : 0;
    check_cwd();
    if (e == 0)
        del_from_flist((int)(flp - flist), (int)(fep - flp->fents));
    if (v)
        RedPrintf("%d/%d: unlink %s %d\n", procid, opno, f.path, e);
    free_pathname(&f);
}

static void write_f(int opno, long r)
{
    char *buf;
    int e;
    pathname_t f;
    int fd;
    uint32_t len;
    __int64_t lr;
    off64_t off;
    REDSTAT stb;
    int v;

    init_pathname(&f);
    if (!get_fname(FT_REGm, r, &f, NULL, NULL, &v)) {
        if (v)
            RedPrintf("%d/%d: write - no filename\n", procid, opno);
        free_pathname(&f);
        return;
    }
    fd = open_path(&f, O_WRONLY);
    e = fd < 0 ? errno : 0;
    check_cwd();
    if (fd < 0) {
        if (v)
            RedPrintf("%d/%d: write - open %s failed %d\n",
                   procid, opno, f.path, e);
        free_pathname(&f);
        return;
    }
    if (fstat64(fd, &stb) < 0) {
        if (v)
            RedPrintf("%d/%d: write - fstat64 %s failed %d\n",
                   procid, opno, f.path, errno);
        free_pathname(&f);
        close(fd);
        return;
    }
    lr = ((__int64_t) random() << 32) + random();
    off = (off64_t) (lr % MIN(stb.st_size + (1024 * 1024), MAXFSIZE));
    off %= maxfsize;
    lseek64(fd, off, SEEK_SET);
    len = (random() % (getpagesize() * 4)) + 1;
    buf = malloc(len);
    memset(buf, nameseq & 0xff, len);
    e = write(fd, buf, len) < 0 ? errno : 0;
    free(buf);
    if (v)
        RedPrintf("%d/%d: write %s [%lld,%ld] %d\n",
               procid, opno, f.path, (long long)off, (long int)len, e);
    free_pathname(&f);
    close(fd);
}


#if REDCONF_CHECKER == 1
static void check_f(int opno, long r)
{
    int32_t ret;
    const char *pszVolume = gpRedVolConf->pszPathPrefix;

    (void)r;

    errno = 0;

    ret = red_transact(pszVolume);

    if(ret == 0)
    {
        ret = red_umount(pszVolume);

        if(ret == 0)
        {
            int32_t ret2;

            errno = -RedCoreVolCheck();
            if(errno != 0)
            {
                ret = -1;
            }

            ret2 = red_mount(pszVolume);

            if(ret == 0)
            {
                ret = ret2;
            }

            if(ret2 != 0)
            {
                exit(1);
            }
        }
    }

    if (verbose)
    {
        RedPrintf("%d/%d: check %s %d\n", procid, opno, pszVolume, errno);
    }
}
#endif


#endif /* FSSTRESS_SUPPORTED */

