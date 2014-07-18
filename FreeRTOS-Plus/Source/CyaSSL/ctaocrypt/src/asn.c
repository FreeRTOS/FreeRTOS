/* asn.c
 *
 * Copyright (C) 2006-2014 wolfSSL Inc.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <cyassl/ctaocrypt/settings.h>

#ifndef NO_ASN

#ifdef HAVE_RTP_SYS
    #include "os.h"           /* dc_rtc_api needs    */
    #include "dc_rtc_api.h"   /* to get current time */
#endif

#include <cyassl/ctaocrypt/integer.h>
#include <cyassl/ctaocrypt/asn.h>
#include <cyassl/ctaocrypt/coding.h>
#include <cyassl/ctaocrypt/md2.h>
#include <cyassl/ctaocrypt/hmac.h>
#include <cyassl/ctaocrypt/error-crypt.h>
#include <cyassl/ctaocrypt/pwdbased.h>
#include <cyassl/ctaocrypt/des3.h>
#include <cyassl/ctaocrypt/logging.h>

#include <cyassl/ctaocrypt/random.h>


#ifndef NO_RC4
    #include <cyassl/ctaocrypt/arc4.h>
#endif

#ifdef HAVE_NTRU
    #include "ntru_crypto.h"
#endif

#ifdef HAVE_ECC
    #include <cyassl/ctaocrypt/ecc.h>
#endif

#ifdef CYASSL_DEBUG_ENCODING
    #ifdef FREESCALE_MQX
        #include <fio.h>
    #else
        #include <stdio.h>
    #endif
#endif

#ifdef _MSC_VER
    /* 4996 warning to use MS extensions e.g., strcpy_s instead of XSTRNCPY */
    #pragma warning(disable: 4996)
#endif


#ifndef TRUE
    #define TRUE  1
#endif
#ifndef FALSE
    #define FALSE 0
#endif


#ifdef HAVE_RTP_SYS 
    /* uses parital <time.h> structures */
    #define XTIME(tl)  (0)
    #define XGMTIME(c) my_gmtime((c))
    #define XVALIDATE_DATE(d, f, t) ValidateDate((d), (f), (t))
#elif defined(MICRIUM)
    #if (NET_SECURE_MGR_CFG_EN == DEF_ENABLED)
        #define XVALIDATE_DATE(d,f,t) NetSecure_ValidateDateHandler((d),(f),(t))
    #else
        #define XVALIDATE_DATE(d, f, t) (0)
    #endif
    #define NO_TIME_H
    /* since Micrium not defining XTIME or XGMTIME, CERT_GEN not available */
#elif defined(MICROCHIP_TCPIP_V5) || defined(MICROCHIP_TCPIP)
    #include <time.h>
    #define XTIME(t1) pic32_time((t1))
    #define XGMTIME(c) gmtime((c))
    #define XVALIDATE_DATE(d, f, t) ValidateDate((d), (f), (t))
#elif defined(FREESCALE_MQX)
    #include <time.h>
    #define XTIME(t1) mqx_time((t1))
    #define XGMTIME(c) gmtime((c))
    #define XVALIDATE_DATE(d, f, t) ValidateDate((d), (f), (t))
#elif defined(CYASSL_MDK_ARM)
    #if defined(CYASSL_MDK5)
        #include "cmsis_os.h"
    #else
        #include <rtl.h>
    #endif
    #undef RNG
    #include "cyassl_MDK_ARM.h"
    #undef RNG
    #define RNG CyaSSL_RNG /*for avoiding name conflict in "stm32f2xx.h" */
    #define XTIME(tl)  (0)
    #define XGMTIME(c) Cyassl_MDK_gmtime((c))
    #define XVALIDATE_DATE(d, f, t)  ValidateDate((d), (f), (t))
#elif defined(USER_TIME)
    /* user time, and gmtime compatible functions, there is a gmtime 
       implementation here that WINCE uses, so really just need some ticks
       since the EPOCH 
    */

    struct tm {
	int	tm_sec;		/* seconds after the minute [0-60] */
	int	tm_min;		/* minutes after the hour [0-59] */
	int	tm_hour;	/* hours since midnight [0-23] */
	int	tm_mday;	/* day of the month [1-31] */
	int	tm_mon;		/* months since January [0-11] */
	int	tm_year;	/* years since 1900 */
	int	tm_wday;	/* days since Sunday [0-6] */
	int	tm_yday;	/* days since January 1 [0-365] */
	int	tm_isdst;	/* Daylight Savings Time flag */
	long	tm_gmtoff;	/* offset from CUT in seconds */
	char	*tm_zone;	/* timezone abbreviation */
    };
    typedef long time_t;

    /* forward declaration */
    struct tm* gmtime(const time_t* timer);
    extern time_t XTIME(time_t * timer);

    #define XGMTIME(c) gmtime((c))
    #define XVALIDATE_DATE(d, f, t) ValidateDate((d), (f), (t))

    #ifdef STACK_TRAP
        /* for stack trap tracking, don't call os gmtime on OS X/linux,
           uses a lot of stack spce */
        extern time_t time(time_t * timer);
        #define XTIME(tl)  time((tl))
    #endif /* STACK_TRAP */

#else
    /* default */
    /* uses complete <time.h> facility */
    #include <time.h>
    #define XTIME(tl)  time((tl))
    #define XGMTIME(c) gmtime((c))
    #define XVALIDATE_DATE(d, f, t) ValidateDate((d), (f), (t))
#endif


#ifdef _WIN32_WCE
/* no time() or gmtime() even though in time.h header?? */

#include <windows.h>


time_t time(time_t* timer)
{
    SYSTEMTIME     sysTime;
    FILETIME       fTime;
    ULARGE_INTEGER intTime;
    time_t         localTime;

    if (timer == NULL)
        timer = &localTime;

    GetSystemTime(&sysTime);
    SystemTimeToFileTime(&sysTime, &fTime);
    
    XMEMCPY(&intTime, &fTime, sizeof(FILETIME));
    /* subtract EPOCH */
    intTime.QuadPart -= 0x19db1ded53e8000;
    /* to secs */
    intTime.QuadPart /= 10000000;
    *timer = (time_t)intTime.QuadPart;

    return *timer;
}

#endif /*  _WIN32_WCE */
#if defined( _WIN32_WCE ) || defined( USER_TIME )

struct tm* gmtime(const time_t* timer)
{
    #define YEAR0          1900
    #define EPOCH_YEAR     1970
    #define SECS_DAY       (24L * 60L * 60L)
    #define LEAPYEAR(year) (!((year) % 4) && (((year) % 100) || !((year) %400)))
    #define YEARSIZE(year) (LEAPYEAR(year) ? 366 : 365)

    static const int _ytab[2][12] =
    {
        {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31},
        {31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31}
    };

    static struct tm st_time;
    struct tm* ret = &st_time;
    time_t secs = *timer;
    unsigned long dayclock, dayno;
    int year = EPOCH_YEAR;

    dayclock = (unsigned long)secs % SECS_DAY;
    dayno    = (unsigned long)secs / SECS_DAY;

    ret->tm_sec  = (int) dayclock % 60;
    ret->tm_min  = (int)(dayclock % 3600) / 60;
    ret->tm_hour = (int) dayclock / 3600;
    ret->tm_wday = (int) (dayno + 4) % 7;        /* day 0 a Thursday */

    while(dayno >= (unsigned long)YEARSIZE(year)) {
        dayno -= YEARSIZE(year);
        year++;
    }

    ret->tm_year = year - YEAR0;
    ret->tm_yday = (int)dayno;
    ret->tm_mon  = 0;

    while(dayno >= (unsigned long)_ytab[LEAPYEAR(year)][ret->tm_mon]) {
        dayno -= _ytab[LEAPYEAR(year)][ret->tm_mon];
        ret->tm_mon++;
    }

    ret->tm_mday  = (int)++dayno;
    ret->tm_isdst = 0;

    return ret;
}

#endif /* _WIN32_WCE  || USER_TIME */


#ifdef HAVE_RTP_SYS  

#define YEAR0          1900

struct tm* my_gmtime(const time_t* timer)       /* has a gmtime() but hangs */
{
    static struct tm st_time;
    struct tm* ret = &st_time;

    DC_RTC_CALENDAR cal;
    dc_rtc_time_get(&cal, TRUE);

    ret->tm_year  = cal.year - YEAR0;       /* gm starts at 1900 */
    ret->tm_mon   = cal.month - 1;          /* gm starts at 0 */
    ret->tm_mday  = cal.day;
    ret->tm_hour  = cal.hour;
    ret->tm_min   = cal.minute;
    ret->tm_sec   = cal.second;

    return ret;
}

#endif /* HAVE_RTP_SYS */


#if defined(MICROCHIP_TCPIP_V5) || defined(MICROCHIP_TCPIP)

/*
 * time() is just a stub in Microchip libraries. We need our own
 * implementation. Use SNTP client to get seconds since epoch.
 */
time_t pic32_time(time_t* timer)
{
#ifdef MICROCHIP_TCPIP_V5
    DWORD sec = 0;
#else
    uint32_t sec = 0;
#endif
    time_t localTime;

    if (timer == NULL)
        timer = &localTime;

#ifdef MICROCHIP_MPLAB_HARMONY 
    sec = TCPIP_SNTP_UTCSecondsGet();
#else
    sec = SNTPGetUTCSeconds();
#endif
    *timer = (time_t) sec;

    return *timer;
}

#endif /* MICROCHIP_TCPIP */


#ifdef FREESCALE_MQX

time_t mqx_time(time_t* timer)
{
    time_t localTime;
    TIME_STRUCT time_s;

    if (timer == NULL)
        timer = &localTime;

    _time_get(&time_s);
    *timer = (time_t) time_s.SECONDS;

    return *timer;
}

#endif /* FREESCALE_MQX */


static INLINE word32 btoi(byte b)
{
    return b - 0x30;
}


/* two byte date/time, add to value */
static INLINE void GetTime(int* value, const byte* date, int* idx)
{
    int i = *idx;

    *value += btoi(date[i++]) * 10;
    *value += btoi(date[i++]);

    *idx = i;
}


#if defined(MICRIUM)

CPU_INT32S NetSecure_ValidateDateHandler(CPU_INT08U *date, CPU_INT08U format,
                                         CPU_INT08U dateType)
{
    CPU_BOOLEAN  rtn_code;
    CPU_INT32S   i;
    CPU_INT32S   val;    
    CPU_INT16U   year;
    CPU_INT08U   month;
    CPU_INT16U   day;
    CPU_INT08U   hour;
    CPU_INT08U   min;
    CPU_INT08U   sec;

    i    = 0;
    year = 0u;

    if (format == ASN_UTC_TIME) {
        if (btoi(date[0]) >= 5)
            year = 1900;
        else
            year = 2000;
    }
    else  { /* format == GENERALIZED_TIME */
        year += btoi(date[i++]) * 1000;
        year += btoi(date[i++]) * 100;
    }    

    val = year;
    GetTime(&val, date, &i);
    year = (CPU_INT16U)val;

    val = 0;
    GetTime(&val, date, &i);   
    month = (CPU_INT08U)val;   

    val = 0;
    GetTime(&val, date, &i);  
    day = (CPU_INT16U)val;

    val = 0;
    GetTime(&val, date, &i);  
    hour = (CPU_INT08U)val;

    val = 0;
    GetTime(&val, date, &i);  
    min = (CPU_INT08U)val;

    val = 0;
    GetTime(&val, date, &i);  
    sec = (CPU_INT08U)val;

    return NetSecure_ValidateDate(year, month, day, hour, min, sec, dateType); 
}

#endif /* MICRIUM */


CYASSL_LOCAL int GetLength(const byte* input, word32* inOutIdx, int* len,
                           word32 maxIdx)
{
    int     length = 0;
    word32  i = *inOutIdx;
    byte    b;

    if ( (i+1) > maxIdx) {   /* for first read */
        CYASSL_MSG("GetLength bad index on input");
        return BUFFER_E;
    }

    b = input[i++];
    if (b >= ASN_LONG_LENGTH) {        
        word32 bytes = b & 0x7F;

        if ( (i+bytes) > maxIdx) {   /* for reading bytes */
            CYASSL_MSG("GetLength bad long length");
            return BUFFER_E;
        }

        while (bytes--) {
            b = input[i++];
            length = (length << 8) | b;
        }
    }
    else
        length = b;
    
    if ( (i+length) > maxIdx) {   /* for user of length */
        CYASSL_MSG("GetLength value exceeds buffer length");
        return BUFFER_E;
    }

    *inOutIdx = i;
    *len      = length;

    return length;
}


CYASSL_LOCAL int GetSequence(const byte* input, word32* inOutIdx, int* len,
                           word32 maxIdx)
{
    int    length = -1;
    word32 idx    = *inOutIdx;

    if (input[idx++] != (ASN_SEQUENCE | ASN_CONSTRUCTED) ||
            GetLength(input, &idx, &length, maxIdx) < 0)
        return ASN_PARSE_E;

    *len      = length;
    *inOutIdx = idx;

    return length;
}


CYASSL_LOCAL int GetSet(const byte* input, word32* inOutIdx, int* len,
                        word32 maxIdx)
{
    int    length = -1;
    word32 idx    = *inOutIdx;

    if (input[idx++] != (ASN_SET | ASN_CONSTRUCTED) ||
            GetLength(input, &idx, &length, maxIdx) < 0)
        return ASN_PARSE_E;

    *len      = length;
    *inOutIdx = idx;

    return length;
}


/* winodws header clash for WinCE using GetVersion */
CYASSL_LOCAL int GetMyVersion(const byte* input, word32* inOutIdx, int* version)
{
    word32 idx = *inOutIdx;

    CYASSL_ENTER("GetMyVersion");

    if (input[idx++] != ASN_INTEGER)
        return ASN_PARSE_E;

    if (input[idx++] != 0x01)
        return ASN_VERSION_E;

    *version  = input[idx++];
    *inOutIdx = idx;

    return *version;
}


#ifndef NO_PWDBASED
/* Get small count integer, 32 bits or less */
static int GetShortInt(const byte* input, word32* inOutIdx, int* number)
{
    word32 idx = *inOutIdx;
    word32 len;

    *number = 0;

    if (input[idx++] != ASN_INTEGER)
        return ASN_PARSE_E;

    len = input[idx++];
    if (len > 4)
        return ASN_PARSE_E;

    while (len--) {
        *number  = *number << 8 | input[idx++];
    }

    *inOutIdx = idx;

    return *number;
}
#endif /* !NO_PWDBASED */


/* May not have one, not an error */
static int GetExplicitVersion(const byte* input, word32* inOutIdx, int* version)
{
    word32 idx = *inOutIdx;

    CYASSL_ENTER("GetExplicitVersion");
    if (input[idx++] == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED)) {
        *inOutIdx = ++idx;  /* eat header */
        return GetMyVersion(input, inOutIdx, version);
    }

    /* go back as is */
    *version = 0;

    return 0;
}


CYASSL_LOCAL int GetInt(mp_int* mpi, const byte* input, word32* inOutIdx,
                  word32 maxIdx)
{
    word32 i = *inOutIdx;
    byte   b = input[i++];
    int    length;

    if (b != ASN_INTEGER)
        return ASN_PARSE_E;

    if (GetLength(input, &i, &length, maxIdx) < 0)
        return ASN_PARSE_E;

    if ( (b = input[i++]) == 0x00)
        length--;
    else
        i--;

    if (mp_init(mpi) != MP_OKAY)
        return MP_INIT_E;

    if (mp_read_unsigned_bin(mpi, (byte*)input + i, length) != 0) {
        mp_clear(mpi);
        return ASN_GETINT_E;
    }

    *inOutIdx = i + length;
    return 0;
}


static int GetObjectId(const byte* input, word32* inOutIdx, word32* oid,
                     word32 maxIdx)
{
    int    length;
    word32 i = *inOutIdx;
    byte   b;
    *oid = 0;
    
    b = input[i++];
    if (b != ASN_OBJECT_ID) 
        return ASN_OBJECT_ID_E;
    
    if (GetLength(input, &i, &length, maxIdx) < 0)
        return ASN_PARSE_E;
    
    while(length--)
        *oid += input[i++];
    /* just sum it up for now */
    
    *inOutIdx = i;
    
    return 0;
}


CYASSL_LOCAL int GetAlgoId(const byte* input, word32* inOutIdx, word32* oid,
                     word32 maxIdx)
{
    int    length;
    word32 i = *inOutIdx;
    byte   b;
    *oid = 0;
   
    CYASSL_ENTER("GetAlgoId");

    if (GetSequence(input, &i, &length, maxIdx) < 0)
        return ASN_PARSE_E;
    
    b = input[i++];
    if (b != ASN_OBJECT_ID) 
        return ASN_OBJECT_ID_E;
    
    if (GetLength(input, &i, &length, maxIdx) < 0)
        return ASN_PARSE_E;
    
    while(length--) {
        /* odd HC08 compiler behavior here when input[i++] */
        *oid += input[i];
        i++;
    }
    /* just sum it up for now */
    
    /* could have NULL tag and 0 terminator, but may not */
    b = input[i++];
    
    if (b == ASN_TAG_NULL) {
        b = input[i++];
        if (b != 0)
            return ASN_EXPECT_0_E;
    }
    else
    /* go back, didn't have it */
        i--;
    
    *inOutIdx = i;
    
    return 0;
}

#ifndef NO_RSA


#ifdef HAVE_CAVIUM

static int GetCaviumInt(byte** buff, word16* buffSz, const byte* input,
                        word32* inOutIdx, word32 maxIdx, void* heap)
{
    word32 i = *inOutIdx;
    byte   b = input[i++];
    int    length;

    if (b != ASN_INTEGER)
        return ASN_PARSE_E;

    if (GetLength(input, &i, &length, maxIdx) < 0)
        return ASN_PARSE_E;

    if ( (b = input[i++]) == 0x00)
        length--;
    else
        i--;

    *buffSz = (word16)length;
    *buff   = XMALLOC(*buffSz, heap, DYNAMIC_TYPE_CAVIUM_RSA);
    if (*buff == NULL)
        return MEMORY_E;

    XMEMCPY(*buff, input + i, *buffSz);

    *inOutIdx = i + length;
    return 0;
}

static int CaviumRsaPrivateKeyDecode(const byte* input, word32* inOutIdx,
                                     RsaKey* key, word32 inSz)
{
    int   version, length;
    void* h = key->heap;

    if (GetSequence(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

    if (GetMyVersion(input, inOutIdx, &version) < 0)
        return ASN_PARSE_E;

    key->type = RSA_PRIVATE;

    if (GetCaviumInt(&key->c_n,  &key->c_nSz,   input, inOutIdx, inSz, h) < 0 ||
        GetCaviumInt(&key->c_e,  &key->c_eSz,   input, inOutIdx, inSz, h) < 0 ||
        GetCaviumInt(&key->c_d,  &key->c_dSz,   input, inOutIdx, inSz, h) < 0 ||
        GetCaviumInt(&key->c_p,  &key->c_pSz,   input, inOutIdx, inSz, h) < 0 ||
        GetCaviumInt(&key->c_q,  &key->c_qSz,   input, inOutIdx, inSz, h) < 0 ||
        GetCaviumInt(&key->c_dP, &key->c_dP_Sz, input, inOutIdx, inSz, h) < 0 ||
        GetCaviumInt(&key->c_dQ, &key->c_dQ_Sz, input, inOutIdx, inSz, h) < 0 ||
        GetCaviumInt(&key->c_u,  &key->c_uSz,   input, inOutIdx, inSz, h) < 0 )
            return ASN_RSA_KEY_E;

    return 0;
}


#endif /* HAVE_CAVIUM */

int RsaPrivateKeyDecode(const byte* input, word32* inOutIdx, RsaKey* key,
                        word32 inSz)
{
    int    version, length;

#ifdef HAVE_CAVIUM
    if (key->magic == CYASSL_RSA_CAVIUM_MAGIC)
        return CaviumRsaPrivateKeyDecode(input, inOutIdx, key, inSz);
#endif

    if (GetSequence(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

    if (GetMyVersion(input, inOutIdx, &version) < 0)
        return ASN_PARSE_E;

    key->type = RSA_PRIVATE;

    if (GetInt(&key->n,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->e,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->d,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->p,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->q,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->dP, input, inOutIdx, inSz) < 0 ||
        GetInt(&key->dQ, input, inOutIdx, inSz) < 0 ||
        GetInt(&key->u,  input, inOutIdx, inSz) < 0 )  return ASN_RSA_KEY_E;

    return 0;
}

#endif /* NO_RSA */

/* Remove PKCS8 header, move beginning of traditional to beginning of input */
int ToTraditional(byte* input, word32 sz)
{
    word32 inOutIdx = 0, oid;
    int    version, length;

    if (GetSequence(input, &inOutIdx, &length, sz) < 0)
        return ASN_PARSE_E;

    if (GetMyVersion(input, &inOutIdx, &version) < 0)
        return ASN_PARSE_E;
    
    if (GetAlgoId(input, &inOutIdx, &oid, sz) < 0)
        return ASN_PARSE_E;

    if (input[inOutIdx] == ASN_OBJECT_ID) {
        /* pkcs8 ecc uses slightly different format */
        inOutIdx++;  /* past id */
        if (GetLength(input, &inOutIdx, &length, sz) < 0)
            return ASN_PARSE_E;
        inOutIdx += length;  /* over sub id, key input will verify */
    }
    
    if (input[inOutIdx++] != ASN_OCTET_STRING)
        return ASN_PARSE_E;
    
    if (GetLength(input, &inOutIdx, &length, sz) < 0)
        return ASN_PARSE_E;
    
    XMEMMOVE(input, input + inOutIdx, length);

    return length;
}


#ifndef NO_PWDBASED

/* Check To see if PKCS version algo is supported, set id if it is return 0
   < 0 on error */
static int CheckAlgo(int first, int second, int* id, int* version)
{
    *id      = ALGO_ID_E;
    *version = PKCS5;   /* default */

    if (first == 1) {
        switch (second) {
        case 1:
            *id = PBE_SHA1_RC4_128;
            *version = PKCS12;
            return 0;
        case 3:
            *id = PBE_SHA1_DES3;
            *version = PKCS12;
            return 0;
        default:
            return ALGO_ID_E;
        }
    }

    if (first != PKCS5)
        return ASN_INPUT_E;  /* VERSION ERROR */

    if (second == PBES2) {
        *version = PKCS5v2;
        return 0;
    }

    switch (second) {
    case 3:                   /* see RFC 2898 for ids */
        *id = PBE_MD5_DES;
        return 0;
    case 10:
        *id = PBE_SHA1_DES;
        return 0;
    default:
        return ALGO_ID_E;

    }
}


/* Check To see if PKCS v2 algo is supported, set id if it is return 0
   < 0 on error */
static int CheckAlgoV2(int oid, int* id)
{
    switch (oid) {
    case 69:
        *id = PBE_SHA1_DES;
        return 0;
    case 652:
        *id = PBE_SHA1_DES3;
        return 0;
    default:
        return ALGO_ID_E;

    }
}


/* Decrypt intput in place from parameters based on id */
static int DecryptKey(const char* password, int passwordSz, byte* salt,
                      int saltSz, int iterations, int id, byte* input,
                      int length, int version, byte* cbcIv)
{
    int typeH;
    int derivedLen;
    int decryptionType;
    int ret = 0;
#ifdef CYASSL_SMALL_STACK
    byte* key;
#else
    byte key[MAX_KEY_SIZE];
#endif

    switch (id) {
        case PBE_MD5_DES:
            typeH = MD5;
            derivedLen = 16;           /* may need iv for v1.5 */
            decryptionType = DES_TYPE;
            break;

        case PBE_SHA1_DES:
            typeH = SHA;
            derivedLen = 16;           /* may need iv for v1.5 */
            decryptionType = DES_TYPE;
            break;

        case PBE_SHA1_DES3:
            typeH = SHA;
            derivedLen = 32;           /* may need iv for v1.5 */
            decryptionType = DES3_TYPE;
            break;

        case PBE_SHA1_RC4_128:
            typeH = SHA;
            derivedLen = 16;
            decryptionType = RC4_TYPE;
            break;

        default:
            return ALGO_ID_E;
    }

#ifdef CYASSL_SMALL_STACK
    key = (byte*)XMALLOC(MAX_KEY_SIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (key == NULL)
        return MEMORY_E;
#endif

    if (version == PKCS5v2)
        ret = PBKDF2(key, (byte*)password, passwordSz, salt, saltSz, iterations,
               derivedLen, typeH);
    else if (version == PKCS5)
        ret = PBKDF1(key, (byte*)password, passwordSz, salt, saltSz, iterations,
               derivedLen, typeH);
    else if (version == PKCS12) {
        int  i, idx = 0;
        byte unicodePasswd[MAX_UNICODE_SZ];

        if ( (passwordSz * 2 + 2) > (int)sizeof(unicodePasswd)) {
#ifdef CYASSL_SMALL_STACK
            XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return UNICODE_SIZE_E; 
        }

        for (i = 0; i < passwordSz; i++) {
            unicodePasswd[idx++] = 0x00;
            unicodePasswd[idx++] = (byte)password[i];
        }
        /* add trailing NULL */
        unicodePasswd[idx++] = 0x00;
        unicodePasswd[idx++] = 0x00;

        ret =  PKCS12_PBKDF(key, unicodePasswd, idx, salt, saltSz,
                            iterations, derivedLen, typeH, 1);
        if (decryptionType != RC4_TYPE)
            ret += PKCS12_PBKDF(cbcIv, unicodePasswd, idx, salt, saltSz,
                                iterations, 8, typeH, 2);
    }
    else {
#ifdef CYASSL_SMALL_STACK
        XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ALGO_ID_E;
    }

    if (ret != 0) {
#ifdef CYASSL_SMALL_STACK
        XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ret;
    }

    switch (decryptionType) {
#ifndef NO_DES3
        case DES_TYPE:
        {
            Des    dec;
            byte*  desIv = key + 8;

            if (version == PKCS5v2 || version == PKCS12)
                desIv = cbcIv;

            ret = Des_SetKey(&dec, key, desIv, DES_DECRYPTION);
            if (ret != 0) {
#ifdef CYASSL_SMALL_STACK
                XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
                return ret;
            }

            Des_CbcDecrypt(&dec, input, input, length);
            break;
        }

        case DES3_TYPE:
        {
            Des3   dec;
            byte*  desIv = key + 24;

            if (version == PKCS5v2 || version == PKCS12)
                desIv = cbcIv;
            ret = Des3_SetKey(&dec, key, desIv, DES_DECRYPTION);
            if (ret != 0) {
#ifdef CYASSL_SMALL_STACK
                XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
                return ret;
            }
            ret = Des3_CbcDecrypt(&dec, input, input, length);
            if (ret != 0) {
#ifdef CYASSL_SMALL_STACK
                XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
                return ret;
            }
            break;
        }
#endif
#ifndef NO_RC4
        case RC4_TYPE:
        {
            Arc4    dec;

            Arc4SetKey(&dec, key, derivedLen);
            Arc4Process(&dec, input, input, length);
            break;
        }
#endif

        default:
#ifdef CYASSL_SMALL_STACK
            XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return ALGO_ID_E; 
    }

#ifdef CYASSL_SMALL_STACK
    XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return 0;
}


/* Remove Encrypted PKCS8 header, move beginning of traditional to beginning
   of input */
int ToTraditionalEnc(byte* input, word32 sz,const char* password,int passwordSz)
{
    word32 inOutIdx = 0, oid;
    int    first, second, length, version, saltSz, id;
    int    iterations = 0;
#ifdef CYASSL_SMALL_STACK
    byte*  salt = NULL;
    byte*  cbcIv = NULL;
#else
    byte   salt[MAX_SALT_SIZE];
    byte   cbcIv[MAX_IV_SIZE];
#endif
    
    if (GetSequence(input, &inOutIdx, &length, sz) < 0)
        return ASN_PARSE_E;

    if (GetAlgoId(input, &inOutIdx, &oid, sz) < 0)
        return ASN_PARSE_E;
    
    first  = input[inOutIdx - 2];   /* PKCS version alwyas 2nd to last byte */
    second = input[inOutIdx - 1];   /* version.algo, algo id last byte */

    if (CheckAlgo(first, second, &id, &version) < 0)
        return ASN_INPUT_E;  /* Algo ID error */

    if (version == PKCS5v2) {

        if (GetSequence(input, &inOutIdx, &length, sz) < 0)
            return ASN_PARSE_E;

        if (GetAlgoId(input, &inOutIdx, &oid, sz) < 0)
            return ASN_PARSE_E;

        if (oid != PBKDF2_OID)
            return ASN_PARSE_E;
    }

    if (GetSequence(input, &inOutIdx, &length, sz) < 0)
        return ASN_PARSE_E;

    if (input[inOutIdx++] != ASN_OCTET_STRING)
        return ASN_PARSE_E;
    
    if (GetLength(input, &inOutIdx, &saltSz, sz) < 0)
        return ASN_PARSE_E;

    if (saltSz > MAX_SALT_SIZE)
        return ASN_PARSE_E;
     
#ifdef CYASSL_SMALL_STACK
    salt = (byte*)XMALLOC(MAX_SALT_SIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (salt == NULL)
        return MEMORY_E;
#endif

    XMEMCPY(salt, &input[inOutIdx], saltSz);
    inOutIdx += saltSz;

    if (GetShortInt(input, &inOutIdx, &iterations) < 0) {
#ifdef CYASSL_SMALL_STACK
        XFREE(salt,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ASN_PARSE_E;
    }

#ifdef CYASSL_SMALL_STACK
    cbcIv = (byte*)XMALLOC(MAX_IV_SIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (cbcIv == NULL) {
        XFREE(salt,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
        return MEMORY_E;
    }
#endif

    if (version == PKCS5v2) {
        /* get encryption algo */
        if (GetAlgoId(input, &inOutIdx, &oid, sz) < 0) {
#ifdef CYASSL_SMALL_STACK
            XFREE(salt,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(cbcIv, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return ASN_PARSE_E;
        }

        if (CheckAlgoV2(oid, &id) < 0) {
#ifdef CYASSL_SMALL_STACK
            XFREE(salt,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(cbcIv, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return ASN_PARSE_E;  /* PKCS v2 algo id error */
        }

        if (input[inOutIdx++] != ASN_OCTET_STRING) {
#ifdef CYASSL_SMALL_STACK
            XFREE(salt,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(cbcIv, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return ASN_PARSE_E;
        }
    
        if (GetLength(input, &inOutIdx, &length, sz) < 0) {
#ifdef CYASSL_SMALL_STACK
            XFREE(salt,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(cbcIv, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return ASN_PARSE_E;
        }

        XMEMCPY(cbcIv, &input[inOutIdx], length);
        inOutIdx += length;
    }

    if (input[inOutIdx++] != ASN_OCTET_STRING) {
#ifdef CYASSL_SMALL_STACK
        XFREE(salt,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(cbcIv, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ASN_PARSE_E;
    }

    if (GetLength(input, &inOutIdx, &length, sz) < 0) {
#ifdef CYASSL_SMALL_STACK
        XFREE(salt,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(cbcIv, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ASN_PARSE_E;
    }

    if (DecryptKey(password, passwordSz, salt, saltSz, iterations, id,
                   input + inOutIdx, length, version, cbcIv) < 0) {
#ifdef CYASSL_SMALL_STACK
        XFREE(salt,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(cbcIv, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ASN_INPUT_E;  /* decrypt failure */
    }

#ifdef CYASSL_SMALL_STACK
    XFREE(salt,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(cbcIv, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    XMEMMOVE(input, input + inOutIdx, length);
    return ToTraditional(input, length);
}

#endif /* NO_PWDBASED */

#ifndef NO_RSA

int RsaPublicKeyDecode(const byte* input, word32* inOutIdx, RsaKey* key,
                       word32 inSz)
{
    int    length;

    if (GetSequence(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

    key->type = RSA_PUBLIC;

#if defined(OPENSSL_EXTRA) || defined(RSA_DECODE_EXTRA)
    {
    byte b = input[*inOutIdx];
    if (b != ASN_INTEGER) {
        /* not from decoded cert, will have algo id, skip past */
        if (GetSequence(input, inOutIdx, &length, inSz) < 0)
            return ASN_PARSE_E;
        
        b = input[(*inOutIdx)++];
        if (b != ASN_OBJECT_ID) 
            return ASN_OBJECT_ID_E;
        
        if (GetLength(input, inOutIdx, &length, inSz) < 0)
            return ASN_PARSE_E;
        
        *inOutIdx += length;   /* skip past */
        
        /* could have NULL tag and 0 terminator, but may not */
        b = input[(*inOutIdx)++];
        
        if (b == ASN_TAG_NULL) {
            b = input[(*inOutIdx)++];
            if (b != 0) 
                return ASN_EXPECT_0_E;
        }
        else
        /* go back, didn't have it */
            (*inOutIdx)--;
        
        /* should have bit tag length and seq next */
        b = input[(*inOutIdx)++];
        if (b != ASN_BIT_STRING)
            return ASN_BITSTR_E;
        
        if (GetLength(input, inOutIdx, &length, inSz) < 0)
            return ASN_PARSE_E;
        
        /* could have 0 */
        b = input[(*inOutIdx)++];
        if (b != 0)
            (*inOutIdx)--;
        
        if (GetSequence(input, inOutIdx, &length, inSz) < 0)
            return ASN_PARSE_E;
    }  /* end if */
    }  /* openssl var block */
#endif /* OPENSSL_EXTRA */

    if (GetInt(&key->n,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->e,  input, inOutIdx, inSz) < 0 )  return ASN_RSA_KEY_E;

    return 0;
}

#endif

#ifndef NO_DH

int DhKeyDecode(const byte* input, word32* inOutIdx, DhKey* key, word32 inSz)
{
    int    length;

    if (GetSequence(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

    if (GetInt(&key->p,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->g,  input, inOutIdx, inSz) < 0 )  return ASN_DH_KEY_E;

    return 0;
}

int DhSetKey(DhKey* key, const byte* p, word32 pSz, const byte* g, word32 gSz)
{
    if (key == NULL || p == NULL || g == NULL || pSz == 0 || gSz == 0)
        return BAD_FUNC_ARG;

    /* may have leading 0 */
    if (p[0] == 0) {
        pSz--; p++;
    }

    if (g[0] == 0) {
        gSz--; g++;
    }

    if (mp_init(&key->p) != MP_OKAY)
        return MP_INIT_E;
    if (mp_read_unsigned_bin(&key->p, p, pSz) != 0) {
        mp_clear(&key->p);
        return ASN_DH_KEY_E;
    }

    if (mp_init(&key->g) != MP_OKAY) {
        mp_clear(&key->p);
        return MP_INIT_E;
    }
    if (mp_read_unsigned_bin(&key->g, g, gSz) != 0) {
        mp_clear(&key->g);
        mp_clear(&key->p);
        return ASN_DH_KEY_E;
    }

    return 0;
}


int DhParamsLoad(const byte* input, word32 inSz, byte* p, word32* pInOutSz,
                 byte* g, word32* gInOutSz)
{
    word32 i = 0;
    byte   b;
    int    length;

    if (GetSequence(input, &i, &length, inSz) < 0)
        return ASN_PARSE_E;

    b = input[i++];
    if (b != ASN_INTEGER)
        return ASN_PARSE_E;

    if (GetLength(input, &i, &length, inSz) < 0)
        return ASN_PARSE_E;

    if ( (b = input[i++]) == 0x00)
        length--;
    else
        i--;

    if (length <= (int)*pInOutSz) {
        XMEMCPY(p, &input[i], length);
        *pInOutSz = length;
    }
    else
        return BUFFER_E;

    i += length;

    b = input[i++];
    if (b != ASN_INTEGER)
        return ASN_PARSE_E;

    if (GetLength(input, &i, &length, inSz) < 0)
        return ASN_PARSE_E;

    if (length <= (int)*gInOutSz) {
        XMEMCPY(g, &input[i], length);
        *gInOutSz = length;
    }
    else
        return BUFFER_E;

    return 0;
}

#endif /* NO_DH */


#ifndef NO_DSA

int DsaPublicKeyDecode(const byte* input, word32* inOutIdx, DsaKey* key,
                        word32 inSz)
{
    int    length;

    if (GetSequence(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

    if (GetInt(&key->p,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->q,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->g,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->y,  input, inOutIdx, inSz) < 0 )  return ASN_DH_KEY_E;

    key->type = DSA_PUBLIC;
    return 0;
}


int DsaPrivateKeyDecode(const byte* input, word32* inOutIdx, DsaKey* key,
                        word32 inSz)
{
    int    length, version;

    if (GetSequence(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

    if (GetMyVersion(input, inOutIdx, &version) < 0)
        return ASN_PARSE_E;

    if (GetInt(&key->p,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->q,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->g,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->y,  input, inOutIdx, inSz) < 0 ||
        GetInt(&key->x,  input, inOutIdx, inSz) < 0 )  return ASN_DH_KEY_E;

    key->type = DSA_PRIVATE;
    return 0;
}

#endif /* NO_DSA */


void InitDecodedCert(DecodedCert* cert, byte* source, word32 inSz, void* heap)
{
    cert->publicKey       = 0;
    cert->pubKeySize      = 0;
    cert->pubKeyStored    = 0;
    cert->version         = 0;
    cert->signature       = 0;
    cert->subjectCN       = 0;
    cert->subjectCNLen    = 0;
    cert->subjectCNEnc    = CTC_UTF8;
    cert->subjectCNStored = 0;
    cert->altNames        = NULL;
#ifndef IGNORE_NAME_CONSTRAINTS
    cert->altEmailNames   = NULL;
    cert->permittedNames  = NULL;
    cert->excludedNames   = NULL;
#endif /* IGNORE_NAME_CONSTRAINTS */
    cert->issuer[0]       = '\0';
    cert->subject[0]      = '\0';
    cert->source          = source;  /* don't own */
    cert->srcIdx          = 0;
    cert->maxIdx          = inSz;    /* can't go over this index */
    cert->heap            = heap;
    XMEMSET(cert->serial, 0, EXTERNAL_SERIAL_SIZE);
    cert->serialSz        = 0;
    cert->extensions      = 0;
    cert->extensionsSz    = 0;
    cert->extensionsIdx   = 0;
    cert->extAuthInfo     = NULL;
    cert->extAuthInfoSz   = 0;
    cert->extCrlInfo      = NULL;
    cert->extCrlInfoSz    = 0;
    XMEMSET(cert->extSubjKeyId, 0, SHA_SIZE);
    cert->extSubjKeyIdSet = 0;
    XMEMSET(cert->extAuthKeyId, 0, SHA_SIZE);
    cert->extAuthKeyIdSet = 0;
    cert->extKeyUsageSet  = 0;
    cert->extKeyUsage     = 0;
    cert->extExtKeyUsageSet = 0;
    cert->extExtKeyUsage    = 0;
    cert->isCA            = 0;
#ifdef HAVE_PKCS7
    cert->issuerRaw       = NULL;
    cert->issuerRawLen    = 0;
#endif
#ifdef CYASSL_CERT_GEN
    cert->subjectSN       = 0;
    cert->subjectSNLen    = 0;
    cert->subjectSNEnc    = CTC_UTF8;
    cert->subjectC        = 0;
    cert->subjectCLen     = 0;
    cert->subjectCEnc     = CTC_PRINTABLE;
    cert->subjectL        = 0;
    cert->subjectLLen     = 0;
    cert->subjectLEnc     = CTC_UTF8;
    cert->subjectST       = 0;
    cert->subjectSTLen    = 0;
    cert->subjectSTEnc    = CTC_UTF8;
    cert->subjectO        = 0;
    cert->subjectOLen     = 0;
    cert->subjectOEnc     = CTC_UTF8;
    cert->subjectOU       = 0;
    cert->subjectOULen    = 0;
    cert->subjectOUEnc    = CTC_UTF8;
    cert->subjectEmail    = 0;
    cert->subjectEmailLen = 0;
#endif /* CYASSL_CERT_GEN */
    cert->beforeDate      = NULL;
    cert->beforeDateLen   = 0;
    cert->afterDate       = NULL;
    cert->afterDateLen    = 0;
#ifdef OPENSSL_EXTRA
    XMEMSET(&cert->issuerName, 0, sizeof(DecodedName));
    XMEMSET(&cert->subjectName, 0, sizeof(DecodedName));
    cert->extBasicConstSet = 0;
    cert->extBasicConstCrit = 0;
    cert->extBasicConstPlSet = 0;
    cert->pathLength = 0;
    cert->extSubjAltNameSet = 0;
    cert->extSubjAltNameCrit = 0;
    cert->extAuthKeyIdCrit = 0;
    cert->extSubjKeyIdCrit = 0;
    cert->extKeyUsageCrit = 0;
    cert->extExtKeyUsageCrit = 0;
    cert->extExtKeyUsageSrc = NULL;
    cert->extExtKeyUsageSz = 0;
    cert->extExtKeyUsageCount = 0;
    cert->extAuthKeyIdSrc = NULL;
    cert->extAuthKeyIdSz = 0;
    cert->extSubjKeyIdSrc = NULL;
    cert->extSubjKeyIdSz = 0;
#endif /* OPENSSL_EXTRA */
#if defined(OPENSSL_EXTRA) || !defined(IGNORE_NAME_CONSTRAINTS)
    cert->extNameConstraintSet = 0;
#endif /* OPENSSL_EXTRA || !IGNORE_NAME_CONSTRAINTS */
#ifdef HAVE_ECC
    cert->pkCurveOID = 0;
#endif /* HAVE_ECC */
#ifdef CYASSL_SEP
    cert->deviceTypeSz = 0;
    cert->deviceType = NULL;
    cert->hwTypeSz = 0;
    cert->hwType = NULL;
    cert->hwSerialNumSz = 0;
    cert->hwSerialNum = NULL;
    #ifdef OPENSSL_EXTRA
        cert->extCertPolicySet = 0;
        cert->extCertPolicyCrit = 0;
    #endif /* OPENSSL_EXTRA */
#endif /* CYASSL_SEP */
}


void FreeAltNames(DNS_entry* altNames, void* heap)
{
    (void)heap;

    while (altNames) {
        DNS_entry* tmp = altNames->next;

        XFREE(altNames->name, heap, DYNAMIC_TYPE_ALTNAME);
        XFREE(altNames,       heap, DYNAMIC_TYPE_ALTNAME);
        altNames = tmp;
    }
}

#ifndef IGNORE_NAME_CONSTRAINTS

void FreeNameSubtrees(Base_entry* names, void* heap)
{
    (void)heap;

    while (names) {
        Base_entry* tmp = names->next;

        XFREE(names->name, heap, DYNAMIC_TYPE_ALTNAME);
        XFREE(names,       heap, DYNAMIC_TYPE_ALTNAME);
        names = tmp;
    }
}

#endif /* IGNORE_NAME_CONSTRAINTS */

void FreeDecodedCert(DecodedCert* cert)
{
    if (cert->subjectCNStored == 1)
        XFREE(cert->subjectCN, cert->heap, DYNAMIC_TYPE_SUBJECT_CN);
    if (cert->pubKeyStored == 1)
        XFREE(cert->publicKey, cert->heap, DYNAMIC_TYPE_PUBLIC_KEY);
    if (cert->altNames)
        FreeAltNames(cert->altNames, cert->heap);
#ifndef IGNORE_NAME_CONSTRAINTS
    if (cert->altEmailNames)
        FreeAltNames(cert->altEmailNames, cert->heap);
    if (cert->permittedNames)
        FreeNameSubtrees(cert->permittedNames, cert->heap);
    if (cert->excludedNames)
        FreeNameSubtrees(cert->excludedNames, cert->heap);
#endif /* IGNORE_NAME_CONSTRAINTS */
#ifdef CYASSL_SEP
    XFREE(cert->deviceType, cert->heap, 0);
    XFREE(cert->hwType, cert->heap, 0);
    XFREE(cert->hwSerialNum, cert->heap, 0);
#endif /* CYASSL_SEP */
#ifdef OPENSSL_EXTRA
    if (cert->issuerName.fullName != NULL)
        XFREE(cert->issuerName.fullName, NULL, DYNAMIC_TYPE_X509);
    if (cert->subjectName.fullName != NULL)
        XFREE(cert->subjectName.fullName, NULL, DYNAMIC_TYPE_X509);
#endif /* OPENSSL_EXTRA */
}


static int GetCertHeader(DecodedCert* cert)
{
    int ret = 0, len;
    byte serialTmp[EXTERNAL_SERIAL_SIZE];
#if defined(CYASSL_SMALL_STACK) && defined(USE_FAST_MATH)
    mp_int* mpi = NULL;
#else
    mp_int stack_mpi;
    mp_int* mpi = &stack_mpi;
#endif

    if (GetSequence(cert->source, &cert->srcIdx, &len, cert->maxIdx) < 0)
        return ASN_PARSE_E;

    cert->certBegin = cert->srcIdx;

    if (GetSequence(cert->source, &cert->srcIdx, &len, cert->maxIdx) < 0)
        return ASN_PARSE_E;
    cert->sigIndex = len + cert->srcIdx;

    if (GetExplicitVersion(cert->source, &cert->srcIdx, &cert->version) < 0)
        return ASN_PARSE_E;

#if defined(CYASSL_SMALL_STACK) && defined(USE_FAST_MATH)
    mpi = (mp_int*)XMALLOC(sizeof(mp_int), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (mpi == NULL)
        return MEMORY_E;
#endif

    if (GetInt(mpi, cert->source, &cert->srcIdx, cert->maxIdx) < 0) {
#if defined(CYASSL_SMALL_STACK) && defined(USE_FAST_MATH)
        XFREE(mpi, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ASN_PARSE_E;
    }

    len = mp_unsigned_bin_size(mpi);
    if (len < (int)sizeof(serialTmp)) {
        if ( (ret = mp_to_unsigned_bin(mpi, serialTmp)) == MP_OKAY) {
            XMEMCPY(cert->serial, serialTmp, len);
            cert->serialSz = len;
        }
    }
    mp_clear(mpi);

#if defined(CYASSL_SMALL_STACK) && defined(USE_FAST_MATH)
    XFREE(mpi, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

#if !defined(NO_RSA)
/* Store Rsa Key, may save later, Dsa could use in future */
static int StoreRsaKey(DecodedCert* cert)
{
    int    length;
    word32 recvd = cert->srcIdx;

    if (GetSequence(cert->source, &cert->srcIdx, &length, cert->maxIdx) < 0)
        return ASN_PARSE_E;
   
    recvd = cert->srcIdx - recvd;
    length += recvd;

    while (recvd--)
       cert->srcIdx--;

    cert->pubKeySize = length;
    cert->publicKey = cert->source + cert->srcIdx;
    cert->srcIdx += length;

    return 0;
}
#endif


#ifdef HAVE_ECC

    /* return 0 on sucess if the ECC curve oid sum is supported */
    static int CheckCurve(word32 oid)
    {
        if (oid != ECC_256R1 && oid != ECC_384R1 && oid != ECC_521R1 && oid !=
                   ECC_160R1 && oid != ECC_192R1 && oid != ECC_224R1)
            return ALGO_ID_E; 

        return 0;
    }

#endif /* HAVE_ECC */


static int GetKey(DecodedCert* cert)
{
    int length;
#ifdef HAVE_NTRU
    int tmpIdx = cert->srcIdx;
#endif

    if (GetSequence(cert->source, &cert->srcIdx, &length, cert->maxIdx) < 0)
        return ASN_PARSE_E;
   
    if (GetAlgoId(cert->source, &cert->srcIdx, &cert->keyOID, cert->maxIdx) < 0)
        return ASN_PARSE_E;

    switch (cert->keyOID) {
   #ifndef NO_RSA
        case RSAk:
        {
            byte b = cert->source[cert->srcIdx++];
            if (b != ASN_BIT_STRING)
                return ASN_BITSTR_E;

            if (GetLength(cert->source,&cert->srcIdx,&length,cert->maxIdx) < 0)
                return ASN_PARSE_E;
            b = cert->source[cert->srcIdx++];
            if (b != 0x00)
                return ASN_EXPECT_0_E;
    
            return StoreRsaKey(cert);
        }

    #endif /* NO_RSA */
    #ifdef HAVE_NTRU
        case NTRUk:
        {
            const byte* key = &cert->source[tmpIdx];
            byte*       next = (byte*)key;
            word16      keyLen;
            word32      rc;
            word32      remaining = cert->maxIdx - cert->srcIdx;
#ifdef CYASSL_SMALL_STACK
            byte*       keyBlob = NULL;
#else
            byte        keyBlob[MAX_NTRU_KEY_SZ];
#endif
            rc = ntru_crypto_ntru_encrypt_subjectPublicKeyInfo2PublicKey(key,
                                &keyLen, NULL, &next, &remaining);
            if (rc != NTRU_OK)
                return ASN_NTRU_KEY_E;
            if (keyLen > MAX_NTRU_KEY_SZ)
                return ASN_NTRU_KEY_E;

#ifdef CYASSL_SMALL_STACK
            keyBlob = (byte*)XMALLOC(MAX_NTRU_KEY_SZ, NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
            if (keyBlob == NULL)
                return MEMORY_E;
#endif

            rc = ntru_crypto_ntru_encrypt_subjectPublicKeyInfo2PublicKey(key,
                                &keyLen, keyBlob, &next, &remaining);
            if (rc != NTRU_OK) {
#ifdef CYASSL_SMALL_STACK
                XFREE(keyBlob, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
                return ASN_NTRU_KEY_E;
            }

            if ( (next - key) < 0) {
#ifdef CYASSL_SMALL_STACK
                XFREE(keyBlob, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
                return ASN_NTRU_KEY_E;
            }

            cert->srcIdx = tmpIdx + (int)(next - key);

            cert->publicKey = (byte*) XMALLOC(keyLen, cert->heap,
                                              DYNAMIC_TYPE_PUBLIC_KEY);
            if (cert->publicKey == NULL) {
#ifdef CYASSL_SMALL_STACK
                XFREE(keyBlob, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
                return MEMORY_E;
            }
            XMEMCPY(cert->publicKey, keyBlob, keyLen);
            cert->pubKeyStored = 1;
            cert->pubKeySize   = keyLen;

#ifdef CYASSL_SMALL_STACK
            XFREE(keyBlob, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

            return 0;
        }
    #endif /* HAVE_NTRU */
    #ifdef HAVE_ECC
        case ECDSAk:
        {
            int    oidSz = 0;
            byte   b = cert->source[cert->srcIdx++];
        
            if (b != ASN_OBJECT_ID) 
                return ASN_OBJECT_ID_E;

            if (GetLength(cert->source,&cert->srcIdx,&oidSz,cert->maxIdx) < 0)
                return ASN_PARSE_E;

            while(oidSz--)
                cert->pkCurveOID += cert->source[cert->srcIdx++];

            if (CheckCurve(cert->pkCurveOID) < 0)
                return ECC_CURVE_OID_E;

            /* key header */
            b = cert->source[cert->srcIdx++];
            if (b != ASN_BIT_STRING)
                return ASN_BITSTR_E;

            if (GetLength(cert->source,&cert->srcIdx,&length,cert->maxIdx) < 0)
                return ASN_PARSE_E;
            b = cert->source[cert->srcIdx++];
            if (b != 0x00)
                return ASN_EXPECT_0_E;

            /* actual key, use length - 1 since ate preceding 0 */
            length -= 1;

            cert->publicKey = (byte*) XMALLOC(length, cert->heap,
                                              DYNAMIC_TYPE_PUBLIC_KEY);
            if (cert->publicKey == NULL)
                return MEMORY_E;
            XMEMCPY(cert->publicKey, &cert->source[cert->srcIdx], length);
            cert->pubKeyStored = 1;
            cert->pubKeySize   = length;

            cert->srcIdx += length;

            return 0;
        }
    #endif /* HAVE_ECC */
        default:
            return ASN_UNKNOWN_OID_E;
    }
}


/* process NAME, either issuer or subject */
static int GetName(DecodedCert* cert, int nameType)
{
    Sha    sha;     /* MUST have SHA-1 hash for cert names */
    int    length;  /* length of all distinguished names */
    int    dummy;
    int    ret;
    char* full = (nameType == ISSUER) ? cert->issuer : cert->subject;
    word32 idx;
    #ifdef OPENSSL_EXTRA
        DecodedName* dName =
                  (nameType == ISSUER) ? &cert->issuerName : &cert->subjectName;
    #endif /* OPENSSL_EXTRA */

    CYASSL_MSG("Getting Cert Name");

    if (cert->source[cert->srcIdx] == ASN_OBJECT_ID) {
        CYASSL_MSG("Trying optional prefix...");

        if (GetLength(cert->source, &cert->srcIdx, &length, cert->maxIdx) < 0)
            return ASN_PARSE_E;

        cert->srcIdx += length;
        CYASSL_MSG("Got optional prefix");
    }

    /* For OCSP, RFC2560 section 4.1.1 states the issuer hash should be
     * calculated over the entire DER encoding of the Name field, including
     * the tag and length. */
    idx = cert->srcIdx;
    if (GetSequence(cert->source, &cert->srcIdx, &length, cert->maxIdx) < 0)
        return ASN_PARSE_E;

    ret = InitSha(&sha);
    if (ret != 0)
        return ret;
    ShaUpdate(&sha, &cert->source[idx], length + cert->srcIdx - idx);
    if (nameType == ISSUER)
        ShaFinal(&sha, cert->issuerHash);
    else
        ShaFinal(&sha, cert->subjectHash);

    length += cert->srcIdx;
    idx = 0;

#ifdef HAVE_PKCS7
    /* store pointer to raw issuer */
    if (nameType == ISSUER) {
        cert->issuerRaw = &cert->source[cert->srcIdx];
        cert->issuerRawLen = length - cert->srcIdx;
    }
#endif
#ifndef IGNORE_NAME_CONSTRAINTS
    if (nameType == SUBJECT) {
        cert->subjectRaw = &cert->source[cert->srcIdx];
        cert->subjectRawLen = length - cert->srcIdx;
    }
#endif

    while (cert->srcIdx < (word32)length) {
        byte   b;
        byte   joint[2];
        byte   tooBig = FALSE;
        int    oidSz;

        if (GetSet(cert->source, &cert->srcIdx, &dummy, cert->maxIdx) < 0) {
            CYASSL_MSG("Cert name lacks set header, trying sequence");
        }

        if (GetSequence(cert->source, &cert->srcIdx, &dummy, cert->maxIdx) < 0)
            return ASN_PARSE_E;

        b = cert->source[cert->srcIdx++];
        if (b != ASN_OBJECT_ID) 
            return ASN_OBJECT_ID_E;

        if (GetLength(cert->source, &cert->srcIdx, &oidSz, cert->maxIdx) < 0)
            return ASN_PARSE_E;

        XMEMCPY(joint, &cert->source[cert->srcIdx], sizeof(joint));

        /* v1 name types */
        if (joint[0] == 0x55 && joint[1] == 0x04) {
            byte   id;
            byte   copy = FALSE;
            int    strLen;

            cert->srcIdx += 2;
            id = cert->source[cert->srcIdx++]; 
            b  = cert->source[cert->srcIdx++]; /* encoding */

            if (GetLength(cert->source, &cert->srcIdx, &strLen,
                          cert->maxIdx) < 0)
                return ASN_PARSE_E;

            if ( (strLen + 14) > (int)(ASN_NAME_MAX - idx)) {
                /* include biggest pre fix header too 4 = "/serialNumber=" */
                CYASSL_MSG("ASN Name too big, skipping");
                tooBig = TRUE;
            }

            if (id == ASN_COMMON_NAME) {
                if (nameType == SUBJECT) {
                    cert->subjectCN = (char *)&cert->source[cert->srcIdx];
                    cert->subjectCNLen = strLen;
                    cert->subjectCNEnc = b;
                }

                if (!tooBig) {
                    XMEMCPY(&full[idx], "/CN=", 4);
                    idx += 4;
                    copy = TRUE;
                }
                #ifdef OPENSSL_EXTRA
                    dName->cnIdx = cert->srcIdx;
                    dName->cnLen = strLen;
                #endif /* OPENSSL_EXTRA */
            }
            else if (id == ASN_SUR_NAME) {
                if (!tooBig) {
                    XMEMCPY(&full[idx], "/SN=", 4);
                    idx += 4;
                    copy = TRUE;
                }
                #ifdef CYASSL_CERT_GEN
                    if (nameType == SUBJECT) {
                        cert->subjectSN = (char*)&cert->source[cert->srcIdx];
                        cert->subjectSNLen = strLen;
                        cert->subjectSNEnc = b;
                    }
                #endif /* CYASSL_CERT_GEN */
                #ifdef OPENSSL_EXTRA
                    dName->snIdx = cert->srcIdx;
                    dName->snLen = strLen;
                #endif /* OPENSSL_EXTRA */
            }
            else if (id == ASN_COUNTRY_NAME) {
                if (!tooBig) {
                    XMEMCPY(&full[idx], "/C=", 3);
                    idx += 3;
                    copy = TRUE;
                }
                #ifdef CYASSL_CERT_GEN
                    if (nameType == SUBJECT) {
                        cert->subjectC = (char*)&cert->source[cert->srcIdx];
                        cert->subjectCLen = strLen;
                        cert->subjectCEnc = b;
                    }
                #endif /* CYASSL_CERT_GEN */
                #ifdef OPENSSL_EXTRA
                    dName->cIdx = cert->srcIdx;
                    dName->cLen = strLen;
                #endif /* OPENSSL_EXTRA */
            }
            else if (id == ASN_LOCALITY_NAME) {
                if (!tooBig) {
                    XMEMCPY(&full[idx], "/L=", 3);
                    idx += 3;
                    copy = TRUE;
                }
                #ifdef CYASSL_CERT_GEN
                    if (nameType == SUBJECT) {
                        cert->subjectL = (char*)&cert->source[cert->srcIdx];
                        cert->subjectLLen = strLen;
                        cert->subjectLEnc = b;
                    }
                #endif /* CYASSL_CERT_GEN */
                #ifdef OPENSSL_EXTRA
                    dName->lIdx = cert->srcIdx;
                    dName->lLen = strLen;
                #endif /* OPENSSL_EXTRA */
            }
            else if (id == ASN_STATE_NAME) {
                if (!tooBig) {
                    XMEMCPY(&full[idx], "/ST=", 4);
                    idx += 4;
                    copy = TRUE;
                }
                #ifdef CYASSL_CERT_GEN
                    if (nameType == SUBJECT) {
                        cert->subjectST = (char*)&cert->source[cert->srcIdx];
                        cert->subjectSTLen = strLen;
                        cert->subjectSTEnc = b;
                    }
                #endif /* CYASSL_CERT_GEN */
                #ifdef OPENSSL_EXTRA
                    dName->stIdx = cert->srcIdx;
                    dName->stLen = strLen;
                #endif /* OPENSSL_EXTRA */
            }
            else if (id == ASN_ORG_NAME) {
                if (!tooBig) {
                    XMEMCPY(&full[idx], "/O=", 3);
                    idx += 3;
                    copy = TRUE;
                }
                #ifdef CYASSL_CERT_GEN
                    if (nameType == SUBJECT) {
                        cert->subjectO = (char*)&cert->source[cert->srcIdx];
                        cert->subjectOLen = strLen;
                        cert->subjectOEnc = b;
                    }
                #endif /* CYASSL_CERT_GEN */
                #ifdef OPENSSL_EXTRA
                    dName->oIdx = cert->srcIdx;
                    dName->oLen = strLen;
                #endif /* OPENSSL_EXTRA */
            }
            else if (id == ASN_ORGUNIT_NAME) {
                if (!tooBig) {
                    XMEMCPY(&full[idx], "/OU=", 4);
                    idx += 4;
                    copy = TRUE;
                }
                #ifdef CYASSL_CERT_GEN
                    if (nameType == SUBJECT) {
                        cert->subjectOU = (char*)&cert->source[cert->srcIdx];
                        cert->subjectOULen = strLen;
                        cert->subjectOUEnc = b;
                    }
                #endif /* CYASSL_CERT_GEN */
                #ifdef OPENSSL_EXTRA
                    dName->ouIdx = cert->srcIdx;
                    dName->ouLen = strLen;
                #endif /* OPENSSL_EXTRA */
            }
            else if (id == ASN_SERIAL_NUMBER) {
                if (!tooBig) {
                   XMEMCPY(&full[idx], "/serialNumber=", 14);
                   idx += 14;
                   copy = TRUE;
                }
                #ifdef OPENSSL_EXTRA
                    dName->snIdx = cert->srcIdx;
                    dName->snLen = strLen;
                #endif /* OPENSSL_EXTRA */
            }

            if (copy && !tooBig) {
                XMEMCPY(&full[idx], &cert->source[cert->srcIdx], strLen);
                idx += strLen;
            }

            cert->srcIdx += strLen;
        }
        else {
            /* skip */
            byte email = FALSE;
            byte uid   = FALSE;
            int  adv;

            if (joint[0] == 0x2a && joint[1] == 0x86)  /* email id hdr */
                email = TRUE;

            if (joint[0] == 0x9  && joint[1] == 0x92)  /* uid id hdr */
                uid = TRUE;

            cert->srcIdx += oidSz + 1;

            if (GetLength(cert->source, &cert->srcIdx, &adv, cert->maxIdx) < 0)
                return ASN_PARSE_E;

            if (adv > (int)(ASN_NAME_MAX - idx)) {
                CYASSL_MSG("ASN name too big, skipping");
                tooBig = TRUE;
            }

            if (email) {
                if ( (14 + adv) > (int)(ASN_NAME_MAX - idx)) {
                    CYASSL_MSG("ASN name too big, skipping");
                    tooBig = TRUE;
                }
                if (!tooBig) {
                    XMEMCPY(&full[idx], "/emailAddress=", 14);
                    idx += 14;
                }

                #ifdef CYASSL_CERT_GEN
                    if (nameType == SUBJECT) {
                        cert->subjectEmail = (char*)&cert->source[cert->srcIdx];
                        cert->subjectEmailLen = adv;
                    }
                #endif /* CYASSL_CERT_GEN */
                #ifdef OPENSSL_EXTRA
                    dName->emailIdx = cert->srcIdx;
                    dName->emailLen = adv;
                #endif /* OPENSSL_EXTRA */
                #ifndef IGNORE_NAME_CONSTRAINTS
                    {
                        DNS_entry* emailName = NULL;

                        emailName = (DNS_entry*)XMALLOC(sizeof(DNS_entry),
                                              cert->heap, DYNAMIC_TYPE_ALTNAME);
                        if (emailName == NULL) {
                            CYASSL_MSG("\tOut of Memory");
                            return MEMORY_E;
                        }
                        emailName->name = (char*)XMALLOC(adv + 1,
                                              cert->heap, DYNAMIC_TYPE_ALTNAME);
                        if (emailName->name == NULL) {
                            CYASSL_MSG("\tOut of Memory");
                            return MEMORY_E;
                        }
                        XMEMCPY(emailName->name,
                                              &cert->source[cert->srcIdx], adv);
                        emailName->name[adv] = 0;

                        emailName->next = cert->altEmailNames;
                        cert->altEmailNames = emailName;
                    }
                #endif /* IGNORE_NAME_CONSTRAINTS */
                if (!tooBig) {
                    XMEMCPY(&full[idx], &cert->source[cert->srcIdx], adv);
                    idx += adv;
                }
            }

            if (uid) {
                if ( (5 + adv) > (int)(ASN_NAME_MAX - idx)) {
                    CYASSL_MSG("ASN name too big, skipping");
                    tooBig = TRUE;
                }
                if (!tooBig) {
                    XMEMCPY(&full[idx], "/UID=", 5);
                    idx += 5;

                    XMEMCPY(&full[idx], &cert->source[cert->srcIdx], adv);
                    idx += adv;
                }
                #ifdef OPENSSL_EXTRA
                    dName->uidIdx = cert->srcIdx;
                    dName->uidLen = adv;
                #endif /* OPENSSL_EXTRA */
            }

            cert->srcIdx += adv;
        }
    }
    full[idx++] = 0;

    #ifdef OPENSSL_EXTRA
    {
        int totalLen = 0;

        if (dName->cnLen != 0)
            totalLen += dName->cnLen + 4;
        if (dName->snLen != 0)
            totalLen += dName->snLen + 4;
        if (dName->cLen != 0)
            totalLen += dName->cLen + 3;
        if (dName->lLen != 0)
            totalLen += dName->lLen + 3;
        if (dName->stLen != 0)
            totalLen += dName->stLen + 4;
        if (dName->oLen != 0)
            totalLen += dName->oLen + 3;
        if (dName->ouLen != 0)
            totalLen += dName->ouLen + 4;
        if (dName->emailLen != 0)
            totalLen += dName->emailLen + 14;
        if (dName->uidLen != 0)
            totalLen += dName->uidLen + 5;
        if (dName->serialLen != 0)
            totalLen += dName->serialLen + 14;

        dName->fullName = (char*)XMALLOC(totalLen + 1, NULL, DYNAMIC_TYPE_X509);
        if (dName->fullName != NULL) {
            idx = 0;

            if (dName->cnLen != 0) {
                dName->entryCount++;
                XMEMCPY(&dName->fullName[idx], "/CN=", 4);
                idx += 4;
                XMEMCPY(&dName->fullName[idx],
                                     &cert->source[dName->cnIdx], dName->cnLen);
                dName->cnIdx = idx;
                idx += dName->cnLen;
            }
            if (dName->snLen != 0) {
                dName->entryCount++;
                XMEMCPY(&dName->fullName[idx], "/SN=", 4);
                idx += 4;
                XMEMCPY(&dName->fullName[idx],
                                     &cert->source[dName->snIdx], dName->snLen);
                dName->snIdx = idx;
                idx += dName->snLen;
            }
            if (dName->cLen != 0) {
                dName->entryCount++;
                XMEMCPY(&dName->fullName[idx], "/C=", 3);
                idx += 3;
                XMEMCPY(&dName->fullName[idx],
                                       &cert->source[dName->cIdx], dName->cLen);
                dName->cIdx = idx;
                idx += dName->cLen;
            }
            if (dName->lLen != 0) {
                dName->entryCount++;
                XMEMCPY(&dName->fullName[idx], "/L=", 3);
                idx += 3;
                XMEMCPY(&dName->fullName[idx],
                                       &cert->source[dName->lIdx], dName->lLen);
                dName->lIdx = idx;
                idx += dName->lLen;
            }
            if (dName->stLen != 0) {
                dName->entryCount++;
                XMEMCPY(&dName->fullName[idx], "/ST=", 4);
                idx += 4;
                XMEMCPY(&dName->fullName[idx],
                                     &cert->source[dName->stIdx], dName->stLen);
                dName->stIdx = idx;
                idx += dName->stLen;
            }
            if (dName->oLen != 0) {
                dName->entryCount++;
                XMEMCPY(&dName->fullName[idx], "/O=", 3);
                idx += 3;
                XMEMCPY(&dName->fullName[idx],
                                       &cert->source[dName->oIdx], dName->oLen);
                dName->oIdx = idx;
                idx += dName->oLen;
            }
            if (dName->ouLen != 0) {
                dName->entryCount++;
                XMEMCPY(&dName->fullName[idx], "/OU=", 4);
                idx += 4;
                XMEMCPY(&dName->fullName[idx],
                                     &cert->source[dName->ouIdx], dName->ouLen);
                dName->ouIdx = idx;
                idx += dName->ouLen;
            }
            if (dName->emailLen != 0) {
                dName->entryCount++;
                XMEMCPY(&dName->fullName[idx], "/emailAddress=", 14);
                idx += 14;
                XMEMCPY(&dName->fullName[idx],
                               &cert->source[dName->emailIdx], dName->emailLen);
                dName->emailIdx = idx;
                idx += dName->emailLen;
            }
            if (dName->uidLen != 0) {
                dName->entryCount++;
                XMEMCPY(&dName->fullName[idx], "/UID=", 5);
                idx += 5;
                XMEMCPY(&dName->fullName[idx],
                                   &cert->source[dName->uidIdx], dName->uidLen);
                dName->uidIdx = idx;
                idx += dName->uidLen;
            }
            if (dName->serialLen != 0) {
                dName->entryCount++;
                XMEMCPY(&dName->fullName[idx], "/serialNumber=", 14);
                idx += 14;
                XMEMCPY(&dName->fullName[idx],
                             &cert->source[dName->serialIdx], dName->serialLen);
                dName->serialIdx = idx;
                idx += dName->serialLen;
            }
            dName->fullName[idx] = '\0';
            dName->fullNameLen = totalLen;
        }
    }
    #endif /* OPENSSL_EXTRA */

    return 0;
}


#ifndef NO_TIME_H

/* to the second */
static int DateGreaterThan(const struct tm* a, const struct tm* b)
{
    if (a->tm_year > b->tm_year)
        return 1;

    if (a->tm_year == b->tm_year && a->tm_mon > b->tm_mon)
        return 1;
    
    if (a->tm_year == b->tm_year && a->tm_mon == b->tm_mon &&
           a->tm_mday > b->tm_mday)
        return 1;

    if (a->tm_year == b->tm_year && a->tm_mon == b->tm_mon &&
        a->tm_mday == b->tm_mday && a->tm_hour > b->tm_hour)
        return 1;

    if (a->tm_year == b->tm_year && a->tm_mon == b->tm_mon &&
        a->tm_mday == b->tm_mday && a->tm_hour == b->tm_hour &&
        a->tm_min > b->tm_min)
        return 1;

    if (a->tm_year == b->tm_year && a->tm_mon == b->tm_mon &&
        a->tm_mday == b->tm_mday && a->tm_hour == b->tm_hour &&
        a->tm_min  == b->tm_min  && a->tm_sec > b->tm_sec)
        return 1;

    return 0; /* false */
}


static INLINE int DateLessThan(const struct tm* a, const struct tm* b)
{
    return DateGreaterThan(b,a);
}


/* like atoi but only use first byte */
/* Make sure before and after dates are valid */
int ValidateDate(const byte* date, byte format, int dateType)
{
    time_t ltime;
    struct tm  certTime;
    struct tm* localTime;
    int    i = 0;

    ltime = XTIME(0);
    XMEMSET(&certTime, 0, sizeof(certTime));

    if (format == ASN_UTC_TIME) {
        if (btoi(date[0]) >= 5)
            certTime.tm_year = 1900;
        else
            certTime.tm_year = 2000;
    }
    else  { /* format == GENERALIZED_TIME */
        certTime.tm_year += btoi(date[i++]) * 1000;
        certTime.tm_year += btoi(date[i++]) * 100;
    }

    GetTime(&certTime.tm_year, date, &i); certTime.tm_year -= 1900; /* adjust */
    GetTime(&certTime.tm_mon,  date, &i); certTime.tm_mon  -= 1;    /* adjust */
    GetTime(&certTime.tm_mday, date, &i);
    GetTime(&certTime.tm_hour, date, &i); 
    GetTime(&certTime.tm_min,  date, &i); 
    GetTime(&certTime.tm_sec,  date, &i); 
        
        if (date[i] != 'Z') {     /* only Zulu supported for this profile */
        CYASSL_MSG("Only Zulu time supported for this profile"); 
        return 0;
    }

    localTime = XGMTIME(&ltime);

    if (dateType == BEFORE) {
        if (DateLessThan(localTime, &certTime))
            return 0;
    }
    else
        if (DateGreaterThan(localTime, &certTime))
            return 0;

    return 1;
}

#endif /* NO_TIME_H */


static int GetDate(DecodedCert* cert, int dateType)
{
    int    length;
    byte   date[MAX_DATE_SIZE];
    byte   b;
    word32 startIdx = 0;

    if (dateType == BEFORE)
        cert->beforeDate = &cert->source[cert->srcIdx];
    else
        cert->afterDate = &cert->source[cert->srcIdx];
    startIdx = cert->srcIdx;

    b = cert->source[cert->srcIdx++];
    if (b != ASN_UTC_TIME && b != ASN_GENERALIZED_TIME)
        return ASN_TIME_E;

    if (GetLength(cert->source, &cert->srcIdx, &length, cert->maxIdx) < 0)
        return ASN_PARSE_E;

    if (length > MAX_DATE_SIZE || length < MIN_DATE_SIZE)
        return ASN_DATE_SZ_E;

    XMEMCPY(date, &cert->source[cert->srcIdx], length);
    cert->srcIdx += length;

    if (dateType == BEFORE)
        cert->beforeDateLen = cert->srcIdx - startIdx;
    else
        cert->afterDateLen  = cert->srcIdx - startIdx;

    if (!XVALIDATE_DATE(date, b, dateType)) {
        if (dateType == BEFORE)
            return ASN_BEFORE_DATE_E;
        else
            return ASN_AFTER_DATE_E;
    }

    return 0;
}


static int GetValidity(DecodedCert* cert, int verify)
{
    int length;
    int badDate = 0;

    if (GetSequence(cert->source, &cert->srcIdx, &length, cert->maxIdx) < 0)
        return ASN_PARSE_E;

    if (GetDate(cert, BEFORE) < 0 && verify)
        badDate = ASN_BEFORE_DATE_E;           /* continue parsing */
    
    if (GetDate(cert, AFTER) < 0 && verify)
        return ASN_AFTER_DATE_E;
   
    if (badDate != 0)
        return badDate;

    return 0;
}


int DecodeToKey(DecodedCert* cert, int verify)
{
    int badDate = 0;
    int ret;

    if ( (ret = GetCertHeader(cert)) < 0)
        return ret;

    CYASSL_MSG("Got Cert Header");

    if ( (ret = GetAlgoId(cert->source, &cert->srcIdx, &cert->signatureOID,
                          cert->maxIdx)) < 0)
        return ret;

    CYASSL_MSG("Got Algo ID");

    if ( (ret = GetName(cert, ISSUER)) < 0)
        return ret;

    if ( (ret = GetValidity(cert, verify)) < 0)
        badDate = ret;

    if ( (ret = GetName(cert, SUBJECT)) < 0)
        return ret;

    CYASSL_MSG("Got Subject Name");

    if ( (ret = GetKey(cert)) < 0)
        return ret;

    CYASSL_MSG("Got Key");

    if (badDate != 0)
        return badDate;

    return ret;
}


static int GetSignature(DecodedCert* cert)
{
    int    length;
    byte   b = cert->source[cert->srcIdx++];

    if (b != ASN_BIT_STRING)
        return ASN_BITSTR_E;

    if (GetLength(cert->source, &cert->srcIdx, &length, cert->maxIdx) < 0)
        return ASN_PARSE_E;

    cert->sigLength = length;

    b = cert->source[cert->srcIdx++];
    if (b != 0x00)
        return ASN_EXPECT_0_E;

    cert->sigLength--;
    cert->signature = &cert->source[cert->srcIdx];
    cert->srcIdx += cert->sigLength;

    return 0;
}


static word32 SetDigest(const byte* digest, word32 digSz, byte* output)
{
    output[0] = ASN_OCTET_STRING;
    output[1] = (byte)digSz;
    XMEMCPY(&output[2], digest, digSz);

    return digSz + 2;
} 


static word32 BytePrecision(word32 value)
{
    word32 i;
    for (i = sizeof(value); i; --i)
        if (value >> ((i - 1) * CYASSL_BIT_SIZE))
            break;

    return i;
}


CYASSL_LOCAL word32 SetLength(word32 length, byte* output)
{
    word32 i = 0, j;

    if (length < ASN_LONG_LENGTH)
        output[i++] = (byte)length;
    else {
        output[i++] = (byte)(BytePrecision(length) | ASN_LONG_LENGTH);
      
        for (j = BytePrecision(length); j; --j) {
            output[i] = (byte)(length >> ((j - 1) * CYASSL_BIT_SIZE));
            i++;
        }
    }

    return i;
}


CYASSL_LOCAL word32 SetSequence(word32 len, byte* output)
{
    output[0] = ASN_SEQUENCE | ASN_CONSTRUCTED;
    return SetLength(len, output + 1) + 1;
}

CYASSL_LOCAL word32 SetOctetString(word32 len, byte* output)
{
    output[0] = ASN_OCTET_STRING;
    return SetLength(len, output + 1) + 1;
}

/* Write a set header to output */
CYASSL_LOCAL word32 SetSet(word32 len, byte* output)
{
    output[0] = ASN_SET | ASN_CONSTRUCTED;
    return SetLength(len, output + 1) + 1;
}

CYASSL_LOCAL word32 SetImplicit(byte tag, byte number, word32 len, byte* output)
{

    output[0] = ((tag == ASN_SEQUENCE || tag == ASN_SET) ? ASN_CONSTRUCTED : 0)
                    | ASN_CONTEXT_SPECIFIC | number;
    return SetLength(len, output + 1) + 1;
}

CYASSL_LOCAL word32 SetExplicit(byte number, word32 len, byte* output)
{
    output[0] = ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | number;
    return SetLength(len, output + 1) + 1;
}


#if defined(HAVE_ECC) && defined(CYASSL_CERT_GEN)

static word32 SetCurve(ecc_key* key, byte* output)
{

    /* curve types */
    static const byte ECC_192v1_AlgoID[] = { 0x2a, 0x86, 0x48, 0xCE, 0x3d,
                                             0x03, 0x01, 0x01};
    static const byte ECC_256v1_AlgoID[] = { 0x2a, 0x86, 0x48, 0xCE, 0x3d,
                                            0x03, 0x01, 0x07};
    static const byte ECC_160r1_AlgoID[] = { 0x2b, 0x81, 0x04, 0x00,
                                             0x02};
    static const byte ECC_224r1_AlgoID[] = { 0x2b, 0x81, 0x04, 0x00,
                                             0x21};
    static const byte ECC_384r1_AlgoID[] = { 0x2b, 0x81, 0x04, 0x00,
                                             0x22};
    static const byte ECC_521r1_AlgoID[] = { 0x2b, 0x81, 0x04, 0x00,
                                             0x23};

    int    oidSz = 0;
    int    idx = 0;
    int    lenSz = 0;
    const  byte* oid = 0;

    output[0] = ASN_OBJECT_ID;
    idx++;

    switch (key->dp->size) {
        case 20:
            oidSz = sizeof(ECC_160r1_AlgoID);
            oid   =        ECC_160r1_AlgoID;
            break;

        case 24:
            oidSz = sizeof(ECC_192v1_AlgoID);
            oid   =        ECC_192v1_AlgoID;
            break;

        case 28:
            oidSz = sizeof(ECC_224r1_AlgoID);
            oid   =        ECC_224r1_AlgoID;
            break;

        case 32:
            oidSz = sizeof(ECC_256v1_AlgoID);
            oid   =        ECC_256v1_AlgoID;
            break;

        case 48:
            oidSz = sizeof(ECC_384r1_AlgoID);
            oid   =        ECC_384r1_AlgoID;
            break;

        case 66:
            oidSz = sizeof(ECC_521r1_AlgoID);
            oid   =        ECC_521r1_AlgoID;
            break;

        default:
            return ASN_UNKNOWN_OID_E;
    }
    lenSz = SetLength(oidSz, output+idx);
    idx += lenSz;

    XMEMCPY(output+idx, oid, oidSz);
    idx += oidSz;

    return idx;
}

#endif /* HAVE_ECC && CYASSL_CERT_GEN */


CYASSL_LOCAL word32 SetAlgoID(int algoOID, byte* output, int type, int curveSz)
{
    /* adding TAG_NULL and 0 to end */
    
    /* hashTypes */
    static const byte shaAlgoID[]    = { 0x2b, 0x0e, 0x03, 0x02, 0x1a,
                                         0x05, 0x00 };
    static const byte sha256AlgoID[] = { 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
                                         0x04, 0x02, 0x01, 0x05, 0x00 };
    static const byte sha384AlgoID[] = { 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
                                         0x04, 0x02, 0x02, 0x05, 0x00 };
    static const byte sha512AlgoID[] = { 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
                                         0x04, 0x02, 0x03, 0x05, 0x00 };
    static const byte md5AlgoID[]    = { 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d,
                                         0x02, 0x05, 0x05, 0x00  };
    static const byte md2AlgoID[]    = { 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d,
                                         0x02, 0x02, 0x05, 0x00};

    /* blkTypes, no NULL tags because IV is there instead */
    static const byte desCbcAlgoID[]  = { 0x2B, 0x0E, 0x03, 0x02, 0x07 };
    static const byte des3CbcAlgoID[] = { 0x2A, 0x86, 0x48, 0x86, 0xF7,
                                          0x0D, 0x03, 0x07 };

    /* RSA sigTypes */
    #ifndef NO_RSA
        static const byte md5wRSA_AlgoID[] = { 0x2a, 0x86, 0x48, 0x86, 0xf7,
                                            0x0d, 0x01, 0x01, 0x04, 0x05, 0x00};
        static const byte shawRSA_AlgoID[] = { 0x2a, 0x86, 0x48, 0x86, 0xf7,
                                            0x0d, 0x01, 0x01, 0x05, 0x05, 0x00};
        static const byte sha256wRSA_AlgoID[] = { 0x2a, 0x86, 0x48, 0x86, 0xf7,
                                            0x0d, 0x01, 0x01, 0x0b, 0x05, 0x00};
        static const byte sha384wRSA_AlgoID[] = {0x2a, 0x86, 0x48, 0x86, 0xf7,
                                            0x0d, 0x01, 0x01, 0x0c, 0x05, 0x00};
        static const byte sha512wRSA_AlgoID[] = {0x2a, 0x86, 0x48, 0x86, 0xf7,
                                            0x0d, 0x01, 0x01, 0x0d, 0x05, 0x00};
    #endif /* NO_RSA */
 
    /* ECDSA sigTypes */
    #ifdef HAVE_ECC 
        static const byte shawECDSA_AlgoID[] = { 0x2a, 0x86, 0x48, 0xCE, 0x3d,
                                                 0x04, 0x01, 0x05, 0x00};
        static const byte sha256wECDSA_AlgoID[] = { 0x2a, 0x86, 0x48, 0xCE,0x3d,
                                                 0x04, 0x03, 0x02, 0x05, 0x00};
        static const byte sha384wECDSA_AlgoID[] = { 0x2a, 0x86, 0x48, 0xCE,0x3d,
                                                 0x04, 0x03, 0x03, 0x05, 0x00};
        static const byte sha512wECDSA_AlgoID[] = { 0x2a, 0x86, 0x48, 0xCE,0x3d,
                                                 0x04, 0x03, 0x04, 0x05, 0x00};
    #endif /* HAVE_ECC */
 
    /* RSA keyType */
    #ifndef NO_RSA
        static const byte RSA_AlgoID[] = { 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d,
                                            0x01, 0x01, 0x01, 0x05, 0x00};
    #endif /* NO_RSA */

    #ifdef HAVE_ECC 
        /* ECC keyType */
        /* no tags, so set tagSz smaller later */
        static const byte ECC_AlgoID[] = { 0x2a, 0x86, 0x48, 0xCE, 0x3d,
                                           0x02, 0x01};
    #endif /* HAVE_ECC */

    int    algoSz = 0;
    int    tagSz  = 2;   /* tag null and terminator */
    word32 idSz, seqSz;
    const  byte* algoName = 0;
    byte ID_Length[MAX_LENGTH_SZ];
    byte seqArray[MAX_SEQ_SZ + 1];  /* add object_id to end */

    if (type == hashType) {
        switch (algoOID) {
        case SHAh:
            algoSz = sizeof(shaAlgoID);
            algoName = shaAlgoID;
            break;

        case SHA256h:
            algoSz = sizeof(sha256AlgoID);
            algoName = sha256AlgoID;
            break;

        case SHA384h:
            algoSz = sizeof(sha384AlgoID);
            algoName = sha384AlgoID;
            break;

        case SHA512h:
            algoSz = sizeof(sha512AlgoID);
            algoName = sha512AlgoID;
            break;

        case MD2h:
            algoSz = sizeof(md2AlgoID);
            algoName = md2AlgoID;
            break;

        case MD5h:
            algoSz = sizeof(md5AlgoID);
            algoName = md5AlgoID;
            break;

        default:
            CYASSL_MSG("Unknown Hash Algo");
            return 0;  /* UNKOWN_HASH_E; */
        }
    }
    else if (type == blkType) {
        switch (algoOID) {
        case DESb:
            algoSz = sizeof(desCbcAlgoID);
            algoName = desCbcAlgoID;
            tagSz = 0;
            break;
        case DES3b:
            algoSz = sizeof(des3CbcAlgoID);
            algoName = des3CbcAlgoID;
            tagSz = 0;
            break;
        default:
            CYASSL_MSG("Unknown Block Algo");
            return 0;
        }
    }
    else if (type == sigType) {    /* sigType */
        switch (algoOID) {
        #ifndef NO_RSA
            case CTC_MD5wRSA:
                algoSz = sizeof(md5wRSA_AlgoID);
                algoName = md5wRSA_AlgoID;
                break;

            case CTC_SHAwRSA:
                algoSz = sizeof(shawRSA_AlgoID);
                algoName = shawRSA_AlgoID;
                break;

            case CTC_SHA256wRSA:
                algoSz = sizeof(sha256wRSA_AlgoID);
                algoName = sha256wRSA_AlgoID;
                break;

            case CTC_SHA384wRSA:
                algoSz = sizeof(sha384wRSA_AlgoID);
                algoName = sha384wRSA_AlgoID;
                break;

            case CTC_SHA512wRSA:
                algoSz = sizeof(sha512wRSA_AlgoID);
                algoName = sha512wRSA_AlgoID;
                break;
        #endif /* NO_RSA */
        #ifdef HAVE_ECC 
            case CTC_SHAwECDSA:
                algoSz = sizeof(shawECDSA_AlgoID);
                algoName = shawECDSA_AlgoID;
                break;

            case CTC_SHA256wECDSA:
                algoSz = sizeof(sha256wECDSA_AlgoID);
                algoName = sha256wECDSA_AlgoID;
                break;

            case CTC_SHA384wECDSA:
                algoSz = sizeof(sha384wECDSA_AlgoID);
                algoName = sha384wECDSA_AlgoID;
                break;

            case CTC_SHA512wECDSA:
                algoSz = sizeof(sha512wECDSA_AlgoID);
                algoName = sha512wECDSA_AlgoID;
                break;
        #endif /* HAVE_ECC */
        default:
            CYASSL_MSG("Unknown Signature Algo");
            return 0;
        }
    }
    else if (type == keyType) {    /* keyType */
        switch (algoOID) {
        #ifndef NO_RSA
            case RSAk:
                algoSz = sizeof(RSA_AlgoID);
                algoName = RSA_AlgoID;
                break;
        #endif /* NO_RSA */
        #ifdef HAVE_ECC 
            case ECDSAk:
                algoSz = sizeof(ECC_AlgoID);
                algoName = ECC_AlgoID;
                tagSz = 0;
                break;
        #endif /* HAVE_ECC */
        default:
            CYASSL_MSG("Unknown Key Algo");
            return 0;
        }
    }
    else {
        CYASSL_MSG("Unknown Algo type");
        return 0;
    }

    idSz  = SetLength(algoSz - tagSz, ID_Length); /* don't include tags */
    seqSz = SetSequence(idSz + algoSz + 1 + curveSz, seqArray); 
                 /* +1 for object id, curveID of curveSz follows for ecc */
    seqArray[seqSz++] = ASN_OBJECT_ID;

    XMEMCPY(output, seqArray, seqSz);
    XMEMCPY(output + seqSz, ID_Length, idSz);
    XMEMCPY(output + seqSz + idSz, algoName, algoSz);

    return seqSz + idSz + algoSz;

}


word32 EncodeSignature(byte* out, const byte* digest, word32 digSz, int hashOID)
{
    byte digArray[MAX_ENCODED_DIG_SZ];
    byte algoArray[MAX_ALGO_SZ];
    byte seqArray[MAX_SEQ_SZ];
    word32 encDigSz, algoSz, seqSz; 

    encDigSz = SetDigest(digest, digSz, digArray);
    algoSz   = SetAlgoID(hashOID, algoArray, hashType, 0);
    seqSz    = SetSequence(encDigSz + algoSz, seqArray);

    XMEMCPY(out, seqArray, seqSz);
    XMEMCPY(out + seqSz, algoArray, algoSz);
    XMEMCPY(out + seqSz + algoSz, digArray, encDigSz);

    return encDigSz + algoSz + seqSz;
}


/* return true (1) or false (0) for Confirmation */
static int ConfirmSignature(const byte* buf, word32 bufSz,
    const byte* key, word32 keySz, word32 keyOID,
    const byte* sig, word32 sigSz, word32 sigOID,
    void* heap)
{
    int  typeH = 0, digestSz = 0, ret = 0;
#ifdef CYASSL_SMALL_STACK
    byte* digest;
#else
    byte digest[MAX_DIGEST_SIZE];
#endif

#ifdef CYASSL_SMALL_STACK
    digest = (byte*)XMALLOC(MAX_DIGEST_SIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (digest == NULL)
        return 0; /* not confirmed */
#endif

    (void)key;
    (void)keySz;
    (void)sig;
    (void)sigSz;
    (void)heap;

    switch (sigOID) {
    #ifndef NO_MD5
        case CTC_MD5wRSA:
        if (Md5Hash(buf, bufSz, digest) == 0) {
            typeH    = MD5h;
            digestSz = MD5_DIGEST_SIZE;
        }
        break;
    #endif
    #if defined(CYASSL_MD2)
        case CTC_MD2wRSA:
        if (Md2Hash(buf, bufSz, digest) == 0) {
            typeH    = MD2h;
            digestSz = MD2_DIGEST_SIZE;
        }
        break;
    #endif
    #ifndef NO_SHA
        case CTC_SHAwRSA:
        case CTC_SHAwDSA:
        case CTC_SHAwECDSA:
        if (ShaHash(buf, bufSz, digest) == 0) {    
            typeH    = SHAh;
            digestSz = SHA_DIGEST_SIZE;                
        }
        break;
    #endif
    #ifndef NO_SHA256
        case CTC_SHA256wRSA:
        case CTC_SHA256wECDSA:
        if (Sha256Hash(buf, bufSz, digest) == 0) {    
            typeH    = SHA256h;
            digestSz = SHA256_DIGEST_SIZE;
        }
        break;
    #endif
    #ifdef CYASSL_SHA512
        case CTC_SHA512wRSA:
        case CTC_SHA512wECDSA:
        if (Sha512Hash(buf, bufSz, digest) == 0) {    
            typeH    = SHA512h;
            digestSz = SHA512_DIGEST_SIZE;
        }
        break;
    #endif
    #ifdef CYASSL_SHA384
        case CTC_SHA384wRSA:
        case CTC_SHA384wECDSA:
        if (Sha384Hash(buf, bufSz, digest) == 0) {    
            typeH    = SHA384h;
            digestSz = SHA384_DIGEST_SIZE;
        }            
        break;
    #endif
        default:
            CYASSL_MSG("Verify Signautre has unsupported type");
    }
    
    if (typeH == 0) {
#ifdef CYASSL_SMALL_STACK
        XFREE(digest, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return 0; /* not confirmed */
    }

    switch (keyOID) {
    #ifndef NO_RSA
        case RSAk:
        {
            word32 idx = 0;
            int    encodedSigSz, verifySz;
            byte*  out;
#ifdef CYASSL_SMALL_STACK
            RsaKey* pubKey;
            byte* plain;
            byte* encodedSig;
#else
            RsaKey pubKey[1];
            byte plain[MAX_ENCODED_SIG_SZ];
            byte encodedSig[MAX_ENCODED_SIG_SZ];
#endif

#ifdef CYASSL_SMALL_STACK
            pubKey = (RsaKey*)XMALLOC(sizeof(RsaKey), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
            plain = (byte*)XMALLOC(MAX_ENCODED_SIG_SZ, NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
            encodedSig = (byte*)XMALLOC(MAX_ENCODED_SIG_SZ, NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
            
            if (pubKey == NULL || plain == NULL || encodedSig == NULL) {
                CYASSL_MSG("Failed to allocate memory at ConfirmSignature");
                
                if (pubKey)
                    XFREE(pubKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
                if (plain)
                    XFREE(plain, NULL, DYNAMIC_TYPE_TMP_BUFFER);
                if (encodedSig)
                    XFREE(encodedSig, NULL, DYNAMIC_TYPE_TMP_BUFFER);
                
                break; /* not confirmed */
            }
#endif

            if (sigSz > MAX_ENCODED_SIG_SZ) {
                CYASSL_MSG("Verify Signautre is too big");
            }
            else if (InitRsaKey(pubKey, heap) != 0) {
                CYASSL_MSG("InitRsaKey failed");
            }
            else if (RsaPublicKeyDecode(key, &idx, pubKey, keySz) < 0) {
                CYASSL_MSG("ASN Key decode error RSA");
            }
            else {
                XMEMCPY(plain, sig, sigSz);

                if ((verifySz = RsaSSL_VerifyInline(plain, sigSz, &out,
                                                                 pubKey)) < 0) {
                    CYASSL_MSG("Rsa SSL verify error");
                }
                else {
                    /* make sure we're right justified */
                    encodedSigSz =
                        EncodeSignature(encodedSig, digest, digestSz, typeH);
                    if (encodedSigSz != verifySz ||
                                XMEMCMP(out, encodedSig, encodedSigSz) != 0) {
                        CYASSL_MSG("Rsa SSL verify match encode error");
                    }
                    else
                        ret = 1; /* match */

                    #ifdef CYASSL_DEBUG_ENCODING
                    {
                        int x;
                        
                        printf("cyassl encodedSig:\n");
                        
                        for (x = 0; x < encodedSigSz; x++) {
                            printf("%02x ", encodedSig[x]);
                            if ( (x % 16) == 15)
                                printf("\n");
                        }
                        
                        printf("\n");
                        printf("actual digest:\n");
                        
                        for (x = 0; x < verifySz; x++) {
                            printf("%02x ", out[x]);
                            if ( (x % 16) == 15)
                                printf("\n");
                        }
                        
                        printf("\n");
                    }
                    #endif /* CYASSL_DEBUG_ENCODING */
                    
                }
                
            }
            
            FreeRsaKey(pubKey);
            
#ifdef CYASSL_SMALL_STACK
            XFREE(pubKey,     NULL, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(plain,      NULL, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(encodedSig, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        }

    #endif /* NO_RSA */
    #ifdef HAVE_ECC
        case ECDSAk:
        {
            int verify = 0;
#ifdef CYASSL_SMALL_STACK
            ecc_key* pubKey;
#else
            ecc_key pubKey[1];
#endif

#ifdef CYASSL_SMALL_STACK
            pubKey = (ecc_key*)XMALLOC(sizeof(ecc_key), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
            if (pubKey == NULL) {
                CYASSL_MSG("Failed to allocate pubKey");
                break; /* not confirmed */
            }
#endif

            if (ecc_import_x963(key, keySz, pubKey) < 0) {
                CYASSL_MSG("ASN Key import error ECC");
            }
            else {   
                if (ecc_verify_hash(sig, sigSz, digest, digestSz, &verify,
                                                                pubKey) != 0) {
                    CYASSL_MSG("ECC verify hash error");
                }
                else if (1 != verify) {
                    CYASSL_MSG("ECC Verify didn't match");
                } else
                    ret = 1; /* match */

                ecc_free(pubKey);
            }
#ifdef CYASSL_SMALL_STACK
            XFREE(pubKey, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        }
    #endif /* HAVE_ECC */
        default:
            CYASSL_MSG("Verify Key type unknown");
    }
    
#ifdef CYASSL_SMALL_STACK
    XFREE(digest, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}


#ifndef IGNORE_NAME_CONSTRAINTS

static int MatchBaseName(int type, const char* name, int nameSz,
                                                   const char* base, int baseSz)
{
    if (base == NULL || baseSz <= 0 || name == NULL || nameSz <= 0 ||
            name[0] == '.' || nameSz < baseSz ||
            (type != ASN_RFC822_TYPE && type != ASN_DNS_TYPE))
        return 0;

    /* If an email type, handle special cases where the base is only
     * a domain, or is an email address itself. */
    if (type == ASN_RFC822_TYPE) {
        const char* p = NULL;
        int count = 0;

        if (base[0] != '.') {
            p = base;
            count = 0;

            /* find the '@' in the base */
            while (*p != '@' && count < baseSz) {
                count++;
                p++;
            }

            /* No '@' in base, reset p to NULL */
            if (count >= baseSz)
                p = NULL;
        }

        if (p == NULL) {
            /* Base isn't an email address, it is a domain name,
             * wind the name forward one character past its '@'. */
            p = name;
            count = 0;
            while (*p != '@' && count < baseSz) {
                count++;
                p++;
            }

            if (count < baseSz && *p == '@') {
                name = p + 1;
                nameSz -= count + 1;
            }
        }
    }

    if ((type == ASN_DNS_TYPE || type == ASN_RFC822_TYPE) && base[0] == '.') {
        int szAdjust = nameSz - baseSz;
        name += szAdjust;
        nameSz -= szAdjust;
    }

    while (nameSz > 0) {
        if (XTOLOWER(*name++) != XTOLOWER(*base++))
            return 0;
        nameSz--;
    }

    return 1;
}


static int ConfirmNameConstraints(Signer* signer, DecodedCert* cert)
{
    if (signer == NULL || cert == NULL)
        return 0;

    /* Check against the excluded list */
    if (signer->excludedNames) {
        Base_entry* base = signer->excludedNames;

        while (base != NULL) {
            if (base->type == ASN_DNS_TYPE) {
                DNS_entry* name = cert->altNames;
                while (name != NULL) {
                    if (MatchBaseName(ASN_DNS_TYPE,
                                          name->name, (int)XSTRLEN(name->name),
                                          base->name, base->nameSz))
                        return 0;
                    name = name->next;
                }
            }
            else if (base->type == ASN_RFC822_TYPE) {
                DNS_entry* name = cert->altEmailNames;
                while (name != NULL) {
                    if (MatchBaseName(ASN_RFC822_TYPE,
                                          name->name, (int)XSTRLEN(name->name),
                                          base->name, base->nameSz))
                        return 0;

                    name = name->next;
                }
            }
            else if (base->type == ASN_DIR_TYPE) {
                if (cert->subjectRawLen == base->nameSz &&
                    XMEMCMP(cert->subjectRaw, base->name, base->nameSz) == 0) {

                    return 0;
                }
            }
            base = base->next;
        }
    }

    /* Check against the permitted list */
    if (signer->permittedNames != NULL) {
        int needDns = 0;
        int matchDns = 0;
        int needEmail = 0;
        int matchEmail = 0;
        int needDir = 0;
        int matchDir = 0;
        Base_entry* base = signer->permittedNames;

        while (base != NULL) {
            if (base->type == ASN_DNS_TYPE) {
                DNS_entry* name = cert->altNames;

                if (name != NULL)
                    needDns = 1;

                while (name != NULL) {
                    matchDns = MatchBaseName(ASN_DNS_TYPE,
                                          name->name, (int)XSTRLEN(name->name),
                                          base->name, base->nameSz);
                    name = name->next;
                }
            }
            else if (base->type == ASN_RFC822_TYPE) {
                DNS_entry* name = cert->altEmailNames;

                if (name != NULL)
                    needEmail = 1;

                while (name != NULL) {
                    matchEmail = MatchBaseName(ASN_DNS_TYPE,
                                          name->name, (int)XSTRLEN(name->name),
                                          base->name, base->nameSz);
                    name = name->next;
                }
            }
            else if (base->type == ASN_DIR_TYPE) {
                needDir = 1;
                if (cert->subjectRaw != NULL &&
                    cert->subjectRawLen == base->nameSz &&
                    XMEMCMP(cert->subjectRaw, base->name, base->nameSz) == 0) {

                    matchDir = 1;
                }
            }
            base = base->next;
        }

        if ((needDns && !matchDns) || (needEmail && !matchEmail) ||
            (needDir && !matchDir)) {

            return 0;
        }
    }

    return 1;
}

#endif /* IGNORE_NAME_CONSTRAINTS */


static int DecodeAltNames(byte* input, int sz, DecodedCert* cert)
{
    word32 idx = 0;
    int length = 0;

    CYASSL_ENTER("DecodeAltNames");

    if (GetSequence(input, &idx, &length, sz) < 0) {
        CYASSL_MSG("\tBad Sequence");
        return ASN_PARSE_E;
    }

    while (length > 0) {
        byte       b = input[idx++];

        length--;

        /* Save DNS Type names in the altNames list. */
        /* Save Other Type names in the cert's OidMap */
        if (b == (ASN_CONTEXT_SPECIFIC | ASN_DNS_TYPE)) {
            DNS_entry* dnsEntry;
            int strLen;
            word32 lenStartIdx = idx;

            if (GetLength(input, &idx, &strLen, sz) < 0) {
                CYASSL_MSG("\tfail: str length");
                return ASN_PARSE_E;
            }
            length -= (idx - lenStartIdx);

            dnsEntry = (DNS_entry*)XMALLOC(sizeof(DNS_entry), cert->heap,
                                        DYNAMIC_TYPE_ALTNAME);
            if (dnsEntry == NULL) {
                CYASSL_MSG("\tOut of Memory");
                return ASN_PARSE_E;
            }

            dnsEntry->name = (char*)XMALLOC(strLen + 1, cert->heap,
                                         DYNAMIC_TYPE_ALTNAME);
            if (dnsEntry->name == NULL) {
                CYASSL_MSG("\tOut of Memory");
                XFREE(dnsEntry, cert->heap, DYNAMIC_TYPE_ALTNAME);
                return ASN_PARSE_E;
            }

            XMEMCPY(dnsEntry->name, &input[idx], strLen);
            dnsEntry->name[strLen] = '\0';

            dnsEntry->next = cert->altNames;
            cert->altNames = dnsEntry;

            length -= strLen;
            idx    += strLen;
        }
#ifndef IGNORE_NAME_CONSTRAINTS
        else if (b == (ASN_CONTEXT_SPECIFIC | ASN_RFC822_TYPE)) {
            DNS_entry* emailEntry;
            int strLen;
            word32 lenStartIdx = idx;

            if (GetLength(input, &idx, &strLen, sz) < 0) {
                CYASSL_MSG("\tfail: str length");
                return ASN_PARSE_E;
            }
            length -= (idx - lenStartIdx);

            emailEntry = (DNS_entry*)XMALLOC(sizeof(DNS_entry), cert->heap,
                                        DYNAMIC_TYPE_ALTNAME);
            if (emailEntry == NULL) {
                CYASSL_MSG("\tOut of Memory");
                return ASN_PARSE_E;
            }

            emailEntry->name = (char*)XMALLOC(strLen + 1, cert->heap,
                                         DYNAMIC_TYPE_ALTNAME);
            if (emailEntry->name == NULL) {
                CYASSL_MSG("\tOut of Memory");
                XFREE(emailEntry, cert->heap, DYNAMIC_TYPE_ALTNAME);
                return ASN_PARSE_E;
            }

            XMEMCPY(emailEntry->name, &input[idx], strLen);
            emailEntry->name[strLen] = '\0';

            emailEntry->next = cert->altEmailNames;
            cert->altEmailNames = emailEntry;

            length -= strLen;
            idx    += strLen;
        }
#endif /* IGNORE_NAME_CONSTRAINTS */
#ifdef CYASSL_SEP
        else if (b == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED | ASN_OTHER_TYPE))
        {
            int strLen;
            word32 lenStartIdx = idx;
            word32 oid = 0;

            if (GetLength(input, &idx, &strLen, sz) < 0) {
                CYASSL_MSG("\tfail: other name length");
                return ASN_PARSE_E;
            }
            /* Consume the rest of this sequence. */
            length -= (strLen + idx - lenStartIdx);

            if (GetObjectId(input, &idx, &oid, sz) < 0) {
                CYASSL_MSG("\tbad OID");
                return ASN_PARSE_E;
            }

            if (oid != HW_NAME_OID) {
                CYASSL_MSG("\tincorrect OID");
                return ASN_PARSE_E;
            }

            if (input[idx++] != (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED)) {
                CYASSL_MSG("\twrong type");
                return ASN_PARSE_E;
            }

            if (GetLength(input, &idx, &strLen, sz) < 0) {
                CYASSL_MSG("\tfail: str len");
                return ASN_PARSE_E;
            }

            if (GetSequence(input, &idx, &strLen, sz) < 0) {
                CYASSL_MSG("\tBad Sequence");
                return ASN_PARSE_E;
            }

            if (input[idx++] != ASN_OBJECT_ID) {
                CYASSL_MSG("\texpected OID");
                return ASN_PARSE_E;
            }

            if (GetLength(input, &idx, &strLen, sz) < 0) {
                CYASSL_MSG("\tfailed: str len");
                return ASN_PARSE_E;
            }

            cert->hwType = (byte*)XMALLOC(strLen, cert->heap, 0);
            if (cert->hwType == NULL) {
                CYASSL_MSG("\tOut of Memory");
                return MEMORY_E;
            }

            XMEMCPY(cert->hwType, &input[idx], strLen);
            cert->hwTypeSz = strLen;
            idx += strLen;

            if (input[idx++] != ASN_OCTET_STRING) {
                CYASSL_MSG("\texpected Octet String");
                return ASN_PARSE_E;
            }

            if (GetLength(input, &idx, &strLen, sz) < 0) {
                CYASSL_MSG("\tfailed: str len");
                return ASN_PARSE_E;
            }

            cert->hwSerialNum = (byte*)XMALLOC(strLen + 1, cert->heap, 0);
            if (cert->hwSerialNum == NULL) {
                CYASSL_MSG("\tOut of Memory");
                return MEMORY_E;
            }

            XMEMCPY(cert->hwSerialNum, &input[idx], strLen);
            cert->hwSerialNum[strLen] = '\0';
            cert->hwSerialNumSz = strLen;
            idx += strLen;
        }
#endif /* CYASSL_SEP */
        else {
            int strLen;
            word32 lenStartIdx = idx;

            CYASSL_MSG("\tUnsupported name type, skipping");

            if (GetLength(input, &idx, &strLen, sz) < 0) {
                CYASSL_MSG("\tfail: unsupported name length");
                return ASN_PARSE_E;
            }
            length -= (strLen + idx - lenStartIdx);
            idx += strLen;
        }
    }
    return 0;
}


static int DecodeBasicCaConstraint(byte* input, int sz, DecodedCert* cert)
{
    word32 idx = 0;
    int length = 0;

    CYASSL_ENTER("DecodeBasicCaConstraint");
    if (GetSequence(input, &idx, &length, sz) < 0) {
        CYASSL_MSG("\tfail: bad SEQUENCE");
        return ASN_PARSE_E;
    }

    if (length == 0)
        return 0;

    /* If the basic ca constraint is false, this extension may be named, but
     * left empty. So, if the length is 0, just return. */

    if (input[idx++] != ASN_BOOLEAN)
    {
        CYASSL_MSG("\tfail: constraint not BOOLEAN");
        return ASN_PARSE_E;
    }

    if (GetLength(input, &idx, &length, sz) < 0)
    {
        CYASSL_MSG("\tfail: length");
        return ASN_PARSE_E;
    }

    if (input[idx++])
        cert->isCA = 1;

    #ifdef OPENSSL_EXTRA
        /* If there isn't any more data, return. */
        if (idx >= (word32)sz)
            return 0;

        /* Anything left should be the optional pathlength */
        if (input[idx++] != ASN_INTEGER) {
            CYASSL_MSG("\tfail: pathlen not INTEGER");
            return ASN_PARSE_E;
        }

        if (input[idx++] != 1) {
            CYASSL_MSG("\tfail: pathlen too long");
            return ASN_PARSE_E;
        }

        cert->pathLength = input[idx];
        cert->extBasicConstPlSet = 1;
    #endif /* OPENSSL_EXTRA */

    return 0;
}


#define CRLDP_FULL_NAME 0
    /* From RFC3280 SS4.2.1.14, Distribution Point Name*/
#define GENERALNAME_URI 6
    /* From RFC3280 SS4.2.1.7, GeneralName */

static int DecodeCrlDist(byte* input, int sz, DecodedCert* cert)
{
    word32 idx = 0;
    int length = 0;

    CYASSL_ENTER("DecodeCrlDist");

    /* Unwrap the list of Distribution Points*/
    if (GetSequence(input, &idx, &length, sz) < 0)
        return ASN_PARSE_E;

    /* Unwrap a single Distribution Point */
    if (GetSequence(input, &idx, &length, sz) < 0)
        return ASN_PARSE_E;

    /* The Distribution Point has three explicit optional members
     *  First check for a DistributionPointName
     */
    if (input[idx] == (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 0))
    {
        idx++;
        if (GetLength(input, &idx, &length, sz) < 0)
            return ASN_PARSE_E;

        if (input[idx] == 
                    (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED | CRLDP_FULL_NAME))
        {
            idx++;
            if (GetLength(input, &idx, &length, sz) < 0)
                return ASN_PARSE_E;

            if (input[idx] == (ASN_CONTEXT_SPECIFIC | GENERALNAME_URI))
            {
                idx++;
                if (GetLength(input, &idx, &length, sz) < 0)
                    return ASN_PARSE_E;

                cert->extCrlInfoSz = length;
                cert->extCrlInfo = input + idx;
                idx += length;
            }
            else
                /* This isn't a URI, skip it. */
                idx += length;
        }
        else
            /* This isn't a FULLNAME, skip it. */
            idx += length;
    }

    /* Check for reasonFlags */
    if (idx < (word32)sz &&
        input[idx] == (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 1))
    {
        idx++;
        if (GetLength(input, &idx, &length, sz) < 0)
            return ASN_PARSE_E;
        idx += length;
    }

    /* Check for cRLIssuer */
    if (idx < (word32)sz &&
        input[idx] == (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 2))
    {
        idx++;
        if (GetLength(input, &idx, &length, sz) < 0)
            return ASN_PARSE_E;
        idx += length;
    }

    if (idx < (word32)sz)
    {
        CYASSL_MSG("\tThere are more CRL Distribution Point records, "
                   "but we only use the first one.");
    }

    return 0;
}


static int DecodeAuthInfo(byte* input, int sz, DecodedCert* cert)
/*
 *  Read the first of the Authority Information Access records. If there are
 *  any issues, return without saving the record.
 */
{
    word32 idx = 0;
    int length = 0;
    byte b;
    word32 oid;

    CYASSL_ENTER("DecodeAuthInfo");

    /* Unwrap the list of AIAs */
    if (GetSequence(input, &idx, &length, sz) < 0)
        return ASN_PARSE_E;

    while (idx < (word32)sz) {
        /* Unwrap a single AIA */
        if (GetSequence(input, &idx, &length, sz) < 0)
            return ASN_PARSE_E;

        oid = 0;
        if (GetObjectId(input, &idx, &oid, sz) < 0)
            return ASN_PARSE_E;

        /* Only supporting URIs right now. */
        b = input[idx++];
        if (GetLength(input, &idx, &length, sz) < 0)
            return ASN_PARSE_E;

        if (b == (ASN_CONTEXT_SPECIFIC | GENERALNAME_URI) &&
            oid == AIA_OCSP_OID)
        {
            cert->extAuthInfoSz = length;
            cert->extAuthInfo = input + idx;
            break;
        }
        idx += length;
    }

    return 0;
}


static int DecodeAuthKeyId(byte* input, int sz, DecodedCert* cert)
{
    word32 idx = 0;
    int length = 0, ret = 0;

    CYASSL_ENTER("DecodeAuthKeyId");

    if (GetSequence(input, &idx, &length, sz) < 0) {
        CYASSL_MSG("\tfail: should be a SEQUENCE\n");
        return ASN_PARSE_E;
    }

    if (input[idx++] != (ASN_CONTEXT_SPECIFIC | 0)) {
        CYASSL_MSG("\tinfo: OPTIONAL item 0, not available\n");
        return 0;
    }

    if (GetLength(input, &idx, &length, sz) < 0) {
        CYASSL_MSG("\tfail: extension data length");
        return ASN_PARSE_E;
    }

    #ifdef OPENSSL_EXTRA
        cert->extAuthKeyIdSrc = &input[idx];
        cert->extAuthKeyIdSz = length;
    #endif /* OPENSSL_EXTRA */

    if (length == SHA_SIZE) {
        XMEMCPY(cert->extAuthKeyId, input + idx, length);
    }
    else {
        Sha sha;
        ret = InitSha(&sha);
        if (ret != 0)
            return ret;
        ShaUpdate(&sha, input + idx, length);
        ShaFinal(&sha, cert->extAuthKeyId);
    }

    return 0;
}


static int DecodeSubjKeyId(byte* input, int sz, DecodedCert* cert)
{
    word32 idx = 0;
    int length = 0, ret = 0;

    CYASSL_ENTER("DecodeSubjKeyId");

    if (input[idx++] != ASN_OCTET_STRING) {
        CYASSL_MSG("\tfail: should be an OCTET STRING");
        return ASN_PARSE_E;
    }

    if (GetLength(input, &idx, &length, sz) < 0) {
        CYASSL_MSG("\tfail: extension data length");
        return ASN_PARSE_E;
    }

    #ifdef OPENSSL_EXTRA
        cert->extSubjKeyIdSrc = &input[idx];
        cert->extSubjKeyIdSz = length;
    #endif /* OPENSSL_EXTRA */

    if (length == SIGNER_DIGEST_SIZE) {
        XMEMCPY(cert->extSubjKeyId, input + idx, length);
    }
    else {
        Sha sha;
        ret = InitSha(&sha);
        if (ret != 0)
            return ret;
        ShaUpdate(&sha, input + idx, length);
        ShaFinal(&sha, cert->extSubjKeyId);
    }

    return ret;
}


static int DecodeKeyUsage(byte* input, int sz, DecodedCert* cert)
{
    word32 idx = 0;
    int length;
    byte unusedBits;
    CYASSL_ENTER("DecodeKeyUsage");

    if (input[idx++] != ASN_BIT_STRING) {
        CYASSL_MSG("\tfail: key usage expected bit string");
        return ASN_PARSE_E;
    }

    if (GetLength(input, &idx, &length, sz) < 0) {
        CYASSL_MSG("\tfail: key usage bad length");
        return ASN_PARSE_E;
    }

    unusedBits = input[idx++];
    length--;

    if (length == 2) {
        cert->extKeyUsage = (word16)((input[idx] << 8) | input[idx+1]);
        cert->extKeyUsage >>= unusedBits;
    }
    else if (length == 1)
        cert->extKeyUsage = (word16)(input[idx] << 1);

    return 0;
}


static int DecodeExtKeyUsage(byte* input, int sz, DecodedCert* cert)
{
    word32 idx = 0, oid;
    int length;

    CYASSL_ENTER("DecodeExtKeyUsage");

    if (GetSequence(input, &idx, &length, sz) < 0) {
        CYASSL_MSG("\tfail: should be a SEQUENCE");
        return ASN_PARSE_E;
    }

    #ifdef OPENSSL_EXTRA
        cert->extExtKeyUsageSrc = input + idx;
        cert->extExtKeyUsageSz = length;
    #endif

    while (idx < (word32)sz) {
        if (GetObjectId(input, &idx, &oid, sz) < 0)
            return ASN_PARSE_E;

        switch (oid) {
            case EKU_ANY_OID:
                cert->extExtKeyUsage |= EXTKEYUSE_ANY;
                break;
            case EKU_SERVER_AUTH_OID:
                cert->extExtKeyUsage |= EXTKEYUSE_SERVER_AUTH;
                break;
            case EKU_CLIENT_AUTH_OID:
                cert->extExtKeyUsage |= EXTKEYUSE_CLIENT_AUTH;
                break;
            case EKU_OCSP_SIGN_OID:
                cert->extExtKeyUsage |= EXTKEYUSE_OCSP_SIGN;
                break;
        }

        #ifdef OPENSSL_EXTRA
            cert->extExtKeyUsageCount++;
        #endif
    }

    return 0;
}


#ifndef IGNORE_NAME_CONSTRAINTS
static int DecodeSubtree(byte* input, int sz, Base_entry** head, void* heap)
{
    word32 idx = 0;

    (void)heap;

    while (idx < (word32)sz) {
        int seqLength, strLength;
        word32 nameIdx;
        byte b;

        if (GetSequence(input, &idx, &seqLength, sz) < 0) {
            CYASSL_MSG("\tfail: should be a SEQUENCE");
            return ASN_PARSE_E;
        }

        nameIdx = idx;
        b = input[nameIdx++];
        if (GetLength(input, &nameIdx, &strLength, sz) <= 0) {
            CYASSL_MSG("\tinvalid length");
            return ASN_PARSE_E;
        }

        if (b == (ASN_CONTEXT_SPECIFIC | ASN_DNS_TYPE) ||
            b == (ASN_CONTEXT_SPECIFIC | ASN_RFC822_TYPE) ||
            b == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED | ASN_DIR_TYPE)) {

            Base_entry* entry = (Base_entry*)XMALLOC(sizeof(Base_entry),
                                                    heap, DYNAMIC_TYPE_ALTNAME);

            if (entry == NULL) {
                CYASSL_MSG("allocate error");
                return MEMORY_E;
            }

            entry->name = (char*)XMALLOC(strLength, heap, DYNAMIC_TYPE_ALTNAME);
            if (entry->name == NULL) {
                CYASSL_MSG("allocate error");
                return MEMORY_E;
            }

            XMEMCPY(entry->name, &input[nameIdx], strLength);
            entry->nameSz = strLength;
            entry->type = b & 0x0F;

            entry->next = *head;
            *head = entry;
        }

        idx += seqLength;
    }

    return 0;
}


static int DecodeNameConstraints(byte* input, int sz, DecodedCert* cert)
{
    word32 idx = 0;
    int length = 0;

    CYASSL_ENTER("DecodeNameConstraints");

    if (GetSequence(input, &idx, &length, sz) < 0) {
        CYASSL_MSG("\tfail: should be a SEQUENCE");
        return ASN_PARSE_E;
    }

    while (idx < (word32)sz) {
        byte b = input[idx++];
        Base_entry** subtree = NULL;

        if (GetLength(input, &idx, &length, sz) <= 0) {
            CYASSL_MSG("\tinvalid length");
            return ASN_PARSE_E;
        }

        if (b == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED | 0))
            subtree = &cert->permittedNames;
        else if (b == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED | 1))
            subtree = &cert->excludedNames;
        else {
            CYASSL_MSG("\tinvalid subtree");
            return ASN_PARSE_E;
        }

        DecodeSubtree(input + idx, length, subtree, cert->heap);

        idx += length;
    }

    return 0;
}
#endif /* IGNORE_NAME_CONSTRAINTS */


#ifdef CYASSL_SEP
    static int DecodeCertPolicy(byte* input, int sz, DecodedCert* cert)
    {
        word32 idx = 0;
        int length = 0;

        CYASSL_ENTER("DecodeCertPolicy");

        /* Unwrap certificatePolicies */
        if (GetSequence(input, &idx, &length, sz) < 0) {
            CYASSL_MSG("\tdeviceType isn't OID");
            return ASN_PARSE_E;
        }

        if (GetSequence(input, &idx, &length, sz) < 0) {
            CYASSL_MSG("\tdeviceType isn't OID");
            return ASN_PARSE_E;
        }

        if (input[idx++] != ASN_OBJECT_ID) {
            CYASSL_MSG("\tdeviceType isn't OID");
            return ASN_PARSE_E;
        }

        if (GetLength(input, &idx, &length, sz) < 0) {
            CYASSL_MSG("\tCouldn't read length of deviceType");
            return ASN_PARSE_E;
        }

        if (length > 0) {
            cert->deviceType = (byte*)XMALLOC(length, cert->heap, 0);
            if (cert->deviceType == NULL) {
                CYASSL_MSG("\tCouldn't alloc memory for deviceType");
                return MEMORY_E;
            }
            cert->deviceTypeSz = length;
            XMEMCPY(cert->deviceType, input + idx, length);
        }

        CYASSL_LEAVE("DecodeCertPolicy", 0);
        return 0;
    }
#endif /* CYASSL_SEP */


static int DecodeCertExtensions(DecodedCert* cert)
/*
 *  Processing the Certificate Extensions. This does not modify the current
 *  index. It is works starting with the recorded extensions pointer.
 */
{
    word32 idx = 0;
    int sz = cert->extensionsSz;
    byte* input = cert->extensions;
    int length;
    word32 oid;
    byte critical = 0;
    byte criticalFail = 0;

    CYASSL_ENTER("DecodeCertExtensions");

    if (input == NULL || sz == 0)
        return BAD_FUNC_ARG;

    if (input[idx++] != ASN_EXTENSIONS)
        return ASN_PARSE_E;

    if (GetLength(input, &idx, &length, sz) < 0)
        return ASN_PARSE_E;

    if (GetSequence(input, &idx, &length, sz) < 0)
        return ASN_PARSE_E;
    
    while (idx < (word32)sz) {
        if (GetSequence(input, &idx, &length, sz) < 0) {
            CYASSL_MSG("\tfail: should be a SEQUENCE");
            return ASN_PARSE_E;
        }

        oid = 0;
        if (GetObjectId(input, &idx, &oid, sz) < 0) {
            CYASSL_MSG("\tfail: OBJECT ID");
            return ASN_PARSE_E;
        }

        /* check for critical flag */
        critical = 0;
        if (input[idx] == ASN_BOOLEAN) {
            int boolLength = 0;
            idx++;
            if (GetLength(input, &idx, &boolLength, sz) < 0) {
                CYASSL_MSG("\tfail: critical boolean length");
                return ASN_PARSE_E;
            }
            if (input[idx++])
                critical = 1;
        }

        /* process the extension based on the OID */
        if (input[idx++] != ASN_OCTET_STRING) {
            CYASSL_MSG("\tfail: should be an OCTET STRING");
            return ASN_PARSE_E;
        }

        if (GetLength(input, &idx, &length, sz) < 0) {
            CYASSL_MSG("\tfail: extension data length");
            return ASN_PARSE_E;
        }

        switch (oid) {
            case BASIC_CA_OID:
                #ifdef OPENSSL_EXTRA
                    cert->extBasicConstSet = 1;
                    cert->extBasicConstCrit = critical;
                #endif
                if (DecodeBasicCaConstraint(&input[idx], length, cert) < 0)
                    return ASN_PARSE_E;
                break;

            case CRL_DIST_OID:
                if (DecodeCrlDist(&input[idx], length, cert) < 0)
                    return ASN_PARSE_E;
                break;

            case AUTH_INFO_OID:
                if (DecodeAuthInfo(&input[idx], length, cert) < 0)
                    return ASN_PARSE_E;
                break;

            case ALT_NAMES_OID:
                #ifdef OPENSSL_EXTRA
                    cert->extSubjAltNameSet = 1;
                    cert->extSubjAltNameCrit = critical;
                #endif
                if (DecodeAltNames(&input[idx], length, cert) < 0)
                    return ASN_PARSE_E;
                break;

            case AUTH_KEY_OID:
                cert->extAuthKeyIdSet = 1;
                #ifdef OPENSSL_EXTRA
                    cert->extAuthKeyIdCrit = critical;
                #endif
                if (DecodeAuthKeyId(&input[idx], length, cert) < 0)
                    return ASN_PARSE_E;
                break;

            case SUBJ_KEY_OID:
                cert->extSubjKeyIdSet = 1;
                #ifdef OPENSSL_EXTRA
                    cert->extSubjKeyIdCrit = critical;
                #endif
                if (DecodeSubjKeyId(&input[idx], length, cert) < 0)
                    return ASN_PARSE_E;
                break;

            case CERT_POLICY_OID:
                CYASSL_MSG("Certificate Policy extension not supported yet.");
                #ifdef CYASSL_SEP
                    #ifdef OPENSSL_EXTRA
                        cert->extCertPolicySet = 1;
                        cert->extCertPolicyCrit = critical;
                    #endif
                    if (DecodeCertPolicy(&input[idx], length, cert) < 0)
                        return ASN_PARSE_E;
                #endif
                break;

            case KEY_USAGE_OID:
                cert->extKeyUsageSet = 1;
                #ifdef OPENSSL_EXTRA
                    cert->extKeyUsageCrit = critical;
                #endif
                if (DecodeKeyUsage(&input[idx], length, cert) < 0)
                    return ASN_PARSE_E;
                break;

            case EXT_KEY_USAGE_OID:
                cert->extExtKeyUsageSet = 1;
                #ifdef OPENSSL_EXTRA
                    cert->extExtKeyUsageCrit = critical;
                #endif
                if (DecodeExtKeyUsage(&input[idx], length, cert) < 0)
                    return ASN_PARSE_E;
                break;

            #ifndef IGNORE_NAME_CONSTRAINTS
            case NAME_CONS_OID:
                cert->extNameConstraintSet = 1;
                #ifdef OPENSSL_EXTRA
                    cert->extNameConstraintCrit = critical;
                #endif
                if (DecodeNameConstraints(&input[idx], length, cert) < 0)
                    return ASN_PARSE_E;
                break;
            #endif /* IGNORE_NAME_CONSTRAINTS */

            case INHIBIT_ANY_OID:
                CYASSL_MSG("Inhibit anyPolicy extension not supported yet.");
                break;

            default:
                /* While it is a failure to not support critical extensions,
                 * still parse the certificate ignoring the unsupported
                 * extention to allow caller to accept it with the verify
                 * callback. */
                if (critical)
                    criticalFail = 1;
                break;
        }
        idx += length;
    }

    return criticalFail ? ASN_CRIT_EXT_E : 0;
}


int ParseCert(DecodedCert* cert, int type, int verify, void* cm)
{
    int   ret;
    char* ptr;

    ret = ParseCertRelative(cert, type, verify, cm);
    if (ret < 0)
        return ret;

    if (cert->subjectCNLen > 0) {
        ptr = (char*) XMALLOC(cert->subjectCNLen + 1, cert->heap,
                              DYNAMIC_TYPE_SUBJECT_CN);
        if (ptr == NULL)
            return MEMORY_E;
        XMEMCPY(ptr, cert->subjectCN, cert->subjectCNLen);
        ptr[cert->subjectCNLen] = '\0';
        cert->subjectCN = ptr;
        cert->subjectCNStored = 1;
    }

    if (cert->keyOID == RSAk &&
                          cert->publicKey != NULL  && cert->pubKeySize > 0) {
        ptr = (char*) XMALLOC(cert->pubKeySize, cert->heap,
                              DYNAMIC_TYPE_PUBLIC_KEY);
        if (ptr == NULL)
            return MEMORY_E;
        XMEMCPY(ptr, cert->publicKey, cert->pubKeySize);
        cert->publicKey = (byte *)ptr;
        cert->pubKeyStored = 1;
    }

    return ret;
}


/* from SSL proper, for locking can't do find here anymore */
#ifdef __cplusplus
    extern "C" {
#endif
    CYASSL_LOCAL Signer* GetCA(void* signers, byte* hash);
    #ifndef NO_SKID
        CYASSL_LOCAL Signer* GetCAByName(void* signers, byte* hash);
    #endif
#ifdef __cplusplus
    } 
#endif


int ParseCertRelative(DecodedCert* cert, int type, int verify, void* cm)
{
    word32 confirmOID;
    int    ret;
    int    badDate     = 0;
    int    criticalExt = 0;

    if ((ret = DecodeToKey(cert, verify)) < 0) {
        if (ret == ASN_BEFORE_DATE_E || ret == ASN_AFTER_DATE_E)
            badDate = ret;
        else
            return ret;
    }

    CYASSL_MSG("Parsed Past Key");

    if (cert->srcIdx < cert->sigIndex) {
        #ifndef ALLOW_V1_EXTENSIONS
            if (cert->version < 2) {
                CYASSL_MSG("    v1 and v2 certs not allowed extensions");
                return ASN_VERSION_E;
            }
        #endif
        /* save extensions */
        cert->extensions    = &cert->source[cert->srcIdx];
        cert->extensionsSz  =  cert->sigIndex - cert->srcIdx;
        cert->extensionsIdx = cert->srcIdx;   /* for potential later use */

        if ((ret = DecodeCertExtensions(cert)) < 0) {
            if (ret == ASN_CRIT_EXT_E)
                criticalExt = ret;
            else
                return ret;
        }

        /* advance past extensions */
        cert->srcIdx =  cert->sigIndex;
    }

    if ((ret = GetAlgoId(cert->source, &cert->srcIdx, &confirmOID,
                         cert->maxIdx)) < 0)
        return ret;

    if ((ret = GetSignature(cert)) < 0)
        return ret;

    if (confirmOID != cert->signatureOID)
        return ASN_SIG_OID_E;

    #ifndef NO_SKID
        if (cert->extSubjKeyIdSet == 0
                          && cert->publicKey != NULL && cert->pubKeySize > 0) {
            Sha sha;
            ret = InitSha(&sha);
            if (ret != 0)
                return ret;
            ShaUpdate(&sha, cert->publicKey, cert->pubKeySize);
            ShaFinal(&sha, cert->extSubjKeyId);
        }
    #endif

    if (verify && type != CA_TYPE) {
        Signer* ca = NULL;
        #ifndef NO_SKID
            if (cert->extAuthKeyIdSet)
                ca = GetCA(cm, cert->extAuthKeyId);
            if (ca == NULL)
                ca = GetCAByName(cm, cert->issuerHash);
        #else /* NO_SKID */
            ca = GetCA(cm, cert->issuerHash);
        #endif /* NO SKID */
        CYASSL_MSG("About to verify certificate signature");
 
        if (ca) {
#ifdef HAVE_OCSP
            /* Need the ca's public key hash for OCSP */
            {
                Sha sha;
                ret = InitSha(&sha);
                if (ret != 0)
                    return ret;
                ShaUpdate(&sha, ca->publicKey, ca->pubKeySize);
                ShaFinal(&sha, cert->issuerKeyHash);
            }
#endif /* HAVE_OCSP */
            /* try to confirm/verify signature */
            if (!ConfirmSignature(cert->source + cert->certBegin,
                        cert->sigIndex - cert->certBegin,
                    ca->publicKey, ca->pubKeySize, ca->keyOID,
                    cert->signature, cert->sigLength, cert->signatureOID,
                    cert->heap)) {
                CYASSL_MSG("Confirm signature failed");
                return ASN_SIG_CONFIRM_E;
            }
#ifndef IGNORE_NAME_CONSTRAINTS
            /* check that this cert's name is permitted by the signer's
             * name constraints */
            if (!ConfirmNameConstraints(ca, cert)) {
                CYASSL_MSG("Confirm name constraint failed");
                return ASN_NAME_INVALID_E;
            }
#endif /* IGNORE_NAME_CONSTRAINTS */
        }
        else {
            /* no signer */
            CYASSL_MSG("No CA signer to verify with");
            return ASN_NO_SIGNER_E;
        }
    }

    if (badDate != 0)
        return badDate;

    if (criticalExt != 0)
        return criticalExt;

    return 0;
}


/* Create and init an new signer */
Signer* MakeSigner(void* heap)
{
    Signer* signer = (Signer*) XMALLOC(sizeof(Signer), heap,
                                       DYNAMIC_TYPE_SIGNER);
    if (signer) {
        signer->pubKeySize = 0;
        signer->keyOID     = 0;
        signer->publicKey  = NULL;
        signer->nameLen    = 0;
        signer->name       = NULL;
        #ifndef IGNORE_NAME_CONSTRAINTS
            signer->permittedNames = NULL;
            signer->excludedNames = NULL;
        #endif /* IGNORE_NAME_CONSTRAINTS */
        signer->next       = NULL;
    }
    (void)heap;

    return signer;
}


/* Free an individual signer */
void FreeSigner(Signer* signer, void* heap)
{
    XFREE(signer->name, heap, DYNAMIC_TYPE_SUBJECT_CN);
    XFREE(signer->publicKey, heap, DYNAMIC_TYPE_PUBLIC_KEY);
    #ifndef IGNORE_NAME_CONSTRAINTS
        if (signer->permittedNames)
            FreeNameSubtrees(signer->permittedNames, heap);
        if (signer->excludedNames)
            FreeNameSubtrees(signer->excludedNames, heap);
    #endif
    XFREE(signer, heap, DYNAMIC_TYPE_SIGNER);

    (void)heap;
}


/* Free the whole singer table with number of rows */
void FreeSignerTable(Signer** table, int rows, void* heap)
{
    int i;

    for (i = 0; i < rows; i++) {
        Signer* signer = table[i];
        while (signer) {
            Signer* next = signer->next;
            FreeSigner(signer, heap);
            signer = next;
        }
        table[i] = NULL;
    }
}


CYASSL_LOCAL int SetMyVersion(word32 version, byte* output, int header)
{
    int i = 0;

    if (header) {
        output[i++] = ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED;
        output[i++] = ASN_BIT_STRING;
    }
    output[i++] = ASN_INTEGER;
    output[i++] = 0x01;
    output[i++] = (byte)version;

    return i;
}


CYASSL_LOCAL int SetSerialNumber(const byte* sn, word32 snSz, byte* output)
{
    int result = 0;

    CYASSL_ENTER("SetSerialNumber");

    if (snSz <= EXTERNAL_SERIAL_SIZE) {
        output[0] = ASN_INTEGER;
        /* The serial number is always positive. When encoding the
         * INTEGER, if the MSB is 1, add a padding zero to keep the
         * number positive. */
        if (sn[0] & 0x80) {
            output[1] = (byte)snSz + 1;
            output[2] = 0;
            XMEMCPY(&output[3], sn, snSz);
            result = snSz + 3;
        }
        else {
            output[1] = (byte)snSz;
            XMEMCPY(&output[2], sn, snSz);
            result = snSz + 2;
        }
    }
    return result;
}




#if defined(CYASSL_KEY_GEN) || defined(CYASSL_CERT_GEN)

/* convert der buffer to pem into output, can't do inplace, der and output
   need to be different */
int DerToPem(const byte* der, word32 derSz, byte* output, word32 outSz,
             int type)
{
#ifdef CYASSL_SMALL_STACK
    char* header = NULL;
    char* footer = NULL;
#else
    char header[80];
    char footer[80];
#endif

    int headerLen = 80;
    int footerLen = 80;
    int i;
    int err;
    int outLen;   /* return length or error */

    if (der == output)      /* no in place conversion */
        return BAD_FUNC_ARG;

#ifdef CYASSL_SMALL_STACK
    header = (char*)XMALLOC(headerLen, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (header == NULL)
        return MEMORY_E;
    
    footer = (char*)XMALLOC(footerLen, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (footer == NULL) {
        XFREE(header, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        return MEMORY_E;
    }
#endif

    if (type == CERT_TYPE) {
        XSTRNCPY(header, "-----BEGIN CERTIFICATE-----\n", headerLen);
        XSTRNCPY(footer, "-----END CERTIFICATE-----\n",   footerLen);
    }
    else if (type == PRIVATEKEY_TYPE) {
        XSTRNCPY(header, "-----BEGIN RSA PRIVATE KEY-----\n", headerLen);
        XSTRNCPY(footer, "-----END RSA PRIVATE KEY-----\n",   footerLen);
    }
    #ifdef HAVE_ECC
    else if (type == ECC_PRIVATEKEY_TYPE) {
        XSTRNCPY(header, "-----BEGIN EC PRIVATE KEY-----\n", headerLen);
        XSTRNCPY(footer, "-----END EC PRIVATE KEY-----\n",   footerLen);
    }
    #endif
    #ifdef CYASSL_CERT_REQ
    else if (type == CERTREQ_TYPE)
    {
        XSTRNCPY(header,
                       "-----BEGIN CERTIFICATE REQUEST-----\n", headerLen);
        XSTRNCPY(footer, "-----END CERTIFICATE REQUEST-----\n", footerLen);
    }
    #endif
    else {
#ifdef CYASSL_SMALL_STACK
        XFREE(header, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(footer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return BAD_FUNC_ARG;
    }

    headerLen = (int)XSTRLEN(header);
    footerLen = (int)XSTRLEN(footer);

    if (!der || !output) {
#ifdef CYASSL_SMALL_STACK
        XFREE(header, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(footer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return BAD_FUNC_ARG;
    }

    /* don't even try if outSz too short */
    if (outSz < headerLen + footerLen + derSz) {
#ifdef CYASSL_SMALL_STACK
        XFREE(header, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(footer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return BAD_FUNC_ARG;
    }

    /* header */
    XMEMCPY(output, header, headerLen);
    i = headerLen;

#ifdef CYASSL_SMALL_STACK
    XFREE(header, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    /* body */
    outLen = outSz - (headerLen + footerLen);  /* input to Base64_Encode */
    if ( (err = Base64_Encode(der, derSz, output + i, (word32*)&outLen)) < 0) {
#ifdef CYASSL_SMALL_STACK
        XFREE(footer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return err;
    }
    i += outLen;

    /* footer */
    if ( (i + footerLen) > (int)outSz) {
#ifdef CYASSL_SMALL_STACK
        XFREE(footer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return BAD_FUNC_ARG;
    }
    XMEMCPY(output + i, footer, footerLen);

#ifdef CYASSL_SMALL_STACK
    XFREE(footer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return outLen + headerLen + footerLen;
}


#endif /* CYASSL_KEY_GEN || CYASSL_CERT_GEN */


#if defined(CYASSL_KEY_GEN) && !defined(NO_RSA)


static mp_int* GetRsaInt(RsaKey* key, int idx)
{
    if (idx == 0)
        return &key->n;
    if (idx == 1)
        return &key->e;
    if (idx == 2)
        return &key->d;
    if (idx == 3)
        return &key->p;
    if (idx == 4)
        return &key->q;
    if (idx == 5)
        return &key->dP;
    if (idx == 6)
        return &key->dQ;
    if (idx == 7)
        return &key->u;

    return NULL;
}


/* Release Tmp RSA resources */
static INLINE void FreeTmpRsas(byte** tmps, void* heap)
{
    int i;

    (void)heap;

    for (i = 0; i < RSA_INTS; i++) 
        XFREE(tmps[i], heap, DYNAMIC_TYPE_RSA);
}


/* Convert RsaKey key to DER format, write to output (inLen), return bytes
   written */
int RsaKeyToDer(RsaKey* key, byte* output, word32 inLen)
{
    word32 seqSz, verSz, rawLen, intTotalLen = 0;
    word32 sizes[RSA_INTS];
    int    i, j, outLen, ret = 0;

    byte  seq[MAX_SEQ_SZ];
    byte  ver[MAX_VERSION_SZ];
    byte* tmps[RSA_INTS];

    if (!key || !output)
        return BAD_FUNC_ARG;

    if (key->type != RSA_PRIVATE)
        return BAD_FUNC_ARG;

    for (i = 0; i < RSA_INTS; i++)
        tmps[i] = NULL;

    /* write all big ints from key to DER tmps */
    for (i = 0; i < RSA_INTS; i++) {
        mp_int* keyInt = GetRsaInt(key, i);
        rawLen = mp_unsigned_bin_size(keyInt);
        tmps[i] = (byte*)XMALLOC(rawLen + MAX_SEQ_SZ, key->heap,
                                 DYNAMIC_TYPE_RSA);
        if (tmps[i] == NULL) {
            ret = MEMORY_E;
            break;
        }

        tmps[i][0] = ASN_INTEGER;
        sizes[i] = SetLength(rawLen, tmps[i] + 1) + 1;  /* int tag */

        if (sizes[i] <= MAX_SEQ_SZ) {
            int err = mp_to_unsigned_bin(keyInt, tmps[i] + sizes[i]);
            if (err == MP_OKAY) {
                sizes[i] += rawLen;
                intTotalLen += sizes[i];
            }
            else {
                ret = err;
                break;
            }
        }
        else {
            ret = ASN_INPUT_E;
            break;
        }
    }

    if (ret != 0) {
        FreeTmpRsas(tmps, key->heap);
        return ret;
    }

    /* make headers */
    verSz = SetMyVersion(0, ver, FALSE);
    seqSz = SetSequence(verSz + intTotalLen, seq);

    outLen = seqSz + verSz + intTotalLen;
    if (outLen > (int)inLen)
        return BAD_FUNC_ARG;

    /* write to output */
    XMEMCPY(output, seq, seqSz);
    j = seqSz;
    XMEMCPY(output + j, ver, verSz);
    j += verSz;

    for (i = 0; i < RSA_INTS; i++) {
        XMEMCPY(output + j, tmps[i], sizes[i]);
        j += sizes[i];
    }
    FreeTmpRsas(tmps, key->heap);

    return outLen;
}

#endif /* CYASSL_KEY_GEN && !NO_RSA */


#if defined(CYASSL_CERT_GEN) && !defined(NO_RSA)


#ifndef min

    static INLINE word32 min(word32 a, word32 b)
    {
        return a > b ? b : a;
    }

#endif /* min */


/* Initialize and Set Certficate defaults:
   version    = 3 (0x2)
   serial     = 0
   sigType    = SHA_WITH_RSA
   issuer     = blank
   daysValid  = 500
   selfSigned = 1 (true) use subject as issuer
   subject    = blank
*/
void InitCert(Cert* cert)
{
    cert->version    = 2;   /* version 3 is hex 2 */
    cert->sigType    = CTC_SHAwRSA;
    cert->daysValid  = 500;
    cert->selfSigned = 1;
    cert->isCA       = 0;
    cert->bodySz     = 0;
#ifdef CYASSL_ALT_NAMES
    cert->altNamesSz   = 0;
    cert->beforeDateSz = 0;
    cert->afterDateSz  = 0;
#endif
    cert->keyType    = RSA_KEY;
    XMEMSET(cert->serial, 0, CTC_SERIAL_SIZE);

    cert->issuer.country[0] = '\0';
    cert->issuer.countryEnc = CTC_PRINTABLE;
    cert->issuer.state[0] = '\0';
    cert->issuer.stateEnc = CTC_UTF8;
    cert->issuer.locality[0] = '\0';
    cert->issuer.localityEnc = CTC_UTF8;
    cert->issuer.sur[0] = '\0';
    cert->issuer.surEnc = CTC_UTF8;
    cert->issuer.org[0] = '\0';
    cert->issuer.orgEnc = CTC_UTF8;
    cert->issuer.unit[0] = '\0';
    cert->issuer.unitEnc = CTC_UTF8;
    cert->issuer.commonName[0] = '\0';
    cert->issuer.commonNameEnc = CTC_UTF8;
    cert->issuer.email[0] = '\0';

    cert->subject.country[0] = '\0';
    cert->subject.countryEnc = CTC_PRINTABLE;
    cert->subject.state[0] = '\0';
    cert->subject.stateEnc = CTC_UTF8;
    cert->subject.locality[0] = '\0';
    cert->subject.localityEnc = CTC_UTF8;
    cert->subject.sur[0] = '\0';
    cert->subject.surEnc = CTC_UTF8;
    cert->subject.org[0] = '\0';
    cert->subject.orgEnc = CTC_UTF8;
    cert->subject.unit[0] = '\0';
    cert->subject.unitEnc = CTC_UTF8;
    cert->subject.commonName[0] = '\0';
    cert->subject.commonNameEnc = CTC_UTF8;
    cert->subject.email[0] = '\0';

#ifdef CYASSL_CERT_REQ
    cert->challengePw[0] ='\0';
#endif
}


/* DER encoded x509 Certificate */
typedef struct DerCert {
    byte size[MAX_LENGTH_SZ];          /* length encoded */
    byte version[MAX_VERSION_SZ];      /* version encoded */
    byte serial[CTC_SERIAL_SIZE + MAX_LENGTH_SZ]; /* serial number encoded */
    byte sigAlgo[MAX_ALGO_SZ];         /* signature algo encoded */
    byte issuer[ASN_NAME_MAX];         /* issuer  encoded */
    byte subject[ASN_NAME_MAX];        /* subject encoded */
    byte validity[MAX_DATE_SIZE*2 + MAX_SEQ_SZ*2];  /* before and after dates */
    byte publicKey[MAX_PUBLIC_KEY_SZ]; /* rsa / ntru public key encoded */
    byte ca[MAX_CA_SZ];                /* basic constraint CA true size */
    byte extensions[MAX_EXTENSIONS_SZ];  /* all extensions */
#ifdef CYASSL_CERT_REQ
    byte attrib[MAX_ATTRIB_SZ];        /* Cert req attributes encoded */
#endif
    int  sizeSz;                       /* encoded size length */
    int  versionSz;                    /* encoded version length */
    int  serialSz;                     /* encoded serial length */
    int  sigAlgoSz;                    /* enocded sig alog length */
    int  issuerSz;                     /* encoded issuer length */
    int  subjectSz;                    /* encoded subject length */
    int  validitySz;                   /* encoded validity length */
    int  publicKeySz;                  /* encoded public key length */
    int  caSz;                         /* encoded CA extension length */
    int  extensionsSz;                 /* encoded extensions total length */
    int  total;                        /* total encoded lengths */
#ifdef CYASSL_CERT_REQ
    int  attribSz;
#endif
} DerCert;


#ifdef CYASSL_CERT_REQ

/* Write a set header to output */
static word32 SetUTF8String(word32 len, byte* output)
{
    output[0] = ASN_UTF8STRING;
    return SetLength(len, output + 1) + 1;
}

#endif /* CYASSL_CERT_REQ */


/* Write a serial number to output */
static int SetSerial(const byte* serial, byte* output)
{
    int length = 0;

    output[length++] = ASN_INTEGER;
    length += SetLength(CTC_SERIAL_SIZE, &output[length]);
    XMEMCPY(&output[length], serial, CTC_SERIAL_SIZE);

    return length + CTC_SERIAL_SIZE;
}


#ifdef HAVE_ECC 

/* Write a public ECC key to output */
static int SetEccPublicKey(byte* output, ecc_key* key)
{
    byte len[MAX_LENGTH_SZ + 1];  /* trailing 0 */
    int  algoSz;
    int  curveSz;
    int  lenSz;
    int  idx;
    word32 pubSz = ECC_BUFSIZE;
#ifdef CYASSL_SMALL_STACK
    byte* algo = NULL;
    byte* curve = NULL;
    byte* pub = NULL;
#else
    byte algo[MAX_ALGO_SZ];
    byte curve[MAX_ALGO_SZ];
    byte pub[ECC_BUFSIZE];
#endif

#ifdef CYASSL_SMALL_STACK
    pub = (byte*)XMALLOC(ECC_BUFSIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (pub == NULL)
        return MEMORY_E;
#endif

    int ret = ecc_export_x963(key, pub, &pubSz);
    if (ret != 0) {
#ifdef CYASSL_SMALL_STACK
        XFREE(pub, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ret;
    }

#ifdef CYASSL_SMALL_STACK
    curve = (byte*)XMALLOC(MAX_ALGO_SZ, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (curve == NULL) {
        XFREE(pub, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        return MEMORY_E;
    }
#endif

    /* headers */
    curveSz = SetCurve(key, curve);
    if (curveSz <= 0) {
#ifdef CYASSL_SMALL_STACK
        XFREE(curve, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(pub,   NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return curveSz;
    }

#ifdef CYASSL_SMALL_STACK
    algo = (byte*)XMALLOC(MAX_ALGO_SZ, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (algo == NULL) {
        XFREE(curve, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(pub,   NULL, DYNAMIC_TYPE_TMP_BUFFER);
        return MEMORY_E;
    }
#endif

    algoSz  = SetAlgoID(ECDSAk, algo, keyType, curveSz);
    lenSz   = SetLength(pubSz + 1, len);
    len[lenSz++] = 0;   /* trailing 0 */

    /* write */
    idx = SetSequence(pubSz + curveSz + lenSz + 1 + algoSz, output);
        /* 1 is for ASN_BIT_STRING */
    /* algo */
    XMEMCPY(output + idx, algo, algoSz);
    idx += algoSz;
    /* curve */
    XMEMCPY(output + idx, curve, curveSz);
    idx += curveSz;
    /* bit string */
    output[idx++] = ASN_BIT_STRING;
    /* length */
    XMEMCPY(output + idx, len, lenSz);
    idx += lenSz;
    /* pub */
    XMEMCPY(output + idx, pub, pubSz);
    idx += pubSz;

#ifdef CYASSL_SMALL_STACK
    XFREE(algo,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(curve, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(pub,   NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return idx;
}


#endif /* HAVE_ECC */


/* Write a public RSA key to output */
static int SetRsaPublicKey(byte* output, RsaKey* key)
{
#ifdef CYASSL_SMALL_STACK
    byte* n = NULL;
    byte* e = NULL;
    byte* algo = NULL;
#else
    byte n[MAX_RSA_INT_SZ];
    byte e[MAX_RSA_E_SZ];
    byte algo[MAX_ALGO_SZ];
#endif
    byte seq[MAX_SEQ_SZ];
    byte len[MAX_LENGTH_SZ + 1];  /* trailing 0 */
    int  nSz;
    int  eSz;
    int  algoSz;
    int  seqSz;
    int  lenSz;
    int  idx;
    int  rawLen;
    int  leadingBit;
    int  err;

    /* n */
#ifdef CYASSL_SMALL_STACK
    n = (byte*)XMALLOC(MAX_RSA_INT_SZ, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (n == NULL)
        return MEMORY_E;
#endif

    leadingBit = mp_leading_bit(&key->n);
    rawLen = mp_unsigned_bin_size(&key->n) + leadingBit;
    n[0] = ASN_INTEGER;
    nSz  = SetLength(rawLen, n + 1) + 1;  /* int tag */

    if ( (nSz + rawLen) < MAX_RSA_INT_SZ) {
        if (leadingBit)
            n[nSz] = 0;
        err = mp_to_unsigned_bin(&key->n, n + nSz + leadingBit);
        if (err == MP_OKAY)
            nSz += rawLen;
        else {
#ifdef CYASSL_SMALL_STACK
            XFREE(n, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return MP_TO_E;
        }
    }
    else {
#ifdef CYASSL_SMALL_STACK
        XFREE(n, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return BUFFER_E;
    }

    /* e */
#ifdef CYASSL_SMALL_STACK
    e = (byte*)XMALLOC(MAX_RSA_E_SZ, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (e == NULL) {
#ifdef CYASSL_SMALL_STACK
        XFREE(n, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return MEMORY_E;
    }
#endif

    leadingBit = mp_leading_bit(&key->e);
    rawLen = mp_unsigned_bin_size(&key->e) + leadingBit;
    e[0] = ASN_INTEGER;
    eSz  = SetLength(rawLen, e + 1) + 1;  /* int tag */

    if ( (eSz + rawLen) < MAX_RSA_E_SZ) {
        if (leadingBit)
            e[eSz] = 0;
        err = mp_to_unsigned_bin(&key->e, e + eSz + leadingBit);
        if (err == MP_OKAY)
            eSz += rawLen;
        else {
#ifdef CYASSL_SMALL_STACK
            XFREE(n, NULL, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(e, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return MP_TO_E;
        }
    }
    else {
#ifdef CYASSL_SMALL_STACK
        XFREE(n, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(e, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return BUFFER_E;
    }

#ifdef CYASSL_SMALL_STACK
    algo = (byte*)XMALLOC(MAX_ALGO_SZ, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (algo == NULL) {
        XFREE(n, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        XFREE(e, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        return MEMORY_E;
    }
#endif

    /* headers */
    algoSz = SetAlgoID(RSAk, algo, keyType, 0);
    seqSz  = SetSequence(nSz + eSz, seq);
    lenSz  = SetLength(seqSz + nSz + eSz + 1, len);
    len[lenSz++] = 0;   /* trailing 0 */

    /* write */
    idx = SetSequence(nSz + eSz + seqSz + lenSz + 1 + algoSz, output);
        /* 1 is for ASN_BIT_STRING */
    /* algo */
    XMEMCPY(output + idx, algo, algoSz);
    idx += algoSz;
    /* bit string */
    output[idx++] = ASN_BIT_STRING;
    /* length */
    XMEMCPY(output + idx, len, lenSz);
    idx += lenSz;
    /* seq */
    XMEMCPY(output + idx, seq, seqSz);
    idx += seqSz;
    /* n */
    XMEMCPY(output + idx, n, nSz);
    idx += nSz;
    /* e */
    XMEMCPY(output + idx, e, eSz);
    idx += eSz;

#ifdef CYASSL_SMALL_STACK
    XFREE(n,    NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(e,    NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(algo, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return idx;
}


static INLINE byte itob(int number)
{
    return (byte)number + 0x30;
}


/* write time to output, format */
static void SetTime(struct tm* date, byte* output)
{
    int i = 0;

    output[i++] = itob((date->tm_year % 10000) / 1000);
    output[i++] = itob((date->tm_year % 1000)  /  100);
    output[i++] = itob((date->tm_year % 100)   /   10);
    output[i++] = itob( date->tm_year % 10);

    output[i++] = itob(date->tm_mon / 10);
    output[i++] = itob(date->tm_mon % 10);

    output[i++] = itob(date->tm_mday / 10);
    output[i++] = itob(date->tm_mday % 10);

    output[i++] = itob(date->tm_hour / 10);
    output[i++] = itob(date->tm_hour % 10);

    output[i++] = itob(date->tm_min / 10);
    output[i++] = itob(date->tm_min % 10);

    output[i++] = itob(date->tm_sec / 10);
    output[i++] = itob(date->tm_sec % 10);
    
    output[i] = 'Z';  /* Zulu profile */
}


#ifdef CYASSL_ALT_NAMES

/* Copy Dates from cert, return bytes written */
static int CopyValidity(byte* output, Cert* cert)
{
    int seqSz;

    CYASSL_ENTER("CopyValidity");

    /* headers and output */
    seqSz = SetSequence(cert->beforeDateSz + cert->afterDateSz, output);
    XMEMCPY(output + seqSz, cert->beforeDate, cert->beforeDateSz);
    XMEMCPY(output + seqSz + cert->beforeDateSz, cert->afterDate,
                                                 cert->afterDateSz);
    return seqSz + cert->beforeDateSz + cert->afterDateSz;
}

#endif


/* Set Date validity from now until now + daysValid */
static int SetValidity(byte* output, int daysValid)
{
    byte before[MAX_DATE_SIZE];
    byte  after[MAX_DATE_SIZE];

    int beforeSz;
    int afterSz;
    int seqSz;

    time_t     ticks;
    struct tm* now;
    struct tm  local;

    ticks = XTIME(0);
    now   = XGMTIME(&ticks);

    /* before now */
    local = *now;
    before[0] = ASN_GENERALIZED_TIME;
    beforeSz  = SetLength(ASN_GEN_TIME_SZ, before + 1) + 1;  /* gen tag */

    /* subtract 1 day for more compliance */
    local.tm_mday -= 1;
    mktime(&local);

    /* adjust */
    local.tm_year += 1900;
    local.tm_mon  +=    1;

    SetTime(&local, before + beforeSz);
    beforeSz += ASN_GEN_TIME_SZ;
    
    /* after now + daysValid */
    local = *now;
    after[0] = ASN_GENERALIZED_TIME;
    afterSz  = SetLength(ASN_GEN_TIME_SZ, after + 1) + 1;  /* gen tag */

    /* add daysValid */
    local.tm_mday += daysValid;
    mktime(&local);

    /* adjust */
    local.tm_year += 1900;
    local.tm_mon  +=    1;

    SetTime(&local, after + afterSz);
    afterSz += ASN_GEN_TIME_SZ;

    /* headers and output */
    seqSz = SetSequence(beforeSz + afterSz, output);
    XMEMCPY(output + seqSz, before, beforeSz);
    XMEMCPY(output + seqSz + beforeSz, after, afterSz);

    return seqSz + beforeSz + afterSz;
}


/* ASN Encoded Name field */
typedef struct EncodedName {
    int  nameLen;                /* actual string value length */
    int  totalLen;               /* total encoded length */
    int  type;                   /* type of name */
    int  used;                   /* are we actually using this one */
    byte encoded[CTC_NAME_SIZE * 2]; /* encoding */
} EncodedName;


/* Get Which Name from index */
static const char* GetOneName(CertName* name, int idx)
{
    switch (idx) {
    case 0:
       return name->country;

    case 1:
       return name->state;

    case 2:
       return name->locality;

    case 3:
       return name->sur;

    case 4:
       return name->org;

    case 5:
       return name->unit;

    case 6:
       return name->commonName;

    case 7:
       return name->email;

    default:
       return 0;
    }
}


/* Get Which Name Encoding from index */
static char GetNameType(CertName* name, int idx)
{
    switch (idx) {
    case 0:
       return name->countryEnc;

    case 1:
       return name->stateEnc;

    case 2:
       return name->localityEnc;

    case 3:
       return name->surEnc;

    case 4:
       return name->orgEnc;

    case 5:
       return name->unitEnc;

    case 6:
       return name->commonNameEnc;

    default:
       return 0;
    }
}


/* Get ASN Name from index */
static byte GetNameId(int idx)
{
    switch (idx) {
    case 0:
       return ASN_COUNTRY_NAME;

    case 1:
       return ASN_STATE_NAME;

    case 2:
       return ASN_LOCALITY_NAME;

    case 3:
       return ASN_SUR_NAME;

    case 4:
       return ASN_ORG_NAME;

    case 5:
       return ASN_ORGUNIT_NAME;

    case 6:
       return ASN_COMMON_NAME;

    case 7:
       /* email uses different id type */
       return 0;

    default:
       return 0;
    }
}


/* encode all extensions, return total bytes written */
static int SetExtensions(byte* output, const byte* ext, int extSz, int header)
{
    byte sequence[MAX_SEQ_SZ];
    byte len[MAX_LENGTH_SZ];

    int sz = 0;
    int seqSz = SetSequence(extSz, sequence);

    if (header) {
        int lenSz = SetLength(seqSz + extSz, len);
        output[0] = ASN_EXTENSIONS; /* extensions id */
        sz++;
        XMEMCPY(&output[sz], len, lenSz);  /* length */
        sz += lenSz;
    }
    XMEMCPY(&output[sz], sequence, seqSz);  /* sequence */
    sz += seqSz;
    XMEMCPY(&output[sz], ext, extSz);  /* extensions */
    sz += extSz;

    return sz;
}


/* encode CA basic constraint true, return total bytes written */
static int SetCa(byte* output)
{
    static const byte ca[] = { 0x30, 0x0c, 0x06, 0x03, 0x55, 0x1d, 0x13, 0x04,
                               0x05, 0x30, 0x03, 0x01, 0x01, 0xff };
    
    XMEMCPY(output, ca, sizeof(ca));

    return (int)sizeof(ca);
}


/* encode CertName into output, return total bytes written */
static int SetName(byte* output, CertName* name)
{
    int          totalBytes = 0, i, idx;
#ifdef CYASSL_SMALL_STACK
    EncodedName* names = NULL;
#else
    EncodedName  names[NAME_ENTRIES];
#endif

#ifdef CYASSL_SMALL_STACK
    names = (EncodedName*)XMALLOC(sizeof(EncodedName) * NAME_ENTRIES, NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (names == NULL)
        return MEMORY_E;
#endif

    for (i = 0; i < NAME_ENTRIES; i++) {
        const char* nameStr = GetOneName(name, i);
        if (nameStr) {
            /* bottom up */
            byte firstLen[MAX_LENGTH_SZ];
            byte secondLen[MAX_LENGTH_SZ];
            byte sequence[MAX_SEQ_SZ];
            byte set[MAX_SET_SZ];

            int email = i == (NAME_ENTRIES - 1) ? 1 : 0;
            int strLen  = (int)XSTRLEN(nameStr);
            int thisLen = strLen;
            int firstSz, secondSz, seqSz, setSz;

            if (strLen == 0) { /* no user data for this item */
                names[i].used = 0;
                continue;
            }

            secondSz = SetLength(strLen, secondLen);
            thisLen += secondSz;
            if (email) {
                thisLen += EMAIL_JOINT_LEN;
                thisLen ++;                               /* id type */
                firstSz  = SetLength(EMAIL_JOINT_LEN, firstLen);
            }
            else {
                thisLen++;                                 /* str type */
                thisLen++;                                 /* id  type */
                thisLen += JOINT_LEN;    
                firstSz = SetLength(JOINT_LEN + 1, firstLen);
            }
            thisLen += firstSz;
            thisLen++;                                /* object id */

            seqSz = SetSequence(thisLen, sequence);
            thisLen += seqSz;
            setSz = SetSet(thisLen, set);
            thisLen += setSz;

            if (thisLen > (int)sizeof(names[i].encoded)) {
#ifdef CYASSL_SMALL_STACK
                XFREE(names, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
                return BUFFER_E;
            }

            /* store it */
            idx = 0;
            /* set */
            XMEMCPY(names[i].encoded, set, setSz);
            idx += setSz;
            /* seq */
            XMEMCPY(names[i].encoded + idx, sequence, seqSz);
            idx += seqSz;
            /* asn object id */
            names[i].encoded[idx++] = ASN_OBJECT_ID;
            /* first length */
            XMEMCPY(names[i].encoded + idx, firstLen, firstSz);
            idx += firstSz;
            if (email) {
                const byte EMAIL_OID[] = { 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d,
                                           0x01, 0x09, 0x01, 0x16 };
                /* email joint id */
                XMEMCPY(names[i].encoded + idx, EMAIL_OID, sizeof(EMAIL_OID));
                idx += (int)sizeof(EMAIL_OID);
            }
            else {
                /* joint id */
                byte bType = GetNameId(i);
                names[i].encoded[idx++] = 0x55;
                names[i].encoded[idx++] = 0x04;
                /* id type */
                names[i].encoded[idx++] = bType; 
                /* str type */
                names[i].encoded[idx++] = GetNameType(name, i);
            }
            /* second length */
            XMEMCPY(names[i].encoded + idx, secondLen, secondSz);
            idx += secondSz;
            /* str value */
            XMEMCPY(names[i].encoded + idx, nameStr, strLen);
            idx += strLen;

            totalBytes += idx;
            names[i].totalLen = idx;
            names[i].used = 1;
        }
        else
            names[i].used = 0;
    }

    /* header */
    idx = SetSequence(totalBytes, output);
    totalBytes += idx;
    if (totalBytes > ASN_NAME_MAX) {
#ifdef CYASSL_SMALL_STACK
        XFREE(names, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return BUFFER_E;
    }

    for (i = 0; i < NAME_ENTRIES; i++) {
        if (names[i].used) {
            XMEMCPY(output + idx, names[i].encoded, names[i].totalLen);
            idx += names[i].totalLen;
        }
    }

#ifdef CYASSL_SMALL_STACK
    XFREE(names, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return totalBytes;
}

/* encode info from cert into DER encoded format */
static int EncodeCert(Cert* cert, DerCert* der, RsaKey* rsaKey, ecc_key* eccKey,
                      RNG* rng, const byte* ntruKey, word16 ntruSz)
{
    int ret;

    (void)eccKey;
    (void)ntruKey;
    (void)ntruSz;

    /* init */
    XMEMSET(der, 0, sizeof(DerCert));

    /* version */
    der->versionSz = SetMyVersion(cert->version, der->version, TRUE);

    /* serial number */
    ret = RNG_GenerateBlock(rng, cert->serial, CTC_SERIAL_SIZE);
    if (ret != 0)
        return ret;

    cert->serial[0] = 0x01;   /* ensure positive */
    der->serialSz  = SetSerial(cert->serial, der->serial);

    /* signature algo */
    der->sigAlgoSz = SetAlgoID(cert->sigType, der->sigAlgo, sigType, 0);
    if (der->sigAlgoSz == 0)
        return ALGO_ID_E;

    /* public key */
    if (cert->keyType == RSA_KEY) {
        if (rsaKey == NULL)
            return PUBLIC_KEY_E;
        der->publicKeySz = SetRsaPublicKey(der->publicKey, rsaKey);
        if (der->publicKeySz <= 0)
            return PUBLIC_KEY_E;
    }

#ifdef HAVE_ECC
    if (cert->keyType == ECC_KEY) {
        if (eccKey == NULL)
            return PUBLIC_KEY_E;
        der->publicKeySz = SetEccPublicKey(der->publicKey, eccKey);
        if (der->publicKeySz <= 0)
            return PUBLIC_KEY_E;
    }
#endif /* HAVE_ECC */

#ifdef HAVE_NTRU
    if (cert->keyType == NTRU_KEY) {
        word32 rc;
        word16 encodedSz;

        rc  = ntru_crypto_ntru_encrypt_publicKey2SubjectPublicKeyInfo( ntruSz,
                                                   ntruKey, &encodedSz, NULL);
        if (rc != NTRU_OK)
            return PUBLIC_KEY_E;
        if (encodedSz > MAX_PUBLIC_KEY_SZ)
            return PUBLIC_KEY_E;

        rc  = ntru_crypto_ntru_encrypt_publicKey2SubjectPublicKeyInfo( ntruSz,
                                         ntruKey, &encodedSz, der->publicKey);
        if (rc != NTRU_OK)
            return PUBLIC_KEY_E;

        der->publicKeySz = encodedSz;
    }
#endif /* HAVE_NTRU */

    der->validitySz = 0;
#ifdef CYASSL_ALT_NAMES
    /* date validity copy ? */
    if (cert->beforeDateSz && cert->afterDateSz) {
        der->validitySz = CopyValidity(der->validity, cert);
        if (der->validitySz == 0)
            return DATE_E;
    }
#endif

    /* date validity */
    if (der->validitySz == 0) {
        der->validitySz = SetValidity(der->validity, cert->daysValid);
        if (der->validitySz == 0)
            return DATE_E;
    }

    /* subject name */
    der->subjectSz = SetName(der->subject, &cert->subject);
    if (der->subjectSz == 0)
        return SUBJECT_E;

    /* issuer name */
    der->issuerSz = SetName(der->issuer, cert->selfSigned ?
             &cert->subject : &cert->issuer);
    if (der->issuerSz == 0)
        return ISSUER_E;

    /* CA */
    if (cert->isCA) {
        der->caSz = SetCa(der->ca);
        if (der->caSz == 0)
            return CA_TRUE_E;
    }
    else
        der->caSz = 0;

    /* extensions, just CA now */
    if (cert->isCA) {
        der->extensionsSz = SetExtensions(der->extensions,
                                          der->ca, der->caSz, TRUE);
        if (der->extensionsSz == 0)
            return EXTENSIONS_E;
    }
    else
        der->extensionsSz = 0;

#ifdef CYASSL_ALT_NAMES
    if (der->extensionsSz == 0 && cert->altNamesSz) {
        der->extensionsSz = SetExtensions(der->extensions, cert->altNames,
                                          cert->altNamesSz, TRUE);
        if (der->extensionsSz == 0)
            return EXTENSIONS_E;
    }
#endif

    der->total = der->versionSz + der->serialSz + der->sigAlgoSz +
        der->publicKeySz + der->validitySz + der->subjectSz + der->issuerSz +
        der->extensionsSz;

    return 0;
}


/* write DER encoded cert to buffer, size already checked */
static int WriteCertBody(DerCert* der, byte* buffer)
{
    int idx;

    /* signed part header */
    idx = SetSequence(der->total, buffer);
    /* version */
    XMEMCPY(buffer + idx, der->version, der->versionSz);
    idx += der->versionSz;
    /* serial */
    XMEMCPY(buffer + idx, der->serial, der->serialSz);
    idx += der->serialSz;
    /* sig algo */
    XMEMCPY(buffer + idx, der->sigAlgo, der->sigAlgoSz);
    idx += der->sigAlgoSz;
    /* issuer */
    XMEMCPY(buffer + idx, der->issuer, der->issuerSz);
    idx += der->issuerSz;
    /* validity */
    XMEMCPY(buffer + idx, der->validity, der->validitySz);
    idx += der->validitySz;
    /* subject */
    XMEMCPY(buffer + idx, der->subject, der->subjectSz);
    idx += der->subjectSz;
    /* public key */
    XMEMCPY(buffer + idx, der->publicKey, der->publicKeySz);
    idx += der->publicKeySz;
    if (der->extensionsSz) {
        /* extensions */
        XMEMCPY(buffer + idx, der->extensions, min(der->extensionsSz,
                                                   sizeof(der->extensions)));
        idx += der->extensionsSz;
    }

    return idx;
}


/* Make RSA signature from buffer (sz), write to sig (sigSz) */
static int MakeSignature(const byte* buffer, int sz, byte* sig, int sigSz,
                         RsaKey* rsaKey, ecc_key* eccKey, RNG* rng,
                         int sigAlgoType)
{
    int encSigSz, digestSz, typeH = 0, ret = 0;
    byte digest[SHA256_DIGEST_SIZE]; /* max size */
#ifdef CYASSL_SMALL_STACK
    byte* encSig;
#else
    byte encSig[MAX_ENCODED_DIG_SZ + MAX_ALGO_SZ + MAX_SEQ_SZ];
#endif

    (void)digest;
    (void)digestSz;
    (void)encSig;
    (void)encSigSz;
    (void)typeH;

    (void)buffer;
    (void)sz;
    (void)sig;
    (void)sigSz;
    (void)rsaKey;
    (void)eccKey;
    (void)rng;

    switch (sigAlgoType) {
    #ifndef NO_MD5
        case CTC_MD5wRSA:
        if ((ret = Md5Hash(buffer, sz, digest)) == 0) {
            typeH    = MD5h;
            digestSz = MD5_DIGEST_SIZE;
        }
        break;
    #endif
    #ifndef NO_SHA
        case CTC_SHAwRSA:
        case CTC_SHAwECDSA:
        if ((ret = ShaHash(buffer, sz, digest)) == 0) {
            typeH    = SHAh;
            digestSz = SHA_DIGEST_SIZE;          
        }
        break;
    #endif
    #ifndef NO_SHA256
        case CTC_SHA256wRSA:
        case CTC_SHA256wECDSA:
        if ((ret = Sha256Hash(buffer, sz, digest)) == 0) {
            typeH    = SHA256h;
            digestSz = SHA256_DIGEST_SIZE;
        }
        break;
    #endif
        default:
            CYASSL_MSG("MakeSignautre called with unsupported type");
            ret = ALGO_ID_E;
    }
    
    if (ret != 0)
        return ret;
    
#ifdef CYASSL_SMALL_STACK
    encSig = (byte*)XMALLOC(MAX_ENCODED_DIG_SZ + MAX_ALGO_SZ + MAX_SEQ_SZ,
                                                 NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (encSig == NULL)
        return MEMORY_E;
#endif
    
    ret = ALGO_ID_E;
    
#ifndef NO_RSA
    if (rsaKey) {
        /* signature */
        encSigSz = EncodeSignature(encSig, digest, digestSz, typeH);
        ret = RsaSSL_Sign(encSig, encSigSz, sig, sigSz, rsaKey, rng);
    }
#endif
    
#ifdef HAVE_ECC
    if (!rsaKey && eccKey) {
        word32 outSz = sigSz;
        ret = ecc_sign_hash(digest, digestSz, sig, &outSz, rng, eccKey);

        if (ret == 0)
            ret = outSz;
    }
#endif

#ifdef CYASSL_SMALL_STACK
    XFREE(encSig, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}


/* add signature to end of buffer, size of buffer assumed checked, return
   new length */
static int AddSignature(byte* buffer, int bodySz, const byte* sig, int sigSz,
                        int sigAlgoType)
{
    byte seq[MAX_SEQ_SZ];
    int  idx = bodySz, seqSz;

    /* algo */
    idx += SetAlgoID(sigAlgoType, buffer + idx, sigType, 0);
    /* bit string */
    buffer[idx++] = ASN_BIT_STRING;
    /* length */
    idx += SetLength(sigSz + 1, buffer + idx);
    buffer[idx++] = 0;   /* trailing 0 */
    /* signature */
    XMEMCPY(buffer + idx, sig, sigSz);
    idx += sigSz;

    /* make room for overall header */
    seqSz = SetSequence(idx, seq);
    XMEMMOVE(buffer + seqSz, buffer, idx);
    XMEMCPY(buffer, seq, seqSz);

    return idx + seqSz;
}


/* Make an x509 Certificate v3 any key type from cert input, write to buffer */
static int MakeAnyCert(Cert* cert, byte* derBuffer, word32 derSz,
                       RsaKey* rsaKey, ecc_key* eccKey, RNG* rng,
                       const byte* ntruKey, word16 ntruSz)
{
    int ret;
#ifdef CYASSL_SMALL_STACK
    DerCert* der;
#else
    DerCert der[1];
#endif

    cert->keyType = eccKey ? ECC_KEY : (rsaKey ? RSA_KEY : NTRU_KEY);

#ifdef CYASSL_SMALL_STACK
    der = (DerCert*)XMALLOC(sizeof(DerCert), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (der == NULL)
        return MEMORY_E;
#endif

    ret = EncodeCert(cert, der, rsaKey, eccKey, rng, ntruKey, ntruSz);

    if (ret == 0) {
        if (der->total + MAX_SEQ_SZ * 2 > (int)derSz)
            ret = BUFFER_E;
        else
            ret = cert->bodySz = WriteCertBody(der, derBuffer);
    }

#ifdef CYASSL_SMALL_STACK
    XFREE(der, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}


/* Make an x509 Certificate v3 RSA or ECC from cert input, write to buffer */
int MakeCert(Cert* cert, byte* derBuffer, word32 derSz, RsaKey* rsaKey,
             ecc_key* eccKey, RNG* rng)
{
    return MakeAnyCert(cert, derBuffer, derSz, rsaKey, eccKey, rng, NULL, 0);
}


#ifdef HAVE_NTRU

int  MakeNtruCert(Cert* cert, byte* derBuffer, word32 derSz,
                  const byte* ntruKey, word16 keySz, RNG* rng)
{
    return MakeAnyCert(cert, derBuffer, derSz, NULL, NULL, rng, ntruKey, keySz);
}

#endif /* HAVE_NTRU */


#ifdef CYASSL_CERT_REQ

static int SetReqAttrib(byte* output, char* pw, int extSz)
{
    static const byte cpOid[] =
        { ASN_OBJECT_ID, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01,
                         0x09, 0x07 };
    static const byte erOid[] =
        { ASN_OBJECT_ID, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01,
                         0x09, 0x0e };

    int sz      = 0; /* overall size */
    int cpSz    = 0; /* Challenge Password section size */
    int cpSeqSz = 0;
    int cpSetSz = 0;
    int cpStrSz = 0;
    int pwSz    = 0;
    int erSz    = 0; /* Extension Request section size */
    int erSeqSz = 0;
    int erSetSz = 0;
    byte cpSeq[MAX_SEQ_SZ];
    byte cpSet[MAX_SET_SZ];
    byte cpStr[MAX_PRSTR_SZ];
    byte erSeq[MAX_SEQ_SZ];
    byte erSet[MAX_SET_SZ];

    output[0] = 0xa0;
    sz++;

    if (pw && pw[0]) {
        pwSz = (int)XSTRLEN(pw);
        cpStrSz = SetUTF8String(pwSz, cpStr);
        cpSetSz = SetSet(cpStrSz + pwSz, cpSet);
        cpSeqSz = SetSequence(sizeof(cpOid) + cpSetSz + cpStrSz + pwSz, cpSeq);
        cpSz = cpSeqSz + sizeof(cpOid) + cpSetSz + cpStrSz + pwSz;
    }

    if (extSz) {
        erSetSz = SetSet(extSz, erSet);
        erSeqSz = SetSequence(erSetSz + sizeof(erOid) + extSz, erSeq);
        erSz = extSz + erSetSz + erSeqSz + sizeof(erOid);
    }

    /* Put the pieces together. */
    sz += SetLength(cpSz + erSz, &output[sz]);

    if (cpSz) {
        XMEMCPY(&output[sz], cpSeq, cpSeqSz);
        sz += cpSeqSz;
        XMEMCPY(&output[sz], cpOid, sizeof(cpOid));
        sz += sizeof(cpOid);
        XMEMCPY(&output[sz], cpSet, cpSetSz);
        sz += cpSetSz;
        XMEMCPY(&output[sz], cpStr, cpStrSz);
        sz += cpStrSz;
        XMEMCPY(&output[sz], pw, pwSz);
        sz += pwSz;
    }

    if (erSz) {
        XMEMCPY(&output[sz], erSeq, erSeqSz);
        sz += erSeqSz;
        XMEMCPY(&output[sz], erOid, sizeof(erOid));
        sz += sizeof(erOid);
        XMEMCPY(&output[sz], erSet, erSetSz);
        sz += erSetSz;
        /* The actual extension data will be tacked onto the output later. */
    }

    return sz;
}


/* encode info from cert into DER encoded format */
static int EncodeCertReq(Cert* cert, DerCert* der,
                         RsaKey* rsaKey, ecc_key* eccKey)
{
    (void)eccKey;

    /* init */
    XMEMSET(der, 0, sizeof(DerCert));

    /* version */
    der->versionSz = SetMyVersion(cert->version, der->version, FALSE);

    /* subject name */
    der->subjectSz = SetName(der->subject, &cert->subject);
    if (der->subjectSz == 0)
        return SUBJECT_E;

    /* public key */
    if (cert->keyType == RSA_KEY) {
        if (rsaKey == NULL)
            return PUBLIC_KEY_E;
        der->publicKeySz = SetRsaPublicKey(der->publicKey, rsaKey);
        if (der->publicKeySz <= 0)
            return PUBLIC_KEY_E;
    }

#ifdef HAVE_ECC
    if (cert->keyType == ECC_KEY) {
        if (eccKey == NULL)
            return PUBLIC_KEY_E;
        der->publicKeySz = SetEccPublicKey(der->publicKey, eccKey);
        if (der->publicKeySz <= 0)
            return PUBLIC_KEY_E;
    }
#endif /* HAVE_ECC */

    /* CA */
    if (cert->isCA) {
        der->caSz = SetCa(der->ca);
        if (der->caSz == 0)
            return CA_TRUE_E;
    }
    else
        der->caSz = 0;

    /* extensions, just CA now */
    if (cert->isCA) {
        der->extensionsSz = SetExtensions(der->extensions,
                                          der->ca, der->caSz, FALSE);
        if (der->extensionsSz == 0)
            return EXTENSIONS_E;
    }
    else
        der->extensionsSz = 0;

    der->attribSz = SetReqAttrib(der->attrib,
                                 cert->challengePw, der->extensionsSz);
    if (der->attribSz == 0)
        return REQ_ATTRIBUTE_E;

    der->total = der->versionSz + der->subjectSz + der->publicKeySz +
        der->extensionsSz + der->attribSz;

    return 0;
}


/* write DER encoded cert req to buffer, size already checked */
static int WriteCertReqBody(DerCert* der, byte* buffer)
{
    int idx;

    /* signed part header */
    idx = SetSequence(der->total, buffer);
    /* version */
    XMEMCPY(buffer + idx, der->version, der->versionSz);
    idx += der->versionSz;
    /* subject */
    XMEMCPY(buffer + idx, der->subject, der->subjectSz);
    idx += der->subjectSz;
    /* public key */
    XMEMCPY(buffer + idx, der->publicKey, der->publicKeySz);
    idx += der->publicKeySz;
    /* attributes */
    XMEMCPY(buffer + idx, der->attrib, der->attribSz);
    idx += der->attribSz;
    /* extensions */
    if (der->extensionsSz) {
        XMEMCPY(buffer + idx, der->extensions, min(der->extensionsSz,
                                                   sizeof(der->extensions)));
        idx += der->extensionsSz;
    }

    return idx;
}


int MakeCertReq(Cert* cert, byte* derBuffer, word32 derSz,
                RsaKey* rsaKey, ecc_key* eccKey)
{
    int ret;
#ifdef CYASSL_SMALL_STACK
    DerCert* der;
#else
    DerCert der[1];
#endif

    cert->keyType = eccKey ? ECC_KEY : RSA_KEY;

#ifdef CYASSL_SMALL_STACK
    der = (DerCert*)XMALLOC(sizeof(DerCert), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (der == NULL)
        return MEMORY_E;
#endif

    ret = EncodeCertReq(cert, der, rsaKey, eccKey);

    if (ret == 0) {
        if (der->total + MAX_SEQ_SZ * 2 > (int)derSz)
            ret = BUFFER_E;
        else
            ret = cert->bodySz = WriteCertReqBody(der, derBuffer);
    }

#ifdef CYASSL_SMALL_STACK
    XFREE(der, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

#endif /* CYASSL_CERT_REQ */


int SignCert(int requestSz, int sType, byte* buffer, word32 buffSz,
             RsaKey* rsaKey, ecc_key* eccKey, RNG* rng)
{
    int sigSz;
#ifdef CYASSL_SMALL_STACK
    byte* sig;
#else
    byte sig[MAX_ENCODED_SIG_SZ];
#endif

    if (requestSz < 0)
        return requestSz;

#ifdef CYASSL_SMALL_STACK
    sig = (byte*)XMALLOC(MAX_ENCODED_SIG_SZ, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (sig == NULL)
        return MEMORY_E;
#endif

    sigSz = MakeSignature(buffer, requestSz, sig, MAX_ENCODED_SIG_SZ, rsaKey,
                          eccKey, rng, sType);

    if (sigSz >= 0) {
        if (requestSz + MAX_SEQ_SZ * 2 + sigSz > (int)buffSz)
            sigSz = BUFFER_E;
        else
            sigSz = AddSignature(buffer, requestSz, sig, sigSz, sType);
    }
    
#ifdef CYASSL_SMALL_STACK
    XFREE(sig, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return sigSz;
}


int MakeSelfCert(Cert* cert, byte* buffer, word32 buffSz, RsaKey* key, RNG* rng)
{
    int ret = MakeCert(cert, buffer, buffSz, key, NULL, rng);

    if (ret < 0)
        return ret;

    return SignCert(cert->bodySz, cert->sigType, buffer, buffSz, key, NULL,rng);
}


#ifdef CYASSL_ALT_NAMES 

/* Set Alt Names from der cert, return 0 on success */
static int SetAltNamesFromCert(Cert* cert, const byte* der, int derSz)
{
    int ret;
#ifdef CYASSL_SMALL_STACK
    DecodedCert* decoded;
#else
    DecodedCert decoded[1];
#endif

    if (derSz < 0)
        return derSz;

#ifdef CYASSL_SMALL_STACK
    decoded = (DecodedCert*)XMALLOC(sizeof(DecodedCert), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (decoded == NULL)
        return MEMORY_E;
#endif
    
    InitDecodedCert(decoded, (byte*)der, derSz, 0);
    ret = ParseCertRelative(decoded, CA_TYPE, NO_VERIFY, 0);

    if (ret < 0) {
        CYASSL_MSG("ParseCertRelative error");
    }
    else if (decoded->extensions) {
        byte   b;
        int    length;
        word32 maxExtensionsIdx;

        decoded->srcIdx = decoded->extensionsIdx;
        b = decoded->source[decoded->srcIdx++];
        
        if (b != ASN_EXTENSIONS) {
            ret = ASN_PARSE_E;
        }
        else if (GetLength(decoded->source, &decoded->srcIdx, &length,
                                                         decoded->maxIdx) < 0) {
            ret = ASN_PARSE_E;
        }
        else if (GetSequence(decoded->source, &decoded->srcIdx, &length,
                                                         decoded->maxIdx) < 0) {
            ret = ASN_PARSE_E;
        }
        else {
            maxExtensionsIdx = decoded->srcIdx + length;

            while (decoded->srcIdx < maxExtensionsIdx) {
                word32 oid;
                word32 startIdx = decoded->srcIdx;
                word32 tmpIdx;

                if (GetSequence(decoded->source, &decoded->srcIdx, &length,
                            decoded->maxIdx) < 0) {
                    ret = ASN_PARSE_E;
                    break;
                }

                tmpIdx = decoded->srcIdx;
                decoded->srcIdx = startIdx;

                if (GetAlgoId(decoded->source, &decoded->srcIdx, &oid,
                              decoded->maxIdx) < 0) {
                    ret = ASN_PARSE_E;
                    break;
                }

                if (oid == ALT_NAMES_OID) {
                    cert->altNamesSz = length + (tmpIdx - startIdx);

                    if (cert->altNamesSz < (int)sizeof(cert->altNames))
                        XMEMCPY(cert->altNames, &decoded->source[startIdx],
                                cert->altNamesSz);
                    else {
                        cert->altNamesSz = 0;
                        CYASSL_MSG("AltNames extensions too big");
                        ret = ALT_NAME_E;
                        break;
                    }
                }
                decoded->srcIdx = tmpIdx + length;
            }
        }
    }

    FreeDecodedCert(decoded);
#ifdef CYASSL_SMALL_STACK
    XFREE(decoded, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret < 0 ? ret : 0;
}


/* Set Dates from der cert, return 0 on success */
static int SetDatesFromCert(Cert* cert, const byte* der, int derSz)
{
    int ret;
#ifdef CYASSL_SMALL_STACK
    DecodedCert* decoded;
#else
    DecodedCert decoded[1];
#endif

    CYASSL_ENTER("SetDatesFromCert");
    if (derSz < 0)
        return derSz;
    
#ifdef CYASSL_SMALL_STACK
    decoded = (DecodedCert*)XMALLOC(sizeof(DecodedCert), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (decoded == NULL)
        return MEMORY_E;
#endif

    InitDecodedCert(decoded, (byte*)der, derSz, 0);
    ret = ParseCertRelative(decoded, CA_TYPE, NO_VERIFY, 0);

    if (ret < 0) {
        CYASSL_MSG("ParseCertRelative error");
    }
    else if (decoded->beforeDate == NULL || decoded->afterDate == NULL) {
        CYASSL_MSG("Couldn't extract dates");
        ret = -1;
    }
    else if (decoded->beforeDateLen > MAX_DATE_SIZE || 
                                        decoded->afterDateLen > MAX_DATE_SIZE) {
        CYASSL_MSG("Bad date size");
        ret = -1;
    }
    else {
        XMEMCPY(cert->beforeDate, decoded->beforeDate, decoded->beforeDateLen);
        XMEMCPY(cert->afterDate,  decoded->afterDate,  decoded->afterDateLen);

        cert->beforeDateSz = decoded->beforeDateLen;
        cert->afterDateSz  = decoded->afterDateLen;
    }

    FreeDecodedCert(decoded);

#ifdef CYASSL_SMALL_STACK
    XFREE(decoded, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret < 0 ? ret : 0;
}


#endif /* CYASSL_ALT_NAMES && !NO_RSA */


/* Set cn name from der buffer, return 0 on success */
static int SetNameFromCert(CertName* cn, const byte* der, int derSz)
{
    int ret, sz;
#ifdef CYASSL_SMALL_STACK
    DecodedCert* decoded;
#else
    DecodedCert decoded[1];
#endif

    if (derSz < 0)
        return derSz;

#ifdef CYASSL_SMALL_STACK
    decoded = (DecodedCert*)XMALLOC(sizeof(DecodedCert), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (decoded == NULL)
        return MEMORY_E;
#endif

    InitDecodedCert(decoded, (byte*)der, derSz, 0);
    ret = ParseCertRelative(decoded, CA_TYPE, NO_VERIFY, 0);

    if (ret < 0) {
        CYASSL_MSG("ParseCertRelative error");
    }
    else {
        if (decoded->subjectCN) {
            sz = (decoded->subjectCNLen < CTC_NAME_SIZE) ? decoded->subjectCNLen
                                                         : CTC_NAME_SIZE - 1;
            strncpy(cn->commonName, decoded->subjectCN, CTC_NAME_SIZE);
            cn->commonName[sz] = 0;
            cn->commonNameEnc = decoded->subjectCNEnc;
        }
        if (decoded->subjectC) {
            sz = (decoded->subjectCLen < CTC_NAME_SIZE) ? decoded->subjectCLen
                                                        : CTC_NAME_SIZE - 1;
            strncpy(cn->country, decoded->subjectC, CTC_NAME_SIZE);
            cn->country[sz] = 0;
            cn->countryEnc = decoded->subjectCEnc;
        }
        if (decoded->subjectST) {
            sz = (decoded->subjectSTLen < CTC_NAME_SIZE) ? decoded->subjectSTLen
                                                         : CTC_NAME_SIZE - 1;
            strncpy(cn->state, decoded->subjectST, CTC_NAME_SIZE);
            cn->state[sz] = 0;
            cn->stateEnc = decoded->subjectSTEnc;
        }
        if (decoded->subjectL) {
            sz = (decoded->subjectLLen < CTC_NAME_SIZE) ? decoded->subjectLLen
                                                        : CTC_NAME_SIZE - 1;
            strncpy(cn->locality, decoded->subjectL, CTC_NAME_SIZE);
            cn->locality[sz] = 0;
            cn->localityEnc = decoded->subjectLEnc;
        }
        if (decoded->subjectO) {
            sz = (decoded->subjectOLen < CTC_NAME_SIZE) ? decoded->subjectOLen
                                                        : CTC_NAME_SIZE - 1;
            strncpy(cn->org, decoded->subjectO, CTC_NAME_SIZE);
            cn->org[sz] = 0;
            cn->orgEnc = decoded->subjectOEnc;
        }
        if (decoded->subjectOU) {
            sz = (decoded->subjectOULen < CTC_NAME_SIZE) ? decoded->subjectOULen
                                                         : CTC_NAME_SIZE - 1;
            strncpy(cn->unit, decoded->subjectOU, CTC_NAME_SIZE);
            cn->unit[sz] = 0;
            cn->unitEnc = decoded->subjectOUEnc;
        }
        if (decoded->subjectSN) {
            sz = (decoded->subjectSNLen < CTC_NAME_SIZE) ? decoded->subjectSNLen
                                                         : CTC_NAME_SIZE - 1;
            strncpy(cn->sur, decoded->subjectSN, CTC_NAME_SIZE);
            cn->sur[sz] = 0;
            cn->surEnc = decoded->subjectSNEnc;
        }
        if (decoded->subjectEmail) {
            sz = (decoded->subjectEmailLen < CTC_NAME_SIZE)
               ?  decoded->subjectEmailLen : CTC_NAME_SIZE - 1;
            strncpy(cn->email, decoded->subjectEmail, CTC_NAME_SIZE);
            cn->email[sz] = 0;
        }
    }

    FreeDecodedCert(decoded);

#ifdef CYASSL_SMALL_STACK
    XFREE(decoded, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret < 0 ? ret : 0;
}


#ifndef NO_FILESYSTEM

/* forward from CyaSSL */
int CyaSSL_PemCertToDer(const char* fileName, unsigned char* derBuf, int derSz);

/* Set cert issuer from issuerFile in PEM */
int SetIssuer(Cert* cert, const char* issuerFile)
{
    int         ret;
    int         derSz;
    byte*       der = (byte*)XMALLOC(EIGHTK_BUF, NULL, DYNAMIC_TYPE_CERT);

    if (der == NULL) {
        CYASSL_MSG("SetIssuer OOF Problem");
        return MEMORY_E;
    }
    derSz = CyaSSL_PemCertToDer(issuerFile, der, EIGHTK_BUF);
    cert->selfSigned = 0;
    ret = SetNameFromCert(&cert->issuer, der, derSz);
    XFREE(der, NULL, DYNAMIC_TYPE_CERT);

    return ret;
}


/* Set cert subject from subjectFile in PEM */
int SetSubject(Cert* cert, const char* subjectFile)
{
    int         ret;
    int         derSz;
    byte*       der = (byte*)XMALLOC(EIGHTK_BUF, NULL, DYNAMIC_TYPE_CERT);

    if (der == NULL) {
        CYASSL_MSG("SetSubject OOF Problem");
        return MEMORY_E;
    }
    derSz = CyaSSL_PemCertToDer(subjectFile, der, EIGHTK_BUF);
    ret = SetNameFromCert(&cert->subject, der, derSz);
    XFREE(der, NULL, DYNAMIC_TYPE_CERT);

    return ret;
}


#ifdef CYASSL_ALT_NAMES

/* Set atl names from file in PEM */
int SetAltNames(Cert* cert, const char* file)
{
    int         ret;
    int         derSz;
    byte*       der = (byte*)XMALLOC(EIGHTK_BUF, NULL, DYNAMIC_TYPE_CERT);

    if (der == NULL) {
        CYASSL_MSG("SetAltNames OOF Problem");
        return MEMORY_E;
    }
    derSz = CyaSSL_PemCertToDer(file, der, EIGHTK_BUF);
    ret = SetAltNamesFromCert(cert, der, derSz);
    XFREE(der, NULL, DYNAMIC_TYPE_CERT);

    return ret;
}

#endif /* CYASSL_ALT_NAMES */

#endif /* NO_FILESYSTEM */

/* Set cert issuer from DER buffer */
int SetIssuerBuffer(Cert* cert, const byte* der, int derSz)
{
    cert->selfSigned = 0;
    return SetNameFromCert(&cert->issuer, der, derSz);
}


/* Set cert subject from DER buffer */
int SetSubjectBuffer(Cert* cert, const byte* der, int derSz)
{
    return SetNameFromCert(&cert->subject, der, derSz);
}


#ifdef CYASSL_ALT_NAMES

/* Set cert alt names from DER buffer */
int SetAltNamesBuffer(Cert* cert, const byte* der, int derSz)
{
    return SetAltNamesFromCert(cert, der, derSz);
}

/* Set cert dates from DER buffer */
int SetDatesBuffer(Cert* cert, const byte* der, int derSz)
{
    return SetDatesFromCert(cert, der, derSz);
}

#endif /* CYASSL_ALT_NAMES */

#endif /* CYASSL_CERT_GEN */


#ifdef HAVE_ECC

/* Der Encode r & s ints into out, outLen is (in/out) size */
int StoreECC_DSA_Sig(byte* out, word32* outLen, mp_int* r, mp_int* s)
{
    word32 idx = 0;
    word32 rSz;                           /* encoding size */
    word32 sSz;
    word32 headerSz = 4;   /* 2*ASN_TAG + 2*LEN(ENUM) */

    /* If the leading bit on the INTEGER is a 1, add a leading zero */
    int rLeadingZero = mp_leading_bit(r);
    int sLeadingZero = mp_leading_bit(s);
    int rLen = mp_unsigned_bin_size(r);   /* big int size */
    int sLen = mp_unsigned_bin_size(s);
    int err;

    if (*outLen < (rLen + rLeadingZero + sLen + sLeadingZero +
                   headerSz + 2))  /* SEQ_TAG + LEN(ENUM) */
        return BAD_FUNC_ARG;

    idx = SetSequence(rLen+rLeadingZero+sLen+sLeadingZero+headerSz, out);

    /* store r */
    out[idx++] = ASN_INTEGER;
    rSz = SetLength(rLen + rLeadingZero, &out[idx]);
    idx += rSz;
    if (rLeadingZero)
        out[idx++] = 0;
    err = mp_to_unsigned_bin(r, &out[idx]);
    if (err != MP_OKAY) return err;
    idx += rLen;

    /* store s */
    out[idx++] = ASN_INTEGER;
    sSz = SetLength(sLen + sLeadingZero, &out[idx]);
    idx += sSz;
    if (sLeadingZero)
        out[idx++] = 0;
    err = mp_to_unsigned_bin(s, &out[idx]);
    if (err != MP_OKAY) return err;
    idx += sLen;

    *outLen = idx;

    return 0;
}


/* Der Decode ECC-DSA Signautre, r & s stored as big ints */
int DecodeECC_DSA_Sig(const byte* sig, word32 sigLen, mp_int* r, mp_int* s)
{
    word32 idx = 0;
    int    len = 0;

    if (GetSequence(sig, &idx, &len, sigLen) < 0)
        return ASN_ECC_KEY_E;

    if ((word32)len > (sigLen - idx))
        return ASN_ECC_KEY_E;

    if (GetInt(r, sig, &idx, sigLen) < 0)
        return ASN_ECC_KEY_E;

    if (GetInt(s, sig, &idx, sigLen) < 0)
        return ASN_ECC_KEY_E;

    return 0;
}


int EccPrivateKeyDecode(const byte* input, word32* inOutIdx, ecc_key* key,
                        word32 inSz)
{
    word32 oid = 0;
    int    version, length;
    int    privSz, pubSz;
    byte   b;
    int    ret = 0;
#ifdef CYASSL_SMALL_STACK
    byte* priv;
    byte* pub;
#else
    byte priv[ECC_MAXSIZE];
    byte pub[ECC_MAXSIZE * 2 + 1]; /* public key has two parts plus header */
#endif

    if (input == NULL || inOutIdx == NULL || key == NULL || inSz == 0)
        return BAD_FUNC_ARG;

    if (GetSequence(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

    if (GetMyVersion(input, inOutIdx, &version) < 0)
        return ASN_PARSE_E;

    b = input[*inOutIdx];
    *inOutIdx += 1;

    /* priv type */
    if (b != 4 && b != 6 && b != 7) 
        return ASN_PARSE_E;

    if (GetLength(input, inOutIdx, &length, inSz) < 0)
        return ASN_PARSE_E;

#ifdef CYASSL_SMALL_STACK
    priv = (byte*)XMALLOC(ECC_MAXSIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (priv == NULL)
        return MEMORY_E;
    
    pub = (byte*)XMALLOC(ECC_MAXSIZE * 2 + 1, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (pub == NULL) {
        XFREE(priv, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        return MEMORY_E;
    }
#endif

    /* priv key */
    privSz = length;
    XMEMCPY(priv, &input[*inOutIdx], privSz);
    *inOutIdx += length;

    /* prefix 0, may have */
    b = input[*inOutIdx];
    if (b == ECC_PREFIX_0) {
        *inOutIdx += 1;

        if (GetLength(input, inOutIdx, &length, inSz) < 0)
            ret = ASN_PARSE_E;
        else {
            /* object id */
            b = input[*inOutIdx];
            *inOutIdx += 1;

            if (b != ASN_OBJECT_ID) {
                ret = ASN_OBJECT_ID_E;
            }
            else if (GetLength(input, inOutIdx, &length, inSz) < 0) {
                ret = ASN_PARSE_E;
            }
            else {
                while(length--) {
                    oid += input[*inOutIdx];
                    *inOutIdx += 1;
                }
                if (CheckCurve(oid) < 0)
                    ret = ECC_CURVE_OID_E;
            }
        }
    }

    if (ret == 0) {
        /* prefix 1 */
        b = input[*inOutIdx];
        *inOutIdx += 1;

        if (b != ECC_PREFIX_1) {
            ret = ASN_ECC_KEY_E;
        }
        else if (GetLength(input, inOutIdx, &length, inSz) < 0) {
            ret = ASN_PARSE_E;
        }
        else {
            /* key header */
            b = input[*inOutIdx];
            *inOutIdx += 1;
            
            if (b != ASN_BIT_STRING) {
                ret = ASN_BITSTR_E;
            }
            else if (GetLength(input, inOutIdx, &length, inSz) < 0) {
                ret = ASN_PARSE_E;
            }
            else {
                b = input[*inOutIdx];
                *inOutIdx += 1;

                if (b != 0x00) {
                    ret = ASN_EXPECT_0_E;
                }
                else {
                    /* pub key */
                    pubSz = length - 1;  /* null prefix */
                    XMEMCPY(pub, &input[*inOutIdx], pubSz);

                    *inOutIdx += length;

                    ret = ecc_import_private_key(priv, privSz, pub, pubSz, key);
                }
            }
        }
    }

#ifdef CYASSL_SMALL_STACK
    XFREE(priv, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(pub,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

#endif  /* HAVE_ECC */


#if defined(HAVE_OCSP) || defined(HAVE_CRL)

/* Get raw Date only, no processing, 0 on success */
static int GetBasicDate(const byte* source, word32* idx, byte* date,
                        byte* format, int maxIdx)
{
    int    length;

    CYASSL_ENTER("GetBasicDate");

    *format = source[*idx];
    *idx += 1;
    if (*format != ASN_UTC_TIME && *format != ASN_GENERALIZED_TIME)
        return ASN_TIME_E;

    if (GetLength(source, idx, &length, maxIdx) < 0)
        return ASN_PARSE_E;

    if (length > MAX_DATE_SIZE || length < MIN_DATE_SIZE)
        return ASN_DATE_SZ_E;

    XMEMCPY(date, &source[*idx], length);
    *idx += length;

    return 0;
}

#endif


#ifdef HAVE_OCSP

static int GetEnumerated(const byte* input, word32* inOutIdx, int *value)
{
    word32 idx = *inOutIdx;
    word32 len;

    CYASSL_ENTER("GetEnumerated");

    *value = 0;

    if (input[idx++] != ASN_ENUMERATED)
        return ASN_PARSE_E;

    len = input[idx++];
    if (len > 4)
        return ASN_PARSE_E;

    while (len--) {
        *value  = *value << 8 | input[idx++];
    }

    *inOutIdx = idx;

    return *value;
}


static int DecodeSingleResponse(byte* source,
                            word32* ioIndex, OcspResponse* resp, word32 size)
{
    word32 idx = *ioIndex, prevIndex, oid;
    int length, wrapperSz;
    CertStatus* cs = resp->status;

    CYASSL_ENTER("DecodeSingleResponse");

    /* Outer wrapper of the SEQUENCE OF Single Responses. */
    if (GetSequence(source, &idx, &wrapperSz, size) < 0)
        return ASN_PARSE_E;

    prevIndex = idx;

    /* When making a request, we only request one status on one certificate
     * at a time. There should only be one SingleResponse */

    /* Wrapper around the Single Response */
    if (GetSequence(source, &idx, &length, size) < 0)
        return ASN_PARSE_E;

    /* Wrapper around the CertID */
    if (GetSequence(source, &idx, &length, size) < 0)
        return ASN_PARSE_E;
    /* Skip the hash algorithm */
    if (GetAlgoId(source, &idx, &oid, size) < 0)
        return ASN_PARSE_E;
    /* Save reference to the hash of CN */
    if (source[idx++] != ASN_OCTET_STRING)
        return ASN_PARSE_E;
    if (GetLength(source, &idx, &length, size) < 0)
        return ASN_PARSE_E;
    resp->issuerHash = source + idx;
    idx += length;
    /* Save reference to the hash of the issuer public key */
    if (source[idx++] != ASN_OCTET_STRING)
        return ASN_PARSE_E;
    if (GetLength(source, &idx, &length, size) < 0)
        return ASN_PARSE_E;
    resp->issuerKeyHash = source + idx;
    idx += length;

    /* Read the serial number, it is handled as a string, not as a 
     * proper number. Just XMEMCPY the data over, rather than load it
     * as an mp_int. */
    if (source[idx++] != ASN_INTEGER)
        return ASN_PARSE_E;
    if (GetLength(source, &idx, &length, size) < 0)
        return ASN_PARSE_E;
    if (length <= EXTERNAL_SERIAL_SIZE)
    {
        if (source[idx] == 0)
        {
            idx++;
            length--;
        }
        XMEMCPY(cs->serial, source + idx, length);
        cs->serialSz = length;
    }
    else
    {
        return ASN_GETINT_E;
    }
    idx += length;

    /* CertStatus */
    switch (source[idx++])
    {
        case (ASN_CONTEXT_SPECIFIC | CERT_GOOD):
            cs->status = CERT_GOOD;
            idx++;
            break;
        case (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED | CERT_REVOKED):
            cs->status = CERT_REVOKED;
            if (GetLength(source, &idx, &length, size) < 0)
                return ASN_PARSE_E;
            idx += length;
            break;
        case (ASN_CONTEXT_SPECIFIC | CERT_UNKNOWN):
            cs->status = CERT_UNKNOWN;
            idx++;
            break;
        default:
            return ASN_PARSE_E;
    }

    if (GetBasicDate(source, &idx, cs->thisDate,
                                                &cs->thisDateFormat, size) < 0)
        return ASN_PARSE_E;
    if (!XVALIDATE_DATE(cs->thisDate, cs->thisDateFormat, BEFORE))
        return ASN_BEFORE_DATE_E;
    
    /* The following items are optional. Only check for them if there is more
     * unprocessed data in the singleResponse wrapper. */
    
    if (((int)(idx - prevIndex) < wrapperSz) &&
        (source[idx] == (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 0)))
    {
        idx++;
        if (GetLength(source, &idx, &length, size) < 0)
            return ASN_PARSE_E;
        if (GetBasicDate(source, &idx, cs->nextDate,
                                                &cs->nextDateFormat, size) < 0)
            return ASN_PARSE_E;
    }
    if (((int)(idx - prevIndex) < wrapperSz) &&
        (source[idx] == (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 1)))
    {
        idx++;
        if (GetLength(source, &idx, &length, size) < 0)
            return ASN_PARSE_E;
        idx += length;
    }

    *ioIndex = idx;

    return 0;
}

static int DecodeOcspRespExtensions(byte* source,
                            word32* ioIndex, OcspResponse* resp, word32 sz)
{
    word32 idx = *ioIndex;
    int length;
    int ext_bound; /* boundary index for the sequence of extensions */
    word32 oid;

    CYASSL_ENTER("DecodeOcspRespExtensions");

    if (source[idx++] != (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 1))
        return ASN_PARSE_E;

    if (GetLength(source, &idx, &length, sz) < 0) return ASN_PARSE_E;

    if (GetSequence(source, &idx, &length, sz) < 0) return ASN_PARSE_E;
   
    ext_bound = idx + length;

    while (idx < (word32)ext_bound) {
        if (GetSequence(source, &idx, &length, sz) < 0) {
            CYASSL_MSG("\tfail: should be a SEQUENCE");
            return ASN_PARSE_E;
        }

        oid = 0;
        if (GetObjectId(source, &idx, &oid, sz) < 0) {
            CYASSL_MSG("\tfail: OBJECT ID");
            return ASN_PARSE_E;
        }

        /* check for critical flag */
        if (source[idx] == ASN_BOOLEAN) {
            CYASSL_MSG("\tfound optional critical flag, moving past");
            idx += (ASN_BOOL_SIZE + 1);
        }

        /* process the extension based on the OID */
        if (source[idx++] != ASN_OCTET_STRING) {
            CYASSL_MSG("\tfail: should be an OCTET STRING");
            return ASN_PARSE_E;
        }

        if (GetLength(source, &idx, &length, sz) < 0) {
            CYASSL_MSG("\tfail: extension data length");
            return ASN_PARSE_E;
        }

        if (oid == OCSP_NONCE_OID) {
            resp->nonce = source + idx;
            resp->nonceSz = length;
        }

        idx += length;
    }

    *ioIndex = idx;
    return 0;
}


static int DecodeResponseData(byte* source,
                            word32* ioIndex, OcspResponse* resp, word32 size)
{
    word32 idx = *ioIndex, prev_idx;
    int length;
    int version;
    word32 responderId = 0;

    CYASSL_ENTER("DecodeResponseData");

    resp->response = source + idx;
    prev_idx = idx;
    if (GetSequence(source, &idx, &length, size) < 0)
        return ASN_PARSE_E;
    resp->responseSz = length + idx - prev_idx;

    /* Get version. It is an EXPLICIT[0] DEFAULT(0) value. If this
     * item isn't an EXPLICIT[0], then set version to zero and move
     * onto the next item.
     */
    if (source[idx] == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED))
    {    
        idx += 2; /* Eat the value and length */
        if (GetMyVersion(source, &idx, &version) < 0)
            return ASN_PARSE_E;
    } else
        version = 0;

    responderId = source[idx++];
    if ((responderId == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED | 1)) ||
        (responderId == (ASN_CONTEXT_SPECIFIC | ASN_CONSTRUCTED | 2)))
    {
        if (GetLength(source, &idx, &length, size) < 0)
            return ASN_PARSE_E;
        idx += length;
    }
    else
        return ASN_PARSE_E;
    
    /* save pointer to the producedAt time */
    if (GetBasicDate(source, &idx, resp->producedDate,
                                        &resp->producedDateFormat, size) < 0)
        return ASN_PARSE_E;

    if (DecodeSingleResponse(source, &idx, resp, size) < 0)
        return ASN_PARSE_E;

    if (DecodeOcspRespExtensions(source, &idx, resp, size) < 0)
        return ASN_PARSE_E;

    *ioIndex = idx;
    return 0;
}


static int DecodeCerts(byte* source,
                            word32* ioIndex, OcspResponse* resp, word32 size)
{
    word32 idx = *ioIndex;

    CYASSL_ENTER("DecodeCerts");

    if (source[idx++] == (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC))
    {
        int length;

        if (GetLength(source, &idx, &length, size) < 0)
            return ASN_PARSE_E;

        if (GetSequence(source, &idx, &length, size) < 0)
            return ASN_PARSE_E;

        resp->cert = source + idx;
        resp->certSz = length;

        idx += length;
    }
    *ioIndex = idx;
    return 0;
}

static int DecodeBasicOcspResponse(byte* source,
                            word32* ioIndex, OcspResponse* resp, word32 size)
{
    int length;
    word32 idx = *ioIndex;
    word32 end_index;

    CYASSL_ENTER("DecodeBasicOcspResponse");

    if (GetSequence(source, &idx, &length, size) < 0)
        return ASN_PARSE_E;

    if (idx + length > size)
        return ASN_INPUT_E;
    end_index = idx + length;

    if (DecodeResponseData(source, &idx, resp, size) < 0)
        return ASN_PARSE_E;
    
    /* Get the signature algorithm */
    if (GetAlgoId(source, &idx, &resp->sigOID, size) < 0)
        return ASN_PARSE_E;

    /* Obtain pointer to the start of the signature, and save the size */
    if (source[idx++] == ASN_BIT_STRING)
    {
        int sigLength = 0;
        if (GetLength(source, &idx, &sigLength, size) < 0)
            return ASN_PARSE_E;
        resp->sigSz = sigLength;
        resp->sig = source + idx;
        idx += sigLength;
    }

    /*
     * Check the length of the BasicOcspResponse against the current index to
     * see if there are certificates, they are optional.
     */
    if (idx < end_index)
    {
        DecodedCert cert;
        int ret;

        if (DecodeCerts(source, &idx, resp, size) < 0)
            return ASN_PARSE_E;

        InitDecodedCert(&cert, resp->cert, resp->certSz, 0);
        ret = ParseCertRelative(&cert, CA_TYPE, NO_VERIFY, 0);
        if (ret < 0)
            return ret;

        ret = ConfirmSignature(resp->response, resp->responseSz,
                            cert.publicKey, cert.pubKeySize, cert.keyOID,
                            resp->sig, resp->sigSz, resp->sigOID, NULL);
        FreeDecodedCert(&cert);

        if (ret == 0)
        {
            CYASSL_MSG("\tOCSP Confirm signature failed");
            return ASN_OCSP_CONFIRM_E;
        }
    }

    *ioIndex = idx;
    return 0;
}


void InitOcspResponse(OcspResponse* resp, CertStatus* status,
                                                    byte* source, word32 inSz)
{
    CYASSL_ENTER("InitOcspResponse");

    resp->responseStatus = -1;
    resp->response = NULL;
    resp->responseSz = 0;
    resp->producedDateFormat = 0;
    resp->issuerHash = NULL;
    resp->issuerKeyHash = NULL;
    resp->sig = NULL;
    resp->sigSz = 0;
    resp->sigOID = 0;
    resp->status = status;
    resp->nonce = NULL;
    resp->nonceSz = 0;
    resp->source = source;
    resp->maxIdx = inSz;
}


int OcspResponseDecode(OcspResponse* resp)
{
    int length = 0;
    word32 idx = 0;
    byte* source = resp->source;
    word32 size = resp->maxIdx;
    word32 oid;

    CYASSL_ENTER("OcspResponseDecode");

    /* peel the outer SEQUENCE wrapper */
    if (GetSequence(source, &idx, &length, size) < 0)
        return ASN_PARSE_E;
    
    /* First get the responseStatus, an ENUMERATED */
    if (GetEnumerated(source, &idx, &resp->responseStatus) < 0)
        return ASN_PARSE_E;

    if (resp->responseStatus != OCSP_SUCCESSFUL)
        return 0;

    /* Next is an EXPLICIT record called ResponseBytes, OPTIONAL */
    if (idx >= size)
        return ASN_INPUT_E;
    if (source[idx++] != (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC))
        return ASN_PARSE_E;
    if (GetLength(source, &idx, &length, size) < 0)
        return ASN_PARSE_E;

    /* Get the responseBytes SEQUENCE */
    if (GetSequence(source, &idx, &length, size) < 0)
        return ASN_PARSE_E;

    /* Check ObjectID for the resposeBytes */
    if (GetObjectId(source, &idx, &oid, size) < 0)
        return ASN_PARSE_E;
    if (oid != OCSP_BASIC_OID)
        return ASN_PARSE_E;
    if (source[idx++] != ASN_OCTET_STRING)
        return ASN_PARSE_E;

    if (GetLength(source, &idx, &length, size) < 0)
        return ASN_PARSE_E;

    if (DecodeBasicOcspResponse(source, &idx, resp, size) < 0)
        return ASN_PARSE_E;
    
    return 0;
}


static word32 SetOcspReqExtensions(word32 extSz, byte* output,
                                            const byte* nonce, word32 nonceSz)
{
    static const byte NonceObjId[] = { 0x2b, 0x06, 0x01, 0x05, 0x05, 0x07,
                                       0x30, 0x01, 0x02 };
    byte seqArray[5][MAX_SEQ_SZ];
    word32 seqSz[5], totalSz;

    CYASSL_ENTER("SetOcspReqExtensions");

    if (nonce == NULL || nonceSz == 0) return 0;
    
    seqArray[0][0] = ASN_OCTET_STRING;
    seqSz[0] = 1 + SetLength(nonceSz, &seqArray[0][1]);

    seqArray[1][0] = ASN_OBJECT_ID;
    seqSz[1] = 1 + SetLength(sizeof(NonceObjId), &seqArray[1][1]);

    totalSz = seqSz[0] + seqSz[1] + nonceSz + (word32)sizeof(NonceObjId);

    seqSz[2] = SetSequence(totalSz, seqArray[2]);
    totalSz += seqSz[2];

    seqSz[3] = SetSequence(totalSz, seqArray[3]);
    totalSz += seqSz[3];

    seqArray[4][0] = (ASN_CONSTRUCTED | ASN_CONTEXT_SPECIFIC | 2);
    seqSz[4] = 1 + SetLength(totalSz, &seqArray[4][1]);
    totalSz += seqSz[4];

    if (totalSz < extSz)
    {
        totalSz = 0;
        XMEMCPY(output + totalSz, seqArray[4], seqSz[4]);
        totalSz += seqSz[4];
        XMEMCPY(output + totalSz, seqArray[3], seqSz[3]);
        totalSz += seqSz[3];
        XMEMCPY(output + totalSz, seqArray[2], seqSz[2]);
        totalSz += seqSz[2];
        XMEMCPY(output + totalSz, seqArray[1], seqSz[1]);
        totalSz += seqSz[1];
        XMEMCPY(output + totalSz, NonceObjId, sizeof(NonceObjId));
        totalSz += (word32)sizeof(NonceObjId);
        XMEMCPY(output + totalSz, seqArray[0], seqSz[0]);
        totalSz += seqSz[0];
        XMEMCPY(output + totalSz, nonce, nonceSz);
        totalSz += nonceSz;
    }

    return totalSz;
}


int EncodeOcspRequest(OcspRequest* req)
{
    byte seqArray[5][MAX_SEQ_SZ];
    /* The ASN.1 of the OCSP Request is an onion of sequences */
    byte algoArray[MAX_ALGO_SZ];
    byte issuerArray[MAX_ENCODED_DIG_SZ];
    byte issuerKeyArray[MAX_ENCODED_DIG_SZ];
    byte snArray[MAX_SN_SZ];
    byte extArray[MAX_OCSP_EXT_SZ];
    byte* output = req->dest;
    word32 seqSz[5], algoSz, issuerSz, issuerKeySz, snSz, extSz, totalSz;
    int i;

    CYASSL_ENTER("EncodeOcspRequest");

    algoSz = SetAlgoID(SHAh, algoArray, hashType, 0);

    req->issuerHash = req->cert->issuerHash;
    issuerSz = SetDigest(req->cert->issuerHash, SHA_SIZE, issuerArray);
    
    req->issuerKeyHash = req->cert->issuerKeyHash;
    issuerKeySz = SetDigest(req->cert->issuerKeyHash, SHA_SIZE, issuerKeyArray);

    req->serial = req->cert->serial;
    req->serialSz = req->cert->serialSz;
    snSz = SetSerialNumber(req->cert->serial, req->cert->serialSz, snArray);

    extSz = 0;
    if (req->useNonce) {
        RNG rng;
        if (InitRng(&rng) != 0) {
            CYASSL_MSG("\tCannot initialize RNG. Skipping the OSCP Nonce.");
        } else {
            if (RNG_GenerateBlock(&rng, req->nonce, MAX_OCSP_NONCE_SZ) != 0)
                CYASSL_MSG("\tCannot run RNG. Skipping the OSCP Nonce.");
            else {
                req->nonceSz = MAX_OCSP_NONCE_SZ;
                extSz = SetOcspReqExtensions(MAX_OCSP_EXT_SZ, extArray,
                                                      req->nonce, req->nonceSz);
            }
        }
    }

    totalSz = algoSz + issuerSz + issuerKeySz + snSz;

    for (i = 4; i >= 0; i--) {
        seqSz[i] = SetSequence(totalSz, seqArray[i]);
        totalSz += seqSz[i];
        if (i == 2) totalSz += extSz;
    }
    totalSz = 0;
    for (i = 0; i < 5; i++) {
        XMEMCPY(output + totalSz, seqArray[i], seqSz[i]);
        totalSz += seqSz[i];
    }
    XMEMCPY(output + totalSz, algoArray, algoSz);
    totalSz += algoSz;
    XMEMCPY(output + totalSz, issuerArray, issuerSz);
    totalSz += issuerSz;
    XMEMCPY(output + totalSz, issuerKeyArray, issuerKeySz);
    totalSz += issuerKeySz;
    XMEMCPY(output + totalSz, snArray, snSz);
    totalSz += snSz;
    if (extSz != 0) {
        XMEMCPY(output + totalSz, extArray, extSz);
        totalSz += extSz;
    }

    return totalSz;
}


void InitOcspRequest(OcspRequest* req, DecodedCert* cert, byte useNonce,
                                                    byte* dest, word32 destSz)
{
    CYASSL_ENTER("InitOcspRequest");

    req->cert = cert;
    req->useNonce = useNonce;
    req->nonceSz = 0;
    req->issuerHash = NULL;
    req->issuerKeyHash = NULL;
    req->serial = NULL;
    req->dest = dest;
    req->destSz = destSz;
}


int CompareOcspReqResp(OcspRequest* req, OcspResponse* resp)
{
    int cmp;

    CYASSL_ENTER("CompareOcspReqResp");

    if (req == NULL)
    {
        CYASSL_MSG("\tReq missing");
        return -1;
    }

    if (resp == NULL)
    {
        CYASSL_MSG("\tResp missing");
        return 1;
    }

    /* Nonces are not critical. The responder may not necessarily add
     * the nonce to the response. */
    if (req->useNonce && resp->nonceSz != 0) {
        cmp = req->nonceSz - resp->nonceSz;
        if (cmp != 0)
        {
            CYASSL_MSG("\tnonceSz mismatch");
            return cmp;
        }
    
        cmp = XMEMCMP(req->nonce, resp->nonce, req->nonceSz);
        if (cmp != 0)
        {
            CYASSL_MSG("\tnonce mismatch");
            return cmp;
        }
    }

    cmp = XMEMCMP(req->issuerHash, resp->issuerHash, SHA_DIGEST_SIZE);
    if (cmp != 0)
    {
        CYASSL_MSG("\tissuerHash mismatch");
        return cmp;
    }

    cmp = XMEMCMP(req->issuerKeyHash, resp->issuerKeyHash, SHA_DIGEST_SIZE);
    if (cmp != 0)
    {
        CYASSL_MSG("\tissuerKeyHash mismatch");
        return cmp;
    }

    cmp = req->serialSz - resp->status->serialSz;
    if (cmp != 0)
    {
        CYASSL_MSG("\tserialSz mismatch");
        return cmp;
    }

    cmp = XMEMCMP(req->serial, resp->status->serial, req->serialSz);
    if (cmp != 0)
    {
        CYASSL_MSG("\tserial mismatch");
        return cmp;
    }

    return 0;
}

#endif


/* store SHA1 hash of NAME */
CYASSL_LOCAL int GetNameHash(const byte* source, word32* idx, byte* hash,
                             int maxIdx)
{
    Sha    sha;
    int    length;  /* length of all distinguished names */
    int    ret = 0;
    word32 dummy;

    CYASSL_ENTER("GetNameHash");

    if (source[*idx] == ASN_OBJECT_ID) {
        CYASSL_MSG("Trying optional prefix...");

        if (GetLength(source, idx, &length, maxIdx) < 0)
            return ASN_PARSE_E;

        *idx += length;
        CYASSL_MSG("Got optional prefix");
    }

    /* For OCSP, RFC2560 section 4.1.1 states the issuer hash should be
     * calculated over the entire DER encoding of the Name field, including
     * the tag and length. */
    dummy = *idx;
    if (GetSequence(source, idx, &length, maxIdx) < 0)
        return ASN_PARSE_E;

    ret = InitSha(&sha);
    if (ret != 0)
        return ret;
    ShaUpdate(&sha, source + dummy, length + *idx - dummy);
    ShaFinal(&sha, hash);

    *idx += length;

    return 0;
}


#ifdef HAVE_CRL

/* initialize decoded CRL */
void InitDecodedCRL(DecodedCRL* dcrl)
{
    CYASSL_MSG("InitDecodedCRL");

    dcrl->certBegin    = 0;
    dcrl->sigIndex     = 0;
    dcrl->sigLength    = 0;
    dcrl->signatureOID = 0;
    dcrl->certs        = NULL;
    dcrl->totalCerts   = 0;
}


/* free decoded CRL resources */
void FreeDecodedCRL(DecodedCRL* dcrl)
{
    RevokedCert* tmp = dcrl->certs;

    CYASSL_MSG("FreeDecodedCRL");

    while(tmp) {
        RevokedCert* next = tmp->next;
        XFREE(tmp, NULL, DYNAMIC_TYPE_REVOKED);
        tmp = next;
    }
}


/* Get Revoked Cert list, 0 on success */
static int GetRevoked(const byte* buff, word32* idx, DecodedCRL* dcrl,
                      int maxIdx)
{
    int    len;
    word32 end;
    byte   b;
    RevokedCert* rc;

    CYASSL_ENTER("GetRevoked");

    if (GetSequence(buff, idx, &len, maxIdx) < 0)
        return ASN_PARSE_E;

    end = *idx + len;

    /* get serial number */
    b = buff[*idx];
    *idx += 1;

    if (b != ASN_INTEGER) {
        CYASSL_MSG("Expecting Integer");
        return ASN_PARSE_E;
    }

    if (GetLength(buff, idx, &len, maxIdx) < 0)
        return ASN_PARSE_E;

    if (len > EXTERNAL_SERIAL_SIZE) {
        CYASSL_MSG("Serial Size too big");
        return ASN_PARSE_E;
    }

    rc = (RevokedCert*)XMALLOC(sizeof(RevokedCert), NULL, DYNAMIC_TYPE_CRL);
    if (rc == NULL) {
        CYASSL_MSG("Alloc Revoked Cert failed");
        return MEMORY_E;
    }

    XMEMCPY(rc->serialNumber, &buff[*idx], len);
    rc->serialSz = len;

    /* add to list */
    rc->next = dcrl->certs;
    dcrl->certs = rc;
    dcrl->totalCerts++;

    *idx += len;

    /* get date */
    b = buff[*idx];
    *idx += 1;

    if (b != ASN_UTC_TIME && b != ASN_GENERALIZED_TIME) {
        CYASSL_MSG("Expecting Date");
        return ASN_PARSE_E;
    }

    if (GetLength(buff, idx, &len, maxIdx) < 0)
        return ASN_PARSE_E;

    /* skip for now */
    *idx += len;

    if (*idx != end)  /* skip extensions */
        *idx = end;

    return 0;
}


/* Get CRL Signature, 0 on success */
static int GetCRL_Signature(const byte* source, word32* idx, DecodedCRL* dcrl,
                            int maxIdx)
{
    int    length;
    byte   b;

    CYASSL_ENTER("GetCRL_Signature");

    b = source[*idx];
    *idx += 1;
    if (b != ASN_BIT_STRING)
        return ASN_BITSTR_E;

    if (GetLength(source, idx, &length, maxIdx) < 0)
        return ASN_PARSE_E;

    dcrl->sigLength = length;

    b = source[*idx];
    *idx += 1;
    if (b != 0x00)
        return ASN_EXPECT_0_E;

    dcrl->sigLength--;
    dcrl->signature = (byte*)&source[*idx];

    *idx += dcrl->sigLength;

    return 0;
}


/* prase crl buffer into decoded state, 0 on success */
int ParseCRL(DecodedCRL* dcrl, const byte* buff, word32 sz, void* cm)
{
    int     version, len;
    word32  oid, idx = 0;
    Signer* ca = NULL;

    CYASSL_MSG("ParseCRL");

    /* raw crl hash */
    /* hash here if needed for optimized comparisons
     * Sha     sha;
     * InitSha(&sha);
     * ShaUpdate(&sha, buff, sz);
     * ShaFinal(&sha, dcrl->crlHash); */

    if (GetSequence(buff, &idx, &len, sz) < 0)
        return ASN_PARSE_E;

    dcrl->certBegin = idx;

    if (GetSequence(buff, &idx, &len, sz) < 0)
        return ASN_PARSE_E;
    dcrl->sigIndex = len + idx;

    /* may have version */
    if (buff[idx] == ASN_INTEGER) {
        if (GetMyVersion(buff, &idx, &version) < 0)
            return ASN_PARSE_E;
    }

    if (GetAlgoId(buff, &idx, &oid, sz) < 0)
        return ASN_PARSE_E;

    if (GetNameHash(buff, &idx, dcrl->issuerHash, sz) < 0)
        return ASN_PARSE_E;

    if (GetBasicDate(buff, &idx, dcrl->lastDate, &dcrl->lastDateFormat, sz) < 0)
        return ASN_PARSE_E;

    if (GetBasicDate(buff, &idx, dcrl->nextDate, &dcrl->nextDateFormat, sz) < 0)
        return ASN_PARSE_E;

    if (!XVALIDATE_DATE(dcrl->nextDate, dcrl->nextDateFormat, AFTER)) {
        CYASSL_MSG("CRL after date is no longer valid");
        return ASN_AFTER_DATE_E;
    }

    if (idx != dcrl->sigIndex && buff[idx] != CRL_EXTENSIONS) {
        if (GetSequence(buff, &idx, &len, sz) < 0)
            return ASN_PARSE_E;

        len += idx;

        while (idx < (word32)len) {
            if (GetRevoked(buff, &idx, dcrl, sz) < 0)
                return ASN_PARSE_E;
        }
    }

    if (idx != dcrl->sigIndex)
        idx = dcrl->sigIndex;   /* skip extensions */

    if (GetAlgoId(buff, &idx, &dcrl->signatureOID, sz) < 0)
        return ASN_PARSE_E;

    if (GetCRL_Signature(buff, &idx, dcrl, sz) < 0)
        return ASN_PARSE_E;

    /* openssl doesn't add skid by default for CRLs cause firefox chokes
       we're not assuming it's available yet */
    #if !defined(NO_SKID) && defined(CRL_SKID_READY)
        if (dcrl->extAuthKeyIdSet)
            ca = GetCA(cm, dcrl->extAuthKeyId);
        if (ca == NULL)
            ca = GetCAByName(cm, dcrl->issuerHash);
    #else /* NO_SKID */
        ca = GetCA(cm, dcrl->issuerHash);
    #endif /* NO_SKID */
    CYASSL_MSG("About to verify CRL signature");

    if (ca) {
        CYASSL_MSG("Found CRL issuer CA");
        /* try to confirm/verify signature */
        #ifndef IGNORE_KEY_EXTENSIONS
            if ((ca->keyUsage & KEYUSE_CRL_SIGN) == 0) {
                CYASSL_MSG("CA cannot sign CRLs");
                return ASN_CRL_NO_SIGNER_E;
            }
        #endif /* IGNORE_KEY_EXTENSIONS */
        if (!ConfirmSignature(buff + dcrl->certBegin,
                dcrl->sigIndex - dcrl->certBegin,
                ca->publicKey, ca->pubKeySize, ca->keyOID,
                dcrl->signature, dcrl->sigLength, dcrl->signatureOID, NULL)) {
            CYASSL_MSG("CRL Confirm signature failed");
            return ASN_CRL_CONFIRM_E;
        }
    }
    else {
        CYASSL_MSG("Did NOT find CRL issuer CA");
        return ASN_CRL_NO_SIGNER_E;
    }

    return 0;
}

#endif /* HAVE_CRL */
#endif

#ifdef CYASSL_SEP



#endif /* CYASSL_SEP */

