/* crl.c
 *
 * Copyright (C) 2006-2012 Sawtooth Consulting Ltd.
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
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif


#ifdef HAVE_CRL

#include <cyassl/internal.h>
#include <cyassl/error.h>

#include <dirent.h>
#include <string.h>


/* Initialze CRL members */
int InitCRL(CYASSL_CRL* crl, CYASSL_CERT_MANAGER* cm)
{
    CYASSL_ENTER("InitCRL");

    crl->cm = cm;
    crl->crlList = NULL;
    crl->monitors[0].path = NULL;
    crl->monitors[1].path = NULL;
#ifdef HAVE_CRL_MONITOR
    crl->tid = 0;
#endif
    if (InitMutex(&crl->crlLock) != 0)
        return BAD_MUTEX_ERROR; 

    return 0;
}


/* Initialze CRL Entry */
static int InitCRL_Entry(CRL_Entry* crle, DecodedCRL* dcrl)
{
    CYASSL_ENTER("InitCRL_Entry");

    XMEMCPY(crle->issuerHash, dcrl->issuerHash, SHA_DIGEST_SIZE);
    XMEMCPY(crle->crlHash, dcrl->crlHash, MD5_DIGEST_SIZE);
    XMEMCPY(crle->lastDate, dcrl->lastDate, MAX_DATE_SIZE);
    XMEMCPY(crle->nextDate, dcrl->nextDate, MAX_DATE_SIZE);
    crle->lastDateFormat = dcrl->lastDateFormat;
    crle->nextDateFormat = dcrl->nextDateFormat;

    crle->certs = dcrl->certs;   /* take ownsership */
    dcrl->certs = NULL;
    crle->totalCerts = dcrl->totalCerts;

    return 0;
}


/* Free all CRL Entry resources */
static void FreeCRL_Entry(CRL_Entry* crle)
{
    RevokedCert* tmp = crle->certs; 

    CYASSL_ENTER("FreeCRL_Entry");

    while(tmp) {
        RevokedCert* next = tmp->next;
        XFREE(tmp, NULL, DYNAMIC_TYPE_REVOKED);
        tmp = next;
    }
}



/* Free all CRL resources */
void FreeCRL(CYASSL_CRL* crl)
{
    CRL_Entry* tmp = crl->crlList;

    CYASSL_ENTER("FreeCRL");

    if (crl->monitors[0].path)
        XFREE(crl->monitors[0].path, NULL, DYNAMIC_TYPE_CRL_MONITOR);

    if (crl->monitors[1].path)
        XFREE(crl->monitors[1].path, NULL, DYNAMIC_TYPE_CRL_MONITOR);

    while(tmp) {
        CRL_Entry* next = tmp->next;
        FreeCRL_Entry(tmp);
        XFREE(tmp, NULL, DYNAMIC_TYPE_CRL_ENTRY);
        tmp = next;
    }	

#ifdef HAVE_CRL_MONITOR
    if (crl->tid != 0) {
        CYASSL_MSG("Canceling monitor thread");
        pthread_cancel(crl->tid);
    }
#endif
    FreeMutex(&crl->crlLock);
}


/* Is the cert ok with CRL, return 0 on success */
int CheckCertCRL(CYASSL_CRL* crl, DecodedCert* cert)
{
    CRL_Entry* crle;
    int        foundEntry = 0;
    int        revoked = 0;
    int        ret = 0;

    CYASSL_ENTER("CheckCertCRL");

    if (LockMutex(&crl->crlLock) != 0) {
        CYASSL_MSG("LockMutex failed");
        return BAD_MUTEX_ERROR;
    }

    crle = crl->crlList;

    while (crle) {
        if (XMEMCMP(crle->issuerHash, cert->issuerHash, SHA_DIGEST_SIZE) == 0) {
            CYASSL_MSG("Found CRL Entry on list");
            CYASSL_MSG("Checking next date validity");

            if (!ValidateDate(crle->nextDate, crle->nextDateFormat, AFTER)) {
                CYASSL_MSG("CRL next date is no longer valid");
                ret = ASN_AFTER_DATE_E;
            }
            else
                foundEntry = 1;
            break;
        }
        crle = crle->next;
    }

    if (foundEntry) {
        RevokedCert* rc = crle->certs;

        while (rc) {
            if (XMEMCMP(rc->serialNumber, cert->serial, rc->serialSz) == 0) {
                CYASSL_MSG("Cert revoked");
                revoked = 1;
                ret = CRL_CERT_REVOKED;
                break;
            }
            rc = rc->next;	
        }
    }

    UnLockMutex(&crl->crlLock);

    if (foundEntry == 0) {
        CYASSL_MSG("Couldn't find CRL for status check");
        ret = CRL_MISSING;
        if (crl->cm->cbMissingCRL) {
            char url[256];

            CYASSL_MSG("Issuing missing CRL callback");
            url[0] = '\0';
            if (cert->extCrlInfoSz < (int)sizeof(url) -1 ) {
                XMEMCPY(url, cert->extCrlInfo, cert->extCrlInfoSz);
                url[cert->extCrlInfoSz] = '\0';
            }
            else  {
                CYASSL_MSG("CRL url too long");
            }
            crl->cm->cbMissingCRL(url);
        }
    }


    return ret;	
}


/* Add Decoded CRL, 0 on success */
static int AddCRL(CYASSL_CRL* crl, DecodedCRL* dcrl)
{
    CRL_Entry* crle;

    CYASSL_ENTER("AddCRL");

    crle = (CRL_Entry*)XMALLOC(sizeof(CRL_Entry), NULL, DYNAMIC_TYPE_CRL_ENTRY);
    if (crle == NULL) {
        CYASSL_MSG("alloc CRL Entry failed");
        return -1;
    }

    if (InitCRL_Entry(crle, dcrl) < 0) {
        CYASSL_MSG("Init CRL Entry failed");
        XFREE(crle, NULL, DYNAMIC_TYPE_CRL_ENTRY);
        return -1;
    }

    if (LockMutex(&crl->crlLock) != 0) {
        CYASSL_MSG("LockMutex failed");
        FreeCRL_Entry(crle);
        XFREE(crle, NULL, DYNAMIC_TYPE_CRL_ENTRY);
        return BAD_MUTEX_ERROR;
    }
    crle->next = crl->crlList;
    crl->crlList = crle;
    UnLockMutex(&crl->crlLock);

    return 0;
}


/* Load CRL File of type, SSL_SUCCESS on ok */
int BufferLoadCRL(CYASSL_CRL* crl, const byte* buff, long sz, int type)
{
    int          ret = SSL_SUCCESS;
    const byte*  myBuffer = buff;    /* if DER ok, otherwise switch */
    buffer       der;
    DecodedCRL   dcrl;

    der.buffer = NULL;

    CYASSL_ENTER("BufferLoadCRL");

    if (crl == NULL || buff == NULL || sz == 0)
        return BAD_FUNC_ARG;

    if (type == SSL_FILETYPE_PEM) {
        int eccKey = 0;   /* not used */
        EncryptedInfo info;
        info.ctx = NULL;

        ret = PemToDer(buff, sz, CRL_TYPE, &der, NULL, &info, &eccKey);
        if (ret == 0) {
            myBuffer = der.buffer;
            sz = der.length;
        }
        else {
            CYASSL_MSG("Pem to Der failed");
            return -1;
        }
    }

    InitDecodedCRL(&dcrl);
    ret = ParseCRL(&dcrl, myBuffer, sz, crl->cm);
    if (ret != 0) {
        CYASSL_MSG("ParseCRL error");
    }
    else {
        ret = AddCRL(crl, &dcrl);
        if (ret != 0) {
            CYASSL_MSG("AddCRL error");
        }
    }
    FreeDecodedCRL(&dcrl);

    if (der.buffer)
        XFREE(der.buffer, NULL, DYNAMIC_TYPE_CRL);

    if (ret == 0)
        return SSL_SUCCESS;  /* convert */
    return ret;
}


#ifdef HAVE_CRL_MONITOR


/* read in new CRL entries and save new list */
static int SwapLists(CYASSL_CRL* crl)
{
    int        ret;
    CYASSL_CRL tmp;
    CRL_Entry* newList;

    if (InitCRL(&tmp, crl->cm) < 0) {
        CYASSL_MSG("Init tmp CRL failed");
        return -1;
    }

    if (crl->monitors[0].path) {
        ret = LoadCRL(&tmp, crl->monitors[0].path, SSL_FILETYPE_PEM, 0);
        if (ret != SSL_SUCCESS) {
            CYASSL_MSG("PEM LoadCRL on dir change failed");
            FreeCRL(&tmp);
            return -1;
        }
    }

    if (crl->monitors[1].path) {
        ret = LoadCRL(&tmp, crl->monitors[1].path, SSL_FILETYPE_ASN1, 0);
        if (ret != SSL_SUCCESS) {
            CYASSL_MSG("DER LoadCRL on dir change failed");
            FreeCRL(&tmp);
            return -1;
        }
    }

    if (LockMutex(&crl->crlLock) != 0) {
        CYASSL_MSG("LockMutex failed");
        FreeCRL(&tmp);
        return -1;
    }

    newList = tmp.crlList;

    /* swap lists */
    tmp.crlList  = crl->crlList;
    crl->crlList = newList;

    UnLockMutex(&crl->crlLock);

    FreeCRL(&tmp);

    return 0;
}


#ifdef __MACH__

#include <sys/event.h>
#include <sys/time.h>
#include <fcntl.h>

/* OS X  monitoring */
static void* DoMonitor(void* arg)
{
    int fPEM, fDER, kq;
    struct kevent change;

    CYASSL_CRL* crl = (CYASSL_CRL*)arg;

    CYASSL_ENTER("DoMonitor");

    kq = kqueue();
    if (kq == -1) {
        CYASSL_MSG("kqueue failed");
        return NULL;
    }

    fPEM = -1;
    fDER = -1;

    if (crl->monitors[0].path) {
        fPEM = open(crl->monitors[0].path, O_EVTONLY);
        if (fPEM == -1) {
            CYASSL_MSG("PEM event dir open failed");
            return NULL;
        }
    }

    if (crl->monitors[1].path) {
        fDER = open(crl->monitors[1].path, O_EVTONLY);
        if (fDER == -1) {
            CYASSL_MSG("DER event dir open failed");
            return NULL;
        }
    }

    if (fPEM != -1)
        EV_SET(&change, fPEM, EVFILT_VNODE, EV_ADD | EV_ENABLE | EV_ONESHOT,
                NOTE_DELETE | NOTE_EXTEND | NOTE_WRITE | NOTE_ATTRIB, 0, 0);

    if (fDER != -1)
        EV_SET(&change, fDER, EVFILT_VNODE, EV_ADD | EV_ENABLE | EV_ONESHOT,
                NOTE_DELETE | NOTE_EXTEND | NOTE_WRITE | NOTE_ATTRIB, 0, 0);

    for (;;) {
        struct kevent event;
        int           numEvents = kevent(kq, &change, 1, &event, 1, NULL);
       
        CYASSL_MSG("Got kevent");

        if (numEvents == -1) {
            CYASSL_MSG("kevent problem, continue");
            continue;
        }

        if (SwapLists(crl) < 0) {
            CYASSL_MSG("SwapLists problem, continue");
        }
    }

    return NULL;
}


#elif __linux__

#include <sys/types.h>
#include <sys/inotify.h>
#include <unistd.h>

/* linux monitoring */
static void* DoMonitor(void* arg)
{
    int         notifyFd;
    int         wd;
    CYASSL_CRL* crl = (CYASSL_CRL*)arg;

    CYASSL_ENTER("DoMonitor");

    notifyFd = inotify_init();
    if (notifyFd < 0) {
        CYASSL_MSG("inotify failed");
        return NULL;
    }

    if (crl->monitors[0].path) {
        wd = inotify_add_watch(notifyFd, crl->monitors[0].path, IN_CLOSE_WRITE |
                                                                IN_DELETE);
        if (wd < 0) {
            CYASSL_MSG("PEM notify add watch failed");
            return NULL;
        }
    }

    if (crl->monitors[1].path) {
        wd = inotify_add_watch(notifyFd, crl->monitors[1].path, IN_CLOSE_WRITE |
                                                                IN_DELETE);
        if (wd < 0) {
            CYASSL_MSG("DER notify add watch failed");
            return NULL;
        }
    }

    for (;;) {
        char          buffer[8192];
        int           length = read(notifyFd, buffer, sizeof(buffer));
       
        CYASSL_MSG("Got notify event");

        if (length < 0) {
            CYASSL_MSG("notify read problem, continue");
            continue;
        } 

        if (SwapLists(crl) < 0) {
            CYASSL_MSG("SwapLists problem, continue");
        }
    }

    return NULL;
}



#endif /* MACH or linux */


/* Start Monitoring the CRL path(s) in a thread */
static int StartMonitorCRL(CYASSL_CRL* crl)
{
    pthread_attr_t attr;

    CYASSL_ENTER("StartMonitorCRL");

    if (crl == NULL) 
        return BAD_FUNC_ARG;

    if (crl->tid != 0) {
        CYASSL_MSG("Monitor thread already running");
        return MONITOR_RUNNING_E;
    }

    pthread_attr_init(&attr);

    if (pthread_create(&crl->tid, &attr, DoMonitor, crl) != 0) {
        CYASSL_MSG("Thread creation error");
        return THREAD_CREATE_E;
    }

    return SSL_SUCCESS;
}


#else /* HAVE_CRL_MONITOR */

static int StartMonitorCRL(CYASSL_CRL* crl)
{
    CYASSL_ENTER("StartMonitorCRL");
    CYASSL_MSG("Not compiled in");

    return NOT_COMPILED_IN;
}

#endif  /* HAVE_CRL_MONITOR */


/* Load CRL path files of type, SSL_SUCCESS on ok */ 
int LoadCRL(CYASSL_CRL* crl, const char* path, int type, int monitor)
{
    struct dirent* entry;
    DIR*   dir;
    int    ret = SSL_SUCCESS;

    CYASSL_ENTER("LoadCRL");
    if (crl == NULL)
        return BAD_FUNC_ARG;

    dir = opendir(path);
    if (dir == NULL) {
        CYASSL_MSG("opendir path crl load failed");
        return BAD_PATH_ERROR;
    }
    while ( (entry = readdir(dir)) != NULL) {
        if (entry->d_type & DT_REG) {
            char name[MAX_FILENAME_SZ];

            if (type == SSL_FILETYPE_PEM) {
                if (strstr(entry->d_name, ".pem") == NULL) {
                    CYASSL_MSG("not .pem file, skipping");
                    continue;
                }
            }
            else {
                if (strstr(entry->d_name, ".der") == NULL &&
                    strstr(entry->d_name, ".crl") == NULL) {

                    CYASSL_MSG("not .der or .crl file, skipping");
                    continue;
                }
            }

            XMEMSET(name, 0, sizeof(name));
            XSTRNCPY(name, path, MAX_FILENAME_SZ/2 - 2);
            XSTRNCAT(name, "/", 1);
            XSTRNCAT(name, entry->d_name, MAX_FILENAME_SZ/2);

            if (ProcessFile(NULL, name, type, CRL_TYPE, NULL, 0, crl)
                                                               != SSL_SUCCESS) {
                CYASSL_MSG("CRL file load failed, continuing");
            }
        }
    }

    if (monitor & CYASSL_CRL_MONITOR) {
        CYASSL_MSG("monitor path requested");

        if (type == SSL_FILETYPE_PEM) {
            crl->monitors[0].path = strdup(path);
            crl->monitors[0].type = SSL_FILETYPE_PEM;
            if (crl->monitors[0].path == NULL)
                ret = MEMORY_E;
        } else {
            crl->monitors[1].path = strdup(path);
            crl->monitors[1].type = SSL_FILETYPE_ASN1;
            if (crl->monitors[1].path == NULL)
                ret = MEMORY_E;
        }
      
        if (monitor & CYASSL_CRL_START_MON) {
            CYASSL_MSG("start monitoring requested");
    
            ret = StartMonitorCRL(crl);
       } 
    }

    return ret;
}

#endif /* HAVE_CRL */
