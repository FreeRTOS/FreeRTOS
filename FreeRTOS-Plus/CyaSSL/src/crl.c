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
	if (InitMutex(&crl->crlLock) != 0)
		return BAD_MUTEX_ERROR; 

	return 0;
}


/* Initialze CRL Entry */
static int InitCRL_Entry(CRL_Entry* crle, DecodedCRL* dcrl)
{
	CYASSL_ENTER("FreeCRL_Entry");

	XMEMCPY(crle->issuerHash, dcrl->issuerHash, SHA_DIGEST_SIZE);
	XMEMCPY(crle->crlHash, dcrl->crlHash, MD5_DIGEST_SIZE);
	XMEMCPY(crle->lastDate, dcrl->lastDate, MAX_DATE_SIZE);
	XMEMCPY(crle->nextDate, dcrl->nextDate, MAX_DATE_SIZE);

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

    while(tmp) {
        CRL_Entry* next = tmp->next;
        FreeCRL_Entry(tmp);
        XFREE(tmp, NULL, DYNAMIC_TYPE_CRL_ENTRY);
        tmp = next;
    }	

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
		return -1;
	}

	if (LockMutex(&crl->crlLock) != 0) {
		CYASSL_MSG("LockMutex failed");
		FreeCRL_Entry(crle);
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
	ret = ParseCRL(&dcrl, myBuffer, sz);
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
	while ( ret == SSL_SUCCESS && (entry = readdir(dir)) != NULL) {
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

			ret = ProcessFile(NULL, name, type, CRL_TYPE, NULL, 0, crl);
		}
	}

    if (monitor) {
        CYASSL_MSG("monitor path requested");
    }

	return SSL_SUCCESS;
}

#endif /* HAVE_CRL */
