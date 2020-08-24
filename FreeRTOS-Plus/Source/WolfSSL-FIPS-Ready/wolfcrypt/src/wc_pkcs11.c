/* wc_pkcs11.c
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#ifdef HAVE_PKCS11

#include <dlfcn.h>

#include <wolfssl/wolfcrypt/wc_pkcs11.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/asn.h>
#include <wolfssl/wolfcrypt/logging.h>
#ifndef NO_RSA
    #include <wolfssl/wolfcrypt/rsa.h>
#endif
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif

#define MAX_EC_PARAM_LEN   16

#if defined(NO_PKCS11_RSA) && !defined(NO_RSA)
    #define NO_RSA
#endif
#if defined(NO_PKCS11_ECC) && defined(HAVE_ECC)
    #undef HAVE_ECC
#endif
#if defined(NO_PKCS11_AES) && !defined(NO_AES)
    #define NO_AES
#endif
#if defined(NO_PKCS11_AESGCM) && defined(HAVE_AESGCM)
    #undef HAVE_AESGCM
#endif
#if defined(NO_PKCS11_AESCBC) && defined(HAVE_AES_CBC)
    #undef HAVE_AES_CBC
#endif
#if defined(NO_PKCS11_HMAC) && !defined(NO_HMAC)
    #define NO_HMAC
#endif
#if defined(NO_PKCS11_RNG) && !defined(WC_NO_RNG)
    #define WC_NO_RNG
#endif


#if defined(HAVE_ECC) && !defined(NO_PKCS11_ECDH)
static CK_BBOOL ckFalse = CK_FALSE;
#endif
#if !defined(NO_RSA) || defined(HAVE_ECC) || (!defined(NO_AES) && \
           (defined(HAVE_AESGCM) || defined(HAVE_AES_CBC))) || !defined(NO_HMAC)
static CK_BBOOL ckTrue  = CK_TRUE;
#endif

#ifndef NO_RSA
static CK_KEY_TYPE rsaKeyType  = CKK_RSA;
#endif
#ifdef HAVE_ECC
static CK_KEY_TYPE ecKeyType   = CKK_EC;
#endif
#if !defined(NO_RSA) || defined(HAVE_ECC)
static CK_OBJECT_CLASS pubKeyClass     = CKO_PUBLIC_KEY;
static CK_OBJECT_CLASS privKeyClass    = CKO_PRIVATE_KEY;
#endif
#if (!defined(NO_AES) && (defined(HAVE_AESGCM) || defined(HAVE_AES_CBC))) || \
            !defined(NO_HMAC) || (defined(HAVE_ECC) && !defined(NO_PKCS11_ECDH))
static CK_OBJECT_CLASS secretKeyClass  = CKO_SECRET_KEY;
#endif

/**
 * Load library, get function list and initialize PKCS#11.
 *
 * @param  dev     [in]  Device object.
 * @param  library [in]  Library name including path.
 * @return  BAD_FUNC_ARG when dev or library are NULL pointers.
 *          BAD_PATH_ERROR when dynamic library cannot be opened.
 *          WC_INIT_E when the initialization PKCS#11 fails.
 *          WC_HW_E when unable to get PKCS#11 function list.
 *          0 on success.
 */
int wc_Pkcs11_Initialize(Pkcs11Dev* dev, const char* library, void* heap)
{
    int                  ret = 0;
    void*                func;
    CK_C_INITIALIZE_ARGS args;

    if (dev == NULL || library == NULL)
        ret = BAD_FUNC_ARG;

    if (ret == 0) {
        dev->heap = heap;
        dev->dlHandle = dlopen(library, RTLD_NOW | RTLD_LOCAL);
        if (dev->dlHandle == NULL) {
            WOLFSSL_MSG(dlerror());
            ret = BAD_PATH_ERROR;
        }
    }

    if (ret == 0) {
        dev->func = NULL;
        func = dlsym(dev->dlHandle, "C_GetFunctionList");
        if (func == NULL)
            ret = WC_HW_E;
    }
    if (ret == 0) {
        if (((CK_C_GetFunctionList)func)(&dev->func) != CKR_OK)
            ret = WC_HW_E;
    }

    if (ret == 0) {
        XMEMSET(&args, 0x00, sizeof(args));
        args.flags = CKF_OS_LOCKING_OK;
        if (dev->func->C_Initialize(&args) != CKR_OK)
            ret = WC_INIT_E;
    }

    if (ret != 0)
        wc_Pkcs11_Finalize(dev);

    return ret;
}

/**
 * Close the Pkcs#11 library.
 *
 * @param  dev  [in]  Device object.
 */
void wc_Pkcs11_Finalize(Pkcs11Dev* dev)
{
    if (dev != NULL && dev->dlHandle != NULL) {
        if (dev->func != NULL) {
            dev->func->C_Finalize(NULL);
            dev->func = NULL;
        }
        dlclose(dev->dlHandle);
        dev->dlHandle = NULL;
    }
}

/**
 * Set up a token for use.
 *
 * @param  token      [in]  Token object.
 * @param  dev        [in]  PKCS#11 device object.
 * @param  slotId     [in]  Slot number of the token.<br>
 *                          Passing -1 uses the first available slot.
 * @param  tokenName  [in]  Name of token to initialize.
 * @param  userPin    [in]  PIN to use to login as user.
 * @param  userPinSz  [in]  Number of bytes in PIN.
 * @return  BAD_FUNC_ARG when token, dev and/or tokenName is NULL.
 *          WC_INIT_E when initializing token fails.
 *          WC_HW_E when another PKCS#11 library call fails.
 *          -1 when no slot available.
 *          0 on success.
 */
int wc_Pkcs11Token_Init(Pkcs11Token* token, Pkcs11Dev* dev, int slotId,
    const char* tokenName, const unsigned char* userPin, int userPinSz)
{
    int         ret = 0;
    CK_RV       rv;
    CK_SLOT_ID* slot = NULL;
    CK_ULONG    slotCnt = 0;

    if (token == NULL || dev == NULL || tokenName == NULL)
        ret = BAD_FUNC_ARG;

    if (ret == 0) {
        if (slotId < 0) {
            /* Use first available slot with a token. */
            rv = dev->func->C_GetSlotList(CK_TRUE, NULL, &slotCnt);
            if (rv != CKR_OK)
                ret = WC_HW_E;
            if (ret == 0) {
                slot = (CK_SLOT_ID*)XMALLOC(slotCnt * sizeof(*slot), dev->heap,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
                if (slot == NULL)
                    ret = MEMORY_E;
            }
            if (ret == 0) {
                rv = dev->func->C_GetSlotList(CK_TRUE, slot, &slotCnt);
                if (rv != CKR_OK)
                    ret = WC_HW_E;
            }
            if (ret == 0) {
                if (slotCnt > 0)
                    slotId = (int)slot[0];
                else
                    ret = WC_HW_E;
            }
        }
    }
    if (ret == 0) {
        token->func = dev->func;
        token->slotId = (CK_SLOT_ID)slotId;
        token->handle = NULL_PTR;
        token->userPin = (CK_UTF8CHAR_PTR)userPin;
        token->userPinSz = (CK_ULONG)userPinSz;
    }

    if (slot != NULL)
        XFREE(slot, dev->heap, DYNAMIC_TYPE_TMP_BUFFER);

    return ret;
}

/**
 * Finalize token.
 * Closes all sessions on token.
 *
 * @param  token  [in]  Token object.
 */
void wc_Pkcs11Token_Final(Pkcs11Token* token)
{
    if (token != NULL && token->func != NULL) {
        token->func->C_CloseAllSessions(token->slotId);
        token->handle = NULL_PTR;
        ForceZero(token->userPin, (word32)token->userPinSz);
    }
}

/**
 * Open a session on a token.
 *
 * @param  token      [in]  Token object.
 * @param  session    [in]  Session object.
 * @param  readWrite  [in]  Boolean indicating to open session for Read/Write.
 * @return  BAD_FUNC_ARG when token or session is NULL.
 *          WC_HW_E when opening the session fails.
 *          0 on success.
 */
static int Pkcs11OpenSession(Pkcs11Token* token, Pkcs11Session* session,
                             int readWrite)
{
    int   ret = 0;
    CK_RV rv;

    if (token == NULL || session == NULL)
        ret = BAD_FUNC_ARG;

    if (ret == 0) {
        if (token->handle != NULL_PTR)
            session->handle = token->handle;
        else {
            /* Create a new session. */
            CK_FLAGS flags = CKF_SERIAL_SESSION;

            if (readWrite)
                flags |= CKF_RW_SESSION;

            rv = token->func->C_OpenSession(token->slotId, flags,
                                            (CK_VOID_PTR)NULL, (CK_NOTIFY)NULL,
                                            &session->handle);
            if (rv != CKR_OK)
                ret = WC_HW_E;
            if (ret == 0 && token->userPin != NULL) {
                rv = token->func->C_Login(session->handle, CKU_USER,
                                              token->userPin, token->userPinSz);
                if (rv != CKR_OK)
                    ret = WC_HW_E;
            }
        }
    }
    if (ret == 0) {
        session->func = token->func;
        session->slotId = token->slotId;
    }

    return ret;
}

/**
 * Close a session on a token.
 * Won't close a session created externally.
 *
 * @param  token    [in]  Token object.
 * @param  session  [in]  Session object.
 */
static void Pkcs11CloseSession(Pkcs11Token* token, Pkcs11Session* session)
{
    if (token != NULL && session != NULL && token->handle != session->handle) {
        if (token->userPin != NULL)
            session->func->C_Logout(session->handle);
        session->func->C_CloseSession(session->handle);
    }
}

/**
 * Open a session on the token to be used for all operations.
 *
 * @param  token      [in]  Token object.
 * @param  readWrite  [in]  Boolean indicating to open session for Read/Write.
 * @return  BAD_FUNC_ARG when token is NULL.
 *          WC_HW_E when opening the session fails.
 *          0 on success.
 */
int wc_Pkcs11Token_Open(Pkcs11Token* token, int readWrite)
{
    int ret = 0;
    Pkcs11Session session;

    if (token == NULL)
        ret = BAD_FUNC_ARG;

    if (ret == 0) {
        ret = Pkcs11OpenSession(token, &session, readWrite);
        token->handle = session.handle;
    }

    return ret;
}

/**
 * Close the token's session.
 * All object, like keys, will be destroyed.
 *
 * @param  token    [in]  Token object.
 */
void wc_Pkcs11Token_Close(Pkcs11Token* token)
{
    Pkcs11Session session;

    if (token != NULL) {
        session.func = token->func;
        session.handle = token->handle;
        token->handle = NULL_PTR;
        Pkcs11CloseSession(token, &session);
    }
}


#if (!defined(NO_AES) && (defined(HAVE_AESGCM) || defined(HAVE_AES_CBC))) || \
                                                               !defined(NO_HMAC)
static int Pkcs11CreateSecretKey(CK_OBJECT_HANDLE* key, Pkcs11Session* session,
                                 CK_KEY_TYPE keyType, unsigned char* data,
                                 int len, unsigned char* id, int idLen)
{
    int              ret = 0;
    CK_RV            rv;
    CK_ATTRIBUTE     keyTemplate[] = {
        { CKA_CLASS,    &secretKeyClass, sizeof(secretKeyClass) },
        { CKA_KEY_TYPE, &keyType,        sizeof(keyType)        },
        { CKA_ENCRYPT,  &ckTrue,         sizeof(ckTrue)         },
        { CKA_VALUE,    NULL,            0                      },
        { CKA_ID,       id,              (CK_ULONG)idLen        }
    };
    int              keyTmplCnt = 4;

    WOLFSSL_MSG("PKCS#11: Create Secret Key");

    /* Set the modulus and public exponent data. */
    keyTemplate[3].pValue     = data;
    keyTemplate[3].ulValueLen = (CK_ULONG)len;

    if (idLen > 0)
        keyTmplCnt++;

    /* Create an object containing key data for device to use. */
    rv = session->func->C_CreateObject(session->handle, keyTemplate, keyTmplCnt,
                                                                           key);
    if (rv != CKR_OK)
        ret = WC_HW_E;

    return ret;
}
#endif

#ifndef NO_RSA
/**
 * Create a PKCS#11 object containing the RSA private key data.
 *
 * @param  privateKey [out]  Henadle to private key object.
 * @param  session    [in]   Session object.
 * @param  rsaKey     [in]   RSA key with private key data.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          0 on success.
 */
static int Pkcs11CreateRsaPrivateKey(CK_OBJECT_HANDLE* privateKey,
                                     Pkcs11Session* session,
                                     RsaKey* rsaKey)
{
    int             ret = 0;
    CK_RV           rv;
    CK_ATTRIBUTE    keyTemplate[] = {
        { CKA_CLASS,            &privKeyClass, sizeof(privKeyClass) },
        { CKA_KEY_TYPE,         &rsaKeyType,   sizeof(rsaKeyType)   },
        { CKA_DECRYPT,          &ckTrue,       sizeof(ckTrue)       },
        { CKA_MODULUS,          NULL,          0                    },
        { CKA_PRIVATE_EXPONENT, NULL,          0                    },
        { CKA_PRIME_1,          NULL,          0                    },
        { CKA_PRIME_2,          NULL,          0                    },
        { CKA_EXPONENT_1,       NULL,          0                    },
        { CKA_EXPONENT_2,       NULL,          0                    },
        { CKA_COEFFICIENT,      NULL,          0                    },
        { CKA_PUBLIC_EXPONENT,  NULL,          0                    }
    };
    CK_ULONG        keyTmplCnt = sizeof(keyTemplate) / sizeof(*keyTemplate);

    /* Set the modulus and private key data. */
    keyTemplate[ 3].pValue     = rsaKey->n.raw.buf;
    keyTemplate[ 3].ulValueLen = rsaKey->n.raw.len;
    keyTemplate[ 4].pValue     = rsaKey->d.raw.buf;
    keyTemplate[ 4].ulValueLen = rsaKey->d.raw.len;
    keyTemplate[ 5].pValue     = rsaKey->p.raw.buf;
    keyTemplate[ 5].ulValueLen = rsaKey->p.raw.len;
    keyTemplate[ 6].pValue     = rsaKey->q.raw.buf;
    keyTemplate[ 6].ulValueLen = rsaKey->q.raw.len;
    keyTemplate[ 7].pValue     = rsaKey->dP.raw.buf;
    keyTemplate[ 7].ulValueLen = rsaKey->dP.raw.len;
    keyTemplate[ 8].pValue     = rsaKey->dQ.raw.buf;
    keyTemplate[ 8].ulValueLen = rsaKey->dQ.raw.len;
    keyTemplate[ 9].pValue     = rsaKey->u.raw.buf;
    keyTemplate[ 9].ulValueLen = rsaKey->u.raw.len;
    keyTemplate[10].pValue     = rsaKey->e.raw.buf;
    keyTemplate[10].ulValueLen = rsaKey->e.raw.len;

    rv = session->func->C_CreateObject(session->handle, keyTemplate, keyTmplCnt,
                                                                    privateKey);
    if (rv != CKR_OK)
        ret = WC_HW_E;

    return ret;
}
#endif

#ifdef HAVE_ECC
/**
 * Set the ECC parameters into the template.
 *
 * @param  key   [in]  ECC key.
 * @param  tmpl  [in]  PKCS#11 template.
 * @param  idx   [in]  Index of template to put parameters into.
 * @return NOT_COMPILE_IN when the EC parameters are not known.
 *         0 on success.
 */
static int Pkcs11EccSetParams(ecc_key* key, CK_ATTRIBUTE* tmpl, int idx)
{
    int ret = 0;

    if (key->dp != NULL && key->dp->oid != NULL) {
        unsigned char* derParams = tmpl[idx].pValue;
        /* ASN.1 encoding: OBJ + ecc parameters OID */
        tmpl[idx].ulValueLen = key->dp->oidSz + 2;
        derParams[0] = ASN_OBJECT_ID;
        derParams[1] = key->dp->oidSz;
        XMEMCPY(derParams + 2, key->dp->oid, key->dp->oidSz);
    }
    else
        ret = NOT_COMPILED_IN;

    return ret;
}

/**
 * Create a PKCS#11 object containing the ECC private key data.
 *
 * @param  privateKey   [out]  Henadle to private key object.
 * @param  session      [in]   Session object.
 * @param  private_key  [in]   ECC private key.
 * @param  operation    [in]   Cryptographic operation key is to be used for.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          0 on success.
 */
static int Pkcs11CreateEccPrivateKey(CK_OBJECT_HANDLE* privateKey,
                                     Pkcs11Session* session,
                                     ecc_key* private_key,
                                     CK_ATTRIBUTE_TYPE operation)
{
    int             ret = 0;
    CK_RV           rv;
    CK_UTF8CHAR     params[MAX_EC_PARAM_LEN];
    CK_ATTRIBUTE    keyTemplate[] = {
        { CKA_CLASS,     &privKeyClass, sizeof(privKeyClass) },
        { CKA_KEY_TYPE,  &ecKeyType,    sizeof(ecKeyType)    },
        { operation,     &ckTrue,       sizeof(ckTrue)       },
        { CKA_EC_PARAMS, params,        0                    },
        { CKA_VALUE,     NULL,          0                    }
    };
    CK_ULONG        keyTmplCnt = sizeof(keyTemplate) / sizeof(*keyTemplate);

    ret = Pkcs11EccSetParams(private_key, keyTemplate, 3);
    if (ret == 0) {
        keyTemplate[4].pValue     = private_key->k.raw.buf;
        keyTemplate[4].ulValueLen = private_key->k.raw.len;

        rv = session->func->C_CreateObject(session->handle, keyTemplate,
                                                        keyTmplCnt, privateKey);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }

    return ret;
}
#endif

#if !defined(NO_RSA) || defined(HAVE_ECC) || (!defined(NO_AES) && \
           (defined(HAVE_AESGCM) || defined(HAVE_AES_CBC))) || !defined(NO_HMAC)
/**
 * Check if mechanism is available in session on token.
 *
 * @param  session  [in]  Session object.
 * @param  mech     [in]  Mechanism to look for.
 * @return  NOT_COMPILED_IN when mechanism not available.
 *          0 when mechanism is available.
 */
static int Pkcs11MechAvail(Pkcs11Session* session, CK_MECHANISM_TYPE mech)
{
    int               ret = 0;
    CK_RV             rv;
    CK_MECHANISM_INFO mechInfo;

    rv = session->func->C_GetMechanismInfo(session->slotId, mech, &mechInfo);
    if (rv != CKR_OK)
        ret = NOT_COMPILED_IN;

    return ret;
}
#endif

#ifndef NO_HMAC
/**
 * Return the mechanism type and key type for the digest type when using HMAC.
 *
 * @param  macType   [in]  Digest type - e.g. WC_SHA256.
 * @param  mechType  [in]  Mechanism type - e.g. CKM_SHA256_HMAC.
 * @param  keyType   [in]  Key type - e.g. CKK_SHA256_HMAC.
 * @return  NOT_COMPILED_IN if the digest algorithm isn't recognised.
 *          0 otherwise.
 */
static int Pkcs11HmacTypes(int macType, int* mechType, int* keyType)
{
    int ret = 0;

    switch (macType)
    {
    #ifndef NO_MD5
        case WC_MD5:
            *mechType = CKM_MD5_HMAC;
            *keyType = CKK_MD5_HMAC;
            break;
    #endif
    #ifndef NO_SHA
        case WC_SHA:
            *mechType = CKM_SHA_1_HMAC;
            *keyType = CKK_SHA_1_HMAC;
            break;
    #endif
    #ifdef WOLFSSL_SHA224
        case WC_SHA224:
            *mechType = CKM_SHA224_HMAC;
            *keyType = CKK_SHA224_HMAC;
            break;
    #endif
    #ifndef NO_SHA256
        case WC_SHA256:
            *mechType = CKM_SHA256_HMAC;
            *keyType = CKK_SHA256_HMAC;
            break;
    #endif
    #ifdef WOLFSSL_SHA384
        case WC_SHA384:
            *mechType = CKM_SHA384_HMAC;
            *keyType = CKK_SHA384_HMAC;
            break;
    #endif
    #ifdef WOLFSSL_SHA512
        case WC_SHA512:
            *mechType = CKM_SHA512_HMAC;
            *keyType = CKK_SHA512_HMAC;
            break;
    #endif
        default:
            ret = NOT_COMPILED_IN;
            break;
    }

    return ret;
}
#endif

/**
 * Store the private key on the token in the session.
 *
 * @param  token  [in]  Token to store private key on.
 * @param  type   [in]  Key type.
 * @param  clear  [in]  Clear out the private data from software key.
 * @param  key    [in]  Key type specific object.
 * @return  NOT_COMPILED_IN when mechanism not available.
 *          0 on success.
 */
int wc_Pkcs11StoreKey(Pkcs11Token* token, int type, int clear, void* key)
{
    int               ret = 0;
    Pkcs11Session     session;
    CK_OBJECT_HANDLE  privKey = NULL_PTR;

    ret = Pkcs11OpenSession(token, &session, 1);
    if (ret == 0) {
        switch (type) {
    #if !defined(NO_AES) && defined(HAVE_AESGCM)
            case PKCS11_KEY_TYPE_AES_GCM: {
                Aes* aes = (Aes*)key;

                ret = Pkcs11MechAvail(&session, CKM_AES_GCM);
                if (ret == 0) {
                    ret = Pkcs11CreateSecretKey(&privKey, &session, CKK_AES,
                                                (unsigned char*)aes->devKey,
                                                aes->keylen,
                                                (unsigned char*)aes->id,
                                                aes->idLen);
                }
                if (ret == 0 && clear)
                    ForceZero(aes->devKey, aes->keylen);
                break;
            }
    #endif
    #if !defined(NO_AES) && defined(HAVE_AES_CBC)
            case PKCS11_KEY_TYPE_AES_CBC: {
                Aes* aes = (Aes*)key;

                ret = Pkcs11MechAvail(&session, CKM_AES_CBC);
                if (ret == 0) {
                    ret = Pkcs11CreateSecretKey(&privKey, &session, CKK_AES,
                                                (unsigned char*)aes->devKey,
                                                aes->keylen,
                                                (unsigned char*)aes->id,
                                                aes->idLen);
                }
                if (ret == 0 && clear)
                    ForceZero(aes->devKey, aes->keylen);
                break;
            }
    #endif
    #ifndef NO_HMAC
            case PKCS11_KEY_TYPE_HMAC: {
                Hmac* hmac = (Hmac*)key;
                int mechType;
                int keyType;

                ret = Pkcs11HmacTypes(hmac->macType, &mechType, &keyType);
                if (ret == NOT_COMPILED_IN)
                    break;

                if (ret == 0)
                    ret = Pkcs11MechAvail(&session, mechType);
                if (ret == 0) {
                    ret = Pkcs11CreateSecretKey(&privKey, &session, keyType,
                                                (unsigned char*)hmac->keyRaw,
                                                hmac->keyLen,
                                                (unsigned char*)hmac->id,
                                                hmac->idLen);
                    if (ret == WC_HW_E) {
                        ret = Pkcs11CreateSecretKey(&privKey, &session,
                                                   CKK_GENERIC_SECRET,
                                                   (unsigned char*)hmac->keyRaw,
                                                   hmac->keyLen,
                                                   (unsigned char*)hmac->id,
                                                   hmac->idLen);
                    }
                }
                break;
            }
    #endif
    #ifndef NO_RSA
            case PKCS11_KEY_TYPE_RSA: {
                RsaKey* rsaKey = (RsaKey*)key;

                ret = Pkcs11MechAvail(&session, CKM_RSA_X_509);
                if (ret == 0)
                    ret = Pkcs11CreateRsaPrivateKey(&privKey, &session, rsaKey);
                if (ret == 0 && clear) {
                    mp_forcezero(&rsaKey->u);
                    mp_forcezero(&rsaKey->dQ);
                    mp_forcezero(&rsaKey->dP);
                    mp_forcezero(&rsaKey->q);
                    mp_forcezero(&rsaKey->p);
                    mp_forcezero(&rsaKey->d);
                }
                break;
            }
    #endif
    #ifdef HAVE_ECC
            case PKCS11_KEY_TYPE_EC: {
                ecc_key* eccKey = (ecc_key*)key;
                int      ret2 = NOT_COMPILED_IN;

        #ifndef NO_PKCS11_ECDH
                /* Try ECDH mechanism first. */
                ret = Pkcs11MechAvail(&session, CKM_ECDH1_DERIVE);
                if (ret == 0) {
                    ret = Pkcs11CreateEccPrivateKey(&privKey, &session, eccKey,
                                                                    CKA_DERIVE);
                }
         #endif
                if (ret == 0 || ret == NOT_COMPILED_IN) {
                    /* Try ECDSA mechanism next. */
                    ret2 = Pkcs11MechAvail(&session, CKM_ECDSA);
                    if (ret2 == 0) {
                        ret2 = Pkcs11CreateEccPrivateKey(&privKey, &session,
                                                              eccKey, CKA_SIGN);
                    }
                    /* OK for this to fail if set for ECDH. */
                    if (ret == NOT_COMPILED_IN)
                        ret = ret2;
                }
                if (ret == 0 && clear)
                    mp_forcezero(&eccKey->k);
                break;
            }
    #endif
            default:
                ret = NOT_COMPILED_IN;
                break;
        }

        Pkcs11CloseSession(token, &session);
    }

    (void)privKey;
    (void)clear;
    (void)key;

    return ret;
}

#if !defined(NO_RSA) || defined(HAVE_ECC) || (!defined(NO_AES) && \
           (defined(HAVE_AESGCM) || defined(HAVE_AES_CBC))) || !defined(NO_HMAC)
/**
 * Find the PKCS#11 object containing the RSA public or private key data with
 * the modulus specified.
 *
 * @param  key       [out]  Henadle to key object.
 * @param  keyClass  [in]   Public or private key class.
 * @param  keyType   [in]   Type of key.
 * @param  session   [in]   Session object.
 * @param  id        [in]   Identifier set against a key.
 * @param  idLen     [in]   Length of identifier.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          0 on success.
 */
static int Pkcs11FindKeyById(CK_OBJECT_HANDLE* key, CK_OBJECT_CLASS keyClass,
                             CK_KEY_TYPE keyType, Pkcs11Session* session,
                             byte* id, int idLen)
{
    int             ret = 0;
    CK_RV           rv;
    CK_ULONG        count;
    CK_ATTRIBUTE    keyTemplate[] = {
        { CKA_CLASS,           &keyClass, sizeof(keyClass) },
        { CKA_KEY_TYPE,        &keyType,  sizeof(keyType)  },
        { CKA_ID,              id,        (CK_ULONG)idLen  }
    };
    CK_ULONG        keyTmplCnt = sizeof(keyTemplate) / sizeof(*keyTemplate);

    WOLFSSL_MSG("PKCS#11: Find Key By Id");

    rv = session->func->C_FindObjectsInit(session->handle, keyTemplate,
                                                                    keyTmplCnt);
    if (rv != CKR_OK)
        ret = WC_HW_E;
    if (ret == 0) {
        rv = session->func->C_FindObjects(session->handle, key, 1, &count);
        if (rv != CKR_OK)
            ret = WC_HW_E;
        rv = session->func->C_FindObjectsFinal(session->handle);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }
    if (ret == 0 && count == 0)
        ret = WC_HW_E;

    return ret;
}
#endif

#ifndef NO_RSA
/**
 * Find the PKCS#11 object containing the RSA public or private key data with
 * the modulus specified.
 *
 * @param  key       [out]  Henadle to key object.
 * @param  keyClass  [in]   Public or private key class.
 * @param  session   [in]   Session object.
 * @param  rsaKey    [in]   RSA key with modulus to search on.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          0 on success.
 */
static int Pkcs11FindRsaKey(CK_OBJECT_HANDLE* key, CK_OBJECT_CLASS keyClass,
                            Pkcs11Session* session, RsaKey* rsaKey)
{
    int             ret = 0;
    CK_RV           rv;
    CK_ULONG        count;
    CK_ATTRIBUTE    keyTemplate[] = {
        { CKA_CLASS,           &keyClass,   sizeof(keyClass)   },
        { CKA_KEY_TYPE,        &rsaKeyType, sizeof(rsaKeyType) },
        { CKA_MODULUS,         NULL,        0                  },
    };
    CK_ULONG        keyTmplCnt = sizeof(keyTemplate) / sizeof(*keyTemplate);

    /* Set the modulus. */
    keyTemplate[2].pValue     = rsaKey->n.raw.buf;
    keyTemplate[2].ulValueLen = rsaKey->n.raw.len;

    rv = session->func->C_FindObjectsInit(session->handle, keyTemplate,
                                                                    keyTmplCnt);
    if (rv != CKR_OK)
        ret = WC_HW_E;
    if (ret == 0) {
        rv = session->func->C_FindObjects(session->handle, key, 1, &count);
        if (rv != CKR_OK)
            ret = WC_HW_E;
        rv = session->func->C_FindObjectsFinal(session->handle);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }

    return ret;
}

/**
 * Exponentiate the input with the public part of the RSA key.
 * Used in public encrypt and decrypt.
 *
 * @param  session  [in]  Session object.
 * @param  info     [in]  Cryptographic operation data.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          0 on success.
 */
static int Pkcs11RsaPublic(Pkcs11Session* session, wc_CryptoInfo* info)
{
    int              ret = 0;
    CK_RV            rv;
    CK_MECHANISM     mech;
    CK_ULONG         outLen;
    CK_OBJECT_HANDLE publicKey = NULL_PTR;
    int              sessionKey = 0;
    CK_ATTRIBUTE     keyTemplate[] = {
        { CKA_CLASS,           &pubKeyClass, sizeof(pubKeyClass) },
        { CKA_KEY_TYPE,        &rsaKeyType,  sizeof(rsaKeyType)  },
        { CKA_ENCRYPT,         &ckTrue,      sizeof(ckTrue)      },
        { CKA_MODULUS,         NULL,         0                   },
        { CKA_PUBLIC_EXPONENT, NULL,         0                   }
    };
    CK_ULONG        keyTmplCnt = sizeof(keyTemplate) / sizeof(*keyTemplate);

    WOLFSSL_MSG("PKCS#11: RSA Public Key Operation");

    if (info->pk.rsa.outLen == NULL) {
        ret = BAD_FUNC_ARG;
    }

    if (ret == 0) {
        if ((sessionKey = !mp_iszero(&info->pk.rsa.key->e))) {
            /* Set the modulus and public exponent data. */
            keyTemplate[3].pValue     = info->pk.rsa.key->n.raw.buf;
            keyTemplate[3].ulValueLen = info->pk.rsa.key->n.raw.len;
            keyTemplate[4].pValue     = info->pk.rsa.key->e.raw.buf;
            keyTemplate[4].ulValueLen = info->pk.rsa.key->e.raw.len;

            /* Create an object containing public key data for device to use. */
            rv = session->func->C_CreateObject(session->handle, keyTemplate,
                                                        keyTmplCnt, &publicKey);
            if (rv != CKR_OK)
                ret = WC_HW_E;
        }
        else {
            ret = Pkcs11FindKeyById(&publicKey, CKO_PUBLIC_KEY, CKK_RSA,
                                    session, info->pk.rsa.key->id,
                                    info->pk.rsa.key->idLen);
        }
    }

    if (ret == 0) {
        /* Raw RSA encrypt/decrypt operation. */
        mech.mechanism      = CKM_RSA_X_509;
        mech.ulParameterLen = 0;
        mech.pParameter     = NULL;

        rv = session->func->C_EncryptInit(session->handle, &mech, publicKey);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }
    if (ret == 0) {
        outLen = (CK_ULONG)*info->pk.rsa.outLen;
        rv = session->func->C_Encrypt(session->handle,
                (CK_BYTE_PTR)info->pk.rsa.in, info->pk.rsa.inLen,
                info->pk.rsa.out, &outLen);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }
    if (ret == 0)
        *info->pk.rsa.outLen = (word32)outLen;

    if (sessionKey)
        session->func->C_DestroyObject(session->handle, publicKey);

    return ret;
}

/**
 * Exponentiate the input with the private part of the RSA key.
 * Used in private encrypt and decrypt.
 *
 * @param  session  [in]  Session object.
 * @param  info     [in]  Cryptographic operation data.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          0 on success.
 */
static int Pkcs11RsaPrivate(Pkcs11Session* session, wc_CryptoInfo* info)
{
    int              ret = 0;
    CK_RV            rv;
    CK_MECHANISM     mech;
    CK_ULONG         outLen;
    CK_OBJECT_HANDLE privateKey = NULL_PTR;
    int              sessionKey = 0;

    WOLFSSL_MSG("PKCS#11: RSA Private Key Operation");

    if (info->pk.rsa.outLen == NULL) {
        ret = BAD_FUNC_ARG;
    }

    if (ret == 0) {
        if ((sessionKey = !mp_iszero(&info->pk.rsa.key->d))) {
            ret = Pkcs11CreateRsaPrivateKey(&privateKey, session,
                                                              info->pk.rsa.key);
        }
        else if (info->pk.rsa.key->idLen > 0) {
            ret = Pkcs11FindKeyById(&privateKey, CKO_PRIVATE_KEY, CKK_RSA,
                                    session, info->pk.rsa.key->id,
                                    info->pk.rsa.key->idLen);
        }
        else {
            ret = Pkcs11FindRsaKey(&privateKey, CKO_PRIVATE_KEY, session,
                                                              info->pk.rsa.key);
        }
    }

    if (ret == 0) {
        /* Raw RSA encrypt/decrypt operation. */
        mech.mechanism      = CKM_RSA_X_509;
        mech.ulParameterLen = 0;
        mech.pParameter     = NULL;

        rv = session->func->C_DecryptInit(session->handle, &mech, privateKey);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }
    if (ret == 0) {
        outLen = (CK_ULONG)*info->pk.rsa.outLen;
        rv = session->func->C_Decrypt(session->handle,
                (CK_BYTE_PTR)info->pk.rsa.in, info->pk.rsa.inLen,
                info->pk.rsa.out, &outLen);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }
    if (ret == 0)
        *info->pk.rsa.outLen = (word32)outLen;

    if (sessionKey)
        session->func->C_DestroyObject(session->handle, privateKey);

    return ret;
}

/**
 * Perform an RSA operation.
 *
 * @param  session  [in]  Session object.
 * @param  info     [in]  Cryptographic operation data.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          0 on success.
 */
static int Pkcs11Rsa(Pkcs11Session* session, wc_CryptoInfo* info)
{
    int               ret = 0;
    CK_RV             rv;
    CK_MECHANISM_INFO mechInfo;

    /* Check operation is supported. */
    rv = session->func->C_GetMechanismInfo(session->slotId, CKM_RSA_X_509,
                                                                     &mechInfo);
    if (rv != CKR_OK)
        ret = NOT_COMPILED_IN;

    if (ret == 0) {
        if (info->pk.rsa.type == RSA_PUBLIC_ENCRYPT ||
                                      info->pk.rsa.type == RSA_PUBLIC_DECRYPT) {
            if ((mechInfo.flags & CKF_ENCRYPT) == 0)
                ret = NOT_COMPILED_IN;
            else
                ret = Pkcs11RsaPublic(session, info);
        }
        else if (info->pk.rsa.type == RSA_PRIVATE_ENCRYPT ||
                                     info->pk.rsa.type == RSA_PRIVATE_DECRYPT) {
            if ((mechInfo.flags & CKF_DECRYPT) == 0)
                ret = NOT_COMPILED_IN;
            else
                ret = Pkcs11RsaPrivate(session, info);
        }
        else
            ret = NOT_COMPILED_IN;
    }

    return ret;
}

#ifdef WOLFSSL_KEY_GEN
/**
 * Get the RSA public key data from the PKCS#11 object.
 *
 * @param  key      [in]  RSA key to put the data into.
 * @param  session  [in]  Session object.
 * @param  pubkey   [in]  Public key object.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          MEMORY_E when a memory allocation fails.
 *          0 on success.
 */
static int Pkcs11GetRsaPublicKey(RsaKey* key, Pkcs11Session* session,
                                 CK_OBJECT_HANDLE pubKey)
{
    int            ret = 0;
    unsigned char* mod = NULL;
    unsigned char* exp = NULL;
    int            modSz, expSz;
    CK_ATTRIBUTE   tmpl[] = {
        { CKA_MODULUS,         NULL_PTR, 0 },
        { CKA_PUBLIC_EXPONENT, NULL_PTR, 0 }
    };
    CK_ULONG       tmplCnt = sizeof(tmpl) / sizeof(*tmpl);
    CK_RV rv;

    rv = session->func->C_GetAttributeValue(session->handle, pubKey, tmpl,
                                                                       tmplCnt);
    if (rv != CKR_OK)
        ret = WC_HW_E;

    if (ret == 0) {
        modSz = (int)tmpl[0].ulValueLen;
        expSz = (int)tmpl[1].ulValueLen;
        mod = (unsigned char*)XMALLOC(modSz, key->heap,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
        if (mod == NULL)
            ret = MEMORY_E;
    }
    if (ret == 0) {
        exp = (unsigned char*)XMALLOC(expSz, key->heap,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
        if (exp == NULL)
            ret = MEMORY_E;
    }
    if (ret == 0) {
        tmpl[0].pValue = mod;
        tmpl[1].pValue = exp;

        rv = session->func->C_GetAttributeValue(session->handle, pubKey,
                                                                 tmpl, tmplCnt);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }
    if (ret == 0)
        ret = wc_RsaPublicKeyDecodeRaw(mod, modSz, exp, expSz, key);

    if (exp != NULL)
        XFREE(exp, key->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (mod != NULL)
        XFREE(mod, key->heap, DYNAMIC_TYPE_TMP_BUFFER);

    return ret;
}

/**
 * Perform an RSA key generation operation.
 * The private key data stays on the device.
 *
 * @param  session  [in]  Session object.
 * @param  info     [in]  Cryptographic operation data.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          0 on success.
 */
static int Pkcs11RsaKeyGen(Pkcs11Session* session, wc_CryptoInfo* info)
{
    int               ret = 0;
    RsaKey*           key = info->pk.rsakg.key;
    CK_RV             rv;
    CK_ULONG          bits = info->pk.rsakg.size;
    CK_OBJECT_HANDLE  pubKey = NULL_PTR, privKey = NULL_PTR;
    CK_MECHANISM      mech;
    static CK_BYTE    pub_exp[] = { 0x01, 0x00, 0x01, 0x00 };
    CK_ATTRIBUTE      pubKeyTmpl[] = {
        { CKA_MODULUS_BITS,    &bits,    sizeof(bits)    },
        { CKA_ENCRYPT,         &ckTrue,  sizeof(ckTrue)  },
        { CKA_VERIFY,          &ckTrue,  sizeof(ckTrue)  },
        { CKA_PUBLIC_EXPONENT, &pub_exp, sizeof(pub_exp) }
    };
    CK_ULONG          pubTmplCnt = sizeof(pubKeyTmpl)/sizeof(*pubKeyTmpl);
    CK_ATTRIBUTE      privKeyTmpl[] = {
        {CKA_DECRYPT,  &ckTrue, sizeof(ckTrue) },
        {CKA_SIGN,     &ckTrue, sizeof(ckTrue) },
        {CKA_ID,       NULL,    0              }
    };
    int               privTmplCnt = 2;
    int               i;

    ret = Pkcs11MechAvail(session, CKM_RSA_PKCS_KEY_PAIR_GEN);
    if (ret == 0) {
        WOLFSSL_MSG("PKCS#11: RSA Key Generation Operation");

        /* Most commonly used public exponent value (array initialized). */
        if (info->pk.rsakg.e != WC_RSA_EXPONENT) {
            for (i = 0; i < (int)sizeof(pub_exp); i++)
                pub_exp[i] = (info->pk.rsakg.e >> (8 * i)) & 0xff;
        }
        for (i = (int)sizeof(pub_exp) - 1; pub_exp[i] == 0; i--) {
        }
        pubKeyTmpl[3].ulValueLen = i + 1;

        if (key->idLen != 0) {
            privKeyTmpl[privTmplCnt].pValue     = key->id;
            privKeyTmpl[privTmplCnt].ulValueLen = key->idLen;
            privTmplCnt++;
        }

        mech.mechanism      = CKM_RSA_PKCS_KEY_PAIR_GEN;
        mech.ulParameterLen = 0;
        mech.pParameter     = NULL;

        rv = session->func->C_GenerateKeyPair(session->handle, &mech,
                                                       pubKeyTmpl, pubTmplCnt,
                                                       privKeyTmpl, privTmplCnt,
                                                       &pubKey, &privKey);
        if (rv != CKR_OK)
            ret = -1;
    }

    if (ret == 0)
        ret = Pkcs11GetRsaPublicKey(key, session, pubKey);

    if (pubKey != NULL_PTR)
        ret = (int)session->func->C_DestroyObject(session->handle, pubKey);
    if (ret != 0 && privKey != NULL_PTR)
        ret = (int)session->func->C_DestroyObject(session->handle, privKey);

    return ret;
}
#endif /* WOLFSSL_KEY_GEN */
#endif /* !NO_RSA */

#ifdef HAVE_ECC
/**
 * Find the PKCS#11 object containing the ECC public or private key data with
 * the modulus specified.
 *
 * @param  key       [out]  Henadle to key object.
 * @param  keyClass  [in]   Public or private key class.
 * @param  session   [in]   Session object.
 * @param  eccKey    [in]   ECC key with parameters.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          MEMORY_E when a memory allocation fails.
 *          0 on success.
 */
static int Pkcs11FindEccKey(CK_OBJECT_HANDLE* key, CK_OBJECT_CLASS keyClass,
                            Pkcs11Session* session, ecc_key* eccKey)
{
    int             ret = 0;
    int             i;
    unsigned char*  ecPoint = NULL;
    word32          len = 0;
    CK_RV           rv;
    CK_ULONG        count;
    CK_UTF8CHAR     params[MAX_EC_PARAM_LEN];
    CK_ATTRIBUTE    keyTemplate[] = {
        { CKA_CLASS,           &keyClass,  sizeof(keyClass)  },
        { CKA_KEY_TYPE,        &ecKeyType, sizeof(ecKeyType) },
        { CKA_EC_PARAMS,       params,     0                 },
        { CKA_EC_POINT,        NULL,       0                 },
    };
    CK_ULONG        attrCnt = 3;

    ret = Pkcs11EccSetParams(eccKey, keyTemplate, 2);
    if (ret == 0 && keyClass == CKO_PUBLIC_KEY) {
        /* ASN1 encoded: OCT + uncompressed point */
        len = 3 + 1 + 2 * eccKey->dp->size;
        ecPoint = (unsigned char*)XMALLOC(len, eccKey->heap, DYNAMIC_TYPE_ECC);
        if (ecPoint == NULL)
            ret = MEMORY_E;
    }
    if (ret == 0 && keyClass == CKO_PUBLIC_KEY) {
        len -= 3;
        i = 0;
        ecPoint[i++] = ASN_OCTET_STRING;
        if (len >= ASN_LONG_LENGTH)
            ecPoint[i++] = (ASN_LONG_LENGTH | 1);
        ecPoint[i++] = len;
        ret = wc_ecc_export_x963(eccKey, ecPoint + i, &len);
    }
    if (ret == 0 && keyClass == CKO_PUBLIC_KEY) {
        keyTemplate[3].pValue     = ecPoint;
        keyTemplate[3].ulValueLen = len + i;
        attrCnt++;
    }
    if (ret == 0) {
        rv = session->func->C_FindObjectsInit(session->handle, keyTemplate,
                                                                       attrCnt);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }
    if (ret == 0) {
        rv = session->func->C_FindObjects(session->handle, key, 1, &count);
        if (rv != CKR_OK)
            ret = WC_HW_E;
        rv = session->func->C_FindObjectsFinal(session->handle);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }

    if (ecPoint != NULL)
        XFREE(ecPoint, eccKey->heap, DYNAMIC_TYPE_ECC);

    return ret;
}

/**
 * Create a PKCS#11 object containing the ECC public key data.
 * Encode the public key as an OCTET_STRING of the encoded point.
 *
 * @param  publicKey    [out]  Henadle to public key object.
 * @param  session      [in]   Session object.
 * @param  public_key   [in]   ECC public key.
 * @param  operation    [in]   Cryptographic operation key is to be used for.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          MEMORY_E when a memory allocation fails.
 *          0 on success.
 */
static int Pkcs11CreateEccPublicKey(CK_OBJECT_HANDLE* publicKey,
                                    Pkcs11Session* session,
                                    ecc_key* public_key,
                                    CK_ATTRIBUTE_TYPE operation)
{
    int             ret = 0;
    int             i;
    unsigned char*  ecPoint = NULL;
    word32          len;
    CK_RV           rv;
    CK_UTF8CHAR     params[MAX_EC_PARAM_LEN];
    CK_ATTRIBUTE    keyTemplate[] = {
        { CKA_CLASS,     &pubKeyClass, sizeof(pubKeyClass) },
        { CKA_KEY_TYPE,  &ecKeyType,   sizeof(ecKeyType)   },
        { operation,     &ckTrue,      sizeof(ckTrue)      },
        { CKA_EC_PARAMS, params,       0                   },
        { CKA_EC_POINT,  NULL,         0                   }
    };
    CK_ULONG        keyTmplCnt = sizeof(keyTemplate) / sizeof(*keyTemplate);

    ret = Pkcs11EccSetParams(public_key, keyTemplate, 3);
    if (ret == 0) {
        /* ASN1 encoded: OCT + uncompressed point */
        len = 3 + 1 + 2 * public_key->dp->size;
        ecPoint = (unsigned char*)XMALLOC(len, public_key->heap,
                                                              DYNAMIC_TYPE_ECC);
        if (ecPoint == NULL)
            ret = MEMORY_E;
    }
    if (ret == 0) {
        len -= 3;
        i = 0;
        ecPoint[i++] = ASN_OCTET_STRING;
        if (len >= ASN_LONG_LENGTH)
            ecPoint[i++] = ASN_LONG_LENGTH | 1;
        ecPoint[i++] = len;
        ret = wc_ecc_export_x963(public_key, ecPoint + i, &len);
    }
    if (ret == 0) {
        keyTemplate[4].pValue     = ecPoint;
        keyTemplate[4].ulValueLen = len + i;

        rv = session->func->C_CreateObject(session->handle, keyTemplate,
                                                         keyTmplCnt, publicKey);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }

    if (ecPoint != NULL)
        XFREE(ecPoint, public_key->heap, DYNAMIC_TYPE_ECC);

    return ret;
}

#ifndef NO_PKCS11_EC_KEYGEN
/**
 * Gets the public key data from the PKCS#11 object and puts into the ECC key.
 *
 * @param  key      [in]  ECC public key.
 * @param  session  [in]  Session object.
 * @param  pubKey   [in]  ECC public key PKCS#11 object.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          MEMORY_E when a memory allocation fails.
 *          0 on success.
 */
static int Pkcs11GetEccPublicKey(ecc_key* key, Pkcs11Session* session,
                                 CK_OBJECT_HANDLE pubKey)
{
    int            ret = 0;
    word32         i = 0;
    int            curveIdx;
    unsigned char* point = NULL;
    int            pointSz;
    byte           tag;
    CK_RV          rv;
    CK_ATTRIBUTE   tmpl[] = {
        { CKA_EC_POINT,  NULL_PTR, 0 },
    };
    CK_ULONG       tmplCnt = sizeof(tmpl) / sizeof(*tmpl);

    rv = session->func->C_GetAttributeValue(session->handle, pubKey, tmpl,
                                                                       tmplCnt);
    if (rv != CKR_OK)
        ret = WC_HW_E;

    if (ret == 0) {
        pointSz = (int)tmpl[0].ulValueLen;
        point = (unsigned char*)XMALLOC(pointSz, key->heap, DYNAMIC_TYPE_ECC);
        if (point == NULL)
            ret = MEMORY_E;
    }
    if (ret == 0) {
        tmpl[0].pValue = point;

        rv = session->func->C_GetAttributeValue(session->handle, pubKey,
                                                                 tmpl, tmplCnt);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }

    /* Make sure the data is big enough for ASN.1: OCT + uncompressed point */
    if (ret == 0 && pointSz < key->dp->size * 2 + 1 + 2)
        ret = ASN_PARSE_E;
    /* Step over the OCTET_STRING wrapper. */
    if (ret == 0 && GetASNTag(point, &i, &tag, pointSz) != 0)
        ret = ASN_PARSE_E;
    if (ret == 0 && tag != ASN_OCTET_STRING)
        ret = ASN_PARSE_E;
    if (ret == 0 && point[i] >= ASN_LONG_LENGTH) {
        if (point[i++] != (ASN_LONG_LENGTH | 1))
            ret = ASN_PARSE_E;
        else if (pointSz < key->dp->size * 2 + 1 + 3)
            ret = ASN_PARSE_E;
    }
    if (ret == 0 && point[i++] != key->dp->size * 2 + 1)
        ret = ASN_PARSE_E;

    if (ret == 0) {
        curveIdx = wc_ecc_get_curve_idx(key->dp->id);
        ret = wc_ecc_import_point_der(point + i, pointSz - i, curveIdx,
                                                                  &key->pubkey);
    }

    if (point != NULL)
        XFREE(point, key->heap, DYNAMIC_TYPE_ECC);

    return ret;
}

/**
 * Perform an ECC key generation operation.
 * The private key data stays on the device.
 *
 * @param  session  [in]  Session object.
 * @param  info     [in]  Cryptographic operation data.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          0 on success.
 */
static int Pkcs11EcKeyGen(Pkcs11Session* session, wc_CryptoInfo* info)
{
    int               ret = 0;
    ecc_key*          key = info->pk.eckg.key;
    CK_RV             rv;
    CK_OBJECT_HANDLE  pubKey = NULL_PTR, privKey = NULL_PTR;
    CK_MECHANISM      mech;
    CK_UTF8CHAR       params[MAX_EC_PARAM_LEN];
    CK_ATTRIBUTE      pubKeyTmpl[] = {
        { CKA_EC_PARAMS,       params,   0               },
        { CKA_ENCRYPT,         &ckTrue,  sizeof(ckTrue)  },
        { CKA_VERIFY,          &ckTrue,  sizeof(ckTrue)  },
    };
    int               pubTmplCnt = sizeof(pubKeyTmpl)/sizeof(*pubKeyTmpl);
    CK_ATTRIBUTE      privKeyTmpl[] = {
        { CKA_DECRYPT,  &ckTrue, sizeof(ckTrue) },
        { CKA_SIGN,     &ckTrue, sizeof(ckTrue) },
        { CKA_DERIVE,   &ckTrue, sizeof(ckTrue) },
        { CKA_ID,       NULL,    0              },
    };
    int               privTmplCnt = 3;

    ret = Pkcs11MechAvail(session, CKM_EC_KEY_PAIR_GEN);
    if (ret == 0) {
        WOLFSSL_MSG("PKCS#11: EC Key Generation Operation");

        ret = Pkcs11EccSetParams(key, pubKeyTmpl, 0);
    }
    if (ret == 0) {
        if (key->idLen != 0) {
            privKeyTmpl[privTmplCnt].pValue     = key->id;
            privKeyTmpl[privTmplCnt].ulValueLen = key->idLen;
            privTmplCnt++;
        }

        mech.mechanism      = CKM_EC_KEY_PAIR_GEN;
        mech.ulParameterLen = 0;
        mech.pParameter     = NULL;

        rv = session->func->C_GenerateKeyPair(session->handle, &mech,
                                                       pubKeyTmpl, pubTmplCnt,
                                                       privKeyTmpl, privTmplCnt,
                                                       &pubKey, &privKey);
        if (rv != CKR_OK)
            ret = -1;
    }

    if (ret == 0)
        ret = Pkcs11GetEccPublicKey(key, session, pubKey);

    if (pubKey != NULL_PTR)
        session->func->C_DestroyObject(session->handle, pubKey);
    if (ret != 0 && privKey != NULL_PTR)
        session->func->C_DestroyObject(session->handle, privKey);

    return ret;
}
#endif

#ifndef NO_PKCS11_ECDH
/**
 * Extracts the secret key data from the PKCS#11 object.
 *
 * @param  session  [in]      Session object.
 * @param  secret   [in]      PKCS#11 object with the secret key data.
 * @param  out      [in]      Buffer to hold secret data.
 * @param  outLen   [in,out]  On in, length of buffer.
 *                            On out, the length of data in buffer.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          0 on success.
 */
static int Pkcs11ExtractSecret(Pkcs11Session* session, CK_OBJECT_HANDLE secret,
    byte* out, word32* outLen)
{
    int ret = 0;
    CK_ATTRIBUTE tmpl[] = {
      {CKA_VALUE, NULL_PTR, 0}
    };
    CK_ULONG     tmplCnt = sizeof(tmpl) / sizeof(*tmpl);
    CK_RV rv;

    rv = session->func->C_GetAttributeValue(session->handle, secret, tmpl,
                                                                       tmplCnt);
    if (rv != CKR_OK)
        ret = WC_HW_E;
    if (ret == 0) {
        if (tmpl[0].ulValueLen > *outLen)
            ret = BUFFER_E;
    }
    if (ret == 0) {
        tmpl[0].pValue = out;
        rv = session->func->C_GetAttributeValue(session->handle, secret,
                                                                 tmpl, tmplCnt);
        if (rv != CKR_OK)
            ret = WC_HW_E;
        *outLen = (word32)tmpl[0].ulValueLen;
    }

    return ret;
}

/**
 * Performs the ECDH secret generation operation.
 *
 * @param  session  [in]  Session object.
 * @param  info     [in]  Cryptographic operation data.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          0 on success.
 */
static int Pkcs11ECDH(Pkcs11Session* session, wc_CryptoInfo* info)
{
    int                    ret = 0;
    int                    sessionKey = 0;
    unsigned char*         point = NULL;
    word32                 pointLen;
    CK_RV                  rv;
    CK_KEY_TYPE            keyType = CKK_GENERIC_SECRET;
    CK_MECHANISM           mech;
    CK_ECDH1_DERIVE_PARAMS params;
    CK_OBJECT_HANDLE       privateKey = NULL_PTR;
    CK_OBJECT_HANDLE       secret = CK_INVALID_HANDLE;
    CK_ULONG               secSz;
    CK_ATTRIBUTE           tmpl[] = {
        { CKA_CLASS,       &secretKeyClass, sizeof(secretKeyClass) },
        { CKA_KEY_TYPE,    &keyType,        sizeof(keyType)        },
        { CKA_PRIVATE,     &ckFalse,        sizeof(ckFalse)        },
        { CKA_SENSITIVE,   &ckFalse,        sizeof(ckFalse)        },
        { CKA_EXTRACTABLE, &ckTrue,         sizeof(ckTrue)         },
        { CKA_VALUE_LEN,   &secSz,          sizeof(secSz)          }
    };
    CK_ULONG               tmplCnt = sizeof(tmpl) / sizeof(*tmpl);

    ret = Pkcs11MechAvail(session, CKM_ECDH1_DERIVE);
    if (ret == 0 && info->pk.ecdh.outlen == NULL) {
        ret = BAD_FUNC_ARG;
    }
    if (ret == 0) {
        WOLFSSL_MSG("PKCS#11: EC Key Derivation Operation");


        if ((sessionKey = !mp_iszero(&info->pk.ecdh.private_key->k)))
            ret = Pkcs11CreateEccPrivateKey(&privateKey, session,
                                         info->pk.ecdh.private_key, CKA_DERIVE);
        else if (info->pk.ecdh.private_key->idLen > 0) {
            ret = Pkcs11FindKeyById(&privateKey, CKO_PRIVATE_KEY, CKK_EC,
                                    session, info->pk.ecdh.private_key->id,
                                    info->pk.ecdh.private_key->idLen);
        }
        else {
            ret = Pkcs11FindEccKey(&privateKey, CKO_PRIVATE_KEY, session,
                                                      info->pk.ecdh.public_key);
        }
    }
    if (ret == 0) {
        ret = wc_ecc_export_x963(info->pk.ecdh.public_key, NULL, &pointLen);
        if (ret == LENGTH_ONLY_E) {
            point = (unsigned char*)XMALLOC(pointLen,
                                                 info->pk.ecdh.public_key->heap,
                                                       DYNAMIC_TYPE_ECC_BUFFER);
            ret = wc_ecc_export_x963(info->pk.ecdh.public_key, point,
                                                                     &pointLen);
        }
    }

    if (ret == 0) {
        secSz = *info->pk.ecdh.outlen;
        if (secSz > (CK_ULONG)info->pk.ecdh.private_key->dp->size)
            secSz = info->pk.ecdh.private_key->dp->size;

        params.kdf             = CKD_NULL;
        params.pSharedData     = NULL;
        params.ulSharedDataLen = 0;
        params.pPublicData     = point;
        params.ulPublicDataLen = pointLen;

        mech.mechanism      = CKM_ECDH1_DERIVE;
        mech.ulParameterLen = sizeof(params);
        mech.pParameter     = &params;

        rv = session->func->C_DeriveKey(session->handle, &mech, privateKey,
                                                        tmpl, tmplCnt, &secret);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }

    if (ret == 0) {
        ret = Pkcs11ExtractSecret(session, secret, info->pk.ecdh.out,
                                                          info->pk.ecdh.outlen);
    }

    if (sessionKey)
        session->func->C_DestroyObject(session->handle, privateKey);

    if (point != NULL)
        XFREE(point, info->pk.ecdh.public_key->heap, DYNAMIC_TYPE_ECC_BUFFER);

    return ret;
}
#endif

/**
 * Encode, in place, the ECDSA signature.
 * Two fixed width values into ASN.1 DER encoded SEQ { INT, INT }
 *
 * @param  sig  [in,out]  Signature data.
 * @param  sz   [in]      Size of original signature data.
 * @return  Length of the ASN.1 DER enencoded signature.
 */
static word32 Pkcs11ECDSASig_Encode(byte* sig, word32 sz)
{
    word32 rHigh, sHigh, seqLen;
    word32 rStart = 0, sStart = 0;
    word32 sigSz, rSz, rLen, sSz, sLen;
    word32 i;

    /* Find first byte of data in r and s. */
    while (rStart < sz - 1 && sig[rStart] == 0x00)
        rStart++;
    while (sStart < sz - 1 && sig[sz + sStart] == 0x00)
        sStart++;
    /* Check if 0 needs to be prepended to make integer a positive number. */
    rHigh = sig[rStart] >> 7;
    sHigh = sig[sz + sStart] >> 7;
    /* Calculate length of integer to put into ASN.1 encoding. */
    rLen = sz - rStart;
    sLen = sz - sStart;
    /* r and s: INT (2 bytes) + [ 0x00 ] + integer */
    rSz = 2 + rHigh + rLen;
    sSz = 2 + sHigh + sLen;
    /* Calculate the complete ASN.1 DER encoded size. */
    sigSz = rSz + sSz;
    if (sigSz >= ASN_LONG_LENGTH)
        seqLen = 3;
    else
        seqLen = 2;

    /* Move s and then r integers into their final places. */
    XMEMMOVE(sig + seqLen + rSz + (sSz - sLen), sig + sz + sStart, sLen);
    XMEMMOVE(sig + seqLen       + (rSz - rLen), sig      + rStart, rLen);

    /* Put the ASN.1 DER encoding around data. */
    i = 0;
    sig[i++] = ASN_CONSTRUCTED | ASN_SEQUENCE;
    if (seqLen == 3)
        sig[i++] = ASN_LONG_LENGTH | 0x01;
    sig[i++] = sigSz;
    sig[i++] = ASN_INTEGER;
    sig[i++] = rHigh + (sz - rStart);
    if (rHigh)
        sig[i++] = 0x00;
    i += sz - rStart;
    sig[i++] = ASN_INTEGER;
    sig[i++] = sHigh + (sz - sStart);
    if (sHigh)
        sig[i] = 0x00;

    return seqLen + sigSz;
}

/**
 * Decode the ECDSA signature.
 * ASN.1 DER encode SEQ { INT, INT } converted to two fixed with values.
 *
 * @param  in    [in]  ASN.1 DER encoded signature.
 * @param  inSz  [in]  Size of ASN.1 signature.
 * @param  sig   [in]  Output buffer.
 * @param  sz    [in]  Size of output buffer.
 * @return  ASN_PARSE_E when the ASN.1 encoding is invalid.
 *          0 on success.
 */
static int Pkcs11ECDSASig_Decode(const byte* in, word32 inSz, byte* sig,
                                 word32 sz)
{
    int ret = 0;
    word32 i = 0;
    byte   tag;
    int len, seqLen = 2;

    /* Make sure zeros in place when decoding short integers. */
    XMEMSET(sig, 0, sz * 2);

    /* Check min data for: SEQ + INT. */
    if (inSz < 5)
        ret = ASN_PARSE_E;
    /* Check SEQ */
    if (ret == 0 && in[i++] != (ASN_CONSTRUCTED | ASN_SEQUENCE))
        ret = ASN_PARSE_E;
    if (ret == 0 && in[i] >= ASN_LONG_LENGTH) {
        if (in[i] != (ASN_LONG_LENGTH | 0x01))
            ret = ASN_PARSE_E;
        else {
            i++;
            seqLen++;
        }
    }
    if (ret == 0 && in[i++] != inSz - seqLen)
        ret = ASN_PARSE_E;

    /* Check INT */
    if (ret == 0 && GetASNTag(in, &i, &tag, inSz) != 0)
        ret = ASN_PARSE_E;
    if (ret == 0 && tag != ASN_INTEGER)
        ret = ASN_PARSE_E;
    if (ret == 0 && (len = in[i++]) > sz + 1)
        ret = ASN_PARSE_E;
    /* Check there is space for INT data */
    if (ret == 0 && i + len > inSz)
        ret = ASN_PARSE_E;
    if (ret == 0) {
        /* Skip leading zero */
        if (in[i] == 0x00) {
            i++;
            len--;
        }
        /* Copy r into sig. */
        XMEMCPY(sig + sz - len, in + i, len);
        i += len;
    }

    /* Check min data for: INT. */
    if (ret == 0 && i + 2 > inSz)
        ret = ASN_PARSE_E;
    /* Check INT */
    if (ret == 0 && GetASNTag(in, &i, &tag, inSz) != 0)
        ret = ASN_PARSE_E;
    if (ret == 0 && tag != ASN_INTEGER)
        ret = ASN_PARSE_E;
    if (ret == 0 && (len = in[i++]) > sz + 1)
        ret = ASN_PARSE_E;
    /* Check there is space for INT data */
    if (ret == 0 && i + len > inSz)
        ret = ASN_PARSE_E;
    if (ret == 0) {
        /* Skip leading zero */
        if (in[i] == 0x00) {
            i++;
            len--;
        }
        /* Copy s into sig. */
        XMEMCPY(sig + sz + sz - len, in + i, len);
    }

    return ret;
}

/**
 * Get the parameters from the private key on the device.
 *
 * @param  session  [in]  Session object.
 * @param  privKey  [in]  PKCS #11 object handle of private key..
 * @param  key      [in]  Ecc key to set parameters against.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          0 on success.
 */
static int Pkcs11GetEccParams(Pkcs11Session* session, CK_OBJECT_HANDLE privKey,
                              ecc_key* key)
{
    int          ret = 0;
    int          curveId;
    CK_RV        rv;
    byte         oid[16];
    CK_ATTRIBUTE template[] = {
        { CKA_EC_PARAMS, (CK_VOID_PTR)oid, sizeof(oid) }
    };

    rv = session->func->C_GetAttributeValue(session->handle, privKey, template,
                                                                             1);
    if (rv != CKR_OK)
        ret = WC_HW_E;
    if (ret == 0) {
        /* PKCS #11 wraps the OID in ASN.1 */
        curveId = wc_ecc_get_curve_id_from_oid(oid + 2,
                                            (word32)template[0].ulValueLen - 2);
        if (curveId == ECC_CURVE_INVALID)
            ret = WC_HW_E;
    }
    if (ret == 0)
        ret = wc_ecc_set_curve(key, 0, curveId);

    return ret;
}

/**
 * Performs the ECDSA signing operation.
 *
 * @param  session  [in]  Session object.
 * @param  info     [in]  Cryptographic operation data.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          0 on success.
 */
static int Pkcs11ECDSA_Sign(Pkcs11Session* session, wc_CryptoInfo* info)
{
    int                    ret = 0;
    int                    sessionKey = 0;
    word32                 sz;
    CK_RV                  rv;
    CK_ULONG               outLen;
    CK_MECHANISM           mech;
    CK_MECHANISM_INFO      mechInfo;
    CK_OBJECT_HANDLE       privateKey = NULL_PTR;

    /* Check operation is supported. */
    rv = session->func->C_GetMechanismInfo(session->slotId, CKM_ECDSA,
                                                                     &mechInfo);
    if (rv != CKR_OK || (mechInfo.flags & CKF_SIGN) == 0)
        ret = NOT_COMPILED_IN;

    if (ret == 0 && info->pk.eccsign.outlen == NULL) {
        ret = BAD_FUNC_ARG;
    }
    if (ret == 0) {
        WOLFSSL_MSG("PKCS#11: EC Signing Operation");

        if ((sessionKey = !mp_iszero(&info->pk.eccsign.key->k)))
            ret = Pkcs11CreateEccPrivateKey(&privateKey, session,
                                                info->pk.eccsign.key, CKA_SIGN);
        else if (info->pk.eccsign.key->idLen > 0) {
            ret = Pkcs11FindKeyById(&privateKey, CKO_PRIVATE_KEY, CKK_EC,
                                    session, info->pk.eccsign.key->id,
                                    info->pk.eccsign.key->idLen);
            if (ret == 0 && info->pk.eccsign.key->dp == NULL) {
                ret = Pkcs11GetEccParams(session, privateKey,
                                                          info->pk.eccsign.key);
            }
        }
        else {
            ret = Pkcs11FindEccKey(&privateKey, CKO_PRIVATE_KEY, session,
                                                          info->pk.eccsign.key);
        }
    }

    if (ret == 0) {
        sz = info->pk.eccsign.key->dp->size;
        /* Maximum encoded size is two ordinates + 8 bytes of ASN.1. */
        if (*info->pk.eccsign.outlen < (word32)wc_ecc_sig_size_calc(sz))
            ret = BUFFER_E;
    }

    if (ret == 0) {
        mech.mechanism      = CKM_ECDSA;
        mech.ulParameterLen = 0;
        mech.pParameter     = NULL;

        rv = session->func->C_SignInit(session->handle, &mech, privateKey);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }

    if (ret == 0) {
        outLen = *info->pk.eccsign.outlen;
        rv = session->func->C_Sign(session->handle,
                                   (CK_BYTE_PTR)info->pk.eccsign.in,
                                   info->pk.eccsign.inlen, info->pk.eccsign.out,
                                   &outLen);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }

    if (ret == 0) {
        *info->pk.eccsign.outlen = Pkcs11ECDSASig_Encode(info->pk.eccsign.out,
                                                         sz);
    }

    if (sessionKey)
        session->func->C_DestroyObject(session->handle, privateKey);

    return ret;
}

/**
 * Performs the ECDSA verification operation.
 *
 * @param  session  [in]  Session object.
 * @param  info     [in]  Cryptographic operation data.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          MEMORY_E when a memory allocation fails.
 *          0 on success.
 */
static int Pkcs11ECDSA_Verify(Pkcs11Session* session, wc_CryptoInfo* info)
{
    int                    ret = 0;
    CK_RV                  rv;
    CK_MECHANISM           mech;
    CK_MECHANISM_INFO      mechInfo;
    CK_OBJECT_HANDLE       publicKey = NULL_PTR;
    unsigned char*         sig = NULL;
    word32                 sz = info->pk.eccverify.key->dp->size;

    /* Check operation is supported. */
    rv = session->func->C_GetMechanismInfo(session->slotId, CKM_ECDSA,
                                                                     &mechInfo);
    if (rv != CKR_OK || (mechInfo.flags & CKF_VERIFY) == 0)
        ret = NOT_COMPILED_IN;

    if (ret == 0 && info->pk.eccverify.res == NULL) {
        ret = BAD_FUNC_ARG;
    }

    if (ret == 0) {
        WOLFSSL_MSG("PKCS#11: EC Verification Operation");

        ret = Pkcs11CreateEccPublicKey(&publicKey, session,
                                            info->pk.eccverify.key, CKA_VERIFY);
    }

    if (ret == 0) {
        sig = XMALLOC(sz * 2, info->pk.eccverify.key->heap,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
        if (sig == NULL)
            ret = MEMORY_E;
    }

    if (ret == 0) {
        ret = Pkcs11ECDSASig_Decode(info->pk.eccverify.sig,
                                    info->pk.eccverify.siglen, sig, sz);
    }
    if (ret == 0) {
        mech.mechanism      = CKM_ECDSA;
        mech.ulParameterLen = 0;
        mech.pParameter     = NULL;

        rv = session->func->C_VerifyInit(session->handle, &mech, publicKey);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }

    if (ret == 0) {
        *info->pk.eccverify.res = 0;
        rv = session->func->C_Verify(session->handle,
                                     (CK_BYTE_PTR)info->pk.eccverify.hash,
                                     info->pk.eccverify.hashlen,
                                     (CK_BYTE_PTR)sig, sz * 2);
        if (rv == CKR_SIGNATURE_INVALID) {
        }
        else if (rv != CKR_OK)
            ret = WC_HW_E;
        else
            *info->pk.eccverify.res = 1;
    }

    if (publicKey != NULL_PTR)
        session->func->C_DestroyObject(session->handle, publicKey);

    if (sig != NULL)
        XFREE(sig, info->pk.eccverify.key->heap, DYNAMIC_TYPE_TMP_BUFFER);

    return ret;
}
#endif

#if !defined(NO_AES) && defined(HAVE_AESGCM)
/**
 * Performs the AES-GCM encryption operation.
 *
 * @param  session  [in]  Session object.
 * @param  info     [in]  Cryptographic operation data.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          MEMORY_E when a memory allocation fails.
 *          0 on success.
 */
static int Pkcs11AesGcmEncrypt(Pkcs11Session* session, wc_CryptoInfo* info)
{
    int                ret = 0;
    CK_RV              rv;
    Aes*               aes = info->cipher.aesgcm_enc.aes;
    CK_GCM_PARAMS      params;
    CK_MECHANISM_INFO  mechInfo;
    CK_OBJECT_HANDLE   key = NULL_PTR;
    CK_MECHANISM       mech;
    CK_ULONG           outLen;

    /* Check operation is supported. */
    rv = session->func->C_GetMechanismInfo(session->slotId, CKM_AES_GCM,
                                                                     &mechInfo);
    if (rv != CKR_OK || (mechInfo.flags & CKF_ENCRYPT) == 0)
        ret = NOT_COMPILED_IN;

    if (ret == 0) {
        WOLFSSL_MSG("PKCS#11: AES-GCM Encryption Operation");
    }

    /* Create a private key object or find by id. */
    if (ret == 0 && aes->idLen == 0) {
        ret = Pkcs11CreateSecretKey(&key, session, CKK_AES,
                                    (unsigned char*)aes->devKey, aes->keylen,
                                    NULL, 0);

    }
    else if (ret == 0) {
        ret = Pkcs11FindKeyById(&key, CKO_SECRET_KEY, CKK_AES, session, aes->id,
                                                                    aes->idLen);
    }

    if (ret == 0) {
        params.pIv       = (CK_BYTE_PTR)info->cipher.aesgcm_enc.iv;
        params.ulIvLen   = info->cipher.aesgcm_enc.ivSz;
        params.pAAD      = (CK_BYTE_PTR)info->cipher.aesgcm_enc.authIn;
        params.ulAADLen  = info->cipher.aesgcm_enc.authInSz;
        params.ulTagBits = info->cipher.aesgcm_enc.authTagSz * 8;

        mech.mechanism      = CKM_AES_GCM;
        mech.ulParameterLen = sizeof(params);
        mech.pParameter     = &params;

        rv = session->func->C_EncryptInit(session->handle, &mech, key);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }
    if (ret == 0) {
        outLen = info->cipher.aesgcm_enc.sz;
        rv = session->func->C_EncryptUpdate(session->handle,
                                        (CK_BYTE_PTR)info->cipher.aesgcm_enc.in,
                                        info->cipher.aesgcm_enc.sz,
                                        info->cipher.aesgcm_enc.out,
                                        &outLen);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }
    if (ret == 0) {
        /* Authentication tag comes out in final block. */
        outLen = info->cipher.aesgcm_enc.authTagSz;
        rv = session->func->C_EncryptFinal(session->handle,
                                           info->cipher.aesgcm_enc.authTag,
                                           &outLen);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }

    if (aes->idLen == 0 && key != NULL_PTR)
        session->func->C_DestroyObject(session->handle, key);

    return ret;
}

/**
 * Performs the AES-GCM decryption operation.
 *
 * @param  session  [in]  Session object.
 * @param  info     [in]  Cryptographic operation data.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          MEMORY_E when a memory allocation fails.
 *          0 on success.
 */
static int Pkcs11AesGcmDecrypt(Pkcs11Session* session, wc_CryptoInfo* info)
{
    int                ret = 0;
    CK_RV              rv;
    Aes*               aes = info->cipher.aesgcm_enc.aes;
    CK_GCM_PARAMS      params;
    CK_MECHANISM_INFO  mechInfo;
    CK_OBJECT_HANDLE   key = NULL_PTR;
    CK_MECHANISM       mech;
    CK_ULONG           outLen;
    word32             len;

    /* Check operation is supported. */
    rv = session->func->C_GetMechanismInfo(session->slotId, CKM_AES_GCM,
                                                                     &mechInfo);
    if (rv != CKR_OK || (mechInfo.flags & CKF_DECRYPT) == 0)
        ret = NOT_COMPILED_IN;

    if (ret == 0) {
        WOLFSSL_MSG("PKCS#11: AES-GCM Decryption Operation");
    }

    /* Create a private key object or find by id. */
    if (ret == 0 && aes->idLen == 0) {
        ret = Pkcs11CreateSecretKey(&key, session, CKK_AES,
                                    (unsigned char*)aes->devKey, aes->keylen,
                                    NULL, 0);
    }
    else if (ret == 0) {
        ret = Pkcs11FindKeyById(&key, CKO_SECRET_KEY, CKK_AES, session, aes->id,
                                                                    aes->idLen);
    }

    if (ret == 0) {
        params.pIv       = (CK_BYTE_PTR)info->cipher.aesgcm_dec.iv;
        params.ulIvLen   = info->cipher.aesgcm_dec.ivSz;
        params.pAAD      = (CK_BYTE_PTR)info->cipher.aesgcm_dec.authIn;
        params.ulAADLen  = info->cipher.aesgcm_dec.authInSz;
        params.ulTagBits = info->cipher.aesgcm_dec.authTagSz * 8;

        mech.mechanism      = CKM_AES_GCM;
        mech.ulParameterLen = sizeof(params);
        mech.pParameter     = &params;

        rv = session->func->C_DecryptInit(session->handle, &mech, key);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }
    if (ret == 0) {
        outLen = len = info->cipher.aesgcm_dec.sz;
        rv = session->func->C_DecryptUpdate(session->handle,
                                        (CK_BYTE_PTR)info->cipher.aesgcm_dec.in,
                                        info->cipher.aesgcm_dec.sz,
                                        info->cipher.aesgcm_dec.out,
                                        &outLen);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }
    if (ret == 0) {
        /* Put authentication tag in as encrypted data. */
        outLen = len = (len + info->cipher.aesgcm_dec.authTagSz -
                                                                (word32)outLen);
        rv = session->func->C_DecryptUpdate(session->handle,
                                   (CK_BYTE_PTR)info->cipher.aesgcm_dec.authTag,
                                   info->cipher.aesgcm_dec.authTagSz,
                                   info->cipher.aesgcm_dec.out,
                                   &outLen);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }
    if (ret == 0) {
        outLen = len = (len - (word32)outLen);
        /* Decrypted data comes out now. */
        rv = session->func->C_DecryptFinal(session->handle,
                                           info->cipher.aesgcm_dec.out,
                                           &outLen);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }

    if (aes->idLen == 0 && key != NULL_PTR)
        session->func->C_DestroyObject(session->handle, key);

    return ret;
}
#endif

#if !defined(NO_AES) && defined(HAVE_AES_CBC)
/**
 * Performs the AES-CBC encryption operation.
 *
 * @param  session  [in]  Session object.
 * @param  info     [in]  Cryptographic operation data.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          MEMORY_E when a memory allocation fails.
 *          0 on success.
 */
static int Pkcs11AesCbcEncrypt(Pkcs11Session* session, wc_CryptoInfo* info)
{
    int                ret = 0;
    CK_RV              rv;
    Aes*               aes = info->cipher.aescbc.aes;
    CK_MECHANISM_INFO  mechInfo;
    CK_OBJECT_HANDLE   key = NULL_PTR;
    CK_MECHANISM       mech;
    CK_ULONG           outLen;

    /* Check operation is supported. */
    rv = session->func->C_GetMechanismInfo(session->slotId, CKM_AES_CBC,
                                                                     &mechInfo);
    if (rv != CKR_OK || (mechInfo.flags & CKF_ENCRYPT) == 0)
        ret = NOT_COMPILED_IN;

    if (ret == 0) {
        WOLFSSL_MSG("PKCS#11: AES-CBC Encryption Operation");
    }

    /* Create a private key object or find by id. */
    if (ret == 0 && aes->idLen == 0) {
        ret = Pkcs11CreateSecretKey(&key, session, CKK_AES,
                                    (unsigned char*)aes->devKey, aes->keylen,
                                    NULL, 0);

    }
    else if (ret == 0) {
        ret = Pkcs11FindKeyById(&key, CKO_SECRET_KEY, CKK_AES, session, aes->id,
                                                                    aes->idLen);
    }

    if (ret == 0) {
        mech.mechanism      = CKM_AES_CBC;
        mech.ulParameterLen = AES_BLOCK_SIZE;
        mech.pParameter     = (CK_BYTE_PTR)info->cipher.aescbc.aes->reg;

        rv = session->func->C_EncryptInit(session->handle, &mech, key);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }
    if (ret == 0) {
        outLen = info->cipher.aescbc.sz;
        rv = session->func->C_Encrypt(session->handle,
                                      (CK_BYTE_PTR)info->cipher.aescbc.in,
                                      info->cipher.aescbc.sz,
                                      info->cipher.aescbc.out,
                                      &outLen);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }

    if (aes->idLen == 0 && key != NULL_PTR)
        session->func->C_DestroyObject(session->handle, key);

    return ret;
}

/**
 * Performs the AES-CBC decryption operation.
 *
 * @param  session  [in]  Session object.
 * @param  info     [in]  Cryptographic operation data.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          MEMORY_E when a memory allocation fails.
 *          0 on success.
 */
static int Pkcs11AesCbcDecrypt(Pkcs11Session* session, wc_CryptoInfo* info)
{
    int                ret = 0;
    CK_RV              rv;
    Aes*               aes = info->cipher.aescbc.aes;
    CK_MECHANISM_INFO  mechInfo;
    CK_OBJECT_HANDLE   key = NULL_PTR;
    CK_MECHANISM       mech;
    CK_ULONG           outLen;

    /* Check operation is supported. */
    rv = session->func->C_GetMechanismInfo(session->slotId, CKM_AES_CBC,
                                                                     &mechInfo);
    if (rv != CKR_OK || (mechInfo.flags & CKF_DECRYPT) == 0)
        ret = NOT_COMPILED_IN;

    if (ret == 0) {
        WOLFSSL_MSG("PKCS#11: AES-CBC Decryption Operation");
    }

    /* Create a private key object or find by id. */
    if (ret == 0 && aes->idLen == 0) {
        ret = Pkcs11CreateSecretKey(&key, session, CKK_AES,
                                    (unsigned char*)aes->devKey, aes->keylen,
                                    NULL, 0);
    }
    else if (ret == 0) {
        ret = Pkcs11FindKeyById(&key, CKO_SECRET_KEY, CKK_AES, session, aes->id,
                                                                    aes->idLen);
    }

    if (ret == 0) {
        mech.mechanism      = CKM_AES_CBC;
        mech.ulParameterLen = AES_BLOCK_SIZE;
        mech.pParameter     = (CK_BYTE_PTR)info->cipher.aescbc.aes->reg;

        rv = session->func->C_DecryptInit(session->handle, &mech, key);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }
    if (ret == 0) {
        outLen = info->cipher.aescbc.sz;
        rv = session->func->C_DecryptUpdate(session->handle,
                                        (CK_BYTE_PTR)info->cipher.aescbc.in,
                                        info->cipher.aescbc.sz,
                                        info->cipher.aescbc.out,
                                        &outLen);
        if (rv != CKR_OK)
            ret = WC_HW_E;
    }

    if (aes->idLen == 0 && key != NULL_PTR)
        session->func->C_DestroyObject(session->handle, key);

    return ret;
}
#endif

#ifndef NO_HMAC
/**
 * Updates or calculates the HMAC of the data.
 *
 * @param  session  [in]  Session object.
 * @param  info     [in]  Cryptographic operation data.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          0 on success.
 */
static int Pkcs11Hmac(Pkcs11Session* session, wc_CryptoInfo* info)
{
    int                ret = 0;
    CK_RV              rv;
    Hmac*              hmac = info->hmac.hmac;
    CK_MECHANISM_INFO  mechInfo;
    CK_OBJECT_HANDLE   key = NULL_PTR;
    CK_MECHANISM       mech;
    CK_ULONG           outLen;
    int                mechType;
    int                keyType;

    if (hmac->innerHashKeyed == WC_HMAC_INNER_HASH_KEYED_SW)
        ret = NOT_COMPILED_IN;

    if (ret == 0)
        ret = Pkcs11HmacTypes(info->hmac.macType, &mechType, &keyType);
    if (ret == 0) {
        /* Check operation is supported. */
        rv = session->func->C_GetMechanismInfo(session->slotId, mechType,
                                                                     &mechInfo);
        if (rv != CKR_OK || (mechInfo.flags & CKF_SIGN) == 0)
            ret = NOT_COMPILED_IN;
    }

    /* Check whether key been used to initialized. */
    if (ret == 0 && !hmac->innerHashKeyed) {
        WOLFSSL_MSG("PKCS#11: HMAC Init");

        /* Check device supports key length. */
        if (mechInfo.ulMaxKeySize > 0 &&
                                       (hmac->keyLen < mechInfo.ulMinKeySize ||
                                        hmac->keyLen > mechInfo.ulMaxKeySize)) {
            WOLFSSL_MSG("PKCS#11: Key Length not supported");
            ret = NOT_COMPILED_IN;
        }

        /* Create a private key object or find by id. */
        if (ret == 0 && hmac->idLen == 0) {
            ret = Pkcs11CreateSecretKey(&key, session, keyType,
                                    (unsigned char*)hmac->keyRaw, hmac->keyLen,
                                    NULL, 0);
            if (ret == WC_HW_E) {
                ret = Pkcs11CreateSecretKey(&key, session, CKK_GENERIC_SECRET,
                                    (unsigned char*)hmac->keyRaw, hmac->keyLen,
                                    NULL, 0);
            }

        }
        else if (ret == 0) {
            ret = Pkcs11FindKeyById(&key, CKO_SECRET_KEY, keyType, session,
                                                         hmac->id, hmac->idLen);
            if (ret == WC_HW_E) {
                ret = Pkcs11FindKeyById(&key, CKO_SECRET_KEY,
                                          CKK_GENERIC_SECRET, session, hmac->id,
                                          hmac->idLen);
            }
        }

        /* Initialize HMAC operation */
        if (ret == 0) {
            mech.mechanism      = mechType;
            mech.ulParameterLen = 0;
            mech.pParameter     = NULL;

            rv = session->func->C_SignInit(session->handle, &mech, key);
            if (rv != CKR_OK)
                ret = WC_HW_E;
        }

        /* Don't imitialize HMAC again if this succeeded */
        if (ret == 0)
            hmac->innerHashKeyed = WC_HMAC_INNER_HASH_KEYED_DEV;
    }
    /* Update the HMAC if input data passed in. */
    if (ret == 0 && info->hmac.inSz > 0) {
        WOLFSSL_MSG("PKCS#11: HMAC Update");

        rv = session->func->C_SignUpdate(session->handle,
                                         (CK_BYTE_PTR)info->hmac.in,
                                         info->hmac.inSz);
        /* Some algorithm implementations only support C_Sign. */
        if (rv == CKR_MECHANISM_INVALID) {
            WOLFSSL_MSG("PKCS#11: HMAC Update/Final not supported");
            ret = NOT_COMPILED_IN;
            /* Allow software implementation to set key. */
            hmac->innerHashKeyed = 0;
        }
        else if (rv != CKR_OK)
            ret = WC_HW_E;
    }
    /* Calculate the HMAC result if output buffer specified. */
    if (ret == 0 && info->hmac.digest != NULL) {
        WOLFSSL_MSG("PKCS#11: HMAC Final");

        outLen = WC_MAX_DIGEST_SIZE;
        rv = session->func->C_SignFinal(session->handle,
                                        (CK_BYTE_PTR)info->hmac.digest,
                                        &outLen);
        /* Some algorithm implementations only support C_Sign. */
        if (rv != CKR_OK)
            ret = WC_HW_E;
        else
            hmac->innerHashKeyed = 0;
    }

    if (hmac->idLen == 0 && key != NULL_PTR)
        session->func->C_DestroyObject(session->handle, key);

    return ret;
}
#endif

#ifndef WC_NO_RNG
#ifndef HAVE_HASHDRBG
/**
 * Performs random number generation.
 *
 * @param  session  [in]  Session object.
 * @param  info     [in]  Cryptographic operation data.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          0 on success.
 */
static int Pkcs11RandomBlock(Pkcs11Session* session, wc_CryptoInfo* info)
{
    int                ret = 0;
    CK_RV              rv;

    rv = session->func->C_GenerateRandom(session->handle, info->rng.out,
                                                                  info->rng.sz);
    if (rv != CKR_OK)
        ret = WC_HW_E;
    return ret;
}
#endif

/**
 * Generates entropy (seed) data.
 *
 * @param  session  [in]  Session object.
 * @param  info     [in]  Cryptographic operation data.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          0 on success.
 */
static int Pkcs11RandomSeed(Pkcs11Session* session, wc_CryptoInfo* info)
{
    int                ret = 0;
    CK_RV              rv;

    rv = session->func->C_GenerateRandom(session->handle, info->seed.seed,
                                                                 info->seed.sz);
    if (rv != CKR_OK)
        ret = WC_HW_E;
    return ret;
}
#endif

/**
 * Perform a cryptographic operation using PKCS#11 device.
 *
 * @param  devId  [in]  Device identifier.
 * @param  info   [in]  Cryptographic operation data.
 * @param  ctx    [in]  Context data for device - the token object.
 * @return  WC_HW_E when a PKCS#11 library call fails.
 *          0 on success.
 */
int wc_Pkcs11_CryptoDevCb(int devId, wc_CryptoInfo* info, void* ctx)
{
    int ret = 0;
    Pkcs11Token* token = (Pkcs11Token*)ctx;
    Pkcs11Session session;
    int readWrite = 0;

    if (devId <= INVALID_DEVID || info == NULL || ctx == NULL)
        ret = BAD_FUNC_ARG;

    if (ret == 0) {
        ret = Pkcs11OpenSession(token, &session, readWrite);
        if (ret == 0) {
            if (info->algo_type == WC_ALGO_TYPE_PK) {
#if !defined(NO_RSA) || defined(HAVE_ECC)
                switch (info->pk.type) {
    #ifndef NO_RSA
                    case WC_PK_TYPE_RSA:
                        ret = Pkcs11Rsa(&session, info);
                        break;
        #ifdef WOLFSSL_KEY_GEN
                    case WC_PK_TYPE_RSA_KEYGEN:
                        ret = Pkcs11RsaKeyGen(&session, info);
                        break;
        #endif
    #endif
    #ifdef HAVE_ECC
        #ifndef NO_PKCS11_EC_KEYGEN
                    case WC_PK_TYPE_EC_KEYGEN:
                        ret = Pkcs11EcKeyGen(&session, info);
                        break;
        #endif
        #ifndef NO_PKCS11_ECDH
                    case WC_PK_TYPE_ECDH:
                        ret = Pkcs11ECDH(&session, info);
                        break;
        #endif
                    case WC_PK_TYPE_ECDSA_SIGN:
                        ret = Pkcs11ECDSA_Sign(&session, info);
                        break;
                    case WC_PK_TYPE_ECDSA_VERIFY:
                        ret = Pkcs11ECDSA_Verify(&session, info);
                        break;
    #endif
                    default:
                        ret = NOT_COMPILED_IN;
                        break;
                }
#else
                ret = NOT_COMPILED_IN;
#endif /* !NO_RSA || HAVE_ECC */
            }
            else if (info->algo_type == WC_ALGO_TYPE_CIPHER) {
    #ifndef NO_AES
                switch (info->cipher.type) {
        #ifdef HAVE_AESGCM
                    case WC_CIPHER_AES_GCM:
                        if (info->cipher.enc)
                            ret = Pkcs11AesGcmEncrypt(&session, info);
                        else
                            ret = Pkcs11AesGcmDecrypt(&session, info);
                        break;
        #endif
        #ifdef HAVE_AES_CBC
                    case WC_CIPHER_AES_CBC:
                        if (info->cipher.enc)
                            ret = Pkcs11AesCbcEncrypt(&session, info);
                        else
                            ret = Pkcs11AesCbcDecrypt(&session, info);
                        break;
        #endif
                }
    #else
                ret = NOT_COMPILED_IN;
    #endif
            }
            else if (info->algo_type == WC_ALGO_TYPE_HMAC) {
    #ifndef NO_HMAC
                ret = Pkcs11Hmac(&session, info);
    #else
                ret = NOT_COMPILED_IN;
    #endif
            }
            else if (info->algo_type == WC_ALGO_TYPE_RNG) {
    #if !defined(WC_NO_RNG) && !defined(HAVE_HASHDRBG)
                ret = Pkcs11RandomBlock(&session, info);
    #else
                ret = NOT_COMPILED_IN;
    #endif
            }
            else if (info->algo_type == WC_ALGO_TYPE_SEED) {
    #ifndef WC_NO_RNG
                ret = Pkcs11RandomSeed(&session, info);
    #else
                ret = NOT_COMPILED_IN;
    #endif
            }
            else
                ret = NOT_COMPILED_IN;

            Pkcs11CloseSession(token, &session);
        }
    }

    return ret;
}

#endif /* HAVE_PKCS11 */

