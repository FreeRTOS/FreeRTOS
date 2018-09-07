/* port.c
 *
 * Copyright (C) 2006-2015 wolfSSL Inc.
 *
 * This file is part of wolfSSL. (formerly known as CyaSSL)
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
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

#include <wolfssl/wolfcrypt/settings.h>
#include <wolfssl/wolfcrypt/types.h>
#include <wolfssl/wolfcrypt/error-crypt.h>


#ifdef _MSC_VER
    /* 4996 warning to use MS extensions e.g., strcpy_s instead of strncpy */
    #pragma warning(disable: 4996)
#endif



#ifdef SINGLE_THREADED

int InitMutex(wolfSSL_Mutex* m)
{
    (void)m;
    return 0;
}


int FreeMutex(wolfSSL_Mutex *m)
{
    (void)m;
    return 0;
}


int LockMutex(wolfSSL_Mutex *m)
{
    (void)m;
    return 0;
}


int UnLockMutex(wolfSSL_Mutex *m)
{
    (void)m;
    return 0;
}

#else /* MULTI_THREAD */

    #if defined(FREERTOS)

        int InitMutex(wolfSSL_Mutex* m)
        {
            int iReturn;

            *m = ( wolfSSL_Mutex ) xSemaphoreCreateMutex();
            if( *m != NULL )
                iReturn = 0;
            else
                iReturn = BAD_MUTEX_E;

            return iReturn;
        }

        int FreeMutex(wolfSSL_Mutex* m)
        {
            vSemaphoreDelete( *m );
            return 0;
        }

        int LockMutex(wolfSSL_Mutex* m)
        {
            /* Assume an infinite block, or should there be zero block? */
            xSemaphoreTake( *m, portMAX_DELAY );
            return 0;
        }

        int UnLockMutex(wolfSSL_Mutex* m)
        {
            xSemaphoreGive( *m );
            return 0;
        }

    #elif defined(WOLFSSL_SAFERTOS)

        int InitMutex(wolfSSL_Mutex* m)
        {
            vSemaphoreCreateBinary(m->mutexBuffer, m->mutex);
            if (m->mutex == NULL)
                return BAD_MUTEX_E;

            return 0;
        }

        int FreeMutex(wolfSSL_Mutex* m)
        {
            (void)m;
            return 0;
        }

        int LockMutex(wolfSSL_Mutex* m)
        {
            /* Assume an infinite block */
            xSemaphoreTake(m->mutex, portMAX_DELAY);
            return 0;
        }

        int UnLockMutex(wolfSSL_Mutex* m)
        {
            xSemaphoreGive(m->mutex);
            return 0;
        }


    #elif defined(USE_WINDOWS_API)

        int InitMutex(wolfSSL_Mutex* m)
        {
            InitializeCriticalSection(m);
            return 0;
        }


        int FreeMutex(wolfSSL_Mutex* m)
        {
            DeleteCriticalSection(m);
            return 0;
        }


        int LockMutex(wolfSSL_Mutex* m)
        {
            EnterCriticalSection(m);
            return 0;
        }


        int UnLockMutex(wolfSSL_Mutex* m)
        {
            LeaveCriticalSection(m);
            return 0;
        }

    #elif defined(WOLFSSL_PTHREADS)

        int InitMutex(wolfSSL_Mutex* m)
        {
            if (pthread_mutex_init(m, 0) == 0)
                return 0;
            else
                return BAD_MUTEX_E;
        }


        int FreeMutex(wolfSSL_Mutex* m)
        {
            if (pthread_mutex_destroy(m) == 0)
                return 0;
            else
                return BAD_MUTEX_E;
        }


        int LockMutex(wolfSSL_Mutex* m)
        {
            if (pthread_mutex_lock(m) == 0)
                return 0;
            else
                return BAD_MUTEX_E;
        }


        int UnLockMutex(wolfSSL_Mutex* m)
        {
            if (pthread_mutex_unlock(m) == 0)
                return 0;
            else
                return BAD_MUTEX_E;
        }

    #elif defined(THREADX)

        int InitMutex(wolfSSL_Mutex* m)
        {
            if (tx_mutex_create(m, "wolfSSL Mutex", TX_NO_INHERIT) == 0)
                return 0;
            else
                return BAD_MUTEX_E;
        }


        int FreeMutex(wolfSSL_Mutex* m)
        {
            if (tx_mutex_delete(m) == 0)
                return 0;
            else
                return BAD_MUTEX_E;
        }


        int LockMutex(wolfSSL_Mutex* m)
        {
            if (tx_mutex_get(m, TX_WAIT_FOREVER) == 0)
                return 0;
            else
                return BAD_MUTEX_E;
        }


        int UnLockMutex(wolfSSL_Mutex* m)
        {
            if (tx_mutex_put(m) == 0)
                return 0;
            else
                return BAD_MUTEX_E;
        }

    #elif defined(MICRIUM)

        int InitMutex(wolfSSL_Mutex* m)
        {
            #if (NET_SECURE_MGR_CFG_EN == DEF_ENABLED)
                if (NetSecure_OS_MutexCreate(m) == 0)
                    return 0;
                else
                    return BAD_MUTEX_E;
            #else
                return 0;
            #endif
        }


        int FreeMutex(wolfSSL_Mutex* m)
        {
            #if (NET_SECURE_MGR_CFG_EN == DEF_ENABLED)
                if (NetSecure_OS_FreeMutex(m) == 0)
                    return 0;
                else
                    return BAD_MUTEX_E;
            #else
                return 0;
            #endif
        }


        int LockMutex(wolfSSL_Mutex* m)
        {
            #if (NET_SECURE_MGR_CFG_EN == DEF_ENABLED)
                if (NetSecure_OS_LockMutex(m) == 0)
                    return 0;
                else
                    return BAD_MUTEX_E;
            #else
                return 0;
            #endif
        }


        int UnLockMutex(wolfSSL_Mutex* m)
        {
            #if (NET_SECURE_MGR_CFG_EN == DEF_ENABLED)
                if (NetSecure_OS_UnLockMutex(m) == 0)
                    return 0;
                else
                    return BAD_MUTEX_E;
            #else
                return 0;
            #endif

        }

    #elif defined(EBSNET)

        int InitMutex(wolfSSL_Mutex* m)
        {
            if (rtp_sig_mutex_alloc(m, "wolfSSL Mutex") == -1)
                return BAD_MUTEX_E;
            else
                return 0;
        }

        int FreeMutex(wolfSSL_Mutex* m)
        {
            rtp_sig_mutex_free(*m);
            return 0;
        }

        int LockMutex(wolfSSL_Mutex* m)
        {
            if (rtp_sig_mutex_claim_timed(*m, RTIP_INF) == 0)
                return 0;
            else
                return BAD_MUTEX_E;
        }

        int UnLockMutex(wolfSSL_Mutex* m)
        {
            rtp_sig_mutex_release(*m);
            return 0;
        }

    #elif defined(FREESCALE_MQX)

        int InitMutex(wolfSSL_Mutex* m)
        {
            if (_mutex_init(m, NULL) == MQX_EOK)
                return 0;
            else
                return BAD_MUTEX_E;
        }

        int FreeMutex(wolfSSL_Mutex* m)
        {
            if (_mutex_destroy(m) == MQX_EOK)
                return 0;
            else
                return BAD_MUTEX_E;
        }

        int LockMutex(wolfSSL_Mutex* m)
        {
            if (_mutex_lock(m) == MQX_EOK)
                return 0;
            else
                return BAD_MUTEX_E;
        }

        int UnLockMutex(wolfSSL_Mutex* m)
        {
            if (_mutex_unlock(m) == MQX_EOK)
                return 0;
            else
                return BAD_MUTEX_E;
        }

    #elif defined (WOLFSSL_TIRTOS)

        int InitMutex(wolfSSL_Mutex* m)
        {
           Semaphore_Params params;

           Semaphore_Params_init(&params);
           params.mode = Semaphore_Mode_BINARY;

           *m = Semaphore_create(1, &params, NULL);

           return 0;
        }

        int FreeMutex(wolfSSL_Mutex* m)
        {
            Semaphore_delete(m);

            return 0;
        }

        int LockMutex(wolfSSL_Mutex* m)
        {
            Semaphore_pend(*m, BIOS_WAIT_FOREVER);

            return 0;
        }

        int UnLockMutex(wolfSSL_Mutex* m)
        {
            Semaphore_post(*m);

            return 0;
        }

    #elif defined(WOLFSSL_uITRON4)
        #include "kernel.h"
        int InitMutex(wolfSSL_Mutex* m)
        {
            int iReturn;
            m->sem.sematr  = TA_TFIFO ;
            m->sem.isemcnt = 1 ;
            m->sem.maxsem  = 1 ;
            m->sem.name    = NULL ;

            m->id = acre_sem(&m->sem);
            if( m->id != NULL )
                iReturn = 0;
            else
                iReturn = BAD_MUTEX_E;

            return iReturn;
        }

        int FreeMutex(wolfSSL_Mutex* m)
        {
            del_sem( m->id );
            return 0;
        }

        int LockMutex(wolfSSL_Mutex* m)
        {
            wai_sem(m->id);
            return 0;
        }

        int UnLockMutex(wolfSSL_Mutex* m)
        {
            sig_sem(m->id);
            return 0;
        }

        /****  uITRON malloc/free ***/
        static ID ID_wolfssl_MPOOL = 0 ;
        static T_CMPL wolfssl_MPOOL = {TA_TFIFO, 0, NULL, "wolfSSL_MPOOL"};

        int uITRON4_minit(size_t poolsz) {
            ER ercd;
            wolfssl_MPOOL.mplsz = poolsz ;
            ercd = acre_mpl(&wolfssl_MPOOL);
            if (ercd > 0) {
                ID_wolfssl_MPOOL = ercd;
                return 0;
            } else {
                return -1;
            }
        }

        void *uITRON4_malloc(size_t sz) {
            ER ercd;
            void *p ;
            ercd = get_mpl(ID_wolfssl_MPOOL, sz, (VP)&p);
            if (ercd == E_OK) {
                return p;
            } else {
                return 0 ;
            }
        }

        void *uITRON4_realloc(void *p, size_t sz) {
          ER ercd;
          void *newp ;
          if(p) {
              ercd = get_mpl(ID_wolfssl_MPOOL, sz, (VP)&newp);
              if (ercd == E_OK) {
                  memcpy(newp, p, sz) ;
                  ercd = rel_mpl(ID_wolfssl_MPOOL, (VP)p);
                  if (ercd == E_OK) {
                      return newp;
                  }
              }
          }
          return 0 ;
        }

        void uITRON4_free(void *p) {
            ER ercd;
            ercd = rel_mpl(ID_wolfssl_MPOOL, (VP)p);
            if (ercd == E_OK) {
                return ;
            } else {
                return ;
            }
        }

#elif defined(WOLFSSL_uTKERNEL2)
        #include "tk/tkernel.h"
        int InitMutex(wolfSSL_Mutex* m)
        {
            int iReturn;
            m->sem.sematr  = TA_TFIFO ;
            m->sem.isemcnt = 1 ;
            m->sem.maxsem  = 1 ;

            m->id = tk_cre_sem(&m->sem);
            if( m->id != NULL )
                iReturn = 0;
            else
                iReturn = BAD_MUTEX_E;

            return iReturn;
        }

        int FreeMutex(wolfSSL_Mutex* m)
        {
            tk_del_sem( m->id );
            return 0;
        }

        int LockMutex(wolfSSL_Mutex* m)
        {
            tk_wai_sem(m->id, 1, TMO_FEVR);
            return 0;
        }

        int UnLockMutex(wolfSSL_Mutex* m)
        {
            tk_sig_sem(m->id, 1);
            return 0;
        }

        /****  uT-Kernel malloc/free ***/
        static ID ID_wolfssl_MPOOL = 0 ;
        static T_CMPL wolfssl_MPOOL =
                     {(void *)NULL,
        TA_TFIFO , 0,   "wolfSSL_MPOOL"};

        int uTKernel_init_mpool(unsigned int sz) {
            ER ercd;
            wolfssl_MPOOL.mplsz = sz ;
            ercd = tk_cre_mpl(&wolfssl_MPOOL);
            if (ercd > 0) {
                ID_wolfssl_MPOOL = ercd;
                return 0;
            } else {
                return -1;
            }
        }

        void *uTKernel_malloc(unsigned int sz) {
            ER ercd;
            void *p ;
            ercd = tk_get_mpl(ID_wolfssl_MPOOL, sz, (VP)&p, TMO_FEVR);
            if (ercd == E_OK) {
                return p;
            } else {
                return 0 ;
            }
        }

        void *uTKernel_realloc(void *p, unsigned int sz) {
          ER ercd;
          void *newp ;
          if(p) {
              ercd = tk_get_mpl(ID_wolfssl_MPOOL, sz, (VP)&newp, TMO_FEVR);
              if (ercd == E_OK) {
                  memcpy(newp, p, sz) ;
                  ercd = tk_rel_mpl(ID_wolfssl_MPOOL, (VP)p);
                  if (ercd == E_OK) {
                      return newp;
                  }
              }
          }
          return 0 ;
        }

        void uTKernel_free(void *p) {
            ER ercd;
            ercd = tk_rel_mpl(ID_wolfssl_MPOOL, (VP)p);
            if (ercd == E_OK) {
                return ;
            } else {
                return ;
            }
        }

    #elif defined(WOLFSSL_MDK_ARM)|| defined(WOLFSSL_CMSIS_RTOS)
    
        #if defined(WOLFSSL_CMSIS_RTOS)
            #include "cmsis_os.h"
            #define CMSIS_NMUTEX 10
            osMutexDef(wolfSSL_mt0) ;  osMutexDef(wolfSSL_mt1) ;  osMutexDef(wolfSSL_mt2) ;
            osMutexDef(wolfSSL_mt3) ;  osMutexDef(wolfSSL_mt4) ;  osMutexDef(wolfSSL_mt5) ;  
            osMutexDef(wolfSSL_mt6) ;  osMutexDef(wolfSSL_mt7) ;  osMutexDef(wolfSSL_mt8) ;  
            osMutexDef(wolfSSL_mt9) ;  
            
            static const osMutexDef_t *CMSIS_mutex[] = { osMutex(wolfSSL_mt0),   
                osMutex(wolfSSL_mt1),    osMutex(wolfSSL_mt2),   osMutex(wolfSSL_mt3),    
                osMutex(wolfSSL_mt4),    osMutex(wolfSSL_mt5),   osMutex(wolfSSL_mt6),
                osMutex(wolfSSL_mt7),    osMutex(wolfSSL_mt8),    osMutex(wolfSSL_mt9) } ;                 
            
            static osMutexId CMSIS_mutexID[CMSIS_NMUTEX] = {0} ;

            int InitMutex(wolfSSL_Mutex* m)
            {
                int i ;
                for (i=0; i<CMSIS_NMUTEX; i++) {
                    if(CMSIS_mutexID[i] == 0) {
                        CMSIS_mutexID[i] = osMutexCreate(CMSIS_mutex[i]) ;
                        (*m) = CMSIS_mutexID[i] ;
                    return 0 ;
                    }
                }
                return -1 ;
            }

            int FreeMutex(wolfSSL_Mutex* m)
            {
                int i ;
                osMutexDelete   (*m) ;
                for (i=0; i<CMSIS_NMUTEX; i++) {
                    if(CMSIS_mutexID[i] == (*m)) {
                        CMSIS_mutexID[i] = 0 ;
                        return(0) ;
                    }
                }
                return(-1) ;
            }
            
            int LockMutex(wolfSSL_Mutex* m)
            {
                osMutexWait(*m, osWaitForever) ;
                return(0) ;
            }

            int UnLockMutex(wolfSSL_Mutex* m)
            {
                osMutexRelease (*m);
                return 0;
            }
        #else
        int InitMutex(wolfSSL_Mutex* m)
        {
            os_mut_init (m); 
            return 0;
        }

        int FreeMutex(wolfSSL_Mutex* m)
        {
            return(0) ;
        }

        int LockMutex(wolfSSL_Mutex* m)
        {
            os_mut_wait (m, 0xffff);
            return(0) ;
        }

        int UnLockMutex(wolfSSL_Mutex* m)
        {
            os_mut_release (m);
            return 0;
        }
        #endif
    #endif /* USE_WINDOWS_API */

#endif /* SINGLE_THREADED */
        
#if defined(WOLFSSL_TI_CRYPT) ||  defined(WOLFSSL_TI_HASH)
    #include <wolfcrypt/src/port/ti/ti-ccm.c>  /* initialize and Mutex for TI Crypt Engine */
    #include <wolfcrypt/src/port/ti/ti-hash.c> /* md5, sha1, sha224, sha256 */
#endif
