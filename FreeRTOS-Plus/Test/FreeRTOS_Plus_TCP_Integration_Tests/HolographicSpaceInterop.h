

/* this ALWAYS GENERATED file contains the definitions for the interfaces */


 /* File created by MIDL compiler version 8.01.0622 */
/* at Mon Jan 18 19:14:07 2038
 */
/* Compiler settings for ..\..\..\..\..\..\..\..\Program Files (x86)\Windows Kits\10\Include\10.0.18362.0\um\HolographicSpaceInterop.idl:
    Oicf, W1, Zp8, env=Win32 (32b run), target_arch=X86 8.01.0622 
    protocol : dce , ms_ext, c_ext, robust
    error checks: allocation ref bounds_check enum stub_data 
    VC __declspec() decoration level: 
         __declspec(uuid()), __declspec(selectany), __declspec(novtable)
         DECLSPEC_UUID(), MIDL_INTERFACE()
*/
/* @@MIDL_FILE_HEADING(  ) */



/* verify that the <rpcndr.h> version is high enough to compile this file*/
#ifndef __REQUIRED_RPCNDR_H_VERSION__
#define __REQUIRED_RPCNDR_H_VERSION__ 500
#endif

#include "rpc.h"
#include "rpcndr.h"

#ifndef __RPCNDR_H_VERSION__
#error this stub requires an updated version of <rpcndr.h>
#endif /* __RPCNDR_H_VERSION__ */

#ifndef COM_NO_WINDOWS_H
#include "windows.h"
#include "ole2.h"
#endif /*COM_NO_WINDOWS_H*/

#ifndef __HolographicSpaceInterop_h__
#define __HolographicSpaceInterop_h__

#if defined(_MSC_VER) && (_MSC_VER >= 1020)
#pragma once
#endif

/* Forward Declarations */ 

#ifndef __IHolographicSpaceInterop_FWD_DEFINED__
#define __IHolographicSpaceInterop_FWD_DEFINED__
typedef interface IHolographicSpaceInterop IHolographicSpaceInterop;

#endif 	/* __IHolographicSpaceInterop_FWD_DEFINED__ */


/* header files for imported files */
#include "inspectable.h"

#ifdef __cplusplus
extern "C"{
#endif 


/* interface __MIDL_itf_HolographicSpaceInterop_0000_0000 */
/* [local] */ 

#include <winapifamily.h>
#if (NTDDI_VERSION >= NTDDI_WIN10_RS2)
#pragma region Desktop Family
#if WINAPI_FAMILY_PARTITION(WINAPI_PARTITION_DESKTOP)


extern RPC_IF_HANDLE __MIDL_itf_HolographicSpaceInterop_0000_0000_v0_0_c_ifspec;
extern RPC_IF_HANDLE __MIDL_itf_HolographicSpaceInterop_0000_0000_v0_0_s_ifspec;

#ifndef __IHolographicSpaceInterop_INTERFACE_DEFINED__
#define __IHolographicSpaceInterop_INTERFACE_DEFINED__

/* interface IHolographicSpaceInterop */
/* [object][uuid] */ 


EXTERN_C const IID IID_IHolographicSpaceInterop;

#if defined(__cplusplus) && !defined(CINTERFACE)
    
    MIDL_INTERFACE("5C4EE536-6A98-4B86-A170-587013D6FD4B")
    IHolographicSpaceInterop : public IInspectable
    {
    public:
        virtual HRESULT STDMETHODCALLTYPE CreateForWindow( 
            /* [in] */ HWND window,
            /* [in] */ REFIID riid,
            /* [iid_is][retval][out] */ void **holographicSpace) = 0;
        
    };
    
    
#else 	/* C style interface */

    typedef struct IHolographicSpaceInteropVtbl
    {
        BEGIN_INTERFACE
        
        HRESULT ( STDMETHODCALLTYPE *QueryInterface )( 
            IHolographicSpaceInterop * This,
            /* [in] */ REFIID riid,
            /* [annotation][iid_is][out] */ 
            _COM_Outptr_  void **ppvObject);
        
        ULONG ( STDMETHODCALLTYPE *AddRef )( 
            IHolographicSpaceInterop * This);
        
        ULONG ( STDMETHODCALLTYPE *Release )( 
            IHolographicSpaceInterop * This);
        
        HRESULT ( STDMETHODCALLTYPE *GetIids )( 
            IHolographicSpaceInterop * This,
            /* [out] */ ULONG *iidCount,
            /* [size_is][size_is][out] */ IID **iids);
        
        HRESULT ( STDMETHODCALLTYPE *GetRuntimeClassName )( 
            IHolographicSpaceInterop * This,
            /* [out] */ HSTRING *className);
        
        HRESULT ( STDMETHODCALLTYPE *GetTrustLevel )( 
            IHolographicSpaceInterop * This,
            /* [out] */ TrustLevel *trustLevel);
        
        HRESULT ( STDMETHODCALLTYPE *CreateForWindow )( 
            IHolographicSpaceInterop * This,
            /* [in] */ HWND window,
            /* [in] */ REFIID riid,
            /* [iid_is][retval][out] */ void **holographicSpace);
        
        END_INTERFACE
    } IHolographicSpaceInteropVtbl;

    interface IHolographicSpaceInterop
    {
        CONST_VTBL struct IHolographicSpaceInteropVtbl *lpVtbl;
    };

    

#ifdef COBJMACROS


#define IHolographicSpaceInterop_QueryInterface(This,riid,ppvObject)	\
    ( (This)->lpVtbl -> QueryInterface(This,riid,ppvObject) ) 

#define IHolographicSpaceInterop_AddRef(This)	\
    ( (This)->lpVtbl -> AddRef(This) ) 

#define IHolographicSpaceInterop_Release(This)	\
    ( (This)->lpVtbl -> Release(This) ) 


#define IHolographicSpaceInterop_GetIids(This,iidCount,iids)	\
    ( (This)->lpVtbl -> GetIids(This,iidCount,iids) ) 

#define IHolographicSpaceInterop_GetRuntimeClassName(This,className)	\
    ( (This)->lpVtbl -> GetRuntimeClassName(This,className) ) 

#define IHolographicSpaceInterop_GetTrustLevel(This,trustLevel)	\
    ( (This)->lpVtbl -> GetTrustLevel(This,trustLevel) ) 


#define IHolographicSpaceInterop_CreateForWindow(This,window,riid,holographicSpace)	\
    ( (This)->lpVtbl -> CreateForWindow(This,window,riid,holographicSpace) ) 

#endif /* COBJMACROS */


#endif 	/* C style interface */




#endif 	/* __IHolographicSpaceInterop_INTERFACE_DEFINED__ */


/* interface __MIDL_itf_HolographicSpaceInterop_0000_0001 */
/* [local] */ 

#endif /* WINAPI_FAMILY_PARTITION(WINAPI_PARTITION_DESKTOP) */
#pragma endregion
#endif //(NTDDI_VERSION >= NTDDI_WIN10)


extern RPC_IF_HANDLE __MIDL_itf_HolographicSpaceInterop_0000_0001_v0_0_c_ifspec;
extern RPC_IF_HANDLE __MIDL_itf_HolographicSpaceInterop_0000_0001_v0_0_s_ifspec;

/* Additional Prototypes for ALL interfaces */

unsigned long             __RPC_USER  HWND_UserSize(     unsigned long *, unsigned long            , HWND * ); 
unsigned char * __RPC_USER  HWND_UserMarshal(  unsigned long *, unsigned char *, HWND * ); 
unsigned char * __RPC_USER  HWND_UserUnmarshal(unsigned long *, unsigned char *, HWND * ); 
void                      __RPC_USER  HWND_UserFree(     unsigned long *, HWND * ); 

unsigned long             __RPC_USER  HWND_UserSize64(     unsigned long *, unsigned long            , HWND * ); 
unsigned char * __RPC_USER  HWND_UserMarshal64(  unsigned long *, unsigned char *, HWND * ); 
unsigned char * __RPC_USER  HWND_UserUnmarshal64(unsigned long *, unsigned char *, HWND * ); 
void                      __RPC_USER  HWND_UserFree64(     unsigned long *, HWND * ); 

/* end of Additional Prototypes */

#ifdef __cplusplus
}
#endif

#endif


