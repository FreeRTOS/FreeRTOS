

/* this ALWAYS GENERATED file contains the definitions for the interfaces */


 /* File created by MIDL compiler version 8.01.0622 */
/* at Mon Jan 18 19:14:07 2038
 */
/* Compiler settings for ..\..\..\..\..\..\..\..\Program Files (x86)\Windows Kits\10\Include\10.0.18362.0\um\htiface.idl:
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

#ifndef __htiface_h__
#define __htiface_h__

#if defined(_MSC_VER) && (_MSC_VER >= 1020)
#pragma once
#endif

/* Forward Declarations */ 

#ifndef __ITargetFrame_FWD_DEFINED__
#define __ITargetFrame_FWD_DEFINED__
typedef interface ITargetFrame ITargetFrame;

#endif 	/* __ITargetFrame_FWD_DEFINED__ */


#ifndef __ITargetEmbedding_FWD_DEFINED__
#define __ITargetEmbedding_FWD_DEFINED__
typedef interface ITargetEmbedding ITargetEmbedding;

#endif 	/* __ITargetEmbedding_FWD_DEFINED__ */


#ifndef __ITargetFramePriv_FWD_DEFINED__
#define __ITargetFramePriv_FWD_DEFINED__
typedef interface ITargetFramePriv ITargetFramePriv;

#endif 	/* __ITargetFramePriv_FWD_DEFINED__ */


#ifndef __ITargetFramePriv2_FWD_DEFINED__
#define __ITargetFramePriv2_FWD_DEFINED__
typedef interface ITargetFramePriv2 ITargetFramePriv2;

#endif 	/* __ITargetFramePriv2_FWD_DEFINED__ */


/* header files for imported files */
#include "objidl.h"
#include "oleidl.h"
#include "urlmon.h"

#ifdef __cplusplus
extern "C"{
#endif 


/* interface __MIDL_itf_htiface_0000_0000 */
/* [local] */ 

//=--------------------------------------------------------------------------=
// HTIface.h
//=--------------------------------------------------------------------------=
// (C) Copyright Microsoft Corporation.  All Rights Reserved.
//
// THIS CODE AND INFORMATION IS PROVIDED "AS IS" WITHOUT WARRANTY OF
// ANY KIND, EITHER EXPRESSED OR IMPLIED, INCLUDING BUT NOT LIMITED TO
// THE IMPLIED WARRANTIES OF MERCHANTABILITY AND/OR FITNESS FOR A
// PARTICULAR PURPOSE.
//=--------------------------------------------------------------------------=

#include <winapifamily.h>
#pragma region Desktop Family
#if WINAPI_FAMILY_PARTITION(WINAPI_PARTITION_DESKTOP)
#pragma comment(lib,"uuid.lib")

//--------------------------------------------------------------------------
// OLE Hyperlinking ITargetFrame Interfaces.

#ifndef _LPTARGETFRAME2_DEFINED														
#include "htiframe.h"														
#endif // _LPTARGETFRAME2_DEFINED														


EXTERN_C const IID IID_ITargetFrame;
EXTERN_C const IID IID_ITargetEmbedding;
EXTERN_C const IID IID_ITargetFramePriv;
EXTERN_C const IID IID_ITargetFramePriv2;
#ifndef _LPTARGETFRAME_DEFINED
#define _LPTARGETFRAME_DEFINED


extern RPC_IF_HANDLE __MIDL_itf_htiface_0000_0000_v0_0_c_ifspec;
extern RPC_IF_HANDLE __MIDL_itf_htiface_0000_0000_v0_0_s_ifspec;

#ifndef __ITargetFrame_INTERFACE_DEFINED__
#define __ITargetFrame_INTERFACE_DEFINED__

/* interface ITargetFrame */
/* [unique][uuid][object] */ 

typedef /* [unique] */ ITargetFrame *LPTARGETFRAME;

typedef /* [public] */ 
enum __MIDL_ITargetFrame_0001
    {
        NAVIGATEFRAME_FL_RECORD	= 0x1,
        NAVIGATEFRAME_FL_POST	= 0x2,
        NAVIGATEFRAME_FL_NO_DOC_CACHE	= 0x4,
        NAVIGATEFRAME_FL_NO_IMAGE_CACHE	= 0x8,
        NAVIGATEFRAME_FL_AUTH_FAIL_CACHE_OK	= 0x10,
        NAVIGATEFRAME_FL_SENDING_FROM_FORM	= 0x20,
        NAVIGATEFRAME_FL_REALLY_SENDING_FROM_FORM	= 0x40
    } 	NAVIGATEFRAME_FLAGS;

typedef struct tagNavigateData
    {
    ULONG ulTarget;
    ULONG ulURL;
    ULONG ulRefURL;
    ULONG ulPostData;
    DWORD dwFlags;
    } 	NAVIGATEDATA;


EXTERN_C const IID IID_ITargetFrame;

#if defined(__cplusplus) && !defined(CINTERFACE)
    
    MIDL_INTERFACE("d5f78c80-5252-11cf-90fa-00AA0042106e")
    ITargetFrame : public IUnknown
    {
    public:
        virtual HRESULT STDMETHODCALLTYPE SetFrameName( 
            /* [in] */ LPCWSTR pszFrameName) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE GetFrameName( 
            /* [out] */ LPWSTR *ppszFrameName) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE GetParentFrame( 
            /* [out] */ IUnknown **ppunkParent) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE FindFrame( 
            /* [in] */ LPCWSTR pszTargetName,
            /* [in] */ IUnknown *ppunkContextFrame,
            /* [in] */ DWORD dwFlags,
            /* [out] */ IUnknown **ppunkTargetFrame) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE SetFrameSrc( 
            /* [in] */ LPCWSTR pszFrameSrc) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE GetFrameSrc( 
            /* [out] */ LPWSTR *ppszFrameSrc) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE GetFramesContainer( 
            /* [out] */ IOleContainer **ppContainer) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE SetFrameOptions( 
            /* [in] */ DWORD dwFlags) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE GetFrameOptions( 
            /* [out] */ DWORD *pdwFlags) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE SetFrameMargins( 
            /* [in] */ DWORD dwWidth,
            /* [in] */ DWORD dwHeight) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE GetFrameMargins( 
            /* [out] */ DWORD *pdwWidth,
            /* [out] */ DWORD *pdwHeight) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE RemoteNavigate( 
            /* [in] */ ULONG cLength,
            /* [size_is][in] */ ULONG *pulData) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE OnChildFrameActivate( 
            /* [in] */ IUnknown *pUnkChildFrame) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE OnChildFrameDeactivate( 
            /* [in] */ IUnknown *pUnkChildFrame) = 0;
        
    };
    
    
#else 	/* C style interface */

    typedef struct ITargetFrameVtbl
    {
        BEGIN_INTERFACE
        
        HRESULT ( STDMETHODCALLTYPE *QueryInterface )( 
            ITargetFrame * This,
            /* [in] */ REFIID riid,
            /* [annotation][iid_is][out] */ 
            _COM_Outptr_  void **ppvObject);
        
        ULONG ( STDMETHODCALLTYPE *AddRef )( 
            ITargetFrame * This);
        
        ULONG ( STDMETHODCALLTYPE *Release )( 
            ITargetFrame * This);
        
        HRESULT ( STDMETHODCALLTYPE *SetFrameName )( 
            ITargetFrame * This,
            /* [in] */ LPCWSTR pszFrameName);
        
        HRESULT ( STDMETHODCALLTYPE *GetFrameName )( 
            ITargetFrame * This,
            /* [out] */ LPWSTR *ppszFrameName);
        
        HRESULT ( STDMETHODCALLTYPE *GetParentFrame )( 
            ITargetFrame * This,
            /* [out] */ IUnknown **ppunkParent);
        
        HRESULT ( STDMETHODCALLTYPE *FindFrame )( 
            ITargetFrame * This,
            /* [in] */ LPCWSTR pszTargetName,
            /* [in] */ IUnknown *ppunkContextFrame,
            /* [in] */ DWORD dwFlags,
            /* [out] */ IUnknown **ppunkTargetFrame);
        
        HRESULT ( STDMETHODCALLTYPE *SetFrameSrc )( 
            ITargetFrame * This,
            /* [in] */ LPCWSTR pszFrameSrc);
        
        HRESULT ( STDMETHODCALLTYPE *GetFrameSrc )( 
            ITargetFrame * This,
            /* [out] */ LPWSTR *ppszFrameSrc);
        
        HRESULT ( STDMETHODCALLTYPE *GetFramesContainer )( 
            ITargetFrame * This,
            /* [out] */ IOleContainer **ppContainer);
        
        HRESULT ( STDMETHODCALLTYPE *SetFrameOptions )( 
            ITargetFrame * This,
            /* [in] */ DWORD dwFlags);
        
        HRESULT ( STDMETHODCALLTYPE *GetFrameOptions )( 
            ITargetFrame * This,
            /* [out] */ DWORD *pdwFlags);
        
        HRESULT ( STDMETHODCALLTYPE *SetFrameMargins )( 
            ITargetFrame * This,
            /* [in] */ DWORD dwWidth,
            /* [in] */ DWORD dwHeight);
        
        HRESULT ( STDMETHODCALLTYPE *GetFrameMargins )( 
            ITargetFrame * This,
            /* [out] */ DWORD *pdwWidth,
            /* [out] */ DWORD *pdwHeight);
        
        HRESULT ( STDMETHODCALLTYPE *RemoteNavigate )( 
            ITargetFrame * This,
            /* [in] */ ULONG cLength,
            /* [size_is][in] */ ULONG *pulData);
        
        HRESULT ( STDMETHODCALLTYPE *OnChildFrameActivate )( 
            ITargetFrame * This,
            /* [in] */ IUnknown *pUnkChildFrame);
        
        HRESULT ( STDMETHODCALLTYPE *OnChildFrameDeactivate )( 
            ITargetFrame * This,
            /* [in] */ IUnknown *pUnkChildFrame);
        
        END_INTERFACE
    } ITargetFrameVtbl;

    interface ITargetFrame
    {
        CONST_VTBL struct ITargetFrameVtbl *lpVtbl;
    };

    

#ifdef COBJMACROS


#define ITargetFrame_QueryInterface(This,riid,ppvObject)	\
    ( (This)->lpVtbl -> QueryInterface(This,riid,ppvObject) ) 

#define ITargetFrame_AddRef(This)	\
    ( (This)->lpVtbl -> AddRef(This) ) 

#define ITargetFrame_Release(This)	\
    ( (This)->lpVtbl -> Release(This) ) 


#define ITargetFrame_SetFrameName(This,pszFrameName)	\
    ( (This)->lpVtbl -> SetFrameName(This,pszFrameName) ) 

#define ITargetFrame_GetFrameName(This,ppszFrameName)	\
    ( (This)->lpVtbl -> GetFrameName(This,ppszFrameName) ) 

#define ITargetFrame_GetParentFrame(This,ppunkParent)	\
    ( (This)->lpVtbl -> GetParentFrame(This,ppunkParent) ) 

#define ITargetFrame_FindFrame(This,pszTargetName,ppunkContextFrame,dwFlags,ppunkTargetFrame)	\
    ( (This)->lpVtbl -> FindFrame(This,pszTargetName,ppunkContextFrame,dwFlags,ppunkTargetFrame) ) 

#define ITargetFrame_SetFrameSrc(This,pszFrameSrc)	\
    ( (This)->lpVtbl -> SetFrameSrc(This,pszFrameSrc) ) 

#define ITargetFrame_GetFrameSrc(This,ppszFrameSrc)	\
    ( (This)->lpVtbl -> GetFrameSrc(This,ppszFrameSrc) ) 

#define ITargetFrame_GetFramesContainer(This,ppContainer)	\
    ( (This)->lpVtbl -> GetFramesContainer(This,ppContainer) ) 

#define ITargetFrame_SetFrameOptions(This,dwFlags)	\
    ( (This)->lpVtbl -> SetFrameOptions(This,dwFlags) ) 

#define ITargetFrame_GetFrameOptions(This,pdwFlags)	\
    ( (This)->lpVtbl -> GetFrameOptions(This,pdwFlags) ) 

#define ITargetFrame_SetFrameMargins(This,dwWidth,dwHeight)	\
    ( (This)->lpVtbl -> SetFrameMargins(This,dwWidth,dwHeight) ) 

#define ITargetFrame_GetFrameMargins(This,pdwWidth,pdwHeight)	\
    ( (This)->lpVtbl -> GetFrameMargins(This,pdwWidth,pdwHeight) ) 

#define ITargetFrame_RemoteNavigate(This,cLength,pulData)	\
    ( (This)->lpVtbl -> RemoteNavigate(This,cLength,pulData) ) 

#define ITargetFrame_OnChildFrameActivate(This,pUnkChildFrame)	\
    ( (This)->lpVtbl -> OnChildFrameActivate(This,pUnkChildFrame) ) 

#define ITargetFrame_OnChildFrameDeactivate(This,pUnkChildFrame)	\
    ( (This)->lpVtbl -> OnChildFrameDeactivate(This,pUnkChildFrame) ) 

#endif /* COBJMACROS */


#endif 	/* C style interface */




#endif 	/* __ITargetFrame_INTERFACE_DEFINED__ */


#ifndef __ITargetEmbedding_INTERFACE_DEFINED__
#define __ITargetEmbedding_INTERFACE_DEFINED__

/* interface ITargetEmbedding */
/* [unique][uuid][object] */ 

typedef /* [unique] */ ITargetEmbedding *LPTARGETEMBEDDING;


EXTERN_C const IID IID_ITargetEmbedding;

#if defined(__cplusplus) && !defined(CINTERFACE)
    
    MIDL_INTERFACE("548793C0-9E74-11cf-9655-00A0C9034923")
    ITargetEmbedding : public IUnknown
    {
    public:
        virtual HRESULT STDMETHODCALLTYPE GetTargetFrame( 
            /* [out] */ ITargetFrame **ppTargetFrame) = 0;
        
    };
    
    
#else 	/* C style interface */

    typedef struct ITargetEmbeddingVtbl
    {
        BEGIN_INTERFACE
        
        HRESULT ( STDMETHODCALLTYPE *QueryInterface )( 
            ITargetEmbedding * This,
            /* [in] */ REFIID riid,
            /* [annotation][iid_is][out] */ 
            _COM_Outptr_  void **ppvObject);
        
        ULONG ( STDMETHODCALLTYPE *AddRef )( 
            ITargetEmbedding * This);
        
        ULONG ( STDMETHODCALLTYPE *Release )( 
            ITargetEmbedding * This);
        
        HRESULT ( STDMETHODCALLTYPE *GetTargetFrame )( 
            ITargetEmbedding * This,
            /* [out] */ ITargetFrame **ppTargetFrame);
        
        END_INTERFACE
    } ITargetEmbeddingVtbl;

    interface ITargetEmbedding
    {
        CONST_VTBL struct ITargetEmbeddingVtbl *lpVtbl;
    };

    

#ifdef COBJMACROS


#define ITargetEmbedding_QueryInterface(This,riid,ppvObject)	\
    ( (This)->lpVtbl -> QueryInterface(This,riid,ppvObject) ) 

#define ITargetEmbedding_AddRef(This)	\
    ( (This)->lpVtbl -> AddRef(This) ) 

#define ITargetEmbedding_Release(This)	\
    ( (This)->lpVtbl -> Release(This) ) 


#define ITargetEmbedding_GetTargetFrame(This,ppTargetFrame)	\
    ( (This)->lpVtbl -> GetTargetFrame(This,ppTargetFrame) ) 

#endif /* COBJMACROS */


#endif 	/* C style interface */




#endif 	/* __ITargetEmbedding_INTERFACE_DEFINED__ */


#ifndef __ITargetFramePriv_INTERFACE_DEFINED__
#define __ITargetFramePriv_INTERFACE_DEFINED__

/* interface ITargetFramePriv */
/* [unique][uuid][object] */ 

typedef /* [unique] */ ITargetFramePriv *LPTARGETFRAMEPRIV;


EXTERN_C const IID IID_ITargetFramePriv;

#if defined(__cplusplus) && !defined(CINTERFACE)
    
    MIDL_INTERFACE("9216E421-2BF5-11d0-82B4-00A0C90C29C5")
    ITargetFramePriv : public IUnknown
    {
    public:
        virtual HRESULT STDMETHODCALLTYPE FindFrameDownwards( 
            /* [in] */ LPCWSTR pszTargetName,
            /* [in] */ DWORD dwFlags,
            /* [out] */ IUnknown **ppunkTargetFrame) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE FindFrameInContext( 
            /* [in] */ LPCWSTR pszTargetName,
            /* [in] */ IUnknown *punkContextFrame,
            /* [in] */ DWORD dwFlags,
            /* [out] */ IUnknown **ppunkTargetFrame) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE OnChildFrameActivate( 
            /* [in] */ IUnknown *pUnkChildFrame) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE OnChildFrameDeactivate( 
            /* [in] */ IUnknown *pUnkChildFrame) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE NavigateHack( 
            /* [in] */ DWORD grfHLNF,
            /* [unique][in] */ LPBC pbc,
            /* [unique][in] */ IBindStatusCallback *pibsc,
            /* [unique][in] */ LPCWSTR pszTargetName,
            /* [in] */ LPCWSTR pszUrl,
            /* [unique][in] */ LPCWSTR pszLocation) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE FindBrowserByIndex( 
            /* [in] */ DWORD dwID,
            /* [out] */ IUnknown **ppunkBrowser) = 0;
        
    };
    
    
#else 	/* C style interface */

    typedef struct ITargetFramePrivVtbl
    {
        BEGIN_INTERFACE
        
        HRESULT ( STDMETHODCALLTYPE *QueryInterface )( 
            ITargetFramePriv * This,
            /* [in] */ REFIID riid,
            /* [annotation][iid_is][out] */ 
            _COM_Outptr_  void **ppvObject);
        
        ULONG ( STDMETHODCALLTYPE *AddRef )( 
            ITargetFramePriv * This);
        
        ULONG ( STDMETHODCALLTYPE *Release )( 
            ITargetFramePriv * This);
        
        HRESULT ( STDMETHODCALLTYPE *FindFrameDownwards )( 
            ITargetFramePriv * This,
            /* [in] */ LPCWSTR pszTargetName,
            /* [in] */ DWORD dwFlags,
            /* [out] */ IUnknown **ppunkTargetFrame);
        
        HRESULT ( STDMETHODCALLTYPE *FindFrameInContext )( 
            ITargetFramePriv * This,
            /* [in] */ LPCWSTR pszTargetName,
            /* [in] */ IUnknown *punkContextFrame,
            /* [in] */ DWORD dwFlags,
            /* [out] */ IUnknown **ppunkTargetFrame);
        
        HRESULT ( STDMETHODCALLTYPE *OnChildFrameActivate )( 
            ITargetFramePriv * This,
            /* [in] */ IUnknown *pUnkChildFrame);
        
        HRESULT ( STDMETHODCALLTYPE *OnChildFrameDeactivate )( 
            ITargetFramePriv * This,
            /* [in] */ IUnknown *pUnkChildFrame);
        
        HRESULT ( STDMETHODCALLTYPE *NavigateHack )( 
            ITargetFramePriv * This,
            /* [in] */ DWORD grfHLNF,
            /* [unique][in] */ LPBC pbc,
            /* [unique][in] */ IBindStatusCallback *pibsc,
            /* [unique][in] */ LPCWSTR pszTargetName,
            /* [in] */ LPCWSTR pszUrl,
            /* [unique][in] */ LPCWSTR pszLocation);
        
        HRESULT ( STDMETHODCALLTYPE *FindBrowserByIndex )( 
            ITargetFramePriv * This,
            /* [in] */ DWORD dwID,
            /* [out] */ IUnknown **ppunkBrowser);
        
        END_INTERFACE
    } ITargetFramePrivVtbl;

    interface ITargetFramePriv
    {
        CONST_VTBL struct ITargetFramePrivVtbl *lpVtbl;
    };

    

#ifdef COBJMACROS


#define ITargetFramePriv_QueryInterface(This,riid,ppvObject)	\
    ( (This)->lpVtbl -> QueryInterface(This,riid,ppvObject) ) 

#define ITargetFramePriv_AddRef(This)	\
    ( (This)->lpVtbl -> AddRef(This) ) 

#define ITargetFramePriv_Release(This)	\
    ( (This)->lpVtbl -> Release(This) ) 


#define ITargetFramePriv_FindFrameDownwards(This,pszTargetName,dwFlags,ppunkTargetFrame)	\
    ( (This)->lpVtbl -> FindFrameDownwards(This,pszTargetName,dwFlags,ppunkTargetFrame) ) 

#define ITargetFramePriv_FindFrameInContext(This,pszTargetName,punkContextFrame,dwFlags,ppunkTargetFrame)	\
    ( (This)->lpVtbl -> FindFrameInContext(This,pszTargetName,punkContextFrame,dwFlags,ppunkTargetFrame) ) 

#define ITargetFramePriv_OnChildFrameActivate(This,pUnkChildFrame)	\
    ( (This)->lpVtbl -> OnChildFrameActivate(This,pUnkChildFrame) ) 

#define ITargetFramePriv_OnChildFrameDeactivate(This,pUnkChildFrame)	\
    ( (This)->lpVtbl -> OnChildFrameDeactivate(This,pUnkChildFrame) ) 

#define ITargetFramePriv_NavigateHack(This,grfHLNF,pbc,pibsc,pszTargetName,pszUrl,pszLocation)	\
    ( (This)->lpVtbl -> NavigateHack(This,grfHLNF,pbc,pibsc,pszTargetName,pszUrl,pszLocation) ) 

#define ITargetFramePriv_FindBrowserByIndex(This,dwID,ppunkBrowser)	\
    ( (This)->lpVtbl -> FindBrowserByIndex(This,dwID,ppunkBrowser) ) 

#endif /* COBJMACROS */


#endif 	/* C style interface */




#endif 	/* __ITargetFramePriv_INTERFACE_DEFINED__ */


#ifndef __ITargetFramePriv2_INTERFACE_DEFINED__
#define __ITargetFramePriv2_INTERFACE_DEFINED__

/* interface ITargetFramePriv2 */
/* [unique][uuid][object] */ 

typedef /* [unique] */ ITargetFramePriv2 *LPTARGETFRAMEPRIV2;


EXTERN_C const IID IID_ITargetFramePriv2;

#if defined(__cplusplus) && !defined(CINTERFACE)
    
    MIDL_INTERFACE("B2C867E6-69D6-46F2-A611-DED9A4BD7FEF")
    ITargetFramePriv2 : public ITargetFramePriv
    {
    public:
        virtual HRESULT STDMETHODCALLTYPE AggregatedNavigation2( 
            /* [in] */ DWORD grfHLNF,
            /* [unique][in] */ LPBC pbc,
            /* [unique][in] */ IBindStatusCallback *pibsc,
            /* [unique][in] */ LPCWSTR pszTargetName,
            /* [in] */ IUri *pUri,
            /* [unique][in] */ LPCWSTR pszLocation) = 0;
        
    };
    
    
#else 	/* C style interface */

    typedef struct ITargetFramePriv2Vtbl
    {
        BEGIN_INTERFACE
        
        HRESULT ( STDMETHODCALLTYPE *QueryInterface )( 
            ITargetFramePriv2 * This,
            /* [in] */ REFIID riid,
            /* [annotation][iid_is][out] */ 
            _COM_Outptr_  void **ppvObject);
        
        ULONG ( STDMETHODCALLTYPE *AddRef )( 
            ITargetFramePriv2 * This);
        
        ULONG ( STDMETHODCALLTYPE *Release )( 
            ITargetFramePriv2 * This);
        
        HRESULT ( STDMETHODCALLTYPE *FindFrameDownwards )( 
            ITargetFramePriv2 * This,
            /* [in] */ LPCWSTR pszTargetName,
            /* [in] */ DWORD dwFlags,
            /* [out] */ IUnknown **ppunkTargetFrame);
        
        HRESULT ( STDMETHODCALLTYPE *FindFrameInContext )( 
            ITargetFramePriv2 * This,
            /* [in] */ LPCWSTR pszTargetName,
            /* [in] */ IUnknown *punkContextFrame,
            /* [in] */ DWORD dwFlags,
            /* [out] */ IUnknown **ppunkTargetFrame);
        
        HRESULT ( STDMETHODCALLTYPE *OnChildFrameActivate )( 
            ITargetFramePriv2 * This,
            /* [in] */ IUnknown *pUnkChildFrame);
        
        HRESULT ( STDMETHODCALLTYPE *OnChildFrameDeactivate )( 
            ITargetFramePriv2 * This,
            /* [in] */ IUnknown *pUnkChildFrame);
        
        HRESULT ( STDMETHODCALLTYPE *NavigateHack )( 
            ITargetFramePriv2 * This,
            /* [in] */ DWORD grfHLNF,
            /* [unique][in] */ LPBC pbc,
            /* [unique][in] */ IBindStatusCallback *pibsc,
            /* [unique][in] */ LPCWSTR pszTargetName,
            /* [in] */ LPCWSTR pszUrl,
            /* [unique][in] */ LPCWSTR pszLocation);
        
        HRESULT ( STDMETHODCALLTYPE *FindBrowserByIndex )( 
            ITargetFramePriv2 * This,
            /* [in] */ DWORD dwID,
            /* [out] */ IUnknown **ppunkBrowser);
        
        HRESULT ( STDMETHODCALLTYPE *AggregatedNavigation2 )( 
            ITargetFramePriv2 * This,
            /* [in] */ DWORD grfHLNF,
            /* [unique][in] */ LPBC pbc,
            /* [unique][in] */ IBindStatusCallback *pibsc,
            /* [unique][in] */ LPCWSTR pszTargetName,
            /* [in] */ IUri *pUri,
            /* [unique][in] */ LPCWSTR pszLocation);
        
        END_INTERFACE
    } ITargetFramePriv2Vtbl;

    interface ITargetFramePriv2
    {
        CONST_VTBL struct ITargetFramePriv2Vtbl *lpVtbl;
    };

    

#ifdef COBJMACROS


#define ITargetFramePriv2_QueryInterface(This,riid,ppvObject)	\
    ( (This)->lpVtbl -> QueryInterface(This,riid,ppvObject) ) 

#define ITargetFramePriv2_AddRef(This)	\
    ( (This)->lpVtbl -> AddRef(This) ) 

#define ITargetFramePriv2_Release(This)	\
    ( (This)->lpVtbl -> Release(This) ) 


#define ITargetFramePriv2_FindFrameDownwards(This,pszTargetName,dwFlags,ppunkTargetFrame)	\
    ( (This)->lpVtbl -> FindFrameDownwards(This,pszTargetName,dwFlags,ppunkTargetFrame) ) 

#define ITargetFramePriv2_FindFrameInContext(This,pszTargetName,punkContextFrame,dwFlags,ppunkTargetFrame)	\
    ( (This)->lpVtbl -> FindFrameInContext(This,pszTargetName,punkContextFrame,dwFlags,ppunkTargetFrame) ) 

#define ITargetFramePriv2_OnChildFrameActivate(This,pUnkChildFrame)	\
    ( (This)->lpVtbl -> OnChildFrameActivate(This,pUnkChildFrame) ) 

#define ITargetFramePriv2_OnChildFrameDeactivate(This,pUnkChildFrame)	\
    ( (This)->lpVtbl -> OnChildFrameDeactivate(This,pUnkChildFrame) ) 

#define ITargetFramePriv2_NavigateHack(This,grfHLNF,pbc,pibsc,pszTargetName,pszUrl,pszLocation)	\
    ( (This)->lpVtbl -> NavigateHack(This,grfHLNF,pbc,pibsc,pszTargetName,pszUrl,pszLocation) ) 

#define ITargetFramePriv2_FindBrowserByIndex(This,dwID,ppunkBrowser)	\
    ( (This)->lpVtbl -> FindBrowserByIndex(This,dwID,ppunkBrowser) ) 


#define ITargetFramePriv2_AggregatedNavigation2(This,grfHLNF,pbc,pibsc,pszTargetName,pUri,pszLocation)	\
    ( (This)->lpVtbl -> AggregatedNavigation2(This,grfHLNF,pbc,pibsc,pszTargetName,pUri,pszLocation) ) 

#endif /* COBJMACROS */


#endif 	/* C style interface */




#endif 	/* __ITargetFramePriv2_INTERFACE_DEFINED__ */


/* interface __MIDL_itf_htiface_0000_0004 */
/* [local] */ 

#endif
#endif /* WINAPI_FAMILY_PARTITION(WINAPI_PARTITION_DESKTOP) */
#pragma endregion


extern RPC_IF_HANDLE __MIDL_itf_htiface_0000_0004_v0_0_c_ifspec;
extern RPC_IF_HANDLE __MIDL_itf_htiface_0000_0004_v0_0_s_ifspec;

/* Additional Prototypes for ALL interfaces */

/* end of Additional Prototypes */

#ifdef __cplusplus
}
#endif

#endif


