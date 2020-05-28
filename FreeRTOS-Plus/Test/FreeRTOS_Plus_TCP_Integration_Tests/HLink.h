

/* this ALWAYS GENERATED file contains the definitions for the interfaces */


 /* File created by MIDL compiler version 8.01.0622 */
/* at Mon Jan 18 19:14:07 2038
 */
/* Compiler settings for ..\..\..\..\..\..\..\..\Program Files (x86)\Windows Kits\10\Include\10.0.18362.0\um\HLink.Idl:
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

#ifndef __HLink_h__
#define __HLink_h__

#if defined(_MSC_VER) && (_MSC_VER >= 1020)
#pragma once
#endif

/* Forward Declarations */ 

#ifndef __IHlink_FWD_DEFINED__
#define __IHlink_FWD_DEFINED__
typedef interface IHlink IHlink;

#endif 	/* __IHlink_FWD_DEFINED__ */


#ifndef __IHlinkSite_FWD_DEFINED__
#define __IHlinkSite_FWD_DEFINED__
typedef interface IHlinkSite IHlinkSite;

#endif 	/* __IHlinkSite_FWD_DEFINED__ */


#ifndef __IHlinkTarget_FWD_DEFINED__
#define __IHlinkTarget_FWD_DEFINED__
typedef interface IHlinkTarget IHlinkTarget;

#endif 	/* __IHlinkTarget_FWD_DEFINED__ */


#ifndef __IHlinkFrame_FWD_DEFINED__
#define __IHlinkFrame_FWD_DEFINED__
typedef interface IHlinkFrame IHlinkFrame;

#endif 	/* __IHlinkFrame_FWD_DEFINED__ */


#ifndef __IEnumHLITEM_FWD_DEFINED__
#define __IEnumHLITEM_FWD_DEFINED__
typedef interface IEnumHLITEM IEnumHLITEM;

#endif 	/* __IEnumHLITEM_FWD_DEFINED__ */


#ifndef __IHlinkBrowseContext_FWD_DEFINED__
#define __IHlinkBrowseContext_FWD_DEFINED__
typedef interface IHlinkBrowseContext IHlinkBrowseContext;

#endif 	/* __IHlinkBrowseContext_FWD_DEFINED__ */


#ifndef __IExtensionServices_FWD_DEFINED__
#define __IExtensionServices_FWD_DEFINED__
typedef interface IExtensionServices IExtensionServices;

#endif 	/* __IExtensionServices_FWD_DEFINED__ */


/* header files for imported files */
#include "urlmon.h"

#ifdef __cplusplus
extern "C"{
#endif 


/* interface __MIDL_itf_HLink_0000_0000 */
/* [local] */ 

//=--------------------------------------------------------------------------=
// HLInk.h
//=--------------------------------------------------------------------------=
// (C) Copyright 1995-1997 Microsoft Corporation.  All Rights Reserved.
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
// OLE Hyperlinking Interfaces.
                                                                              
#ifndef HLINK_H                                                               
#define HLINK_H                                                               
                                                                              






// ;BUGBUG We temporarily support the old 'source' names                              
#define SID_SHlinkFrame IID_IHlinkFrame
#define IID_IHlinkSource IID_IHlinkTarget                                     
#define IHlinkSource IHlinkTarget                                             
#define IHlinkSourceVtbl IHlinkTargetVtbl                                     
#define LPHLINKSOURCE LPHLINKTARGET                                           
                                                                              
/****************************************************************************/
/**** Error codes                                                        ****/
/****************************************************************************/
#ifndef _HLINK_ERRORS_DEFINED                                                 
#define _HLINK_ERRORS_DEFINED                                                 
#define HLINK_E_FIRST                    (OLE_E_LAST+1)                       
#define HLINK_S_FIRST                    (OLE_S_LAST+1)                       
#define HLINK_S_DONTHIDE                 (HLINK_S_FIRST)                      
#endif //_HLINK_ERRORS_DEFINED                                                
                                                                              
                                                                              
/****************************************************************************/
/**** Hyperlink APIs                                                     ****/
/****************************************************************************/
                                                                              
#define CFSTR_HYPERLINK         (TEXT("Hyperlink"))                         
                                                                              
                                                                              
STDAPI HlinkCreateFromMoniker(                                                
             IMoniker * pimkTrgt,                                             
             LPCWSTR pwzLocation,                                             
             LPCWSTR pwzFriendlyName,                                         
             IHlinkSite * pihlsite,                                           
             DWORD dwSiteData,                                                
             IUnknown * piunkOuter,                                           
             REFIID riid,                                                     
             void ** ppvObj);                                                 
                                                                              
STDAPI HlinkCreateFromString(                                                 
             LPCWSTR pwzTarget,                                               
             LPCWSTR pwzLocation,                                             
             LPCWSTR pwzFriendlyName,                                         
             IHlinkSite * pihlsite,                                           
             DWORD dwSiteData,                                                
             IUnknown * piunkOuter,                                           
             REFIID riid,                                                     
             void ** ppvObj);                                                 
                                                                              
STDAPI HlinkCreateFromData(                                                   
             IDataObject *piDataObj,                                          
             IHlinkSite * pihlsite,                                           
             DWORD dwSiteData,                                                
             IUnknown * piunkOuter,                                           
             REFIID riid,                                                     
             void ** ppvObj);                                                 
                                                                              
STDAPI HlinkQueryCreateFromData(IDataObject *piDataObj);                      
                                                                              
STDAPI HlinkClone(                                                            
             IHlink * pihl,                                                   
             REFIID riid,                                                     
             IHlinkSite * pihlsiteForClone,                                   
             DWORD dwSiteData,                                                
             void ** ppvObj);                                                 
                                                                              
STDAPI HlinkCreateBrowseContext(                                              
             IUnknown * piunkOuter,                                           
             REFIID riid,                                                     
             void ** ppvObj);                                                 
                                                                              
STDAPI HlinkNavigateToStringReference(                                        
             LPCWSTR pwzTarget,                                               
             LPCWSTR pwzLocation,                                             
             IHlinkSite * pihlsite,                                           
             DWORD dwSiteData,                                                
             IHlinkFrame *pihlframe,                                          
             DWORD grfHLNF,                                                   
             LPBC pibc,                                                       
             IBindStatusCallback * pibsc,                                     
             IHlinkBrowseContext *pihlbc);                                    
                                                                              
STDAPI HlinkNavigate(                                                         
             IHlink * pihl,                                                   
             IHlinkFrame * pihlframe,                                         
             DWORD grfHLNF,                                                   
             LPBC pbc,                                                        
             IBindStatusCallback * pibsc,                                     
             IHlinkBrowseContext *pihlbc);                                    
                                                                              
STDAPI HlinkOnNavigate(                                                       
             IHlinkFrame * pihlframe,                                         
             IHlinkBrowseContext * pihlbc,                                    
             DWORD grfHLNF,                                                   
             IMoniker * pimkTarget,                                           
             LPCWSTR pwzLocation,                                             
             LPCWSTR pwzFriendlyName,                                         
             ULONG * puHLID);                                                 
                                                                              
STDAPI HlinkUpdateStackItem(                                                  
             IHlinkFrame * pihlframe,                                         
             IHlinkBrowseContext * pihlbc,                                    
             ULONG uHLID,                                                     
             IMoniker * pimkTrgt,                                             
             LPCWSTR pwzLocation,                                             
             LPCWSTR pwzFriendlyName);                                        
                                                                              
STDAPI HlinkOnRenameDocument(                                                 
             DWORD dwReserved,                                                
             IHlinkBrowseContext * pihlbc,                                    
             IMoniker * pimkOld,                                              
             IMoniker * pimkNew);                                             
                                                                              
STDAPI HlinkResolveMonikerForData(                                            
             LPMONIKER pimkReference,                                         
             DWORD reserved,                                                  
             LPBC pibc,                                                       
             ULONG cFmtetc,                                                   
             FORMATETC * rgFmtetc,                                            
             IBindStatusCallback * pibsc,                                     
             LPMONIKER pimkBase);                                             
                                                                              
STDAPI HlinkResolveStringForData(                                             
             LPCWSTR pwzReference,                                            
             DWORD reserved,                                                  
             LPBC pibc,                                                       
             ULONG cFmtetc,                                                   
             FORMATETC * rgFmtetc,                                            
             IBindStatusCallback * pibsc,                                     
             LPMONIKER pimkBase);                                             
                                                                              
STDAPI HlinkParseDisplayName(                                                 
             LPBC pibc,                                                       
             LPCWSTR pwzDisplayName,                                          
             BOOL fNoForceAbs,                                                
             ULONG * pcchEaten,                                               
             IMoniker ** ppimk);                                              
                                                                              
STDAPI HlinkCreateExtensionServices(                                          
             LPCWSTR pwzAdditionalHeaders,                                    
             HWND phwnd,                                                      
             LPCWSTR pszUsername,                                             
             LPCWSTR pszPassword,                                             
             IUnknown * piunkOuter,                                           
             REFIID riid,                                                     
             void ** ppvObj);                                                 
                                                                              
STDAPI HlinkPreprocessMoniker(                                                
             LPBC pibc,                                                       
             IMoniker *pimkIn,                                                
             IMoniker **ppimkOut);                                            
                                                                              
STDAPI OleSaveToStreamEx(                                                     
             IUnknown * piunk,                                                
             IStream * pistm,                                                 
             BOOL fClearDirty);                                               
                                                                              
typedef 
enum _HLSR_NOREDEF10
    {
        HLSR_HOME	= 0,
        HLSR_SEARCHPAGE	= 1,
        HLSR_HISTORYFOLDER	= 2
    } 	HLSR;

                                                                              
STDAPI HlinkSetSpecialReference(                                              
             ULONG uReference,                                                
             LPCWSTR pwzReference);                                           
                                                                              
STDAPI HlinkGetSpecialReference(                                              
             ULONG uReference,                                                
             _Outptr_ LPWSTR *ppwzReference);                                          
                                                                              
typedef 
enum _HLSHORTCUTF__NOREDEF10
    {
        HLSHORTCUTF_DEFAULT	= 0,
        HLSHORTCUTF_DONTACTUALLYCREATE	= 0x1,
        HLSHORTCUTF_USEFILENAMEFROMFRIENDLYNAME	= 0x2,
        HLSHORTCUTF_USEUNIQUEFILENAME	= 0x4,
        HLSHORTCUTF_MAYUSEEXISTINGSHORTCUT	= 0x8
    } 	HLSHORTCUTF;

                                                                              
STDAPI HlinkCreateShortcut(                                                   
             DWORD grfHLSHORTCUTF,                                            
             IHlink *pihl,                                                    
             LPCWSTR pwzDir,                                                  
             LPCWSTR pwzFileName,                                             
             _Outptr_ LPWSTR *ppwzShortcutFile,                                        
             DWORD dwReserved);                                               
                                                                              
STDAPI HlinkCreateShortcutFromMoniker(                                        
             DWORD grfHLSHORTCUTF,                                            
             IMoniker *pimkTarget,                                            
             LPCWSTR pwzLocation,                                             
             LPCWSTR pwzDir,                                                  
             LPCWSTR pwzFileName,                                             
             _Outptr_ LPWSTR *ppwzShortcutFile,                                        
             DWORD dwReserved);                                               
                                                                              
STDAPI HlinkCreateShortcutFromString(                                         
             DWORD grfHLSHORTCUTF,                                            
             LPCWSTR pwzTarget,                                               
             LPCWSTR pwzLocation,                                             
             LPCWSTR pwzDir,                                                  
             LPCWSTR pwzFileName,                                             
             _Outptr_ LPWSTR *ppwzShortcutFile,                                        
             DWORD dwReserved);                                               
                                                                              
STDAPI HlinkResolveShortcut(                                                  
             LPCWSTR pwzShortcutFileName,                                     
             IHlinkSite * pihlsite,                                           
             DWORD dwSiteData,                                                
             IUnknown * piunkOuter,                                           
             REFIID riid,                                                     
             void ** ppvObj);                                                 
                                                                              
STDAPI HlinkResolveShortcutToMoniker(                                         
             LPCWSTR pwzShortcutFileName,                                     
             IMoniker **ppimkTarget,                                          
             _Outptr_ LPWSTR *ppwzLocation);                                           
                                                                              
STDAPI HlinkResolveShortcutToString(                                          
             LPCWSTR pwzShortcutFileName,                                     
             _Outptr_ LPWSTR *ppwzTarget,                                              
             _Outptr_ LPWSTR *ppwzLocation);                                           
                                                                              
                                                                              
 STDAPI HlinkIsShortcut(LPCWSTR pwzFileName);                                 
                                                                              
                                                                              
STDAPI HlinkGetValueFromParams(                                               
             LPCWSTR pwzParams,                                               
             LPCWSTR pwzName,                                                 
             _Outptr_ LPWSTR *ppwzValue);                                              
                                                                              
                                                                              
typedef 
enum _HLTRANSLATEF_NOREDEF10
    {
        HLTRANSLATEF_DEFAULT	= 0,
        HLTRANSLATEF_DONTAPPLYDEFAULTPREFIX	= 0x1
    } 	HLTRANSLATEF;

                                                                              
STDAPI HlinkTranslateURL(                                                     
             LPCWSTR pwzURL,                                                  
             DWORD grfFlags,                                                  
             _Outptr_ LPWSTR *ppwzTranslatedURL);                                      
                                                                              
                                                                              
                                                                              
/****************************************************************************/
/**** Hyperlink interface definitions                                    ****/
/****************************************************************************/
                                                                              
#ifndef _LPHLINK_DEFINED
#define _LPHLINK_DEFINED


extern RPC_IF_HANDLE __MIDL_itf_HLink_0000_0000_v0_0_c_ifspec;
extern RPC_IF_HANDLE __MIDL_itf_HLink_0000_0000_v0_0_s_ifspec;

#ifndef __IHlink_INTERFACE_DEFINED__
#define __IHlink_INTERFACE_DEFINED__

/* interface IHlink */
/* [unique][uuid][object] */ 

typedef /* [unique] */ IHlink *LPHLINK;

typedef /* [public] */ 
enum __MIDL_IHlink_0001
    {
        HLNF_INTERNALJUMP	= 0x1,
        HLNF_OPENINNEWWINDOW	= 0x2,
        HLNF_NAVIGATINGBACK	= 0x4,
        HLNF_NAVIGATINGFORWARD	= 0x8,
        HLNF_NAVIGATINGTOSTACKITEM	= 0x10,
        HLNF_CREATENOHISTORY	= 0x20
    } 	HLNF;

typedef /* [public] */ 
enum __MIDL_IHlink_0002
    {
        HLINKGETREF_DEFAULT	= 0,
        HLINKGETREF_ABSOLUTE	= 1,
        HLINKGETREF_RELATIVE	= 2
    } 	HLINKGETREF;

typedef /* [public] */ 
enum __MIDL_IHlink_0003
    {
        HLFNAMEF_DEFAULT	= 0,
        HLFNAMEF_TRYCACHE	= 0x1,
        HLFNAMEF_TRYPRETTYTARGET	= 0x2,
        HLFNAMEF_TRYFULLTARGET	= 0x4,
        HLFNAMEF_TRYWIN95SHORTCUT	= 0x8
    } 	HLFNAMEF;

typedef /* [public] */ 
enum __MIDL_IHlink_0004
    {
        HLINKMISC_RELATIVE	= 0x1
    } 	HLINKMISC;

typedef /* [public] */ 
enum __MIDL_IHlink_0005
    {
        HLINKSETF_TARGET	= 0x1,
        HLINKSETF_LOCATION	= 0x2
    } 	HLINKSETF;


EXTERN_C const IID IID_IHlink;

#if defined(__cplusplus) && !defined(CINTERFACE)
    
    MIDL_INTERFACE("79eac9c3-baf9-11ce-8c82-00aa004ba90b")
    IHlink : public IUnknown
    {
    public:
        virtual HRESULT STDMETHODCALLTYPE SetHlinkSite( 
            /* [unique][in] */ IHlinkSite *pihlSite,
            /* [in] */ DWORD dwSiteData) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE GetHlinkSite( 
            /* [out] */ IHlinkSite **ppihlSite,
            /* [out] */ DWORD *pdwSiteData) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE SetMonikerReference( 
            /* [in] */ DWORD grfHLSETF,
            /* [unique][in] */ IMoniker *pimkTarget,
            /* [unique][in] */ LPCWSTR pwzLocation) = 0;
        
        virtual /* [local] */ HRESULT STDMETHODCALLTYPE GetMonikerReference( 
            /* [in] */ DWORD dwWhichRef,
            /* [annotation][out] */ 
            _Outptr_opt_result_maybenull_  IMoniker **ppimkTarget,
            /* [annotation][out] */ 
            _Outptr_opt_result_maybenull_  LPWSTR *ppwzLocation) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE SetStringReference( 
            /* [in] */ DWORD grfHLSETF,
            /* [unique][in] */ LPCWSTR pwzTarget,
            /* [unique][in] */ LPCWSTR pwzLocation) = 0;
        
        virtual /* [local] */ HRESULT STDMETHODCALLTYPE GetStringReference( 
            /* [in] */ DWORD dwWhichRef,
            /* [annotation][out] */ 
            _Outptr_opt_  LPWSTR *ppwzTarget,
            /* [annotation][out] */ 
            _Outptr_opt_result_maybenull_  LPWSTR *ppwzLocation) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE SetFriendlyName( 
            /* [unique][in] */ LPCWSTR pwzFriendlyName) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE GetFriendlyName( 
            /* [in] */ DWORD grfHLFNAMEF,
            /* [out] */ LPWSTR *ppwzFriendlyName) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE SetTargetFrameName( 
            /* [unique][in] */ LPCWSTR pwzTargetFrameName) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE GetTargetFrameName( 
            /* [out] */ LPWSTR *ppwzTargetFrameName) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE GetMiscStatus( 
            /* [out] */ DWORD *pdwStatus) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE Navigate( 
            /* [in] */ DWORD grfHLNF,
            /* [unique][in] */ LPBC pibc,
            /* [unique][in] */ IBindStatusCallback *pibsc,
            /* [unique][in] */ IHlinkBrowseContext *pihlbc) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE SetAdditionalParams( 
            /* [unique][in] */ LPCWSTR pwzAdditionalParams) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE GetAdditionalParams( 
            /* [out] */ LPWSTR *ppwzAdditionalParams) = 0;
        
    };
    
    
#else 	/* C style interface */

    typedef struct IHlinkVtbl
    {
        BEGIN_INTERFACE
        
        HRESULT ( STDMETHODCALLTYPE *QueryInterface )( 
            IHlink * This,
            /* [in] */ REFIID riid,
            /* [annotation][iid_is][out] */ 
            _COM_Outptr_  void **ppvObject);
        
        ULONG ( STDMETHODCALLTYPE *AddRef )( 
            IHlink * This);
        
        ULONG ( STDMETHODCALLTYPE *Release )( 
            IHlink * This);
        
        HRESULT ( STDMETHODCALLTYPE *SetHlinkSite )( 
            IHlink * This,
            /* [unique][in] */ IHlinkSite *pihlSite,
            /* [in] */ DWORD dwSiteData);
        
        HRESULT ( STDMETHODCALLTYPE *GetHlinkSite )( 
            IHlink * This,
            /* [out] */ IHlinkSite **ppihlSite,
            /* [out] */ DWORD *pdwSiteData);
        
        HRESULT ( STDMETHODCALLTYPE *SetMonikerReference )( 
            IHlink * This,
            /* [in] */ DWORD grfHLSETF,
            /* [unique][in] */ IMoniker *pimkTarget,
            /* [unique][in] */ LPCWSTR pwzLocation);
        
        /* [local] */ HRESULT ( STDMETHODCALLTYPE *GetMonikerReference )( 
            IHlink * This,
            /* [in] */ DWORD dwWhichRef,
            /* [annotation][out] */ 
            _Outptr_opt_result_maybenull_  IMoniker **ppimkTarget,
            /* [annotation][out] */ 
            _Outptr_opt_result_maybenull_  LPWSTR *ppwzLocation);
        
        HRESULT ( STDMETHODCALLTYPE *SetStringReference )( 
            IHlink * This,
            /* [in] */ DWORD grfHLSETF,
            /* [unique][in] */ LPCWSTR pwzTarget,
            /* [unique][in] */ LPCWSTR pwzLocation);
        
        /* [local] */ HRESULT ( STDMETHODCALLTYPE *GetStringReference )( 
            IHlink * This,
            /* [in] */ DWORD dwWhichRef,
            /* [annotation][out] */ 
            _Outptr_opt_  LPWSTR *ppwzTarget,
            /* [annotation][out] */ 
            _Outptr_opt_result_maybenull_  LPWSTR *ppwzLocation);
        
        HRESULT ( STDMETHODCALLTYPE *SetFriendlyName )( 
            IHlink * This,
            /* [unique][in] */ LPCWSTR pwzFriendlyName);
        
        HRESULT ( STDMETHODCALLTYPE *GetFriendlyName )( 
            IHlink * This,
            /* [in] */ DWORD grfHLFNAMEF,
            /* [out] */ LPWSTR *ppwzFriendlyName);
        
        HRESULT ( STDMETHODCALLTYPE *SetTargetFrameName )( 
            IHlink * This,
            /* [unique][in] */ LPCWSTR pwzTargetFrameName);
        
        HRESULT ( STDMETHODCALLTYPE *GetTargetFrameName )( 
            IHlink * This,
            /* [out] */ LPWSTR *ppwzTargetFrameName);
        
        HRESULT ( STDMETHODCALLTYPE *GetMiscStatus )( 
            IHlink * This,
            /* [out] */ DWORD *pdwStatus);
        
        HRESULT ( STDMETHODCALLTYPE *Navigate )( 
            IHlink * This,
            /* [in] */ DWORD grfHLNF,
            /* [unique][in] */ LPBC pibc,
            /* [unique][in] */ IBindStatusCallback *pibsc,
            /* [unique][in] */ IHlinkBrowseContext *pihlbc);
        
        HRESULT ( STDMETHODCALLTYPE *SetAdditionalParams )( 
            IHlink * This,
            /* [unique][in] */ LPCWSTR pwzAdditionalParams);
        
        HRESULT ( STDMETHODCALLTYPE *GetAdditionalParams )( 
            IHlink * This,
            /* [out] */ LPWSTR *ppwzAdditionalParams);
        
        END_INTERFACE
    } IHlinkVtbl;

    interface IHlink
    {
        CONST_VTBL struct IHlinkVtbl *lpVtbl;
    };

    

#ifdef COBJMACROS


#define IHlink_QueryInterface(This,riid,ppvObject)	\
    ( (This)->lpVtbl -> QueryInterface(This,riid,ppvObject) ) 

#define IHlink_AddRef(This)	\
    ( (This)->lpVtbl -> AddRef(This) ) 

#define IHlink_Release(This)	\
    ( (This)->lpVtbl -> Release(This) ) 


#define IHlink_SetHlinkSite(This,pihlSite,dwSiteData)	\
    ( (This)->lpVtbl -> SetHlinkSite(This,pihlSite,dwSiteData) ) 

#define IHlink_GetHlinkSite(This,ppihlSite,pdwSiteData)	\
    ( (This)->lpVtbl -> GetHlinkSite(This,ppihlSite,pdwSiteData) ) 

#define IHlink_SetMonikerReference(This,grfHLSETF,pimkTarget,pwzLocation)	\
    ( (This)->lpVtbl -> SetMonikerReference(This,grfHLSETF,pimkTarget,pwzLocation) ) 

#define IHlink_GetMonikerReference(This,dwWhichRef,ppimkTarget,ppwzLocation)	\
    ( (This)->lpVtbl -> GetMonikerReference(This,dwWhichRef,ppimkTarget,ppwzLocation) ) 

#define IHlink_SetStringReference(This,grfHLSETF,pwzTarget,pwzLocation)	\
    ( (This)->lpVtbl -> SetStringReference(This,grfHLSETF,pwzTarget,pwzLocation) ) 

#define IHlink_GetStringReference(This,dwWhichRef,ppwzTarget,ppwzLocation)	\
    ( (This)->lpVtbl -> GetStringReference(This,dwWhichRef,ppwzTarget,ppwzLocation) ) 

#define IHlink_SetFriendlyName(This,pwzFriendlyName)	\
    ( (This)->lpVtbl -> SetFriendlyName(This,pwzFriendlyName) ) 

#define IHlink_GetFriendlyName(This,grfHLFNAMEF,ppwzFriendlyName)	\
    ( (This)->lpVtbl -> GetFriendlyName(This,grfHLFNAMEF,ppwzFriendlyName) ) 

#define IHlink_SetTargetFrameName(This,pwzTargetFrameName)	\
    ( (This)->lpVtbl -> SetTargetFrameName(This,pwzTargetFrameName) ) 

#define IHlink_GetTargetFrameName(This,ppwzTargetFrameName)	\
    ( (This)->lpVtbl -> GetTargetFrameName(This,ppwzTargetFrameName) ) 

#define IHlink_GetMiscStatus(This,pdwStatus)	\
    ( (This)->lpVtbl -> GetMiscStatus(This,pdwStatus) ) 

#define IHlink_Navigate(This,grfHLNF,pibc,pibsc,pihlbc)	\
    ( (This)->lpVtbl -> Navigate(This,grfHLNF,pibc,pibsc,pihlbc) ) 

#define IHlink_SetAdditionalParams(This,pwzAdditionalParams)	\
    ( (This)->lpVtbl -> SetAdditionalParams(This,pwzAdditionalParams) ) 

#define IHlink_GetAdditionalParams(This,ppwzAdditionalParams)	\
    ( (This)->lpVtbl -> GetAdditionalParams(This,ppwzAdditionalParams) ) 

#endif /* COBJMACROS */


#endif 	/* C style interface */



/* [call_as] */ HRESULT STDMETHODCALLTYPE IHlink_RemoteGetMonikerReference_Proxy( 
    IHlink * This,
    /* [in] */ DWORD dwWhichRef,
    /* [out] */ IMoniker **ppimkTarget,
    /* [out] */ LPWSTR *ppwzLocation);


void __RPC_STUB IHlink_RemoteGetMonikerReference_Stub(
    IRpcStubBuffer *This,
    IRpcChannelBuffer *_pRpcChannelBuffer,
    PRPC_MESSAGE _pRpcMessage,
    DWORD *_pdwStubPhase);


/* [call_as] */ HRESULT STDMETHODCALLTYPE IHlink_RemoteGetStringReference_Proxy( 
    IHlink * This,
    /* [in] */ DWORD dwWhichRef,
    /* [out] */ LPWSTR *ppwzTarget,
    /* [out] */ LPWSTR *ppwzLocation);


void __RPC_STUB IHlink_RemoteGetStringReference_Stub(
    IRpcStubBuffer *This,
    IRpcChannelBuffer *_pRpcChannelBuffer,
    PRPC_MESSAGE _pRpcMessage,
    DWORD *_pdwStubPhase);



#endif 	/* __IHlink_INTERFACE_DEFINED__ */


/* interface __MIDL_itf_HLink_0000_0001 */
/* [local] */ 

#endif
#ifndef _LPHLINKSITE_DEFINED
#define _LPHLINKSITE_DEFINED
EXTERN_C const GUID SID_SContainer;


extern RPC_IF_HANDLE __MIDL_itf_HLink_0000_0001_v0_0_c_ifspec;
extern RPC_IF_HANDLE __MIDL_itf_HLink_0000_0001_v0_0_s_ifspec;

#ifndef __IHlinkSite_INTERFACE_DEFINED__
#define __IHlinkSite_INTERFACE_DEFINED__

/* interface IHlinkSite */
/* [unique][uuid][object] */ 

typedef /* [unique] */ IHlinkSite *LPHLINKSITE;

typedef /* [public] */ 
enum __MIDL_IHlinkSite_0001
    {
        HLINKWHICHMK_CONTAINER	= 1,
        HLINKWHICHMK_BASE	= 2
    } 	HLINKWHICHMK;


EXTERN_C const IID IID_IHlinkSite;

#if defined(__cplusplus) && !defined(CINTERFACE)
    
    MIDL_INTERFACE("79eac9c2-baf9-11ce-8c82-00aa004ba90b")
    IHlinkSite : public IUnknown
    {
    public:
        virtual HRESULT STDMETHODCALLTYPE QueryService( 
            /* [in] */ DWORD dwSiteData,
            /* [in] */ REFGUID guidService,
            /* [in] */ REFIID riid,
            /* [iid_is][out] */ IUnknown **ppiunk) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE GetMoniker( 
            /* [in] */ DWORD dwSiteData,
            /* [in] */ DWORD dwAssign,
            /* [in] */ DWORD dwWhich,
            /* [out] */ IMoniker **ppimk) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE ReadyToNavigate( 
            /* [in] */ DWORD dwSiteData,
            /* [in] */ DWORD dwReserved) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE OnNavigationComplete( 
            /* [in] */ DWORD dwSiteData,
            /* [in] */ DWORD dwreserved,
            /* [in] */ HRESULT hrError,
            /* [unique][in] */ LPCWSTR pwzError) = 0;
        
    };
    
    
#else 	/* C style interface */

    typedef struct IHlinkSiteVtbl
    {
        BEGIN_INTERFACE
        
        HRESULT ( STDMETHODCALLTYPE *QueryInterface )( 
            IHlinkSite * This,
            /* [in] */ REFIID riid,
            /* [annotation][iid_is][out] */ 
            _COM_Outptr_  void **ppvObject);
        
        ULONG ( STDMETHODCALLTYPE *AddRef )( 
            IHlinkSite * This);
        
        ULONG ( STDMETHODCALLTYPE *Release )( 
            IHlinkSite * This);
        
        HRESULT ( STDMETHODCALLTYPE *QueryService )( 
            IHlinkSite * This,
            /* [in] */ DWORD dwSiteData,
            /* [in] */ REFGUID guidService,
            /* [in] */ REFIID riid,
            /* [iid_is][out] */ IUnknown **ppiunk);
        
        HRESULT ( STDMETHODCALLTYPE *GetMoniker )( 
            IHlinkSite * This,
            /* [in] */ DWORD dwSiteData,
            /* [in] */ DWORD dwAssign,
            /* [in] */ DWORD dwWhich,
            /* [out] */ IMoniker **ppimk);
        
        HRESULT ( STDMETHODCALLTYPE *ReadyToNavigate )( 
            IHlinkSite * This,
            /* [in] */ DWORD dwSiteData,
            /* [in] */ DWORD dwReserved);
        
        HRESULT ( STDMETHODCALLTYPE *OnNavigationComplete )( 
            IHlinkSite * This,
            /* [in] */ DWORD dwSiteData,
            /* [in] */ DWORD dwreserved,
            /* [in] */ HRESULT hrError,
            /* [unique][in] */ LPCWSTR pwzError);
        
        END_INTERFACE
    } IHlinkSiteVtbl;

    interface IHlinkSite
    {
        CONST_VTBL struct IHlinkSiteVtbl *lpVtbl;
    };

    

#ifdef COBJMACROS


#define IHlinkSite_QueryInterface(This,riid,ppvObject)	\
    ( (This)->lpVtbl -> QueryInterface(This,riid,ppvObject) ) 

#define IHlinkSite_AddRef(This)	\
    ( (This)->lpVtbl -> AddRef(This) ) 

#define IHlinkSite_Release(This)	\
    ( (This)->lpVtbl -> Release(This) ) 


#define IHlinkSite_QueryService(This,dwSiteData,guidService,riid,ppiunk)	\
    ( (This)->lpVtbl -> QueryService(This,dwSiteData,guidService,riid,ppiunk) ) 

#define IHlinkSite_GetMoniker(This,dwSiteData,dwAssign,dwWhich,ppimk)	\
    ( (This)->lpVtbl -> GetMoniker(This,dwSiteData,dwAssign,dwWhich,ppimk) ) 

#define IHlinkSite_ReadyToNavigate(This,dwSiteData,dwReserved)	\
    ( (This)->lpVtbl -> ReadyToNavigate(This,dwSiteData,dwReserved) ) 

#define IHlinkSite_OnNavigationComplete(This,dwSiteData,dwreserved,hrError,pwzError)	\
    ( (This)->lpVtbl -> OnNavigationComplete(This,dwSiteData,dwreserved,hrError,pwzError) ) 

#endif /* COBJMACROS */


#endif 	/* C style interface */




#endif 	/* __IHlinkSite_INTERFACE_DEFINED__ */


/* interface __MIDL_itf_HLink_0000_0002 */
/* [local] */ 

#endif
#ifndef _LPHLINKTARGET_DEFINED
#define _LPHLINKTARGET_DEFINED


extern RPC_IF_HANDLE __MIDL_itf_HLink_0000_0002_v0_0_c_ifspec;
extern RPC_IF_HANDLE __MIDL_itf_HLink_0000_0002_v0_0_s_ifspec;

#ifndef __IHlinkTarget_INTERFACE_DEFINED__
#define __IHlinkTarget_INTERFACE_DEFINED__

/* interface IHlinkTarget */
/* [unique][uuid][object] */ 

typedef /* [unique] */ IHlinkTarget *LPHLINKTARGET;


EXTERN_C const IID IID_IHlinkTarget;

#if defined(__cplusplus) && !defined(CINTERFACE)
    
    MIDL_INTERFACE("79eac9c4-baf9-11ce-8c82-00aa004ba90b")
    IHlinkTarget : public IUnknown
    {
    public:
        virtual HRESULT STDMETHODCALLTYPE SetBrowseContext( 
            /* [unique][in] */ IHlinkBrowseContext *pihlbc) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE GetBrowseContext( 
            /* [out] */ IHlinkBrowseContext **ppihlbc) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE Navigate( 
            /* [in] */ DWORD grfHLNF,
            /* [unique][in] */ LPCWSTR pwzJumpLocation) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE GetMoniker( 
            /* [unique][in] */ LPCWSTR pwzLocation,
            /* [in] */ DWORD dwAssign,
            /* [out] */ IMoniker **ppimkLocation) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE GetFriendlyName( 
            /* [unique][in] */ LPCWSTR pwzLocation,
            /* [out] */ LPWSTR *ppwzFriendlyName) = 0;
        
    };
    
    
#else 	/* C style interface */

    typedef struct IHlinkTargetVtbl
    {
        BEGIN_INTERFACE
        
        HRESULT ( STDMETHODCALLTYPE *QueryInterface )( 
            IHlinkTarget * This,
            /* [in] */ REFIID riid,
            /* [annotation][iid_is][out] */ 
            _COM_Outptr_  void **ppvObject);
        
        ULONG ( STDMETHODCALLTYPE *AddRef )( 
            IHlinkTarget * This);
        
        ULONG ( STDMETHODCALLTYPE *Release )( 
            IHlinkTarget * This);
        
        HRESULT ( STDMETHODCALLTYPE *SetBrowseContext )( 
            IHlinkTarget * This,
            /* [unique][in] */ IHlinkBrowseContext *pihlbc);
        
        HRESULT ( STDMETHODCALLTYPE *GetBrowseContext )( 
            IHlinkTarget * This,
            /* [out] */ IHlinkBrowseContext **ppihlbc);
        
        HRESULT ( STDMETHODCALLTYPE *Navigate )( 
            IHlinkTarget * This,
            /* [in] */ DWORD grfHLNF,
            /* [unique][in] */ LPCWSTR pwzJumpLocation);
        
        HRESULT ( STDMETHODCALLTYPE *GetMoniker )( 
            IHlinkTarget * This,
            /* [unique][in] */ LPCWSTR pwzLocation,
            /* [in] */ DWORD dwAssign,
            /* [out] */ IMoniker **ppimkLocation);
        
        HRESULT ( STDMETHODCALLTYPE *GetFriendlyName )( 
            IHlinkTarget * This,
            /* [unique][in] */ LPCWSTR pwzLocation,
            /* [out] */ LPWSTR *ppwzFriendlyName);
        
        END_INTERFACE
    } IHlinkTargetVtbl;

    interface IHlinkTarget
    {
        CONST_VTBL struct IHlinkTargetVtbl *lpVtbl;
    };

    

#ifdef COBJMACROS


#define IHlinkTarget_QueryInterface(This,riid,ppvObject)	\
    ( (This)->lpVtbl -> QueryInterface(This,riid,ppvObject) ) 

#define IHlinkTarget_AddRef(This)	\
    ( (This)->lpVtbl -> AddRef(This) ) 

#define IHlinkTarget_Release(This)	\
    ( (This)->lpVtbl -> Release(This) ) 


#define IHlinkTarget_SetBrowseContext(This,pihlbc)	\
    ( (This)->lpVtbl -> SetBrowseContext(This,pihlbc) ) 

#define IHlinkTarget_GetBrowseContext(This,ppihlbc)	\
    ( (This)->lpVtbl -> GetBrowseContext(This,ppihlbc) ) 

#define IHlinkTarget_Navigate(This,grfHLNF,pwzJumpLocation)	\
    ( (This)->lpVtbl -> Navigate(This,grfHLNF,pwzJumpLocation) ) 

#define IHlinkTarget_GetMoniker(This,pwzLocation,dwAssign,ppimkLocation)	\
    ( (This)->lpVtbl -> GetMoniker(This,pwzLocation,dwAssign,ppimkLocation) ) 

#define IHlinkTarget_GetFriendlyName(This,pwzLocation,ppwzFriendlyName)	\
    ( (This)->lpVtbl -> GetFriendlyName(This,pwzLocation,ppwzFriendlyName) ) 

#endif /* COBJMACROS */


#endif 	/* C style interface */




#endif 	/* __IHlinkTarget_INTERFACE_DEFINED__ */


/* interface __MIDL_itf_HLink_0000_0003 */
/* [local] */ 

#endif
#ifndef _LPHLINKFRAME_DEFINED
#define _LPHLINKFRAME_DEFINED
EXTERN_C const GUID SID_SHlinkFrame;


extern RPC_IF_HANDLE __MIDL_itf_HLink_0000_0003_v0_0_c_ifspec;
extern RPC_IF_HANDLE __MIDL_itf_HLink_0000_0003_v0_0_s_ifspec;

#ifndef __IHlinkFrame_INTERFACE_DEFINED__
#define __IHlinkFrame_INTERFACE_DEFINED__

/* interface IHlinkFrame */
/* [unique][uuid][object] */ 

typedef /* [unique] */ IHlinkFrame *LPHLINKFRAME;


EXTERN_C const IID IID_IHlinkFrame;

#if defined(__cplusplus) && !defined(CINTERFACE)
    
    MIDL_INTERFACE("79eac9c5-baf9-11ce-8c82-00aa004ba90b")
    IHlinkFrame : public IUnknown
    {
    public:
        virtual HRESULT STDMETHODCALLTYPE SetBrowseContext( 
            /* [unique][in] */ IHlinkBrowseContext *pihlbc) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE GetBrowseContext( 
            /* [out] */ IHlinkBrowseContext **ppihlbc) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE Navigate( 
            /* [in] */ DWORD grfHLNF,
            /* [unique][in] */ LPBC pbc,
            /* [unique][in] */ IBindStatusCallback *pibsc,
            /* [unique][in] */ IHlink *pihlNavigate) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE OnNavigate( 
            /* [in] */ DWORD grfHLNF,
            /* [unique][in] */ IMoniker *pimkTarget,
            /* [unique][in] */ LPCWSTR pwzLocation,
            /* [unique][in] */ LPCWSTR pwzFriendlyName,
            /* [in] */ DWORD dwreserved) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE UpdateHlink( 
            /* [in] */ ULONG uHLID,
            /* [unique][in] */ IMoniker *pimkTarget,
            /* [unique][in] */ LPCWSTR pwzLocation,
            /* [unique][in] */ LPCWSTR pwzFriendlyName) = 0;
        
    };
    
    
#else 	/* C style interface */

    typedef struct IHlinkFrameVtbl
    {
        BEGIN_INTERFACE
        
        HRESULT ( STDMETHODCALLTYPE *QueryInterface )( 
            IHlinkFrame * This,
            /* [in] */ REFIID riid,
            /* [annotation][iid_is][out] */ 
            _COM_Outptr_  void **ppvObject);
        
        ULONG ( STDMETHODCALLTYPE *AddRef )( 
            IHlinkFrame * This);
        
        ULONG ( STDMETHODCALLTYPE *Release )( 
            IHlinkFrame * This);
        
        HRESULT ( STDMETHODCALLTYPE *SetBrowseContext )( 
            IHlinkFrame * This,
            /* [unique][in] */ IHlinkBrowseContext *pihlbc);
        
        HRESULT ( STDMETHODCALLTYPE *GetBrowseContext )( 
            IHlinkFrame * This,
            /* [out] */ IHlinkBrowseContext **ppihlbc);
        
        HRESULT ( STDMETHODCALLTYPE *Navigate )( 
            IHlinkFrame * This,
            /* [in] */ DWORD grfHLNF,
            /* [unique][in] */ LPBC pbc,
            /* [unique][in] */ IBindStatusCallback *pibsc,
            /* [unique][in] */ IHlink *pihlNavigate);
        
        HRESULT ( STDMETHODCALLTYPE *OnNavigate )( 
            IHlinkFrame * This,
            /* [in] */ DWORD grfHLNF,
            /* [unique][in] */ IMoniker *pimkTarget,
            /* [unique][in] */ LPCWSTR pwzLocation,
            /* [unique][in] */ LPCWSTR pwzFriendlyName,
            /* [in] */ DWORD dwreserved);
        
        HRESULT ( STDMETHODCALLTYPE *UpdateHlink )( 
            IHlinkFrame * This,
            /* [in] */ ULONG uHLID,
            /* [unique][in] */ IMoniker *pimkTarget,
            /* [unique][in] */ LPCWSTR pwzLocation,
            /* [unique][in] */ LPCWSTR pwzFriendlyName);
        
        END_INTERFACE
    } IHlinkFrameVtbl;

    interface IHlinkFrame
    {
        CONST_VTBL struct IHlinkFrameVtbl *lpVtbl;
    };

    

#ifdef COBJMACROS


#define IHlinkFrame_QueryInterface(This,riid,ppvObject)	\
    ( (This)->lpVtbl -> QueryInterface(This,riid,ppvObject) ) 

#define IHlinkFrame_AddRef(This)	\
    ( (This)->lpVtbl -> AddRef(This) ) 

#define IHlinkFrame_Release(This)	\
    ( (This)->lpVtbl -> Release(This) ) 


#define IHlinkFrame_SetBrowseContext(This,pihlbc)	\
    ( (This)->lpVtbl -> SetBrowseContext(This,pihlbc) ) 

#define IHlinkFrame_GetBrowseContext(This,ppihlbc)	\
    ( (This)->lpVtbl -> GetBrowseContext(This,ppihlbc) ) 

#define IHlinkFrame_Navigate(This,grfHLNF,pbc,pibsc,pihlNavigate)	\
    ( (This)->lpVtbl -> Navigate(This,grfHLNF,pbc,pibsc,pihlNavigate) ) 

#define IHlinkFrame_OnNavigate(This,grfHLNF,pimkTarget,pwzLocation,pwzFriendlyName,dwreserved)	\
    ( (This)->lpVtbl -> OnNavigate(This,grfHLNF,pimkTarget,pwzLocation,pwzFriendlyName,dwreserved) ) 

#define IHlinkFrame_UpdateHlink(This,uHLID,pimkTarget,pwzLocation,pwzFriendlyName)	\
    ( (This)->lpVtbl -> UpdateHlink(This,uHLID,pimkTarget,pwzLocation,pwzFriendlyName) ) 

#endif /* COBJMACROS */


#endif 	/* C style interface */




#endif 	/* __IHlinkFrame_INTERFACE_DEFINED__ */


/* interface __MIDL_itf_HLink_0000_0004 */
/* [local] */ 

#endif
#ifndef _LPENUMHLITEM_DEFINED
#define _LPENUMHLITEM_DEFINED


extern RPC_IF_HANDLE __MIDL_itf_HLink_0000_0004_v0_0_c_ifspec;
extern RPC_IF_HANDLE __MIDL_itf_HLink_0000_0004_v0_0_s_ifspec;

#ifndef __IEnumHLITEM_INTERFACE_DEFINED__
#define __IEnumHLITEM_INTERFACE_DEFINED__

/* interface IEnumHLITEM */
/* [unique][uuid][object][local] */ 

typedef /* [unique] */ IEnumHLITEM *LPENUMHLITEM;

typedef struct tagHLITEM
    {
    ULONG uHLID;
    LPWSTR pwzFriendlyName;
    } 	HLITEM;

typedef /* [unique] */ HLITEM *LPHLITEM;


EXTERN_C const IID IID_IEnumHLITEM;

#if defined(__cplusplus) && !defined(CINTERFACE)
    
    MIDL_INTERFACE("79eac9c6-baf9-11ce-8c82-00aa004ba90b")
    IEnumHLITEM : public IUnknown
    {
    public:
        virtual HRESULT __stdcall Next( 
            /* [in] */ ULONG celt,
            /* [out] */ HLITEM *rgelt,
            /* [out] */ ULONG *pceltFetched) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE Skip( 
            /* [in] */ ULONG celt) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE Reset( void) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE Clone( 
            /* [out] */ IEnumHLITEM **ppienumhlitem) = 0;
        
    };
    
    
#else 	/* C style interface */

    typedef struct IEnumHLITEMVtbl
    {
        BEGIN_INTERFACE
        
        HRESULT ( STDMETHODCALLTYPE *QueryInterface )( 
            IEnumHLITEM * This,
            /* [in] */ REFIID riid,
            /* [annotation][iid_is][out] */ 
            _COM_Outptr_  void **ppvObject);
        
        ULONG ( STDMETHODCALLTYPE *AddRef )( 
            IEnumHLITEM * This);
        
        ULONG ( STDMETHODCALLTYPE *Release )( 
            IEnumHLITEM * This);
        
        HRESULT ( __stdcall *Next )( 
            IEnumHLITEM * This,
            /* [in] */ ULONG celt,
            /* [out] */ HLITEM *rgelt,
            /* [out] */ ULONG *pceltFetched);
        
        HRESULT ( STDMETHODCALLTYPE *Skip )( 
            IEnumHLITEM * This,
            /* [in] */ ULONG celt);
        
        HRESULT ( STDMETHODCALLTYPE *Reset )( 
            IEnumHLITEM * This);
        
        HRESULT ( STDMETHODCALLTYPE *Clone )( 
            IEnumHLITEM * This,
            /* [out] */ IEnumHLITEM **ppienumhlitem);
        
        END_INTERFACE
    } IEnumHLITEMVtbl;

    interface IEnumHLITEM
    {
        CONST_VTBL struct IEnumHLITEMVtbl *lpVtbl;
    };

    

#ifdef COBJMACROS


#define IEnumHLITEM_QueryInterface(This,riid,ppvObject)	\
    ( (This)->lpVtbl -> QueryInterface(This,riid,ppvObject) ) 

#define IEnumHLITEM_AddRef(This)	\
    ( (This)->lpVtbl -> AddRef(This) ) 

#define IEnumHLITEM_Release(This)	\
    ( (This)->lpVtbl -> Release(This) ) 


#define IEnumHLITEM_Next(This,celt,rgelt,pceltFetched)	\
    ( (This)->lpVtbl -> Next(This,celt,rgelt,pceltFetched) ) 

#define IEnumHLITEM_Skip(This,celt)	\
    ( (This)->lpVtbl -> Skip(This,celt) ) 

#define IEnumHLITEM_Reset(This)	\
    ( (This)->lpVtbl -> Reset(This) ) 

#define IEnumHLITEM_Clone(This,ppienumhlitem)	\
    ( (This)->lpVtbl -> Clone(This,ppienumhlitem) ) 

#endif /* COBJMACROS */


#endif 	/* C style interface */




#endif 	/* __IEnumHLITEM_INTERFACE_DEFINED__ */


/* interface __MIDL_itf_HLink_0000_0005 */
/* [local] */ 

#endif
#ifndef _LPHLINKBROWSECONTEXT_DEFINED
#define _LPHLINKBROWSECONTEXT_DEFINED


extern RPC_IF_HANDLE __MIDL_itf_HLink_0000_0005_v0_0_c_ifspec;
extern RPC_IF_HANDLE __MIDL_itf_HLink_0000_0005_v0_0_s_ifspec;

#ifndef __IHlinkBrowseContext_INTERFACE_DEFINED__
#define __IHlinkBrowseContext_INTERFACE_DEFINED__

/* interface IHlinkBrowseContext */
/* [unique][uuid][object][local] */ 

typedef /* [unique] */ IHlinkBrowseContext *LPHLINKBROWSECONTEXT;


enum __MIDL_IHlinkBrowseContext_0001
    {
        HLTB_DOCKEDLEFT	= 0,
        HLTB_DOCKEDTOP	= 1,
        HLTB_DOCKEDRIGHT	= 2,
        HLTB_DOCKEDBOTTOM	= 3,
        HLTB_FLOATING	= 4
    } ;
typedef struct _tagHLTBINFO
    {
    ULONG uDockType;
    RECT rcTbPos;
    } 	HLTBINFO;


enum __MIDL_IHlinkBrowseContext_0002
    {
        HLBWIF_HASFRAMEWNDINFO	= 0x1,
        HLBWIF_HASDOCWNDINFO	= 0x2,
        HLBWIF_FRAMEWNDMAXIMIZED	= 0x4,
        HLBWIF_DOCWNDMAXIMIZED	= 0x8,
        HLBWIF_HASWEBTOOLBARINFO	= 0x10,
        HLBWIF_WEBTOOLBARHIDDEN	= 0x20
    } ;
typedef struct _tagHLBWINFO
    {
    ULONG cbSize;
    DWORD grfHLBWIF;
    RECT rcFramePos;
    RECT rcDocPos;
    HLTBINFO hltbinfo;
    } 	HLBWINFO;

typedef /* [unique] */ HLBWINFO *LPHLBWINFO;


enum __MIDL_IHlinkBrowseContext_0003
    {
        HLID_INVALID	= 0,
        HLID_PREVIOUS	= 0xffffffff,
        HLID_NEXT	= 0xfffffffe,
        HLID_CURRENT	= 0xfffffffd,
        HLID_STACKBOTTOM	= 0xfffffffc,
        HLID_STACKTOP	= 0xfffffffb
    } ;

enum __MIDL_IHlinkBrowseContext_0004
    {
        HLQF_ISVALID	= 0x1,
        HLQF_ISCURRENT	= 0x2
    } ;

EXTERN_C const IID IID_IHlinkBrowseContext;

#if defined(__cplusplus) && !defined(CINTERFACE)
    
    MIDL_INTERFACE("79eac9c7-baf9-11ce-8c82-00aa004ba90b")
    IHlinkBrowseContext : public IUnknown
    {
    public:
        virtual HRESULT STDMETHODCALLTYPE Register( 
            /* [in] */ DWORD reserved,
            /* [unique][in] */ IUnknown *piunk,
            /* [unique][in] */ IMoniker *pimk,
            /* [out] */ DWORD *pdwRegister) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE GetObject( 
            /* [unique][in] */ IMoniker *pimk,
            /* [in] */ BOOL fBindIfRootRegistered,
            /* [out] */ IUnknown **ppiunk) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE Revoke( 
            /* [in] */ DWORD dwRegister) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE SetBrowseWindowInfo( 
            /* [unique][in] */ HLBWINFO *phlbwi) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE GetBrowseWindowInfo( 
            /* [out] */ HLBWINFO *phlbwi) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE SetInitialHlink( 
            /* [unique][in] */ IMoniker *pimkTarget,
            /* [unique][in] */ LPCWSTR pwzLocation,
            /* [unique][in] */ LPCWSTR pwzFriendlyName) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE OnNavigateHlink( 
            /* [in] */ DWORD grfHLNF,
            /* [unique][in] */ IMoniker *pimkTarget,
            /* [unique][in] */ LPCWSTR pwzLocation,
            /* [unique][in] */ LPCWSTR pwzFriendlyName,
            /* [out] */ ULONG *puHLID) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE UpdateHlink( 
            /* [in] */ ULONG uHLID,
            /* [unique][in] */ IMoniker *pimkTarget,
            /* [unique][in] */ LPCWSTR pwzLocation,
            /* [unique][in] */ LPCWSTR pwzFriendlyName) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE EnumNavigationStack( 
            /* [in] */ DWORD dwReserved,
            /* [in] */ DWORD grfHLFNAMEF,
            /* [out] */ IEnumHLITEM **ppienumhlitem) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE QueryHlink( 
            /* [in] */ DWORD grfHLQF,
            /* [in] */ ULONG uHLID) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE GetHlink( 
            /* [in] */ ULONG uHLID,
            /* [out] */ IHlink **ppihl) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE SetCurrentHlink( 
            /* [in] */ ULONG uHLID) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE Clone( 
            /* [unique][in] */ IUnknown *piunkOuter,
            /* [in] */ REFIID riid,
            /* [iid_is][out] */ IUnknown **ppiunkObj) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE Close( 
            /* [in] */ DWORD reserved) = 0;
        
    };
    
    
#else 	/* C style interface */

    typedef struct IHlinkBrowseContextVtbl
    {
        BEGIN_INTERFACE
        
        HRESULT ( STDMETHODCALLTYPE *QueryInterface )( 
            IHlinkBrowseContext * This,
            /* [in] */ REFIID riid,
            /* [annotation][iid_is][out] */ 
            _COM_Outptr_  void **ppvObject);
        
        ULONG ( STDMETHODCALLTYPE *AddRef )( 
            IHlinkBrowseContext * This);
        
        ULONG ( STDMETHODCALLTYPE *Release )( 
            IHlinkBrowseContext * This);
        
        HRESULT ( STDMETHODCALLTYPE *Register )( 
            IHlinkBrowseContext * This,
            /* [in] */ DWORD reserved,
            /* [unique][in] */ IUnknown *piunk,
            /* [unique][in] */ IMoniker *pimk,
            /* [out] */ DWORD *pdwRegister);
        
        HRESULT ( STDMETHODCALLTYPE *GetObject )( 
            IHlinkBrowseContext * This,
            /* [unique][in] */ IMoniker *pimk,
            /* [in] */ BOOL fBindIfRootRegistered,
            /* [out] */ IUnknown **ppiunk);
        
        HRESULT ( STDMETHODCALLTYPE *Revoke )( 
            IHlinkBrowseContext * This,
            /* [in] */ DWORD dwRegister);
        
        HRESULT ( STDMETHODCALLTYPE *SetBrowseWindowInfo )( 
            IHlinkBrowseContext * This,
            /* [unique][in] */ HLBWINFO *phlbwi);
        
        HRESULT ( STDMETHODCALLTYPE *GetBrowseWindowInfo )( 
            IHlinkBrowseContext * This,
            /* [out] */ HLBWINFO *phlbwi);
        
        HRESULT ( STDMETHODCALLTYPE *SetInitialHlink )( 
            IHlinkBrowseContext * This,
            /* [unique][in] */ IMoniker *pimkTarget,
            /* [unique][in] */ LPCWSTR pwzLocation,
            /* [unique][in] */ LPCWSTR pwzFriendlyName);
        
        HRESULT ( STDMETHODCALLTYPE *OnNavigateHlink )( 
            IHlinkBrowseContext * This,
            /* [in] */ DWORD grfHLNF,
            /* [unique][in] */ IMoniker *pimkTarget,
            /* [unique][in] */ LPCWSTR pwzLocation,
            /* [unique][in] */ LPCWSTR pwzFriendlyName,
            /* [out] */ ULONG *puHLID);
        
        HRESULT ( STDMETHODCALLTYPE *UpdateHlink )( 
            IHlinkBrowseContext * This,
            /* [in] */ ULONG uHLID,
            /* [unique][in] */ IMoniker *pimkTarget,
            /* [unique][in] */ LPCWSTR pwzLocation,
            /* [unique][in] */ LPCWSTR pwzFriendlyName);
        
        HRESULT ( STDMETHODCALLTYPE *EnumNavigationStack )( 
            IHlinkBrowseContext * This,
            /* [in] */ DWORD dwReserved,
            /* [in] */ DWORD grfHLFNAMEF,
            /* [out] */ IEnumHLITEM **ppienumhlitem);
        
        HRESULT ( STDMETHODCALLTYPE *QueryHlink )( 
            IHlinkBrowseContext * This,
            /* [in] */ DWORD grfHLQF,
            /* [in] */ ULONG uHLID);
        
        HRESULT ( STDMETHODCALLTYPE *GetHlink )( 
            IHlinkBrowseContext * This,
            /* [in] */ ULONG uHLID,
            /* [out] */ IHlink **ppihl);
        
        HRESULT ( STDMETHODCALLTYPE *SetCurrentHlink )( 
            IHlinkBrowseContext * This,
            /* [in] */ ULONG uHLID);
        
        HRESULT ( STDMETHODCALLTYPE *Clone )( 
            IHlinkBrowseContext * This,
            /* [unique][in] */ IUnknown *piunkOuter,
            /* [in] */ REFIID riid,
            /* [iid_is][out] */ IUnknown **ppiunkObj);
        
        HRESULT ( STDMETHODCALLTYPE *Close )( 
            IHlinkBrowseContext * This,
            /* [in] */ DWORD reserved);
        
        END_INTERFACE
    } IHlinkBrowseContextVtbl;

    interface IHlinkBrowseContext
    {
        CONST_VTBL struct IHlinkBrowseContextVtbl *lpVtbl;
    };

    

#ifdef COBJMACROS


#define IHlinkBrowseContext_QueryInterface(This,riid,ppvObject)	\
    ( (This)->lpVtbl -> QueryInterface(This,riid,ppvObject) ) 

#define IHlinkBrowseContext_AddRef(This)	\
    ( (This)->lpVtbl -> AddRef(This) ) 

#define IHlinkBrowseContext_Release(This)	\
    ( (This)->lpVtbl -> Release(This) ) 


#define IHlinkBrowseContext_Register(This,reserved,piunk,pimk,pdwRegister)	\
    ( (This)->lpVtbl -> Register(This,reserved,piunk,pimk,pdwRegister) ) 

#define IHlinkBrowseContext_GetObject(This,pimk,fBindIfRootRegistered,ppiunk)	\
    ( (This)->lpVtbl -> GetObject(This,pimk,fBindIfRootRegistered,ppiunk) ) 

#define IHlinkBrowseContext_Revoke(This,dwRegister)	\
    ( (This)->lpVtbl -> Revoke(This,dwRegister) ) 

#define IHlinkBrowseContext_SetBrowseWindowInfo(This,phlbwi)	\
    ( (This)->lpVtbl -> SetBrowseWindowInfo(This,phlbwi) ) 

#define IHlinkBrowseContext_GetBrowseWindowInfo(This,phlbwi)	\
    ( (This)->lpVtbl -> GetBrowseWindowInfo(This,phlbwi) ) 

#define IHlinkBrowseContext_SetInitialHlink(This,pimkTarget,pwzLocation,pwzFriendlyName)	\
    ( (This)->lpVtbl -> SetInitialHlink(This,pimkTarget,pwzLocation,pwzFriendlyName) ) 

#define IHlinkBrowseContext_OnNavigateHlink(This,grfHLNF,pimkTarget,pwzLocation,pwzFriendlyName,puHLID)	\
    ( (This)->lpVtbl -> OnNavigateHlink(This,grfHLNF,pimkTarget,pwzLocation,pwzFriendlyName,puHLID) ) 

#define IHlinkBrowseContext_UpdateHlink(This,uHLID,pimkTarget,pwzLocation,pwzFriendlyName)	\
    ( (This)->lpVtbl -> UpdateHlink(This,uHLID,pimkTarget,pwzLocation,pwzFriendlyName) ) 

#define IHlinkBrowseContext_EnumNavigationStack(This,dwReserved,grfHLFNAMEF,ppienumhlitem)	\
    ( (This)->lpVtbl -> EnumNavigationStack(This,dwReserved,grfHLFNAMEF,ppienumhlitem) ) 

#define IHlinkBrowseContext_QueryHlink(This,grfHLQF,uHLID)	\
    ( (This)->lpVtbl -> QueryHlink(This,grfHLQF,uHLID) ) 

#define IHlinkBrowseContext_GetHlink(This,uHLID,ppihl)	\
    ( (This)->lpVtbl -> GetHlink(This,uHLID,ppihl) ) 

#define IHlinkBrowseContext_SetCurrentHlink(This,uHLID)	\
    ( (This)->lpVtbl -> SetCurrentHlink(This,uHLID) ) 

#define IHlinkBrowseContext_Clone(This,piunkOuter,riid,ppiunkObj)	\
    ( (This)->lpVtbl -> Clone(This,piunkOuter,riid,ppiunkObj) ) 

#define IHlinkBrowseContext_Close(This,reserved)	\
    ( (This)->lpVtbl -> Close(This,reserved) ) 

#endif /* COBJMACROS */


#endif 	/* C style interface */




#endif 	/* __IHlinkBrowseContext_INTERFACE_DEFINED__ */


/* interface __MIDL_itf_HLink_0000_0006 */
/* [local] */ 

#endif
#ifndef _LPEXTENSIONSERVICES_DEFINED
#define _LPEXTENSIONSERVICES_DEFINED


extern RPC_IF_HANDLE __MIDL_itf_HLink_0000_0006_v0_0_c_ifspec;
extern RPC_IF_HANDLE __MIDL_itf_HLink_0000_0006_v0_0_s_ifspec;

#ifndef __IExtensionServices_INTERFACE_DEFINED__
#define __IExtensionServices_INTERFACE_DEFINED__

/* interface IExtensionServices */
/* [unique][uuid][object][local] */ 

typedef /* [unique] */ IExtensionServices *LPEXTENSIONSERVICES;


EXTERN_C const IID IID_IExtensionServices;

#if defined(__cplusplus) && !defined(CINTERFACE)
    
    MIDL_INTERFACE("79eac9cb-baf9-11ce-8c82-00aa004ba90b")
    IExtensionServices : public IUnknown
    {
    public:
        virtual HRESULT STDMETHODCALLTYPE SetAdditionalHeaders( 
            /* [in] */ LPCWSTR pwzAdditionalHeaders) = 0;
        
        virtual HRESULT STDMETHODCALLTYPE SetAuthenticateData( 
            /* [in] */ HWND phwnd,
            /* [in] */ LPCWSTR pwzUsername,
            /* [in] */ LPCWSTR pwzPassword) = 0;
        
    };
    
    
#else 	/* C style interface */

    typedef struct IExtensionServicesVtbl
    {
        BEGIN_INTERFACE
        
        HRESULT ( STDMETHODCALLTYPE *QueryInterface )( 
            IExtensionServices * This,
            /* [in] */ REFIID riid,
            /* [annotation][iid_is][out] */ 
            _COM_Outptr_  void **ppvObject);
        
        ULONG ( STDMETHODCALLTYPE *AddRef )( 
            IExtensionServices * This);
        
        ULONG ( STDMETHODCALLTYPE *Release )( 
            IExtensionServices * This);
        
        HRESULT ( STDMETHODCALLTYPE *SetAdditionalHeaders )( 
            IExtensionServices * This,
            /* [in] */ LPCWSTR pwzAdditionalHeaders);
        
        HRESULT ( STDMETHODCALLTYPE *SetAuthenticateData )( 
            IExtensionServices * This,
            /* [in] */ HWND phwnd,
            /* [in] */ LPCWSTR pwzUsername,
            /* [in] */ LPCWSTR pwzPassword);
        
        END_INTERFACE
    } IExtensionServicesVtbl;

    interface IExtensionServices
    {
        CONST_VTBL struct IExtensionServicesVtbl *lpVtbl;
    };

    

#ifdef COBJMACROS


#define IExtensionServices_QueryInterface(This,riid,ppvObject)	\
    ( (This)->lpVtbl -> QueryInterface(This,riid,ppvObject) ) 

#define IExtensionServices_AddRef(This)	\
    ( (This)->lpVtbl -> AddRef(This) ) 

#define IExtensionServices_Release(This)	\
    ( (This)->lpVtbl -> Release(This) ) 


#define IExtensionServices_SetAdditionalHeaders(This,pwzAdditionalHeaders)	\
    ( (This)->lpVtbl -> SetAdditionalHeaders(This,pwzAdditionalHeaders) ) 

#define IExtensionServices_SetAuthenticateData(This,phwnd,pwzUsername,pwzPassword)	\
    ( (This)->lpVtbl -> SetAuthenticateData(This,phwnd,pwzUsername,pwzPassword) ) 

#endif /* COBJMACROS */


#endif 	/* C style interface */




#endif 	/* __IExtensionServices_INTERFACE_DEFINED__ */


/* interface __MIDL_itf_HLink_0000_0007 */
/* [local] */ 

#endif
                                                                              
#endif // !HLINK_H                                                            
#endif /* WINAPI_FAMILY_PARTITION(WINAPI_PARTITION_DESKTOP) */
#pragma endregion


extern RPC_IF_HANDLE __MIDL_itf_HLink_0000_0007_v0_0_c_ifspec;
extern RPC_IF_HANDLE __MIDL_itf_HLink_0000_0007_v0_0_s_ifspec;

/* Additional Prototypes for ALL interfaces */

/* [local] */ HRESULT STDMETHODCALLTYPE IHlink_GetMonikerReference_Proxy( 
    IHlink * This,
    /* [in] */ DWORD dwWhichRef,
    /* [annotation][out] */ 
    _Outptr_opt_result_maybenull_  IMoniker **ppimkTarget,
    /* [annotation][out] */ 
    _Outptr_opt_result_maybenull_  LPWSTR *ppwzLocation);


/* [call_as] */ HRESULT STDMETHODCALLTYPE IHlink_GetMonikerReference_Stub( 
    IHlink * This,
    /* [in] */ DWORD dwWhichRef,
    /* [out] */ IMoniker **ppimkTarget,
    /* [out] */ LPWSTR *ppwzLocation);

/* [local] */ HRESULT STDMETHODCALLTYPE IHlink_GetStringReference_Proxy( 
    IHlink * This,
    /* [in] */ DWORD dwWhichRef,
    /* [annotation][out] */ 
    _Outptr_opt_  LPWSTR *ppwzTarget,
    /* [annotation][out] */ 
    _Outptr_opt_result_maybenull_  LPWSTR *ppwzLocation);


/* [call_as] */ HRESULT STDMETHODCALLTYPE IHlink_GetStringReference_Stub( 
    IHlink * This,
    /* [in] */ DWORD dwWhichRef,
    /* [out] */ LPWSTR *ppwzTarget,
    /* [out] */ LPWSTR *ppwzLocation);



/* end of Additional Prototypes */

#ifdef __cplusplus
}
#endif

#endif


