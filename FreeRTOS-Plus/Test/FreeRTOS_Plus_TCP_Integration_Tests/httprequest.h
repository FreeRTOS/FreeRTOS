

/* this ALWAYS GENERATED file contains the definitions for the interfaces */


 /* File created by MIDL compiler version 8.01.0622 */
/* at Mon Jan 18 19:14:07 2038
 */
/* Compiler settings for ..\..\..\..\..\..\..\..\Program Files (x86)\Windows Kits\10\Include\10.0.18362.0\um\httprequest.idl:
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


#ifndef __httprequest_h__
#define __httprequest_h__

#if defined(_MSC_VER) && (_MSC_VER >= 1020)
#pragma once
#endif

/* Forward Declarations */ 

#ifndef __IWinHttpRequest_FWD_DEFINED__
#define __IWinHttpRequest_FWD_DEFINED__
typedef interface IWinHttpRequest IWinHttpRequest;

#endif 	/* __IWinHttpRequest_FWD_DEFINED__ */


#ifndef __IWinHttpRequestEvents_FWD_DEFINED__
#define __IWinHttpRequestEvents_FWD_DEFINED__
typedef interface IWinHttpRequestEvents IWinHttpRequestEvents;

#endif 	/* __IWinHttpRequestEvents_FWD_DEFINED__ */


#ifndef __WinHttpRequest_FWD_DEFINED__
#define __WinHttpRequest_FWD_DEFINED__

#ifdef __cplusplus
typedef class WinHttpRequest WinHttpRequest;
#else
typedef struct WinHttpRequest WinHttpRequest;
#endif /* __cplusplus */

#endif 	/* __WinHttpRequest_FWD_DEFINED__ */


#ifdef __cplusplus
extern "C"{
#endif 


/* interface __MIDL_itf_httprequest_0000_0000 */
/* [local] */ 

//+-------------------------------------------------------------------------
//
//  Microsoft Windows HTTP Services (WinHTTP) version 5.1
//  Copyright (C) Microsoft Corporation. All rights reserved.
//
//--------------------------------------------------------------------------
#include <winapifamily.h>
#pragma region Desktop Family or OneCore Family
#if WINAPI_FAMILY_PARTITION(WINAPI_PARTITION_DESKTOP | WINAPI_PARTITION_SYSTEM)
#pragma warning(push)
#pragma warning(disable:4001) 
#pragma once
#pragma warning(push)
#pragma warning(disable:4001) 
#pragma once
#pragma warning(pop)
#pragma warning(pop)
#pragma region Desktop Family or OneCore Family
#pragma endregion


extern RPC_IF_HANDLE __MIDL_itf_httprequest_0000_0000_v0_0_c_ifspec;
extern RPC_IF_HANDLE __MIDL_itf_httprequest_0000_0000_v0_0_s_ifspec;


#ifndef __WinHttp_LIBRARY_DEFINED__
#define __WinHttp_LIBRARY_DEFINED__

/* library WinHttp */
/* [version][lcid][helpstring][uuid] */ 

typedef /* [public] */ long HTTPREQUEST_PROXY_SETTING;

#define	HTTPREQUEST_PROXYSETTING_DEFAULT	( 0 )

#define	HTTPREQUEST_PROXYSETTING_PRECONFIG	( 0 )

#define	HTTPREQUEST_PROXYSETTING_DIRECT	( 0x1 )

#define	HTTPREQUEST_PROXYSETTING_PROXY	( 0x2 )

typedef /* [public] */ long HTTPREQUEST_SETCREDENTIALS_FLAGS;

#define	HTTPREQUEST_SETCREDENTIALS_FOR_SERVER	( 0 )

#define	HTTPREQUEST_SETCREDENTIALS_FOR_PROXY	( 0x1 )

typedef /* [helpstring][uuid] */  DECLSPEC_UUID("12782009-FE90-4877-9730-E5E183669B19") 
enum WinHttpRequestOption
    {
        WinHttpRequestOption_UserAgentString	= 0,
        WinHttpRequestOption_URL	= ( WinHttpRequestOption_UserAgentString + 1 ) ,
        WinHttpRequestOption_URLCodePage	= ( WinHttpRequestOption_URL + 1 ) ,
        WinHttpRequestOption_EscapePercentInURL	= ( WinHttpRequestOption_URLCodePage + 1 ) ,
        WinHttpRequestOption_SslErrorIgnoreFlags	= ( WinHttpRequestOption_EscapePercentInURL + 1 ) ,
        WinHttpRequestOption_SelectCertificate	= ( WinHttpRequestOption_SslErrorIgnoreFlags + 1 ) ,
        WinHttpRequestOption_EnableRedirects	= ( WinHttpRequestOption_SelectCertificate + 1 ) ,
        WinHttpRequestOption_UrlEscapeDisable	= ( WinHttpRequestOption_EnableRedirects + 1 ) ,
        WinHttpRequestOption_UrlEscapeDisableQuery	= ( WinHttpRequestOption_UrlEscapeDisable + 1 ) ,
        WinHttpRequestOption_SecureProtocols	= ( WinHttpRequestOption_UrlEscapeDisableQuery + 1 ) ,
        WinHttpRequestOption_EnableTracing	= ( WinHttpRequestOption_SecureProtocols + 1 ) ,
        WinHttpRequestOption_RevertImpersonationOverSsl	= ( WinHttpRequestOption_EnableTracing + 1 ) ,
        WinHttpRequestOption_EnableHttpsToHttpRedirects	= ( WinHttpRequestOption_RevertImpersonationOverSsl + 1 ) ,
        WinHttpRequestOption_EnablePassportAuthentication	= ( WinHttpRequestOption_EnableHttpsToHttpRedirects + 1 ) ,
        WinHttpRequestOption_MaxAutomaticRedirects	= ( WinHttpRequestOption_EnablePassportAuthentication + 1 ) ,
        WinHttpRequestOption_MaxResponseHeaderSize	= ( WinHttpRequestOption_MaxAutomaticRedirects + 1 ) ,
        WinHttpRequestOption_MaxResponseDrainSize	= ( WinHttpRequestOption_MaxResponseHeaderSize + 1 ) ,
        WinHttpRequestOption_EnableHttp1_1	= ( WinHttpRequestOption_MaxResponseDrainSize + 1 ) ,
        WinHttpRequestOption_EnableCertificateRevocationCheck	= ( WinHttpRequestOption_EnableHttp1_1 + 1 ) ,
        WinHttpRequestOption_RejectUserpwd	= ( WinHttpRequestOption_EnableCertificateRevocationCheck + 1 ) 
    } 	WinHttpRequestOption;

typedef /* [uuid] */  DECLSPEC_UUID("9d8a6df8-13de-4b1f-a330-67c719d62514") 
enum WinHttpRequestAutoLogonPolicy
    {
        AutoLogonPolicy_Always	= 0,
        AutoLogonPolicy_OnlyIfBypassProxy	= ( AutoLogonPolicy_Always + 1 ) ,
        AutoLogonPolicy_Never	= ( AutoLogonPolicy_OnlyIfBypassProxy + 1 ) 
    } 	WinHttpRequestAutoLogonPolicy;

typedef /* [uuid] */  DECLSPEC_UUID("152a1ca2-55a9-43a3-b187-0605bb886349") 
enum WinHttpRequestSslErrorFlags
    {
        SslErrorFlag_UnknownCA	= 0x100,
        SslErrorFlag_CertWrongUsage	= 0x200,
        SslErrorFlag_CertCNInvalid	= 0x1000,
        SslErrorFlag_CertDateInvalid	= 0x2000,
        SslErrorFlag_Ignore_All	= 0x3300
    } 	WinHttpRequestSslErrorFlags;

typedef /* [uuid] */  DECLSPEC_UUID("6b2c51c1-a8ea-46bd-b928-c9b76f9f14dd") 
enum WinHttpRequestSecureProtocols
    {
        SecureProtocol_SSL2	= 0x8,
        SecureProtocol_SSL3	= 0x20,
        SecureProtocol_TLS1	= 0x80,
        SecureProtocol_TLS1_1	= 0x200,
        SecureProtocol_TLS1_2	= 0x800,
        SecureProtocol_ALL	= 0xa8
    } 	WinHttpRequestSecureProtocols;


EXTERN_C const IID LIBID_WinHttp;

#ifndef __IWinHttpRequest_INTERFACE_DEFINED__
#define __IWinHttpRequest_INTERFACE_DEFINED__

/* interface IWinHttpRequest */
/* [unique][helpstring][nonextensible][oleautomation][dual][uuid][object] */ 


EXTERN_C const IID IID_IWinHttpRequest;

#if defined(__cplusplus) && !defined(CINTERFACE)
    
    MIDL_INTERFACE("016fe2ec-b2c8-45f8-b23b-39e53a75396b")
    IWinHttpRequest : public IDispatch
    {
    public:
        virtual /* [helpstring][id] */ HRESULT STDMETHODCALLTYPE SetProxy( 
            /* [in] */ HTTPREQUEST_PROXY_SETTING ProxySetting,
            /* [optional][in] */ VARIANT ProxyServer,
            /* [optional][in] */ VARIANT BypassList) = 0;
        
        virtual /* [helpstring][id] */ HRESULT STDMETHODCALLTYPE SetCredentials( 
            /* [in] */ BSTR UserName,
            /* [in] */ BSTR Password,
            /* [in] */ HTTPREQUEST_SETCREDENTIALS_FLAGS Flags) = 0;
        
        virtual /* [helpstring][id] */ HRESULT STDMETHODCALLTYPE Open( 
            /* [in] */ BSTR Method,
            /* [in] */ BSTR Url,
            /* [optional][in] */ VARIANT Async) = 0;
        
        virtual /* [helpstring][id] */ HRESULT STDMETHODCALLTYPE SetRequestHeader( 
            /* [in] */ BSTR Header,
            /* [in] */ BSTR Value) = 0;
        
        virtual /* [helpstring][id] */ HRESULT STDMETHODCALLTYPE GetResponseHeader( 
            /* [in] */ BSTR Header,
            /* [retval][out] */ BSTR *Value) = 0;
        
        virtual /* [helpstring][id] */ HRESULT STDMETHODCALLTYPE GetAllResponseHeaders( 
            /* [retval][out] */ BSTR *Headers) = 0;
        
        virtual /* [helpstring][id] */ HRESULT STDMETHODCALLTYPE Send( 
            /* [optional][in] */ VARIANT Body) = 0;
        
        virtual /* [helpstring][id][propget] */ HRESULT STDMETHODCALLTYPE get_Status( 
            /* [retval][out] */ long *Status) = 0;
        
        virtual /* [helpstring][id][propget] */ HRESULT STDMETHODCALLTYPE get_StatusText( 
            /* [retval][out] */ BSTR *Status) = 0;
        
        virtual /* [helpstring][id][propget] */ HRESULT STDMETHODCALLTYPE get_ResponseText( 
            /* [retval][out] */ BSTR *Body) = 0;
        
        virtual /* [helpstring][id][propget] */ HRESULT STDMETHODCALLTYPE get_ResponseBody( 
            /* [retval][out] */ VARIANT *Body) = 0;
        
        virtual /* [helpstring][id][propget] */ HRESULT STDMETHODCALLTYPE get_ResponseStream( 
            /* [retval][out] */ VARIANT *Body) = 0;
        
        virtual /* [id][propget] */ HRESULT STDMETHODCALLTYPE get_Option( 
            /* [in] */ WinHttpRequestOption Option,
            /* [retval][out] */ VARIANT *Value) = 0;
        
        virtual /* [id][propput] */ HRESULT STDMETHODCALLTYPE put_Option( 
            /* [in] */ WinHttpRequestOption Option,
            /* [in] */ VARIANT Value) = 0;
        
        virtual /* [helpstring][id] */ HRESULT STDMETHODCALLTYPE WaitForResponse( 
            /* [optional][in] */ VARIANT Timeout,
            /* [retval][out] */ VARIANT_BOOL *Succeeded) = 0;
        
        virtual /* [helpstring][id] */ HRESULT STDMETHODCALLTYPE Abort( void) = 0;
        
        virtual /* [helpstring][id] */ HRESULT STDMETHODCALLTYPE SetTimeouts( 
            /* [in] */ long ResolveTimeout,
            /* [in] */ long ConnectTimeout,
            /* [in] */ long SendTimeout,
            /* [in] */ long ReceiveTimeout) = 0;
        
        virtual /* [helpstring][id] */ HRESULT STDMETHODCALLTYPE SetClientCertificate( 
            /* [in] */ BSTR ClientCertificate) = 0;
        
        virtual /* [helpstring][id] */ HRESULT STDMETHODCALLTYPE SetAutoLogonPolicy( 
            /* [in] */ WinHttpRequestAutoLogonPolicy AutoLogonPolicy) = 0;
        
    };
    
    
#else 	/* C style interface */

    typedef struct IWinHttpRequestVtbl
    {
        BEGIN_INTERFACE
        
        HRESULT ( STDMETHODCALLTYPE *QueryInterface )( 
            IWinHttpRequest * This,
            /* [in] */ REFIID riid,
            /* [annotation][iid_is][out] */ 
            _COM_Outptr_  void **ppvObject);
        
        ULONG ( STDMETHODCALLTYPE *AddRef )( 
            IWinHttpRequest * This);
        
        ULONG ( STDMETHODCALLTYPE *Release )( 
            IWinHttpRequest * This);
        
        HRESULT ( STDMETHODCALLTYPE *GetTypeInfoCount )( 
            IWinHttpRequest * This,
            /* [out] */ UINT *pctinfo);
        
        HRESULT ( STDMETHODCALLTYPE *GetTypeInfo )( 
            IWinHttpRequest * This,
            /* [in] */ UINT iTInfo,
            /* [in] */ LCID lcid,
            /* [out] */ ITypeInfo **ppTInfo);
        
        HRESULT ( STDMETHODCALLTYPE *GetIDsOfNames )( 
            IWinHttpRequest * This,
            /* [in] */ REFIID riid,
            /* [size_is][in] */ LPOLESTR *rgszNames,
            /* [range][in] */ UINT cNames,
            /* [in] */ LCID lcid,
            /* [size_is][out] */ DISPID *rgDispId);
        
        /* [local] */ HRESULT ( STDMETHODCALLTYPE *Invoke )( 
            IWinHttpRequest * This,
            /* [annotation][in] */ 
            _In_  DISPID dispIdMember,
            /* [annotation][in] */ 
            _In_  REFIID riid,
            /* [annotation][in] */ 
            _In_  LCID lcid,
            /* [annotation][in] */ 
            _In_  WORD wFlags,
            /* [annotation][out][in] */ 
            _In_  DISPPARAMS *pDispParams,
            /* [annotation][out] */ 
            _Out_opt_  VARIANT *pVarResult,
            /* [annotation][out] */ 
            _Out_opt_  EXCEPINFO *pExcepInfo,
            /* [annotation][out] */ 
            _Out_opt_  UINT *puArgErr);
        
        /* [helpstring][id] */ HRESULT ( STDMETHODCALLTYPE *SetProxy )( 
            IWinHttpRequest * This,
            /* [in] */ HTTPREQUEST_PROXY_SETTING ProxySetting,
            /* [optional][in] */ VARIANT ProxyServer,
            /* [optional][in] */ VARIANT BypassList);
        
        /* [helpstring][id] */ HRESULT ( STDMETHODCALLTYPE *SetCredentials )( 
            IWinHttpRequest * This,
            /* [in] */ BSTR UserName,
            /* [in] */ BSTR Password,
            /* [in] */ HTTPREQUEST_SETCREDENTIALS_FLAGS Flags);
        
        /* [helpstring][id] */ HRESULT ( STDMETHODCALLTYPE *Open )( 
            IWinHttpRequest * This,
            /* [in] */ BSTR Method,
            /* [in] */ BSTR Url,
            /* [optional][in] */ VARIANT Async);
        
        /* [helpstring][id] */ HRESULT ( STDMETHODCALLTYPE *SetRequestHeader )( 
            IWinHttpRequest * This,
            /* [in] */ BSTR Header,
            /* [in] */ BSTR Value);
        
        /* [helpstring][id] */ HRESULT ( STDMETHODCALLTYPE *GetResponseHeader )( 
            IWinHttpRequest * This,
            /* [in] */ BSTR Header,
            /* [retval][out] */ BSTR *Value);
        
        /* [helpstring][id] */ HRESULT ( STDMETHODCALLTYPE *GetAllResponseHeaders )( 
            IWinHttpRequest * This,
            /* [retval][out] */ BSTR *Headers);
        
        /* [helpstring][id] */ HRESULT ( STDMETHODCALLTYPE *Send )( 
            IWinHttpRequest * This,
            /* [optional][in] */ VARIANT Body);
        
        /* [helpstring][id][propget] */ HRESULT ( STDMETHODCALLTYPE *get_Status )( 
            IWinHttpRequest * This,
            /* [retval][out] */ long *Status);
        
        /* [helpstring][id][propget] */ HRESULT ( STDMETHODCALLTYPE *get_StatusText )( 
            IWinHttpRequest * This,
            /* [retval][out] */ BSTR *Status);
        
        /* [helpstring][id][propget] */ HRESULT ( STDMETHODCALLTYPE *get_ResponseText )( 
            IWinHttpRequest * This,
            /* [retval][out] */ BSTR *Body);
        
        /* [helpstring][id][propget] */ HRESULT ( STDMETHODCALLTYPE *get_ResponseBody )( 
            IWinHttpRequest * This,
            /* [retval][out] */ VARIANT *Body);
        
        /* [helpstring][id][propget] */ HRESULT ( STDMETHODCALLTYPE *get_ResponseStream )( 
            IWinHttpRequest * This,
            /* [retval][out] */ VARIANT *Body);
        
        /* [id][propget] */ HRESULT ( STDMETHODCALLTYPE *get_Option )( 
            IWinHttpRequest * This,
            /* [in] */ WinHttpRequestOption Option,
            /* [retval][out] */ VARIANT *Value);
        
        /* [id][propput] */ HRESULT ( STDMETHODCALLTYPE *put_Option )( 
            IWinHttpRequest * This,
            /* [in] */ WinHttpRequestOption Option,
            /* [in] */ VARIANT Value);
        
        /* [helpstring][id] */ HRESULT ( STDMETHODCALLTYPE *WaitForResponse )( 
            IWinHttpRequest * This,
            /* [optional][in] */ VARIANT Timeout,
            /* [retval][out] */ VARIANT_BOOL *Succeeded);
        
        /* [helpstring][id] */ HRESULT ( STDMETHODCALLTYPE *Abort )( 
            IWinHttpRequest * This);
        
        /* [helpstring][id] */ HRESULT ( STDMETHODCALLTYPE *SetTimeouts )( 
            IWinHttpRequest * This,
            /* [in] */ long ResolveTimeout,
            /* [in] */ long ConnectTimeout,
            /* [in] */ long SendTimeout,
            /* [in] */ long ReceiveTimeout);
        
        /* [helpstring][id] */ HRESULT ( STDMETHODCALLTYPE *SetClientCertificate )( 
            IWinHttpRequest * This,
            /* [in] */ BSTR ClientCertificate);
        
        /* [helpstring][id] */ HRESULT ( STDMETHODCALLTYPE *SetAutoLogonPolicy )( 
            IWinHttpRequest * This,
            /* [in] */ WinHttpRequestAutoLogonPolicy AutoLogonPolicy);
        
        END_INTERFACE
    } IWinHttpRequestVtbl;

    interface IWinHttpRequest
    {
        CONST_VTBL struct IWinHttpRequestVtbl *lpVtbl;
    };

    

#ifdef COBJMACROS


#define IWinHttpRequest_QueryInterface(This,riid,ppvObject)	\
    ( (This)->lpVtbl -> QueryInterface(This,riid,ppvObject) ) 

#define IWinHttpRequest_AddRef(This)	\
    ( (This)->lpVtbl -> AddRef(This) ) 

#define IWinHttpRequest_Release(This)	\
    ( (This)->lpVtbl -> Release(This) ) 


#define IWinHttpRequest_GetTypeInfoCount(This,pctinfo)	\
    ( (This)->lpVtbl -> GetTypeInfoCount(This,pctinfo) ) 

#define IWinHttpRequest_GetTypeInfo(This,iTInfo,lcid,ppTInfo)	\
    ( (This)->lpVtbl -> GetTypeInfo(This,iTInfo,lcid,ppTInfo) ) 

#define IWinHttpRequest_GetIDsOfNames(This,riid,rgszNames,cNames,lcid,rgDispId)	\
    ( (This)->lpVtbl -> GetIDsOfNames(This,riid,rgszNames,cNames,lcid,rgDispId) ) 

#define IWinHttpRequest_Invoke(This,dispIdMember,riid,lcid,wFlags,pDispParams,pVarResult,pExcepInfo,puArgErr)	\
    ( (This)->lpVtbl -> Invoke(This,dispIdMember,riid,lcid,wFlags,pDispParams,pVarResult,pExcepInfo,puArgErr) ) 


#define IWinHttpRequest_SetProxy(This,ProxySetting,ProxyServer,BypassList)	\
    ( (This)->lpVtbl -> SetProxy(This,ProxySetting,ProxyServer,BypassList) ) 

#define IWinHttpRequest_SetCredentials(This,UserName,Password,Flags)	\
    ( (This)->lpVtbl -> SetCredentials(This,UserName,Password,Flags) ) 

#define IWinHttpRequest_Open(This,Method,Url,Async)	\
    ( (This)->lpVtbl -> Open(This,Method,Url,Async) ) 

#define IWinHttpRequest_SetRequestHeader(This,Header,Value)	\
    ( (This)->lpVtbl -> SetRequestHeader(This,Header,Value) ) 

#define IWinHttpRequest_GetResponseHeader(This,Header,Value)	\
    ( (This)->lpVtbl -> GetResponseHeader(This,Header,Value) ) 

#define IWinHttpRequest_GetAllResponseHeaders(This,Headers)	\
    ( (This)->lpVtbl -> GetAllResponseHeaders(This,Headers) ) 

#define IWinHttpRequest_Send(This,Body)	\
    ( (This)->lpVtbl -> Send(This,Body) ) 

#define IWinHttpRequest_get_Status(This,Status)	\
    ( (This)->lpVtbl -> get_Status(This,Status) ) 

#define IWinHttpRequest_get_StatusText(This,Status)	\
    ( (This)->lpVtbl -> get_StatusText(This,Status) ) 

#define IWinHttpRequest_get_ResponseText(This,Body)	\
    ( (This)->lpVtbl -> get_ResponseText(This,Body) ) 

#define IWinHttpRequest_get_ResponseBody(This,Body)	\
    ( (This)->lpVtbl -> get_ResponseBody(This,Body) ) 

#define IWinHttpRequest_get_ResponseStream(This,Body)	\
    ( (This)->lpVtbl -> get_ResponseStream(This,Body) ) 

#define IWinHttpRequest_get_Option(This,Option,Value)	\
    ( (This)->lpVtbl -> get_Option(This,Option,Value) ) 

#define IWinHttpRequest_put_Option(This,Option,Value)	\
    ( (This)->lpVtbl -> put_Option(This,Option,Value) ) 

#define IWinHttpRequest_WaitForResponse(This,Timeout,Succeeded)	\
    ( (This)->lpVtbl -> WaitForResponse(This,Timeout,Succeeded) ) 

#define IWinHttpRequest_Abort(This)	\
    ( (This)->lpVtbl -> Abort(This) ) 

#define IWinHttpRequest_SetTimeouts(This,ResolveTimeout,ConnectTimeout,SendTimeout,ReceiveTimeout)	\
    ( (This)->lpVtbl -> SetTimeouts(This,ResolveTimeout,ConnectTimeout,SendTimeout,ReceiveTimeout) ) 

#define IWinHttpRequest_SetClientCertificate(This,ClientCertificate)	\
    ( (This)->lpVtbl -> SetClientCertificate(This,ClientCertificate) ) 

#define IWinHttpRequest_SetAutoLogonPolicy(This,AutoLogonPolicy)	\
    ( (This)->lpVtbl -> SetAutoLogonPolicy(This,AutoLogonPolicy) ) 

#endif /* COBJMACROS */


#endif 	/* C style interface */




#endif 	/* __IWinHttpRequest_INTERFACE_DEFINED__ */


#ifndef __IWinHttpRequestEvents_INTERFACE_DEFINED__
#define __IWinHttpRequestEvents_INTERFACE_DEFINED__

/* interface IWinHttpRequestEvents */
/* [unique][helpstring][nonextensible][oleautomation][uuid][object] */ 


EXTERN_C const IID IID_IWinHttpRequestEvents;

#if defined(__cplusplus) && !defined(CINTERFACE)
    
    MIDL_INTERFACE("f97f4e15-b787-4212-80d1-d380cbbf982e")
    IWinHttpRequestEvents : public IUnknown
    {
    public:
        virtual void STDMETHODCALLTYPE OnResponseStart( 
            /* [in] */ long Status,
            /* [in] */ BSTR ContentType) = 0;
        
        virtual void STDMETHODCALLTYPE OnResponseDataAvailable( 
            /* [in] */ SAFEARRAY * *Data) = 0;
        
        virtual void STDMETHODCALLTYPE OnResponseFinished( void) = 0;
        
        virtual void STDMETHODCALLTYPE OnError( 
            /* [in] */ long ErrorNumber,
            /* [in] */ BSTR ErrorDescription) = 0;
        
    };
    
    
#else 	/* C style interface */

    typedef struct IWinHttpRequestEventsVtbl
    {
        BEGIN_INTERFACE
        
        HRESULT ( STDMETHODCALLTYPE *QueryInterface )( 
            IWinHttpRequestEvents * This,
            /* [in] */ REFIID riid,
            /* [annotation][iid_is][out] */ 
            _COM_Outptr_  void **ppvObject);
        
        ULONG ( STDMETHODCALLTYPE *AddRef )( 
            IWinHttpRequestEvents * This);
        
        ULONG ( STDMETHODCALLTYPE *Release )( 
            IWinHttpRequestEvents * This);
        
        void ( STDMETHODCALLTYPE *OnResponseStart )( 
            IWinHttpRequestEvents * This,
            /* [in] */ long Status,
            /* [in] */ BSTR ContentType);
        
        void ( STDMETHODCALLTYPE *OnResponseDataAvailable )( 
            IWinHttpRequestEvents * This,
            /* [in] */ SAFEARRAY * *Data);
        
        void ( STDMETHODCALLTYPE *OnResponseFinished )( 
            IWinHttpRequestEvents * This);
        
        void ( STDMETHODCALLTYPE *OnError )( 
            IWinHttpRequestEvents * This,
            /* [in] */ long ErrorNumber,
            /* [in] */ BSTR ErrorDescription);
        
        END_INTERFACE
    } IWinHttpRequestEventsVtbl;

    interface IWinHttpRequestEvents
    {
        CONST_VTBL struct IWinHttpRequestEventsVtbl *lpVtbl;
    };

    

#ifdef COBJMACROS


#define IWinHttpRequestEvents_QueryInterface(This,riid,ppvObject)	\
    ( (This)->lpVtbl -> QueryInterface(This,riid,ppvObject) ) 

#define IWinHttpRequestEvents_AddRef(This)	\
    ( (This)->lpVtbl -> AddRef(This) ) 

#define IWinHttpRequestEvents_Release(This)	\
    ( (This)->lpVtbl -> Release(This) ) 


#define IWinHttpRequestEvents_OnResponseStart(This,Status,ContentType)	\
    ( (This)->lpVtbl -> OnResponseStart(This,Status,ContentType) ) 

#define IWinHttpRequestEvents_OnResponseDataAvailable(This,Data)	\
    ( (This)->lpVtbl -> OnResponseDataAvailable(This,Data) ) 

#define IWinHttpRequestEvents_OnResponseFinished(This)	\
    ( (This)->lpVtbl -> OnResponseFinished(This) ) 

#define IWinHttpRequestEvents_OnError(This,ErrorNumber,ErrorDescription)	\
    ( (This)->lpVtbl -> OnError(This,ErrorNumber,ErrorDescription) ) 

#endif /* COBJMACROS */


#endif 	/* C style interface */




#endif 	/* __IWinHttpRequestEvents_INTERFACE_DEFINED__ */


EXTERN_C const CLSID CLSID_WinHttpRequest;

#ifdef __cplusplus

class DECLSPEC_UUID("2087c2f4-2cef-4953-a8ab-66779b670495")
WinHttpRequest;
#endif
#endif /* __WinHttp_LIBRARY_DEFINED__ */

/* interface __MIDL_itf_httprequest_0000_0001 */
/* [local] */ 

#endif /* WINAPI_FAMILY_PARTITION(WINAPI_PARTITION_DESKTOP | WINAPI_PARTITION_SYSTEM) */
#pragma endregion


extern RPC_IF_HANDLE __MIDL_itf_httprequest_0000_0001_v0_0_c_ifspec;
extern RPC_IF_HANDLE __MIDL_itf_httprequest_0000_0001_v0_0_s_ifspec;

/* Additional Prototypes for ALL interfaces */

/* end of Additional Prototypes */

#ifdef __cplusplus
}
#endif

#endif


