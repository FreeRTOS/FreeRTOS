

/* this ALWAYS GENERATED file contains the IIDs and CLSIDs */

/* link this file in with the server and any clients */


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



#ifdef __cplusplus
extern "C"{
#endif 


#include <rpc.h>
#include <rpcndr.h>

#ifdef _MIDL_USE_GUIDDEF_

#ifndef INITGUID
#define INITGUID
#include <guiddef.h>
#undef INITGUID
#else
#include <guiddef.h>
#endif

#define MIDL_DEFINE_GUID(type,name,l,w1,w2,b1,b2,b3,b4,b5,b6,b7,b8) \
        DEFINE_GUID(name,l,w1,w2,b1,b2,b3,b4,b5,b6,b7,b8)

#else // !_MIDL_USE_GUIDDEF_

#ifndef __IID_DEFINED__
#define __IID_DEFINED__

typedef struct _IID
{
    unsigned long x;
    unsigned short s1;
    unsigned short s2;
    unsigned char  c[8];
} IID;

#endif // __IID_DEFINED__

#ifndef CLSID_DEFINED
#define CLSID_DEFINED
typedef IID CLSID;
#endif // CLSID_DEFINED

#define MIDL_DEFINE_GUID(type,name,l,w1,w2,b1,b2,b3,b4,b5,b6,b7,b8) \
        EXTERN_C __declspec(selectany) const type name = {l,w1,w2,{b1,b2,b3,b4,b5,b6,b7,b8}}

#endif // !_MIDL_USE_GUIDDEF_

MIDL_DEFINE_GUID(IID, IID_ITargetFrame,0xd5f78c80,0x5252,0x11cf,0x90,0xfa,0x00,0xAA,0x00,0x42,0x10,0x6e);


MIDL_DEFINE_GUID(IID, IID_ITargetEmbedding,0x548793C0,0x9E74,0x11cf,0x96,0x55,0x00,0xA0,0xC9,0x03,0x49,0x23);


MIDL_DEFINE_GUID(IID, IID_ITargetFramePriv,0x9216E421,0x2BF5,0x11d0,0x82,0xB4,0x00,0xA0,0xC9,0x0C,0x29,0xC5);


MIDL_DEFINE_GUID(IID, IID_ITargetFramePriv2,0xB2C867E6,0x69D6,0x46F2,0xA6,0x11,0xDE,0xD9,0xA4,0xBD,0x7F,0xEF);

#undef MIDL_DEFINE_GUID

#ifdef __cplusplus
}
#endif



