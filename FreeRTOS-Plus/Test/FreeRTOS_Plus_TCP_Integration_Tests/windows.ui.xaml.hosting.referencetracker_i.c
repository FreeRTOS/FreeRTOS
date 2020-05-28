

/* this ALWAYS GENERATED file contains the IIDs and CLSIDs */

/* link this file in with the server and any clients */


 /* File created by MIDL compiler version 8.01.0622 */
/* at Mon Jan 18 19:14:07 2038
 */
/* Compiler settings for ..\..\..\..\..\..\..\..\Program Files (x86)\Windows Kits\10\Include\10.0.18362.0\um\windows.ui.xaml.hosting.referencetracker.idl:
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

MIDL_DEFINE_GUID(IID, IID_IReferenceTrackerTarget,0x64bd43f8,0xbfee,0x4ec4,0xb7,0xeb,0x29,0x35,0x15,0x8d,0xae,0x21);


MIDL_DEFINE_GUID(IID, IID_IReferenceTracker,0x11d3b13a,0x180e,0x4789,0xa8,0xbe,0x77,0x12,0x88,0x28,0x93,0xe6);


MIDL_DEFINE_GUID(IID, IID_IReferenceTrackerManager,0x3cf184b4,0x7ccb,0x4dda,0x84,0x55,0x7e,0x6c,0xe9,0x9a,0x32,0x98);


MIDL_DEFINE_GUID(IID, IID_IFindReferenceTargetsCallback,0x04b3486c,0x4687,0x4229,0x8d,0x14,0x50,0x5a,0xb5,0x84,0xdd,0x88);


MIDL_DEFINE_GUID(IID, IID_IReferenceTrackerHost,0x29a71c6a,0x3c42,0x4416,0xa3,0x9d,0xe2,0x82,0x5a,0x07,0xa7,0x73);


MIDL_DEFINE_GUID(IID, IID_IReferenceTrackerExtension,0x4e897caa,0x59d5,0x4613,0x8f,0x8c,0xf7,0xeb,0xd1,0xf3,0x99,0xb0);


MIDL_DEFINE_GUID(IID, IID_ITrackerOwner,0xeb24c20b,0x9816,0x4ac7,0x8c,0xff,0x36,0xf6,0x7a,0x11,0x8f,0x4e);

#undef MIDL_DEFINE_GUID

#ifdef __cplusplus
}
#endif



