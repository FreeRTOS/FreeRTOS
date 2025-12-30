# Microsoft Developer Studio Project File - Name="AcpiSubsystem" - Package Owner=<4>
# Microsoft Developer Studio Generated Build File, Format Version 6.00
# ** DO NOT EDIT **

# TARGTYPE "Win32 (x86) Static Library" 0x0104

CFG=AcpiSubsystem - Win32 Debug
!MESSAGE This is not a valid makefile. To build this project using NMAKE,
!MESSAGE use the Export Makefile command and run
!MESSAGE
!MESSAGE NMAKE /f "AcpiSubsystem.mak".
!MESSAGE
!MESSAGE You can specify a configuration when running NMAKE
!MESSAGE by defining the macro CFG on the command line. For example:
!MESSAGE
!MESSAGE NMAKE /f "AcpiSubsystem.mak" CFG="AcpiSubsystem - Win32 Debug"
!MESSAGE
!MESSAGE Possible choices for configuration are:
!MESSAGE
!MESSAGE "AcpiSubsystem - Win32 Release" (based on "Win32 (x86) Static Library")
!MESSAGE "AcpiSubsystem - Win32 Debug" (based on "Win32 (x86) Static Library")
!MESSAGE

# Begin Project
# PROP AllowPerConfigDependencies 0
# PROP Scc_ProjName ""
# PROP Scc_LocalPath ""
CPP=cl.exe
RSC=rc.exe

!IF  "$(CFG)" == "AcpiSubsystem - Win32 Release"

# PROP BASE Use_MFC 0
# PROP BASE Use_Debug_Libraries 0
# PROP BASE Output_Dir "Release"
# PROP BASE Intermediate_Dir "Release"
# PROP BASE Target_Dir ""
# PROP Use_MFC 0
# PROP Use_Debug_Libraries 0
# PROP Output_Dir "AcpiSubsystem"
# PROP Intermediate_Dir "AcpiSubsystem"
# PROP Target_Dir ""
# ADD BASE CPP /nologo /W3 /GX /O2 /D "WIN32" /D "NDEBUG" /D "_MBCS" /D "_LIB" /YX /FD /c
# ADD CPP /nologo /W3 /Gi /Ob1 /Gf /I "..\..\source\include" /D "NDEBUG" /D "WIN32" /D "_MBCS" /D "_CONSOLE" /D "__STDC__" /D "ACPI_LIBRARY" /FD /c
# SUBTRACT CPP /Fr /YX
# ADD BASE RSC /l 0x409 /d "NDEBUG"
# ADD RSC /l 0x409 /d "NDEBUG"
BSC32=bscmake.exe
# ADD BASE BSC32 /nologo
# ADD BSC32 /nologo
LIB32=link.exe -lib
# ADD BASE LIB32 /nologo
# Begin Special Build Tool
SOURCE="$(InputPath)"
PreLink_Desc=Checking existence of acpica/libraries directory
PreLink_Cmds=if NOT EXIST ..\..\libraries mkdir ..\..\libraries
PostBuild_Desc=Copying libacpica to libraries...
PostBuild_Cmds=copy acpisubsystem\acpisubsystem.lib ..\..\libraries\acpica.lib
# End Special Build Tool

!ELSEIF  "$(CFG)" == "AcpiSubsystem - Win32 Debug"

# PROP BASE Use_MFC 0
# PROP BASE Use_Debug_Libraries 1
# PROP BASE Output_Dir "Debug"
# PROP BASE Intermediate_Dir "Debug"
# PROP BASE Target_Dir ""
# PROP Use_MFC 0
# PROP Use_Debug_Libraries 1
# PROP Output_Dir "AcpiSubsystemDebug"
# PROP Intermediate_Dir "AcpiSubsystemDebug"
# PROP Target_Dir ""
# ADD BASE CPP /nologo /W3 /GX /ZI /Od /D "WIN32" /D "_DEBUG" /D "_MBCS" /D "_LIB" /YX /FD /GZ /c
# ADD CPP /nologo /MTd /W3 /Gm /Gi /Zi /Od /Oy /Ob1 /Gf /I "..\..\source\include" /D "NDEBUG" /D "WIN32" /D "_MBCS" /D "_CONSOLE" /D "__STDC__" /D "ACPI_LIBRARY" /FD /c
# SUBTRACT CPP /Fr
# ADD BASE RSC /l 0x409 /d "_DEBUG"
# ADD RSC /l 0x409
BSC32=bscmake.exe
# ADD BASE BSC32 /nologo
# ADD BSC32 /nologo /o"/acpica/generate/msvc/AcpiSubsystemDebug/AcpiSubsystem.bsc"
LIB32=link.exe -lib
# ADD BASE LIB32 /nologo
# ADD LIB32 /nologo
# Begin Special Build Tool
SOURCE="$(InputPath)"
PreLink_Desc=Checking existence of acpica/libraries directory
PreLink_Cmds=if NOT EXIST ..\..\libraries mkdir ..\..\libraries
PostBuild_Desc=Copying libacpica to libraries...
PostBuild_Cmds=copy acpisubsystemdebug\acpisubsystem.lib ..\..\libraries\acpica_dbg.lib
# End Special Build Tool

!ENDIF

# Begin Target

# Name "AcpiSubsystem - Win32 Release"
# Name "AcpiSubsystem - Win32 Debug"
# Begin Group "Source Files"

# PROP Default_Filter "cpp;c;cxx;rc;def;r;odl;idl;hpj;bat"
# Begin Group "Utilities"

# PROP Default_Filter ".c"
# Begin Source File

SOURCE=..\..\source\components\utilities\utaddress.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utalloc.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utbuffer.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utcache.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utclib.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utcopy.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utdebug.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utdecode.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utdelete.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\uterror.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\uteval.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utexcep.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utglobal.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\uthex.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utids.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utinit.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utlock.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utmath.c
# ADD CPP /Ze
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utmisc.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utmutex.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utnonansi.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utobject.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utosi.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utownerid.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utpredef.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utresrc.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utstate.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utstring.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utstrtoul64.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\uttrack.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utxface.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utxferror.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utxfinit.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utxfmutex.c
# End Source File
# End Group
# Begin Group "Events"

# PROP Default_Filter ".c"
# Begin Source File

SOURCE=..\..\source\components\events\evevent.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\events\evglock.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\EVENTS\evgpe.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\EVENTS\evgpeblk.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\events\evgpeinit.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\events\evgpeutil.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\events\evhandler.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\events\evmisc.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\events\evregion.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\events\evrgnini.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\events\evsci.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\events\evxface.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\events\evxfevnt.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\events\evxfgpe.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\events\evxfregn.c
# End Source File
# End Group
# Begin Group "Hardware"

# PROP Default_Filter ".c"
# Begin Source File

SOURCE=..\..\source\components\hardware\hwacpi.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\hardware\hwesleep.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\hardware\hwgpe.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\hardware\hwpci.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\hardware\hwregs.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\hardware\hwsleep.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\hardware\hwtimer.c
# ADD CPP /Ze
# End Source File
# Begin Source File

SOURCE=..\..\source\components\hardware\hwvalid.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\hardware\hwxface.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\hardware\hwxfsleep.c
# End Source File
# End Group
# Begin Group "Namespace"

# PROP Default_Filter ".c"
# Begin Source File

SOURCE=..\..\source\components\namespace\nsaccess.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nsalloc.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nsarguments.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nsconvert.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nsdump.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\NAMESPACE\nsdumpdv.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nseval.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nsinit.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nsload.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nsnames.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nsobject.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\NAMESPACE\nsparse.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nspredef.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nsprepkg.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nsrepair.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nsrepair2.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nssearch.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nsutils.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nswalk.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\NAMESPACE\nsxfeval.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nsxfname.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nsxfobj.c
# End Source File
# End Group
# Begin Group "Resources"

# PROP Default_Filter ".c"
# Begin Source File

SOURCE=..\..\source\components\resources\rsaddr.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\resources\rscalc.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\resources\rscreate.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\resources\rsdump.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\resources\rsdumpinfo.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\resources\rsinfo.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\resources\rsio.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\resources\rsirq.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\resources\rslist.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\resources\rsmemory.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\resources\rsmisc.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\resources\rsserial.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\resources\rsutils.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\resources\rsxface.c
# End Source File
# End Group
# Begin Group "Tables"

# PROP Default_Filter ""
# Begin Source File

SOURCE=..\..\source\components\tables\tbdata.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\tables\tbfadt.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\tables\tbfind.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\tables\tbinstal.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\tables\tbprint.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\tables\tbutils.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\tables\tbxface.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\tables\tbxfload.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\tables\tbxfroot.c
# End Source File
# End Group
# Begin Group "Disassembler"

# PROP Default_Filter ""
# Begin Source File

SOURCE=..\..\source\COMPONENTS\Disassembler\dmbuffer.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\disassembler\dmdeferred.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\Disassembler\dmnames.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\Disassembler\dmopcode.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\Disassembler\dmresrc.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\Disassembler\dmresrcl.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\disassembler\dmresrcl2.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\Disassembler\dmresrcs.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\Disassembler\dmutils.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\Disassembler\dmwalk.c
# End Source File
# End Group
# Begin Group "Debugger"

# PROP Default_Filter ""
# Begin Source File

SOURCE=..\..\source\COMPONENTS\DEBUGGER\dbcmds.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\debugger\dbconvert.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\DEBUGGER\dbdisply.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\DEBUGGER\dbexec.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\DEBUGGER\dbfileio.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\DEBUGGER\dbhistry.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\DEBUGGER\dbinput.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\debugger\dbmethod.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\debugger\dbnames.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\debugger\dbobject.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\DEBUGGER\dbstats.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\debugger\dbtest.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\DEBUGGER\dbutils.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\DEBUGGER\dbxface.c
# End Source File
# End Group
# Begin Group "Interpreter"

# PROP Default_Filter "*.c"
# Begin Source File

SOURCE=..\..\source\components\executer\exconfig.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exconvrt.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\excreate.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exdebug.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exdump.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exfield.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exfldio.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exmisc.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exmutex.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exnames.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exoparg1.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exoparg2.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exoparg3.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exoparg6.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exprep.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exregion.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exresnte.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exresolv.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exresop.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exstore.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exstoren.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exstorob.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exsystem.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exutils.c
# End Source File
# End Group
# Begin Group "Dispatcher"

# PROP Default_Filter "*.c"
# Begin Source File

SOURCE=..\..\source\components\dispatcher\dsargs.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\dispatcher\dscontrol.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\dispatcher\dsfield.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\dispatcher\dsinit.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\dispatcher\dsmethod.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\dispatcher\dsmthdat.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\dispatcher\dsobject.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\dispatcher\dsopcode.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\dispatcher\dsutils.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\dispatcher\dswexec.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\dispatcher\dswload.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\dispatcher\dswload2.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\dispatcher\dswscope.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\dispatcher\dswstate.c
# End Source File
# End Group
# Begin Group "Parser"

# PROP Default_Filter "*.c"
# Begin Source File

SOURCE=..\..\source\components\parser\psargs.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\parser\psloop.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\parser\psobject.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\parser\psopcode.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\parser\psopinfo.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\parser\psparse.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\parser\psscope.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\parser\pstree.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\parser\psutils.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\parser\pswalk.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\parser\psxface.c
# End Source File
# End Group
# Begin Group "Common"

# PROP Default_Filter ""
# Begin Source File

SOURCE=..\..\source\common\ahids.c
# End Source File
# Begin Source File

SOURCE=..\..\source\common\cmfsize.c
# End Source File
# End Group
# End Group
# Begin Group "Header Files"

# PROP Default_Filter "h;hpp;hxx;hm;inl"
# Begin Source File

SOURCE=..\..\source\include\acbuffer.h
# End Source File
# Begin Source File

SOURCE=..\..\source\include\accommon.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\acconfig.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\acdebug.h
# End Source File
# Begin Source File

SOURCE=..\..\source\INCLUDE\acdisasm.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\acdispat.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\platform\acefi.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\platform\acenv.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\acevents.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\acexcep.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\platform\acfreebsd.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\platform\acgcc.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\acglobal.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\achware.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\acinterp.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\platform\aclinux.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\aclocal.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\acmacros.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\platform\acmsvc.h
# End Source File
# Begin Source File

SOURCE=..\..\source\include\acnames.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\acnamesp.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\acobject.h
# End Source File
# Begin Source File

SOURCE=..\..\source\include\acopcode.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\acoutput.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\acparser.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\acpi.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\acpiosxf.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\acpixf.h
# End Source File
# Begin Source File

SOURCE=..\..\source\include\acpredef.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\acresrc.h
# End Source File
# Begin Source File

SOURCE=..\..\source\include\acrestyp.h
# End Source File
# Begin Source File

SOURCE=..\..\source\include\acstruct.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\actables.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\actbl.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\actbl1.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\actbl2.h
# End Source File
# Begin Source File

SOURCE=..\..\source\include\actbl3.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\actypes.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\acutils.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\platform\acwin.h
# End Source File
# Begin Source File

SOURCE=..\..\source\Include\amlcode.h
# End Source File
# Begin Source File

SOURCE=..\..\source\INCLUDE\amlresrc.h
# End Source File
# End Group
# End Target
# End Project
