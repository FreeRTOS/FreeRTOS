# Microsoft Developer Studio Project File - Name="AslCompiler" - Package Owner=<4>
# Microsoft Developer Studio Generated Build File, Format Version 6.00
# ** DO NOT EDIT **

# TARGTYPE "Win32 (x86) Application" 0x0101

CFG=AslCompiler - Win32 Debug
!MESSAGE This is not a valid makefile. To build this project using NMAKE,
!MESSAGE use the Export Makefile command and run
!MESSAGE
!MESSAGE NMAKE /f "AslCompiler.mak".
!MESSAGE
!MESSAGE You can specify a configuration when running NMAKE
!MESSAGE by defining the macro CFG on the command line. For example:
!MESSAGE
!MESSAGE NMAKE /f "AslCompiler.mak" CFG="AslCompiler - Win32 Debug"
!MESSAGE
!MESSAGE Possible choices for configuration are:
!MESSAGE
!MESSAGE "AslCompiler - Win32 Release" (based on "Win32 (x86) Application")
!MESSAGE "AslCompiler - Win32 Debug" (based on "Win32 (x86) Application")
!MESSAGE

# Begin Project
# PROP AllowPerConfigDependencies 0
# PROP Scc_ProjName ""
# PROP Scc_LocalPath ""
CPP=cl.exe
MTL=midl.exe
RSC=rc.exe

!IF  "$(CFG)" == "AslCompiler - Win32 Release"

# PROP BASE Use_MFC 2
# PROP BASE Use_Debug_Libraries 0
# PROP BASE Output_Dir "Release"
# PROP BASE Intermediate_Dir "Release"
# PROP BASE Target_Dir ""
# PROP Use_MFC 0
# PROP Use_Debug_Libraries 0
# PROP Output_Dir "AslCompiler"
# PROP Intermediate_Dir "AslCompiler"
# PROP Ignore_Export_Lib 0
# PROP Target_Dir ""
# ADD BASE CPP /nologo /MD /W3 /GX /O2 /D "WIN32" /D "NDEBUG" /D "_WINDOWS" /D "_AFXDLL" /YX /FD /c
# ADD CPP /nologo /W3 /Gi /Ob1 /Gf /I "..\..\source\include" /I "..\..\source\compiler" /I "." /D "NDEBUG" /D "WIN32" /D "_MBCS" /D "_CONSOLE" /D "__STDC__" /D "YY_NEVER_INTERACTIVE" /D "YY_NO_UNISTD_H" /D "ACPI_ASL_COMPILER" /FD /c
# SUBTRACT CPP /X /Fr /YX
# ADD BASE MTL /nologo /D "NDEBUG" /mktyplib203 /win32
# ADD MTL /nologo /D "NDEBUG" /mktyplib203 /win32
# ADD BASE RSC /l 0x409 /d "NDEBUG" /d "_AFXDLL"
# ADD RSC /l 0x409 /d "NDEBUG"
BSC32=bscmake.exe
# ADD BASE BSC32 /nologo
# ADD BSC32 /nologo /o"/acpica/generate/msvc2017/AslCompiler/AslCompiler.bsc"
LINK32=link.exe
# ADD BASE LINK32 /nologo /subsystem:windows /machine:I386
# ADD LINK32 kernel32.lib advapi32.lib setargv.obj /nologo /machine:I386
# SUBTRACT LINK32 /pdb:none
# Begin Special Build Tool
SOURCE="$(InputPath)"
PreLink_Desc=Checking existence of acpica/libraries directory
PreLink_Cmds=if NOT EXIST ..\..\libraries mkdir ..\..\libraries
PostBuild_Desc=Copying iasl to libraries...
PostBuild_Cmds=copy aslcompiler\aslcompiler.exe ..\..\libraries\iasl.exe
# End Special Build Tool

!ELSEIF  "$(CFG)" == "AslCompiler - Win32 Debug"

# PROP BASE Use_MFC 2
# PROP BASE Use_Debug_Libraries 1
# PROP BASE Output_Dir "Debug"
# PROP BASE Intermediate_Dir "Debug"
# PROP BASE Target_Dir ""
# PROP Use_MFC 0
# PROP Use_Debug_Libraries 1
# PROP Output_Dir "AslCompilerDebug"
# PROP Intermediate_Dir "AslCompilerDebug"
# PROP Ignore_Export_Lib 0
# PROP Target_Dir ""
# ADD BASE CPP /nologo /MDd /W3 /Gm /GX /ZI /Od /D "WIN32" /D "_DEBUG" /D "_WINDOWS" /D "_AFXDLL" /YX /FD /GZ /c
# ADD CPP /nologo /W3 /Gm /Gi /Zi /Od /Oy /Ob1 /Gf /I "..\..\source\include" /I "..\..\source\compiler" /I "." /D "_DEBUG" /D "WIN32" /D "_MBCS" /D "_CONSOLE" /D "__STDC__" /D "YY_NEVER_INTERACTIVE" /D "YY_NO_UNISTD_H" /D "ACPI_ASL_COMPILER" /FD /GZ /c
# SUBTRACT CPP /Fr
# ADD BASE MTL /nologo /D "_DEBUG" /mktyplib203 /win32
# ADD MTL /nologo /D "_DEBUG" /mktyplib203 /win32
# ADD BASE RSC /l 0x409 /d "_DEBUG" /d "_AFXDLL"
# ADD RSC /l 0x409 /d "_DEBUG"
BSC32=bscmake.exe
# ADD BASE BSC32 /nologo
# ADD BSC32 /nologo /o"/acpica/generate/msvc2017/AslCompilerDebug/AslCompiler.bsc"
LINK32=link.exe
# ADD BASE LINK32 /nologo /subsystem:windows /debug /machine:I386 /pdbtype:sept
# ADD LINK32 kernel32.lib advapi32.lib setargv.obj /nologo /pdb:none /debug /machine:I386 /nodefaultlib:"libcmt.lib" /pdb:"/acpica/generate/msvc2017/AslCompilerDebug/AslCompiler.pdb"
# Begin Special Build Tool
SOURCE="$(InputPath)"
PreLink_Desc=Checking existence of acpica/libraries directory
PreLink_Cmds=if NOT EXIST ..\..\libraries mkdir ..\..\libraries
PostBuild_Desc=Copying iasl to libraries...
PostBuild_Cmds=copy aslcompilerdebug\aslcompiler.exe ..\..\\libraries\iasl_dbg.exe
# End Special Build Tool

!ENDIF

# Begin Target

# Name "AslCompiler - Win32 Release"
# Name "AslCompiler - Win32 Debug"
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

SOURCE=..\..\source\components\utilities\utascii.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utbuffer.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utcache.c
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

SOURCE=..\..\source\components\utilities\utexcep.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utglobal.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\uthex.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utinit.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utlock.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utmath.c
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

SOURCE=..\..\source\components\utilities\utuuid.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utxface.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utxferror.c
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

SOURCE=..\..\source\components\namespace\nsdump.c
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

SOURCE=..\..\source\components\namespace\nssearch.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nsutils.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nswalk.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\NAMESPACE\nsxfobj.c
# End Source File
# End Group
# Begin Group "Compiler"

# PROP Default_Filter ""
# Begin Source File

SOURCE=..\..\source\compiler\aslanalyze.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslascii.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslbtypes.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslcodegen.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslcompile.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\asldebug.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslerror.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslexternal.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslfileio.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslfiles.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslfold.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslhelp.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslhex.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\asllength.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\asllisting.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\asllistsup.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslload.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\asllookup.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslmain.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslmap.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslmapenter.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslmapoutput.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslmaputils.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslmessages.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslmethod.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslnamesp.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\asloffset.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslopcodes.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\asloperands.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslopt.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\asloptions.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslpld.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslpredef.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslprepkg.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslprintf.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslprune.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslresource.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslrestype1.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslrestype1i.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslrestype2.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslrestype2d.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslrestype2e.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslrestype2q.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslrestype2s.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslrestype2w.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslstartup.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslstubs.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\asltransform.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\asltree.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslutils.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\asluuid.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslwalks.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslxref.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslxrefout.c
# End Source File
# End Group
# Begin Group "Common"

# PROP Default_Filter ".c"
# Begin Source File

SOURCE=..\..\source\common\acfileio.c
# End Source File
# Begin Source File

SOURCE=..\..\source\common\adfile.c
# End Source File
# Begin Source File

SOURCE=..\..\source\common\adisasm.c
# End Source File
# Begin Source File

SOURCE=..\..\source\common\adwalk.c
# End Source File
# Begin Source File

SOURCE=..\..\source\common\ahids.c
# End Source File
# Begin Source File

SOURCE=..\..\source\common\ahpredef.c
# End Source File
# Begin Source File

SOURCE=..\..\source\common\ahtable.c
# End Source File
# Begin Source File

SOURCE=..\..\source\common\ahuuids.c
# End Source File
# Begin Source File

SOURCE=..\..\source\common\cmfsize.c
# End Source File
# Begin Source File

SOURCE=..\..\source\common\dmextern.c
# End Source File
# Begin Source File

SOURCE=..\..\source\common\dmrestag.c
# End Source File
# Begin Source File

SOURCE=..\..\source\common\dmswitch.c
# End Source File
# Begin Source File

SOURCE=..\..\source\common\dmtable.c
# End Source File
# Begin Source File

SOURCE=..\..\source\common\dmtables.c
# End Source File
# Begin Source File

SOURCE=..\..\source\common\dmtbdump.c
# End Source File
# Begin Source File

SOURCE=..\..\source\common\dmtbinfo.c
# End Source File
# Begin Source File

SOURCE=..\..\source\common\getopt.c
# End Source File
# Begin Source File

SOURCE=..\..\source\os_specific\service_layers\oswindir.c
# End Source File
# Begin Source File

SOURCE=..\..\source\os_specific\service_layers\oswintbl.c
# ADD CPP /Ze
# End Source File
# Begin Source File

SOURCE=..\..\source\os_specific\service_layers\oswinxf.c
# ADD CPP /Ze
# End Source File
# End Group
# Begin Group "Intermediate"

# PROP Default_Filter "*.c, *.h"
# Begin Source File

SOURCE=.\aslcompiler.l.c
# End Source File
# Begin Source File

SOURCE=.\aslcompiler.y.c
# End Source File
# Begin Source File

SOURCE=.\dtparser.l.c
# End Source File
# Begin Source File

SOURCE=.\dtparser.y.c
# End Source File
# Begin Source File

SOURCE=.\prparser.l.c
# End Source File
# Begin Source File

SOURCE=.\prparser.y.c
# End Source File
# End Group
# Begin Group "Disassembler"

# PROP Default_Filter ""
# Begin Source File

SOURCE=..\..\source\COMPONENTS\DEBUGGER\dbfileio.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\disassembler\dmbuffer.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\disassembler\dmcstyle.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\disassembler\dmdeferred.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\disassembler\dmnames.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\disassembler\dmopcode.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\disassembler\dmresrc.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\disassembler\dmresrcl.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\disassembler\dmresrcl2.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\disassembler\dmresrcs.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\Disassembler\dmutils.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\disassembler\dmwalk.c
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

SOURCE=..\..\source\COMPONENTS\tables\tbinstal.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\tables\tbprint.c
# End Source File
# Begin Source File

SOURCE=..\..\source\COMPONENTS\tables\tbutils.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\tables\tbxface.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\tables\tbxfload.c
# End Source File
# End Group
# Begin Group "Interpreter"

# PROP Default_Filter ""
# Begin Source File

SOURCE=..\..\source\components\executer\exconcat.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exconvrt.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\excreate.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exdump.c
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
# Begin Group "Parser"

# PROP Default_Filter ""
# Begin Source File

SOURCE=..\..\source\compiler\prexpress.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\prmacros.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\prscan.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\prutils.c
# End Source File
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
# End Group
# Begin Group "Dispatcher"

# PROP Default_Filter ""
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
# Begin Group "DataCompiler"

# PROP Default_Filter ""
# Begin Source File

SOURCE=..\..\source\compiler\dtcompile.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\dtexpress.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\dtfield.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\dtio.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\dtsubtable.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\dttable.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\dttable1.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\dttable2.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\dttemplate.c
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\dtutils.c
# End Source File
# End Group
# End Group
# Begin Group "Header Files"

# PROP Default_Filter "h;hpp;hxx;hm;inl"
# Begin Source File

SOURCE=..\..\source\compiler\aslcompiler.h
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\asldefine.h
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslglobal.h
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslmessages.h
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\asltypes.h
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\dtcompiler.h
# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\dttemplate.h
# End Source File
# End Group
# Begin Group "Resource Files"

# PROP Default_Filter "ico;cur;bmp;dlg;rc2;rct;bin;rgs;gif;jpg;jpeg;jpe"
# End Group
# Begin Source File

SOURCE=../../source/compiler/aslcompiler.l

!IF  "$(CFG)" == "AslCompiler - Win32 Release"

# PROP Ignore_Default_Tool 1
# Begin Custom Build - Lexing $(InputPath)...
InputPath=../../source/compiler/aslcompiler.l
InputName=aslcompiler

"$(InputName).l.c" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
	flex -i -PAslCompiler -o$(InputName).l.c $(InputPath)

# End Custom Build

!ELSEIF  "$(CFG)" == "AslCompiler - Win32 Debug"

# PROP Ignore_Default_Tool 1
# Begin Custom Build - Lexing $(InputPath)...
InputPath=../../source/compiler/aslcompiler.l
InputName=aslcompiler

"$(InputName).l.c" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
	flex -i -PAslCompiler -o$(InputName).l.c $(InputPath)

# End Custom Build

!ENDIF

# End Source File
# Begin Source File

SOURCE=../../source/compiler/aslcompiler.y

!IF  "$(CFG)" == "AslCompiler - Win32 Release"

# PROP Ignore_Default_Tool 1
# Begin Custom Build - Yaccing $(InputPath)...
InputPath=../../source/compiler/aslcompiler.y
InputName=aslcompiler

BuildCmds= \
	bison -d -l -pAslCompiler -v $(InputPath) -vd -o$(InputName).y.c

"$(InputName).y.c" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
   $(BuildCmds)

"$(InputName).y.h" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
   $(BuildCmds)
# End Custom Build

!ELSEIF  "$(CFG)" == "AslCompiler - Win32 Debug"

# PROP Ignore_Default_Tool 1
# Begin Custom Build - Yaccing $(InputPath)...
InputPath=../../source/compiler/aslcompiler.y
InputName=aslcompiler

BuildCmds= \
	bison -d -l -pAslCompiler -v $(InputPath) -vd -o$(InputName).y.c

"$(InputName).y.c" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
   $(BuildCmds)

"$(InputName).y.h" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
   $(BuildCmds)
# End Custom Build

!ENDIF

# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\aslparser.y

!IF  "$(CFG)" == "AslCompiler - Win32 Release"

# PROP Ignore_Default_Tool 1
# Begin Custom Build - Macro-processing $(InputPath)...
InputDir=\workspace\acpica\source\compiler
InputPath=..\..\source\compiler\aslparser.y

"$(InputDir)/aslcompiler.y" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
	m4 -P -I$(InputDir) $(InputPath) > $(InputDir)/aslcompiler.y

# End Custom Build

!ELSEIF  "$(CFG)" == "AslCompiler - Win32 Debug"

# PROP Ignore_Default_Tool 1
# Begin Custom Build - Macro-processing $(InputPath)...
InputDir=\workspace\acpica\source\compiler
InputPath=..\..\source\compiler\aslparser.y

"$(InputDir)/aslcompiler.y" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
	m4 -P -I$(InputDir) $(InputPath) > $(InputDir)/aslcompiler.y

# End Custom Build

!ENDIF

# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\dtparser.l

!IF  "$(CFG)" == "AslCompiler - Win32 Release"

# Begin Custom Build - Lexing $(InputPath)...
InputPath=..\..\source\compiler\dtparser.l
InputName=dtparser

"$(InputName).l.c" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
	flex -PDtParser -o$(InputName).l.c $(InputPath)

# End Custom Build

!ELSEIF  "$(CFG)" == "AslCompiler - Win32 Debug"

# PROP Ignore_Default_Tool 1
# Begin Custom Build - Lexing $(InputPath)...
InputPath=..\..\source\compiler\dtparser.l
InputName=dtparser

"$(InputName).l.c" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
	flex -PDtParser -o$(InputName).l.c $(InputPath)

# End Custom Build

!ENDIF

# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\dtparser.y

!IF  "$(CFG)" == "AslCompiler - Win32 Release"

# Begin Custom Build - Yaccing $(InputPath)...
InputPath=..\..\source\compiler\dtparser.y
InputName=dtparser

BuildCmds= \
	bison -d -l -pDtParser -v $(InputPath) -vd -o$(InputName).y.c

"$(InputName).y.c" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
   $(BuildCmds)

"$(InputName).y.h" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
   $(BuildCmds)
# End Custom Build

!ELSEIF  "$(CFG)" == "AslCompiler - Win32 Debug"

# PROP Ignore_Default_Tool 1
# Begin Custom Build - Yaccing $(InputPath)...
InputPath=..\..\source\compiler\dtparser.y
InputName=dtparser

BuildCmds= \
	bison -d -l -pDtParser -v $(InputPath) -vd -o$(InputName).y.c

"$(InputName).y.c" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
   $(BuildCmds)

"$(InputName).y.h" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
   $(BuildCmds)
# End Custom Build

!ENDIF

# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\prparser.l

!IF  "$(CFG)" == "AslCompiler - Win32 Release"

# Begin Custom Build - Lexing $(InputPath)...
InputPath=..\..\source\compiler\prparser.l
InputName=prparser

"$(InputName).l.c" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
	flex -PPrParser -o$(InputName).l.c $(InputPath)

# End Custom Build

!ELSEIF  "$(CFG)" == "AslCompiler - Win32 Debug"

# PROP Ignore_Default_Tool 1
# Begin Custom Build - Lexing $(InputPath)...
InputPath=..\..\source\compiler\prparser.l
InputName=prparser

"$(InputName).l.c" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
	flex -PPrParser -o$(InputName).l.c $(InputPath)

# End Custom Build

!ENDIF

# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\prparser.y

!IF  "$(CFG)" == "AslCompiler - Win32 Release"

# Begin Custom Build - Yaccing $(InputPath)...
InputPath=..\..\source\compiler\prparser.y
InputName=prparser

BuildCmds= \
	bison -d -l -pPrParser -v $(InputPath) -vd -o$(InputName).y.c

"$(InputName).y.c" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
   $(BuildCmds)

"$(InputName).y.h" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
   $(BuildCmds)
# End Custom Build

!ELSEIF  "$(CFG)" == "AslCompiler - Win32 Debug"

# PROP Ignore_Default_Tool 1
# Begin Custom Build - Yaccing $(InputPath)...
InputPath=..\..\source\compiler\prparser.y
InputName=prparser

BuildCmds= \
	bison -d -l -pPrParser -v $(InputPath) -vd -o$(InputName).y.c

"$(InputName).y.c" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
   $(BuildCmds)

"$(InputName).y.h" : $(SOURCE) "$(INTDIR)" "$(OUTDIR)"
   $(BuildCmds)
# End Custom Build

!ENDIF

# End Source File
# Begin Source File

SOURCE=..\..\source\compiler\readme.txt
# End Source File
# End Target
# End Project
