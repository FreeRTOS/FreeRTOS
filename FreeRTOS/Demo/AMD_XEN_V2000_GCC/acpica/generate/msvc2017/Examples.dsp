# Microsoft Developer Studio Project File - Name="Examples" - Package Owner=<4>
# Microsoft Developer Studio Generated Build File, Format Version 6.00
# ** DO NOT EDIT **

# TARGTYPE "Win32 (x86) Console Application" 0x0103

CFG=Examples - Win32 Debug
!MESSAGE This is not a valid makefile. To build this project using NMAKE,
!MESSAGE use the Export Makefile command and run
!MESSAGE
!MESSAGE NMAKE /f "Examples.mak".
!MESSAGE
!MESSAGE You can specify a configuration when running NMAKE
!MESSAGE by defining the macro CFG on the command line. For example:
!MESSAGE
!MESSAGE NMAKE /f "Examples.mak" CFG="Examples - Win32 Debug"
!MESSAGE
!MESSAGE Possible choices for configuration are:
!MESSAGE
!MESSAGE "Examples - Win32 Release" (based on "Win32 (x86) Console Application")
!MESSAGE "Examples - Win32 Debug" (based on "Win32 (x86) Console Application")
!MESSAGE

# Begin Project
# PROP AllowPerConfigDependencies 0
# PROP Scc_ProjName ""
# PROP Scc_LocalPath ""
CPP=cl.exe
RSC=rc.exe

!IF  "$(CFG)" == "Examples - Win32 Release"

# PROP BASE Use_MFC 0
# PROP BASE Use_Debug_Libraries 0
# PROP BASE Output_Dir "Release"
# PROP BASE Intermediate_Dir "Release"
# PROP BASE Target_Dir ""
# PROP Use_MFC 0
# PROP Use_Debug_Libraries 0
# PROP Output_Dir "Examples"
# PROP Intermediate_Dir "Examples"
# PROP Ignore_Export_Lib 0
# PROP Target_Dir ""
# ADD BASE CPP /nologo /W3 /GX /O2 /D "WIN32" /D "NDEBUG" /D "_CONSOLE" /D "_MBCS" /YX /FD /c
# ADD CPP /nologo /W3 /Gi /Ob1 /Gf /I "..\..\source\include" /D "NDEBUG" /D "WIN32" /D "_MBCS" /D "_CONSOLE" /D "__STDC__" /D "ACPI_EXAMPLE_APP" /FD /c
# SUBTRACT CPP /Fr /YX
# ADD BASE RSC /l 0x409 /d "NDEBUG"
# ADD RSC /l 0x409 /d "NDEBUG"
BSC32=bscmake.exe
# ADD BASE BSC32 /nologo
# ADD BSC32 /nologo
LINK32=link.exe
# ADD BASE LINK32 kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib /nologo /subsystem:console /machine:I386
# ADD LINK32 kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib /nologo /subsystem:console /incremental:yes /map /machine:I386 /nodefaultlib:"LIBCMTD"
# SUBTRACT LINK32 /pdb:none
# Begin Special Build Tool
SOURCE="$(InputPath)"
PostBuild_Desc=Copying examples to libraries...
PostBuild_Cmds=copy examples\examples.exe ..\..\libraries\examples.exe
# End Special Build Tool

!ELSEIF  "$(CFG)" == "Examples - Win32 Debug"

# PROP BASE Use_MFC 0
# PROP BASE Use_Debug_Libraries 1
# PROP BASE Output_Dir "Debug"
# PROP BASE Intermediate_Dir "Debug"
# PROP BASE Target_Dir ""
# PROP Use_MFC 0
# PROP Use_Debug_Libraries 1
# PROP Output_Dir "ExamplesDebug"
# PROP Intermediate_Dir "ExamplesDebug"
# PROP Ignore_Export_Lib 0
# PROP Target_Dir ""
# ADD BASE CPP /nologo /W3 /Gm /GX /ZI /Od /D "WIN32" /D "_DEBUG" /D "_CONSOLE" /D "_MBCS" /YX /FD /GZ /c
# ADD CPP /nologo /W3 /Gm /Gi /Zi /Od /Ob1 /I "..\..\source\include" /D "_DEBUG" /D "WIN32" /D "_MBCS" /D "_CONSOLE" /D "__STDC__" /D "ACPI_EXAMPLE_APP" /FD /GZ /c
# SUBTRACT CPP /Fr /YX
# ADD BASE RSC /l 0x409 /d "_DEBUG"
# ADD RSC /l 0x409 /d "_DEBUG"
BSC32=bscmake.exe
# ADD BASE BSC32 /nologo
# ADD BSC32 /nologo /o"/acpica/generate/msvc/ExamplesDebug/Examples.bsc"
LINK32=link.exe
# ADD BASE LINK32 kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib /nologo /subsystem:console /debug /machine:I386 /pdbtype:sept
# ADD LINK32 kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib /nologo /subsystem:console /map /debug /machine:I386 /pdbtype:sept
# SUBTRACT LINK32 /pdb:none
# Begin Special Build Tool
SOURCE="$(InputPath)"
PostBuild_Desc=Copying examples to libraries...
PostBuild_Cmds=copy examplesdebug\examples.exe ..\..\\libraries\examples_dbg.exe
# End Special Build Tool

!ENDIF

# Begin Target

# Name "Examples - Win32 Release"
# Name "Examples - Win32 Debug"
# Begin Group "Source Files"

# PROP Default_Filter "cpp;c;cxx;rc;def;r;odl;idl;hpj;bat"
# Begin Group "AcpiExamples"

# PROP Default_Filter ""
# Begin Source File

SOURCE=..\..\source\tools\examples\examples.c
# End Source File
# Begin Source File

SOURCE=..\..\source\tools\examples\exstubs.c
# End Source File
# Begin Source File

SOURCE=..\..\source\tools\examples\extables.c
# End Source File
# Begin Source File

SOURCE=..\..\source\os_specific\service_layers\oswinxf.c
# ADD CPP /Ze
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

SOURCE=..\..\source\components\dispatcher\dsdebug.c
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
# Begin Group "Executer"

# PROP Default_Filter ""
# Begin Source File

SOURCE=..\..\source\components\executer\exconcat.c
# End Source File
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

SOURCE=..\..\source\components\executer\extrace.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\executer\exutils.c
# End Source File
# End Group
# Begin Group "Namespace"

# PROP Default_Filter ""
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

SOURCE=..\..\source\components\namespace\nsparse.c
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

SOURCE=..\..\source\components\namespace\nsxfeval.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nsxfname.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\namespace\nsxfobj.c
# End Source File
# End Group
# Begin Group "Parser"

# PROP Default_Filter ""
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
# Begin Group "Utilities"

# PROP Default_Filter ""
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

# PROP Default_Filter ""
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

SOURCE=..\..\source\components\events\evxface.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\events\evxfregn.c
# End Source File
# End Group
# Begin Group "Hardware"

# PROP Default_Filter ""
# Begin Source File

SOURCE=..\..\source\components\hardware\hwpci.c
# End Source File
# End Group
# End Group
# Begin Group "Header Files"

# PROP Default_Filter "h;hpp;hxx;hm;inl"
# Begin Source File

SOURCE=..\..\source\tools\examples\examples.h
# End Source File
# End Group
# Begin Group "Resource Files"

# PROP Default_Filter "ico;cur;bmp;dlg;rc2;rct;bin;rgs;gif;jpg;jpeg;jpe"
# End Group
# End Target
# End Project
