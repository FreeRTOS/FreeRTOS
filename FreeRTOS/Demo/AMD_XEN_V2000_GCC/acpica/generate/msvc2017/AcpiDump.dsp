# Microsoft Developer Studio Project File - Name="AcpiDump" - Package Owner=<4>
# Microsoft Developer Studio Generated Build File, Format Version 6.00
# ** DO NOT EDIT **

# TARGTYPE "Win32 (x86) Console Application" 0x0103

CFG=AcpiDump - Win32 Debug
!MESSAGE This is not a valid makefile. To build this project using NMAKE,
!MESSAGE use the Export Makefile command and run
!MESSAGE
!MESSAGE NMAKE /f "AcpiDump.mak".
!MESSAGE
!MESSAGE You can specify a configuration when running NMAKE
!MESSAGE by defining the macro CFG on the command line. For example:
!MESSAGE
!MESSAGE NMAKE /f "AcpiDump.mak" CFG="AcpiDump - Win32 Debug"
!MESSAGE
!MESSAGE Possible choices for configuration are:
!MESSAGE
!MESSAGE "AcpiDump - Win32 Release" (based on "Win32 (x86) Console Application")
!MESSAGE "AcpiDump - Win32 Debug" (based on "Win32 (x86) Console Application")
!MESSAGE

# Begin Project
# PROP AllowPerConfigDependencies 0
# PROP Scc_ProjName ""
# PROP Scc_LocalPath ""
CPP=cl.exe
RSC=rc.exe

!IF  "$(CFG)" == "AcpiDump - Win32 Release"

# PROP BASE Use_MFC 0
# PROP BASE Use_Debug_Libraries 0
# PROP BASE Output_Dir "Release"
# PROP BASE Intermediate_Dir "Release"
# PROP BASE Target_Dir ""
# PROP Use_MFC 0
# PROP Use_Debug_Libraries 0
# PROP Output_Dir "AcpiDump"
# PROP Intermediate_Dir "AcpiDump"
# PROP Ignore_Export_Lib 0
# PROP Target_Dir ""
# ADD BASE CPP /nologo /W3 /GX /O2 /D "WIN32" /D "NDEBUG" /D "_CONSOLE" /D "_MBCS" /Yu"stdafx.h" /FD /c
# ADD CPP /nologo /W3 /Gi /Ob1 /Gf /I "..\..\source\include" /D "NDEBUG" /D "WIN32" /D "_MBCS" /D "_CONSOLE" /D "__STDC__" /D "ACPI_DUMP_APP" /FD /c
# SUBTRACT CPP /Fr /YX /Yc /Yu
# ADD BASE RSC /l 0x409 /d "NDEBUG"
# ADD RSC /l 0x409 /d "NDEBUG"
BSC32=bscmake.exe
# ADD BASE BSC32 /nologo
# ADD BSC32 /nologo
LINK32=link.exe
# ADD BASE LINK32 kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib /nologo /subsystem:console /machine:I386
# ADD LINK32 kernel32.lib advapi32.lib /nologo /subsystem:console /machine:I386
# SUBTRACT LINK32 /pdb:none
# Begin Special Build Tool
SOURCE="$(InputPath)"
PreLink_Desc=Checking existence of acpica/libraries directory
PreLink_Cmds=if NOT EXIST ..\..\libraries mkdir ..\..\libraries
PostBuild_Desc=Copying acpidump to libraries...
PostBuild_Cmds=copy acpidump\acpidump.exe ..\..\libraries\acpidump.exe
# End Special Build Tool

!ELSEIF  "$(CFG)" == "AcpiDump - Win32 Debug"

# PROP BASE Use_MFC 0
# PROP BASE Use_Debug_Libraries 1
# PROP BASE Output_Dir "Debug"
# PROP BASE Intermediate_Dir "Debug"
# PROP BASE Target_Dir ""
# PROP Use_MFC 0
# PROP Use_Debug_Libraries 1
# PROP Output_Dir "AcpiDumpDebug"
# PROP Intermediate_Dir "AcpiDumpDebug"
# PROP Ignore_Export_Lib 0
# PROP Target_Dir ""
# ADD BASE CPP /nologo /W3 /Gm /GX /ZI /Od /D "WIN32" /D "_DEBUG" /D "_CONSOLE" /D "_MBCS" /Yu"stdafx.h" /FD /GZ /c
# ADD CPP /nologo /W3 /Gm /Gi /Zi /Od /Ob1 /Gf /I "..\..\source\include" /D "_DEBUG" /D "WIN32" /D "_MBCS" /D "_CONSOLE" /D "__STDC__" /D "ACPI_DUMP_APP" /FD /GZ /c
# SUBTRACT CPP /Fr
# ADD BASE RSC /l 0x409 /d "_DEBUG"
# ADD RSC /l 0x409 /d "_DEBUG"
BSC32=bscmake.exe
# ADD BASE BSC32 /nologo
# ADD BSC32 /nologo /o"/acpica/generate/msvc/AcpiDumpDebug/AcpiDump.bsc"
LINK32=link.exe
# ADD BASE LINK32 kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib /nologo /subsystem:console /debug /machine:I386 /pdbtype:sept
# ADD LINK32 kernel32.lib advapi32.lib /nologo /subsystem:console /incremental:no /map /debug /machine:I386 /pdbtype:sept
# SUBTRACT LINK32 /pdb:none
# Begin Special Build Tool
SOURCE="$(InputPath)"
PreLink_Desc=Checking existence of acpica/libraries directory
PreLink_Cmds=if NOT EXIST ..\..\libraries mkdir ..\..\libraries
PostBuild_Desc=Copying acpidump to libraries...
PostBuild_Cmds=copy acpidumpdebug\acpidump.exe ..\..\libraries\acpidump_dbg.exe
# End Special Build Tool

!ENDIF

# Begin Target

# Name "AcpiDump - Win32 Release"
# Name "AcpiDump - Win32 Debug"
# Begin Group "Source Files"

# PROP Default_Filter "cpp;c;cxx;rc;def;r;odl;idl;hpj;bat"
# Begin Group "AcpiDump"

# PROP Default_Filter ".c"
# Begin Source File

SOURCE=..\..\source\tools\acpidump\apdump.c
# End Source File
# Begin Source File

SOURCE=..\..\source\tools\acpidump\apfiles.c
# End Source File
# Begin Source File

SOURCE=..\..\source\tools\acpidump\apmain.c
# End Source File
# Begin Source File

SOURCE=..\..\source\os_specific\service_layers\oswintbl.c
# End Source File
# End Group
# Begin Group "Common"

# PROP Default_Filter ".c"
# Begin Source File

SOURCE=..\..\source\common\cmfsize.c
# End Source File
# Begin Source File

SOURCE=..\..\source\common\getopt.c
# End Source File
# Begin Source File

SOURCE=..\..\source\os_specific\SERVICE_LAYERS\oswindir.c
# End Source File
# Begin Source File

SOURCE=..\..\source\os_specific\service_layers\oswinxf.c
# End Source File
# End Group
# Begin Group "Utils"

# PROP Default_Filter ""
# Begin Source File

SOURCE=..\..\source\components\utilities\utascii.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utbuffer.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utdebug.c
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

SOURCE=..\..\source\components\utilities\utmath.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utnonansi.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utstring.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utstrtoul64.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\utilities\utxferror.c
# End Source File
# End Group
# Begin Group "Tables"

# PROP Default_Filter ""
# Begin Source File

SOURCE=..\..\source\components\tables\tbprint.c
# End Source File
# Begin Source File

SOURCE=..\..\source\components\tables\tbxfroot.c
# End Source File
# End Group
# End Group
# Begin Group "Header Files"

# PROP Default_Filter "h;hpp;hxx;hm;inl"
# Begin Source File

SOURCE=..\..\source\tools\acpidump\acpidump.h
# End Source File
# End Group
# Begin Group "Resource Files"

# PROP Default_Filter "ico;cur;bmp;dlg;rc2;rct;bin;rgs;gif;jpg;jpeg;jpe"
# End Group
# End Target
# End Project
