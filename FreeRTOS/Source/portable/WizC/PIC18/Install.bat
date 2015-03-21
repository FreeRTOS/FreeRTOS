REM/*
REM    FreeRTOS V8.2.1 - Copyright (C) 2015 Real Time Engineers Ltd.
REM
REM
REM    ***************************************************************************
REM     *                                                                       *
REM     *    FreeRTOS tutorial books are available in pdf and paperback.        *
REM     *    Complete, revised, and edited pdf reference manuals are also       *
REM     *    available.                                                         *
REM     *                                                                       *
REM     *    Purchasing FreeRTOS documentation will not only help you, by       *
REM     *    ensuring you get running as quickly as possible and with an        *
REM     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
REM     *    the FreeRTOS project to continue with its mission of providing     *
REM     *    professional grade, cross platform, de facto standard solutions    *
REM     *    for microcontrollers - completely free of charge!                  *
REM     *                                                                       *
REM     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
REM     *                                                                       *
REM     *    Thank you for using FreeRTOS, and thank you for your support!      *
REM     *                                                                       *
REM    ***************************************************************************
REM
REM
REM    This file is part of the FreeRTOS distribution.
REM
REM    FreeRTOS is free softwareREM you can redistribute it and/or modify it under
REM    the terms of the GNU General Public License (version 2) as published by the
REM    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
REM    >>>NOTE<<< The modification to the GPL is included to allow you to
REM    distribute a combined work that includes FreeRTOS without being obliged to
REM    provide the source code for proprietary components outside of the FreeRTOS
REM    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
REM    WITHOUT ANY WARRANTYREM without even the implied warranty of MERCHANTABILITY
REM    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
REM    more details. You should have received a copy of the GNU General Public
REM    License and the FreeRTOS license exception along with FreeRTOSREM if not it
REM    can be viewed here: http://www.freertos.org/a00114.html and also obtained
REM    by writing to Richard Barry, contact details for whom are available on the
REM    FreeRTOS WEB site.
REM
REM    1 tab == 4 spaces!
REM
REM    http://www.FreeRTOS.org - Documentation, latest information, license and
REM    contact details.
REM
REM    http://www.SafeRTOS.com - A version that is certified for use in safety
REM    critical systems.
REM
REM    http://www.OpenRTOS.com - Commercial support, development, porting,
REM    licensing and training services.
REM*/


@echo off
cls

SET PACKAGENAME=the FreeRTOS port for fedC and wizC

echo.
echo Hello, I'm the installationscript for %PACKAGENAME%.
echo.

:CHECKFEDC
  set FED=C:\Program Files\FED\PIC_C
  echo.
  echo I'm checking your system for fedC
  if not exist "%FED%" goto NOFEDC
  echo YES, I found a fedC-installation!
  goto FOUNDFED
:NOFEDC
  echo I could not find a fedC-installation.


:CHECKWIZC
  set FED=C:\Program Files\FED\PIXIE
  echo.
  echo I'm checking your system for wizC
  if not exist "%FED%" goto NOWIZC
  echo YES, I found a wizC-installation!
  goto FOUNDFED
:noWIZC
  echo I could not find a wizC-installation.


:ERROR
  echo.
  echo.
  echo I could not find a FED C-compiler installation on your system.
  echo.
  echo Perhaps I got confused because you installed fedC or wizC in a non-default directory.
  echo If this is the case, please change the path at the top of this install-script.
  echo After that rerun the script and I will be happy to try again.
  echo.
  goto ENDIT


:FOUNDFED
  echo.
  echo.

  set FEDLIBS=%FED%\Libs
  set FEDLIBSUSER=%FEDLIBS%\LibsUser

  if exist "%FEDLIBS%" goto INSTALL
  echo The FED installationdirectory "%FED%"
  echo contains no Libs subdirectory. This is weird!
  echo.
  echo Installation is aborted, sorry...
  goto ENDIT


:INSTALL
  echo I am about to install %PACKAGENAME%
  echo into directory %FEDLIBSUSER%
  echo.
  echo   Press 'enter'  to let me do my thing
  echo   Press 'ctrl-c' to stop me
  pause >nul
  echo.
  echo Installing...


:RESET_READONLY
  echo.
  echo   Removing ReadOnly attributes
  attrib -R "%FEDLIBSUSER%\libFreeRTOS\Modules\Croutine.c"     >nul
  attrib -R "%FEDLIBSUSER%\libFreeRTOS\Modules\Port.c"         >nul
  attrib -R "%FEDLIBSUSER%\libFreeRTOS\Modules\List.c"         >nul
  attrib -R "%FEDLIBSUSER%\libFreeRTOS\Modules\Queue.c"        >nul
  attrib -R "%FEDLIBSUSER%\libFreeRTOS\Modules\Tasks.c"        >nul
  attrib -R "%FEDLIBSUSER%\libFreeRTOS\Drivers\Tick\Tick.c"    >nul
  attrib -R "%FEDLIBSUSER%\libFreeRTOS\Drivers\Tick\isrTick.c" >nul
  attrib -R "%FEDLIBSUSER%\libFreeRTOS\Include\Portmacro.h"    >nul
  attrib -R "%FEDLIBSUSER%\libFreeRTOS\Include\Croutine.h"     >nul
  attrib -R "%FEDLIBSUSER%\libFreeRTOS\Include\List.h"         >nul
  attrib -R "%FEDLIBSUSER%\libFreeRTOS\Include\Portable.h"     >nul
  attrib -R "%FEDLIBSUSER%\libFreeRTOS\Include\Projdefs.h"     >nul
  attrib -R "%FEDLIBSUSER%\libFreeRTOS\Include\Queue.h"        >nul
  attrib -R "%FEDLIBSUSER%\libFreeRTOS\Include\Semphr.h"       >nul
  attrib -R "%FEDLIBSUSER%\libFreeRTOS\Include\Task.h"         >nul
  attrib -R "%FEDLIBSUSER%\FreeRTOS.h"                         >nul
  echo   Done

:CREATE_DIRECTORIES
  echo.
  echo   Creating directories (if necessary)...
  if not exist "%FEDLIBSUSER%"                          mkdir "%FEDLIBSUSER%"
  if not exist "%FEDLIBSUSER%\libFreeRTOS"              mkdir "%FEDLIBSUSER%\libFreeRTOS"
  if not exist "%FEDLIBSUSER%\libFreeRTOS\Drivers"      mkdir "%FEDLIBSUSER%\libFreeRTOS\Drivers"
  if not exist "%FEDLIBSUSER%\libFreeRTOS\Drivers\Tick" mkdir "%FEDLIBSUSER%\libFreeRTOS\Drivers\Tick"
  if not exist "%FEDLIBSUSER%\libFreeRTOS\Include"      mkdir "%FEDLIBSUSER%\libFreeRTOS\Include"
  if not exist "%FEDLIBSUSER%\libFreeRTOS\Modules"      mkdir "%FEDLIBSUSER%\libFreeRTOS\Modules"
  echo   Done


  echo.
  echo   Copying Files...
:COPY_MODULES
  echo     Modules...
  copy /V /Y "Port.c"                      "%FEDLIBSUSER%\libFreeRTOS\Modules\Port.c"         >nul
  copy /V /Y "..\..\..\Croutine.c"         "%FEDLIBSUSER%\libFreeRTOS\Modules\Croutine.c"     >nul
  copy /V /Y "..\..\..\List.c"             "%FEDLIBSUSER%\libFreeRTOS\Modules\List.c"         >nul
  copy /V /Y "..\..\..\Queue.c"            "%FEDLIBSUSER%\libFreeRTOS\Modules\Queue.c"        >nul
  copy /V /Y "..\..\..\Tasks.c"            "%FEDLIBSUSER%\libFreeRTOS\Modules\Tasks.c"        >nul

:COPY_DRIVERS
  echo     Drivers...
  copy /V /Y "Drivers\Tick\Tick.c"         "%FEDLIBSUSER%\libFreeRTOS\Drivers\Tick\Tick.c"    >nul
  copy /V /Y "Drivers\Tick\isrTick.c"      "%FEDLIBSUSER%\libFreeRTOS\Drivers\Tick\isrTick.c" >nul

:COPY_HEADERS
  echo     Headers...
  copy /V /Y "portmacro.h"                 "%FEDLIBSUSER%\libFreeRTOS\Include\Portmacro.h"    >nul
  copy /V /Y "..\..\..\include\Croutine.h" "%FEDLIBSUSER%\libFreeRTOS\Include\Croutine.h"     >nul
  copy /V /Y "..\..\..\include\List.h"     "%FEDLIBSUSER%\libFreeRTOS\Include\List.h"         >nul
  copy /V /Y "..\..\..\include\Portable.h" "%FEDLIBSUSER%\libFreeRTOS\Include\Portable.h"     >nul
  copy /V /Y "..\..\..\include\Projdefs.h" "%FEDLIBSUSER%\libFreeRTOS\Include\Projdefs.h"     >nul
  copy /V /Y "..\..\..\include\Queue.h"    "%FEDLIBSUSER%\libFreeRTOS\Include\Queue.h"        >nul
  copy /V /Y "..\..\..\include\Semphr.h"   "%FEDLIBSUSER%\libFreeRTOS\Include\Semphr.h"       >nul
  copy /V /Y "..\..\..\include\Task.h"     "%FEDLIBSUSER%\libFreeRTOS\Include\Task.h"         >nul
  copy /V /Y "addFreeRTOS.h" + "..\..\..\include\FreeRTOS.h" "%FEDLIBSUSER%\FreeRTOS.h"       >nul


  echo   Done


:SET_READONLY
  echo.
  echo   Setting files to ReadOnly
  attrib +R "%FEDLIBSUSER%\libFreeRTOS\Modules\Port.c"         >nul
  attrib +R "%FEDLIBSUSER%\libFreeRTOS\Modules\Croutine.c"     >nul
  attrib +R "%FEDLIBSUSER%\libFreeRTOS\Modules\List.c"         >nul
  attrib +R "%FEDLIBSUSER%\libFreeRTOS\Modules\Queue.c"        >nul
  attrib +R "%FEDLIBSUSER%\libFreeRTOS\Modules\Tasks.c"        >nul
  attrib +R "%FEDLIBSUSER%\libFreeRTOS\Drivers\Tick\Tick.c"    >nul
  attrib +R "%FEDLIBSUSER%\libFreeRTOS\Drivers\Tick\isrTick.c" >nul
  attrib +R "%FEDLIBSUSER%\libFreeRTOS\Include\Portmacro.h"    >nul
  attrib +R "%FEDLIBSUSER%\libFreeRTOS\Include\Croutine.h"     >nul
  attrib +R "%FEDLIBSUSER%\libFreeRTOS\Include\List.h"         >nul
  attrib +R "%FEDLIBSUSER%\libFreeRTOS\Include\Portable.h"     >nul
  attrib +R "%FEDLIBSUSER%\libFreeRTOS\Include\Projdefs.h"     >nul
  attrib +R "%FEDLIBSUSER%\libFreeRTOS\Include\Queue.h"        >nul
  attrib +R "%FEDLIBSUSER%\libFreeRTOS\Include\Semphr.h"       >nul
  attrib +R "%FEDLIBSUSER%\libFreeRTOS\Include\Task.h"         >nul
  attrib +R "%FEDLIBSUSER%\FreeRTOS.h"                         >nul
  echo   Done


:FINISHED
  echo.
  echo The installation of %PACKAGENAME% is completed.
  echo.
  echo Please review the installation instructions as additional libraries
  echo  and fedC/wizC configuration settings may be needed for FreeRTOS
  echo  to function correctly.

  goto ENDIT


:ENDIT
  echo.
  echo.
  echo Press 'enter' to close this window
  pause >nul
