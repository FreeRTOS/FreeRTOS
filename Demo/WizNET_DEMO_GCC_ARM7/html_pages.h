/*
    FreeRTOS V6.0.3 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public 
    License and the FreeRTOS license exception along with FreeRTOS; if not it 
    can be viewed here: http://www.freertos.org/a00114.html and also obtained 
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/

#ifndef HTML_PAGES_H
#define HTML_PAGES_H

/* Simply defines some strings that get sent as HTML pages. */

const char * const cSamplePageFirstPart =
"HTTP/1.0 200 OK\r\n"
"Content-type: text/html\r\n"
"\r\n"																				 
"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0 Transitional//EN\">\r\n"
"<html>\r\n"
"<head>\r\n"
"<title>FreeRTOS - Live embedded WEB server demo</title>\r\n"
"</head>\r\n"
"<body BGCOLOR=\"#CCCCFF\">\r\n"
"<font face=\"arial\">\r\n"
"<small><b><a href=\"http://www.freertos.org\" target=\"_top\">FreeRTOS Homepage</a></b></small><p>"
"<H1>Embedded WEB Server<br><small>On the FreeRTOS real time kernel</small></h1>\r\n"
"<p>\r\n"
"<b>This demo is now using FreeRTOS.org V4.x.x!</b><p>"
"This page is being served by the FreeRTOS embedded WEB server running on an ARM7 microcontroller.\r\n<pre>";

const char * const cSamplePageSecondPart =
"</pre>"
"If all is well you should see that 18 tasks are executing - 15 standard demo tasks, the embedded WEB server"
" task, the error check task and the idle task.<p>"
"</font>\r\n"
"</body>\r\n"
"</html>\r\n";



#endif

