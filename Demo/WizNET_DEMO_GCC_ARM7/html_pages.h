/*
	FreeRTOS.org V4.7.2 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************

	Please ensure to read the configuration and relevant port sections of the 
	online documentation.

	+++ http://www.FreeRTOS.org +++
	Documentation, latest information, license and contact details.  

	+++ http://www.SafeRTOS.com +++
	A version that is certified for use in safety critical systems.

	+++ http://www.OpenRTOS.com +++
	Commercial support, development, porting, licensing and training services.

	***************************************************************************
*/

#ifndef HTML_PAGES_H
#define HTML_PAGES_H

/* Simply defines some strings that get sent as HTML pages. */

const portCHAR * const cSamplePageFirstPart =
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

const portCHAR * const cSamplePageSecondPart =
"</pre>"
"If all is well you should see that 18 tasks are executing - 15 standard demo tasks, the embedded WEB server"
" task, the error check task and the idle task.<p>"
"</font>\r\n"
"</body>\r\n"
"</html>\r\n";



#endif

