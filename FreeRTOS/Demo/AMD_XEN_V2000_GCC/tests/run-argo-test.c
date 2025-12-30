/* run-argo-test
 *
 * Copyright (C) 2025 Advanced Micro Devices, Inc. or its affiliates. All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 *
 */

#include "FreeRTOS.h"
#include "FreeRTOS_CLI.h"
#include "stdint.h"
#include "stdlib.h"
#include "string.h"
#include "stdio.h"
#include "stdbool.h"
#include "cli.h"
#include <argo_module.h>

void send_to_app (domid_t dom, xen_argo_port_t aport, char msg[], size_t len);

/*********************** Core Setup *************************/

static BaseType_t  prvArgoRegistertest( char * pcWriteBuffer,
                                  	size_t xWriteBufferLen,
                                  	const char * pcCommandString )
{
    memset( pcWriteBuffer, 0x00, xWriteBufferLen );
    
    const char *pcParameter1;
    const char *pcParameter2;
    BaseType_t xParameter1Length, xParameter2Length;
    domid_t dom;
    xen_argo_port_t aport;

    pcParameter1 = FreeRTOS_CLIGetParameter(pcCommandString, 1, &xParameter1Length);
    if (pcParameter1 == NULL) {
        printk("FREERTOS: Please enter partner domid.\n");
        return 0;
    }

    pcParameter2 = FreeRTOS_CLIGetParameter(pcCommandString, 2, &xParameter2Length);
    if (pcParameter2 == NULL) {
        printk("FREERTOS: Please enter port number.\n");
	return 0;
    }

    char param1Str[16] = {0}, param2Str[16] = {0};
    memcpy(param1Str, pcParameter1, xParameter1Length);
    memcpy(param2Str, pcParameter2, xParameter2Length);

    dom = (domid_t)strtoul(param1Str, NULL, 10);
    aport = (xen_argo_port_t)strtoul(param2Str, NULL, 10);

    int ret = argo_ring_register(dom, aport, send_to_app);
    if (ret == -11)
	printk("Failed to allocate buffer for dom%u:%u.\n", dom, aport);
    else if (ret == 0)
	printk("Ring for dom%u:%u registered.\n", dom, aport);
    else
	printk("Failed to register argo ring for dom%u:%u (%d).\n", dom, aport, ret);

    return 0;
}


static connected_port = 0;
static connected_domain = 0;
static BaseType_t prvArgoConnecttest ( char * pcWriteBuffer,
                                     size_t xWriteBufferLen,
                                     const char * pcCommandString )
{
    memset( pcWriteBuffer, 0x00, xWriteBufferLen );

    const char *pcParameter1;
    const char *pcParameter2;
    BaseType_t xParameter1Length, xParameter2Length;
    domid_t dom;
    xen_argo_port_t aport;

    pcParameter1 = FreeRTOS_CLIGetParameter(pcCommandString, 1, &xParameter1Length);
    if (pcParameter1 == NULL) {
        printk("FREERTOS: Please enter partner domid.\n");
        return 0;
    }

    pcParameter2 = FreeRTOS_CLIGetParameter(pcCommandString, 2, &xParameter2Length);
    if (pcParameter2 == NULL) {
        printk("FREERTOS: Please enter port number.\n");
        return 0;
    }

    char param1Str[16] = {0}, param2Str[16] = {0};
    memcpy(param1Str, pcParameter1, xParameter1Length);
    memcpy(param2Str, pcParameter2, xParameter2Length);

    dom = (domid_t)strtoul(param1Str, NULL, 10);
    aport = (xen_argo_port_t)strtoul(param2Str, NULL, 10);

    int ret = sendv(dom, aport, NULL, 1);
    if (ret == -11)
	printk("No such ring found.\n");
    else if (ret < 0)
	printk("ERROR: Failed to send packet to Dom%u.\n", dom);
    else
        printk("Connected to port: %d\n", aport);
    connected_port = aport;
    connected_domain = dom;


    return 0;
}


static BaseType_t  prvArgoSendvtest ( char * pcWriteBuffer,
                                     size_t xWriteBufferLen,
                                     const char * pcCommandString )
{
    memset( pcWriteBuffer, 0x00, xWriteBufferLen );

    const char *pcParameters;
    static char msg[255];
    size_t cmdLength = strlen("run-ArgoSendv-test");
    size_t msgLen;

    pcParameters = pcCommandString + cmdLength;
    if (*pcParameters == ' ') {
        pcParameters++;
    }

    if (*pcParameters == '\0') {
        printk("FREERTOS: No message string given.\n");
	return 0;
    }

    msgLen = strlen(pcParameters);
    strncpy(msg, pcParameters, msgLen);
    msg[msgLen] = '\n';
    msg[msgLen+1] = '\0';

    int ret = sendv(connected_domain, connected_port, msg, 0);
    if (ret == -11)
	printk("No such ring found.\n");
    else if (ret < 0)
	printk("ERROR: Failed to send message to Dom0.\n");

    return 0;
}

void send_to_app (domid_t dom, xen_argo_port_t aport, char msg[], size_t len)
{
	printk("Message from dom%u on port-%u: ", dom, aport);
	for (int i = 0; i < len; i++)
		printk("%c", msg[i]);
}

static BaseType_t  prvArgoUnregistertest( char * pcWriteBuffer,
                                          size_t xWriteBufferLen,
                                          const char * pcCommandString )
{
    memset( pcWriteBuffer, 0x00, xWriteBufferLen );

    const char *pcParameter1;
    const char *pcParameter2;
    BaseType_t xParameter1Length, xParameter2Length;
    domid_t dom;
    xen_argo_port_t aport;

    pcParameter1 = FreeRTOS_CLIGetParameter(pcCommandString, 1, &xParameter1Length);
    if (pcParameter1 == NULL) {
        printk("FREERTOS: Please enter partner domid.\n");
        return 0;
    }

    pcParameter2 = FreeRTOS_CLIGetParameter(pcCommandString, 2, &xParameter2Length);
    if (pcParameter2 == NULL) {
        printk("FREERTOS: Please enter port number.\n");
        return 0;
    }

    char param1Str[16] = {0}, param2Str[16] = {0};
    memcpy(param1Str, pcParameter1, xParameter1Length);
    memcpy(param2Str, pcParameter2, xParameter2Length);

    dom = (domid_t)strtoul(param1Str, NULL, 10);
    aport = (xen_argo_port_t)strtoul(param2Str, NULL, 10);

    int ret = argo_ring_unregister(dom, aport);
    if (ret == -11)
	    printk("No such ring found.\n");
    else if (ret == 0)
	    printk("Ring for dom%u:%u unregistered.\n", dom, aport);
    else
	    printk("Failed to unregister argo ring for dom%u:%u (%d).\n", dom, aport, ret);

    return 0;
}

/*********************** FreeRTOS Command Registration *************************/

static const CLI_Command_Definition_t run_argoRegister_test =
{
    "run-ArgoRegister-test",
    "\r\nrun-ArgoRegister-test <Partner domid> <Port number>:\r\n Run ARGO Register test\r\n\r\n",
    prvArgoRegistertest,
    2
};

static const CLI_Command_Definition_t run_argoSendv_test =
{
    "run-ArgoSendv-test",
    "\r\nrun-ArgoSendv-test <message>:\r\n Send a message port no. 23357 to Dom0\r\n\r\n",
    prvArgoSendvtest,
    -1
};

static const CLI_Command_Definition_t run_argoConnect_test =
{
    "run-ArgoConnect-test",
    "\r\nrun-ArgoConnect-test <Partner domid> <Port number>:\r\n Send connection request to partner\r\n\r\n",
    prvArgoConnecttest,
    2
};

static const CLI_Command_Definition_t run_argoUnregister_test =
{
    "run-ArgoUnregister-test",
    "\r\nrun-ArgoUnregister-test <Partner domid> <Port number>:\r\n Run ARGO Unregister test\r\n\r\n",
    prvArgoUnregistertest,
    2
};

void register_argoRegister_test(void) {
    FreeRTOS_CLIRegisterCommand( &run_argoRegister_test );
}

void register_argoSendv_test(void) {
    FreeRTOS_CLIRegisterCommand( &run_argoSendv_test );
}

void register_argoConnect_test(void) {
    FreeRTOS_CLIRegisterCommand( &run_argoConnect_test );
}

void register_argoUnregister_test(void) {
    FreeRTOS_CLIRegisterCommand( &run_argoUnregister_test );
}
