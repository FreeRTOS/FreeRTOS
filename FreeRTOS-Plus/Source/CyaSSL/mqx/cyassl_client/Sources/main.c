/* 
 * main.c 
 */

#include "main.h"
#include "util.h"

#if !BSPCFG_ENABLE_IO_SUBSYSTEM
#error This application requires BSPCFG_ENABLE_IO_SUBSYSTEM defined \
    non-zero in user_config.h. Please recompile BSP with this option.
#endif

#ifndef BSP_DEFAULT_IO_CHANNEL_DEFINED
#error This application requires BSP_DEFAULT_IO_CHANNEL to be not NULL. \
    Please set corresponding BSPCFG_ENABLE_TTYx to non-zero in \
    user_config.h and recompile BSP with this option.
#endif

#if defined BSP_SDCARD_ESDHC_CHANNEL
#if ! BSPCFG_ENABLE_ESDHC
#error This application requires BSPCFG_ENABLE_ESDHC defined non-zero in \
    user_config.h. Please recompile libraries with this option.
#endif

#elif defined BSP_SDCARD_SDHC_CHANNEL

#if ! BSPCFG_ENABLE_SDHC
#error This application requires BSPCFG_ENABLE_SDHC defined non-zero in \
    user_config.h. Please recompile libraries with this option.
#endif

#endif

#if defined (BSP_SDCARD_SPI_CHANNEL)
    #define SDCARD_COM_CHANNEL BSP_SDCARD_SPI_CHANNEL
#elif defined (BSP_SDCARD_ESDHC_CHANNEL)
    #define SDCARD_COM_CHANNEL BSP_SDCARD_ESDHC_CHANNEL
#elif defined (BSP_SDCARD_SDHC_CHANNEL)
    #define SDCARD_COM_CHANNEL BSP_SDCARD_SDHC_CHANNEL
#else
    #error "SDCARD low level communication device not defined!"
#endif

TASK_TEMPLATE_STRUCT MQX_template_list[] = 
{ 
/*  Task number, Entry point, Stack, Pri, String, Auto? */
   {MAIN_TASK,   Main_task,   20000,  9,   "main", MQX_AUTO_START_TASK},
   {0,           0,           0,     0,   0,      0,                 }
};

/*TASK*-----------------------------------------------------
* 
* Task Name    : Main_task
* Comments     :
*    This task sets up the SD card and Ethernet devices,
*    then starts the example CyaSSL client.  The example
*    CyaSSL client connects to a server over SSL and sends 
*    a simple HTTP GET message, then prints out the reply 
*    from the server.
*
*    To change the IP address and port of the server,
*    change the yasslIP and yasslPort variables in
*    client_test(). Note that yasslIP needs to be given
*    in hexadecimal.
*
*END*-----------------------------------------------------*/

void Main_task(uint_32 initial_data)
{	
	int          ret = 0;
	_mqx_int     error_code, bytes;
	_mqx_uint    param;
	_mqx_uint	 sz;
	MQX_FILE_PTR com_handle, sdcard_handle, filesystem_handle, partman_handle;
	MQX_FILE_PTR cert_file = NULL;
	char         filesystem_name[] = "a:";
	char         partman_name[] = "pm:";
    const char*  fileName = "a:\certs\\client-key.der";
	    
    printf("Starting client example... \n"); 

    ret = sdcard_open(&com_handle, &sdcard_handle, &partman_handle,
			&filesystem_handle, partman_name, filesystem_name);
    
	if (ret != 0) {
		printf("error: sdcard_open(), ret = %d\n", ret);
		_mqx_exit(1);
	}
	printf("SD card installed to %s\n", filesystem_name);

	setup_ethernet();
	client_test();

	ret = sdcard_close(&sdcard_handle, &partman_handle, &filesystem_handle,
			partman_name, filesystem_name);

	if (ret != 0) {
		printf("error: sdcard_close(), ret = %d\n", ret);
		_mqx_exit(1);
	}
	printf("SD card uninstalled.\n");
   
   _mqx_exit(0);
}

void setup_ethernet(void) {
	
	int	error;
	_enet_handle	ehandle;	/* for Ethernet driver */
	_rtcs_if_handle	ihandle;
	_enet_address	address;
	
	error = RTCS_create();
	if (error) {
		err_sys("failed to create RTCS");
	}
	
	ENET_get_mac_address(BSP_DEFAULT_ENET_DEVICE, ENET_IPADDR, address);
	
	/* Set up the Ethernet driver */
	error = ENET_initialize(BSP_DEFAULT_ENET_DEVICE, address, 0, &ehandle);
	if (error)
		err_sys("failed to initialize Ethernet driver");
	
	error = RTCS_if_add(ehandle, RTCS_IF_ENET, &ihandle);
	if (error)
		err_sys("failed to add interface for Ethernet");
	
	error = RTCS_if_bind(ihandle, ENET_IPADDR, ENET_IPMASK);
	if (error)
		err_sys("failed to bind interface for Ethernet");
	
#ifdef GATE_IPADDR
	RTCS_gate_add(GATE_IPADDR, INADDR_ANY, INADDR_ANY);
#endif
	
	printf("Ethernet device %d bound to %X\n", BSP_DEFAULT_ENET_DEVICE, 
            ENET_IPADDR);
}

void client_test(void) {
	
	char msg[64];
	char reply[1024];
	int sockfd, input;
	int ret = 0, msgSz = 0;
	struct sockaddr_in	servaddr;
	CYASSL_CTX*			ctx;
	CYASSL*				ssl;
	
	long yasslIP = 0xa9fea662;	/* 169.254.166.98 */
	long yasslPort = 11111;
	
	CyaSSL_Debugging_ON();
	CyaSSL_Init();
	
	ctx = CyaSSL_CTX_new(CyaSSLv3_client_method());
	
	if (ctx == 0)
		err_sys("setting up ctx");
	
	ret = CyaSSL_CTX_use_certificate_file(ctx, clientCert, SSL_FILETYPE_PEM);
	if (ret != SSL_SUCCESS) {
		err_sys("can't load client cert file, check file");
	}
		
	ret = CyaSSL_CTX_use_PrivateKey_file(ctx, clientKey, SSL_FILETYPE_PEM);
	if (ret != SSL_SUCCESS) {
		err_sys("can't load client key file, check file");
	}

	ret = CyaSSL_CTX_load_verify_locations(ctx, caCert, 0);
	if (ret != SSL_SUCCESS) {
		err_sys("can't load CA cert file, check file");
	}
	
	/* create socket descriptor */
	sockfd = socket(AF_INET, SOCK_STREAM, 0);
	if (sockfd == RTCS_SOCKET_ERROR) {
		err_sys("socket creation failed");
	} else {
		printf("socket created successfully\n");
	}

    /* Unlike most TCP/IP stacks, RTCS requires that sin_port and
     * sin_addr needs to be in Host Byte Order, not Network Byte Order.
     * This means we shouldn't use htons() when setting these values. */    
	memset((char*)&servaddr, 0, sizeof(servaddr));
	servaddr.sin_family = AF_INET;
	servaddr.sin_port = yasslPort;
	servaddr.sin_addr.s_addr = yasslIP;
	
	ret = connect(sockfd, &servaddr, sizeof(servaddr));
	if (ret != RTCS_OK) {
		err_sys("connect() failed");
	} else {
		printf("Connected to %lx, port %d.\n", servaddr.sin_addr.s_addr,
				servaddr.sin_port);
	}
	
	if( (ssl = CyaSSL_new(ctx)) == NULL) {
		err_sys("CyaSSL_new failed");
	}
	
	CyaSSL_set_fd(ssl, sockfd);
	
	ret = CyaSSL_connect(ssl);
	if (ret != SSL_SUCCESS)
		err_sys("CyaSSL_connect failed");
	
	printf("CyaSSL_connect() ok, sending GET...\n");
	msgSz = 28;
	strncpy(msg, "GET /index.html HTTP/1.0\r\n\r\n", msgSz);
	if (CyaSSL_write(ssl, msg, msgSz) != msgSz)
		err_sys("CyaSSL_write() failed");
	
	input = CyaSSL_read(ssl, reply, sizeof(reply)-1);
	if (input > 0) {
		reply[input] = 0;
		printf("Server response: %s\n", reply);
		
		while(1) {
			input = CyaSSL_read(ssl, reply, sizeof(reply)-1);
			if (input > 0) {
				reply[input] = 0;
				printf("%s\n", reply);
			} else {
				break;
			}
		}
	}
	
	CyaSSL_shutdown(ssl);
	CyaSSL_free(ssl);
	CyaSSL_CTX_free(ctx);
	CyaSSL_Cleanup();
}

/* EOF */
