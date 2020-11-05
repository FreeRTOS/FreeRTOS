Building a network transport implementation:

1. Go into the sub directory for the TCP/IP stack you are using (e.g. freertos_plus_tcp).
2. Build the wrapper file located in the directory (i.e. sockets_wrapper.c).
3. Select an additional folder based on the TLS stack you are using (e.g. using_mbedtls), or the using_plaintext folder if not using TLS.
4. Build and include all files from the selected folder.
