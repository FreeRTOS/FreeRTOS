Client and Server Examples
==========================

SSL/TLS Client Example
----------------------

.. code-block:: python

    import socket
    import wolfssl
    
    CA_DATA = \
    """
    -----BEGIN CERTIFICATE-----
    MIIDxTCCAq2gAwIBAgIQAqxcJmoLQJuPC3nyrkYldzANBgkqhkiG9w0BAQUFADBs
    MQswCQYDVQQGEwJVUzEVMBMGA1UEChMMRGlnaUNlcnQgSW5jMRkwFwYDVQQLExB3
    d3cuZGlnaWNlcnQuY29tMSswKQYDVQQDEyJEaWdpQ2VydCBIaWdoIEFzc3VyYW5j
    ZSBFViBSb290IENBMB4XDTA2MTExMDAwMDAwMFoXDTMxMTExMDAwMDAwMFowbDEL
    MAkGA1UEBhMCVVMxFTATBgNVBAoTDERpZ2lDZXJ0IEluYzEZMBcGA1UECxMQd3d3
    LmRpZ2ljZXJ0LmNvbTErMCkGA1UEAxMiRGlnaUNlcnQgSGlnaCBBc3N1cmFuY2Ug
    RVYgUm9vdCBDQTCCASIwDQYJKoZIhvcNAQEBBQADggEPADCCAQoCggEBAMbM5XPm
    +9S75S0tMqbf5YE/yc0lSbZxKsPVlDRnogocsF9ppkCxxLeyj9CYpKlBWTrT3JTW
    PNt0OKRKzE0lgvdKpVMSOO7zSW1xkX5jtqumX8OkhPhPYlG++MXs2ziS4wblCJEM
    xChBVfvLWokVfnHoNb9Ncgk9vjo4UFt3MRuNs8ckRZqnrG0AFFoEt7oT61EKmEFB
    Ik5lYYeBQVCmeVyJ3hlKV9Uu5l0cUyx+mM0aBhakaHPQNAQTXKFx01p8VdteZOE3
    hzBWBOURtCmAEvF5OYiiAhF8J2a3iLd48soKqDirCmTCv2ZdlYTBoSUeh10aUAsg
    EsxBu24LUTi4S8sCAwEAAaNjMGEwDgYDVR0PAQH/BAQDAgGGMA8GA1UdEwEB/wQF
    MAMBAf8wHQYDVR0OBBYEFLE+w2kD+L9HAdSYJhoIAu9jZCvDMB8GA1UdIwQYMBaA
    FLE+w2kD+L9HAdSYJhoIAu9jZCvDMA0GCSqGSIb3DQEBBQUAA4IBAQAcGgaX3Nec
    nzyIZgYIVyHbIUf4KmeqvxgydkAQV8GK83rZEWWONfqe/EW1ntlMMUu4kehDLI6z
    eM7b41N5cdblIZQB2lWHmiRk9opmzN6cN82oNLFpmyPInngiK3BD41VHMWEZ71jF
    hS9OMPagMRYjyOfiZRYzy78aG6A9+MpeizGLYAiJLQwGXFK3xPkKmNEVX58Svnw2
    Yzi9RKR/5CYrCsSXaQ3pjOLAEFe4yHYSkVXySGnYvCoCWw9E1CAx2/S6cCZdkGCe
    vEsXCS+0yx5DaMkHJ8HSXPfqIbloEpw8nL+e/IBcm2PN7EeqJSdnoDfzAIJ9VNep
    +OkuE6N36B9K
    -----END CERTIFICATE-----
    """
    
    bind_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM, 0)
    
    context = wolfssl.SSLContext(wolfssl.PROTOCOL_TLSv1_2)
    
    context.verify_mode = wolfssl.CERT_REQUIRED
    context.load_verify_locations(cadata=CA_DATA)
    
    secure_socket = context.wrap_socket(bind_socket)
    
    secure_socket.connect(("www.python.org", 443))
    
    secure_socket.write(b"GET / HTTP/1.1\n\n")
    
    print(secure_socket.read())
    
    secure_socket.close()


SSL/TLS Server Example
----------------------

.. code-block:: python

    import socket
    import wolfssl
    
    bind_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM, 0)
    
    bind_socket.bind(("", 4433))
    bind_socket.listen(5)
    
    context = wolfssl.SSLContext(wolfssl.PROTOCOL_TLSv1_2, server_side=True)
    
    context.load_cert_chain("certs/server-cert.pem", "certs/server-key.pem")
    
    while True:
        try:
            secure_socket = None
            
            new_socket, from_addr = bind_socket.accept()
            
            secure_socket = context.wrap_socket(new_socket)
            
            print("Connection received from", from_addr)
            
            print("\n", secure_socket.read(), "\n")
            secure_socket.write(b"I hear you fa shizzle!")
            
        except KeyboardInterrupt:
            print()
            break
        
        finally:
            if secure_socket:
                secure_socket.close()
    
    bind_socket.close()
