Basic Usage
===========

The SSL/TLS protocol works securing an underlying TCP connection, this module
adds the secure layer around the Python standard library 
`socket <https://docs.python.org/3.6/library/socket.html>`_ module.

There are three different paths to secure a socket in this module:

* Using the top level function wolfssl.wrap_socket();
* Using the method wrap_socket() from a SSLContext instance;
* Creating an SSLSocket object from the scratch.

Note 1:
    It is possible to use the same SSLContext for multiple SSLSockets to save
    time and resources.

Note 2:
    Each path provides its own options for fine-tuning the securint parameters.
    Check them out in the API documentation.


Using the top level function wolfssl.wrap_socket()
--------------------------------------------------

.. code-block:: python

    >>> import socket
    >>> import wolfssl
    >>>
    >>> sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM, 0)
    >>>
    >>> secure_socket = wolfssl.wrap_socket(sock)
    >>>
    >>> secure_socket.connect(("www.python.org", 443))
    >>>
    >>> secure_socket.write(b"GET / HTTP/1.1\n\n")
    >>>
    >>> print(secure_socket.read())
    b'HTTP/1.1 500 Domain Not Found\r\nServer: Varnish\r\nRetry-After: 0\r\ncontent-type: text/html\r\nCache-Control: private, no-cache\r\nconnection: keep-alive\r\nContent-Length: 179\r\nAccept-Ranges: bytes\r\nDate: Sun, 05 Feb 2017 21:26:48 GMT\r\nVia: 1.1 varnish\r\nConnection: keep-alive\r\n\r\n\n<html>\n<head>\n<title>Fastly error: unknown domain </title>\n</head>\n<body>\nFastly error: unknown domain: . Please check that this domain has been added to a service.</body></html>'
    >>>
    >>> secure_socket.close()


Using the method wrap_socket() from a SSLContext instance
---------------------------------------------------------

.. code-block:: python

    >>> import socket
    >>> import wolfssl
    >>>
    >>> sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM, 0)
    >>>
    >>> context = wolfssl.SSLContext(wolfssl.PROTOCOL_TLSv1_2)
    >>>
    >>> secure_socket = context.wrap_socket(sock)
    >>>
    >>> secure_socket.connect(("www.python.org", 443))
    >>>
    >>> secure_socket.write(b"GET / HTTP/1.1\n\n")
    >>>
    >>> print(secure_socket.read())
    b'HTTP/1.1 500 Domain Not Found\r\nServer: Varnish\r\nRetry-After: 0\r\ncontent-type: text/html\r\nCache-Control: private, no-cache\r\nconnection: keep-alive\r\nContent-Length: 179\r\nAccept-Ranges: bytes\r\nDate: Sun, 05 Feb 2017 21:26:48 GMT\r\nVia: 1.1 varnish\r\nConnection: keep-alive\r\n\r\n\n<html>\n<head>\n<title>Fastly error: unknown domain </title>\n</head>\n<body>\nFastly error: unknown domain: . Please check that this domain has been added to a service.</body></html>'
    >>>
    >>> secure_socket.close()

Creating an SSLSocket object from the scratch
---------------------------------------------

.. code-block:: python

    >>> import socket
    >>> import wolfssl
    >>>
    >>> sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM, 0)
    >>>
    >>> secure_socket = wolfssl.SSLSocket(sock)
    >>>
    >>> secure_socket.connect(("www.python.org", 443))
    >>>
    >>> secure_socket.write(b"GET / HTTP/1.1\n\n")
    >>>
    >>> print(secure_socket.read())
    b'HTTP/1.1 500 Domain Not Found\r\nServer: Varnish\r\nRetry-After: 0\r\ncontent-type: text/html\r\nCache-Control: private, no-cache\r\nconnection: keep-alive\r\nContent-Length: 179\r\nAccept-Ranges: bytes\r\nDate: Sun, 05 Feb 2017 21:26:48 GMT\r\nVia: 1.1 varnish\r\nConnection: keep-alive\r\n\r\n\n<html>\n<head>\n<title>Fastly error: unknown domain </title>\n</head>\n<body>\nFastly error: unknown domain: . Please check that this domain has been added to a service.</body></html>'
    >>>
    >>> secure_socket.close()
