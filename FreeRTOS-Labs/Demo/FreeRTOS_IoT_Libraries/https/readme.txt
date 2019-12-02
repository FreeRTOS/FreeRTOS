See https://freertos.org/https/ for further information.

Contains projects that demonstrate the IoT HTTPS library.

- Securing HTTPS Communication -
The Hypertext Transfer Protocol (HTTP) is a widely used protocol for application
such as home media to interact with web servers. The Hypertext Transfer Protocol
Secure (HTTPS) is an extension to HTTP, adding secure element to the connection.
HTTPS is encrypted with Transport Layer Security (TLS), which also requires server
authentication. In addition to server authentication, mutual authentication
authenticates the identity of both the server and the client.

- Pre-configured HTTPS Example Projects -
The examples contained in subdirectories from here demonstrate the concepts
described above one at a time.  The first example demonstrates plain text
HTTP (insecure) communication, the second example builds on the first to
introduce weak server authentication, and the third example builds on the second to
introduce strong mutual authentication.  Note:  It is our recommendation to always
use strong mutual authentication in any Internet of Things (IoT) application.  The
plain text project is only provided to validate HTTP communication can be
established prior to introducing encryption and authentication, and to allow the
HTTP packets to be observed using a network packet sniffer such as Wireshark for
those who wish to do so.  The first two projects are in no way intended to be
examples suitable for production use.
