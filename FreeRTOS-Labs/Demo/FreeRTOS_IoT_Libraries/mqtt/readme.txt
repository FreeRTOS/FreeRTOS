See https://freertos.org/mqtt/ for further information.

Contains projects that demonstrate the IoT MQTT library.

- Securing MQTT Communication -
Internet of Things use cases require MQTT communications to be secured, but secure
authentication and encryption are not part of the MQTT specification.  It is
therefore common to use MQTT in combination with Transport Layer Security (TLS).
TLS encrypts data sent across a network and enables the data's destination to be
authenticated.  'Server authentication' is when the MQTT client authenticates the
identity of the MQTT broker.  'Mutual authentication' is when the MQTT broker also
authenticates the identity of the MQTT client.


- Pre-configured MQTT Example Projects -
The examples contained in subdirectories from here demonstrate the concepts
described above one at a time.  The first example demonstrates plain text
(unencrypted) MQTT communication, the second example builds on the first to
introduce weak server authentication, and the third example builds on the second to
introduce strong mutual authentication.  Note:  It is our recommendation to always
use strong mutual authentication in any Internet of Things (IoT) application.  The
plain text project is only provided to validate MQTT communication can be
established prior to introducing encryption and authentication, and to allow the
MQTT packets to be observed using a network packet sniffer such as Wireshark for
those who wish to do so.  The first two projects are in no way intended to be
examples suitable for production use.
