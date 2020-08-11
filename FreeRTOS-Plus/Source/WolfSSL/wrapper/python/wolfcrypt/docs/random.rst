Random Number Generation
========================

A **cryptographically secure pseudo-random number generator** (CSPRNG) is a
**pseudo-random number generator** (PRNG) with properties that make it suitable
for use in cryptography.

Using the standard random module APIs for cryptographic keys or initialization
vectors can result in major security issues depending on the algorithms in use.

``wolfcrypt`` provides the following CSPRNG implementation:

.. module:: wolfcrypt.random

.. autoclass:: Random
    :members:


Example
-------

    >>> from wolfcrypt.random import Random
    >>>
    >>> r = Random()
    >>> b = r.byte()
    >>> b # doctest: +SKIP
    b'\x8c'
    >>> b16 = r.bytes(16)
    >>> b16 # doctest: +SKIP
    b']\x93nk\x95\xbc@\xffX\xab\xdcB\xda\x11\xf7\x03'
