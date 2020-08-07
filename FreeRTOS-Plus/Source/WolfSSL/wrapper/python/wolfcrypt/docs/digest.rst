Message Digests
===============

.. module:: wolfcrypt.hashes

A **message digest** is the output of a **cryptographic hash function**
containing a string of bytes created by a **one-way formula** using the
original message as input.

Message digests are designed to protect the integrity of a piece of data or
media to detect changes and alterations to any part of a message.


Hashing Classes
---------------

Interface
~~~~~~~~~

All Hashing Functions available in this module implements the following
interface:

.. autoclass:: _Hash
    :members:

SHA-1
~~~~~

.. attention::

    NIST has deprecated SHA-1 in favor of the SHA-2 variants. New applications
    are strongly suggested to use SHA-2 over SHA-1.

.. autoclass:: Sha

SHA-2 family
~~~~~~~~~~~~

.. autoclass:: Sha256


.. autoclass:: Sha384


.. autoclass:: Sha512


Example
-------

.. doctest::

    >>> from wolfcrypt.hashes import Sha256
    >>>
    >>> s = Sha256()
    >>> s.update(b'wolf')
    >>> s.update(b'crypt')
    >>> s.digest()
    b'\x96\xe0.{\x1c\xbc\xd6\xf1\x04\xfe\x1f\xdbFR\x02zU\x05\xb6\x86R\xb7\x00\x95\xc61\x8f\x9d\xce\r\x18D'
    >>> s.hexdigest()
    b'96e02e7b1cbcd6f104fe1fdb4652027a5505b68652b70095c6318f9dce0d1844'
    >>>
    >>> s.update(b'rocks')
    >>> s.hexdigest()
    b'e1a50df419d65715c48316bdc6a6f7f0485f4b26c1b107228faf17988b61c83f'
    >>>
    >>> Sha256(b'wolfcryptrocks').hexdigest()
    b'e1a50df419d65715c48316bdc6a6f7f0485f4b26c1b107228faf17988b61c83f'
    >>>
    >>> Sha256.new(b'wolfcryptrocks').hexdigest()
    b'e1a50df419d65715c48316bdc6a6f7f0485f4b26c1b107228faf17988b61c83f'
