Message Authentication Codes
============================

.. module:: wolfcrypt.hashes

A **message authentication code** (MAC) is a short piece of information used
to authenticate a message — in other words, to confirm that the message came
from the stated sender (its authenticity) and has not been changed in transit
(its integrity).

``wolfcrypt`` implements the **Hash-based message authentication code** (HMAC),
which uses a cryptographic hash function coupled with a secret key to produce
**message authentication codes**.


Hmac Classes
------------

Interface
~~~~~~~~~

All Hmac classes available in this module implements the following
interface:

.. autoclass:: _Hmac
    :members:
    :inherited-members:

SHA-1
~~~~~

.. attention::

    NIST has deprecated SHA-1 in favor of the SHA-2 variants. New applications
    are strongly suggested to use SHA-2 over SHA-1.

.. autoclass:: HmacSha

SHA-2 family
~~~~~~~~~~~~

.. autoclass:: HmacSha256


.. autoclass:: HmacSha384


.. autoclass:: HmacSha512


Example
-------

.. doctest::

    >>> from wolfcrypt.hashes import HmacSha256
    >>>
    >>> h = HmacSha256('secret')
    >>> h.update("wolf")
    >>> h.update("crypt")
    >>> h.digest()
    b'\x18\xbf*\t9\xa2o\xdf\\\xc8\xe0\xc2U\x94,\x8dY\x02;\x1c<Q\xdf\x8d\xdb\x863\xfb\xc1f#o'
    >>> h.hexdigest()
    b'18bf2a0939a26fdf5cc8e0c255942c8d59023b1c3c51df8ddb8633fbc166236f'
    >>>
    >>> h.update("rocks")
    >>> h.hexdigest()
    b'85dc8c1995d20b17942d52773d8a597d028ad958e5736beafb59a4742f63889e'
    >>>
    >>> HmacSha256('secret', 'wolfcryptrocks').hexdigest()
    b'85dc8c1995d20b17942d52773d8a597d028ad958e5736beafb59a4742f63889e'
    >>>
    >>> HmacSha256.new('secret', 'wolfcryptrocks').hexdigest()
    b'85dc8c1995d20b17942d52773d8a597d028ad958e5736beafb59a4742f63889e'
