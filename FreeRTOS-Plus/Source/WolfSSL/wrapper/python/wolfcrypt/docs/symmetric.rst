Symmetric Key Algorithms
========================

.. module:: wolfcrypt.ciphers

**Symmetric key algorithms** are encryption algorithms that use the **same
cryptographic keys** for both encryption and decryption of data.
This operation is also known as **Symmetric Key Encryption**.

``wolfcrypt`` provides access to the following **Symmetric Key Ciphers**:

Symmetric Key Encryption Classes
--------------------------------

Interface
~~~~~~~~~

All **Symmetric Key Ciphers** available in this module implements the following
interface:

.. autoclass:: _Cipher
    :members:

Classes
~~~~~~~

.. autoclass:: Aes


Example
-------

.. doctest::

    >>> from wolfcrypt.ciphers import Aes, MODE_CBC
    >>>
    >>> cipher = Aes(b'0123456789abcdef', MODE_CBC, b'1234567890abcdef')
    >>> ciphertext = cipher.encrypt('now is the time ')
    >>> ciphertext
    b'\x95\x94\x92W_B\x81S,\xcc\x9dFw\xa23\xcb'
    >>> cipher.decrypt(ciphertext)
    b'now is the time '
