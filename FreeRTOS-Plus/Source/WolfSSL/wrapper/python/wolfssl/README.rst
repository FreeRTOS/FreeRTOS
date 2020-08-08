Welcome
=======

``wolfssl Python`` is a Python module that encapsulates ``wolfssl C``, a `lightweight C-language-based SSL/TLS library <https://wolfssl.com/wolfSSL/Products-wolfssl.html>`_ targeted for embedded, RTOS, or
resource-constrained environments primarily because of its small size, speed,
and portability.

Installation
============

In order to use ``wolfssl Python``, you'll also need to install ``wolfssl C``.

Mac OSX
-------

Installing from ``homebrew`` and ``pip`` package managers:

.. code-block:: shell

    # wolfssl C installation
    brew install wolfssl

    # wolfssl Python installation
    sudo -H pip install wolfssl

Installing from ``source code``:

.. code-block:: shell

    # wolfssl C installation
    git clone https://github.com/wolfssl/wolfssl.git
    cd wolfssl/
    ./autogen.sh
    ./configure --enable-sha512
    make
    sudo make install

    # wolfssl Python installation
    cd wrapper/python/wolfssl
    sudo make install


Linux
-----

.. code-block:: shell

    # dependencies installation
    sudo apt-get update
    sudo apt-get install -y git autoconf libtool
    sudo apt-get install -y python-dev python3-dev python-pip libffi-dev

    # wolfssl C installation
    git clone https://github.com/wolfssl/wolfssl.git
    cd wolfssl/
    ./autogen.sh
    ./configure --enable-sha512
    make
    sudo make install

    sudo ldconfig

    # wolfssl Python installation
    sudo -H pip install wolfssl


Testing
=======

To run the tox tests in the source code, you'll need ``tox`` and a few other
requirements. The source code relies at **WOLFSSL_DIR/wrapper/python/wolfssl**
where **WOLFSSL_DIR** is the path of ``wolfssl C``'s source code.

1. Make sure that the testing requirements are installed:

.. code-block:: shell

    sudo -H pip install -r requirements-testing.txt


2. Run ``make check``:

.. code-block:: console

    $ make check
    ...
    _________________________________ summary _________________________________
    py27: commands succeeded
    SKIPPED: py34: InterpreterNotFound: python3.4
    py35: commands succeeded
    py36: commands succeeded
    congratulations :)

Note: the test is performed using multiple versions of python. If you are
missing a version the test will be skipped with an **InterpreterNotFound
error**.
