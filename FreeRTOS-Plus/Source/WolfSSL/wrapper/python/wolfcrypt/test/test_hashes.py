# test_hashes.py
#
# Copyright (C) 2006-2020 wolfSSL Inc.
#
# This file is part of wolfSSL.
#
# wolfSSL is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.
#
# wolfSSL is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
#/
import unittest
from wolfcrypt.hashes import *
from wolfcrypt.utils  import t2b, h2b


class TestSha(unittest.TestCase):
    _class = Sha
    digest = t2b("1b6182d68ae91ce0853bd9c6b6edfedd4b6a510d")


    def setUp(self):
        self.hash = self._class()


    def test_new(self):
        # update inside constructor
        assert self._class.new("wolfcrypt").hexdigest() == self.digest


    def test_hash_update_001(self):
        self.hash.update("wolfcrypt")

        assert self.hash.hexdigest() == self.digest
        assert self.hash.digest() == h2b(self.digest)


    def test_hash_update_002(self):
        self.hash.update("wolf")
        self.hash.update("crypt")

        assert self.hash.hexdigest() == self.digest
        assert self.hash.digest() == h2b(self.digest)


    def test_hash_copy(self):
        copy = self.hash.copy()

        assert self.hash.hexdigest() == copy.hexdigest()

        self.hash.update("wolfcrypt")

        assert self.hash.hexdigest() != copy.hexdigest()

        copy.update("wolfcrypt")

        assert self.hash.hexdigest() == copy.hexdigest() == self.digest


class TestSha256(TestSha):
    _class = Sha256
    digest = t2b("96e02e7b1cbcd6f104fe1fdb4652027a" \
                + "5505b68652b70095c6318f9dce0d1844")


class TestSha384(TestSha):
    _class = Sha384
    digest = t2b("4c79d80531203a16f91bee325f18c6aada47f9382fe44fc1" \
                + "1f92917837e9b7902f5dccb7d3656f667a1dce3460bc884b")


class TestSha512(TestSha):
    _class = Sha512
    digest = t2b("88fcf67ffd8558d713f9cedcd852db47" \
                + "9e6573f0bd9955610a993f609637553c" \
                + "e8fff55e644ee8a106aae19c07f91b3f" \
                + "2a2a6d40dfa7302c0fa6a1a9a5bfa03f")


_HMAC_KEY = "python"


class TestHmacSha(unittest.TestCase):
    _class = HmacSha
    digest = t2b("5dfabcfb3a25540824867cd21f065f52f73491e0")


    def setUp(self):
        self.hash = self._class(_HMAC_KEY)


    def test_new(self):
        # update inside constructor
        assert self._class.new(_HMAC_KEY,"wolfcrypt").hexdigest() == self.digest


    def test_hash_update_001(self):
        self.hash.update("wolfcrypt")

        assert self.hash.hexdigest() == self.digest


    def test_hash_update_002(self):
        self.hash.update("wolf")
        self.hash.update("crypt")

        assert self.hash.hexdigest() == self.digest


    def test_hash_copy(self):
        copy = self.hash.copy()

        assert self.hash.hexdigest() == copy.hexdigest()

        self.hash.update("wolfcrypt")

        assert self.hash.hexdigest() != copy.hexdigest()

        copy.update("wolfcrypt")

        assert self.hash.hexdigest() == copy.hexdigest() == self.digest


class TestHmacSha256(TestHmacSha):
    _class = HmacSha256
    digest = t2b("4b641d721493d80f019d9447830ebfee" \
                + "89234a7d594378b89f8bb73873576bf6")


class TestHmacSha384(TestHmacSha):
    _class = HmacSha384
    digest = t2b("e72c72070c9c5c78e3286593068a510c1740cdf9dc34b512" \
                + "ccec97320295db1fe673216b46fe72e81f399a9ec04780ab")


class TestHmacSha512(TestHmacSha):
    _class = HmacSha512
    digest = t2b("c7f48db79314fc2b5be9a93fd58601a1" \
                + "bf42f397ec7f66dba034d44503890e6b" \
                + "5708242dcd71a248a78162d815c685f6" \
                + "038a4ac8cb34b8bf18986dbd300c9b41")
