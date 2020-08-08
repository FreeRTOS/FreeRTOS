# test_ciphers.py
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
from wolfcrypt.ciphers import *
from wolfcrypt.utils   import t2b, h2b


class TestAes(unittest.TestCase):
    key    = "0123456789abcdef"
    IV     = "1234567890abcdef"
    plain  = t2b("now is the time ")
    cipher = h2b("959492575f4281532ccc9d4677a233cb")


    def setUp(self):
        self.aes = Aes.new(self.key, MODE_CBC, self.IV)


    def test_raises(self):
        # invalid key length
        self.assertRaises(ValueError, Aes.new, "key", MODE_CBC, self.IV)

        # invalid mode
        self.assertRaises(ValueError, Aes.new, self.key, MODE_ECB, self.IV)

        # invalid iv length
        self.assertRaises(ValueError, Aes.new, self.key, MODE_CBC, "IV")

        # invalid data length
        self.assertRaises(ValueError, self.aes.encrypt, "foo")
        self.assertRaises(ValueError, self.aes.decrypt, "bar")


    def test_single_encryption(self):
        assert self.aes.encrypt(self.plain) == self.cipher


    def test_multi_encryption(self):
        result = t2b("")
        segments = tuple(self.plain[i:i + self.aes.block_size] \
            for i in range(0, len(self.plain), self.aes.block_size))

        for segment in segments:
            result += self.aes.encrypt(segment)

        assert result == self.cipher


    def test_single_decryption(self):
        assert self.aes.decrypt(self.cipher) == self.plain


    def test_multi_decryption(self):
        result = t2b("")
        segments = tuple(self.cipher[i:i + self.aes.block_size] \
            for i in range(0, len(self.cipher), self.aes.block_size))

        for segment in segments:
            result += self.aes.decrypt(segment)

        assert result == self.plain


class TestRsaPrivate(unittest.TestCase):
    key = "3082025C02010002818100BC730EA849F374A2A9EF18A5DA559921F9C8ECB36D" \
        + "48E53535757737ECD161905F3ED9E4D5DF94CAC1A9D719DA86C9E84DC4613682" \
        + "FEABAD7E7725BB8D11A5BC623AA838CC39A20466B4F7F7F3AADA4D020EBB5E8D" \
        + "6948DC77C9280E22E96BA426BA4CE8C1FD4A6F2B1FEF8AAEF69062E5641EEB2B" \
        + "3C67C8DC2700F6916865A902030100010281801397EAE8387825A25C04CE0D40" \
        + "7C31E5C470CD9B823B5809863B665FDC3190F14FD5DB15DDDED73B9593311831" \
        + "0E5EA3D6A21A716E81481C4BCFDB8E7A866132DCFB55C1166D279224458BF1B8" \
        + "48B14B1DACDEDADD8E2FC291FBA5A96EF83A6AF1FD5018EF9FE7C3CA78EA56D3" \
        + "D3725B96DD4E064E3AC3D9BE72B66507074C01024100FA47D47A7C923C55EF81" \
        + "F041302DA3CF8F1CE6872705700DDF9835D6F18B382F24B5D084B6794F712994" \
        + "5AF0646AACE772C6ED4D59983E673AF3742CF9611769024100C0C1820D0CEBC6" \
        + "2FDC92F99D821A31E9E9F74BF282871CEE166AD11D188270F3C0B62FF6F3F71D" \
        + "F18623C84EEB8F568E8FF5BFF1F72BB5CC3DC657390C1B54410241009D7E05DE" \
        + "EDF4B7B2FBFC304B551DE32F0147966905CD0E2E2CBD8363B6AB7CB76DCA5B64" \
        + "A7CEBE86DF3B53DE61D21EEBA5F637EDACAB78D94CE755FBD71199C102401898" \
        + "1829E61E2739702168AC0A2FA172C121869538C65890A0579CBAE3A7B115C8DE" \
        + "F61BC2612376EFB09D1C44BE1343396717C89DCAFBF545648B38822CF2810240" \
        + "3989E59C195530BAB7488C48140EF49F7E779743E1B419353123759C3B44AD69" \
        + "1256EE0061641666D37C742B15B4A2FEBF086B1A5D3F9012B105863129DBD9E2"

    plain = t2b("Everyone gets Friday off.")


    def setUp(self):
        self.rsa = RsaPrivate(h2b(self.key))


    def test_raises(self):
        # invalid key
        self.assertRaises(WolfCryptError, RsaPrivate, 'key')


    def test_output_size(self):
        assert self.rsa.output_size == 1024 / 8


    def test_encrypt_decrypt(self):
        cipher = self.rsa.encrypt(self.plain)
        result = self.rsa.decrypt(cipher)

        assert len(cipher) == self.rsa.output_size == 1024 / 8
        assert self.plain == result


    def test_sign_verify(self):
        signature = self.rsa.sign(self.plain)
        result    = self.rsa.verify(signature)

        assert len(signature) == self.rsa.output_size == 1024 / 8
        assert self.plain == result


class TestRsaPublic(unittest.TestCase):
    prv = "3082025C02010002818100BC730EA849F374A2A9EF18A5DA559921F9C8ECB36D" \
        + "48E53535757737ECD161905F3ED9E4D5DF94CAC1A9D719DA86C9E84DC4613682" \
        + "FEABAD7E7725BB8D11A5BC623AA838CC39A20466B4F7F7F3AADA4D020EBB5E8D" \
        + "6948DC77C9280E22E96BA426BA4CE8C1FD4A6F2B1FEF8AAEF69062E5641EEB2B" \
        + "3C67C8DC2700F6916865A902030100010281801397EAE8387825A25C04CE0D40" \
        + "7C31E5C470CD9B823B5809863B665FDC3190F14FD5DB15DDDED73B9593311831" \
        + "0E5EA3D6A21A716E81481C4BCFDB8E7A866132DCFB55C1166D279224458BF1B8" \
        + "48B14B1DACDEDADD8E2FC291FBA5A96EF83A6AF1FD5018EF9FE7C3CA78EA56D3" \
        + "D3725B96DD4E064E3AC3D9BE72B66507074C01024100FA47D47A7C923C55EF81" \
        + "F041302DA3CF8F1CE6872705700DDF9835D6F18B382F24B5D084B6794F712994" \
        + "5AF0646AACE772C6ED4D59983E673AF3742CF9611769024100C0C1820D0CEBC6" \
        + "2FDC92F99D821A31E9E9F74BF282871CEE166AD11D188270F3C0B62FF6F3F71D" \
        + "F18623C84EEB8F568E8FF5BFF1F72BB5CC3DC657390C1B54410241009D7E05DE" \
        + "EDF4B7B2FBFC304B551DE32F0147966905CD0E2E2CBD8363B6AB7CB76DCA5B64" \
        + "A7CEBE86DF3B53DE61D21EEBA5F637EDACAB78D94CE755FBD71199C102401898" \
        + "1829E61E2739702168AC0A2FA172C121869538C65890A0579CBAE3A7B115C8DE" \
        + "F61BC2612376EFB09D1C44BE1343396717C89DCAFBF545648B38822CF2810240" \
        + "3989E59C195530BAB7488C48140EF49F7E779743E1B419353123759C3B44AD69" \
        + "1256EE0061641666D37C742B15B4A2FEBF086B1A5D3F9012B105863129DBD9E2"

    pub = "30819F300D06092A864886F70D010101050003818D0030818902818100BC730E" \
        + "A849F374A2A9EF18A5DA559921F9C8ECB36D48E53535757737ECD161905F3ED9" \
        + "E4D5DF94CAC1A9D719DA86C9E84DC4613682FEABAD7E7725BB8D11A5BC623AA8" \
        + "38CC39A20466B4F7F7F3AADA4D020EBB5E8D6948DC77C9280E22E96BA426BA4C" \
        + "E8C1FD4A6F2B1FEF8AAEF69062E5641EEB2B3C67C8DC2700F6916865A90203010001"

    plain = t2b("Everyone gets Friday off.")


    def setUp(self):
        self.private = RsaPrivate(h2b(self.prv))
        self.public  = RsaPublic(h2b(self.pub))


    def test_raises(self):
        # invalid key
        self.assertRaises(WolfCryptError, RsaPublic, 'key')


    def test_output_size(self):
        assert self.public.output_size == 1024 / 8


    def test_encrypt_decrypt(self):
        cipher = self.public.encrypt(self.plain)
        result = self.private.decrypt(cipher)

        assert len(cipher) == self.public.output_size == 1024 / 8
        assert self.plain == result


    def test_sign_verify(self):
        signature = self.private.sign(self.plain)
        result    = self.public.verify(signature)

        assert len(signature) == self.public.output_size == 1024 / 8
        assert self.plain == result
