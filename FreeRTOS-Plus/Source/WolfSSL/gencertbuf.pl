#!/usr/bin/perl

# gencertbuf.pl
# version 1.1
# Updated 07/01/2014
#
# Copyright (C) 2006-2015 wolfSSL Inc.
#

use strict;
use warnings;

# ---- SCRIPT SETTINGS -------------------------------------------------------

# output C header file to write cert/key buffers to
my $outputFile = "./wolfssl/certs_test.h";

# ecc keys and certs to be converted
# Used with HAVE_ECC && USE_CERT_BUFFERS_256

my @fileList_ecc = (
        [ "./certs/ecc-client-key.der",    "ecc_clikey_der_256" ],
        [ "./certs/ecc-client-keyPub.der", "ecc_clikeypub_der_256" ],
        [ "./certs/client-ecc-cert.der",   "cliecc_cert_der_256" ],
        [ "./certs/ecc-key.der",           "ecc_key_der_256" ],
        [ "./certs/ecc-keyPub.der",        "ecc_key_pub_der_256" ],
        [ "./certs/server-ecc-comp.der",   "serv_ecc_comp_der_256" ],
        [ "./certs/server-ecc-rsa.der",    "serv_ecc_rsa_der_256" ],
        [ "./certs/server-ecc.der",        "serv_ecc_der_256" ],
        [ "./certs/ca-ecc-key.der",        "ca_ecc_key_der_256" ],
        [ "./certs/ca-ecc-cert.der",       "ca_ecc_cert_der_256" ],
        [ "./certs/ca-ecc384-key.der",     "ca_ecc_key_der_384" ],
        [ "./certs/ca-ecc384-cert.der",    "ca_ecc_cert_der_384" ]
        );


# ed25519 keys and certs
# Used with HAVE_ED25519 define.
my @fileList_ed = (
        [ "./certs/ed25519/server-ed25519.der",     "server_ed25519_cert" ],
        [ "./certs/ed25519/server-ed25519-key.der", "server_ed25519_key" ],
        [ "./certs/ed25519/ca-ed25519.der",         "ca_ed25519_cert" ],
        [ "./certs/ed25519/client-ed25519.der",     "client_ed25519_cert" ],
        [ "./certs/ed25519/client-ed25519-key.der", "client_ed25519_key" ]
        );

# 1024-bit certs/keys to be converted
# Used with USE_CERT_BUFFERS_1024 define.

my @fileList_1024 = (
        [ "./certs/1024/client-key.der", "client_key_der_1024" ],
        [ "./certs/1024/client-keyPub.der", "client_keypub_der_1024" ],
        [ "./certs/1024/client-cert.der", "client_cert_der_1024" ],
        [ "./certs/1024/dh1024.der", "dh_key_der_1024" ],
        [ "./certs/1024/dsa1024.der", "dsa_key_der_1024" ],
        [ "./certs/1024/rsa1024.der", "rsa_key_der_1024" ],
        [ "./certs/1024/ca-key.der", "ca_key_der_1024"],
        [ "./certs/1024/ca-cert.der", "ca_cert_der_1024" ],
        [ "./certs/1024/server-key.der", "server_key_der_1024" ],
        [ "./certs/1024/server-cert.der", "server_cert_der_1024" ]
        );

# 2048-bit certs/keys to be converted
# Used with USE_CERT_BUFFERS_2048 define.
my @fileList_2048 = (
        [ "./certs/client-key.der", "client_key_der_2048" ],
        [ "./certs/client-keyPub.der", "client_keypub_der_2048" ],
        [ "./certs/client-cert.der", "client_cert_der_2048" ],
        [ "./certs/dh2048.der", "dh_key_der_2048" ],
        [ "./certs/dsa2048.der", "dsa_key_der_2048" ],
        [ "./certs/rsa2048.der", "rsa_key_der_2048" ],
        [ "./certs/ca-key.der", "ca_key_der_2048" ],
        [ "./certs/ca-cert.der", "ca_cert_der_2048" ],
        [ "./certs/ca-cert-chain.der", "ca_cert_chain_der" ],
        [ "./certs/server-key.der", "server_key_der_2048" ],
        [ "./certs/server-cert.der", "server_cert_der_2048" ]
        );

# 3072-bit certs/keys to be converted
# Used with USE_CERT_BUFFERS_3072 define.
my @fileList_3072 = (
        [ "./certs/dh3072.der", "dh_key_der_3072" ],
        [ "./certs/dsa3072.der", "dsa_key_der_3072" ],
        [ "./certs/rsa3072.der", "rsa_key_der_3072" ],
        [ "./certs/3072/client-key.der", "client_key_der_3072" ],
        [ "./certs/3072/client-keyPub.der", "client_keypub_der_3072" ],
        [ "./certs/3072/client-cert.der", "client_cert_der_3072" ],
        );

# 4096-bit certs/keys to be converted
# Used with USE_CERT_BUFFERS_4096 define.
my @fileList_4096 = (
        [ "./certs/4096/client-key.der", "client_key_der_4096" ],
        [ "./certs/4096/client-keyPub.der", "client_keypub_der_4096" ],
        [ "./certs/4096/client-cert.der", "client_cert_der_4096" ],
        [ "./certs/dh4096.der", "dh_key_der_4096" ],
        );

# ----------------------------------------------------------------------------

my $num_ecc = @fileList_ecc;
my $num_ed = @fileList_ed;
my $num_1024 = @fileList_1024;
my $num_2048 = @fileList_2048;
my $num_3072 = @fileList_3072;
my $num_4096 = @fileList_4096;

# open our output file, "+>" creates and/or truncates
open OUT_FILE, "+>", $outputFile  or die $!;

print OUT_FILE "/* certs_test.h */\n\n";
print OUT_FILE "#ifndef WOLFSSL_CERTS_TEST_H\n";
print OUT_FILE "#define WOLFSSL_CERTS_TEST_H\n\n";


# convert and print 1024-bit cert/keys
print OUT_FILE "#ifdef USE_CERT_BUFFERS_1024\n\n";
for (my $i = 0; $i < $num_1024; $i++) {

    my $fname = $fileList_1024[$i][0];
    my $sname = $fileList_1024[$i][1];

    print OUT_FILE "/* $fname, 1024-bit */\n";
    print OUT_FILE "static const unsigned char $sname\[] =\n";
    print OUT_FILE "{\n";
    file_to_hex($fname);
    print OUT_FILE "};\n";
    print OUT_FILE "static const int sizeof_$sname = sizeof($sname);\n\n";
}
print OUT_FILE "#endif /* USE_CERT_BUFFERS_1024 */\n\n";


# convert and print 2048-bit certs/keys
print OUT_FILE "#ifdef USE_CERT_BUFFERS_2048\n\n";
for (my $i = 0; $i < $num_2048; $i++) {

    my $fname = $fileList_2048[$i][0];
    my $sname = $fileList_2048[$i][1];

    print OUT_FILE "/* $fname, 2048-bit */\n";
    print OUT_FILE "static const unsigned char $sname\[] =\n";
    print OUT_FILE "{\n";
    file_to_hex($fname);
    print OUT_FILE "};\n";
    print OUT_FILE "static const int sizeof_$sname = sizeof($sname);\n\n";
}


print OUT_FILE "#endif /* USE_CERT_BUFFERS_2048 */\n\n";


# convert and print 3072-bit certs/keys
print OUT_FILE "#ifdef USE_CERT_BUFFERS_3072\n\n";
for (my $i = 0; $i < $num_3072; $i++) {

    my $fname = $fileList_3072[$i][0];
    my $sname = $fileList_3072[$i][1];

    print OUT_FILE "/* $fname, 3072-bit */\n";
    print OUT_FILE "static const unsigned char $sname\[] =\n";
    print OUT_FILE "{\n";
    file_to_hex($fname);
    print OUT_FILE "};\n";
    print OUT_FILE "static const int sizeof_$sname = sizeof($sname);\n\n";
}

print OUT_FILE "#endif /* USE_CERT_BUFFERS_3072 */\n\n";


# convert and print 4096-bit certs/keys
print OUT_FILE "#ifdef USE_CERT_BUFFERS_4096\n\n";
for (my $i = 0; $i < $num_4096; $i++) {

    my $fname = $fileList_4096[$i][0];
    my $sname = $fileList_4096[$i][1];

    print OUT_FILE "/* $fname, 4096-bit */\n";
    print OUT_FILE "static const unsigned char $sname\[] =\n";
    print OUT_FILE "{\n";
    file_to_hex($fname);
    print OUT_FILE "};\n";
    print OUT_FILE "static const int sizeof_$sname = sizeof($sname);\n\n";
}

print OUT_FILE "#endif /* USE_CERT_BUFFERS_4096 */\n\n";


# convert and print 256-bit cert/keys
print OUT_FILE "#if defined(HAVE_ECC) && defined(USE_CERT_BUFFERS_256)\n\n";
for (my $i = 0; $i < $num_ecc; $i++) {

    my $fname = $fileList_ecc[$i][0];
    my $sname = $fileList_ecc[$i][1];

    print OUT_FILE "/* $fname, ECC */\n";
    print OUT_FILE "static const unsigned char $sname\[] =\n";
    print OUT_FILE "{\n";
    file_to_hex($fname);
    print OUT_FILE "};\n";
    print OUT_FILE "static const int sizeof_$sname = sizeof($sname);\n\n";
}
print OUT_FILE "#endif /* HAVE_ECC && USE_CERT_BUFFERS_256 */\n\n";


print OUT_FILE "/* dh1024 p */
static const unsigned char dh_p[] =
{
    0xE6, 0x96, 0x9D, 0x3D, 0x49, 0x5B, 0xE3, 0x2C, 0x7C, 0xF1, 0x80, 0xC3,
    0xBD, 0xD4, 0x79, 0x8E, 0x91, 0xB7, 0x81, 0x82, 0x51, 0xBB, 0x05, 0x5E,
    0x2A, 0x20, 0x64, 0x90, 0x4A, 0x79, 0xA7, 0x70, 0xFA, 0x15, 0xA2, 0x59,
    0xCB, 0xD5, 0x23, 0xA6, 0xA6, 0xEF, 0x09, 0xC4, 0x30, 0x48, 0xD5, 0xA2,
    0x2F, 0x97, 0x1F, 0x3C, 0x20, 0x12, 0x9B, 0x48, 0x00, 0x0E, 0x6E, 0xDD,
    0x06, 0x1C, 0xBC, 0x05, 0x3E, 0x37, 0x1D, 0x79, 0x4E, 0x53, 0x27, 0xDF,
    0x61, 0x1E, 0xBB, 0xBE, 0x1B, 0xAC, 0x9B, 0x5C, 0x60, 0x44, 0xCF, 0x02,
    0x3D, 0x76, 0xE0, 0x5E, 0xEA, 0x9B, 0xAD, 0x99, 0x1B, 0x13, 0xA6, 0x3C,
    0x97, 0x4E, 0x9E, 0xF1, 0x83, 0x9E, 0xB5, 0xDB, 0x12, 0x51, 0x36, 0xF7,
    0x26, 0x2E, 0x56, 0xA8, 0x87, 0x15, 0x38, 0xDF, 0xD8, 0x23, 0xC6, 0x50,
    0x50, 0x85, 0xE2, 0x1F, 0x0D, 0xD5, 0xC8, 0x6B,
};

/* dh1024 g */
static const unsigned char dh_g[] =
{
  0x02,
};\n\n";

# convert and print ed25519 cert/keys
print OUT_FILE "#if defined(HAVE_ED25519)\n\n";
for (my $i = 0; $i < $num_ed; $i++) {

    my $fname = $fileList_ed[$i][0];
    my $sname = $fileList_ed[$i][1];

    print OUT_FILE "/* $fname, ED25519 */\n";
    print OUT_FILE "static const unsigned char $sname\[] =\n";
    print OUT_FILE "{\n";
    file_to_hex($fname);
    print OUT_FILE "};\n";
    print OUT_FILE "static const int sizeof_$sname = sizeof($sname);\n\n";
}
print OUT_FILE "#endif /* HAVE_ED25519 */\n\n";

print OUT_FILE "#endif /* WOLFSSL_CERTS_TEST_H */\n\n";

# close certs_test.h file
close OUT_FILE or die $!;

# print file as hex, comma-separated, as needed by C buffer
sub file_to_hex {
    my $fileName = $_[0];

    open my $fp, "<", $fileName or die $!;
    binmode($fp);

    my $fileLen = -s $fileName;
    my $byte;

    for (my $i = 0, my $j = 1; $i < $fileLen; $i++, $j++)
    {
        if ($j == 1) {
            print OUT_FILE "        ";
        }
        if ($j != 1) {
            print OUT_FILE " ";
        }
        read($fp, $byte, 1) or die "Error reading $fileName";
        my $output = sprintf("0x%02X", ord($byte));
        print OUT_FILE $output;

        if ($i != ($fileLen - 1)) {
            print OUT_FILE ",";
        }

        if ($j == 10) {
            $j = 0;
            print OUT_FILE "\n";
        }
    }

    print OUT_FILE "\n";

    close($fp);
}
