#!/usr/bin/perl

# gencertbuf.pl
# version 1.1
# Updated 07/01/2014
#
# Copyright (C) 2006-2014 wolfSSL Inc.
#

use strict;
use warnings;

# ---- SCRIPT SETTINGS -------------------------------------------------------

# output C header file to write cert/key buffers to
my $outputFile = "./cyassl/certs_test.h";

# 1024-bit certs/keys to be converted
# Used with USE_CERT_BUFFERS_1024 define.

my @fileList_1024 = (
        [ "./certs/1024/client-key.der", "client_key_der_1024" ],
        [ "./certs/1024/client-cert.der", "client_cert_der_1024" ],
        [ "./certs/1024/dh1024.der", "dh_key_der_1024" ],
        [ "./certs/1024/dsa1024.der", "dsa_key_der_1024" ],
        [ "./certs/1024/rsa1024.der", "rsa_key_der_1024" ]
        );

# 2048-bit certs/keys to be converted
# Used with USE_CERT_BUFFERS_2048 define.

my @fileList_2048 = (
        [ "./certs/client-key.der", "client_key_der_2048" ],
        [ "./certs/client-cert.der", "client_cert_der_2048" ],
        [ "./certs/dh2048.der", "dh_key_der_2048" ],
        [ "./certs/dsa2048.der", "dsa_key_der_2048" ],
        [ "./certs/rsa2048.der", "rsa_key_der_2048" ],
        [ "./certs/ca-cert.der", "ca_cert_der_2048" ],
        [ "./certs/server-key.der", "server_key_der_2048" ],
        [ "./certs/server-cert.der", "server_cert_der_2048" ]
        );

# ----------------------------------------------------------------------------

my $num_1024 = @fileList_1024;
my $num_2048 = @fileList_2048;

# open our output file, "+>" creates and/or truncates
open OUT_FILE, "+>", $outputFile  or die $!;

print OUT_FILE "/* certs_test.h */\n\n";
print OUT_FILE "#ifndef CYASSL_CERTS_TEST_H\n";
print OUT_FILE "#define CYASSL_CERTS_TEST_H\n\n";

# convert and print 1024-bit cert/keys
print OUT_FILE "#ifdef USE_CERT_BUFFERS_1024\n\n";
for (my $i = 0; $i < $num_1024; $i++) {

    my $fname = $fileList_1024[$i][0];
    my $sname = $fileList_1024[$i][1];

    print OUT_FILE "/* $fname, 1024-bit */\n";
    print OUT_FILE "const unsigned char $sname\[] =\n";
    print OUT_FILE "{\n";
    file_to_hex($fname);
    print OUT_FILE "};\n";
    print OUT_FILE "const int sizeof_$sname = sizeof($sname);\n\n";
}

# convert and print 2048-bit certs/keys
print OUT_FILE "#elif defined(USE_CERT_BUFFERS_2048)\n\n";
for (my $i = 0; $i < $num_2048; $i++) {

    my $fname = $fileList_2048[$i][0];
    my $sname = $fileList_2048[$i][1];

    print OUT_FILE "/* $fname, 2048-bit */\n";
    print OUT_FILE "const unsigned char $sname\[] =\n";
    print OUT_FILE "{\n";
    file_to_hex($fname);
    print OUT_FILE "};\n";
    print OUT_FILE "const int sizeof_$sname = sizeof($sname);\n\n";
}

print OUT_FILE "#endif /* USE_CERT_BUFFERS_1024 */\n\n";
print OUT_FILE "#endif /* CYASSL_CERTS_TEST_H */\n\n";

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
            print OUT_FILE "\t";
        }
        read($fp, $byte, 1) or die "Error reading $fileName";
        my $output = sprintf("0x%02X", ord($byte));
        print OUT_FILE $output;

        if ($i != ($fileLen - 1)) {
            print OUT_FILE ", ";
        }

        if ($j == 10) {
            $j = 0;
            print OUT_FILE "\n";
        }
    }

    print OUT_FILE "\n";

    close($fp); 
}

