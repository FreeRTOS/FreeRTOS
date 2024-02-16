#!/usr/bin/env python

import os
import argparse
from cryptography import x509
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives import serialization

# Get the absolute path of this script
script_file_dir_abs_path = os.path.abspath(os.path.dirname(__file__))

# Get the parent directory, as that is where the demo expects the keys to be placed
parent_abs_path = os.path.abspath(os.path.join(script_file_dir_abs_path, os.pardir))

KEY_OUT_NAME = os.path.join(parent_abs_path, 'corePKCS11_Claim_Key.dat')
CERT_OUT_NAME = os.path.join(parent_abs_path, 'corePKCS11_Claim_Certificate.dat')


def convert_pem_to_der(cert_pem, key_pem):
    # Convert certificate from PEM to DER
    key = serialization.load_pem_private_key(
        bytes(key_pem, "utf-8"), None, default_backend())
    key_der = key.private_bytes(
        serialization.Encoding.DER,
        serialization.PrivateFormat.TraditionalOpenSSL,
        serialization.NoEncryption(),
    )
    with open(f"{KEY_OUT_NAME}", "wb") as key_out:
        key_out.write(key_der)

    print(f"Successfully converted key PEM to DER. Output file named:\n\t{KEY_OUT_NAME}")

    cert = x509.load_pem_x509_certificate(
        bytes(cert_pem, "utf-8"), default_backend())

    with open(f"{CERT_OUT_NAME}", "wb") as cert_out:
        cert_out.write(cert.public_bytes(serialization.Encoding.DER))

    print(f"Successfully converted certificate PEM to DER. Output file named:\n\t{CERT_OUT_NAME}")

def main(args):
    with open(args.cert_file, "r") as cert:
        cert_pem = cert.read()

    with open(args.key_file, "r") as key:
        key_pem = key.read()

    convert_pem_to_der(cert_pem, key_pem)


if __name__ == "__main__":
    arg_parser = argparse.ArgumentParser(
        description="This script converts passed in PEM format certificates and keys into the binary DER format."
    )
    arg_parser.add_argument(
        "-c",
        "--cert_file",
        type=str,
        help="Specify the name of the generated certificate file.",
        required=True,
    )
    arg_parser.add_argument(
        "-k",
        "--key_file",
        type=str,
        help="Specify the name of the generated key file.",
        required=True,
    )
    args = arg_parser.parse_args()
    main(args)
