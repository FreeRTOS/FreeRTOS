#!/usr/bin/env python

import argparse
import os
from cryptography import x509
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives import serialization

KEY_OUT_NAME = f"{os.getcwd()}\\corePKCS11_Key.dat"
CERT_OUT_NAME = f"{os.getcwd()}\\corePKCS11_Certificate.dat"


def convert_pem_to_der(cert_file, key_file):
    # Convert certificate from PEM to DER
    print("Converting format to DER format...")
    with open(key_file, "rb") as key:
        print("Starting key PEM to DER conversion.")
        pemkey = serialization.load_pem_private_key(key.read(), None, default_backend())
        key_der = pemkey.private_bytes(
            serialization.Encoding.DER,
            serialization.PrivateFormat.TraditionalOpenSSL,
            serialization.NoEncryption(),
        )
        with open(KEY_OUT_NAME, "wb") as key_out:
            key_out.write(key_der)
        print(
            f"Successfully converted key PEM to DER. Output file named: {KEY_OUT_NAME}"
        )

    print("Starting certificate pem conversion.")
    with open(cert_file, "rb") as cert:
        cert = x509.load_pem_x509_certificate(cert.read(), default_backend())
        with open(CERT_OUT_NAME, "wb") as cert_out:
            cert_out.write(cert.public_bytes(serialization.Encoding.DER))

        print(
            f"Successfully converted certificate PEM to DER. Output file named: {CERT_OUT_NAME}"
        )


def main(args):
    convert_pem_to_der(cert_file=args.cert_file, key_file=args.key_file)


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
