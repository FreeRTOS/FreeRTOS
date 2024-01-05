#!/usr/bin/env python

import os
import argparse
import random
import datetime
import subprocess
from cryptography import x509
from cryptography.x509.oid import NameOID
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives import serialization, hashes
from cryptography.hazmat.primitives.asymmetric import ec

# Helper scripts from this directory
from convert_credentials_to_der import convert_pem_to_der

script_file_dir_abs_path = os.path.abspath(os.path.dirname(__file__))

# File names for generated credentials
ROOT_CA_PRIV_KEY_FILE = f"{script_file_dir_abs_path}{os.sep}ECDSA_root_priv_key.pem"
ROOT_CA_PUB_KEY_FILE = f"{script_file_dir_abs_path}{os.sep}ECDSA_root_pub_key.pem"
ROOT_CA_CERT_FILE = f"{script_file_dir_abs_path}{os.sep}ECDSA_root_ca_cert.pem"

CLAIM_PRIV_KEY_FILE = f"{script_file_dir_abs_path}{os.sep}ECDSA_claim_priv_key.pem"
CLAIM_PUB_KEY_FILE = f"{script_file_dir_abs_path}{os.sep}ECDSA_claim_pub_key.pem"
CLAIM_CERT_FILE = f"{script_file_dir_abs_path}{os.sep}ECDSA_claim_device_cert.pem"

# Use the current date and time to create a unique subject name
now = datetime.datetime.now()
dt_string = now.strftime("%d_%m_%Y_%H_%M_%S")

# Default values for the CA cert
subject = issuer = x509.Name([
    x509.NameAttribute(NameOID.COUNTRY_NAME, "US"),
    x509.NameAttribute(NameOID.STATE_OR_PROVINCE_NAME, "FP_State"),
    x509.NameAttribute(NameOID.LOCALITY_NAME, "FP_Locality"),
    x509.NameAttribute(NameOID.ORGANIZATION_NAME, "FP_Organization"),
    x509.NameAttribute(NameOID.COMMON_NAME, f'FP_CN_{dt_string}'),
])

# Simple check of the generated keys.
# Documentation says if the operations fail an exception is thrown.
# https://cryptography.io/en/latest/hazmat/primitives/asymmetric/ec/#cryptography.hazmat.primitives.asymmetric.ec.ECDSA
def validate_keys(private_key, public_key):
    # Verify the generated keys work correctly by signing a message and then verifying it
    data = b"TEST DATA TO SIGN"

    # Sign the above message using the private key
    signature = private_key.sign(
        data,
        ec.ECDSA(hashes.SHA256())
    )

    # Verify the signature using the public key
    public_key.verify(
        signature,
        data,
        ec.ECDSA(hashes.SHA256())
    )


def generate_priv_keys_and_certs(write_der_keys):
    print("Generating ECDSA Root Keys\n")
    # Generate an ECDSA Key Pair
    # NOTE: At time of writing corePKCS11 only supports the prime256v1/secp256r1 keys
    # If this changes then these keys should be changed to use a better alg.
    root_prv_key = ec.generate_private_key(
        ec.SECP256R1()
    )

    # Get the related public key
    root_pub_key = root_prv_key.public_key()

    validate_keys(
        private_key = root_prv_key,
        public_key = root_pub_key
    )

    # Now that the public and private key have been validated, create a x509 Cert
    root_ca_cert = x509.CertificateBuilder().subject_name(
        subject
    ).issuer_name(
        issuer
    ).public_key(
        root_pub_key
    ).serial_number(
        x509.random_serial_number()
    ).not_valid_before(
        datetime.datetime.now(datetime.timezone.utc)
    ).not_valid_after(
        # Our certificate will be valid for 14 days
        datetime.datetime.now(datetime.timezone.utc) + datetime.timedelta(days=14)
    ).add_extension(
        x509.BasicConstraints(ca=True, path_length=None), critical=True,
    # Sign our certificate with our private key
    ).sign(root_prv_key, hashes.SHA256())

    # Check to make sure the cert generated correctly
    isinstance(root_ca_cert, x509.Certificate)

    # Print out the generated ECDSA Keys and Certs
    root_pub_key_pem = root_pub_key.public_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PublicFormat.SubjectPublicKeyInfo
    )

    root_prv_key_pem = root_prv_key.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.TraditionalOpenSSL,
        encryption_algorithm=serialization.NoEncryption()
    )

    root_ca_cert_pem = root_ca_cert.public_bytes(serialization.Encoding.PEM)

    print("Public Key Pem:\n{0}\n".format(root_pub_key_pem.decode("utf-8")))
    print("Private Key Pem:\n{0}\n".format(root_prv_key_pem.decode("utf-8")))
    print("Root CA Cert Pem:\n{0}\n".format(root_ca_cert_pem.decode("utf-8")))

    open(ROOT_CA_PRIV_KEY_FILE, "wb").write(root_prv_key_pem)
    open(ROOT_CA_PUB_KEY_FILE, "wb").write(root_pub_key_pem)
    open(ROOT_CA_CERT_FILE, "wb").write(root_ca_cert_pem)

    print(f"Wrote PEM Encoded Root Private Key to:\n\t{ROOT_CA_PRIV_KEY_FILE}")
    print(f"Wrote PEM Encoded Root Public Key to:\n\t{ROOT_CA_PUB_KEY_FILE}")
    print(f"Wrote PEM Encoded Root CA Cert to:\n\t{ROOT_CA_CERT_FILE}")

    # Device credential generation
    print("\n\nGenerating ECDSA Claim Keys\n")
    # Generate a ECDSA Key Pair
    claim_prv_key = ec.generate_private_key(
        ec.SECP256R1()
    )

    # Get the related public key
    claim_pub_key = claim_prv_key.public_key()

    # Simple check of the generated keys
    validate_keys(
        private_key = claim_prv_key,
        public_key = claim_pub_key
    )

    # Now that the public and private key have been validated, create a x509 Cert
    claim_cert = x509.CertificateBuilder().subject_name(
        subject
    ).issuer_name(
        issuer
    ).public_key(
        claim_pub_key
    ).serial_number(
        x509.random_serial_number()
    ).not_valid_before(
        datetime.datetime.now(datetime.timezone.utc)
    ).not_valid_after(
        # Our certificate will be valid for 14 days
        datetime.datetime.now(datetime.timezone.utc) + datetime.timedelta(days=14)
    ).add_extension(
        x509.BasicConstraints(ca=False, path_length=None), critical=True,
    # Sign our certificate with the Root private key
    ).sign(root_prv_key, hashes.SHA256())

    # Check to make sure the cert generated correctly
    isinstance(claim_cert, x509.Certificate)

    # Serialize the generated ECDSA Keys and Certs
    claim_pub_key_pem = claim_pub_key.public_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PublicFormat.SubjectPublicKeyInfo
    )

    claim_prv_key_pem = claim_prv_key.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.TraditionalOpenSSL,
        encryption_algorithm=serialization.NoEncryption()
    )

    claim_cert_pem = claim_cert.public_bytes(serialization.Encoding.PEM)

    print("Claim Public Key Pem:\n{0}\n".format(claim_pub_key_pem.decode("utf-8")))
    print("Claim Private Key Pem:\n{0}\n".format(claim_prv_key_pem.decode("utf-8")))
    print("Claim Cert Pem:\n{0}\n".format(claim_cert_pem.decode("utf-8")))

    open(CLAIM_PRIV_KEY_FILE, "wb").write(claim_pub_key_pem)
    open(CLAIM_PUB_KEY_FILE, "wb").write(claim_prv_key_pem)
    open(CLAIM_CERT_FILE, "wb").write(claim_cert_pem)

    print(f"Wrote PEM Encoded Claim Private Key to:\n\t{CLAIM_PRIV_KEY_FILE}")
    print(f"Wrote PEM Encoded Claim Public Key to:\n\t{CLAIM_PUB_KEY_FILE}")
    print(f"Wrote PEM Encoded Claim CA Cert to:\n\t{CLAIM_CERT_FILE}")

    if write_der_keys == True:
        print("\nWrite DER Format Version of Claim Private Key and Cert")
        # Use the helper function in convert_credentials_to_der to write out DER formatted keys
        convert_pem_to_der(
            cert_pem = claim_cert_pem.decode("utf-8"),
            key_pem = claim_prv_key_pem.decode("utf-8")
        )

    return root_ca_cert_pem.decode("utf-8"), claim_cert_pem.decode("utf-8")
