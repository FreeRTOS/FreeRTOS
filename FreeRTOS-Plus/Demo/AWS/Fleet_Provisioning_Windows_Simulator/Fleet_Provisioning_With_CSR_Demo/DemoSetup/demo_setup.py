#!/usr/bin/env python

import os
import argparse
import boto3
import botocore
import random
import datetime
from cryptography import x509
from cryptography.x509.oid import NameOID
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives import serialization, hashes
from cryptography.hazmat.primitives.asymmetric import ec

from convert_credentials_to_der import convert_pem_to_der

RESOURCE_STACK_NAME = "FPDemoStack"

script_file_dir_abs_path = os.path.abspath(os.path.dirname(__file__))
cf = boto3.client("cloudformation")
iot = boto3.client("iot")

# File names for generated credentials
ROOT_CA_PRIV_KEY_FILE = "ECDSA_root_priv_key.pem"
ROOT_CA_PUB_KEY_FILE = "ECDSA_root_pub_key.pem"
ROOT_CA_CERT_FILE = "ECDSA_root_ca_cert.pem"

CLAIM_PRIV_KEY_FILE = "ECDSA_claim_priv_key.pem"
CLAIM_PUB_KEY_FILE = "ECDSA_claim_pub_key.pem"
CLAIM_CERT_FILE = "ECDSA_claim_device_cert.pem"

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

def generate_priv_keys_and_certs():
    print("Generating ECDSA Root Keys\n")
    # Generate an ECDSA Key Pair
    root_private_key = ec.generate_private_key(
        ec.SECP256R1()
    )

    # Get the related public key
    root_public_key = root_private_key.public_key()

    validate_keys(
        private_key = root_private_key,
        public_key = root_public_key
    )

    # Now that the public and private key have been validated, create a x509 Cert
    root_ca_cert = x509.CertificateBuilder().subject_name(
        subject
    ).issuer_name(
        issuer
    ).public_key(
        root_public_key
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
    ).sign(root_private_key, hashes.SHA256())

    # Check to make sure the cert generated correctly
    isinstance(root_ca_cert, x509.Certificate)

    # Print out the generated ECDSA Keys and Certs
    serialized_public = root_public_key.public_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PublicFormat.SubjectPublicKeyInfo
    )

    serialized_private = root_private_key.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.TraditionalOpenSSL,
        encryption_algorithm=serialization.NoEncryption()
    )

    serialized_ca_cert = root_ca_cert.public_bytes(serialization.Encoding.PEM)

    print("\nPublic Key Pem:\n{0}".format(serialized_public))
    print("Private Key Pem:\n{0}".format(serialized_private))
    print("Root CA Cert Pem:\n{0}\n".format(serialized_ca_cert))

    open(ROOT_CA_PRIV_KEY_FILE, "wb").write(serialized_private)
    open(ROOT_CA_PUB_KEY_FILE, "wb").write(serialized_public)
    open(ROOT_CA_CERT_FILE, "wb").write(serialized_ca_cert)

    print(f"Wrote PEM Encoded Root Private Key to {ROOT_CA_PRIV_KEY_FILE}")
    print(f"Wrote PEM Encoded Root Public Key to {ROOT_CA_PUB_KEY_FILE}")
    print(f"Wrote PEM Encoded Root CA Cert to {ROOT_CA_CERT_FILE}")


    # Device credential generation
    print("\n\nGenerating ECDSA Claim Keys\n")
    # Generate a ECDSA Key Pair
    claim_private_key = ec.generate_private_key(
        ec.SECP256R1()
    )

    # Get the related public key
    claim_public_key = claim_private_key.public_key()

    # Simple check of the generated keys
    validate_keys(
        private_key = claim_private_key,
        public_key = claim_public_key
    )

    # Now that the public and private key have been validated, create a x509 Cert
    claim_cert = x509.CertificateBuilder().subject_name(
        subject
    ).issuer_name(
        issuer
    ).public_key(
        claim_public_key
    ).serial_number(
        x509.random_serial_number()
    ).not_valid_before(
        datetime.datetime.now(datetime.timezone.utc)
    ).not_valid_after(
        # Our certificate will be valid for 14 days
        datetime.datetime.now(datetime.timezone.utc) + datetime.timedelta(days=14)
    ).add_extension(
        x509.SubjectAlternativeName([x509.DNSName("localhost")]),
        critical=False,
    # Sign our certificate with the Root private key
    ).sign(root_private_key, hashes.SHA256())

    # Check to make sure the cert generated correctly
    isinstance(claim_cert, x509.Certificate)

    # Print out the generated ECDSA Keys and Certs
    serialized_public_claim_key = claim_public_key.public_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PublicFormat.SubjectPublicKeyInfo
    )

    serialized_private_claim_key = claim_private_key.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.TraditionalOpenSSL,
        encryption_algorithm=serialization.NoEncryption()
    )

    serialized_claim_cert = claim_cert.public_bytes(serialization.Encoding.PEM)

    print("\nClaim Public Key Pem:\n{0}".format(serialized_public_claim_key))
    print("Claim Private Key Pem:\n{0}".format(serialized_private_claim_key))
    print("Claim Cert Pem:\n{0}\n".format(serialized_claim_cert))

    open(CLAIM_PRIV_KEY_FILE, "wb").write(serialized_public_claim_key)
    open(CLAIM_PUB_KEY_FILE, "wb").write(serialized_private_claim_key)
    open(CLAIM_CERT_FILE, "wb").write(serialized_claim_cert)

    print(f"Wrote PEM Encoded Claim Private Key to {CLAIM_PRIV_KEY_FILE}")
    print(f"Wrote PEM Encoded Claim Public Key to {CLAIM_PUB_KEY_FILE}")
    print(f"Wrote PEM Encoded Claim CA Cert to {CLAIM_CERT_FILE}")

    # Use the helper function in convert_credentials_to_der to write out DER formatted keys
    convert_pem_to_der(
        cert_pem = str(serialized_claim_cert, encoding='utf-8'),
        key_pem = str(serialized_private_claim_key, encoding='utf-8')
    )


# Convert a CloudFormation arn into a link to the resource
def convert_cf_arn_to_link(arn):
    region = arn.split(":")[3]
    return f"https://{region}.console.aws.amazon.com/cloudformation/home?region={region}#/stacks/stackinfo?stackId={arn}"

# Get the CloudFormation stack if it exists - "STACK_NOT_FOUND" otherwise
def get_stack():
    try:
        paginator = cf.get_paginator("describe_stacks")
        response_iterator = paginator.paginate(StackName=RESOURCE_STACK_NAME)
        for response in response_iterator:
            return response["Stacks"][0]
        response = cf.describe_stacks(StackName=RESOURCE_STACK_NAME)
        return response["Stacks"][0]
    except botocore.exceptions.ClientError as e:
        if e.response["Error"]["Code"] == "ValidationError":
            return "STACK_NOT_FOUND"
        raise


# Create the required resources from the CloudFormation template
def create_resources():
    stack_response = get_stack()
    if stack_response != "STACK_NOT_FOUND":
        print("Fleet Provisioning resource stack already exists with status: " +
              stack_response["StackStatus"])
        print()
        if stack_response["StackStatus"] != "CREATE_COMPLETE":
            raise Exception("Fleet Provisioning resource stack failed to create successfully. You may need to delete the stack and retry."
                            + "\nView the stack in the CloudFormation console here:\n" + convert_cf_arn_to_link(stack_response["StackId"]))
    else:
        # Read the cloudformation template file contained in the same directory
        cf_template_file = open(f"{script_file_dir_abs_path}/cloudformation_template.json", "r")
        cf_template = cf_template_file.read()
        cf_template_file.close()

        create_response = cf.create_stack(
            StackName=RESOURCE_STACK_NAME,
            TemplateBody=cf_template,
            Capabilities=["CAPABILITY_NAMED_IAM"],
            OnFailure="ROLLBACK"
        )

        print("Stack creation started. View the stack in the CloudFormation console here:")
        print(convert_cf_arn_to_link(create_response["StackId"]))
        print("Waiting...")
        try:
            create_waiter = cf.get_waiter("stack_create_complete")
            create_waiter.wait(StackName=RESOURCE_STACK_NAME)
            print("Successfully created the resources stack.")
        except botocore.exceptions.WaiterError as err:
            print(
                "Error: Stack creation failed. You may need to delete_all and try again.")
            raise

# Generate IoT credentials in DER format and save them in the demo directory


def create_credentials():
    print("Creating Certs and Credentials for the Fleet Provisioning Demo...")
    # Verify that the stack exists (create_resources has been ran before somewhere)
    stack_response = get_stack()
    if stack_response == "STACK_NOT_FOUND":
        raise Exception(
            f"CloudFormation stack \"{RESOURCE_STACK_NAME}\" not found.")
    elif stack_response["StackStatus"] != "CREATE_COMPLETE":
        print("Error: Stack was not successfully created. View the stack in the CloudFormation console here:")
        stack_link = convert_cf_arn_to_link(stack_response["StackId"])
        raise Exception(
            "Stack was not successfully created. View the stack in the CloudFormation console here:\n" + stack_link)

    # Generate an ECDSA CA cert, and a ECDSA Cert and key to use for device provisioning
    generate_priv_keys_and_certs()

    # Read the PEM files that were generated
    root_ca_cert = open(ROOT_CA_CERT_FILE,"r").read()
    claim_cert = open(CLAIM_CERT_FILE,"r").read()

    if ( len(root_ca_cert) == 0 ) or ( len(claim_cert) == 0 ):
        raise Exception(
            "Failed to generate the required ECDSA Certs"
        )

    ca_cert_response = iot.register_ca_certificate(
        caCertificate=root_ca_cert,
        setAsActive=True,
        allowAutoRegistration=True,
        certificateMode='SNI_ONLY'
    )

    if "certificateArn" not in ca_cert_response.keys():
        raise Exception(
            "Failed to register the generated ECDSA CA Certificate"
        )
    else:
        print("Registered CA Cert\n\tARN:{0}\n\tCertID:{1}"
            .format(
                ca_cert_response["certificateArn"],
                ca_cert_response["certificateId"]
            )
        )

    claim_cert_response = iot.register_certificate(
        certificatePem=claim_cert,
        caCertificatePem=root_ca_cert,
        setAsActive=True
    )

    if "certificateArn" not in claim_cert_response.keys():
        raise Exception(
            "Failed to register the generate CA Certificate"
        )
    else:
        print("Registered CA Cert\n\tARN:{0}\n\tCertID:{1}"
            .format(
                claim_cert_response["certificateArn"],
                claim_cert_response["certificateId"]
            )
        )

    iot.attach_policy(policyName="CF_FleetProvisioningDemoClaimPolicy",
                        target=claim_cert_response["certificateArn"])

    # convert_pem_to_der(
    #    credentials["certificatePem"], credentials["keyPair"]["PrivateKey"])

# Set the necessary fields in demo_config.h
def update_demo_config():
    print("Updating the demo config for the Fleet Provisioning Demo...")
    endpoint = iot.describe_endpoint(endpointType='iot:Data-ATS')

    template_file = open(f"{script_file_dir_abs_path}/demo_config.templ", 'r')
    file_text = template_file.read()
    file_text = file_text.replace(
        "<IOTEndpoint>", "\"" + endpoint["endpointAddress"] + "\"")

    header_file = open(f"{script_file_dir_abs_path}/../demo_config.h", "w")
    header_file.write(file_text)
    header_file.close()
    template_file.close()
    print("Successfully updated demo_config.h")

# Get arguments
def get_args():
    parser = argparse.ArgumentParser(description="Fleet Provisioning Demo setup script.")
    parser.add_argument("--force", action="store_true", help="Used to skip the user prompt before executing.")
    args = parser.parse_args()
    return args

# Parse arguments and execute appropriate functions
def main():

    # Check arguments and go appropriately
    args = get_args();
    print("\nThis script will set up the AWS resources required for the Fleet Provisioning demo.")
    print("It may take several minutes for the resources to be provisioned.")
    if args.force or input("Are you sure you want to do this? (y/n) ") == "y":
        print()
        print("\n---------------------- Start Create Cloud Stack Resources ----------------------")
        create_resources()
        print("----------------------- End Create Cloud Stack Resources -----------------------\n")

        print("\n-------------------------- Start Creating Credentials --------------------------")
        create_credentials()
        print("--------------------------- End Creating Credentials ---------------------------\n")

        print("\n--------------------------- Start Update Demo Config ---------------------------")
        print("")
        update_demo_config()
        print("---------------------------- End Update Demo Config ----------------------------\n")

        print("\nFleet Provisioning demo setup complete. Ensure that all generated files (key, certificate, demo_config.h) are in the same folder as \"fleet_provisioning_demo.sln\".")


if __name__ == "__main__":
    main()
