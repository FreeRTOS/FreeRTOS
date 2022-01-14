#!/usr/bin/env python

import sys
import boto3
import botocore
import argparse
import json
from dataclasses import dataclass
from typing import Dict, List
from cryptography import x509
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives import serialization

KEY_OUT_NAME = "corePKCS11_Claim_Key.dat"
CERT_OUT_NAME = "corePKCS11_Claim_Certificate.dat"

cf = boto3.client("cloudformation")
iot = boto3.client("iot")

# Convert a CloudFormation arn into a link to the resource
def convert_cf_arn_to_link(arn):
    region = arn.split(":")[3]
    return "".join([
        "https://",
        region,
        ".console.aws.amazon.com/cloudformation/home?region=",
        region,
        "#/stacks/stackinfo?stackId=",
        arn
    ])

# Get the CloudFormation stack if it exists - "STACK_NOT_FOUND" otherwise
def get_stack(stack_name):
    try:
        response = cf.describe_stacks(StackName=stack_name)
        return response["Stacks"][0]
    except botocore.exceptions.ClientError:
        return "STACK_NOT_FOUND"


# Create the required resources from the CloudFormation template
def create_resources(stack_name):
    stack_response = get_stack(stack_name)
    if stack_response != "STACK_NOT_FOUND":
        print("Stack already exists with status: " + stack_response["StackStatus"])
        print("View the stack in the CloudFormation console here:\n" + convert_cf_arn_to_link(stack_response["StackId"]))
    else:
        # Read the cloudformation template file contained in the same directory
        cf_template_file = open("demo_cloudformation_template.json", "r")
        cf_template = cf_template_file.read()
        cf_template_file.close()

        create_response = cf.create_stack(
            StackName=stack_name,
            TemplateBody=cf_template,
            Capabilities=["CAPABILITY_NAMED_IAM"]
        )

        print("Stack creation started. View the stack in the CloudFormation console here:\n")
        print(convert_cf_arn_to_link(create_response["StackId"]))
        print("Waiting...")
        try:
            create_waiter = cf.get_waiter("stack_create_complete")
            create_waiter.wait(StackName=stack_name)
            print("Successfully created the resources stack.")
        except botocore.exceptions.WaiterError as err:
            print("Error: Stack creation failed. You may need to delete_all and try again.")
            raise

def convert_pem_to_der(cert_pem, key_pem):
    # Convert certificate from PEM to DER
    print("Converting format to DER format...")
    print("Starting key PEM to DER conversion.")
    key = serialization.load_pem_private_key(bytes(key_pem, "utf-8"), None, default_backend())
    key_der = key.private_bytes(
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
    cert = x509.load_pem_x509_certificate(bytes(cert_pem, "utf-8"), default_backend())
    with open(CERT_OUT_NAME, "wb") as cert_out:
        cert_out.write(cert.public_bytes(serialization.Encoding.DER))

    print(
        f"Successfully converted certificate PEM to DER. Output file named: {CERT_OUT_NAME}"
    )

# Generate IoT credentials in DER format and save them in the demo directory
def create_credentials(stack_name):
    # Verify that the stack exists (create_resources has been ran before somewhere)
    stack_response = get_stack(stack_name)
    if stack_response == "STACK_NOT_FOUND":
        raise Exception("CloudFormation stack \"" + stack_name + "\" not found. You must run 'create_resources'.")
    elif stack_response["StackStatus"] != "CREATE_COMPLETE":
        print("Error: Stack was not successfully created. View the stack in the CloudFormation console here:")
        stack_link = convert_cf_arn_to_link(stack_response["StackId"])
        raise Exception("Stack was not successfully created. View the stack in the CloudFormation console here:\n" + stack_link)
    else:
        credentials = iot.create_keys_and_certificate(setAsActive=True)
        iot.attach_policy(policyName="CF_FleetProvisioningDemoClaimPolicy", target=credentials["certificateArn"])
        convert_pem_to_der(credentials["certificatePem"], credentials["keyPair"]["PrivateKey"])


# Set the necessary fields in demo_config.h (perhaps more difficult than worth it)
def update_demo_config():
    print("TODO")

# Delete all resources (including provisioned Things)
def delete_all():
    print("TODO")

# Parse arguments and execute appropriate functions
def main(args):
    # Check arguments and go appropriately
    print("Begin Execution")
    #create_resources("FPDemoStack")
    create_credentials("FPDemoStack")

if __name__ == "__main__":
    main({"Test": "Value"})