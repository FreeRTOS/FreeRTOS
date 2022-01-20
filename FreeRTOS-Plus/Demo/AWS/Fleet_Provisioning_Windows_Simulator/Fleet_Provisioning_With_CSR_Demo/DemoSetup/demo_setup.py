#!/usr/bin/env python

import boto3
import botocore
from typing import Dict, List
from cryptography import x509
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives import serialization

KEY_OUT_NAME = "corePKCS11_Claim_Key.dat"
CERT_OUT_NAME = "corePKCS11_Claim_Certificate.dat"

RESOURCE_STACK_NAME = "FPDemoStack"

cf = boto3.client("cloudformation")
iot = boto3.client("iot")

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
        print("Stack already exists with status: " + stack_response["StackStatus"])
        print("View the stack in the CloudFormation console here:\n" + convert_cf_arn_to_link(stack_response["StackId"]))
    else:
        # Read the cloudformation template file contained in the same directory
        cf_template_file = open("cloudformation_template.json", "r")
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
            print("Error: Stack creation failed. You may need to delete_all and try again.")
            raise

def convert_pem_to_der(cert_pem, key_pem):
    # Convert certificate from PEM to DER
    key = serialization.load_pem_private_key(bytes(key_pem, "utf-8"), None, default_backend())
    key_der = key.private_bytes(
        serialization.Encoding.DER,
        serialization.PrivateFormat.TraditionalOpenSSL,
        serialization.NoEncryption(),
    )
    with open(f"../{KEY_OUT_NAME}", "wb") as key_out:
        key_out.write(key_der)
    print(
        f"Successfully converted key PEM to DER. Output file named: {KEY_OUT_NAME}"
    )

    cert = x509.load_pem_x509_certificate(bytes(cert_pem, "utf-8"), default_backend())
    with open(f"../{CERT_OUT_NAME}", "wb") as cert_out:
        cert_out.write(cert.public_bytes(serialization.Encoding.DER))

    print(
        f"Successfully converted certificate PEM to DER. Output file named: {CERT_OUT_NAME}"
    )

# Generate IoT credentials in DER format and save them in the demo directory
def create_credentials():
    # Verify that the stack exists (create_resources has been ran before somewhere)
    stack_response = get_stack()
    if stack_response == "STACK_NOT_FOUND":
        raise Exception(f"CloudFormation stack \"{RESOURCE_STACK_NAME}\" not found.")
    elif stack_response["StackStatus"] != "CREATE_COMPLETE":
        print("Error: Stack was not successfully created. View the stack in the CloudFormation console here:")
        stack_link = convert_cf_arn_to_link(stack_response["StackId"])
        raise Exception("Stack was not successfully created. View the stack in the CloudFormation console here:\n" + stack_link)
    else:
        credentials = iot.create_keys_and_certificate(setAsActive=True)
        iot.attach_policy(policyName="CF_FleetProvisioningDemoClaimPolicy", target=credentials["certificateArn"])
        convert_pem_to_der(credentials["certificatePem"], credentials["keyPair"]["PrivateKey"])


# Set the necessary fields in demo_config.h
def update_demo_config():
    print("TODO")

# Parse arguments and execute appropriate functions
def main(args):
    # Check arguments and go appropriately
    print("\nThis script will set up the AWS resources required for the Fleet Provisioning demo.")
    print("It may take several minutes for the resources to be provisioned.")
    if input("Are you sure you want to do this? (y/n) ") == "y":
        print()
        create_resources()
        create_credentials()
        print("\nFleet Provisioning demo setup complete. Ensure that the Key and Certificate files are in the same folder as \"fleet_provisioning_demo.sln\".")

if __name__ == "__main__":
    main({"Test": "Value"})