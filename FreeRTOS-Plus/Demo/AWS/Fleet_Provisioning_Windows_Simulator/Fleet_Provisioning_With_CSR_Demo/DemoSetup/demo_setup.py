#!/usr/bin/env python

import os
import argparse
import boto3
import botocore
from convert_credentials_to_der import convert_pem_to_der

KEY_OUT_NAME = f"{os.getcwd()}\\corePKCS11_Claim_Key.dat"
CERT_OUT_NAME = f"{os.getcwd()}\\corePKCS11_Claim_Certificate.dat"

RESOURCE_STACK_NAME = "FPDemoStack"

script_file_dir_abs_path = os.path.abspath(os.path.dirname(__file__))
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
    else:
        credentials = iot.create_keys_and_certificate(setAsActive=True)
        iot.attach_policy(policyName="CF_FleetProvisioningDemoClaimPolicy",
                          target=credentials["certificateArn"])
        convert_pem_to_der(
            credentials["certificatePem"], credentials["keyPair"]["PrivateKey"])


# Set the necessary fields in demo_config.h
def update_demo_config():
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
        create_resources()
        create_credentials()
        update_demo_config()
        print("\nFleet Provisioning demo setup complete. Ensure that all generated files (key, certificate, demo_config.h) are in the same folder as \"fleet_provisioning_demo.sln\".")


if __name__ == "__main__":
    main()
