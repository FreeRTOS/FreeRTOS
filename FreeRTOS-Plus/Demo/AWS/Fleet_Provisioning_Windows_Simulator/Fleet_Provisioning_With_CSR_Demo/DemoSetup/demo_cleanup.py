#!/usr/bin/env python

import os
import boto3
import botocore
import argparse

KEY_OUT_NAME = os.path.join(os.getcwd(), "corePKCS11_Claim_Key.dat")
CERT_OUT_NAME = os.path.join(os.getcwd(), "corePKCS11_Claim_Certificate.dat")

THING_PRIVATE_KEY_NAME = os.path.join(os.getcwd(), "corePKCS11_Key.dat")
THING_PUBLIC_KEY_NAME = os.path.join(os.getcwd(), "corePKCS11_PubKey.dat")
THING_CERT_NAME = os.path.join(os.getcwd(), "corePKCS11_Certificate.dat")

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
        response = cf.describe_stacks(StackName=RESOURCE_STACK_NAME)
        return response["Stacks"][0]
    except botocore.exceptions.ClientError as e:
        if e.response["Error"]["Code"] == "ValidationError":
            return "STACK_NOT_FOUND"
        raise

# Delete a Thing after clearing it of all certificates
def delete_thing(thing_name):
    paginator = iot.get_paginator("list_thing_principals")
    list_certificates_iterator = paginator.paginate(
        thingName=thing_name
    )

    for response in list_certificates_iterator:
        for certificate_arn in response["principals"]:
            iot.detach_thing_principal(
                thingName=thing_name,
                principal=certificate_arn
            )

    iot.delete_thing(thingName=thing_name)

# Delete a certificate and all Things attached to it
def delete_certificate_and_things(certificate_arn, policy_name):
    paginator = iot.get_paginator("list_principal_things")
    list_things_iterator = paginator.paginate(
        principal=certificate_arn
    )
    for response in list_things_iterator:
        for thing_name in response["things"]:
            delete_thing(thing_name)

    iot.detach_policy(
        policyName=policy_name,
        target=certificate_arn
    )

    certificate_id = certificate_arn.split("/")[-1]
    iot.update_certificate(
        certificateId=certificate_id,
        newStatus="INACTIVE"
    )
    iot.delete_certificate(certificateId=certificate_id)

# Delete all resources (including provisioned Things)
def delete_resources():
    stack_response = get_stack()
    if stack_response == "STACK_NOT_FOUND":
        print("Nothing to delete - no Fleet Provisioning resources were found.")
        return

    # Find all certificates with "CF_FleetProvisioningDemoThingPolicy" attached
    print("Deleting certificates and things...")
    paginator = iot.get_paginator("list_targets_for_policy")
    list_targets_things_iterator = paginator.paginate(
        policyName="CF_FleetProvisioningDemoThingPolicy"
    )

    # Delete all certificates and Things created by this demo
    for response in list_targets_things_iterator:
        for certificate_arn in response["targets"]:
            delete_certificate_and_things(
                certificate_arn,
                "CF_FleetProvisioningDemoThingPolicy"
            )

    # Find all certificates with "CF_FleetProvisioningDemoClaimPolicy" attached
    paginator = iot.get_paginator("list_targets_for_policy")
    list_targets_claim_iterator = paginator.paginate(
        policyName="CF_FleetProvisioningDemoClaimPolicy"
    )

    # Delete all Fleet Provisioning Claim certificates
    for response in list_targets_claim_iterator:
        for certificate_arn in response["targets"]:
            delete_certificate_and_things(
                certificate_arn,
                "CF_FleetProvisioningDemoClaimPolicy"
            )

    print("Done.")

    print("Fleet Provisioning resource stack deletion started. View the stack in the CloudFormation console here:")
    print(convert_cf_arn_to_link(stack_response["StackId"]))
    delete_response = cf.delete_stack(
        StackName=RESOURCE_STACK_NAME
    )
    print("Waiting...")
    try:
        create_waiter = cf.get_waiter("stack_delete_complete")
        create_waiter.wait(StackName=RESOURCE_STACK_NAME)
        print("Successfully deleted the resources stack.")
    except botocore.exceptions.WaiterError as err:
        print("Error: Stack deletion failed. Check the CloudFormation link for more information.")
        raise

    print("All Fleet Provisioning demo resources have been cleaned up.")

# Delete the files created by the demo and reset demo_config.h
def reset_files():
    script_file_dir_abs_path = os.path.abspath(os.path.dirname(__file__))
    # Remove Claim credentials
    if os.path.exists(f"{KEY_OUT_NAME}"):
        os.remove(f"{KEY_OUT_NAME}")
    if os.path.exists(f"{CERT_OUT_NAME}"):
        os.remove(f"{CERT_OUT_NAME}")

    # Remove demo-generated Thing credentials
    if os.path.exists(f"{THING_PRIVATE_KEY_NAME}"):
        os.remove(f"{THING_PRIVATE_KEY_NAME}")
    if os.path.exists(f"{THING_PUBLIC_KEY_NAME}"):
        os.remove(f"{THING_PUBLIC_KEY_NAME}")
    if os.path.exists(f"{THING_CERT_NAME}"):
        os.remove(f"{THING_CERT_NAME}")

    # Reset demo_config.h
    template_file = open(f"{script_file_dir_abs_path}/demo_config_empty.templ", 'r')
    file_text = template_file.read()

    header_file = open(f"{script_file_dir_abs_path}/../demo_config.h", "w")
    header_file.write(file_text)
    header_file.close()
    template_file.close()
    print("Credentials removed and demo_config.h reset.")

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
    print("\nThis script will delete ALL Things, credentials, and resources which were created by demo_setup.py and the Fleet Provisioning demo.")
    print("It may take several minutes for all of the resources to be deleted.")
    if args.force or input("Are you sure you want to do this? (y/n) ") == "y":
        print()
        reset_files()
        delete_resources()


if __name__ == "__main__":
    main()
