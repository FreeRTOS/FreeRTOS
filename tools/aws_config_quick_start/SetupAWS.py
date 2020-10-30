#!/usr/bin/env python

import os
import sys
import json
import pprint
import argparse
import boto3
import misc
import certs
import thing
import policy

pp = pprint.PrettyPrinter(indent=4)


def check_aws_configuration():
    mysession = boto3.session.Session()
    if not mysession._session._config['profiles']:
        print("AWS not configured. Please run `aws configure`.")
        sys.exit(1)


def prereq():
    with open('configure.json') as configure_file:
        json_text = json.load(configure_file)

    # Create a Thing
    thing_name = json_text['thing_name']
    thing_obj = thing.Thing(thing_name)
    if not thing_obj.create():

        # Create a Certificate
        cert_obj = certs.Certificate()
        result = cert_obj.create()

        # Store certId
        cert_id = result['certificateId']
        cert_id_filename = thing_name + '_cert_id_file.txt'
        cert_id_file = open(cert_id_filename, 'w')
        cert_id_file.write(cert_id)
        cert_id_file_path = os.path.abspath(cert_id_filename)
        os.chmod(cert_id_file_path, 0o444)
        cert_id_file.close()

        # Store cert_pem as file
        cert_pem = result['certificatePem']
        cert_pem_filename = thing_name + '_cert_pem_file.pem'
        cert_pem_file = open(cert_pem_filename, 'w')
        cert_pem_file.write(cert_pem)
        cert_pem_file_path = os.path.abspath(cert_pem_filename)
        os.chmod(cert_pem_file_path, 0o444)
        cert_pem_file.close()

        # Store private key PEM as file
        private_key_pem = result['keyPair']['PrivateKey']
        private_key_pem_filename = thing_name + '_private_key_pem_file.pem'
        private_key_pem_file = open(private_key_pem_filename, 'w')
        private_key_pem_file.write(private_key_pem)
        private_key_pem_file_path = os.path.abspath(private_key_pem_filename)
        os.chmod(private_key_pem_file_path, 0o444)
        private_key_pem_file.close()

        # Create a Policy
        policy_document = misc.create_policy_document()
        policy_name = thing_name + '_amazon_freertos_policy'
        policy_obj = policy.Policy(policy_name, policy_document)
        policy_obj.create()

        # Attach certificate to Thing
        cert_obj.attach_thing(thing_name)

        # Attach policy to certificate
        cert_obj.attach_policy(policy_name)


def update_credential_file():
    with open('configure.json') as configure_file:
        json_text = json.load(configure_file)

    source_dir = os.path.expanduser(json_text['FreeRTOS_source_dir'])
    thing_name = json_text['thing_name']

    # Read cert_pem from file
    cert_pem_filename = thing_name + '_cert_pem_file.pem'
    try:
        cert_pem_file = open(cert_pem_filename, 'r')
    except IOError:
        print("{} file not found. Run prerequisite step"
              .format(cert_pem_filename))
        sys.exit(1)
    else:
        cert_pem = cert_pem_file.read()

    # Read private_key_pem from file
    private_key_pem_filename = thing_name + '_private_key_pem_file.pem'
    try:
        private_key_pem_file = open(private_key_pem_filename, 'r')
    except IOError:
        print("{} file not found. Run prerequisite step"
              .format(private_key_pem_filename))
        sys.exit(1)
    else:
        private_key_pem = private_key_pem_file.read()

    # Modify 'demo_config.h' file
    misc.write_client_credentials(
        source_dir,
        thing_name=thing_name,
        client_certificate_pem=cert_pem,
        client_private_key_pem=private_key_pem,
        cleanup=False)


def delete_prereq():
    with open('configure.json') as configure_file:
        json_text = json.load(configure_file)

    # Delete Thing
    thing_name = json_text['thing_name']
    thing_obj = thing.Thing(thing_name)
    if thing_obj.exists():
        thing_obj.delete()

    # Delete certificate
    cert_id_filename = thing_name + '_cert_id_file.txt'
    if os.path.exists(cert_id_filename):
        cert_id_file = open(cert_id_filename, 'r')
        cert_id = cert_id_file.read()
        cert_obj = certs.Certificate(cert_id)
        cert_obj.delete()
        cert_id_file.close()
        cert_id_file_path = os.path.abspath(cert_id_filename)
        os.chmod(cert_id_file_path, 0o666)
        os.remove(cert_id_filename)

    # Delete cert_pem file and private_key_pem file
    cert_pem_filename = thing_name + '_cert_pem_file.pem'
    if os.path.exists(cert_pem_filename):
        cert_pem_file_path = os.path.abspath(cert_pem_filename)
        os.chmod(cert_pem_file_path, 0o666)
        os.remove(cert_pem_filename)

    private_key_pem_filename = thing_name + '_private_key_pem_file.pem'
    if os.path.exists(private_key_pem_filename):
        private_key_pem_file_path = os.path.abspath(private_key_pem_filename)
        os.chmod(private_key_pem_file_path, 0o666)
        os.remove(private_key_pem_filename)

    # Delete policy
    policy_name = thing_name + '_amazon_freertos_policy'
    policy_obj = policy.Policy(policy_name)
    if policy_obj.exists():
        policy_obj.delete()


def cleanup_creds():
    with open('configure.json') as file:
        json_text = json.load(file)

    source_dir = os.path.expanduser(json_text['FreeRTOS_source_dir'])

    # Cleanup 'demo_config.h' file
    misc.write_client_credentials(source_dir, cleanup=True)


def setup():
    prereq()
    update_credential_file()
    print("Setup Completed")


def cleanup():
    delete_prereq()
    cleanup_creds()
    print("Cleanup Completed")


def list_certificates():
    client = boto3.client('iot')
    certs = client.list_certificates()['certificates']
    pp.pprint(certs)


def list_things():
    client = boto3.client('iot')
    things = client.list_things()['things']
    pp.pprint(things)


def list_policies():
    client = boto3.client('iot')
    policies = client.list_policies()['policies']
    pp.pprint(policies)


if __name__ == "__main__":

    arg_parser = argparse.ArgumentParser()
    subparsers = arg_parser.add_subparsers(help='Available commands',
                                           dest='command')
    subparsers.add_parser('setup', help='Setup AWS IoT')
    subparsers.add_parser('cleanup', help='Cleanup AWS IoT')
    subparsers.add_parser('list_certificates', help='List certificates')
    subparsers.add_parser('list_things', help='List things')
    subparsers.add_parser('list_policies', help='List policies')
    subparsers.add_parser('prereq', help='Setup prerequisites for AWS IoT')
    subparsers.add_parser('update_creds', help='Update credential files')
    subparsers.add_parser('delete_prereq', help='Delete prerequisites created')
    subparsers.add_parser('cleanup_creds', help='Cleanup credential files')
    args = arg_parser.parse_args()
    check_aws_configuration()

    if args.command == 'setup':
        setup()
    elif args.command == 'cleanup':
        cleanup()
    elif args.command == 'list_certificates':
        list_certificates()
    elif args.command == 'list_things':
        list_things()
    elif args.command == 'list_policies':
        list_policies()
    elif args.command == 'prereq':
        prereq()
    elif args.command == 'update_creds':
        update_credential_file()
    elif args.command == 'delete_prereq':
        delete_prereq()
    elif args.command == 'cleanup_creds':
        cleanup_creds()
    else:
        print("Command does not exist")

    sys.exit(0)
