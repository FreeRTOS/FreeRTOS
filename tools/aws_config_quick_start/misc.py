#!/usr/bin/env python

import os
import boto3


def describe_endpoint():
    client = boto3.client('iot')
    endpoint = client.describe_endpoint(endpointType='iot:Data-ATS')
    return endpoint['endpointAddress']


def get_account_id():
    client = boto3.client('sts')
    aws_account_id = client.get_caller_identity()['Account']
    return aws_account_id.strip('\n')


def get_aws_region():
    my_session = boto3.session.Session()
    aws_region = my_session.region_name
    return aws_region.strip('\n')


def create_policy_document():
    this_file_directory = os.getcwd()
    policy_document = os.path.join(this_file_directory,
                                   'policy_document.templ')
    region_name = str(get_aws_region())
    aws_account_id = str(get_account_id())
    with open(policy_document) as policy_document_file:
        policy_document_text = policy_document_file.read()

    # Replace Account ID and AWS Region
    policy_document_text = policy_document_text.replace('<aws-region>',
                                                        region_name)
    policy_document_text = policy_document_text.replace('<aws-account-id>',
                                                        aws_account_id)

    return policy_document_text


def format_credential_keys_text(credential_text):
    credential_text_lines = credential_text.split('\n')
    formatted_credential_text_lines = []

    for credential_text_line in credential_text_lines:
        if credential_text_line.strip():
            formatted_credential_text_line = '    {:68s}'\
                .format('"' + credential_text_line + '\\n"')
            formatted_credential_text_lines.append(
                formatted_credential_text_line)

    formatted_credential_text = ' \\\n'.join(formatted_credential_text_lines)
    return formatted_credential_text


def write_client_credentials(
        source_dir,
        thing_name='',
        client_certificate_pem='',
        client_private_key_pem='',
        cleanup=False):

    file_to_modify = os.path.join(source_dir,
                                  'FreeRTOS-Plus',
                                  'Demo',
                                  'coreMQTT_Windows_Simulator',
                                  'MQTT_Mutual_Auth',
                                  'demo_config.h')
    file_text = ''

    if cleanup:
        filename = "demo_config_empty.templ"
        with open(filename, 'r') as template_file:
            file_text = template_file.read()

    else:
        endpoint = describe_endpoint()
        client_certificate_pem =\
            format_credential_keys_text(client_certificate_pem)
        client_private_key_pem =\
            format_credential_keys_text(client_private_key_pem)

        filename = "demo_config.templ"
        with open(filename, 'r') as template_file:
            file_text = template_file.read()
            file_text = file_text.replace("<IOTEndpoint>",
                                          "\"" + endpoint + "\"")
            file_text = file_text.replace("<IOTThingName>",
                                          "\"" + thing_name + "\"")
            file_text = file_text.replace("<ClientCertificatePEM>",
                                          client_certificate_pem)
            file_text = file_text.replace("<ClientPrivateKeyPEM>",
                                          client_private_key_pem)

    header_file = open(str(file_to_modify), 'w')
    header_file.write(file_text)
    header_file.close()
