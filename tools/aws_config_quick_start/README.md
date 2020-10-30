## Script to setup the AWS resources through command line

This script automates the process of [Prerequisites](https://docs.aws.amazon.com/freertos/latest/userguide/freertos-prereqs.html) and the configuring the files `demo_config.h` to connect to AWS IoT.

Make sure you have `aws cli` configured on your machine with access_key, secret_key and region.

Open the file `configure.json` and fill in the following details:
* FreeRTOS_source_dir : The path of the FreeRTOS directory. By default, this is set to the top level of this repo (../..).
* thing_name : Name of the thing you want to create

**Options to use with the script**
1. To setup your Thing, and update credentials file, type the command: `python SetupAWS.py setup`
2. To cleanup the Thing you created with the script, and revert changes in credentials file, type the command: `python SetupAWS.py cleanup`
3. To only create thing, certificate and policy, type the command: `python SetupAWS.py prereq`
4. To update the files `demo_config.h` with thing name and the certificate keys, type the command `python SetupAWS.py update_creds`
5. To delete the thing, certificate and policy created by the script, type the command: `python SetupAWS.py delete_prereq`
6. To revert the changes in the file `demo_config.h`, type the command: `python SetupAWS.py cleanup_creds`
7. To list your certificates, type the command: `python SetupAWS.py list_certificates`
8. To list your policies, type the command: `python SetupAWS.py list_policies`
9. To list your things, type the command: `python SetupAWS.py list_things`
