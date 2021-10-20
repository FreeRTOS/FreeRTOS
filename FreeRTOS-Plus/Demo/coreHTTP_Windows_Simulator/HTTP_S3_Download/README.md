# Configure HTTP S3 Download Demo using SigV4 Library.

Following steps needs to be followed to configure HTTP S3 Download Demo to use SigV4 library for authenticating the requests sent to AWS S3.

### Prerequisites

1. You will need an AWS Account with S3 access before beginning. You must be familiar with AWS IoT and IAM to perform steps using the AWS CLI. You must install and configure the AWS CLI in order to follow the steps.  
   For information on AWS S3 please see: https://docs.aws.amazon.com/AmazonS3/latest/dev/Welcome.html  
   For AWS CLI installation information please see: https://docs.aws.amazon.com/cli/latest/userguide/cli-chap-install.html  
   For AWS CLI configuration information please see: https://docs.aws.amazon.com/cli/latest/userguide/cli-chap-configure.html

   ```sh
   aws configure
   ```

### Detailed Steps

#### 1. Create an AWS IoT thing: 

You may utilize an already existing AWS IoT Thing or create a new one in the IoT Core section of the AWS Management Console UI.

You may also use the AWS CLI with the following command to create a Thing, keeping track of its name:
```sh
aws iot create-thing --thing-name device_thing_name
```

#### 2. Register a certificate:

If your AWS IoT Thing already has a certificate attached to it, then that certificate's ARN can be used in [step 5](#5. attach-a-policy). Otherwise, you can create a certificate and attach it to the thing through IoT Core in the AWS Management Console UI. By doing any of these, you may skip to [step 3](#3-configure-an-iam-role).

It is also possible to sign the Thing's certificate using your own Certificate Authority (CA) certificate, and register both certificates with AWS IoT before your device can authenticate to AWS IoT. If you do not already have a CA certificate, you can use OpenSSL to create a CA certificate, as described in [Use Your Own Certificate](https://docs.aws.amazon.com/iot/latest/developerguide/device-certs-your-own.html). To register your CA certificate with AWS IoT, follow the steps on [Registering Your CA Certificate](https://docs.aws.amazon.com/iot/latest/developerguide/device-certs-your-own.html#register-CA-cert).

You then have to create a device certificate signed by the CA certificate and register it with AWS IoT, which you can do by following the steps on [Creating a Device Certificate Using Your CA Certificate](https://docs.aws.amazon.com/iot/latest/developerguide/device-certs-your-own.html#create-device-cert). Save the certificate and the corresponding key pair; you will use them when you request a security token later. Also, remember the password you provide when you create the certificate.

Run the following command in the AWS CLI to attach the device certificate to your thing so that you can use thing attributes in policy variables.

```sh
aws iot attach-thing-principal --thing-name device_thing_name --principal <certificate-arn>
```
    
#### 3. Configure an IAM role: 

Next, configure an IAM role in your AWS account that will be assumed by the credentials provider on behalf of your device. You are required to associate two policies with the role: a trust policy that controls who can assume the role, and an access policy that controls which actions can be performed on which resources by assuming the role.

The following trust policy grants the credentials provider permission to assume the role. Put it in a text document and save the document with the name, trustpolicyforiot.json.

```
{
   "Version": "2012-10-17",
   "Statement": {
   "Effect": "Allow",
   "Principal": {"Service": "credentials.iot.amazonaws.com"},
   "Action": "sts:AssumeRole"
    }
}
```
Run the following command in the AWS CLI to create an IAM role with the preceding trust policy.

```sh
aws iam create-role --role-name s3-access-role --assume-role-policy-document file://trustpolicyforiot.json
```
The following s3 access policy allows you to perform actions on S3. Put the following policy in a text document and save the document with the name `accesspolicyfors3.json`.
```
{
   "Version": "2012-10-17",
   "Statement": {
   "Effect": "Allow",
   "Action": [
             "s3:GetObject"
             ],
   "Resource": "arn:aws:s3:::BUCKET_NAME/*"
    }
}
```
Run the following command in the AWS CLI to create the access policy.
```sh
aws iam create-policy --policy-name accesspolicyfors3 --policy-document file://accesspolicyfors3.json
```
Finally, run the following command in the AWS CLI to attach the access policy to your role.
```sh
aws iam attach-role-policy --role-name s3-access-role --policy-arn arn:aws:iam::<your_aws_account_id>:policy/accesspolicyfors3
```

Configure the PassRole permissions

The IAM role that you have created must be passed to AWS IoT to create a role alias, as described in Step 4. The IAM user who performs the operation requires `iam:PassRole` permission to authorize this action. You also should add permission for the `iam:GetRole` action to allow the IAM user to retrieve information about the specified role. Create the following policy to grant `iam:PassRole` and `iam:GetRole` permissions. Name this policy `passrolepermission.json`.
```
{
           "Version": "2012-10-17",
           "Statement": {
             "Effect": "Allow",
             "Action": [
                 "iam:GetRole",
                 "iam:PassRole"
             ],
             "Resource": "arn:aws:iam::<your_aws_account_id>:role/s3-access-role"
           }
}
```

Run the following command in the AWS CLI to create the policy in your AWS account.
```sh
aws iam create-policy --policy-name passrolepermission --policy-document file://passrolepermission.json
```

Now, run the following command to attach the policy to the IAM user.
```sh
aws iam attach-user-policy --policy-arn arn:aws:iam::<your_aws_account_id>:policy/passrolepermission --user-name <user_name>
```

#### 4. Create a role alias: 
         
Now that you have configured the IAM role, you will create a role alias with AWS IoT. You must provide the following pieces of information when creating a role alias:

RoleAlias: This is the primary key of the role alias data model and hence a mandatory attribute. It is a string; the minimum length is 1 character, and the maximum length is 128 characters.

RoleArn: This is the [Amazon Resource Name (ARN)](https://docs.aws.amazon.com/general/latest/gr/aws-arns-and-namespaces.html) of the IAM role you have created. This is also a mandatory attribute.

CredentialDurationSeconds: This is an optional attribute specifying the validity (in seconds) of the security token. The minimum value is 900 seconds (15 minutes), and the maximum value is 3,600 seconds (60 minutes); the default value is 3,600 seconds, if not specified.

Run the following command in the AWS CLI to create a role alias. Use the credentials of the user to whom you have given the iam:PassRole permission.
```sh
aws iot create-role-alias --role-alias name-s3-access-role-alias --role-arn arn:aws:iam::<your_aws_account_id>:role/s3-access-role --credential-duration-seconds 3600
```

#### 5. Attach a policy: 
You created and registered a certificate with AWS IoT earlier for successful authentication of your device. Now, you need to create and attach a policy to the certificate to authorize the request for the security token.
```
{
           "Version": "2012-10-17",
           "Statement": [
             {
               "Effect": "Allow",
               "Action": "iot:AssumeRoleWithCertificate",
               "Resource": "arn:aws:iot:<aws_region_name>:<your_aws_account_id>:rolealias/name-s3-access-role-alias"
             }
           ]
}
```
Run the following command in the AWS CLI to create the policy in your AWS IoT database.
```sh
aws iot create-policy --policy-name Thing_Policy_Name --policy-document file://thingpolicy.json
```
Use the following command to attach the policy with the certificate you registered earlier.
```sh
aws iot attach-policy --policy-name Thing_Policy_Name --target <certificate-arn>
```

#### 6. Request a security token: 
        
Make an HTTPS request to the credentials provider to fetch a security token. You have to supply the following information:

Certificate and key pair: Because this is an HTTP request over TLS mutual authentication, you have to provide the certificate and the corresponding key pair to your client while making the request. Use the same certificate and key pair that you used during certificate registration with AWS IoT.

RoleAlias: Provide the role alias (in this example, Thermostat-dynamodb-access-role-alias) to be assumed in the request.

ThingName: Provide the thing name that you created earlier in the AWS IoT thing registry database. This is passed as a header with the name, x-amzn-iot-thingname. Note that the thing name is mandatory only if you have thing attributes as policy variables in AWS IoT or IAM policies.

Run the following command in the AWS CLI to obtain your AWS account-specific endpoint for the credentials provider. See the [DescribeEndpoint API documentation](https://docs.aws.amazon.com/iot/latest/apireference/API_DescribeEndpoint.html) for further details.

```sh
aws iot describe-endpoint --endpoint-type iot:CredentialProvider
```
The following is sample output of the describe-endpoint command. It contains the endpointAddress.
```
{
   "endpointAddress": "<your_aws_account_specific_prefix>.credentials.iot.us-east-1.amazonaws.com"
}
```

#### 7. Copy and paste the output to `demo_config.h` for macros `democonfigIOT_CREDENTIAL_PROVIDER_ENDPOINT`.
```c
#define democonfigIOT_CREDENTIAL_PROVIDER_ENDPOINT    "<your_aws_account_specific_prefix>.credentials.iot.us-east-1.amazonaws.com"

#define CLIENT_CERT_PATH "path of the client certificate downloaded when setting up the device certificate in AWS IoT Account Setup"

#define CLIENT_PRIVATE_KEY_PATH "path of the private key downloaded when setting up the device certificate in AWS IoT Account Setup"
```

#### 8. After the following the above steps, configure the below macros in `demo_config.h`.
```c
#define democonfigIOT_THING_NAME                  "Name of IOT Thing that you provided in STEP 1" 
#define democonfigIOT_CREDENTIAL_PROVIDER_ROLE    "Name of ROLE ALIAS that you provided in STEP 4"
#define democonfigS3_BUCKET_NAME                  "Name of Bucket that contains the object that needs to be downloaded"
#define democonfigS3_BUCKET_REGION                "Region where Bucket is located"
#define democonfigS3_OBJECT_NAME                  "Name of object that needs to be downloaded from AWS S3"
```
         
### Parameters

#### device_thing_name
The name of the AWS IoT thing for your device registered with AWS IoT core.

#### thing_name-s3-access-role-alias
The name for the role alias for S3.

#### Thing_Policy_Name
The name of the policy attached to the device certificate in [step 5](#5-attach-a-policy).

#### BUCKET_NAME
The name of the S3 bucket from which the demo will download.
