# Presigned S3 URLs Generator	

`presigned_url_gen.py` generates pre-signed URLs for S3 HTTP GET and PUT request access.	

### Dependencies	

* Python 3+	
* boto3	
* argparse	

### Prerequisites	

1. Install the dependencies.	
   ```sh	
   pip install boto3 argparse	
   ```	

1. You will need an AWS Account with S3 access before beginning. You must install and configure the AWS CLI in order to	
   use this script.  	
   For information on AWS S3 please see: https://docs.aws.amazon.com/AmazonS3/latest/dev/Welcome.html  	
   For AWS CLI installation information please see: https://docs.aws.amazon.com/cli/latest/userguide/cli-chap-install.html  	
   For AWS CLI configuration information please see: https://docs.aws.amazon.com/cli/latest/userguide/cli-chap-configure.html	

   ```sh	
   aws configure	
   ```	

### Usage	

1. Run `presigned_url_gen.py` with your s3 bucket name and s3 object key.	
   ```sh	
   ./presigned_urls_gen.py --bucket <YOUR BUCKET NAME> --key <YOUR OBJECT KEY>	
   ```	
   An example expected output:	
   ```	
   #define democonfigS3_PRESIGNED_GET_URL    "https://aws-s3-endpoint/object-key.txt?X-Amz-Algorithm=AWS4-HMAC-SHA256&X-Amz-Credential=ABABABABABABABABABAB%2F20201027%2Fus-west-2%2Fs3%2Faws4_request&X-Amz-Date=20201027T194726Z&X-Amz-Expires=3600&X-Amz-SignedHeaders=host&X-Amz-Signature=SomeHash12345UrlABcdEFgfIjK"	
   #define democonfigS3_PRESIGNED_PUT_URL    "https://aws-s3-endpoint/object-key.txt?X-Amz-Algorithm=AWS4-HMAC-SHA256&X-Amz-Credential=ABABABABABABABABABAB%2F20201027%2Fus-west-2%2Fs3%2Faws4_request&X-Amz-Date=20201027T194726Z&X-Amz-Expires=3600&X-Amz-SignedHeaders=host&X-Amz-Signature=SomeHash12345UrlLMnmOPqrStUvW"	
   ```	
1. Copy and paste the output to `demo_config.h` for macros `democonfigS3_PRESIGNED_GET_URL` and `democonfigS3_PRESIGNED_PUT_URL`.	
   ```c	
   #define democonfigS3_PRESIGNED_GET_URL    "https://aws-s3-endpoint/object-key.txt?X-Amz-Algorithm=AWS4-HMAC-SHA256&X-Amz-Credential=ABABABABABABABABABAB%2F20201027%2Fus-west-2%2Fs3%2Faws4_request&X-Amz-Date=20201027T194726Z&X-Amz-Expires=3600&X-Amz-SignedHeaders=host&X-Amz-Signature=SomeHash12345UrlABcdEFgfIjK"	
   #define democonfigS3_PRESIGNED_PUT_URL    "https://aws-s3-endpoint/object-key.txt?X-Amz-Algorithm=AWS4-HMAC-SHA256&X-Amz-Credential=ABABABABABABABABABAB%2F20201027%2Fus-west-2%2Fs3%2Faws4_request&X-Amz-Date=20201027T194726Z&X-Amz-Expires=3600&X-Amz-SignedHeaders=host&X-Amz-Signature=SomeHash12345UrlLMnmOPqrStUvW"	
   ```	

### Parameters	

#### --bucket	
The name of the S3 bucket from which the demo will download or upload.	

#### --key	
The name of the existing object you wish to download (GET),	
or the name of the object you wish to upload (PUT).	

#### --region	
Optional parameter for the AWS region in which the bucket is located.	