#!/usr/bin/env python3

import boto3
from botocore.client import Config
import argparse


def get_presigned_urls(bucket_name, key_name, region_name) -> None:
    """
    Prints the presigned GET and PUT URLs assigned to the demo specific C
    macros, for the given object key in the given S3 bucket. If the region
    parameter is not defined, boto3 will use the one configured using AWS CLI.
    The URLs are presigned with AWS's Signature Version 4.
    Args:
        bucket_name (str): S3 bucket
        key_name (str):  S3 object key
        region_name (str): S3 bucket's region
    """

    # Get the service client.
    # SigV2 is being deprecated. If the boto3 installation in the current Python environment has an older version of
    # the package, then this configuration forces the use of SigV4.
    s3 = boto3.client("s3", config=Config(signature_version="s3v4", region_name=region_name))

    client_method_dict = {"GET": "get_object", "PUT": "put_object"}

    # Generate the URL to get 'key-name' from 'bucket-name'
    for method in client_method_dict.keys():
        url = s3.generate_presigned_url(
            ClientMethod=client_method_dict[method],
            Params={"Bucket": bucket_name, "Key": key_name},
        )
        print("#define democonfigS3_PRESIGNED_" + method + "_URL" + "    " + '"' + url + '"\n')


def main():
    """
    Generate demo C macro strings, on the console, for the input S3 bucket and object key.
    """
    parser = argparse.ArgumentParser(description="S3 Presigned URL Generator. See README.md")
    parser.add_argument(
        "--bucket",
        action="store",
        required=True,
        dest="bucket_name",
        help="The name of the S3 bucket of interest.",
    )
    parser.add_argument(
        "--key",
        action="store",
        required=True,
        dest="key_name",
        help="The name of the S3 Object in the bucket. This is referred to as a 'key'",
    )
    parser.add_argument(
        "--region",
        action="store",
        required=False,
        dest="region_name",
        help="The region in which the S3 bucket of interest is created.",
    )
    args = parser.parse_args()

    get_presigned_urls(args.bucket_name, args.key_name, args.region_name)


if __name__ == "__main__":  # pragma: no cover
    main()
