See https://freertos.org/pkcs11/ for further information.

Contains projects that demonstrate the PKCS #11 library.
In order to run the mutual authentication demo, please convert the certificate and key PEM files associated with your IoT Thing, into a binary format DER.

To do this, use either the python script pkcs11_demo_setup.py or openssl.
If you choose to use the python script, pass in the absolute path of your PEM files.

If you are to use openssl, the following commands should be sufficient in converting from PEM to DER.
Certificate conversion:
openssl x509 -outform der -in $CERT_IN_NAME -out $CERT_OUT_NAME

Key conversion:
openssl pkcs8 -topk8 -inform PEM -outform DER -in $KEY_IN_NAME -out $KEY_OUT_NAME -nocrypt

Once the certificate and key are in binary format, move them to the same folder as the solution of the PKCS #11 demo you wish to run.

PKCS #11 is a standard for managing crypto operations. Please see the following for more information.
http://docs.oasis-open.org/pkcs11/pkcs11-base/v2.40/os/pkcs11-base-v2.40-os.html



