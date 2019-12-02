
// Check for the various File API support.
if (window.File && window.FileReader && window.FileList && window.Blob) {
  // Success! All the File APIs are supported.
} else {
  alert('Please use a web browser that supports HTML5 file APIs.')
}

function formatCredentialTextForHeader (credentialText) {
  // Replace any CR/LF pairs with a newline character.
  credentialText = credentialText.replace(/\r\n/g, '\n')

  // Add line endings for C-language variable declaration.
  credentialText = credentialText.replace(/\n/g, '\\n" \\\n    "')

  // Remove '\n"' from the last line of the declaration and add a semicolon.
  credentialText = credentialText.slice(0, -9) + '"\n'
  return credentialText
}

function generateCertificateConfigurationHeader () {
  var pemCertificateText = ''
  var pemPrivateKeyText = ''
  var filename = 'aws_iot_demo_profile.h'
  var outputText = ''

  var readerCertificate = new FileReader()
  var readerPrivateKey = new FileReader()

  // Start certificate read
  readerCertificate.readAsText(pemInputFileCertificate.files[0])

  // Define a handler to create appropriate client certificate file text.
  readerCertificate.onload = function (e) {
    pemCertificateText = e.target.result

    // Add C-language variable declaration plus EOL formatting.
    pemCertificateText = '    "' + formatCredentialTextForHeader(pemCertificateText)

    // Because this is async, read next file inline.
    readerPrivateKey.readAsText(pemInputFilePrivateKey.files[0])
  }

  // Define a handler to create appropriate private key file text.
  readerPrivateKey.onload = function (e) {
    pemPrivateKeyText = e.target.result

    // Add C-language variable declaration plus EOL formatting.
    pemPrivateKeyText = '    "' + formatCredentialTextForHeader(pemPrivateKeyText)

    outputText = awsIotProfileTemplate
    outputText = outputText.replace('<IOTEndpoint>', '"' + document.getElementById('AWSEndpoint').value + '"')
    outputText = outputText.replace('<IOTThingName>', '"' + document.getElementById('thingName').value + '"')
    outputText = outputText.replace('<ClientCertificatePEM>', pemCertificateText)
    outputText = outputText.replace('<ClientPrivateKeyPEM>', pemPrivateKeyText)

    // Because this is async, handle download generation inline.
    var downloadBlob = new Blob([outputText], { type: 'text/plain' })
    if (window.navigator.msSaveOrOpenBlob) {
      window.navigator.msSaveBlob(downloadBlob, filename)
    } else {
      var downloadLink = document.createElement('a')
      downloadLink.href = window.URL.createObjectURL(downloadBlob)
      downloadLink.download = filename
      document.body.appendChild(downloadLink)
      downloadLink.click()
      document.body.removeChild(downloadLink)
    }
  }
}
