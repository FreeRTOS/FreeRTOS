It is our recommendation to always use strong mutual authentication in any Internet of Things
application. Instructions below are for setting up a local httpbin server that communicates
over plaintext for use with this HTTP demo.
1. Install Docker from https://docs.docker.com/docker-for-windows/install/
2. Run httpbin from port 80.
     docker pull kennethreitz/httpbin
     docker run -p 80:80 kennethreitz/httpbin
3. Verify that httpbin server is running locally and listening on port 80
   by following the steps below.
     a. Open PowerShell.
     b. Type in command `netstat -a -p TCP | findstr 80` to check if there
        is an active connection listening on port 80.
     c. Verify that there is an output as shown below
        `TCP    0.0.0.0:80           <HOST-NAME>:0       LISTENING`
4. Make sure the httpbin server is allowed to communicate through
   Windows Firewall.
   After running this demo, consider disabling the httpbin server to
   communicate through Windows Firewall to avoid unwanted network traffic
   to your machine.
5. After verifying that a httpbin server is running successfully, update
   the config `democonfigSERVER_HOSTNAME` in `demo_config.h` to the local IP
   address of your Windows host machine. Please note that "localhost" or address
   "127.0.0.1" will not work as this example is running on a Windows Simulator and
   not on a Windows host natively. Also note that, if the Windows host is using a
   Virtual Private Network(VPN), connection to the server may not work.
