The subdirectories of this directory contain multiple examples that demonstrate
coreMQTT using in both single and multi-threaded scenarios, as well as with
both plain text and authenticated and encrypted network interfaces.

The multi threaded example creates an MQTT agent (or daemon task).  It is thread
safe because only the agent task is allowed to access the coreMQTT API - hence
the API is only accessed from one FreeRTOS task.  Other tasks and interrupts
needing to interact with the MQTT agent do so through a thread safe queue.
We are generalising this technique for future coreMQTT releases, which will have
a re-usable agent component.

! Plain text examples are for ease of evaluation only - product devices should
! always use authenticated and encrypted communication.  Never send private or
! sensitive data on an unencrypted connection.


In MQTT demos, for each iteration we send 3 QoS2 MQTT Publish messages and receive
3 QoS2 MQTT Publish messages because we are subscribed to the same topics we
publish on. Each QoS2 MQTT publish message results in total 4 MQTT packets
being exchanged between the device and the broker. For example, the following
MQTT packets are exchanged between the device and the broker when the device
sends a QoS2 MQTT Publish message:

   Device                   Broker
      |                         |
      |      Publish QoS2       |
      +------------------------>|
      |        PUBREC           |
      |<------------------------+
      |        PUBREL           |
      +------------------------>|
      |       PUBCOMP           |
      |<------------------------+
      |                         |

The coreMQTT library keeps track of the in-flight publish messages (i.e. the
publish messages for which the above 4 packets sequence is not complete) in 2
application supplied arrays - pOutgoingPublishRecords and pIncomingPublishRecords
in this demo. We need to set the value of mqttexamplePROCESS_LOOP_TIMEOUT_MS to
ensure that we can keep up with the incoming MQTT packets. We did some experiments
to find the optimal value of mqttexamplePROCESS_LOOP_TIMEOUT_MS. The following
table lists the results of our experiments:

 +------------------------------------+-------------+----------------------------------------------------+
  | mqttexamplePROCESS_LOOP_TIMEOUT_MS | Iteration # | No. of pending messages in pOutgoingPublishRecords |
  +------------------------------------+-------------+----------------------------------------------------+
  |               500                  | 0           | 0                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 1           | 3                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 2           | 3                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 3           | 6                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 4           | 9                                                  |
  +------------------------------------+-------------+----------------------------------------------------+
  |              1000                  | 0           | 0                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 1           | 1                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 2           | 3                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 3           | 4                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 4           | 6                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 5           | 7                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 6           | 7                                                  |
  +------------------------------------+-------------+----------------------------------------------------+
  |              1500                  | 0           | 0                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 1           | 0                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 2           | 1                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 3           | 2                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 4           | 3                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 5           | 3                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 6           | 0                                                  |
  +------------------------------------+-------------+----------------------------------------------------+
  |              2000                  | 0           | 0                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 1           | 0                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 2           | 0                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 3           | 0                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 4           | 0                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 5           | 0                                                  |
  +                                    +-------------+----------------------------------------------------+
  |                                    | 6           | 0                                                  |
  +------------------------------------+-------------+----------------------------------------------------+

As clear from the above table, with the value of mqttexamplePROCESS_LOOP_TIMEOUT_MS
set to 2000, we are able to keep up with the incoming MQTT packets every iteration.
mqttexamplePROCESS_LOOP_TIMEOUT_MS can be updated according to the requirements.

