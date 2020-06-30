#ifndef MQTT_INTERNAL_H_
#define MQTT_INTERNAL_H_

/* Include config file before other headers. */
#include "mqtt_config.h"

#ifndef LogError
    #define LogError( message )
#endif

#ifndef LogWarn
    #define LogWarn( message )
#endif

#ifndef LogInfo
    #define LogInfo( message )
#endif

#ifndef LogDebug
    #define LogDebug( message )
#endif

#endif /* ifndef MQTT_INTERNAL_H_ */
