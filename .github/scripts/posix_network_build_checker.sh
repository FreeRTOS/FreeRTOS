
PROJECT=$1
echo "Verifying url links of: ${PROJECT}"
if [ ! -d "$PROJECT" ]
then
    echo "Directory passed does not exist"
    exit 2
fi

SCRIPT_RET=0

set -o nounset        # Treat unset variables as an error

cd ${PROJECT}/FreeRTOS-Plus/Demo/FreeRTOS_Plus_TCP_Echo_Posix
make

SCRIPT_RET=$?

if [ "${SCRIPT_RET}" -eq 0 ]
then
    exit 0
else
    exit 1
fi
