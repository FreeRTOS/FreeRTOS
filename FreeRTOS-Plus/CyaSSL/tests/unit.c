/* unit.c unit tests driver */
#include <stdio.h>
#include "unit.h"

int main(int argc, char** argv)
{
    printf("hello unit tests\n");

    if (ApiTest() != 0)
        printf("api test failed\n");

    if (HashTest() != 0)
        printf("hash test failed\n");

    return 0;
}
