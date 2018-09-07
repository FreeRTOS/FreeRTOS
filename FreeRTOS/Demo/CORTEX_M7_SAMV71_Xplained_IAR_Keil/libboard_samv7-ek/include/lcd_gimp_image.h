#ifndef _GIMP_IMAGE_
#define _GIMP_IMAGE_

#include <stdint.h>

typedef struct _SGIMPImage
{
  uint32_t dwWidth;
  uint32_t dwHeight;
  uint32_t dwBytes_per_pixel; /* 3:RGB, 4:RGBA */ 
  uint8_t* pucPixel_data ;
} SGIMPImage ;

#endif // _GIMP_IMAGE_
