#include <sys/socket.h> // <-- This one
#include <linux/if.h>
#include <linux/if_tun.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <sys/ioctl.h>
#include <unistd.h>
#include <stdlib.h>

int tun_alloc(char *dev, int flags) {

  struct ifreq ifr;
  int fd, err;
  char *clonedev = "/dev/net/tun";

  /* Arguments taken by the function:
   *
   * char *dev: the name of an interface (or '\0'). MUST have enough
   *   space to hold the interface name if '\0' is passed
   * int flags: interface flags (eg, IFF_TUN etc.)
   */

   /* open the clone device */
   if( (fd = open(clonedev, O_RDWR)) < 0 ) {
     return fd;
   }

   /* preparation of the struct ifr, of type "struct ifreq" */
   memset(&ifr, 0, sizeof(ifr));

   ifr.ifr_flags = flags;   /* IFF_TUN or IFF_TAP, plus maybe IFF_NO_PI */

   if (*dev) {
     /* if a device name was specified, put it in the structure; otherwise,
      * the kernel will try to allocate the "next" device of the
      * specified type */
     strncpy(ifr.ifr_name, dev, IFNAMSIZ);
   }

   /* try to create the device */
   if( (err = ioctl(fd, TUNSETIFF, (void *) &ifr)) < 0 ) {
     close(fd);
     return err;
   }

  /* if the operation was successful, write back the name of the
   * interface to the variable "dev", so the caller can know
   * it. Note that the caller MUST reserve space in *dev (see calling
   * code below) */
  strcpy(dev, ifr.ifr_name);

  /* this is the special file descriptor that the caller will use to talk
   * with the virtual interface */
  return fd;
}

void main() {

  printf("Starting tuntap\n");

  char tun_name[IFNAMSIZ];
  int nread, tun_fd;
  char *buffer;
  int buffer_size = 1600 * sizeof(char);

  /* Connect to the device */
  strcpy(tun_name, "tap0");
  tun_fd = tun_alloc(tun_name, IFF_TAP | IFF_NO_PI);  /* tun interface */

  if(tun_fd < 0){
    printf("Allocating interface failed...\n");
    return;
  }

  /* Now read data coming from the kernel */
  while(1) {
    /* Note that "buffer" should be at least the MTU size of the interface, eg 1500 bytes */
    buffer = malloc(buffer_size);
    nread = read(tun_fd, buffer, buffer_size);
    if(nread < 0) {
      printf("Reading from interface\n");
      close(tun_fd);
      return;
    }

    /* Do whatever with the data */
    printf("Read %d bytes from device %s\n", nread, tun_name);

    free(buffer);
  }
}
