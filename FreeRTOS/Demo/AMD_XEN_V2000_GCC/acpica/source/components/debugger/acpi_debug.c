#include <stdint.h>
/*
*
* These functions are used by ACPICA to print debug message
* Empty definitions are placed here to link acpica withou
* code modification
*/
void tcgetattr(void);
void tcsetattr(void);
void usleep(void);
void AeLookupInitFileEntry(void);
void clock_gettime(void);
void __errno_location(void);
void fclose(void);
void fopen(void);
void  fprintf(void);
void fputs(void);
void fread(void);
void  vfprintf(void);
void fseek(void);
void ftell(void);
void getc(void);
int  isatty(int fd);
void memmove(void);
void MpSaveGpioInfo(void);
void MpSaveSerialInfo(void);
void perror(void);
void putc(void);
void stderr(void);
void stdin(void);
void stdout(void);
void fwrite(void);
void sleep(void);


void tcgetattr(void){};
void tcsetattr(void){};
void usleep(void){};
void AeLookupInitFileEntry(void){};
void clock_gettime(void){};
void __errno_location(void){};
void fclose(void){};
void fopen(void){};
void  fprintf(void){};
void fputs(void){};
void fread(void){};
void  vfprintf(void){};
void fseek(void){};
void ftell(void){};
void getc(void){};
int  isatty(int fd){return 0;};
void memmove(void){};
void MpSaveGpioInfo(void){};
void MpSaveSerialInfo(void){};
void perror(void){};
void putc(void){};
void stderr(void){};
void stdin(void){};
void stdout(void){};
void fwrite(void){};
void sleep(void){};
