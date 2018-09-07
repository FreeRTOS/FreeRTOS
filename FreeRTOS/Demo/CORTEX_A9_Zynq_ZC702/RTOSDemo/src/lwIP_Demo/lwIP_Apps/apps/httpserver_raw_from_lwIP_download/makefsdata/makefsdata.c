/**
 * makefsdata: Converts a directory structure for use with the lwIP httpd.
 *
 * This file is part of the lwIP TCP/IP stack.
 * 
 * Author: Jim Pettinato
 *         Simon Goldschmidt
 *
 * @todo:
 * - take TCP_MSS, LWIP_TCP_TIMESTAMPS and
 *   PAYLOAD_ALIGN_TYPE/PAYLOAD_ALIGNMENT as arguments
 */

#include <stdio.h>
#include <stdlib.h>
#ifdef WIN32
#define WIN32_LEAN_AND_MEAN
#include "windows.h"
#else
#include <dir.h>
#endif
#include <dos.h>
#include <string.h>

/* Compatibility defines Win32 vs. DOS */
#ifdef WIN32

#define FIND_T                        WIN32_FIND_DATAA
#define FIND_T_FILENAME(fInfo)        (fInfo.cFileName)
#define FIND_T_IS_DIR(fInfo)          ((fInfo.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) != 0)
#define FIND_T_IS_FILE(fInfo)         ((fInfo.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) == 0)
#define FIND_RET_T                    HANDLE
#define FINDFIRST_FILE(path, result)  FindFirstFileA(path, result)
#define FINDFIRST_DIR(path, result)   FindFirstFileA(path, result)
#define FINDNEXT(ff_res, result)      FindNextFileA(ff_res, result)
#define FINDFIRST_SUCCEEDED(ret)      (ret != INVALID_HANDLE_VALUE)
#define FINDNEXT_SUCCEEDED(ret)       (ret == TRUE)

#define GETCWD(path, len)             GetCurrentDirectoryA(len, path)
#define CHDIR(path)                   SetCurrentDirectoryA(path)

#define NEWLINE     "\r\n"
#define NEWLINE_LEN 2

#else

#define FIND_T                        struct fflbk
#define FIND_T_FILENAME(fInfo)        (fInfo.ff_name)
#define FIND_T_IS_DIR(fInfo)          ((fInfo.ff_attrib & FA_DIREC) == FA_DIREC)
#define FIND_T_IS_FILE(fInfo)         (1)
#define FIND_RET_T                    int
#define FINDFIRST_FILE(path, result)  findfirst(path, result, FA_ARCH)
#define FINDFIRST_DIR(path, result)   findfirst(path, result, FA_DIREC)
#define FINDNEXT(ff_res, result)      FindNextFileA(ff_res, result)
#define FINDFIRST_SUCCEEDED(ret)      (ret == 0)
#define FINDNEXT_SUCCEEDED(ret)       (ret == 0)

#define GETCWD(path, len)             getcwd(path, len)
#define CHDIR(path)                   chdir(path)

#endif

/* define this to get the header variables we use to build HTTP headers */
#define LWIP_HTTPD_DYNAMIC_HEADERS 1
#include "../httpd_structs.h"

#include "../../../lwip-1.4.0/src/core/ipv4/inet_chksum.c"
#include "../../../lwip-1.4.0/src/core/def.c"

/** (Your server name here) */
const char *serverID = "Server: "HTTPD_SERVER_AGENT"\r\n";

/* change this to suit your MEM_ALIGNMENT */
#define PAYLOAD_ALIGNMENT 4
/* set this to 0 to prevent aligning payload */
#define ALIGN_PAYLOAD 1
/* define this to a type that has the required alignment */
#define PAYLOAD_ALIGN_TYPE "unsigned int"
static int payload_alingment_dummy_counter = 0;

#define HEX_BYTES_PER_LINE 16

#define MAX_PATH_LEN 256

#define COPY_BUFSIZE 10240

int process_sub(FILE *data_file, FILE *struct_file);
int process_file(FILE *data_file, FILE *struct_file, const char *filename);
int file_write_http_header(FILE *data_file, const char *filename, int file_size,
                           u16_t *http_hdr_len, u16_t *http_hdr_chksum);
int file_put_ascii(FILE *file, const char *ascii_string, int len, int *i);
int s_put_ascii(char *buf, const char *ascii_string, int len, int *i);
void concat_files(const char *file1, const char *file2, const char *targetfile);

static unsigned char file_buffer_raw[COPY_BUFSIZE];
/* 5 bytes per char + 3 bytes per line */
static char file_buffer_c[COPY_BUFSIZE * 5 + ((COPY_BUFSIZE / HEX_BYTES_PER_LINE) * 3)];

char curSubdir[MAX_PATH_LEN];
char lastFileVar[MAX_PATH_LEN];
char hdr_buf[4096];

unsigned char processSubs = 1;
unsigned char includeHttpHeader = 1;
unsigned char useHttp11 = 0;
unsigned char precalcChksum = 0;

int main(int argc, char *argv[])
{
  FIND_T fInfo;
  FIND_RET_T fret;
  char path[MAX_PATH_LEN];
  char appPath[MAX_PATH_LEN];
  FILE *data_file;
  FILE *struct_file;
  int filesProcessed;
  int i;
  char targetfile[MAX_PATH_LEN];
  strcpy(targetfile, "fsdata.c");

  memset(path, 0, sizeof(path));
  memset(appPath, 0, sizeof(appPath));

  printf(NEWLINE " makefsdata - HTML to C source converter" NEWLINE);
  printf("     by Jim Pettinato               - circa 2003 " NEWLINE);
  printf("     extended by Simon Goldschmidt  - 2009 " NEWLINE NEWLINE);

  strcpy(path, "fs");
  for(i = 1; i < argc; i++) {
    if (argv[i][0] == '-') {
      if (strstr(argv[i], "-s")) {
        processSubs = 0;
      } else if (strstr(argv[i], "-e")) {
        includeHttpHeader = 0;
      } else if (strstr(argv[i], "-11")) {
        useHttp11 = 1;
      } else if (strstr(argv[i], "-c")) {
        precalcChksum = 1;
      } else if((argv[i][1] == 'f') && (argv[i][2] == ':')) {
        strcpy(targetfile, &argv[i][3]);
        printf("Writing to file \"%s\"\n", targetfile);
      }
    } else {
      strcpy(path, argv[i]);
    }
  }

  /* if command line param or subdir named 'fs' not found spout usage verbiage */
  fret = FINDFIRST_DIR(path, &fInfo);
  if (!FINDFIRST_SUCCEEDED(fret)) {
    /* if no subdir named 'fs' (or the one which was given) exists, spout usage verbiage */
    printf(" Failed to open directory \"%s\"." NEWLINE NEWLINE, path);
    printf(" Usage: htmlgen [targetdir] [-s] [-i] [-f:<filename>]" NEWLINE NEWLINE);
    printf("   targetdir: relative or absolute path to files to convert" NEWLINE);
    printf("   switch -s: toggle processing of subdirectories (default is on)" NEWLINE);
    printf("   switch -e: exclude HTTP header from file (header is created at runtime, default is off)" NEWLINE);
    printf("   switch -11: include HTTP 1.1 header (1.0 is default)" NEWLINE);
    printf("   switch -c: precalculate checksums for all pages (default is off)" NEWLINE);
    printf("   switch -f: target filename (default is \"fsdata.c\")" NEWLINE);
    printf("   if targetdir not specified, htmlgen will attempt to" NEWLINE);
    printf("   process files in subdirectory 'fs'" NEWLINE);
    exit(-1);
  }

  printf("HTTP %sheader will %s statically included." NEWLINE,
    (includeHttpHeader ? (useHttp11 ? "1.1 " : "1.0 ") : ""),
    (includeHttpHeader ? "be" : "not be"));

  sprintf(curSubdir, "");  /* start off in web page's root directory - relative paths */
  printf("  Processing all files in directory %s", path);
  if (processSubs) {
    printf(" and subdirectories..." NEWLINE NEWLINE);
  } else {
    printf("..." NEWLINE NEWLINE);
  }

  GETCWD(appPath, MAX_PATH_LEN);
  data_file = fopen("fsdata.tmp", "wb");
  if (data_file == NULL) {
    printf("Failed to create file \"fsdata.tmp\"\n");
    exit(-1);
  }
  struct_file = fopen("fshdr.tmp", "wb");
  if (struct_file == NULL) {
    printf("Failed to create file \"fshdr.tmp\"\n");
    exit(-1);
  }

  CHDIR(path);

  fprintf(data_file, "#include \"fs.h\"" NEWLINE);
  fprintf(data_file, "#include \"lwip/def.h\"" NEWLINE);
  fprintf(data_file, "#include \"fsdata.h\"" NEWLINE NEWLINE NEWLINE);

  fprintf(data_file, "#define file_NULL (struct fsdata_file *) NULL" NEWLINE NEWLINE NEWLINE);

  sprintf(lastFileVar, "NULL");

  filesProcessed = process_sub(data_file, struct_file);

  /* data_file now contains all of the raw data.. now append linked list of
   * file header structs to allow embedded app to search for a file name */
  fprintf(data_file, NEWLINE NEWLINE);
  fprintf(struct_file, "#define FS_ROOT file_%s" NEWLINE, lastFileVar);
  fprintf(struct_file, "#define FS_NUMFILES %d" NEWLINE NEWLINE, filesProcessed);

  fclose(data_file);
  fclose(struct_file);

  CHDIR(appPath);
  /* append struct_file to data_file */
  printf(NEWLINE "Creating target file..." NEWLINE NEWLINE);
  concat_files("fsdata.tmp", "fshdr.tmp", targetfile);

  /* if succeeded, delete the temporary files */
  remove("fsdata.tmp");
  remove("fshdr.tmp"); 

  printf(NEWLINE "Processed %d files - done." NEWLINE NEWLINE, filesProcessed);

  return 0;
}

static void copy_file(const char *filename_in, FILE *fout)
{
  FILE *fin;
  size_t len;
  fin = fopen(filename_in, "rb");
  if (fin == NULL) {
    printf("Failed to open file \"%s\"\n", filename_in);
    exit(-1);
  }

  while((len = fread(file_buffer_raw, 1, COPY_BUFSIZE, fin)) > 0)
  {
    fwrite(file_buffer_raw, 1, len, fout);
  }
  fclose(fin);
}

void concat_files(const char *file1, const char *file2, const char *targetfile)
{
  FILE *fout;
  fout = fopen(targetfile, "wb");
  if (fout == NULL) {
    printf("Failed to open file \"%s\"\n", targetfile);
    exit(-1);
  }
  copy_file(file1, fout);
  copy_file(file2, fout);
  fclose(fout);
}

int process_sub(FILE *data_file, FILE *struct_file)
{
  FIND_T fInfo;
  FIND_RET_T fret;
  int filesProcessed = 0;
  char oldSubdir[MAX_PATH_LEN];

  if (processSubs) {
    /* process subs recursively */
    strcpy(oldSubdir, curSubdir);
    fret = FINDFIRST_DIR("*", &fInfo);
    if (FINDFIRST_SUCCEEDED(fret)) {
      do {
        const char *curName = FIND_T_FILENAME(fInfo);
        if (curName == NULL) continue;
        if (curName[0] == '.') continue;
        if (strcmp(curName, "CVS") == 0) continue;
        if (!FIND_T_IS_DIR(fInfo)) continue;
        CHDIR(curName);
        strcat(curSubdir, "/");
        strcat(curSubdir, curName);
        printf(NEWLINE "processing subdirectory %s/..." NEWLINE, curSubdir);
        filesProcessed += process_sub(data_file, struct_file);
        CHDIR("..");
        strcpy(curSubdir, oldSubdir);
      } while (FINDNEXT_SUCCEEDED(FINDNEXT(fret, &fInfo)));
    }
  }

  fret = FINDFIRST_FILE("*.*", &fInfo);
  if (FINDFIRST_SUCCEEDED(fret)) {
    /* at least one file in directory */
    do {
      if (FIND_T_IS_FILE(fInfo)) {
        const char *curName = FIND_T_FILENAME(fInfo);
        printf("processing %s/%s..." NEWLINE, curSubdir, curName);
        if (process_file(data_file, struct_file, curName) < 0) {
          printf(NEWLINE "Error... aborting" NEWLINE);
          return -1;
        }
        filesProcessed++;
      }
    } while (FINDNEXT_SUCCEEDED(FINDNEXT(fret, &fInfo)));
  }
  return filesProcessed;
}

int get_file_size(const char* filename)
{
  FILE *inFile;
  int file_size = -1;
  inFile = fopen(filename, "rb");
  if (inFile == NULL) {
    printf("Failed to open file \"%s\"\n", filename);
    exit(-1);
  }
  fseek(inFile, 0, SEEK_END);
  file_size = ftell(inFile);
  fclose(inFile);
  return file_size;
}

void process_file_data(const char *filename, FILE *data_file)
{
  FILE *source_file;
  size_t len, written, i, src_off=0;

  source_file = fopen(filename, "rb");

  do {
    size_t off = 0;
    len = fread(file_buffer_raw, 1, COPY_BUFSIZE, source_file);
    if (len > 0) {
      for (i = 0; i < len; i++) {
        sprintf(&file_buffer_c[off], "0x%02.2x,", file_buffer_raw[i]);
        off += 5;
        if ((++src_off % HEX_BYTES_PER_LINE) == 0) {
          memcpy(&file_buffer_c[off], NEWLINE, NEWLINE_LEN);
          off += NEWLINE_LEN;
        }
      }
      written = fwrite(file_buffer_c, 1, off, data_file);
    }
  } while(len > 0);
  fclose(source_file);
}

int write_checksums(FILE *struct_file, const char *filename, const char *varname,
                    u16_t hdr_len, u16_t hdr_chksum)
{
  int chunk_size = TCP_MSS;
  int offset;
  size_t len;
  int i = 0;
  FILE *f;
#if LWIP_TCP_TIMESTAMPS
  /* when timestamps are used, usable space is 12 bytes less per segment */
  chunk_size -= 12;
#endif

  fprintf(struct_file, "#if HTTPD_PRECALCULATED_CHECKSUM" NEWLINE);
  fprintf(struct_file, "const struct fsdata_chksum chksums_%s[] = {" NEWLINE, varname);

  memset(file_buffer_raw, 0xab, sizeof(file_buffer_raw));
  f = fopen(filename, "rb");
  if (f == INVALID_HANDLE_VALUE) {
    printf("Failed to open file \"%s\"\n", filename);
    exit(-1);
  }
  if (hdr_len > 0) {
    /* add checksum for HTTP header */
    fprintf(struct_file, "{%d, 0x%04x, %d}," NEWLINE, 0, hdr_chksum, hdr_len);
    i++;
  }
  for (offset = hdr_len; ; offset += len) {
    unsigned short chksum;
    len = fread(file_buffer_raw, 1, chunk_size, f);
    if (len == 0) {
      break;
    }
    chksum = ~inet_chksum(file_buffer_raw, (u16_t)len);
    /* add checksum for data */
    fprintf(struct_file, "{%d, 0x%04x, %d}," NEWLINE, offset, chksum, len);
    i++;
  }
  fclose(f);
  fprintf(struct_file, "};" NEWLINE);
  fprintf(struct_file, "#endif /* HTTPD_PRECALCULATED_CHECKSUM */" NEWLINE);
  return i;
}

int process_file(FILE *data_file, FILE *struct_file, const char *filename)
{
  char *pch;
  char varname[MAX_PATH_LEN];
  int i = 0;
  char qualifiedName[MAX_PATH_LEN];
  int file_size;
  u16_t http_hdr_chksum = 0;
  u16_t http_hdr_len = 0;
  int chksum_count = 0;

  /* create qualified name (TODO: prepend slash or not?) */
  sprintf(qualifiedName,"%s/%s", curSubdir, filename);
  /* create C variable name */
  strcpy(varname, qualifiedName);
  /* convert slashes & dots to underscores */
  while ((pch = strpbrk(varname, "./\\")) != NULL) {
    *pch = '_';
  }
#if ALIGN_PAYLOAD
  /* to force even alignment of array */
  fprintf(data_file, "static const " PAYLOAD_ALIGN_TYPE " dummy_align_%s = %d;" NEWLINE, varname, payload_alingment_dummy_counter++);
#endif /* ALIGN_PAYLOAD */
  fprintf(data_file, "static const unsigned char data_%s[] = {" NEWLINE, varname);
  /* encode source file name (used by file system, not returned to browser) */
  fprintf(data_file, "/* %s (%d chars) */" NEWLINE, qualifiedName, strlen(qualifiedName)+1);
  file_put_ascii(data_file, qualifiedName, strlen(qualifiedName)+1, &i);
#if ALIGN_PAYLOAD
  /* pad to even number of bytes to assure payload is on aligned boundary */
  while(i % PAYLOAD_ALIGNMENT != 0) {
    fprintf(data_file, "0x%02.2x,", 0);
    i++;
  }
#endif /* ALIGN_PAYLOAD */
  fprintf(data_file, NEWLINE);

  file_size = get_file_size(filename);
  if (includeHttpHeader) {
    file_write_http_header(data_file, filename, file_size, &http_hdr_len, &http_hdr_chksum);
  }
  if (precalcChksum) {
    chksum_count = write_checksums(struct_file, filename, varname, http_hdr_len, http_hdr_chksum);
  }

  /* build declaration of struct fsdata_file in temp file */
  fprintf(struct_file, "const struct fsdata_file file_%s[] = { {" NEWLINE, varname);
  fprintf(struct_file, "file_%s," NEWLINE, lastFileVar);
  fprintf(struct_file, "data_%s," NEWLINE, varname);
  fprintf(struct_file, "data_%s + %d," NEWLINE, varname, i);
  fprintf(struct_file, "sizeof(data_%s) - %d," NEWLINE, varname, i);
  fprintf(struct_file, "%d," NEWLINE, includeHttpHeader);
  if (precalcChksum) {
    fprintf(struct_file, "#if HTTPD_PRECALCULATED_CHECKSUM" NEWLINE);
    fprintf(struct_file, "%d, chksums_%s," NEWLINE, chksum_count, varname);
    fprintf(struct_file, "#endif /* HTTPD_PRECALCULATED_CHECKSUM */" NEWLINE);
  }
  fprintf(struct_file, "}};" NEWLINE NEWLINE);
  strcpy(lastFileVar, varname);

  /* write actual file contents */
  i = 0;
  fprintf(data_file, NEWLINE "/* raw file data (%d bytes) */" NEWLINE, file_size);
  process_file_data(filename, data_file);
  fprintf(data_file, "};" NEWLINE NEWLINE);

  return 0;
}

int file_write_http_header(FILE *data_file, const char *filename, int file_size,
                           u16_t *http_hdr_len, u16_t *http_hdr_chksum)
{
  int i = 0;
  int response_type = HTTP_HDR_OK;
  int file_type = HTTP_HDR_DEFAULT_TYPE;
  const char *cur_string;
  size_t cur_len;
  int written = 0;
  size_t hdr_len = 0;
  u16_t acc;
  const char *file_ext;
  int j;

  memset(hdr_buf, 0, sizeof(hdr_buf));
  
  if (useHttp11) {
    response_type = HTTP_HDR_OK_11;
  }

  fprintf(data_file, NEWLINE "/* HTTP header */");
  if (strstr(filename, "404") == filename) {
    response_type = HTTP_HDR_NOT_FOUND;
    if (useHttp11) {
      response_type = HTTP_HDR_NOT_FOUND_11;
    }
  } else if (strstr(filename, "400") == filename) {
    response_type = HTTP_HDR_BAD_REQUEST;
    if (useHttp11) {
      response_type = HTTP_HDR_BAD_REQUEST_11;
    }
  } else if (strstr(filename, "501") == filename) {
    response_type = HTTP_HDR_NOT_IMPL;
    if (useHttp11) {
      response_type = HTTP_HDR_NOT_IMPL_11;
    }
  }
  cur_string = g_psHTTPHeaderStrings[response_type];
  cur_len = strlen(cur_string);
  fprintf(data_file, NEWLINE "/* \"%s\" (%d bytes) */" NEWLINE, cur_string, cur_len);
  written += file_put_ascii(data_file, cur_string, cur_len, &i);
  i = 0;
  if (precalcChksum) {
    memcpy(&hdr_buf[hdr_len], cur_string, cur_len);
    hdr_len += cur_len;
  }

  cur_string = serverID;
  cur_len = strlen(cur_string);
  fprintf(data_file, NEWLINE "/* \"%s\" (%d bytes) */" NEWLINE, cur_string, cur_len);
  written += file_put_ascii(data_file, cur_string, cur_len, &i);
  i = 0;
  if (precalcChksum) {
    memcpy(&hdr_buf[hdr_len], cur_string, cur_len);
    hdr_len += cur_len;
  }

  file_ext = filename;
  while(strstr(file_ext, ".") != NULL) {
    file_ext = strstr(file_ext, ".");
    file_ext++;
  }
  if((file_ext == NULL) || (*file_ext == 0)) {
    printf("failed to get extension for file \"%s\", using default.\n", filename);
  } else {
    for(j = 0; j < NUM_HTTP_HEADERS; j++) {
      if(!strcmp(file_ext, g_psHTTPHeaders[j].extension)) {
        file_type = g_psHTTPHeaders[j].headerIndex;
        break;
      }
    }
    if (j >= NUM_HTTP_HEADERS) {
      printf("failed to get file type for extension \"%s\", using default.\n", file_ext);
      file_type = HTTP_HDR_DEFAULT_TYPE;
    }
  }

  if (useHttp11) {
    char intbuf[MAX_PATH_LEN];
    memset(intbuf, 0, sizeof(intbuf));

    cur_string = g_psHTTPHeaderStrings[HTTP_HDR_CONTENT_LENGTH];
    cur_len = strlen(cur_string);
    fprintf(data_file, NEWLINE "/* \"%s%d\r\n\" (%d+ bytes) */" NEWLINE, cur_string, file_size, cur_len+2);
    written += file_put_ascii(data_file, cur_string, cur_len, &i);
    if (precalcChksum) {
      memcpy(&hdr_buf[hdr_len], cur_string, cur_len);
      hdr_len += cur_len;
    }

    _itoa(file_size, intbuf, 10);
    strcat(intbuf, "\r\n");
    cur_len = strlen(intbuf);
    written += file_put_ascii(data_file, intbuf, cur_len, &i);
    i = 0;
    if (precalcChksum) {
      memcpy(&hdr_buf[hdr_len], intbuf, cur_len);
      hdr_len += cur_len;
    }

    cur_string = g_psHTTPHeaderStrings[HTTP_HDR_CONN_CLOSE];
    cur_len = strlen(cur_string);
    fprintf(data_file, NEWLINE "/* \"%s\" (%d bytes) */" NEWLINE, cur_string, cur_len);
    written += file_put_ascii(data_file, cur_string, cur_len, &i);
    i = 0;
    if (precalcChksum) {
      memcpy(&hdr_buf[hdr_len], cur_string, cur_len);
      hdr_len += cur_len;
    }
  }

  cur_string = g_psHTTPHeaderStrings[file_type];
  cur_len = strlen(cur_string);
  fprintf(data_file, NEWLINE "/* \"%s\" (%d bytes) */" NEWLINE, cur_string, cur_len);
  written += file_put_ascii(data_file, cur_string, cur_len, &i);
  i = 0;
  if (precalcChksum) {
    memcpy(&hdr_buf[hdr_len], cur_string, cur_len);
    hdr_len += cur_len;

    LWIP_ASSERT("hdr_len <= 0xffff", hdr_len <= 0xffff);
    LWIP_ASSERT("strlen(hdr_buf) == hdr_len", strlen(hdr_buf) == hdr_len);
    acc = ~inet_chksum(hdr_buf, (u16_t)hdr_len);
    *http_hdr_len = (u16_t)hdr_len;
    *http_hdr_chksum = acc;
  }

  return written;
}

int file_put_ascii(FILE *file, const char* ascii_string, int len, int *i)
{
  int x;
  for(x = 0; x < len; x++) {
    unsigned char cur = ascii_string[x];
    fprintf(file, "0x%02.2x,", cur);
    if ((++(*i) % HEX_BYTES_PER_LINE) == 0) {
      fprintf(file, NEWLINE);
    }
  }
  return len;
}

int s_put_ascii(char *buf, const char *ascii_string, int len, int *i)
{
  int x;
  int idx = 0;
  for(x = 0; x < len; x++) {
    unsigned char cur = ascii_string[x];
    sprintf(&buf[idx], "0x%02.2x,", cur);
    idx += 5;
    if ((++(*i) % HEX_BYTES_PER_LINE) == 0) {
      sprintf(&buf[idx], NEWLINE);
      idx += NEWLINE_LEN;
    }
  }
  return len;
}
