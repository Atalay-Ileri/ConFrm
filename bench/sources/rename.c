#include <stdio.h>
#include <errno.h>
#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <stdint.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/time.h>

#define N 1000
#define FILESIZE 100
#define NAMESIZE 100

static char newname[NAMESIZE];
static char oldname[NAMESIZE];
static char buf[FILESIZE]; 
static char *dir;

void printstats(int reset)
{
  int fd;
  int r;
  
if (reset == 1) {
  	sprintf(oldname, "%s/clear-stats", dir);
	open(oldname, O_RDONLY);
  } 
  
  sprintf(oldname, "%s/stats", dir);
  if((fd = open(oldname, O_RDONLY)) < 0) {
    return;
  }

  bzero(buf, FILESIZE);

  if ((r = read(fd, buf, FILESIZE)) < 0) {
    perror("read");
    exit(1);
  }

  if (!reset)
    fprintf(stdout, "=== FS Stats ===\n%s========\n", buf);

  if ((r = close(fd)) < 0) {
    perror("close");
  }
}

static uint64_t
usec_now()
{
  struct timeval tv;

  gettimeofday(&tv, NULL);

  uint64_t res = tv.tv_sec;
  res *= 1000000;
  res += tv.tv_usec;
  return res;
}

int main(int argc, char *argv[])
{
  int i;
  int r;
  int fd;
  uint64_t start, end;

  if (argc != 2) {
    printf("Usage: %s basedir\n", argv[0]);
    exit(-1);
  }
  
  dir = argv[1];
  sprintf(buf, "%s/d", argv[1]);
  if (mkdir(buf,  S_IRWXU) < 0) {
    printf("%s: mkdir %s failed %s\n", argv[0], buf, strerror(errno));
    exit(1);
  }
  printstats(1);
  start = usec_now();
  sprintf(oldname, "%s/d/f%d", argv[1], 0);
  sprintf(newname, "%s/d/f%d", argv[1], 1);
  if((fd = open(oldname, O_RDWR | O_CREAT | O_TRUNC, S_IRWXU)) < 0) {
    printf("%s: create %s failed %s\n", argv[0], oldname, strerror(errno));
    exit(1);
  }
  close(fd);  
  for (i = 1; ; i++) {
    if((fd = open(newname, O_RDWR | O_CREAT | O_TRUNC, S_IRWXU)) < 0) {
      printf("%s: create %s failed %s\n", argv[0], newname, strerror(errno));
      exit(1);
    }
    close(fd);  
    rename(newname, oldname);
    end = usec_now();
    if (end - start > 1000000)
      break;
  }

  printf("DATA: %d %ld\n", i, end-start);

  printstats(0);
  
}
