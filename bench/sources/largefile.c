#include <stdio.h>
#include <errno.h>
#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/time.h>

/* Measure creating a large file and overwriting that file */

#define WSIZE (4096)
#define FILESIZE 500 * 4096
#define NAMESIZE 100

static char name[NAMESIZE];
static char buf[WSIZE];
static char *prog;
static char *dir;

void printstats(int reset)
{
  int fd;
  int r;

  sprintf(name, "%s/stats", dir);
  if((fd = open(name, O_RDONLY)) < 0) {
    return;
  }

  bzero(buf, WSIZE);

  if ((r = read(fd, buf, WSIZE)) < 0) {
    perror("read");
    exit(1);
  }

  if (!reset) fprintf(stdout, "=== FS Stats ===\n%s========\n", buf);

  if ((r = close(fd)) < 0) {
    perror("close");
  }
}

int makefile()
{
  int i;
  int r;
  int fd;

  int n = FILESIZE/WSIZE;
  
  sprintf(name, "%s", dir);
  /*
  if((fd = open(name, O_RDWR, S_IRWXU)) < 0) {
    printf("%s: create %s failed %s\n", prog, name, strerror(errno));
    exit(1);
  }
  */
  sprintf(buf, "%s/stats", dir);
    
  for (i = 0; i < n; i++) {
    if (write(1, buf, WSIZE) != WSIZE) {
      printf("%s: write %s failed %s\n", prog, name, strerror(errno));
      exit(1);
    }
  }
}


int main(int argc, char *argv[])
{
  long time;
  struct timeval before;
  struct timeval after;
  float tput;

  if (argc != 2) {
    printf("Usage: %s basedir\n", argv[0]);
    exit(-1);
  }
  
  prog = argv[0];
  dir = argv[1];

    
  gettimeofday ( &before, NULL );  
  makefile();
  gettimeofday ( &after, NULL );

  time = (after.tv_sec - before.tv_sec) * 1000000 +
	(after.tv_usec - before.tv_usec);
  tput = ((float) (FILESIZE/1024) /  (time / 1000000.0));
  printf("makefile %d MB %ld usec throughput %5.1f KB/s\n", FILESIZE/(1024*1024), time, tput);
}
