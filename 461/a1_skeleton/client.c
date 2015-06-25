#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <netdb.h>

#include <fcntl.h>

#define MAXBUF 4096

int createSocket(char *pcAddress, char *pcPort) {
  struct addrinfo aHints, *paRes;
  int iSockfd;

  /* Get address information for stream socket on input port */
  memset(&aHints, 0, sizeof(aHints));
  aHints.ai_family = AF_UNSPEC;
  aHints.ai_socktype = SOCK_STREAM;
  if (getaddrinfo(pcAddress, pcPort, &aHints, &paRes) != 0) {
    perror("GETADDR error");
    exit(EXIT_FAILURE);
  }

  /* Create and connect */
  if ((iSockfd = socket(paRes->ai_family, paRes->ai_socktype, paRes->ai_protocol)) < 0) {
    perror("CREATE error");
    exit(EXIT_FAILURE);
  }
  if (connect(iSockfd, paRes->ai_addr, paRes->ai_addrlen) < 0) {
    perror("CONNECT error");
    exit(EXIT_FAILURE);
  }

  /* Free paRes, which was dynamically allocated by getaddrinfo */
  freeaddrinfo(paRes);

  return iSockfd;
}

/* client <server-address> <server-port> < <text-message> */
int main(int argc, char *argv[]) {
  int iSockfd, iRead, iWrite, iSend;
  char pcBuf[MAXBUF];

  /* Two arguments for server address and port */
  if (argc != 3) {
    fprintf(stderr, "Usage: %s <server-address> <port-number>\n", argv[0]);
    exit(EXIT_FAILURE);
  }

  /* Create and connect socket */
  iSockfd = createSocket(argv[1], argv[2]);

  /* Read from stdin and write data into the socket */
  while ((iRead = read(0, pcBuf, MAXBUF)) > 0) {
    /* Keep writing till all of the data is successfully written */
    for (iWrite = 0; iWrite < iRead; iWrite+=iSend) {
      if ((iSend = write(iSockfd, pcBuf+iWrite, iRead-iWrite)) < 0) {
	perror("WRITE error");
	exit(EXIT_FAILURE);
      }
    }
  }

  /* Clean up */
  close(iSockfd);
  return 0;
}
