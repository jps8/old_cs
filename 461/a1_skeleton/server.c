#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <netinet/in.h>
#include <netdb.h>
#include <sys/socket.h>



#define MAXBUF 4096
/* #define BACKLOG 128*/
#define BACKLOG 0

/* Create, bind, and listen on a stream socket on port pcPort and return socket */
int createSocket(char *pcPort) {
  struct addrinfo aHints, *paRes;
  int iSockfd;

  /* Get address information for stream socket on input port */
  memset(&aHints, 0, sizeof(aHints));
  aHints.ai_family = AF_UNSPEC;
  aHints.ai_socktype = SOCK_STREAM;
  aHints.ai_flags = AI_PASSIVE;
  getaddrinfo(NULL, pcPort, &aHints, &paRes);

  /* Create, bind, listen */
  if ((iSockfd = socket(paRes->ai_family, paRes->ai_socktype, paRes->ai_protocol)) < 0) {
    perror("CREATE error");
    exit(EXIT_FAILURE);
  }
  if (bind(iSockfd, paRes->ai_addr, paRes->ai_addrlen) < 0) {
    perror("BIND error");
    exit(EXIT_FAILURE);
  }
  if (listen(iSockfd, BACKLOG) < 0) {
    perror("LISTEN error");
    exit(EXIT_FAILURE);
  }

  /* Free paRes, which was dynamically allocated by getaddrinfo */
  freeaddrinfo(paRes);

  return iSockfd;
}

/* Call: server <port-number> */
int main(int argc, char** argv) {
  int iSockfd, iClientfd, iRecv; 
  socklen_t iLen;
  char pcBuf[MAXBUF];
  struct sockaddr aClient;

  /* Single argument of argv[1] is the port number */
  if (argc != 2) {
    fprintf(stderr, "Usage: %s <port-number>\n", argv[0]);
    exit(EXIT_FAILURE);
  }
  
  /* Prepare to process requests */
  iSockfd = createSocket(argv[1]);
  iLen = sizeof(struct sockaddr);

  /* Handle clients, one at a time */
  while (1) {
    /* Accept the client, skipping on failure */
    if ((iClientfd = accept(iSockfd, &aClient, &iLen)) <=  0) {
      perror(argv[0]);
      close(iClientfd);
      continue;
    }

    /* Print and move along */
    while ((iRecv = recv(iClientfd, pcBuf, MAXBUF, 0)) > 0) {}

    close(iClientfd);
  }

  /* Clean up */
  close(iSockfd);
  
  return 0;
}
