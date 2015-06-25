#include "proxy_parse.h"


#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#define badexit(s) { \
        fprintf(stderr, (s)); \
        exit(EXIT_FAILURE); }


int main(int argc, char * argv[]) {

	if (argv[1] == NULL) {
		badexit("Main: missing port number \n");
	}

	
	printf("%s \n", argv[1]);

}
