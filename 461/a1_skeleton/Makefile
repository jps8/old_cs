CC=gcc
CFLAGS= -g -Wall -Werror

all: proxy

proxy: proxy.c
	$(CC) $(CFLAGS) -o proxy_parse.o -c proxy_parse.c
	$(CC) $(CFLAGS) -o proxy.o -c proxy.c
	$(CC) $(CFLAGS) -o proxy proxy_parse.o proxy.o

server:
	$(CC) $(CFLAGS) -o server.o -c server.c
	$(CC) $(CFLAGS) -o server server.o

client:
	$(CC) $(CFLAGS) -o client.o -c client.c
	$(CC) $(CFLAGS) -o client client.o

clean:
	rm -f proxy *.o

tar:
	tar -cvzf ass1.tgz proxy.c README Makefile proxy_parse.c proxy_parse.h
