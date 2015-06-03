all:
	gcc -Wall -O3 -DNDEBUG -o zummarize zummarize.c
clean:
	rm -f zummarize
