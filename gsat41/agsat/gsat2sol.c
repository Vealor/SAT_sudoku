/*********************************************************/
/*  Conversion of GSAT assign files to AMPL .sol format  */
/*  For information about this program, contact          */
/*      kautz@research.att.com                           */
/*********************************************************/

#include "proto.h"
#include <malloc.h>
#include <stdio.h>
#include <signal.h>
#include <string.h>
#include <math.h>

/****************/
/*  Global data */
/****************/

#define MAX_LINE 10000

static char line[MAX_LINE];

/*****************/
/*  Input/Output */
/*****************/

static char * read_line_buf;
static int read_line_max;

void
init_read_line(PROTO(char *) buf, PROTO(int) max)
PARAMS( char * buf; int max; )
{
    read_line_buf = buf;
    read_line_max = max;
    buf[max-2] = '\n';
}

void
read_line()
{
    if (fgets(read_line_buf, read_line_max, stdin)==NULL){
	fprintf(stderr, "Unexpected end of input\n");
	exit(-1);
    }
    if (read_line_buf[read_line_max-2]!='\n'){
	fprintf(stderr, "Line too long\n");
	exit(-1);
    }
}

void
fread_line(PROTO(FILE *) fp)
PARAMS(FILE * fp;)
{
    if (fgets(read_line_buf, read_line_max, fp)==NULL){
	    fprintf(stderr, "Unexpected end of input\n");
	    exit(-1);
	}
    if (read_line_buf[read_line_max-2]!='\n'){
	fprintf(stderr, "Line too long\n");
	exit(-1);
    }
}

void
must_be(PROTO(int) a, PROTO(int) b)
PARAMS( int a; int b; )
{
    if (a!=b){
	fprintf(stderr, "Bad input\n");
	exit(-1);
    }
}


/****************/
/*  Conversion  */
/****************/

int
main( PROTO(int) argc, PROTO(char * *) argv )
PARAMS( int argc; char * * argv; )
{
    int numvars, numconstraints, i;
    int value, num_bad;
    FILE * nl;
    char * s;
    char * se;
    long ampl_options[10];

    init_read_line(line, MAX_LINE);

    /* Get info from .nl file */
    if (argc!=2){
	fprintf(stderr, "Bad argument\n");
	exit(-1);
    }
    if ((nl = fopen(argv[1], "r")) == NULL){
	fprintf(stderr, "Cannot open .nl file\n");
	exit(-1);
    }
    fread_line(nl);
    s = line;
    if (ampl_options[0] = strtol(++s, &se, 10)) {
	for(i = 1; i <= ampl_options[0] && se > s; i++)
	  ampl_options[i] = strtol(s = se, &se, 10);
    }
    fread_line(nl);
    must_be(2, sscanf(line, "%d %d", &numvars, &numconstraints));

    /* Get info from assign file */
    do {
	read_line();
	if (line[0]!='\n') printf("%s", line);
    } while (strncmp("(setq *gsat-best-num-bad*", line, 20)!=0);
    must_be(1, sscanf(line, "(setq *gsat-best-num-bad* %d", &num_bad));
    if (num_bad>0)
      printf(";;; Sorry, failed to find assignment!\n");
    else
      printf(";;; Satisying assignment found!\n");
    printf("\n");

    printf("Options\n");
    for (i=0; i<=ampl_options[0]; i++)
	printf("%ld\n", ampl_options[i]);
    printf("%ld\n%ld\n%ld\n%ld\n", numconstraints, 0, numvars, numvars);
    do
      read_line();
    while (strncmp("(setq *current-propositional-model*", line, 32)!=0);    
    for (i=1; i<= numvars; i++){
	must_be(1, scanf("%d", &value));
	printf("%d\n", value);
    }
    return 0;
}
