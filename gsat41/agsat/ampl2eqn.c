/*********************************************************/
/*  Conversion of AMPL .nl files to Equations            */
/*  For information about this program, contact          */
/*      kautz@research.att.com                           */
/*********************************************************/

#include "proto.h"
#include <malloc.h>
#include <stdio.h>
#include <signal.h>
#include <string.h>
#include <math.h>

#define LOWER_UPPER 0
#define MAX_LINE 10000

typedef int relation;
typedef int literal;

typedef struct {
    relation reln;
    int left;
    int right; } range;

/****************/
/*  Global data */
/****************/

static range * rhs;
static char line[MAX_LINE];
static char ignore[MAX_LINE];

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
must_be(PROTO(int) a, PROTO(int) b)
PARAMS( int a; int b;)
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
    int numconstr, i, j, numterms, coeff;
    literal lit;

    init_read_line(line, MAX_LINE);
    read_line();
    if (line[0]!='g'){
	fprintf(stderr, "Intermediate file not ascii (type g)\n");
	exit(-1);
    }

    read_line();
    must_be(2, sscanf(line, "%s %d", ignore, &numconstr));
    rhs = (range *) malloc( (numconstr + 1)*(sizeof(range)) );

    do {
	read_line();
	if (line[0]=='C') { 
	    read_line();
	    if (!(line[0]=='n' && line[1]=='0')){
		fprintf(stderr, "Cannot parse non-linear equations\n");
		exit(-1);
	    }
	}
    } while (line[0]!='r');
    for (i=1; i<=numconstr; i++){
	read_line();
	must_be(2, sscanf(line, "%d %d", &rhs[i].reln, &rhs[i].left));
	if (rhs[i].reln == LOWER_UPPER)
	  must_be(3, sscanf(line, "%s %s %d", ignore, ignore, &rhs[i].right));
    }

    for (i=1; i<=numconstr; i++){
	do
	  read_line();
	while (line[0]!='J');
	must_be(2, sscanf(line, "%s %d", ignore, &numterms));
	printf("%d", numterms);
	for (j=1; j<=numterms; j++){
	    read_line();
	    must_be(2, sscanf(line, "%d %d", &lit, &coeff));
	    printf(" %d %d", lit, coeff);
	}
	printf(" %d %d", rhs[i].reln, rhs[i].left);
	if (rhs[i].reln == LOWER_UPPER)
	  printf(" %d", rhs[i].right);
	printf("\n");
    }
    
    return 0;
}
