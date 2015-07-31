/*********************************************************/
/*  Conversion of 0-1 Integer Programs to Clauses        */
/*  For information about this program, contact          */
/*      kautz@research.att.com                           */
/*********************************************************/

#include "proto.h"
#include <malloc.h>
#include <stdio.h>
#include <signal.h>
#include <string.h>
#include <math.h>

#define MAX_TERMS 1000

typedef int literal;

typedef int relation;
#define LOWER_UPPER 0
#define LESS_EQUAL 1
#define GREATER_EQUAL 2
#define LESS 3
#define EQUAL 4
#define GREATER 5
#define HIGHEST_RELN 5

extern char * relation_names[];

typedef struct {
    relation reln;
    int c0;
    int c0upper;
    int sumcoeff;
    int numterms;
    struct {
	literal lit;
	int coeff; } body[ MAX_TERMS ]; } equation;

typedef struct {
    int len;
    literal lit[ MAX_TERMS]; } clause;


/****************/
/*  Global data */
/****************/

static equation eqn;
static int flag_pretty = 0;
static int flag_offset = 0;

char * relation_names[] = {
    "between", "<=", ">=", "<", "=", ">" };

/*****************/
/*  Input/Output */
/*****************/

void
write_clause( PROTO(clause *) clp)
PARAMS( clause * clp; )
{
    int i;
    for (i=1; i<= clp->len; i++)
      printf(" %i ", clp->lit[i]);
    printf("\n");
}

void
write_true()
{
    if (flag_pretty)
      printf("#  TRUE\n");
}

void
write_false()
{
    if (flag_pretty)
      printf("#  FALSE\n");
    printf("1\n-1\n");
    /* Eliminate the rest of the input */
    while (getchar()!=EOF);
}

int
read_int()
{
    int i;
    if (scanf("%i", &i) != 1){
	fprintf(stderr, "Bad input\n");
	exit(-1);
    }
    return i;
}


/* Input format for read_eqn:
   numterms x_1 c_1  ... x_n c_n  reln c0 [ c0upper ]
   Variables x_i are all ints >= 0
   Reln represented by integers of type relation
   Returns 1 if eqn read, 0 if eof
*/
int
read_eqn(PROTO(equation *) eqnp)
PARAMS( equation * eqnp; )
{
    literal lit;
    int len, coeff, cond, numterms, i;
    relation reln;

    cond = scanf("%i", &numterms);
    if (cond == EOF) return 0;
    if (cond != 1 || numterms <= 0){
	fprintf(stderr, "Bad input\n");
	exit(-1);
    }
    len = 0;
    for (i = 1; i<= numterms; i++){
	lit = (literal) read_int() + flag_offset;
	if (lit <= 0){
	    fprintf(stderr, "Bad input\n");
	    exit(-1);
	}
	coeff = read_int();
	if (coeff != 0){
	    if (++len >= MAX_TERMS){
		fprintf(stderr, "Too many terms\n");
		exit(-1);
	    }
	    eqnp->body[len].lit = lit;
	    eqnp->body[len].coeff = coeff;
	}
    }
    reln = (relation) read_int();
    if (reln < 0 || reln > HIGHEST_RELN){
	fprintf(stderr, "Bad relation %i\n", reln);
	exit(-1);
    }
    eqnp->reln = reln;
    eqnp->c0 = read_int();
    if (reln == LOWER_UPPER)
      eqnp->c0upper = read_int();
    eqnp->numterms = len;
    return 1;
}

void
write_eqn(PROTO(equation *) eqnp)
PARAMS( equation * eqnp; )
{
    int i;
    for (i = 1; i <= eqnp->numterms; i++){
	printf(" %i %i\n", eqnp->body[i].lit, eqnp->body[i].coeff);
    }
    printf("     %i   %i   %i\n", 0, eqnp->reln, eqnp->c0);
}

void
pretty_print_eqn(PROTO(equation *) eqnp)
PARAMS( equation * eqnp; )
{
    int i, coeff;

    printf("#  ");
    for (i = 1; i <= eqnp->numterms; i++){
	coeff = eqnp->body[i].coeff;
	if (i>1 && coeff>=0) printf("+ ");
	if (coeff<0) { 
	    printf("- ");
	    coeff *= -1;
	}
	if (coeff != 1) printf("%i ", coeff);
	printf("p_%i ", eqnp->body[i].lit);
    }
    if (eqnp->reln>=0 && eqnp->reln <=HIGHEST_RELN) {
	printf("%s %i", relation_names[eqnp->reln], eqnp->c0);
	if (eqnp->reln == LOWER_UPPER)
	  printf(" %i", eqnp->c0upper);
    }
    else
      printf("ILLEGAL_RELN=%i %i", eqnp->reln, eqnp->c0);
    printf("\n");
}


/***************************/
/*  Equation Manipulation  */
/***************************/

static equation * sort_terms_eqnp;
static equation sort_terms_aux;

void
sort_terms_mergesort( PROTO(int) lower, PROTO(int) upper)
PARAMS( int lower; int upper; )
{
    int i, j, k, m;
    if (upper > lower){
	m = (upper + lower)/2;
	sort_terms_mergesort(lower, m);
	sort_terms_mergesort(m + 1, upper);
	for (i = lower; i <= upper; i++)
	  sort_terms_aux.body[i] = sort_terms_eqnp->body[i];
	i = lower;
	j = m + 1;
	for (k = lower; k <= upper; k++)
	  sort_terms_eqnp->body[k] =
	    ( i > m )
	      ? sort_terms_aux.body[j++]
		: ( j > upper)
		  ? sort_terms_aux.body[i++]
		    : (sort_terms_aux.body[i].coeff >= sort_terms_aux.body[j].coeff) 
		      ? sort_terms_aux.body[i++] 
			: sort_terms_aux.body[j++];
    }
}

void
sort_terms( PROTO(equation *) eqnp)
PARAMS( equation * eqnp; )
     /* Sort the terms so that those with the largest coefficients
	appear first */
{
    sort_terms_eqnp = eqnp;
    sort_terms_mergesort( 1, eqnp->numterms );
}

static clause choose_cl;
static equation * choose_eqnp;
static void (* choose_clfun)( PROTO(clause *) );

int
choose_recurse( PROTO(int) head, PROTO(int) startat, PROTO(int) needed)
PARAMS( int head; int startat; int needed; )
{
    int newneeded, foundflag;

    if (needed <= 0) {
	choose_cl.len = head;
	(* choose_clfun)(&choose_cl);
	return 1;
    }
    if (startat > choose_eqnp->numterms){
	return 0;
    }
    head++;
    foundflag = 0;
    for ( ; startat <= choose_eqnp->numterms; startat++){
	choose_cl.lit[head] = choose_eqnp->body[startat].lit;
	newneeded = needed - choose_eqnp->body[startat].coeff;
	if (choose_recurse(head, startat + 1, newneeded))
	  foundflag = 1;
	else
	  break;
    }
    return foundflag;
}


void
#ifdef PROTOTYPES
choose( equation * eqnp, int amt, void (* clfun)(clause *))
#else
choose( eqnp, amt, clfun )
equation * eqnp;
int amt;
void (* clfun)();
#endif
     /* From eqn construct clauses by choosing literals whose
	coefficients sum to amt; apply clfun to each clause so
	constructed. */
{
    sort_terms(eqnp);
    choose_clfun = clfun;
    choose_eqnp = eqnp;
    choose_cl.len = 0;
    (void) choose_recurse( 0, 1, amt );
}

void
convert_ge_eqn( PROTO(equation *) eqnp)
PARAMS( equation * eqnp; )
{
    int i;

    /* Make all coefficients positive */
    for (i=1; i<=eqnp->numterms; i++){
	if (eqnp->body[i].coeff < 0){
	    eqnp->c0 -= eqnp->body[i].coeff;
	    eqnp->body[i].coeff *= -1;
	    eqnp->body[i].lit *= -1; /* -lit stands for (1-lit) */
	}
    }

    /* Compute the sum of the coefficients */
    eqnp->sumcoeff = 0;
    for (i = 1; i <= eqnp->numterms; i++)
      eqnp->sumcoeff += eqnp->body[i].coeff;

    /* Check for tautology or inconsistency */
    if (eqnp->c0 <= 0) {
	write_true();
    }
    else if (eqnp->c0 > eqnp->sumcoeff) {
	write_false();
    }
    else {
	choose( eqnp, eqnp->sumcoeff + 1 - eqnp->c0, write_clause );
    }
}

void
convert_eqn( PROTO(equation *) eqnp)
PARAMS( equation * eqnp; )
{
    equation eqn2;
    int i;

    switch (eqnp->reln) {
      case GREATER_EQUAL:
	convert_ge_eqn(eqnp);
	break;
      case GREATER:
	eqnp->c0++;
	eqnp->reln = GREATER_EQUAL;
	convert_ge_eqn(eqnp);
	break;
      case LESS_EQUAL:
	for (i=1; i<=eqnp->numterms; i++)
	  eqnp->body[i].coeff *= -1;
	eqnp->c0 *= -1;
	eqnp->reln = GREATER_EQUAL;
	convert_eqn(eqnp);
	break;
      case LESS:
	eqnp->c0--;
	eqnp->reln = LESS_EQUAL;
	convert_eqn(eqnp);
	break;
      case EQUAL:
	eqn2 = *eqnp;
	eqnp->reln = LESS_EQUAL;
	eqn2.reln = GREATER_EQUAL;
	convert_eqn(eqnp);
	convert_eqn(&eqn2);
	break;
      case LOWER_UPPER:
	eqn2 = *eqnp;
	eqnp->reln = GREATER_EQUAL;
	eqn2.c0 = eqn2.c0upper;
	eqn2.reln = LESS_EQUAL;
	convert_eqn(eqnp);
	convert_eqn(&eqn2);
	break;
      default:
	fprintf(stderr, "Bad relation %i\n", eqnp->reln);
	exit(-1);
    }
}


/**********/
/*  Main  */
/**********/

int
main( PROTO(int) argc, PROTO(char * *) argv )
PARAMS( int argc; char * * argv; )
{
    int i;

    for (i=1; i<argc; i++){
	if (strcmp(argv[i], "-pretty")==0)
	  flag_pretty = 1;
	else if (strcmp(argv[i], "-offset")==0)
	  flag_offset = 1;
	else {
	    fprintf(stderr, "Bad option %s\n", argv[i]);
	    exit(-1);
	}
    }
    
    while (read_eqn(&eqn)){
	if (flag_pretty)
	  pretty_print_eqn(&eqn);
	convert_eqn(&eqn);
    }
    printf("%%\n0\n");
    return 0;
}

