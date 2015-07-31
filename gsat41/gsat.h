/**************************/
/*  gsat.h -- GSAT        */
/**************************/

/* DISCLAIMER                                                     */
/* AT&T disclaims all warranties with regard to this program,     */
/* including all implied warranties of merchantability and        */
/* fitness.  In no event shall AT&T be liable for any special,    */
/* indirect or consequential damages or any damages whatsoever    */
/* resulting from loss of use, data or profits, whether in an     */
/* action of contract, negligence or other tortious action,       */
/* arising out of or in connection with the use or performance of */
/* this program.                                                  */
/*                                                                */

#ifndef GSAT_H
#define GSAT_H

/***************************/
/* ANSI/K&R compatibility  */
/***************************/

#include "proto.h"

/**************************/
/*  Standard Includes     */
/**************************/

#if NeedFunctionPrototypes || defined(sun)
#include <stdlib.h>
#endif

#include <malloc.h>
#include <stdio.h>
#ifndef SEEK_END
#define SEEK_END 2
#endif
#include <signal.h>
#include <string.h>
#include <math.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <sys/utsname.h>
#include "urand.h"

EXTERN_FUNCTION( long random, (void) );
EXTERN_FUNCTION( int gethostname, (char *name, int namelen));
EXTERN_FUNCTION( FILE * tmpfile, (void) );


/***************/
/*  Macros     */
/***************/

/* Debugging macros */
#define DEBUG(x)		/* define as x to turn on debugging output */
#ifdef NOCHECK
#define CHECK(x)
#else
#define CHECK(x) x		/* define as x to turn on self-checking */
#endif
/* To not compile walk code, define NOWALK */
#define BOUNDS(low, index, hi) if (low > index || index > hi) { \
                                  printf("ERROR!  index out of bounds!\n"); \
                                  exit(-1); }
/* Math macros */
extern int scratch;		/* integer absolute value */
#define abs_val(x) ((scratch=(x))<0 ? (-(scratch)) : (scratch))
#define ifloor(x)  ((int)(x))	/* floor of a positive float or double, converted to int */
#define same_sign(x,y) ( (x)<=0 ? (y)<=0 : (y)>0 )
#define max_value(x,y)  ( (x) > (y) ? (x) : (y))

#define BIG 0x7fffffff  /* 2**31 - 1 */

/* Parameter macros */
#define LINE_LENGTH 10		/* number of elements to print on each line when printing arrays */
#define MAXLINE 128		/* max number char for fgets function */
#define MAX_DIAGNOSTICS 10	/* max num output lines per diagnositic print function */  
#define LENGTH_BAD_CLAUSE_COUNT 100 /* size of bad clause histogram array */
#define DEFAULT_ONE_BIT_MASK (0100000)	/* Bit used for random flips */
#define INT_PROB_BASE 10000000 
#define SAVE_BEST_MAX_DEFAULT 20
/* Used as the implicit base for parameters which are probabilities stored as integers.  */

#define PROGRAM_NAME "program: gsat version 41, July 1995\n"
#define PROGRAM_VERSION "41"


/****************************/
/*  Dynamic Data Structures */
/****************************/

typedef short int truth_val_type; /* may be defined as int, short int, or signed char */

typedef struct wff_str {
  int lit;			/* contains a lit OR the # of lits in following clause  */
  int next;			/* next clause containing the lit OR the weight of the clause */
				/*    lit:     #lits  lit1 lit2 lit3 ... */
				/*    next:    weight c1   c2   c3   ... */
				/* where c1 = index of start of next clause containing */
				/* lit1 or -lit1, etc. */
} *wff_str_ptr;

extern
wff_str_ptr wff;		/* wff contains the clauses in the format */
				/*    #lits, lit1, ..., litn */
				/* First clause begins at index wff[1]. */
				/* size = nlits + nclauses + 1 */

typedef struct index_list_str {
  int pos;
  int list; 
} indexed_list;

typedef struct var_str {
    int name;			/* same as the index of the variable */
    truth_val_type value;	/* -1 = false, 1 = true, -2 = not assigned */
    truth_val_type value_best;	/* value var got in best assignment */
    truth_val_type value_low;	/* value var got in best assignment during current try */
    truth_val_type prev_low;	/* used for averaging assignments */
    truth_val_type first_init_value; /* initial value assigned on try 1 */
    int diff;			/* current diff = make - critical */
    int make;			/* current make */
    int positive_count;		/* number of times variable is 1 at end of try */
    int flip_count;		/* number of times variable is flipped */
    int first;			/* index into wff of first clause containing var */
    /* Following hold lists, are NOT indexed by var! */
    int lastwalk;
    indexed_list walk;		/* list of vars with make values > 0 */
    indexed_list up;		/* list of vars with diff values < 0 */
    indexed_list down;		/* list of vars with diff values > 0 */
    indexed_list sideways;	/* list of vars with diff values = 0 */
    indexed_list maxdiff;	/* list of var with max diff */
    indexed_list tabu;		/* tabu list */
    indexed_list free;		/* list of unassigned vars */
} *var_str_ptr;        

extern
var_str_ptr assign;		/* assign is global array containing the assignment */
				/* variable n stored at assign[n] */
				/* size = nvars + 1 */
extern
int
  tabu_in,			/* indexes of first/last element in tabu list */
  tabu_out;

typedef struct bad_clause_count_str {
  int value;			/* number of times there were this many bad clauses */
} *bad_clause_count_str_ptr;        

extern
bad_clause_count_str_ptr bad_clause_count; /* array contains histogram of bad clause counts */
extern
bad_clause_count_str_ptr reset_bad_clause_count; 
				/* array contains histogram of bad clause counts */
				/* at the end of reset_tries number of tries or */
				/* after an assignment is actually found */

extern
int * clause_index_to_num;	/* array mapping clause indexes to clause numbers,
				   where indexes correspond to wff[] indexes */

extern
int * clause_num_to_index;	/* array mapping clause numbers to clause indexes,
				   where indexes correspond to wff[] indexes */

/****************************/
/*  Current State           */
/****************************/

extern
int nvars,			/* number of variables */
  nclauses,			/* number of clauses */
  nlits;			/* number of literals  */

extern
int
  current_max_diff,		/* Current greatest .diff value for any variable */
  current_num_bad;		/* Current number of unsatisfied clauses */

extern
int
  current_try,			/* Current try */
  flip,				/* Current flip */
  try_this_assign;		/* Number of tries in since program started */
				/* or since last assignment was found */

extern
int boost_on;			/* 1 = in boost mode */

extern
FILE * fp_xtent;		/* File pointer for xtent_pipe */

extern
uniform * rd;			/* Structure used by urand */

/**************************/
/*  Statistics            */
/**************************/

extern
int downwards_count,		/* counting max_diff > 0  -- total count for each try */
  sideways_count,		/* counting max_diff = 0  -- total count for each try */
  upwards_count,		/* counting max_diff < 0  -- total count for each try */
  null_count;			/* counting var == 0  -- total count for each try */

extern
int init_bad;			/* number bad clauses immediately after initialization */

extern
int low_bad;			/* lowest number bad found during CURRENT try */

extern
int				/* Best values found at the END of any try */
  best_num_bad, best_flip, best_try, best_max_diff, best_reset_count,
  best_downwards, best_sideways, best_upwards, best_null;

extern
int				/* Totals for entire experiment */
  total_num_assigns, total_sum_flips, total_sum_tries, 
  total_downwards, total_sideways, total_upwards,
  total_successful_flips_incl_resets, total_successful_reset_count,
  total_null,
  total_after_init_num_bad,	/* Sum of num bad right after initial assignment */
  total_sum_successful_flips;	/* Sum of flips, only counting tries that found an */
				/* assignment. */

extern
double experiment_seconds;	/* Number of seconds consumed after wff is read in */

/**************************/
/*  Parameters            */
/**************************/

extern
char program_name[];

extern
FILE * try_stat_filep;

extern
char wff_file[MAXLINE], assign_file[MAXLINE], report_file[MAXLINE], 
  init_file[MAXLINE],
  convert_file[MAXLINE], xtent_pipe[MAXLINE];

extern
char hostname[MAXLINE];
extern
struct utsname hostutsname;

extern
int max_flips,			/* max number of flips per try */
  max_tries,			/* max number of tries from random state */
  reset_tries,			/* number to tries to perform before a random restart*/
  reset_weight_tries,		/* number of tries before resetting weights to 1 */
                                /*    = 0 - never reset or change weights, not even at start */
                                /*    = 1 - reset at start of each multiple assign */
				/*    > 1 - reset at start of each multiple assign and every n tries */
                                /*    = -1 - reset at start of first assign only */
                                /*    < -1 - reset at start of first assign and every n tries */
  weight_update_amt,		/* amount to update clause weights by */
  flips_to_plateau;             /* number of flips until plateau is reached */

extern
int seed1,			/* Used to seed random number generator */
  seed2;			/* Rest of seed, used by urand */

extern
int flag_save_best_max;		/* Save best assigns at end of try OR when current_num_bad is less */
				/* than this number */
extern
  flag_walk,			/* 1 - 100 = when current_max_diff <= 0, then that
				   percentage of the time choose var to flip from 
				   pos_make_list, rather than max_diff_list. 
				   If negative, then do this even when max_diff > 0. */
  flag_walk_all_vars,		/* 1 = pick from all vars instead of pos_make_list */
  flag_only_unsat;		/* 1 = restrict max_diff_list (and up, down, sideways buckets) */
				/* to variables that appear in unsatisfied clauses. */

extern
  int flag_mail;		/* 1 = email error messages */

extern
int flag_partial;		/* initial assignment file is a partial assignment */

extern
int
  tabu_list_length;		/* Maximum (NOT current!) length of tabu list */

extern
int
  flag_hillclimb;		/* Perform hillclimbing using up, down, sideways buckets */

extern
int
  flag_manual_pick;			/* Debugging option */

extern
int
  flag_bigflip;

extern
int
  flag_superlinear;

#define FLAG_TRACE_FLIPS 1
#define FLAG_TRACE_FLIP_CLAUSES 2
#define FLAG_TRACE_DIFFS 4
#define FLAG_TRACE_MAKES 8
#define FLAG_TRACE_WALKS 16
#define FLAG_TRACE_ANNEAL 32
#define FLAG_TRACE_CLAUSES 64
#define FLAG_TRACE_TRIES 128	/* Also, tries traced if ANYTHING is traced */
#define FLAG_TRACE_BEST 256
#define FLAG_TRACE_TABU 512
#define FLAG_TRACE_ORPHANS 1024
#define FLAG_TRACE_ASSIGN 2048
#define FLAG_TRACE_CLAUSE_STATE 4096

#define FLAG_TRACE_NAMES_SIZE 13

#define FLAG_FORMAT_F 1
#define FLAG_FORMAT_KF 2
#define FLAG_FORMAT_CNF 3
#define FLAG_FORMAT_LISP 4

extern
char *flag_trace_names[];

extern
int 
  flag_adaptive,		/* >0 means compute initial states by "adaptive random starts" -- 
				   use values from previous lowest state, and make this number
				   of random flips.  When = 0 and reset_tries>1, then instead
				   generate initial states by averaging two previous lowest states. */
  flag_init_prop,		/* 1 = unit propagation */
  flag_multiple_assigns,	/* 1 = don't stop after finding assignment, */
				/* continue on for max_tries */
  flag_direction,		/* if 1 then only downwards moves */
				/* if 2 downwards and sideways only */
  flag_plateau,                 /* >0 means explore plateau with this many unsat clauses by choosing sideways moves only */
  flag_hole,                    /* 1 = stop after finding first downward move from plateau */
  flag_hole_continue,           /* 1 = continue searching plateau after finding hole */
  flag_convert,			/* 1 = convert wff format and exit */
  flag_fixed_init,		/* 1 = always use same random assignment */
  flag_format,		        /* Indicates format of input file */
  flag_abort,			/* 1 = gsat is terminated by a signal */
  flag_long_report,		/* 1 = print additional info in report file */
  flag_weigh_clauses,		/* 1 = use the clause weights in calculating the diffs */
  flag_coloring,		/* != 0 assume "implicit" k-coloring clauses */
  flag_trace,			/* Each bit specifies feature to trace */
  flag_anneal;			/* 1 = perform simulated annealing */

extern
int
  flag_graphics;		/* != call graphics routines after each flip */

#define FLAG_GRAPHICS_QUEENS 1
#define FLAG_GRAPHICS_XGSAT 2
/*#define XGSAT	1*/ 

extern
int boost_threshhold,		/* Boost if current_num_bad below this value */
  boost_amount;			/* Number of flips to boost */

extern
int report_interval;		/* Print report after this many tries */

extern
int rand_method;		/* Method used to generate random flips; default = 3 */

extern
int one_bit_mask;		/* Masks bit used by random functions in random_01 */

extern
int odds_true;		/* Odds that a variable will be initialized to true */

extern
unsigned pause_usecs;		/* Number of usecs to pause between each flip */

extern
long int raw_start_time;		/* current time of day */
extern
struct tm * raw_start_tmptr;
extern
char datestring[30];

/**************************/
/*  Misc                  */
/**************************/

extern
int scratch;			/* used by abs_val macro */

extern
char ss[10000];			/* scratch string */


/*********************************/
/*  List manipulation macros     */
/*********************************/

#define add_to(KEY, VARPTR) \
{ assign[VARPTR->KEY.pos = ++(assign->KEY.list)].KEY.list = (VARPTR ->name); }

#define delete_from(KEY, VARPTR) \
{  assign[(assign[(VARPTR->KEY.pos)].KEY.list = (assign[(assign->KEY.list)--].KEY.list))].KEY.pos = (VARPTR->KEY.pos); \
    VARPTR->KEY.pos = 0; }

#define length_of(KEY) \
  (assign->KEY.list)

#define is_in(KEY, VARPTR) \
  (VARPTR->KEY.pos)

#define delete_if_in(KEY, VARPTR) \
{ if (is_in(KEY, VARPTR)) delete_from(KEY, VARPTR); }
				      
#define print_list(KEY, VAL, PROMPT) \
{   int i; \
    fputs(PROMPT, stdout); \
    printf("(length %d) ", length_of(KEY)); \
    for (i=1; i<=length_of(KEY); i++) {\
      printf(" %d/%d ", assign[i].KEY.list, assign[assign[i].KEY.list].VAL); \
      if (assign[assign[i].KEY.list].KEY.pos != i){ \
         sprintf(ss, "List error - var %d pos = %d, not %d\n", \
            assign[i].KEY.list, assign[assign[i].KEY.list].KEY.pos, i); \
         crash_and_burn(ss); \
      } \
    } \
    printf("\n"); }

#define random_member(KEY) \
  (assign[random_1_to(length_of(KEY))].KEY.list)

#define empty_out(KEY) \
{ int i, len; var_str_ptr vp; \
  for (len = length_of(KEY), vp = &assign[1], i=1; i<=len; i++, vp++) \
    assign[ vp->KEY.list ].KEY.pos = 0; \
  assign->KEY.list = 0; }
	  
/*********************************/
/*  Functions Defined in gsat.c  */
/*********************************/

EXTERN_FUNCTION( int random_1_to, (int n));
EXTERN_FUNCTION( int random_01_odds, (int odds));
EXTERN_FUNCTION( int get_bad_clauses, (int print_flag, int update_flag));
EXTERN_FUNCTION( void print_report, (char * message));
EXTERN_FUNCTION( int pick_greedy_var, ());
EXTERN_FUNCTION( int lit_of_clause_num, (int lit_num, int clause_num));
EXTERN_FUNCTION( int length_of_clause_num, (int clause_num));

#endif

