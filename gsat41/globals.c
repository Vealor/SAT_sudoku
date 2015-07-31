/**************************/
/*  globals.c -- GSAT     */
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

#include "gsat.h"

/****************************/
/*  Dynamic Data Structures */
/****************************/

wff_str_ptr wff;		/* wff contains the clauses in the format */
				/*    #lits, lit1, ..., litn */
				/* First clause begins at index wff[1]. */
				/* size = nlits + nclauses + 1 */

var_str_ptr assign;		/* assign is global array containing the assignment */
				/* variable n stored at assign[n] */
				/* size = nvars + 1 */

int
  tabu_in,			/* indexes of first/last element in tabu list */
  tabu_out;

bad_clause_count_str_ptr bad_clause_count; /* array contains histogram of bad clause counts */
bad_clause_count_str_ptr reset_bad_clause_count; 
				/* array contains histogram of bad clause counts */
				/* at the end of reset_tries number of tries or */
				/* after an assignment is actually found */

int * clause_index_to_num;	/* array mapping clause indexes to clause numbers,
				   where indexes correspond to wff[] indexes */

int * clause_num_to_index = NULL;	/* array mapping clause numbers to clause indexes,
					   where indexes correspond to wff[] indexes */

/****************************/
/*  Current State           */
/****************************/

int nvars,			/* number of variables */
  nclauses,			/* number of clauses */
  nlits;			/* number of literals  */

int
  current_max_diff,		/* Current greatest .diff value for any variable */
  current_num_bad;		/* Current number of unsatisfied clauses */

int
  current_try,			/* Current try */
  flip,				/* Current flip */
  try_this_assign;		/* Number of tries in since program started */
				/* or since last assignment was found */

int boost_on;			/* 1 = in boost mode */

FILE * fp_xtent;		/* File pointer for xtent_pipe */

uniform * rd;			/* Structure used by urand */

/**************************/
/*  Statistics            */
/**************************/

int downwards_count,		/* counting max_diff > 0  -- total count for each try */
  sideways_count,		/* counting max_diff = 0  -- total count for each try */
  upwards_count,		/* counting max_diff < 0  -- total count for each try */
  null_count;			/* counting var == 0  -- total count for each try */

int				/* Best values found at the END of any try */
  best_num_bad, best_flip, best_try, best_max_diff, best_reset_count,
  best_downwards, best_sideways, best_upwards,  best_null;

int init_bad;			/* number bad clauses immediately after initialization */

int low_bad;			/* lowest number bad found during CURRENT try */

int				/* Totals for entire experiment */
  total_num_assigns, total_sum_flips, total_sum_tries, 
  total_downwards, total_sideways, total_upwards,
  total_successful_flips_incl_resets, total_successful_reset_count,
  total_null,
  total_after_init_num_bad,	/* Sum of num bad right after initial assignment */
  total_sum_successful_flips;	/* Sum of flips, only counting tries that found an */
				/* assignment. */

double experiment_seconds;	/* Number of seconds consumed after wff is read in */

/**************************/
/*  Parameters            */
/**************************/

char program_name[] = PROGRAM_NAME ;

FILE * try_stat_filep;

char wff_file[MAXLINE], assign_file[MAXLINE], report_file[MAXLINE], 
  init_file[MAXLINE],
  convert_file[MAXLINE], xtent_pipe[MAXLINE];

char hostname[MAXLINE] = "unknown";
struct utsname hostutsname;

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

int seed1,			/* Used to seed random number generator */
  seed2;			/* Rest of seed, used by urand */

int flag_save_best_max;		/* Save best assigns at end of try OR when current_num_bad is less */
				/* than this number */

int
  flag_walk,			/* 1 - 100 = when current_max_diff <= 0, then that
				   percentage of the time choose var to flip from 
				   pos_make_list, rather than max_diff_list. 
				   If negative, then do this even when max_diff > 0. */
  flag_walk_all_vars,		/* 1 = pick from all vars instead of pos_make_list */
  flag_only_unsat;		/* 1 = restrict max_diff_list (and up, down, sideways buckets) */
				/* to variables that appear in unsatisfied clauses. */

int flag_mail;			/* 1 = email error messages */

int flag_partial;		/* initial assignment file is a partial assignment */

int
  tabu_list_length;		/* Maximum (NOT current!) length of tabu list */

int
  flag_hillclimb;		/* Perform hillclimbing using up, down, sideways buckets */

int
  flag_manual_pick;			/* Debugging option */

int
  flag_bigflip;

int
  flag_superlinear;

char *flag_trace_names[] = {
    "flips", "flip_clauses", "diffs", "makes", "walks", "anneal", "clauses", "tries", "best", "tabu",
    "orphans", "assign", "clause_state"};

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

int
  flag_graphics;		/* 1 = call graphics routines after each flip */

int boost_threshhold,		/* Boost if current_num_bad below this value */
  boost_amount;			/* Number of flips to boost */

int report_interval;		/* Print report after this many tries */

int rand_method;		/* Method used to generate random flips; default = 3 */

int one_bit_mask;		/* Masks bit used by random functions in random_01 */

int  odds_true;		/* Odds that a variable will be initialized to true */

unsigned pause_usecs;		/* Number of usecs to pause between each flip */

long int raw_start_time;		/* current time of day */
struct tm * raw_start_tmptr;
char datestring[30];

/**************************/
/*  Misc                  */
/**************************/

int scratch;			/* used by abs_val macro */

char ss[10000] = "Error message string not initialized";	/* scratch string */

