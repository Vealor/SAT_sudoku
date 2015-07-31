/* anneal.c -- GSAT */

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
#include "urand.h"
#include "anneal.h"
#include "utils.h"

#define MAX_SCHEDULE_SIZE 1000

struct anneal_sched_str {
    int steps;
    float temp;
    float finaltemp;
    float factor;
    int floor;
};

/* typedef struct anneal_sched_str *anneal_sched_str_ptr; */

struct anneal_sched_str anneal_schedule[MAX_SCHEDULE_SIZE+2];

char anneal_file[MAXLINE];	/* name of file (if any) containing anneal schedule */
int anneal_sched_size;		/* length of schedule */
int anneal_sched_repeat;	/* at end of schedule, repeat previous sched_repeat lines */
int anneal_repeat_max;		/* maximum number of times to repeat schedule; -1 = infinite */
int anneal_infinite;		/* 1 = an infinite geometric sequence is specified */
int anneal_pick_randomly;	/* 0 = sequence, 1 = random */
int anneal_count_flips;		/* 0 = schedule specifies number of picks;
				   1 = schedule specifies number of flips */
int anneal_current_line;	/* current line in the annealing schedule */
int anneal_current_step;	/* current step within the current line */
int anneal_current_repeat;	/* number of times schedule has been repeated */
int anneal_last_var_picked;	/* the last variable looked at by anneal; initially 0 */
int anneal_cumulative;		/* total number steps so far */
int anneal_total_length;	/* the maximum total length of the annealing schedule
				   (for informational purposes only) */
double anneal_current_temp;	/* current temperature */


static char helpmsg[] = "Format of annealing schedule:\n\
(1) 0 or more keywords, one per line:\n\
	random		- pick vars randomly (default)\n\
	sequential	- pick vars in sequence\n\
	flips		- count each flip as a step (default)\n\
	picks		- count each pick as a step\n\
(2) 1 or more lines of any of the following formats:\n\
\n\
(2a)  Pairs of steps and temperature; e.g.\n\
	400 50\n\
A temperature of -1 means run greedy; temperature of -2 means pick\n\
randomly from variables that appear in unsatisfied clauses.\n\
Temperatures are divided by 100.\n\
The change in energy function for a variable is simply its diff value.\n\
\n\
(2b)  A geometric progression, specified as\n\
	STEPS START_TEMP to END_TEMP by FACTOR\n\
For example,\n\
	100  50 to 20 by .8\n\
To mean anneal at temperature 50 for 100 steps, then at 50*0.8 for 100\n\
steps, then 50*0.8*0.8 steps, etc, stopping AFTER a run in which the\n\
temperature is 20 or less.  (E.g., the last 100 steps may be at\n\
19.89.)  Note that an END_TEMP of 0 specifies an infinite progression.\n\
\n\
(2c)  As above, but with the keyword floor:\n\
	STEPS START_TEMP to END_TEMP by floor FACTOR\n\
In this case, the temperature is updated each time to\n\
	 floor( FACTOR * temp )\n\
\n\
(3) A blank line, or a terminating keyword:\n\
	end		- end of schedule\n\
	repeat N	- repeat the last N lines indefinitely\n\
	repeat N M	- repeat the last N lines M times\n\
";


int
random_01_prob( PROTO( double ) p )
     /* Return a value of 1 with probability p, a value of 0 otherwise,
	using the probability function specified by rand_method */
PARAMS ( double p; )
{

    /* printf("Debug! left=%d, right=%d\n", (long)(urand(rd) %  INT_PROB_BASE ),
	   (long)( p * INT_PROB_BASE )); */


    if (p == 0.0) return 0;
    if (p == 1.0) return 1;
    switch(rand_method){
      case 1:
#ifdef SYSVR4
	if (((long)(lrand48() %  INT_PROB_BASE )) < (long)( p * INT_PROB_BASE ))
#else
	if (((long)(random() %  INT_PROB_BASE )) < (long)( p * INT_PROB_BASE ))
#endif
	  return 1;
	else return 0;
      case 2:
	if (((long)(urand(rd) %  INT_PROB_BASE )) < (long)( p * INT_PROB_BASE ))
	  return 1;
	else return 0;
    }
    return 0;			/* not reached */
}


int
anneal_parse_error()
     /* Print error message, and either exit(-1) or return 0 */
{
    crash_maybe("Error:  Can't parse annealing schedule!\n");
    return 0;
}

int
anneal_compute_length(PROTO(int) i)
     /* return total number of steps in line i of the schedule,
	including geometric cooling */
PARAMS( int i; )
{
    int total, steps, flr;
    double temp;
    float final, factor;

    if (anneal_schedule[i].factor == 0)
      total = anneal_schedule[i].steps;
    else {
	temp = anneal_schedule[i].temp;
	final = anneal_schedule[i].finaltemp;
	steps = anneal_schedule[i].steps;
	factor = anneal_schedule[i].factor;
	flr =  anneal_schedule[i].floor;
	total = steps;
	if (final == 0 && !flr){
	    anneal_infinite = 1;
	}
	else {
	    while (temp > final) {
		total += steps;
		temp *= factor;
		if (flr) temp = floor(temp);
	    }
	}
    }
    return total;
}


int 
anneal_parse_parameters(PROTO(char *) inputline)
     /* Input annealing schedule.  Returns 1 if schedule read,
	0 if errors encountered when reading from stdin; 
	print error and exit if error when reading from a file.
	May reset max_flips if the schedule does not repeat and is
	shorter than max_flips. */
PARAMS(char * inputline;)
{
    FILE * af;
    char word1[MAXLINE];
    int s;
    float t, tf, factor;
    int total_s;
    int repeat_s;
    int i;

    strcpy(anneal_file, "");

    if (sscanf(inputline, " anneal %s", anneal_file)==1){
	af = fopen(anneal_file, "r");
	if (af == NULL) {
	    crash_maybe("Error: can't open file\n");
	    return 0;
	}
	printf("Reading anneal file %s\n", anneal_file);
    }
    else {
	af =  stdin;
	printf("Enter annealing schedule (steps / temp):\n");
    }

    anneal_sched_size = 0;
    anneal_pick_randomly = 1;
    anneal_count_flips = 1;
    anneal_sched_repeat = 0;
    anneal_repeat_max = -1;
    anneal_total_length = -1;
    anneal_infinite = 0;
    total_s = 0;

    printf("> ");
    while(fgets(inputline, MAXLINE, af)!=NULL){
	printf("%s", inputline);
	if (sscanf(inputline, " %s", word1) != 1)
	  break;
	if (strcmp(word1, "?")==0)
	    printf(helpmsg);
	else if (strcmp(word1, "random")==0)
	  anneal_pick_randomly = 1;
	else if (strcmp(word1, "sequential")== 0)
	  anneal_pick_randomly = 0;
	else if (strcmp(word1, "flips")== 0)
	  anneal_count_flips = 1;
	else if (strcmp(word1, "picks")== 0)
	  anneal_count_flips = 0;
	else if (strcmp(word1, "end")==0)
	  break;
	else if (sscanf(inputline, " repeat %d %d", &anneal_sched_repeat, &anneal_repeat_max)==2) {
	    if (anneal_sched_repeat > anneal_sched_size)
	      return anneal_parse_error(); 
	    break; }
	else if (sscanf(inputline, " repeat %d", &anneal_sched_repeat)==1) {
	    if (anneal_sched_repeat > anneal_sched_size)
	      return anneal_parse_error(); 
	    anneal_infinite = 1;
	    break; }
	else if (sscanf(inputline, " %d %f to %f by floor %f", &s, &t, &tf, &factor)==4){
	    anneal_sched_size ++;
	    if (s < 1 || t < tf || factor >= 1 || factor <= 0) return anneal_parse_error();
	    anneal_schedule[anneal_sched_size].steps = s;
	    anneal_schedule[anneal_sched_size].temp = t;
	    anneal_schedule[anneal_sched_size].finaltemp = tf;
	    anneal_schedule[anneal_sched_size].factor = factor;
	    anneal_schedule[anneal_sched_size].floor = 1;
	    total_s += anneal_compute_length(anneal_sched_size); }
	else if (sscanf(inputline, " %d %f to %f by %f", &s, &t, &tf, &factor)==4){
	    anneal_sched_size ++;
	    if (s < 1 || t < tf || factor >= 1 || factor <= 0) return anneal_parse_error();
	    anneal_schedule[anneal_sched_size].steps = s;
	    anneal_schedule[anneal_sched_size].temp = t;
	    anneal_schedule[anneal_sched_size].finaltemp = tf;
	    anneal_schedule[anneal_sched_size].factor = factor;
	    anneal_schedule[anneal_sched_size].floor = 0;
	    total_s += anneal_compute_length(anneal_sched_size); }
	else if (sscanf(inputline, " %d %f", &s, &t)==2){
	    anneal_sched_size ++;
	    if (s < 1) return anneal_parse_error();
	    anneal_schedule[anneal_sched_size].steps = s;
	    anneal_schedule[anneal_sched_size].temp = t;
	    anneal_schedule[anneal_sched_size].finaltemp = 0.0;
	    anneal_schedule[anneal_sched_size].factor = 0.0;
	    anneal_schedule[anneal_sched_size].floor = 0;
	    total_s += s; }
	else 
	  return anneal_parse_error();
	if (anneal_sched_size >= MAX_SCHEDULE_SIZE){
	    crash_maybe("ERROR!  Annealing schedule too long!\n");
	    return 0;
	}
	printf("> ");
    }

    if (anneal_sched_size < 1) return anneal_parse_error();

    if (anneal_sched_repeat && anneal_repeat_max > 0){
	repeat_s = 0;
	for (i=anneal_sched_repeat; i > 0; i--)
	  repeat_s += anneal_compute_length(anneal_sched_size + 1 - i);
	total_s += repeat_s * anneal_repeat_max;
    }  

    if (!anneal_infinite){
	if (anneal_count_flips){
	    printf("Attention!  Resetting max_flips to %d\n", total_s);
	    max_flips = total_s;
	}
	else {
	    if (max_flips > 0)
	      printf("Attention!  Try will end when max_flips=%d OR picks=%d\n",
		     max_flips, total_s);
	    else
	      printf("Attention!  Try will end when max_flips=%d X nvars OR picks=%d\n",
		     -max_flips, total_s);
	}
    }
    else {
      if (max_flips > 0)
	printf("Attention!  Infinite schedule will end when max_flips=%d\n", max_flips);
      else
	printf("Attention!  Infinite schedule will end when max_flips=%d X nvars\n", -max_flips);
    }
    anneal_total_length = total_s;


    /* printf("DEBUG, anneal_repeat_max= %d\n", anneal_repeat_max); */
    
    return 1;
}


void 
anneal_print_report(PROTO(FILE *) fp)
     /* Print annealing schedule to report file */
PARAMS(FILE * fp;)
{
    int i;


    /* printf("DEBUG: at report time, anneal_repat_max  = %d \n", anneal_repeat_max); */


    fprintf(fp, "anneal_file: %s\n", anneal_file);
    fprintf(fp, "anneal_total_length: %d\n", anneal_total_length);
    fprintf(fp, "Annealing schedule:\n");
    fprintf(fp, "    steps     temp\n");
    if (anneal_pick_randomly != 0)
      fprintf(fp, "random\n");
    else
      fprintf(fp, "sequential\n");
    if (anneal_count_flips != 0)
      fprintf(fp, "flips\n");
    else
      fprintf(fp, "picks\n");
    for (i=1; i<= anneal_sched_size; i++){
	if (anneal_schedule[i].factor == 0.0)
	  fprintf(fp, "  %6d    %6.2f\n", anneal_schedule[i].steps, 
		  anneal_schedule[i].temp);
	else if (anneal_schedule[i].floor == 0)
	  fprintf(fp, "  %6d    %6.2f  to  %6.2f  by  %6.4f\n", 
		  anneal_schedule[i].steps, 
		  anneal_schedule[i].temp,
		  anneal_schedule[i].finaltemp,
		  anneal_schedule[i].factor);
	else
	  fprintf(fp, "  %6d    %6.2f  to  %6.2f  by  floor %6.4f\n", 
		  anneal_schedule[i].steps, 
		  anneal_schedule[i].temp,
		  anneal_schedule[i].finaltemp,
		  anneal_schedule[i].factor);
    }
    if (anneal_sched_repeat == 0)
      fprintf(fp, "end\n");
    else
      fprintf(fp, "repeat %d %d\n", anneal_sched_repeat, anneal_repeat_max);
    fprintf(fp, "End of annealing schedule\n\n");
}

void
anneal_initialize()
     /* Call before each try */
{
    anneal_last_var_picked = 0;
    anneal_current_step = 1;
    anneal_current_line = 1;
    anneal_cumulative = 0;
    anneal_current_repeat = 0;
    anneal_current_temp = anneal_schedule[1].temp;
}

void
anneal_bump_schedule(PROTO(int) var, PROTO(int) diff)
     /* Move to next temperature */
PARAMS( int var; int diff; )
{

    if ((flag_trace & FLAG_TRACE_ANNEAL)){
	anneal_cumulative += anneal_schedule[anneal_current_line].steps;
	if (anneal_current_temp == 0 && current_max_diff < 0)
	  printf("Warning!  Stuck in local minima, skipping to next line in schedule\n");
	if (var == 0){
	    printf("  Annealed line=%d, cum=%d, steps=%d, temp=%.2f, num_bad=%d, low_bad=%d, d=%d s=%d u=%d n=%d\n",
		   anneal_current_line, 
		   anneal_cumulative,
		   anneal_schedule[anneal_current_line].steps,
		   anneal_current_temp,
		   current_num_bad,
		   low_bad,
		   downwards_count,
		   sideways_count,
		   upwards_count,
		   null_count );
	}
	else {			/* Must adjust numbers to account for following flip */
	    printf("  Annealed line=%d, cum=%d, steps=%d, temp=%.2f, num_bad=%d, low_bad=%d, d=%d s=%d u=%d n=%d\n",
		   anneal_current_line, 
		   anneal_cumulative,
		   anneal_schedule[anneal_current_line].steps,
		   anneal_current_temp,
		   current_num_bad - diff,
		   (diff > 0 ? low_bad - diff : low_bad),
		   downwards_count + (diff > 0),
		   sideways_count + (diff == 0),
		   upwards_count + (diff < 0),
		   null_count );
	}
	if (flag_trace & FLAG_TRACE_CLAUSES) get_bad_clauses(1, 0);
    }
		
    if (anneal_schedule[anneal_current_line].factor != 0 &&
	anneal_current_temp > anneal_schedule[anneal_current_line].finaltemp){
				/* geometric cooling */
	anneal_current_step = 1;
	anneal_current_temp *= anneal_schedule[anneal_current_line].factor;
	if (anneal_schedule[anneal_current_line].floor) 
	  anneal_current_temp = floor(anneal_current_temp);
    }
    else {
	anneal_current_line ++;
	anneal_current_step = 1;

	/* printf("DEBUG: now anneal_repeat_max  = %d \n", anneal_repeat_max); */
	/* printf("DEBUG: now anneal_current_line  = %d \n", anneal_current_line); */


	if (anneal_current_line > anneal_sched_size && 
	    ( anneal_repeat_max == -1 ||
	     ++anneal_current_repeat <= anneal_repeat_max )){
	    anneal_current_line -= anneal_sched_repeat;

	    /* printf("DEBUG: resetting anneal_current_line  = %d \n", anneal_current_line); */

	}
	anneal_current_temp = anneal_schedule[anneal_current_line].temp;
    }
}



int
anneal_pick_var()
     /* Pick var to flip according to annealing schedule.
	Returns 0 if end of schedule is reached. */
{
    double prob;
    int var, diff, busylimit;

    busylimit = 10000 * nvars;
    do {
	if (anneal_current_line > anneal_sched_size) /* End of schedule reached */
	  return 0;

	if (--busylimit<=0){
	    printf("HELP!  Annealing stuck in infinite loop!\n");
	    printf("  line=%d, temp=%.2f, null_count=%d, flip=%d\n",
		   anneal_current_line, anneal_current_temp, null_count, flip);
	    flag_abort = 1;
	    print_report("ANNEALING STUCK IN INFINITE LOOP");
	    exit(-1);
	}

	/* make a pick */
	if (anneal_current_temp == -1){ 
	    var = pick_greedy_var();
	    diff = assign[var].diff;
	}
	else if (anneal_current_temp == -2){ 

	    if (length_of(walk) > 0) {
		var = random_member(walk);
	    }
	    else {
		var = pick_greedy_var();
	    }
	    diff = assign[var].diff;
	}
	else if (anneal_current_temp < 0){
	    sprintf(ss, "ERROR, bad annealing temp %f\n", anneal_current_temp);
	    crash_and_burn(ss);
	}
	else {
	    if (anneal_pick_randomly && anneal_current_temp == 0 && current_max_diff == 0){
		var = pick_greedy_var();
	    }
	    else if (anneal_pick_randomly) {
		var = random_1_to(nvars);
	    }
	    else {
		var = (1 + anneal_last_var_picked) % nvars + 1;
		anneal_last_var_picked = var;
	    }
	    diff = assign[var].diff;

	    if (diff < 0){
		if (anneal_current_temp <= 0)
		  var = 0;
		else {
		    
		    /* printf("DEBUG!  arg to exp=%f\n",   ((double)diff * 100.0) / anneal_current_temp); */

		    prob = exp (  ((double)diff * 100.0) / anneal_current_temp);

		    /* printf("DEBUG!  diff=%d, temp=%f, prob=%f\n", diff, anneal_current_temp, prob); */

		    if (random_01_prob(prob)==0){
			var = 0;
			/* printf("DEBUG!  random_01_prob returns 0!\n"); */
		    }
		}
	    }
	}

	if (var == 0) null_count ++;

	if (!anneal_count_flips || var != 0 || (anneal_current_temp == 0 && current_max_diff < 0)){
	    anneal_current_step ++;
	    if (anneal_current_step > anneal_schedule[anneal_current_line].steps ||
		(anneal_current_temp == 0 && current_max_diff < 0))
	      anneal_bump_schedule(var, diff);
	}
    } while (var == 0);

    return var;
}

