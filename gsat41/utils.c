/* utils.c -- utility functions */

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

#include "utils.h"
#include <stdio.h>
#include <string.h>
#include "gsat.h"

int
interactive()
     /* Returns 1 iff stdin is a tty */
{
    return isatty(fileno(stdin));
}

void
exit_maybe()
     /* Error exit iff stdin is not a tty (i.e. not interactive) */
{
    if (!interactive()) exit (-1);
}

int
crash_and_burn(PROTO(char *) msg)
PARAMS( char * msg; )
{
    FILE *fp_report;
    char mailmsg[4000];

    /* cin_system(); */

    printf("\n\nERROR - ERROR - ERROR - ERROR - ERROR - ERROR\n");
    printf(msg);
    printf("ERROR - ERROR - ERROR - ERROR - ERROR - ERROR\n");
    
    fprintf(stderr, "\n\nERROR - ERROR - ERROR - ERROR - ERROR - ERROR\n");
    fprintf(stderr, msg);
    fprintf(stderr, "ERROR - ERROR - ERROR - ERROR - ERROR - ERROR\n");

    if ((fp_report = fopen(report_file, "w"))!=NULL){
	fprintf(fp_report, "ERROR - ERROR - ERROR - ERROR - ERROR - ERROR\n");
	fprintf(fp_report, "wff_file: %s\n", wff_file);
	fprintf(fp_report, msg);
	fprintf(fp_report, "ERROR - ERROR - ERROR - ERROR - ERROR - ERROR\n");
	fclose(fp_report);
    }
    if (flag_mail){
	strcpy(mailmsg, "echo 'Subject:  Error Message from GSAT\n\nGSAT ERROR: ");
	strcat(mailmsg, msg);
	/* Some systems don't have the Berkeley mailer installed! */
	/* strcat(mailmsg, "' | mail -s 'bad news from GSAT' `whoami`"); */
	strcat(mailmsg, "' | /bin/mail `whoami`");
	system(mailmsg);
    }

    exit(-1);
}

void
crash_maybe(PROTO(char *) msg)
   /* Noisy error exit iff stdin is not a tty; otherwise, just print 
      error messge */
PARAMS( char * msg; )
{
    if (interactive()) {
	printf(msg);
    }
    else {
	crash_and_burn(msg);
    }
}

int
file_exists( PROTO(char *) fname)
     /* Returns 1 iff file named fname is readable */
PARAMS( char * fname; )
{
    FILE * fp;

    if ((fp = fopen(fname, "r")) == NULL) return 0;
    (void) fclose(fp);
    return 1;
}

void
get_input_file_name( PROTO( char * ) prompt, PROTO( char * ) name )
     /* Print prompt and read a line from stdin naming a file;
	check that the file exists; if not, then if interactive
	input, reprompt and reread; otherwise error exit. */
PARAMS( char *  prompt; char *  name; )
{
    while (1) {
	printf( prompt );
	if (gets( name ) == NULL) {
	    crash_maybe("Unexpected EOF on stdin!\n");
	    exit(-1);
	}
	if (file_exists( name )) return;
	crash_maybe("Error: cannot open file\n");
	exit(-1);
    }
}

void
get_symbol( PROTO( char * ) prompt, PROTO( char * ) dest)
     /* Print prompt and read a line; put the first (whitespace delimited)
	word in dest; if line is all whitespace, leave dest unchanged.
	If gets fails on end of file, error exit. */
PARAMS( char * prompt; char * dest; )
{
    char inputline[128];
    char dummy[128];

    printf(prompt);
    if (gets( inputline ) == NULL) {
	crash_maybe("Unexpected EOF on stdin!\n");
	exit(-1);
    }
    if (sscanf(inputline, " %s", dummy)==1)
      strcpy(dest, dummy);
}
    
int
empty_string( PROTO( char * ) str )
     /* Return 1 iff str is empty or only whitespace */
PARAMS( char * str; )
{
    char dummy[128];
    return (sscanf(str, " %s", dummy)!=1);
}
