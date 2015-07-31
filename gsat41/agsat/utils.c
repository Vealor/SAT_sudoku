/* utils.c -- utility functions */

#include "utils.h"
#include <stdio.h>
#include <string.h>

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
	    printf("Unexpected EOF on stdin!\n");
	    exit(-1);
	}
	if (file_exists( name )) return;
	printf("Error: can't open file\n");
	if (! interactive()) exit(-1);
    }
}

void
get_symbol_default( PROTO( char * ) prompt, PROTO( char * ) dest, PROTO( char * ) def)
     /* Print prompt and read a line; put the first (whitespace delimited)
	word in dest; if line is all whitespace, instead copy default into dest.
	If gets fails on end of file, error exit. */
PARAMS( char * prompt; char * dest; char * def;)
{
    char inputline[128];

    printf(prompt);
    if (gets( inputline ) == NULL) {
	printf("Unexpected EOF on stdin!\n");
	exit(-1);
    }
    if (sscanf(inputline, " %s", dest)!=1)
      strcpy(dest, def);
}
    
int
empty_string( PROTO( char * ) str )
     /* Return 1 iff str is empty or only whitespace */
PARAMS( char * str; )
{
    char dummy[128];
    return (sscanf(str, " %s", dummy)!=1);
}
