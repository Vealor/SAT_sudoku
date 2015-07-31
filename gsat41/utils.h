/* utils.h -- utility functions */

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

#include "proto.h"

EXTERN_FUNCTION( int interactive, () ); /* Returns 1 iff stdin is a tty */
EXTERN_FUNCTION( void exit_maybe, () );	/* Error exit iff stdin is not a tty */
EXTERN_FUNCTION( int file_exists, (char * fname) ); 
     /* Returns 1 iff file named fname is readable */
EXTERN_FUNCTION( void get_input_file_name, (char *  prompt, char *  name ));
     /* Print prompt and read a line from stdin naming a file;
	check that the file exists; if not, then if interactive
	input, reprompt and reread; otherwise error exit. */
EXTERN_FUNCTION( void get_symbol, (char * prompt, char * dest));
     /* Print prompt and read a line; put the first (whitespace delimited)
	word in dest; if line is all whitespace, instead copy def into dest.
	If gets fails on end of file, error exit. */
EXTERN_FUNCTION( int empty_string, ( char *  str ));
     /* Return 1 iff str is empty or only whitespace */
EXTERN_FUNCTION ( int crash_and_burn, (char * msg));
     /* Print a lot of error messages everywhere and then die */
EXTERN_FUNCTION ( void crash_maybe, (char * msg));
     /* Print a lot of error messages only if not interactive */
