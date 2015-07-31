/* anneal.h -- GSAT */

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

#ifndef ANNEAL_H
#define ANNEAL_H
#include "proto.h"

EXTERN_FUNCTION( int anneal_parse_parameters, (char * inputline));
EXTERN_FUNCTION( void anneal_print_report, (FILE * fp_report));
EXTERN_FUNCTION( int anneal_pick_var, () );
EXTERN_FUNCTION( int random_01_prob, (double p ));
EXTERN_FUNCTION( void anneal_initialize, ());
EXTERN_FUNCTION( void anneal_gather_statistics, ());

#endif
