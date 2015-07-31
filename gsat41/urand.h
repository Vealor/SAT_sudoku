/* urand.h --- 9/25/92 */

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

#ifndef URAND_H
#define URAND_H
#include "proto.h"

typedef struct {
    int s1;
    int s2;
    int s1_seed;
    int s2_seed;
    } uniform;

EXTERN_FUNCTION( void useed, (uniform *up, int x1, int x2));
EXTERN_FUNCTION( void uclose, (uniform *up));
EXTERN_FUNCTION( void urewind, (uniform *up));
EXTERN_FUNCTION( uniform *uopen, () );
EXTERN_FUNCTION( uniform *udup, (uniform *up) );
EXTERN_FUNCTION( int urand, (uniform *up) );

#endif
