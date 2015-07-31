/* This mixed linear congruential generator has period 2.30584E+18
/* and "good" spectral properties.
/* */
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

#include "urand.h"

extern char *malloc(), *calloc();

#define a1 40014
#define m1 2147483563
#define q1 (m1/a1)
#define r1 (m1%a1)

#define a2 40692
#define m2 2147483399
#define q2 (m2/a2)
#define r2 (m2%a2)

void
urewind(up)
uniform *up;
{
	up->s1 = up->s1_seed;
	up->s2 = up->s2_seed;
}

uniform *
uopen()
{
	uniform *up;

	if(up = (uniform *) calloc(1, sizeof(*up))) {
		up->s1_seed = 1;
		up->s2_seed = 1;
		urewind(up);
		return(up);
	}

	return((uniform *)0);
}

uniform *
udup(up)
uniform *up;
{
	uniform *new_up;
	if(new_up = (uniform *) malloc(sizeof(*up))) {
		*new_up = *up;
		return(new_up);
	}
	return((uniform *)0);
}

void
uclose(up)
uniform *up;
{
	up->s1 = 0;	/* mark this stream closed */
}

void
useed(up, x1, x2)
uniform *up;
int x1, x2;
{

	up->s1_seed = x1%m1;
	up->s2_seed = x2%m2;
	urewind(up);
}

int
urand(up)
register uniform *up;
{
	register int lo, hi, z;
	register int s1, s2;

	s1 = up->s1;
	s2 = up->s2;

	hi = s1 / q1;
	lo = s1 - (hi * q1);	/* lo = seed % q */

	s1 = (a1 * lo) - (r1 * hi);

	if(s1 < 0) {
		s1 += m1;
	}

	up->s1 = s1;

	hi = s2 / q2;
	lo = s2 - (hi * q2);	/* lo = seed % q */

	s2 = (a2 * lo) - (r2 * hi);

	if(s2 < 0) {
		s2 += m2;
	}

	up->s2 = s2;

	z = s1 - s2;

	if(z < 1) {
		z = z + m1;
	}

	return(z);
}
