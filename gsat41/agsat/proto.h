/* proto.h */

#if !defined(PROTO)
#  include "xv_c_types.h"
#  if defined(__cplusplus)||defined(sun)||defined(__STDC__)
#      include <stdlib.h>
#  endif
#  if defined(__cplusplus) || defined(__STDC__)
#    define PROTO( x )  x
#    define PARAMS( x )
#    define FORWARD( fun, args ) extern fun args
#    define PROTOTYPES 1
#  else
#    define PROTO( x )
#    define PARAMS( x ) x 
#    define FORWARD( fun, args ) extern fun ()
#  endif
#endif
