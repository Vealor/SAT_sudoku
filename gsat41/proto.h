/* proto.h */

#ifndef PROTO

#ifndef NeedFunctionPrototypes
#if defined(FUNCPROTO) || __STDC__ || defined(__cplusplus) || defined(c_plusplus)
#define NeedFunctionPrototypes 1
#else
#define NeedFunctionPrototypes 0
#endif
#endif /* NeedFunctionPrototypes */

#  if NeedFunctionPrototypes
#    define PROTO( x )  x
#    define PARAMS( x )
#    define EXTERN_FUNCTION( fun, args ) extern fun args
#    define STATIC_FUNCTION( fun, args ) static fun args
#  else
#    define PROTO( x )
#    define PARAMS( x ) x 
#    define EXTERN_FUNCTION( fun, args ) extern fun ()
#    define STATIC_FUNCTION( fun, args ) static fun ()
#  endif

#endif /* PROTO */

