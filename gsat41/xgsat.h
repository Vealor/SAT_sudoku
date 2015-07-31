#include <X11/Intrinsic.h>

#if NeedFunctionPrototypes

extern  void	xgsat_init( char ** argv, int argc, int nvars, int nclauses, Boolean (*work_proc)());
extern	void	xgsat_do_events_forever(void);
extern	void	xgsat_do_events(void);
extern	void	xgsat_wait_for_var( int * var );
extern	void	xgsat_show_all( int state );
extern	void	xgsat_show_clause_state( int clause, int state, Boolean	flush );
extern	void	xgsat_show_var_state( int var, int state, Boolean flush );
extern	void	xgsat_show_flip_and_unsat( int flip, int unsat );

#else

extern  void	xgsat_init();
extern	void	xgsat_do_events_forever();
extern	void	xgsat_do_events();
extern	void	xgsat_wait_for_var();
extern	void	xgsat_show_all();
extern	void	xgsat_show_clause_state();
extern	void	xgsat_show_var_state();
extern	void	xgsat_show_flip_and_unsat();

#endif

/* GLOBALS */
extern 	int	xgsat_command;

/* GLOBAL DEFINITIONS */
#define	XGSAT_STOP	0
#define	XGSAT_GO	1
#define XGSAT_CONTINUOUS 2
#define	XGSAT_QUIT	3
#define XGSAT_STEP	4
