/**
 ** FILE:  xgsat.c
 **/

#if defined(mips) && !defined(sgi) && !defined(Mips)
#define Mips
#endif

#include <X11/Intrinsic.h>		 		/* 	     Intrinsics Definitions */
#include <X11/StringDefs.h>				/* Standard Name-String definitions */
#include <X11/Xaw/Scrollbar.h>					 /* Athena Scrollbar Widget */
#include <X11/Xaw/Command.h>				   	 /*   Athena Command Widget */
#include <X11/Xaw/Paned.h>				  	 /*     Athena Paned Widget */
#include <X11/Xaw/Label.h>				  	 /*     Athena Label Widget */
#include <X11/Xaw/Form.h>					 /*      Athena Form Widget */
#include <X11/Xaw/Box.h>					 /*      Athena Form Widget */
#include <X11/Core.h>					 	 /*  Intrinsics Core Widget */


#if NeedFunctionPrototypes || defined(sun)
#include <stdlib.h> 
#endif
#include <string.h>
#include <stdio.h>
#include <math.h>

#include "xgsat.h"
#include "gsat.h"

#define DRAW_VAR	1
#define DRAW_CLAUSE	0

/**
 ** FUNCTION NAMES:  These are the functions called from gsat.c,
 **		     or whichever program chooses to use this
 **		     graphical interface:
 **		     xgsat_init, xgsat_wait_for_var, xgsat_do_events, 
 **		     xgsat_do_events_forever, xgsat_pause_maybe,
 **		     xgsat_show_clause_state, xgsat_show_var_state,
 **		     xgsat_show_all, xgsat_show_flip_and_unsat,
 **		    
 ** PURPOSES:  
 **	xgsat_init - Passed the number of variables and clauses used, & a pointer 
 **		     to a work procedure (may be NULL).  Initializes the variables 
 **		     used in the program, & the widgets are created for the interface 
 **		     with their callback functions.  Called before other xgsat.c functions.
 **
 **	xgsat_wait_for_var - Passed a variable that will wait to become non-zero while
 **		     handling events (Expose, Resizing, Button Press, etc).  The 
 **		     variable will become non-zero when any button but STOP is pressed.
 **
 **     xgsat_do_events - No parameters passed.  Events are handled while pending.
 **
 **     xgsat_do_events_forever - No parameters passed.  Events are handled until
 **		     the user presses the Quit button.  Call this when all computation 
 **		     is done. 
 **
 **     xgsat_pause_maybe - called if a pause is needed before performing the next
 **		     calculation in the drawing window.  Can change the pause time 
 **		     by using the "Delay" scrollbar. 
 **
 **	xgsat_show_(clause/variable)_state - Passed the clause/variable number, the
 **		     state for the clause/variable, and flush, which should be passed
 **		     as true if not called from xgsat.c.  The clause/variable is set
 **		     to the given state if possible, and then updates the display.
 **
 **	xgsat_show_all - Passed the state to set all the clauses and variables to.
 **		     They are updated and the display is then redrawn.
 **
 **	xgsat_show_flip_and_unsat - Passed the number of variables flipped so far 
 **		     and the number of unsatisfied clauses.  These numbers are 
 **		     updated on the display.
 **
 ** GLOBAL VARIABLES REFERENCED:  xgsat_command							
 **/

/* local variables */
static  XtAppContext	app_context;
static  Widget		topLevel, base, draw_win, quit_button, label_box, button_box, 
			stop_button, step_button, go_button, cont_button, box_box,
			delay_box, delay_label, delay_scroll, big_box, left_box,
			message_box, flip_label, flip_num, unsat_label, unsat_num;

static Boolean		*var_is_displayed;    /*    determines if the variable is displayed */
static Boolean  	work_proc_installed;  /*    whether the work procedure is installed */
static Boolean		(* xgsat_work_proc)();/*     the work procedure (passed in to main) */ 
static GC		gc[5];		      /*   array of graphic contexts for the colors */
static char		*name[] = {"red", "yellow", "green"};   /* names of the colors used */
static char		states[4];	      /* holds the characters of states-'t','f','u' */
static char		messg[1024];	      /* holds the message (ie. clause or variable) */
static int		*clauses;	      /*     array to hold the state of the clauses */
static int		*variables;	      /*  array to hold the states of the variables */
static int		num_clauses;	      /*       the number of clauses in the problem */
static int		num_vars;	      /*     the number of variables in the problem */
static int		message_size;  /* # parameters in messg (determining var or clause) */
static int		first_param;   /*  first parameter in the message (clause or var #) */
static int		rects_per_side;	   /* # rectangles on side of square in the drawing */
static int              rects_per_small_side;     /* #rects on vertical side of smaller one */
static int              larger;		  /*  whichever is larger:  num_clauses or num_vars */
static int		smaller;	  /*  whichever is smaller: num_clauses or num_vars */
static int		X_Base, Y_Base;	  /* bottom left location of messg in the label_box */
static int		xgsat_pause_duration; /* time(secs) to pause between variable flips */
static unsigned int	pix_per_rect;	  /*  # screen pixels per each rectangle in drawing */
static int              flip_number; /* last value passed by show_flip_and_unsat */
static int              unsat_number; /* last value passed by show_flip_and_unsat */

/* global variables */
int			xgsat_command;	  /*        keeps track of which button was pressed */


/* xgsat_allocate_colors(topLevel, name, num_name, gc):
   Allocate an array of graphic contexts, gc, where the background of each is white
   and the foregrounds are specified by the array of color names name.
   num_name+2 GC's will be allocated, where the next to last has a white foreground,
   and the last has a black background.  This procedure creates a private colormap
   if and only if the colors do not fit in the default colormap. */
#if NeedFunctionPrototypes
static void xgsat_allocate_colors(Widget topLevel,
				  char * name[],
				  int num_name,
				  GC gc[])
#else
static void xgsat_allocate_colors(topLevel, name, num_name, gc)
Widget topLevel;
char * name[];
int num_name;
GC gc[];
#endif
{
    int 		i;
    int			color_exist; /* true if color can be parsed */
    XGCValues		gcv;	/* structure for setting graphics context */
    XColor		exact_def_return; /* holds the RGB values and pixel value */
    Colormap		colormap; /* either the default or a private colormap */
    unsigned long 	my_white, my_black; /* pixel values for white and black on display */
    int 		private_colormap = FALSE; /* initially try to use default colormap */
    int 		alloc_okay; /* true if each alloc color succeeds */
    Screen *            screen = XtScreen( topLevel );
    Display *           display = XtDisplay( topLevel );
    Window              rootwin = RootWindowOfScreen( XtScreen( topLevel ));
    
    colormap = DefaultColormapOfScreen( screen); /* get a colormap */
    my_white = WhitePixelOfScreen( screen);
    my_black = BlackPixelOfScreen( screen);
    for(i=0;i < num_name;i++) {	/* get the RGB values for each color */
	color_exist = XParseColor( display, colormap, name[i], &exact_def_return);
	if (!color_exist){
	    perror("Warning: Colors desired for application not available\n");
	    exact_def_return.pixel = i == 0 ? my_black : my_white;
	}
	else {
	    alloc_okay = XAllocColor( display, colormap, &exact_def_return);
	    if (!alloc_okay){	/* the default colormap is full, so create a private colormap */
		if (private_colormap){
		    perror("XAllocColor in private colormap failed\n");
		    exit(1);
		}
		colormap = XCopyColormapAndFree( display, colormap );
		private_colormap = TRUE;
		XtVaSetValues( topLevel, XtNcolormap, colormap, NULL); /* install private colormap */
		exact_def_return.pixel = my_white; /* define white pixel in private colormap */
		XQueryColor( display, DefaultColormapOfScreen(screen), &exact_def_return );
		XAllocColor( display, colormap, &exact_def_return );
		my_white = exact_def_return.pixel;
		exact_def_return.pixel = my_black; /* define black pixel in private colormap */
		XQueryColor( display, DefaultColormapOfScreen(screen), &exact_def_return );
		XAllocColor( display, colormap, &exact_def_return );
		my_black = exact_def_return.pixel;
		/* re-parse and re-allocate the current color */
		XParseColor( display, colormap, name[i], &exact_def_return);
		if (!XAllocColor( display, colormap, &exact_def_return)){
		    perror("XAllocColor in private colormap failed\n");
		    exit(1);
		}
	    }
	}
	/*     create the GC for the color desired */
	gcv.foreground = exact_def_return.pixel;
	gc[i] = XCreateGC( display, rootwin, GCForeground, &gcv);
    }
    /* create GC with white foreground and white background */
    gcv.foreground = my_white;
    gc[i] = XCreateGC( display, rootwin, GCForeground, &gcv); i++;
    /* create GC with black foreground and white background */
    gcv.foreground = my_black;
    gc[i] = XCreateGC( display, rootwin, GCForeground, &gcv);
    /* set all the GC backgrounds to white; note that my_white may be redefined */
    /* when a private colormap is allocated */
    gcv.background = my_white;
    for (i=0; i< num_name+2; i++){
	XChangeGC( display, gc[i], GCBackground, &gcv);
    }
}


 /** This function is called from gsat and handles
  ** events until one of them causes var to be 
  ** non-zero.
  **/
#if NeedFunctionPrototypes
void xgsat_wait_for_var( int * var )
#else
void xgsat_wait_for_var( var)
   int	*var;
#endif
{
   XEvent	event;

   if ((* var) == 0) {		/* update the flip and unsat display, if necessary */
       xgsat_show_flip_and_unsat( flip_number, unsat_number );
   }

   while ((* var) == 0)				  /* while gsat is not calculating anything */
   {
 	XtAppNextEvent( app_context, &event);	  /*   get the next even on the event queue */
	XtDispatchEvent( &event);	 	  /* 			 dispatch the event */
   }

   while (XtAppPending( app_context))		  /*        after "go","step",or "continue" */
   {	XtAppNextEvent( app_context, &event);	  /*        was pressed, finish dispatching */
	XtDispatchEvent(&event);		  /*    the rest of the events on the queue */
   }
}


 /** While there are events pending on the event queue, 
  ** get them and dispatch them.  Called by gsat.
  **/
#if NeedFunctionPrototypes
void xgsat_do_events(void)
#else
void xgsat_do_events()  
#endif
{
   XEvent	event;

   while (XtAppPending( app_context)) 
   {	XtAppNextEvent( app_context, &event);
	XtDispatchEvent(&event);
   }
}


 /** When gsat is done with all it's calculations, this function
  ** is invoked to handle any events until the quit button is
  ** pressed, which terminates the program.
  **/
#if NeedFunctionPrototypes
void xgsat_do_events_forever(void)
#else
void xgsat_do_events_forever()   
#endif
{
   XEvent	event;

   while (xgsat_command != XGSAT_QUIT)	      
   {					      
   	XtAppNextEvent( app_context, &event);                      /* get & dispatch events */
	XtDispatchEvent(&event); 				   /*  from the event queue */
   }
   exit(1);				  
}


 /** If a work procedure was passed to xgsat_init()
  ** and hasn't been installed yet, then install it.
  ** This fuction is called by xgsat_callback().
  **/
#if NeedFunctionPrototypes
static void xgsat_start_work(void)
#else
static void xgsat_start_work()
#endif
{
   XtWorkProcId		work_ID;

   if (xgsat_work_proc != NULL && work_proc_installed != TRUE)	
   {
        work_ID = XtAppAddWorkProc( app_context, xgsat_work_proc, draw_win);	
	work_proc_installed = TRUE;					
   }	
}


 /** When any of the buttons are pressed, this
  ** function is invoked, installing the work_procedure
  ** if desired.
  **/
#if NeedFunctionPrototypes
static void xgsat_callback(
   Widget	w,
   XtPointer	client_data,
   XtPointer	call_data)
#else
static void xgsat_callback( w, client_data, call_data)
   Widget	w;
   XtPointer	client_data,
		call_data;
#endif
{
   xgsat_command = (int) client_data;	   /* if any button was pressed, xgsat_command will */
   if (xgsat_command != XGSAT_STOP)	   /*     be set to the number corresponding to the */
   	xgsat_start_work();		   /*       button, and if it wasn't Stop, then the */
}					   /*   work procedure will attempt to be installed */


 /** If the scrollbar was moved, this function is invoked,
  ** changing the time of the desired pause between flips.
  **/

#if NeedFunctionPrototypes
static void xgsat_change_delay(
   Widget       scrollbar,				 /* the scrollbar widget was passed */
   XtPointer    client_data,
   XtPointer    percent_ptr)				 /*  where the left side of the bar */
#else
static void xgsat_change_delay( scrollbar, client_data, percent_ptr)
   Widget       scrollbar;				 /* the scrollbar widget was passed */
   XtPointer    client_data,
                percent_ptr;				 /*  where the left side of the bar */
#endif
{							 /*      is in the scrollbar window */
   float percent;

   percent = *(float *)percent_ptr;			 /* cast the percent_ptr as a float */
   xgsat_pause_duration = (int) ((percent) * 1000);	 /*       how long the delay should */
}						 /* be between flipping vars (milliseconds) */


 /** This function is called when the time is up from
  ** XtAppAddTimeOut() in xgsat_pause_maybe.  It allows
  ** for the program to continue calculations.
  **/   

#if NeedFunctionPrototypes
static void xgsat_pause_timeout(
   XtPointer data,
   XtIntervalId * id)
#else
static void xgsat_pause_timeout( data, id )
XtPointer data;	
XtIntervalId * id;
#endif
{
    XEvent	dummy_event;
    int 	* done;

    done = (int *) data;				     /*     cast data off as an int */
    (* done) = 1;					     /*  & set done to 1 so *var in */
							     /*     xgsat_wait_for_var != 0 */
    dummy_event.xexpose.type = Expose;			     /* create a dummy expose event */
    dummy_event.xexpose.window = XtWindow( draw_win );	     /*   that will not be executed */
    dummy_event.xexpose.display = XtDisplay( draw_win );     /*     since the xexpose.count */
    dummy_event.xexpose.count = 2;			     /* 	         equal to 2 */
    XSendEvent( dummy_event.xexpose.display, dummy_event.xexpose.window,  /* send the event */
        FALSE, ExposureMask, &dummy_event );

}

 /** This function is called by gsat while calculations
  ** are being processed to see if a pause between flips
  ** is desired, and if so, takes care of it.
  **/

#if NeedFunctionPrototypes
void xgsat_pause_maybe(void)
#else
void xgsat_pause_maybe()
#endif
{
    int pause_finished;

    if (0 != xgsat_pause_duration){		    /*          if a pause duration is set, */
        pause_finished = 0;			    /* 	          the pause is not finished */
        XtAppAddTimeOut( app_context, (unsigned long)xgsat_pause_duration,  /* set up timer */
			  xgsat_pause_timeout, (XtPointer) &pause_finished);/*   that calls */
        xgsat_wait_for_var(&pause_finished);	    /* xgsat_pause_timeout when time is up, */
    }					  /* releasing the pause, so the gsat will continue */
}


 /** This function draws the correct box in the drawing
  ** window in the correct color and size, corresponding
  ** to the state of the clause or variable
  **/
#if NeedFunctionPrototypes
static void xgsat_draw(
   int	clause_var,			  /* 		   is either a clause or a variable */
   int	parameter,			  /* 	       the number of the clause or variable */
   int	state)				  /* 	        the state of the clause or variable */
#else
static void xgsat_draw( clause_var, parameter, state)
   int	clause_var,			  /* 		   is either a clause or a variable */
	parameter,			  /* 	       the number of the clause or variable */
	state;				  /* 	        the state of the clause or variable */
#endif
{
   int	y_block,			  /* 	     which row the clause or variable is in */
	x_block,			  /*      which column the clause or variable is in */
	y_coord,			  /* the pixel y-coordinate in draw_win for the box */
	x_coord;			  /* the pixel x-coordinate in draw_win for the box */

   y_block = ((parameter + rects_per_side - 1)/rects_per_side) - 1; /* calculate the blocks */
   x_block = (parameter - (y_block * rects_per_side)) - 1;
   if (clause_var == DRAW_VAR)
	y_block = (smaller == num_clauses)?y_block + rects_per_small_side + 1:
					   y_block + rects_per_side + 1;
   y_coord = y_block * pix_per_rect; 			       /* calculate the coordinates */
   x_coord = x_block * pix_per_rect;  
		      /* draw the rectangle in the correct color for the variable or clause */
   XFillRectangle( XtDisplay( topLevel), XtWindow( draw_win), gc[state+1], 
		   x_coord, y_coord, pix_per_rect, pix_per_rect); 
}


 /** When a variable or clause state is going to get changed, 
  ** this function is called first to check if the clause or
  ** variable and the state is valid. 
  **/

#if NeedFunctionPrototypes
static void check_state(
   int	num, 
   int	clause_var, 
   int	state)
#else
static void check_state( num, clause_var, state)
   int	num, 
	clause_var, 
	state;
#endif
{
   if (clause_var > num || clause_var < 1)		   /*   if there is no such clause, */
   {    perror("Sorry, clause or variable is invalid.\n"); /*   user gets error message and */
	exit(1);					   /*        the program terminates */
   }
   if (state != 1 && state != 0 && state != -1)		   /* if the state given is invalid */
   {    perror("Sorry, state is invalid.\n");		   /*   user gets error message and */
	exit(1);					   /*        the program terminates */
   }
}


 /** If the used presses on a square in the drawing window
  ** or the message(clause or variable) needs changing due
  ** to a variable change, this function rewrites the updated 
  ** message.
  **/

#if NeedFunctionPrototypes
static void xgsat_redo_messg(void)
#else
static void xgsat_redo_messg()	
#endif
{
   int	i,
	literal;
						 /*   create the string messg to be printed */
   sprintf(messg,"%d: %c  (", first_param, states[clauses[first_param]+1]);	
   for (i = 1; i < message_size - 1; i++)
   {  	literal = lit_of_clause_num( i, first_param);
   	sprintf(messg,"%s%d:%c  ",messg, literal, states[variables[abs( literal)]+1]);
	var_is_displayed[ abs( literal)] = TRUE; /* make sure we know variable is displayed */
   }
   literal = lit_of_clause_num( i, first_param);
   var_is_displayed[ abs( literal)] = TRUE;  /* make sure we know the variable is displayed */
   sprintf(messg,"%s%d:%c)   ",messg, literal, states[variables[abs( literal)]+1]);
}


 /** This function is called from gsat and xgsat_show_all()
  ** to change the state of the clause to the state passed,
  ** and checks if this clause is being displayed so the
  ** display may be updated.
  **/

#if NeedFunctionPrototypes
void xgsat_show_clause_state( int clause, int state, Boolean flush )
#else
void xgsat_show_clause_state( clause, state, flush)  
   int	clause;
   int	state;
   Boolean	flush;
#endif
{
   check_state( num_clauses, clause, state);	/* check if the clause # and state is valid */
   if (clauses[clause] == state)		/* if state is already set, then do nothing */
	return;

   clauses[clause] = state;			    /*       change the state of the clause */
   xgsat_draw(DRAW_CLAUSE, clause, state);	    /* draw the clause in the correct color */

   if (clause == first_param && message_size > 1)   /*  if this clause is being printed out */
   { 	
        /* Do not clear window -- that would cause flashing; instead, use XDrawImageString */
   	xgsat_redo_messg();					     /* get the new message */
     	XDrawImageString( XtDisplay( label_box), XtWindow( label_box), gc[4],
  	             X_Base, Y_Base, messg, strlen(messg));	     /*  write them message */ 
   }

   if (flush == TRUE)			      /* flush is True if this was called from gsat */ 
   	XFlush( XtDisplay( topLevel)); 	      /* flush the events so the drawing will occur */
} 


 /** This function is called from gsat and xgsat_show_all()
  ** to change the state of the variable to the state passed,
  ** and checks if this variable is being displayed so the
  ** display may be updated.
  **/

#if NeedFunctionPrototypes
void	xgsat_show_var_state( int var, int state, Boolean flush )
#else
void xgsat_show_var_state( var, state, flush)		
   int	var,
	state;
   Boolean	flush;
#endif
{  
   int	literal, n;
   char	string[50];

   check_state( num_vars, var, state);	      /*   check if the variable # & state is valid */
   if (variables[var] == state)		      /*   if state is already set, then do nothing */
	return;

   variables[var] = state;		      /* 	   change the state of the variable */
   xgsat_draw(DRAW_VAR, var, state);	      /*     draw the variable in the correct color */

   if (var_is_displayed[ var ])		      /*      if this variable is being printed out */
   {
        /* Do not clear window -- that would cause flashing; instead, use XDrawImageString */
	if (message_size == 1)		      /*     if this is the only variable displayed */
   	    sprintf(messg,"%d: %c   ", first_param, states[variables[first_param]+1]);	
	else				      /* 	    then reprint with correct state */
	    xgsat_redo_messg();		      /* 	     else it's a clause, so redo it */

     	XDrawImageString( XtDisplay( label_box), XtWindow( label_box), gc[4],
  	             X_Base, Y_Base, messg, strlen(messg));	       /* write the message */ 
   }

   if (flush == TRUE) 			      /* flush is True if this was called from gsat */
   	XFlush( XtDisplay( topLevel)); 	      /* flush the events so the drawing will occur */
} 


 /** This function is called from gsat.  It calls the functions
  ** that change the variable and clause states to the state
  ** passed in.
  **/
#if NeedFunctionPrototypes
void xgsat_show_all(
   int	state)
#else
void xgsat_show_all( state)	
   int	state;
#endif
{						
   int	i;

   for (i = 1; i <= num_clauses; i++)		          /*   change all the clause states */
	xgsat_show_clause_state(i, state, FALSE);
   for (i = 1; i <= num_vars; i++)		          /* change all the variable states */
	xgsat_show_var_state( i, state, FALSE);
   XFlush( XtDisplay( topLevel)); 		          /*     Flush all the drawing done */
}


#if NeedFunctionPrototypes
static void draw_flip_number_string(int flip)
#else
static void draw_flip_number_string(flip)
int flip;
#endif
{   
    char string[20];

    sprintf(string,"%7d  ", flip);
    XDrawImageString( XtDisplay(flip_num), XtWindow(flip_num), gc[4],
  	        5, 12, string, strlen(string));
}

#if NeedFunctionPrototypes
static void draw_unsat_number_string(int unsat)
#else
static void draw_unsat_number_string(unsat)
int unsat;
#endif
{   
    char string[20];

    sprintf(string,"%7d  ", unsat);
    XDrawImageString( XtDisplay(unsat_num), XtWindow(unsat_num), gc[4],
  	        5, 12, string, strlen(string));
}


 /** This function updates the number of variables flipped
  ** so far and the number of unsatisfied clauses.
  **/
#if NeedFunctionPrototypes
void xgsat_show_flip_and_unsat(
   int	flip,
   int	unsat)
#else
void xgsat_show_flip_and_unsat( flip, unsat)
   int	flip,
	unsat;
#endif
{
   char	  		string[20];
   static	int	prev_flip = -10;
   static	int  	prev_unsat = -10;

   flip_number = flip;
   unsat_number = unsat;

   if (xgsat_pause_duration == 0 && (flip % 100) != 0 &&
       (xgsat_command == XGSAT_GO || xgsat_command == XGSAT_CONTINUOUS)){
       return;
   }

   if (flip != prev_flip){
       draw_flip_number_string(flip);
       prev_flip = flip;
   }

   if (unsat != prev_unsat){   
       draw_unsat_number_string(unsat);
       prev_unsat = unsat;
   }
}


 /** If the user presses any where in the drawing window to get 
  ** information about a clause or variable, then this function
  ** is called first to clear out the var_is_displayed array.
  **/
#if NeedFunctionPrototypes
static void xgsat_clear(void)
#else
static void xgsat_clear()
#endif
{ 
   int	i;

   for (i = 1;i < nvars;i++)		     /*    clear the var_is_displayed array so that */
	var_is_displayed[i] = FALSE; 	     /* they are all false, & can be re-initialized */
}


 /** If the user pressed the button in the drawing window, then this
  ** function will figure out which clause or variable it was, or if
  ** it wasn't either, and print out the appropriate information
  ** in the window.
  **/
#if NeedFunctionPrototypes
static void xgsat_locate(
   Widget w,
   XEvent *event1,
   String *params,
   Cardinal *num_params)
#else
static void xgsat_locate( w, event1, params, num_params)
   Widget w;
   XEvent *event1;	
   String *params;
   Cardinal *num_params;
#endif
{
   XButtonEvent *event = (XButtonEvent *) event1;      /* typecast event1 as a button event */	
   int	i, literal,
 	x_block,		        /*       the possible column where the user pressed */
	y_block,		        /* possible row for clauses, where the user pressed */
	y_block2,		        /* 		     the possible row for variables */
	parameter1,		        /* 		         the possible clause number */
	parameter2;		        /* 		       the possible variable number */

   x_block = ((*event).x/pix_per_rect) + 1;	
   y_block = (*event).y/pix_per_rect;
   i = (larger == num_clauses)?rects_per_side:rects_per_small_side;
   y_block2 = y_block - i - 1;
   parameter1 = x_block + (y_block * rects_per_side);
   parameter2 = x_block + (y_block2 * rects_per_side);
   xgsat_clear();
   message_size = 0;

   if ((*event).x > (pix_per_rect * rects_per_side) || (parameter1 > num_clauses &&
		(parameter2 <= 0 || parameter2 > num_vars)))
	strcpy( messg, "Invalid choice");			    /*        out of bounds */

   else if (parameter1 <= num_clauses)				    /*        it's a clause */
   {
 	/* Assuming at least one variable per clause */
 	first_param = parameter1;
	message_size = length_of_clause_num( parameter1) + 1;
	xgsat_redo_messg();
   }
   else /* (parameter2 > 0 && parameter2 <= num_vars) */	    /*      it's a variable */
   {
	message_size = 1;
 	first_param = parameter2;
   	sprintf(messg,"%d: %c", parameter2, states[variables[parameter2]+1]);	
	var_is_displayed[ parameter2] = TRUE;
   }

   XClearWindow( XtDisplay( label_box), XtWindow( label_box)); 
   XDrawString( XtDisplay( label_box), XtWindow( label_box), gc[4], /*   put the message in */
  	        X_Base, Y_Base, messg, strlen(messg));		    /* 	  the window */	
   XFlush( XtDisplay( topLevel));				    /* make sure it appears */
}




 /** If the message window was obscured in any way, and then
  ** re-exposed, then this function rewrites the message 
  **/

#if NeedFunctionPrototypes
static void xgsat_rewrite(
   Widget w,
   XEvent *event,
   String *params,
   Cardinal *num_params)
#else
static void xgsat_rewrite( w, event, params, num_params)
   Widget w;
   XEvent *event;
   String *params;
   Cardinal *num_params;
#endif
{
   if ((*event).xexpose.count != 0)		     /* there might be more than one expose */
	return;					     /* event created--we want the last one */
   XDrawString( XtDisplay( button_box), XtWindow( label_box), gc[4],
  	        X_Base, Y_Base, messg, strlen(messg));		      
   
   draw_flip_number_string(flip_number);
   draw_unsat_number_string(unsat_number);
}   


 /** If the drawing window was obscured in any way, and then 
  ** re-exposed, then this function redraws the window
  **/

#if NeedFunctionPrototypes
static void xgsat_redraw(
   Widget w,
   XEvent *event,
   String *params,
   Cardinal *num_params)
#else
static void xgsat_redraw( w, event, params, num_params)
   Widget w;					  
   XEvent *event;
   String *params;
   Cardinal *num_params;
#endif
{
  
   Arg		args[3];
   Dimension	height, width;
   int		i, x_pixels, y_pixels;

   if ((*event).xexpose.count != 0)			/* if more than one expose event is */
	return;					 	/*           then take the last one */
   i = 0;
   XtSetArg( args[i], XtNwidth, &width); i++;
   XtSetArg( args[i], XtNheight, &height); i++;
   XtGetValues( draw_win, args, i);   	    /* get the width & height of the drawing window */
					    /* 		        since it might have changed */
   y_pixels = height/(rects_per_side + rects_per_small_side + 1);
   x_pixels = width/rects_per_side;
   pix_per_rect = (unsigned int) (y_pixels < x_pixels) ? y_pixels:x_pixels;	

   XClearWindow( XtDisplay( draw_win), XtWindow( draw_win));

   /* redraw the Core window, based on the state of the data structure clauses */
   for (i=1;i <= num_clauses;i++) 
	xgsat_draw(DRAW_CLAUSE, i, clauses[i]);	
   for (i=1;i <= num_vars;i++)
	xgsat_draw(DRAW_VAR, i, variables[i]);
   XFlush( XtDisplay( topLevel)); 
}


 /** This function is called by gsat only once to initialize
  ** the variables, and set up the widgets and callback functions.
  **/
#if NeedFunctionPrototypes
void xgsat_init(
   char		**argv,
   int		argc,
   int		nvars,				                 /*	   # variables used */
   int		nclauses,			       		 /* 		  # clauses */
   Boolean	(* work_proc)())		       		 /*     work procedure when */ 
#else
void xgsat_init( argv, argc, nvars, nclauses, work_proc)
   char		**argv;
   int		argc,
		nvars,				                 /*	   # variables used */
		nclauses;			       		 /* 		  # clauses */
   Boolean	(* work_proc)();		       		 /*     work procedure when */ 
#endif
{								 /*           empty event Q */
   int 			i;			                 /*       used as a counter */
   XSetWindowAttributes winattr;	      /*  window attribute for changing the gravity */
   static unsigned int	display_height;       /*  height in pixels of the screen being used */
   static unsigned int	display_width;	      /*   width in pixels of the screen being used */
   static XtActionsRec	actions[] = {					    /* action table */
		{"xgsat_redraw", xgsat_redraw},
		{"xgsat_locate", xgsat_locate},
		{"xgsat_rewrite", xgsat_rewrite},
   };			      
			       /* translation tables for the drawing window & the label_box */
   String	trans  = "<Expose>:		xgsat_redraw()  \n\
			  <Btn1Down>:		xgsat_locate()";   
   String	trans2 = "<Expose>:		xgsat_rewrite()"; 

   states[0] = 'f';				/*   initialize the states to use for messg */
   states[1] = 'u';
   states[2] = 't';
   X_Base = 15;					/* 	      set the location of the messg */
   Y_Base = 23; 
   flip_number = 0;
   unsat_number = 0;
   num_clauses = nclauses;			/* 	set the global variables to be used */
   num_vars = nvars;
   message_size = 0;				/* 	       no message initially printed */
   xgsat_command = XGSAT_STOP;			/* 	 no buttons should be set initially */
   xgsat_work_proc = work_proc;			/* 	   set the work procedure passed in */
   work_proc_installed = FALSE;			/* work procedure hasn't been installed yet */
   clauses = (int *) calloc(nclauses+1,sizeof(int));  	     /* dynamically allocate arrays */
   variables = (int *) calloc(nvars + 1, sizeof(int)); 
   var_is_displayed = (Boolean *) calloc(nvars + 1, sizeof(Boolean)); 

   larger = (num_clauses < num_vars)?num_vars:num_clauses;   /*    find which is larger and */
   smaller = (num_clauses == larger)?num_vars:num_clauses;   /*            which is smaller */
   rects_per_side = (int) sqrt( (double)larger);   /*       get # rectangles/side of larger */
   if (rects_per_side * rects_per_side != larger)  /* if not perfect square, allow for more */
        ++rects_per_side;

   rects_per_small_side = smaller/rects_per_side;   /* get vertical # rectangles of smaller */
   if (rects_per_side * rects_per_small_side != smaller)    /*    if not perfect rectangle, */
        ++rects_per_small_side;				    /* 	        then allow for more */

   for (i = 1;i <= nclauses;i++)			    /*   initialize clause elements */
	clauses[i] = 0;

   for (i = 1;i < nvars;i++)				    /* initialize variable elements */
	variables[i] = 0; 

   xgsat_clear();	  		         /* initialize elements of var_is_displayed */ 

   topLevel = XtVaAppInitialize( &app_context, "XXgsat", NULL, 0,  
                                 &argc, argv, NULL, NULL);

   XtAppAddActions( app_context, actions, XtNumber( actions));

   for (i = 1; i < argc; i++)			    /* look thru the command line arguments */
   {   if (strcmp( argv[i], "-cT") == 0) {	    /*  for different colors to use and set */
	    name[2] = argv[++i];		    /* the names accordingly for T, F, or U */
	    continue;  }
       if (strcmp( argv[i], "-cF") == 0) {
	    name[0] = argv[++i];
	    continue;  }
       if (strcmp( argv[i], "-cU") == 0) {
	    name[1] = argv[++i];
	    continue;  }
   }

   base = XtVaCreateManagedWidget("base", panedWidgetClass, topLevel, 
				   XtNshowGrip, FALSE, NULL);

   box_box = XtVaCreateManagedWidget( "box_box", panedWidgetClass, base,
                                       XtNshowGrip, FALSE,
                                       XtNorientation, XtorientHorizontal,
                                       NULL);

   big_box = XtVaCreateManagedWidget( "big_box", boxWidgetClass, box_box, 
                                       XtNorientation, XtorientHorizontal,
				       XtNborderWidth, 0, 
				       NULL); 

   left_box = XtVaCreateManagedWidget( "left_box", boxWidgetClass, big_box, 
                                        XtNorientation, XtorientVertical,
				        XtNborderWidth, 0, 
					XtNvSpace, 0,
				        NULL); 

   button_box = XtVaCreateManagedWidget( "button_box", boxWidgetClass, left_box, 
                                          XtNorientation, XtorientHorizontal,
				          XtNborderWidth, 0, 
					  XtNvSpace, 0,
				          NULL); 

   message_box = XtVaCreateManagedWidget("message_box", boxWidgetClass, left_box,
					  XtNorientation, XtorientHorizontal,
					  XtNinternalHeight, 0,
				          XtNborderWidth, 0,
				          NULL); 

   flip_label = XtVaCreateManagedWidget("flip_label", labelWidgetClass, message_box,
					 XtNinternalHeight, 0,
				   	 XtNlabel, "Flip:",
					 XtNborderWidth, 0,
					 NULL);

   flip_num = XtVaCreateManagedWidget("flip_num", labelWidgetClass, message_box,
					XtNinternalHeight, 0,
					XtNborderWidth, 0,
					XtNresize, FALSE,
					XtNwidth, 60,
				        XtNlabel, "",
				        XtNtranslations, XtParseTranslationTable( trans2), 
					NULL);

   unsat_label = XtVaCreateManagedWidget("unsat_label", labelWidgetClass, message_box,
					 XtNinternalHeight, 0,
				   	 XtNlabel, "Unsat:",
					 XtNborderWidth, 0,
					 NULL);

   unsat_num = XtVaCreateManagedWidget("unsat_num", labelWidgetClass, message_box,
					XtNinternalHeight, 0,
					XtNborderWidth, 0,
					XtNresize, FALSE,
					XtNwidth, 60,
				        XtNlabel, "",
				        XtNtranslations, XtParseTranslationTable( trans2), 
					NULL);

   label_box = XtVaCreateManagedWidget( "label_box", widgetClass, box_box,
				         XtNtranslations, XtParseTranslationTable( trans2), 
					 XtNwidth, 100, XtNheight, 10, NULL);

   step_button = XtVaCreateManagedWidget( "step_button", commandWidgetClass, button_box,
					   XtNlabel, "Step", NULL);	
   XtAddCallback( step_button, XtNcallback, xgsat_callback, (XtPointer) XGSAT_STEP);

   go_button = XtVaCreateManagedWidget( "go_button", commandWidgetClass, button_box,
					   XtNlabel, "Go", NULL);	
   XtAddCallback( go_button, XtNcallback, xgsat_callback, (XtPointer) XGSAT_GO);
   
   cont_button = XtVaCreateManagedWidget( "cont_button", commandWidgetClass, button_box,
					   XtNlabel, "Continuous", NULL);	
   XtAddCallback( cont_button, XtNcallback, xgsat_callback, (XtPointer) XGSAT_CONTINUOUS);

   stop_button = XtVaCreateManagedWidget( "stop_button", commandWidgetClass, button_box,
					   XtNlabel, "Stop", NULL);	
   XtAddCallback( stop_button, XtNcallback, xgsat_callback, (XtPointer) XGSAT_STOP);

   quit_button = XtVaCreateManagedWidget( "quit_button", commandWidgetClass, button_box,
					   XtNlabel, "Quit", NULL);	
   XtAddCallback( quit_button, XtNcallback, xgsat_callback, (XtPointer) XGSAT_QUIT);

   delay_box = XtVaCreateManagedWidget( "delay_box", boxWidgetClass, big_box,
					 XtNorientation, XtorientVertical,
					 XtNvSpace, 0, XtNhSpace, 2,
					 XtNborderWidth, 0, NULL);

   delay_scroll = XtVaCreateManagedWidget( "delay_scroll", scrollbarWidgetClass, delay_box,
					    XtNorientation, XtorientHorizontal,
					    XtNthickness, 20, XtNlength, 107,  
					    XtNminimumThumb, (Dimension) 12,
					    NULL);
   XtAddCallback( delay_scroll, XtNjumpProc, xgsat_change_delay, delay_scroll);

   delay_label = XtVaCreateManagedWidget( "delay_label", labelWidgetClass, delay_box, 
					   XtNborderWidth, 0, 
					   XtNinternalHeight, 0,
					   XtNlabel, "0    Delay    1", NULL); 

   display_height = XDisplayHeight( XtDisplay( topLevel),	    /* get height of screen */ 
		  	   	    XScreenNumberOfScreen( XtScreen( topLevel)));
   display_width = XDisplayWidth( XtDisplay( topLevel), 	    /*  get width of screen */
			 	  XScreenNumberOfScreen( XtScreen( topLevel)));

   draw_win = XtVaCreateManagedWidget( "draw_win", widgetClass, base,
				        XtNtranslations, XtParseTranslationTable( trans), 
   					XtNwidth, (Dimension) (display_width * .6), 
					XtNheight, (Dimension) (display_height - 100), NULL); 

   xgsat_allocate_colors( topLevel, name, 3, gc );

   XtRealizeWidget( topLevel);		/*          create windows for widgets and map them */

					/*      ForgetGravity for a window means the window */
   winattr.bit_gravity = ForgetGravity;	/* contents are discarded after a size change so an */	
   XChangeWindowAttributes( XtDisplay( draw_win), XtWindow( draw_win),      /* Expose event */
			    CWBitGravity, &winattr);  /* will be created to redraw draw_win */

}
