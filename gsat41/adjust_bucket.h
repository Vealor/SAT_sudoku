#define adjust_bucket(VARPTR) \
{ \
    /* printf("adjusting bucket for var=%d, cmd=%d, diff=%d\n", VARPTR->name, current_max_diff, VARPTR->diff); */\
    if (! is_in(tabu, VARPTR)){ \
	if (flag_hillclimb){ \
	    if (VARPTR->make > 0){ \
		if (! is_in(walk, VARPTR)){ \
		    add_to(walk, VARPTR); \
		} \
	    } \
	    else { \
		if (is_in(walk, VARPTR)){\
		    delete_from(walk, VARPTR);\
		    if (flag_only_unsat){\
			delete_if_in(down, VARPTR);\
			delete_if_in(up, VARPTR);\
			delete_if_in(sideways, VARPTR);\
		    }\
		} \
	    }\
	    if (!flag_only_unsat || VARPTR->make > 0){\
		if (VARPTR->diff > 0){ \
		    if (! is_in(down, VARPTR)){ \
			delete_if_in(up, VARPTR); \
			delete_if_in(sideways, VARPTR); \
			add_to(down, VARPTR); \
		    } \
		} \
		else if (VARPTR->diff == 0){ \
		    if (! is_in(sideways, VARPTR)){ \
			delete_if_in(up, VARPTR); \
			delete_if_in(down, VARPTR); \
			add_to(sideways, VARPTR); \
		    } \
		} \
		else { \
		    if (! is_in(up, VARPTR)){ \
			delete_if_in(down, VARPTR); \
			delete_if_in(sideways, VARPTR); \
			add_to(up, VARPTR); \
		    } \
		} \
	    }\
	}\
	else { \
	    if (VARPTR->make > 0){ \
		if (! is_in(walk, VARPTR)){ \
		    add_to(walk, VARPTR); \
		} \
	    } \
	    else { \
		if (is_in(walk, VARPTR)){\
		    delete_from(walk, VARPTR);\
		    if (flag_only_unsat){\
			delete_if_in(maxdiff, VARPTR);\
		    }\
		} \
	    }\
	    if (!flag_only_unsat || VARPTR->make > 0){\
		if (VARPTR->diff > current_max_diff){ \
		    empty_out(maxdiff); \
		    add_to(maxdiff, VARPTR); \
		    current_max_diff = VARPTR->diff; \
		} \
		else {\
		    if (is_in(maxdiff, VARPTR)){ \
			if (VARPTR->diff < current_max_diff){ \
			    delete_from(maxdiff, VARPTR); \
			} \
		    }\
		    else {\
			if (VARPTR->diff == current_max_diff){ \
			    add_to(maxdiff, VARPTR); \
			} \
		    } \
		} \
	    } \
	}\
    }\
}

