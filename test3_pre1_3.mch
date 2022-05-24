MACHINE
	test3_pre1_3(aa, bb)

ABSTRACT_VARIABLES
	users, users_i_arr

INVARIANT
	users : FIN(USERID) &
	users_i_arr : 0 .. 100 - 1 >+> (1 .. 100 \/ {0}) - {0} &
	users = {xx | xx : ran(users_i_arr) & aa : ran(users_i_arr)}

ASSERTIONS
	!uu.(users /= 1 .. 100 & uu : 1 .. 100 => users_i_arr /= (1 .. 100 \/ {0}))

INITIALISATION
	users := {} ||
	users_i_arr := {}

END
