MACHINE
	test3_pst1_3

ABSTRACT_VARIABLES
	users, users_i_arr

INVARIANT
	users : FIN(1 .. 100) &
	users_i_arr : 0 .. 100 - 1 >+> (1 .. 100 \/ {0}) - {0} &
	users = {xx | xx : ran(users_i_arr) & xx : ran(users_i_arr)}

ASSERTIONS
	!uu.(users /= 1 .. 100 & uu : 1 .. 100 & users_i_arr /= (1 .. 100 \/ {0}) & not(uu = 0) & not(uu = 1) => users \/ {uu} = users_i_arr \/ {uu + 2})

INITIALISATION
	users := {} ||
	users_i_arr := {}

END
