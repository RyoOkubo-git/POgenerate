MACHINE
	test2_pst1_1

ABSTRACT_VARIABLES
	users, users_i_arr

INVARIANT
	users : FIN(1 .. 100) &
	users_i_arr : 0 .. 100 - 1 >+> (1 .. 100 \/ {0}) - {0} &
	users = {xx | xx : ran(users_i_arr) & xx : ran(users_i_arr)}

ASSERTIONS
	!uu.(users /= 1 .. 100 & uu : 1 .. 100 & users_i_arr /= (1 .. 100 \/ {0}) & uu = 0 => users \/ {uu} = users_i_arr \/ {uu})

INITIALISATION
	users := {} ||
	users_i_arr := {}

END
