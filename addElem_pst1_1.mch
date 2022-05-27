MACHINE
	addElem_pst1_1

ABSTRACT_VARIABLES
	users, users_i_arr

INVARIANT
	users : FIN(1 .. 100) &
	users_i_arr : 0 .. 100 - 1 >+> (1 .. 100 \/ {0}) - {0} &
	users = {xx | xx : ran(users_i_arr) & xx : ran(users_i_arr)}

ASSERTIONS
	!(uu, users_i_ii).(users /= 1 .. 100 & uu : 1 .. 100 & uu : 1 .. 100 \/ {0} & uu /= 0 & uu /: ran(users_i_arr) & users_i_ii : 0 .. 100 - 1 & users_i_ii /: dom(users_i_arr) => users \/ {uu} = users_i_arr <+ {users_i_ii |-> uu})

INITIALISATION
	users := {} ||
	users_i_arr := {}

END
