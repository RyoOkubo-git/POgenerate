MACHINE
	Library

SETS
	USERID

ABSTRACT_VARIABLES
	users

INVARIANT
	users : FIN(USERID)

INITIALISATION
	users := {}

OPERATIONS
	uid <-- addUser =
		PRE
			users /= USERID
		THEN
			ANY
				uu
			WHERE
				uu : USERID &
				uu /: users
			THEN
				users := users \/ {uu} ||
				uid := uu
			END
		END
END
