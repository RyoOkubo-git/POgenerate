MACHINE
    Library(aa, bb)
SETS
    USERID
VARIABLES
    users
INVARIANT
    users : FIN(USERID)
INITIALISATION
    users := {}
OPERATIONS
    uid <-- addUser(uu) =
    PRE
        users /= USERID &
        uu : USERID
    THEN
        users := users \/ {uu} ||
        uid :: users
    END
END
