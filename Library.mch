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
    uid <-- addUser =
    PRE
        users /= USERID
    THEN
        ANY uu WHERE
            uu : USERID &
            uu /: users
        THEN
            users := users \/ {uu} ||
            uid :: users
        END
    END
END
