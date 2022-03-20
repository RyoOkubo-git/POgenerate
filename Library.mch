MACHINE
    Library
SETS
    USERID
VARIABLES
    users, aa
INVARIANT
    users : FIN(USERID) &
    aa : 0..100 --> USERID &
    !xx.(xx : dom(aa) => aa(xx) : ran(aa))
INITIALISATION
    users := {} ||
    aa := USERID
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
            uid := uu
        END
    END
END
