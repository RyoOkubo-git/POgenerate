MACHINE
    ARRAY(VALUE, empty, Size)
CONSTRAINTS
    Size : NAT1 &
    empty : VALUE
VARIABLES
    arr
INVARIANT
    arr : 0..Size-1 >+> (VALUE - {empty})
INITIALISATION
    arr := {}
OPERATIONS
    idx <-- addElem(ee) =
    PRE
        ee : VALUE &
        ee /= empty &
        ee /: ran(arr)
    THEN
        ANY ii WHERE
            ii : 0..Size-1 &
            ii /: dom(arr)
        THEN
            arr(ii) := ee ||
            idx :(idx:dom(arr))
        END
    END;
    
    status <-- memElem(ee) =
    PRE
        ee : VALUE
    THEN
        status := bool(ee : ran(arr))
    END
END
