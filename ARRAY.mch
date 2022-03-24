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

    ret <-- test(arg) =
    PRE
        arr /= VALUE
    THEN
        LET xx BE
            xx = arg + 1
        IN
            arr := arg |>> {xx}
        END
    END

    ret2 <-- test2(arg2) =
    PRE
        arr /= VALUE
    THEN
        CASE arg2 OF
            EITHER 0 THEN
                arr := arr \/ {arg2}
            OR 1, 2 THEN
                arr := arr \/ {arg2+1}
            OR 3, 4, 5 THEN
                arr := arr \/ {arg2+2}
            END
        END
        
    END
END
