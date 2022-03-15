exception BMatchError of string

fun eq_lit (RealLiteral x1, RealLiteral x2) = x1 @= x2
  | eq_lit (tk1, tk2) = tk1=tk2

fun areUnifiable NONE NONE = true
  | areUnifiable (SOME _) NONE = true
  | areUnifiable NONE (SOME _) = true
  | areUnifiable (SOME(BT_Power(x1))) (SOME(BT_Power(x2))) = areUnifiable x1 x2
  | areUnifiable (SOME(BT_Pair(x1, y1))) (SOME(BT_Pair(x2, y2))) = (areUnifiable x1 x2) andalso (areUnifiable y1 y2)
  | areUnifiable (SOME(x1)) (SOME(x2)) = x1 = x2


fun exprUnification (ex1 as BE_Leaf(ty1, Var x)) ex2 = SOME([(ex1, ex2)])
  | exprUnification (BE_Leaf(ty1, tk1)) (BE_Leaf(ty2, tk2)) =
    if areUnifiable ty1 ty2 andalso tk1 = tk2 then
      SOME([])
    else
      NONE
  | exprUnification (BE_Node1(ty1, tk1, ex1)) (BE_Node1(ty2, tk2, ex2)) = 
    if areUnifiable ty1 ty2 andalso tk1 = tk2 then
      exprUnification ex1 ex2
    else
      NONE
  | exprUnification (BE_Node2(ty1, tk1, ex11, ex12)) (BE_Node2(ty2, tk2, ex21, ex22)) =
    if areUnifiable ty1 ty2 andalso tk1 = tk2 then
      let
        val next1o = (exprUnification ex11 ex21)
        val next2o = (exprUnification ex12 ex22)
      in
        case (next1o, next2o) of
          (SOME(next1), SOME(next2)) => SOME(next1@next2)
        | _ => NONE
      end
    else
      NONE
  | exprUnification (BE_NodeN(ty1, tk1, exs1)) (BE_NodeN(ty2, tk2, exs2)) =
    if areUnifiable ty1 ty2 andalso tk1 = tk2 andalso (length exs1) = (length exs2) then
      let
        val nextlo = ListPair.map (Utils.uncurry exprUnification) (exs1, exs2)
      in
        if List.all (Utils.neqto NONE) nextlo then
          List.foldl (fn (xo, yo) => SOME((valOf xo)@(valOf yo))) (SOME []) nextlo
        else
          NONE
      end
    else
      NONE
  | exprUnification (BE_Fnc(ty1, x1, y1)) (BE_Fnc(ty2, x2, y2)) =
    if areUnifiable ty1 ty2 then
      let
        val next1o = (exprUnification x1 x2)
        val next2o = (exprUnification y1 y2)
      in
        case (next1o, next2o) of
          (SOME(next1), SOME(next2)) => SOME(next1@next2)
        | _ => NONE
      end
    else
      NONE
  | exprUnification (BE_Img(ty1, x1, y1)) (BE_Img(ty2, x2, y2)) =
    if areUnifiable ty1 ty2 then
      let
        val next1o = (exprUnification x1 x2)
        val next2o = (exprUnification y1 y2)
      in
        case (next1o, next2o) of
          (SOME(next1), SOME(next2)) => SOME(next1@next2)
        | _ => NONE
      end
    else
      NONE
(*ExSet*)(**)
  | exprunification (BE_InSet l1) (BE_InSet l2) = 
  | exprUnification x y = NONE


