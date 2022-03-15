signature TYPEINFERENCE =
sig
  exception BTypeError of string
  val type_component : BComponent -> BComponent
  val type_expr : BExpr -> BExpr
end

structure TypeInference :> TYPEINFERENCE =
struct
  exception BTypeError of string
  fun typeOf (BE_Leaf(t, _)) = t 
    | typeOf (BE_Node1(t, _, _)) = t 
    | typeOf (BE_Fnc(t,_,_)) = t 
    | typeOf (BE_Img(t,_,_)) = t
    | typeOf (BE_NodeN(t,_,_)) =t
    | typeOf (BE_Bool _) = SOME(BT_Predicate)
    | typeOf (BE_Node2(t,_,_,_))=t 
    | typeOf (BE_ExSet(t, _)) = t 
    | typeOf (BE_InSet(t,_,_)) = t 
    | typeOf (BE_Seq(t, _)) = t 
    | typeOf (BE_ForAny _) = SOME(BT_Predicate)
    | typeOf (BE_Exists _) = SOME(BT_Predicate)
    | typeOf (BE_Lambda(t ,_,_,_)) = t
    | typeOf (BE_Sigma(t ,_,_,_)) = t
    | typeOf (BE_Pi(t ,_,_,_)) = t
    | typeOf (BE_Inter(t ,_,_,_)) = t
    | typeOf (BE_Union(t ,_,_,_)) = t
    | typeOf (BE_Struct(t,_)) = t
    | typeOf (BE_Rec(t,_)) = t
    | typeOf (BE_RcAc(t,_,_)) = t
  and
    setType t x = setType_opt (SOME t) x
  and
    setType_opt   t (BE_Leaf      (_, x))           = (BE_Leaf      (t, x)) 
    | setType_opt t (BE_Node1     (_, x1, x2))      = (BE_Node1     (t, x1, x2))
    | setType_opt t (BE_Fnc   (_, x1, x2))      = (BE_Fnc   (t, x1, x2))
    | setType_opt t (BE_Img (_, x1, x2))      = (BE_Img (t, x1, x2))
    | setType_opt t (BE_NodeN     (_, x1, x2))      = (BE_NodeN     (t, x1, x2))
    | setType_opt t (BE_Node2     (_, x1, x2, x3))  = (BE_Node2     (t, x1, x2, x3)) 
    | setType_opt t (BE_ExSet     (_, x))           = (BE_ExSet     (t, x)) 
    | setType_opt t (BE_InSet     (_, x1, x2))      = (BE_InSet     (t, x1, x2))
    | setType_opt t (BE_Seq       (_, x))           = (BE_Seq       (t, x))
    | setType_opt t (BE_Lambda    (_, x1, x2, x3))  = (BE_Lambda    (t, x1, x2, x3))
    | setType_opt t (BE_Sigma     (_, x1, x2, x3))  = (BE_Sigma     (t, x1, x2, x3))
    | setType_opt t (BE_Pi        (_, x1, x2, x3))  = (BE_Pi        (t, x1, x2, x3))
    | setType_opt t (BE_Inter     (_, x1, x2, x3))  = (BE_Inter     (t, x1, x2, x3))
    | setType_opt t (BE_Union     (_, x1, x2, x3))  = (BE_Union     (t, x1, x2, x3))
    | setType_opt t (BE_Struct    (_, x))           = (BE_Struct    (t, x))
    | setType_opt t (BE_Rec       (_, x))           = (BE_Rec       (t, x))
    | setType_opt t x = x
  and
    setEnv env expr = 
      let
        fun setEnv_sub (BE_Leaf(to, Var x)) =
            let
              val tinfo_opt = List.find (fn (v,to)=>(v=Var x)) env
            in
              case tinfo_opt of
                NONE => BE_Leaf(to, Var x)
              | SOME(_, to1) => BE_Leaf(typeUnification to to1, Var x)
            end
          | setEnv_sub x = x
      in
        AST.applyExprTree setEnv_sub expr
      end
  and
    getEnv [] expr = []
    | getEnv ((Var x, to)::env) expr =
      let
        val next = getEnv env expr
        val es = AST.findExprs (fn y => case y of BE_Leaf(SOME(t),Var z)=>x=z | _ => false) expr
      in
        if es = [] then
          (Var x, to)::next
        else
          (Var x, (List.foldl (Utils.uncurry typeUnification) to (List.map typeOf es)))::next
      end
    | getEnv _ _ = raise BTypeError ""
  and
    type_constraints parameters constraints_opt clauses = 
      (case (parameters, constraints_opt) of
          ([], NONE) => ([], clauses)
        | ([], SOME(_)) => raise BTypeError "0 machine parameter with constraints clause"
        | (param, NONE) => if List.all (fn vx => case vx of (Var [x]) => Utils.isAllUpper x | _ => raise BTypeError "") parameters then
            let
              val env = List.map (fn vx => case vx of Var [x] => (Var [x], SOME(BT_Power(SOME(BT_Deferred(x))))) | _ => raise BTypeError "") param
            in
              (env, clauses)
            end
          else
            raise BTypeError "scalar parameters without constraints"
        | (param, SOME(clauseName,BC_CONSTRAINTS(BP_list e))) => 
          let
            val env1 = List.map (fn vx => case vx of Var [x] => if Utils.isAllUpper x then (Var [x], SOME(BT_Power(SOME(BT_Deferred(x))))) else (Var [x], NONE) | _ => raise BTypeError "") param
            val ne = List.map (fn x => type_exprTree (setEnv env1 x)) e
            val env2 = getEnvFromPredicate env1 ne
            val ncls = (clauseName,BC_CONSTRAINTS(BP_list ne))::(List.filter (fn (s,_)=>s<>clauseName) clauses)
          in
            (env2, ncls)
          end
        | _ => raise BTypeError ""
      )
  and
    type_properties env NONE clauses = (env, clauses)
    | type_properties [] (SOME(_)) _ = raise BTypeError "properties clause with no constants to be typed"
    | type_properties env (SOME(clauseName,BC_PROPERTIES(BP_list e))) clauses =
      let
        fun updateEnv (oldenv, oldexpr) =
            let
              val nexpr = List.map (fn x => type_exprTree (setEnv oldenv x)) oldexpr
              val nenv = getEnvFromPredicate oldenv nexpr
            in
              (nenv, nexpr)
            end
        val (env1, e1) = Utils.repeatApply updateEnv (env, e)
        val ncls = (clauseName,BC_PROPERTIES(BP_list e1))::(List.filter (fn (s,_)=>s<>clauseName) clauses)
      in
        (env1, ncls)
      end
    | type_properties _ _ _ = raise BTypeError ""
  and
    type_invariant env NONE clauses = (env, clauses)
    | type_invariant env (SOME(clauseName,BC_INVARIANT(BP_list e))) clauses =
      let
        fun updateEnv (oldenv, oldexpr) =
            let
              val nexpr = List.map (fn x => type_exprTree (setEnv oldenv x)) oldexpr
              val nenv = getEnvFromPredicate oldenv nexpr
            in
              (nenv, nexpr)
            end
        val (env1, e1) = Utils.repeatApply updateEnv (env, e)
        val ncls = (clauseName,BC_INVARIANT(BP_list e1))::(List.filter (fn (s,_)=>s<>clauseName) clauses)
      in
        (env1, ncls)
      end
    | type_invariant _ _ _ = raise BTypeError ""
  and
    type_initialisation env NONE clauses = clauses
    | type_initialisation env (SOME(clauseName,BC_INITIALISATION(s))) clauses = 
      let
        val ns = type_subsTree env s
      in
        (clauseName,BC_INITIALISATION(ns))::(List.filter (fn (s,_)=>s<>clauseName) clauses)
      end
    | type_initialisation _ _ _ = raise BTypeError ""
  and
    type_operations env NONE clauses = clauses
    | type_operations env (SOME(clauseName,BC_OPERATIONS(ops))) clauses = 
      (clauseName,BC_OPERATIONS(List.map (type_operation env) ops))::(List.filter (fn (s,_)=>s<>clauseName) clauses)
    | type_operations _ _ _ = raise BTypeError ""
  and
    type_operation env (BOp(name, outputs, inputs, s)) =
      let
        val inenv = List.map (fn token => (token, NONE:BType option)) inputs
        val outenv = List.map (fn token => (token, NONE:BType option)) outputs
      in
        BOp(name, outputs, inputs, type_subsTree (outenv@inenv@env) s)
      end
  and
    type_assertions env NONE clauses = clauses
    | type_assertions env (SOME(clauseName,BC_ASSERTIONS(BP_list e))) clauses =
      let
        val ne = List.map (fn x => type_exprTree (setEnv env x)) e
      in
        (clauseName, BC_ASSERTIONS(BP_list ne))::(List.filter (fn (s,_) => s <> clauseName) clauses)
      end
    | type_assertions _ _ _ = raise BTypeError ""
  and
    type_includes env NONE clauses = clauses
    | type_includes env (SOME(clauseName, BC_INCLUDES(l))) clauses = (clauseName, BC_INCLUDES(type_machinelist env l))::(List.filter (fn (s,_) => s <> clauseName) clauses)
    | type_includes _ _ _ = raise BTypeError ""
  and
    type_extends env NONE clauses = clauses
    | type_extends env (SOME(clauseName, BC_EXTENDS(l))) clauses = (clauseName, BC_EXTENDS(type_machinelist env l))::(List.filter (fn (s,_)=>s<>clauseName) clauses)
    | type_extends _ _ _ = raise BTypeError ""
  and
    type_machinelist env [] = []
    | type_machinelist env ((BMchInst(t, []))::ms) = (BMchInst(t, []))::(type_machinelist env ms)
    | type_machinelist env ((BMchInst(t, l))::ms) = (BMchInst(t, List.map (fn e => (Utils.repeatApply type_expr) (setEnv env e)) l))::(type_machinelist env ms)
  and
    type_component (BMch(machinename, parameters, clauses)) = 
      let
        fun eqto_clause s1 (s2, _) = s1 = s2
        val constraints_opt =       List.find (eqto_clause "CONSTRAINTS") clauses
        val sets_opt =              List.find (eqto_clause "SETS") clauses
        val includes_opt =          List.find (eqto_clause "INCLUDES") clauses
        val extends_opt =           List.find (eqto_clause "EXTENDS") clauses
        val aconstants_opt =        List.find (eqto_clause "ABSTRACT_CONSTANTS") clauses
        val cconstants_opt =        List.find (eqto_clause "CONCRETE_CONSTANTS") clauses
        val properties_opt =        List.find (eqto_clause "PROPERTIES") clauses
        val avariables_opt =        List.find (eqto_clause "ABSTRACT_VARIABLES") clauses
        val cvariables_opt =        List.find (eqto_clause "CONCRETE_VARIABLES") clauses
        val invariant_opt =         List.find (eqto_clause "INVARIANT") clauses
        val assertions_opt =        List.find (eqto_clause "ASSERTIONS") clauses
        val initialisation_opt =    List.find (eqto_clause "INITIALISATION") clauses
        val operations_opt =        List.find (eqto_clause "OPERATIONS") clauses
        val (env_constraints, c1) = type_constraints parameters constraints_opt clauses
        val env_sets = (
            case sets_opt of
              NONE => []
            | SOME(_,BC_SETS(ts)) => List.map (fn btd => case btd of (BT_Deferred(s)) =>(Var [s],SOME(BT_Power(SOME(BT_Deferred(s))))) | _ => raise BTypeError "") ts
            | _ => raise BTypeError ""
          )
        val env_aconstants = (
            case aconstants_opt of
              NONE => []
            | SOME(_,BC_ACONSTANTS(vs)) => List.map (fn vx => case vx of (Var x) => (Var x, NONE : BType option) | _ => raise BTypeError "") vs
            | _ => raise BTypeError ""
          )
        val env_cconstants = (
            case cconstants_opt of
              NONE => []
            | SOME(_,BC_CCONSTANTS(vs)) => List.map (fn vx => case vx of (Var x) => (Var x, NONE : BType option) | _ => raise BTypeError "") vs
            | _ => raise BTypeError ""
          ) 
        val (env_properties, c2) = type_properties (env_sets@env_aconstants@env_cconstants) properties_opt c1
        val c3 = type_includes env_properties includes_opt c2
        val c4 = type_extends env_properties extends_opt c3
        val env_avariables = (
            case avariables_opt of
              NONE => []
            | SOME(_,BC_AVARIABLES(vs)) => List.map (fn vx => case vx of (Var x)=>(Var x, NONE : BType option) | _ => raise BTypeError "") vs
            | _ => raise BTypeError ""
          ) 
        val env_cvariables = (
            case cvariables_opt of
              NONE => []
            | SOME(_,BC_CVARIABLES(vs)) => List.map (fn vx => case vx of (Var x)=>(Var x, NONE : BType option)| _ => raise BTypeError "") vs
            | _ => raise BTypeError ""
          ) 
        val (env_invariant, c5) = type_invariant (env_constraints@env_properties@env_avariables@env_cvariables) invariant_opt c4
        val c6 = type_assertions env_invariant assertions_opt c5
        val c7 = type_initialisation env_invariant initialisation_opt c6
        val c8 = type_operations env_invariant operations_opt c7
        (*val c9 = convertClausesCNF c8 *)(*各Predicateの連言標準形への変換*)(*プリミティブ化で=>の変換等と一緒にやる*)
      in
        BMch(machinename, parameters, c8)
      end
    | type_component _ = raise BTypeError "input is not an abstract machine"
    (*
  and
    convertClausesCNF clauses = 
      let
        fun
          convCNF (BE_Node2(_, Keyword "And", e1, e2)) = (convCNF e1)@(convCNF e2)
          | convCNF expr = [convCNF_e expr]
        and
          convCNF_e = x
        and
          convCNF_s (BS_Block(s)) = BS_Block(convCNF_s s)
          | convCNF_s (BS_Precondition(BP_list [p], s)) = BS_Precondition(BP_list(convCNF p), convCNF_s s)
          | convCNF_s (BS_Identity) = BS_Identity
          | convCNF_s (BS_Assertion(BP_list [p], s)) = BS_Assertion(BP_list(convCNF p), convCNF_s s)
          | convCNF_s (BS_Choice(l)) = BS_Choice(List.map convCNF_s l)
          | convCNF_s (BS_If(l)) = BS_If(List.map (fn (BP_list [p], s) => (BP_list(convCNF p), convCNF_s s)) l)
          | convCNF_s (BS_Select(l)) = BS_Select(List.map (fn (BP_list [p], s) => (BP_list(convCNF p), convCNF_s s)) l)
          | convCNF_s (BS_Case(ex, l)) = BS_Case(convCNF_e ex, List.map (fn (e, s) => (e, convCNF_s s)) l)
          | convCNF_s (BS_Any(l, BP_list [p], s)) = BS_Any(l, BP_list(convCNF p), convCNF_s s)
          | convCNF_s (BS_Let(l, s)) = BS_Let(List.map (fn (n, e) => (n, convCNF_e e)) l, convCNF_s s)
          | convCNF_s (BS_BecomesElt(e1, e2)) = BS_BecomesElt(convCNF_e e1, convCNF_e e2)
          | convCNF_s (BS_BecomesSuchThat(l, BP_list [p])) = BS_BecomesSuchThat(List.map convCNF_e l, BP_list( convCNF p))
          | convCNF_s (BS_Call(l1, name, l2)) = BS_Call(l1, name, List.map convCNF_e l2)
          | convCNF_s (BS_BecomesEqual(e1, e2)) = BS_BecomesEqual(convCNF_e e1, convCNF_e e2)
          | convCNF_s (BS_Simultaneous l) = BS_Simultaneous(List.map convCNF_s l)
          | convCNF_s (BS_BecomesEqual_list(_)) = raise BTypeError "a substitution like \"a,b := c,d\" is detected in typing phase"
          | convCNF_s _ => raise BTypeError ""

        and
          convCNF_c (s, BC_CONSTRAINTS(BP_list [expr])) = (s, BC_CONSTRAINTS(BP_list (convCNF expr)))
          | convCNF_c (s, BC_PROPERTIES(BP_list [expr])) = (s, BC_PROPERTIES(BP_list (convCNF expr)))
          | convCNF_c (s, BC_INVARIANT(BP_list [expr])) = (s, BC_INVARIANT(BP_list (convCNF expr)))
          | convCNF_c (s, BC_ASSERTIONS(BP_list [expr])) = (s, BC_ASSERTIONS(BP_list (convCNF expr)))
          | convCNF_c (s, BC_INITIALISATION(subs)) = (s, BC_INITIALISATION(convCNF_s subs))
          | convCNF_c (s, BC_OPERATIONS(l)) =
            let
              val f = fn (BOp(name,outputs,inputs,subs)) => BOp(name,outputs,inputs,convCNF_s subs)
            in
              List.map f l
            end
          | convCNF_c x = x
      in  
        List.map convCNF_c clauses
      end
*)
  and
    type_subsTree env (BS_Block(s)) = (BS_Block(type_subsTree env s))
    | type_subsTree env (BS_Precondition(BP_list ps, s)) = 
      let
        fun updateEnv (oldenv, oldp) =
            let
              val np = List.map (fn x => type_exprTree (setEnv oldenv x)) oldp
              val nenv = getEnvFromPredicate oldenv np
            in
              (nenv, np)
            end
        val (env1, ps1) = Utils.repeatApply updateEnv (env, ps)
        val s1 = type_subsTree env1 s
      in
        BS_Precondition(BP_list ps1, s1)
      end
    | type_subsTree env (BS_Assertion(BP_list ps, s)) = 
      let
        fun updateEnv (oldenv, oldp) =
            let
              val np = List.map (fn x => type_exprTree (setEnv oldenv x)) oldp
              val nenv = getEnvFromPredicate oldenv np
            in
              (nenv, np)
            end
        val (env1, p1) = Utils.repeatApply updateEnv (env, ps)
        val s1 = type_subsTree env1 s
      in
        BS_Assertion(BP_list p1, s1)
      end
    | type_subsTree env (BS_Choice l) = BS_Choice (List.map (type_subsTree env) l)
    | type_subsTree env (BS_If l) = BS_If(List.map (fn (p,s) => (type_predicateTree_list env p, type_subsTree env s)) l)
    | type_subsTree env (BS_Select l) = BS_If(List.map (fn (p,s) => (type_predicateTree_list env p, type_subsTree env s)) l)
    | type_subsTree env (BS_Case(ex, l)) = BS_Case(type_exprTree (setEnv env ex), List.map (fn (es, s)=>(List.map (fn x => type_exprTree (setEnv env x)) es, type_subsTree env s)) l)
    | type_subsTree env (BS_Any(vs, BP_list ps, s)) = 
      let
        val env1 = List.map (fn x => (x, NONE)) vs
        fun updateEnv (oldenv, oldp) = 
            let
              val np = List.map (fn x => type_exprTree (setEnv oldenv x)) oldp
              val nenv = getEnvFromPredicate oldenv np
            in
              (nenv, np)
            end
        val (env2, p1) = Utils.repeatApply updateEnv (env1@env, ps)
        val s1 = type_subsTree env2 s
      in
        BS_Any(vs, BP_list p1, s1)
      end
    | type_subsTree env (BS_Let(l, s)) = 
      let
        fun updateEnv (oldenv, oldl) =
            let
              val nl = List.map (fn (i, e) => (i, type_exprTree (setEnv oldenv e))) l
              val lenv = List.map (fn (i, e) => (Var [i], typeOf e)) l
              fun addEnv en [] = en
                | addEnv en ((v,t)::rest) =
                  let
                    val e_opt = List.find (fn x => case x of (vv,tt) => (vv=v)) en
                  in
                    case e_opt of
                      NONE => addEnv en rest
                    | SOME(vv,tt) => 
                      let
                        val nt = typeUnification t tt
                      in
                        if nt = t then
                          addEnv en rest
                        else
                          let
                            val nen = (v,nt)::(List.filter (fn x => (case x of (vv, tt) => vv<>v)) en)
                          in
                            addEnv nen rest
                          end
                      end 
                  end
              val nenv = addEnv oldenv lenv
            in
              (nenv, nl)
            end
        val (env1, l1) = Utils.repeatApply updateEnv (env, l)
        val s1 = type_subsTree env1 s
      in
        BS_Let(l1, s1)
      end    
    
    | type_subsTree env (BS_BecomesElt(x, y)) =
      let
        fun subsTree_sub (xold, yold) =
            let
              val nx = type_exprTree (setEnv env xold)
              val ny = type_exprTree (setEnv env yold)
              val xto = typeOf nx
              val yto = typeOf ny
              val nxto = (
                  case yto of
                    SOME(BT_Power(xto1)) => typeUnification xto xto1
                  | NONE => xto
                  | _ => raise BTypeError ""
                )
              val nyto = SOME(BT_Power(nxto))
            in
              (setType_opt nxto nx, setType_opt nyto ny)
            end
      in
        BS_BecomesElt(Utils.repeatApply subsTree_sub (x,y))
      end
    | type_subsTree env (BS_BecomesSuchThat(es, p)) = BS_BecomesSuchThat(List.map (fn e => type_exprTree (setEnv env e)) es, type_predicateTree_list env p)
    | type_subsTree env (BS_BecomesEqual(x, y)) = 
      let
        fun subsTree_sub (xold, yold) =
            let
              val nx = type_exprTree (setEnv env xold)
              val ny = type_exprTree (setEnv env yold)
              val xto = typeOf nx
              val yto = typeOf ny
              val nt = typeUnification xto yto
            in
              (setType_opt nt nx, setType_opt nt ny)
            end
        val (x1, y1) = Utils.repeatApply subsTree_sub (x, y)
      in
        BS_BecomesEqual(x1, y1)
      end
    | type_subsTree env (BS_Simultaneous l) = BS_Simultaneous(List.map (type_subsTree env) l)
    | type_subsTree _ x = x
  and
    type_predicateTree_list env (BP_list elst) = BP_list (List.map (fn x => type_exprTree (setEnv env x)) elst)
  and
    type_exprTree et = Utils.repeatApply (AST.applyExprTree type_expr) et
  and
    typeUnification NONE NONE = NONE
    | typeUnification NONE (SOME x) = SOME x
    | typeUnification (SOME x) NONE = SOME x
    | typeUnification (SOME(BT_Power(x))) (SOME(BT_Power(y))) = (SOME(BT_Power(typeUnification x y)))
    | typeUnification (SOME(BT_Pair(x1, x2))) (SOME(BT_Pair(y1, y2))) = (SOME(BT_Pair(typeUnification x1 y1, typeUnification x2 y2)))
    | typeUnification (SOME(BT_Struct(l1))) (SOME(BT_Struct(l2))) = 
      let
        val l12 = ListPair.zip (l1,l2)
        val nl = List.map (fn ((t1,s1),(t2,s2)) => if s1 = s2 then (valOf(typeUnification (SOME t1) (SOME t2)), s1) else raise BTypeError "") l12
      in
        SOME(BT_Struct(nl))
      end
    | typeUnification (SOME x) (SOME y) = if x=y then (SOME x) else raise BTypeError ""
  and
    type_expr (ex as BE_RcAc(NONE, rcd, x)) = (* a -> a'b *)
      let
        val rct = typeOf rcd
      in
        (case rct of
            NONE => ex
          | SOME(BT_Struct(flst)) => 
            let
              val t = #1(valOf(List.find (fn y => (#2(y))=x) flst))
            in
              BE_RcAc(SOME t, rcd, x)
            end
          | _ => raise BTypeError ""
        )
      end
    | type_expr (ex as BE_Node1(yto, (Keyword "Reverse"), x)) = (* a~ *)
      let
        val (na, nb) =
          (case (typeOf x, yto) of
              (SOME(BT_Power(SOME(BT_Pair(a1, b1)))),SOME(BT_Power(SOME(BT_Pair(b2,a2))))) => 
                (typeUnification a1 a2, typeUnification b1 b2)
            | ((SOME(BT_Power(SOME(BT_Pair(a1, b1))))), _) => (a1, b1)
            | (_, (SOME(BT_Power(SOME(BT_Pair(b2, a2)))))) => (a2, b2)
            | _ => (NONE, NONE))
        val (nxt, nyt) = (BT_Power(SOME(BT_Pair(na, nb))), BT_Power(SOME(BT_Pair(nb, na))))
      in
        BE_Node1(SOME nyt, (Keyword "Reverse"), setType nxt x)
      end
    
    | type_expr (ex as BE_Node1(xto, Keyword "Minus", y)) = (* -a *)
      let
        val t = typeUnification xto (typeOf y)
      in
        BE_Node1(t, Keyword "Minus", setType_opt t y)
      end
    
    | type_expr (BE_Node2(_, Keyword "Power", x, y)) = (* a**b *)
      BE_Node2(SOME BT_Integer, Keyword "Power", setType BT_Integer x, setType BT_Integer y)
  
    | type_expr (BE_Node2(_, Keyword "Slash", x, y)) = (* a/b *)
      BE_Node2(SOME BT_Integer, Keyword "Slash", setType BT_Integer x, setType BT_Integer y)
    | type_expr (BE_Node2(_, Reserved "mod", x, y)) = (* a mod b *)
      BE_Node2(SOME BT_Integer, Reserved "mod", setType BT_Integer x, setType BT_Integer y)
    
    | type_expr (ex as BE_Node2(zto, Keyword "Asta", x, y)) = (* a*b *)(*集合・スカラー両方に対応*)
      let
        val xto = typeOf x
        val yto = typeOf y
        val (nxto, nyto, nzto) =
          (
            case (xto, yto, zto) of 
              (NONE, NONE, NONE) => (NONE, NONE, NONE)
            | (SOME(BT_Power(xt)), SOME(BT_Power(yt)), SOME(BT_Power(SOME(BT_Pair(zt1, zt2))))) =>
              let
                val t1 = typeUnification xt zt1
                val t2 = typeUnification yt zt2
              in
                (SOME(BT_Power(t1)), SOME(BT_Power(t2)), SOME(BT_Power(SOME(BT_Pair(t1, t2)))))
              end
            | (_, SOME(BT_Power(yt)), SOME(BT_Power(SOME(BT_Pair(zt1, zt2))))) =>
              let
                val t1 = zt1
                val t2 = typeUnification yt zt2
              in
                (SOME(BT_Power(t1)), SOME(BT_Power(t2)), SOME(BT_Power(SOME(BT_Pair(t1, t2)))))
              end
            | (SOME(BT_Power(xt)), _, SOME(BT_Power(SOME(BT_Pair(zt1, zt2))))) =>
              let
                val t1 = typeUnification xt zt1
                val t2 = zt2
              in
                (SOME(BT_Power(t1)), SOME(BT_Power(t2)), SOME(BT_Power(SOME(BT_Pair(t1, t2)))))
              end
            | (SOME(BT_Power(xt)), SOME(BT_Power(yt)), _) =>
              let
                val t1 = xt
                val t2 = yt
              in
                (SOME(BT_Power(t1)), SOME(BT_Power(t2)), SOME(BT_Power(SOME(BT_Pair(t1, t2)))))
              end
            | (SOME(BT_Power(xt)), _, _) =>
              let
                val t1 = xt
                val t2 = NONE
              in
                (SOME(BT_Power(t1)), SOME(BT_Power(t2)), SOME(BT_Power(SOME(BT_Pair(t1, t2)))))
              end
            | (_, SOME(BT_Power(yt)), _) =>
              let
                val t1 = NONE
                val t2 = yt
              in
                (SOME(BT_Power(t1)), SOME(BT_Power(t2)), SOME(BT_Power(SOME(BT_Pair(t1, t2)))))
              end
            | (_, _, SOME(BT_Power(SOME(BT_Pair(zt1, zt2))))) =>
              let
                val t1 = zt1
                val t2 = zt2
              in
                (SOME(BT_Power(t1)), SOME(BT_Power(t2)), SOME(BT_Power(SOME(BT_Pair(t1, t2)))))
              end
            | (_, _, SOME(BT_Power(_))) =>
              let
                val t1 = NONE
                val t2 = NONE
              in
                (SOME(BT_Power(t1)), SOME(BT_Power(t2)), SOME(BT_Power(SOME(BT_Pair(t1, t2)))))
              end
            | (SOME xt, _, _) => (SOME xt, SOME xt, SOME xt)
            | (_, SOME yt, _) => (SOME yt, SOME yt, SOME yt)
            | (_, _, SOME zt) => (SOME zt, SOME zt, SOME zt)
          )
      in
        BE_Node2(nzto, Keyword "Asta", setType_opt nxto x, setType_opt nyto y)
      end
    
    | type_expr (BE_Node2(_, Keyword "Interval", x, y)) = 
      (BE_Node2(SOME(BT_Power(SOME(BT_Integer))), Keyword "Interval", setType BT_Integer x, setType BT_Integer y))
    | type_expr (ex as BE_Node2(_, Keyword "NBelong", x, y)) =
      let
        val xto = typeOf x
        val yto = typeOf y
        val nxto =
          (case (xto, yto) of
              (NONE, NONE) => NONE
            | (xto2, SOME(BT_Power yto2)) => typeUnification xto2 yto2
            | (SOME xt, NONE) => SOME xt
            | _ => raise BTypeError "")
      in
        BE_Node2(SOME BT_Predicate, Keyword "NBelong", setType_opt nxto x, setType_opt (SOME(BT_Power(nxto))) y)
      end
    | type_expr (ex as BE_Node2(_, Keyword "Coron", x, y)) =
      let
        val xto = typeOf x
        val yto = typeOf y
        val nxto =
          (case (xto, yto) of
              (NONE, NONE) => NONE
            | (xto2, SOME(BT_Power yto2)) => typeUnification xto2 yto2
            | (SOME xt, NONE) => SOME xt
            | _ => raise BTypeError "")
      in
        BE_Node2(SOME BT_Predicate, Keyword "Coron", setType_opt nxto x, setType_opt (SOME(BT_Power(nxto))) y)
      end
    
    | type_expr (BE_Node2(_, Reserved "or", x, y)) = 
      BE_Node2(SOME BT_Predicate, Reserved "or", setType BT_Predicate x, setType BT_Predicate y)
    | type_expr (BE_Node2(_, Keyword "And", x, y)) = 
      BE_Node2(SOME BT_Predicate, Keyword "And", setType BT_Predicate x, setType BT_Predicate y)
    | type_expr (BE_Node2(_, Keyword "Implies", x, y)) = 
      BE_Node2(SOME BT_Predicate, Keyword "Implies", setType BT_Predicate x, setType BT_Predicate y)
    | type_expr (BE_Node2(_, Keyword "Equiv", x, y)) = 
      BE_Node2(SOME BT_Predicate, Keyword "Equiv", setType BT_Predicate x, setType BT_Predicate y)
    
    | type_expr (BE_Node2(to, Keyword "Plus", x, y)) = kw_xxx (x, y, to, "Plus")
    | type_expr (BE_Node2(to, Keyword "Minus", x, y)) = kw_xxx (x, y, to, "Minus")
    | type_expr (BE_Node2(to, Keyword "Overwrite", x, y)) = kw_xxx (x, y, to, "Overwrite")
    | type_expr (BE_Node2(to, Keyword "Inter", x, y)) = kw_xxx (x, y, to, "Inter")
    | type_expr (BE_Node2(to, Keyword "Union", x, y)) = kw_xxx (x, y, to, "Union")
    | type_expr (BE_Node2(to, Keyword "ConcatSeq", x, y)) = kw_xxx (x, y, to, "ConcatSeq")
    
    | type_expr (BE_Node2(to, Keyword "Comma", x, y)) = type_expr (BE_Node2(to, Keyword "Maplet", x, y))(*,を|->に変換*)
    | type_expr (ex as BE_Node2(zto, Keyword "Maplet", x, y)) =
      let
        val xto = typeOf x
        val yto = typeOf y
        val (nxto, nyto) = 
          (case zto of
              SOME(BT_Pair(zto1, zto2)) => 
                (typeUnification xto zto1, typeUnification yto zto2)
            | NONE => (xto, yto)
            | _ => raise BTypeError "")
      in
        BE_Node2(SOME (BT_Pair(nxto, nyto)), Keyword "Maplet", setType_opt nxto x, setType_opt nyto y)
      end

    | type_expr (BE_Node2(_, Keyword "NEq", x, y)) = kw_xxp (x, y, "NEq")
    | type_expr (BE_Node2(_, Keyword "GEq", x, y)) = kw_xxp (x, y, "GEq")
    | type_expr (BE_Node2(_, Keyword "LEq", x, y)) = kw_xxp (x, y, "LEq")
    | type_expr (BE_Node2(_, Keyword "Gt", x, y)) = kw_xxp (x, y, "Gt")
    | type_expr (BE_Node2(_, Keyword "Lt", x, y)) = kw_xxp (x, y, "Lt")
    | type_expr (BE_Node2(_, Keyword "Inclusion", x, y)) = kw_xxp (x, y, "Inclusion")
    | type_expr (BE_Node2(_, Keyword "SNInc", x, y)) = kw_xxp (x, y, "SNInc")
    | type_expr (BE_Node2(_, Keyword "NInc", x, y)) = kw_xxp (x, y, "NInc")
    | type_expr (BE_Node2(_, Keyword "SInc", x, y)) = kw_xxp (x, y, "SInc")
    | type_expr (BE_Node2(_, Keyword "Eq", x, y)) = kw_xxp (x, y, "Eq")

    | type_expr (BE_Node2(zto, Keyword "TBij", x, y)) = type_relationsets (zto, x, y, "TBij")
    | type_expr (BE_Node2(zto, Keyword "TFun", x, y)) = type_relationsets (zto, x, y, "TFun")
    | type_expr (BE_Node2(zto, Keyword "PFun", x, y)) = type_relationsets (zto, x, y, "PFun")
    | type_expr (BE_Node2(zto, Keyword "Sur",  x, y)) = type_relationsets (zto, x, y, "Sur")
    | type_expr (BE_Node2(zto, Keyword "PSur", x, y)) = type_relationsets (zto, x, y, "PSur")
    | type_expr (BE_Node2(zto, Keyword "TInj", x, y)) = type_relationsets (zto, x, y, "TInj")
    | type_expr (BE_Node2(zto, Keyword "PInj", x, y)) = type_relationsets (zto, x, y, "PInj")
    | type_expr (BE_Node2(zto, Keyword "Rel",  x, y)) = type_relationsets (zto, x, y, "Rel")

    | type_expr (BE_Node2(zto, Keyword "SubRan", x, y)) = type_ranOperations (zto, x, y, "SubRan")
    | type_expr (BE_Node2(zto, Keyword "ResRan", x, y)) = type_ranOperations (zto, x, y, "ResRan")
    
    | type_expr (BE_Node2(zto, Keyword "SubDom", x, y)) = type_domOperations (zto, x, y, "SubDom")
    | type_expr (BE_Node2(zto, Keyword "ResDom", x, y)) = type_domOperations (zto, x, y, "ResDom")

    | type_expr (BE_Node2(zto, Keyword "RseqE", x, y)) = type_rseq (zto, x, y, "RseqE")
    | type_expr (BE_Node2(zto, Keyword "RseqH", x, y)) = type_rseq (zto, x, y, "RseqH")

    | type_expr (BE_Node2(zto, Keyword "InsSeqEnd", x, y)) = 
      let
        val xzto = typeUnification (typeOf x) zto
        val yto = typeOf y
        val eto = (
            case xzto of 
              SOME(BT_Power(SOME(BT_Pair(_, eto1)))) => typeUnification eto1 yto
            | _ => yto
          )
        val nxto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer), eto))))
        val nyto = eto
        val nzto = nxto 
      in
        BE_Node2(nzto, Keyword "InsSeqEnd", setType_opt nxto x, setType_opt nyto y)
      end
    | type_expr (BE_Node2(zto, Keyword "InsSeqStart", x, y)) =
      let
        val yzto = typeUnification (typeOf y) zto
        val xto = typeOf x
        val eto = (
            case yzto of 
              SOME(BT_Power(SOME(BT_Pair(_, eto1)))) => typeUnification eto1 xto
            | _ => xto
          )
        val nxto = eto
        val nyto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer), eto))))
        val nzto = nyto 
      in
        BE_Node2(nzto, Keyword "InsSeqStart", setType_opt nxto x, setType_opt nyto y)
      end
    | type_expr (BE_Node2(zto, Keyword "Semicoron", x, y)) = 
      let
        val xto = typeOf x
        val yto = typeOf y
        val (nato, nbto, ncto) = 
          (
            case (xto, yto, zto) of
              (SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))), SOME(BT_Power(SOME(BT_Pair(bto2, cto1)))), SOME(BT_Power(SOME(BT_Pair(ato2, cto2))))) =>
                (typeUnification ato1 ato2, typeUnification bto1 bto2, typeUnification cto1 cto2)
            | (SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))), SOME(BT_Power(SOME(BT_Pair(bto2, cto1)))), _                                        ) =>
              (ato1, typeUnification bto1 bto2, cto1)
            | (SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))), _                                        , SOME(BT_Power(SOME(BT_Pair(ato2, cto2))))) =>
              (typeUnification ato1 ato2, bto1, cto2)
            | (_                                        , SOME(BT_Power(SOME(BT_Pair(bto2, cto1)))), SOME(BT_Power(SOME(BT_Pair(ato2, cto2))))) =>
              (ato2, bto2, typeUnification cto1 cto2)
            | (SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))), _                                        , _                                        ) =>
              (ato1, bto1, NONE)
            | (_                                        , SOME(BT_Power(SOME(BT_Pair(bto2, cto1)))), _                                        ) =>
              (NONE, bto2, cto1)
            | (_                                        , _                                        , SOME(BT_Power(SOME(BT_Pair(ato2, cto2))))) =>
              (ato2, NONE, cto2)
            | _ => (NONE, NONE, NONE)
          )
        val nxto = SOME(BT_Power(SOME(BT_Pair(nato, nbto))))
        val nyto = SOME(BT_Power(SOME(BT_Pair(nbto, ncto))))
        val nzto = SOME(BT_Power(SOME(BT_Pair(nato, ncto))))
      in
        BE_Node2(nzto, Keyword "Semicoron", setType_opt nxto x, setType_opt nyto y)
      end
    | type_expr (BE_Node2(zto, Keyword "DProductRel", x, y)) =
      let
        val xto = typeOf x
        val yto = typeOf y
        val (nato, nbto, ncto) = (
            case (xto, yto, zto) of
              (SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))),
                SOME(BT_Power(SOME(BT_Pair(bto2, cto2)))),
                SOME(BT_Power(SOME(BT_Pair(ato3, SOME(BT_Pair(bto3, cto3)))))))
              => 
                (typeUnification ato1 ato3, typeUnification bto1 (typeUnification bto2 bto3), typeUnification cto2 cto3)
            | (SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))),
              SOME(BT_Power(SOME(BT_Pair(bto2, cto2)))),
              SOME(BT_Power(SOME(BT_Pair(ato3, _)))))
            => 
              (typeUnification ato1 ato3, typeUnification bto1 bto2, cto2)
            |(SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))),
              SOME(BT_Power(SOME(BT_Pair(bto2, cto2)))),
              _)
            => 
              (ato1, typeUnification bto1 bto2, cto2)
            |(SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))),
              _,
              SOME(BT_Power(SOME(BT_Pair(ato3, SOME(BT_Pair(bto3, cto3)))))))
            => 
              (typeUnification ato1 ato3, typeUnification bto1 bto3, cto3)
            |(SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))),
              _,
              SOME(BT_Power(SOME(BT_Pair(ato3, _)))))
            => 
              (typeUnification ato1 ato3, bto1, NONE)
            |(_,
              SOME(BT_Power(SOME(BT_Pair(bto2, cto2)))),
              SOME(BT_Power(SOME(BT_Pair(ato3, SOME(BT_Pair(bto3, cto3)))))))
            => 
              (ato3, typeUnification bto2 bto3, typeUnification cto2 cto3)
            |(SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))), _, _)
            => 
              (ato1, bto1, NONE)
            |(_, SOME(BT_Power(SOME(BT_Pair(bto2, cto2)))), _)
            => 
              (NONE, bto2, cto2)
            |(_, _, SOME(BT_Power(SOME(BT_Pair(ato3, SOME(BT_Pair(bto3, cto3)))))))
            => 
              (ato3, bto3, cto3)
            | _ => (NONE, NONE, NONE)
          )
        val nxto = SOME(BT_Power(SOME(BT_Pair(nato, nbto))))
        val nyto = SOME(BT_Power(SOME(BT_Pair(nbto, ncto))))
        val nzto = SOME(BT_Power(SOME(BT_Pair(nato, SOME(BT_Pair(nbto, ncto))))))
      in
        BE_Node2(nzto, Keyword "DProductRel", setType_opt nxto x, setType_opt nyto y)
      end
    | type_expr (BE_Fnc(yto, f, x)) =
      let
        val fto = typeOf f
        val xto = typeOf x
        val (nxto, nyto) = (
            case fto of 
              SOME(BT_Power(SOME(BT_Pair(ato, bto)))) => 
                (typeUnification ato xto, typeUnification bto yto)
            | _ => (xto, yto)
          )
        val nfto = SOME(BT_Power(SOME(BT_Pair(nxto, nyto))))
      in
        BE_Fnc(nyto, setType_opt nfto f, setType_opt nxto x)
      end
    | type_expr (BE_Img(yto, f, x)) =
      let
        val fto = typeOf f
        val xto = typeOf x
        val (nato, nbto) = (
            case (fto, xto, yto) of 
              (SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))), SOME(BT_Power(ato2)), SOME(BT_Power(bto2))) => 
                (typeUnification ato1 ato2, typeUnification bto1 bto2)
            |(SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))), SOME(BT_Power(ato2)), NONE) => 
              (typeUnification ato1 ato2, bto1)
            |(SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))), NONE, SOME(BT_Power(bto2))) => 
              (ato1, typeUnification bto1 bto2)
            |(_, SOME(BT_Power(ato2)), SOME(BT_Power(bto2))) => 
              (ato2, bto2)
            |(SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))), NONE, NONE) => 
              (ato1, bto1)
            |(_, SOME(BT_Power(ato2)), NONE) => 
              (ato2, NONE)
            |(_, NONE, SOME(BT_Power(bto2))) => 
              (NONE, bto2)
            | _ => (NONE, NONE)
          )
        val nxto = SOME(BT_Power(nato))
        val nyto = SOME(BT_Power(nbto))
        val nfto = SOME(BT_Power(SOME(BT_Pair(nato, nbto))))
      in
        BE_Img(nyto, setType_opt nfto f, setType_opt nxto x)
      end
    | type_expr (BE_Node1(_, Reserved "not", x)) = 
      BE_Node1(SOME(BT_Predicate), Reserved "not", setType BT_Predicate x)
    | type_expr (BE_Node1(_, Reserved "pred", x)) = 
      BE_Node1(SOME(BT_Integer), Reserved "pred", setType BT_Integer x)
    | type_expr (BE_Node1(_, Reserved "succ", x)) = 
      BE_Node1(SOME(BT_Integer), Reserved "succ", setType BT_Integer x)
    | type_expr (BE_Node1(_, Reserved "floor", x)) = 
      BE_Node1(SOME(BT_Integer), Reserved "floor", setType BT_Real x)
    | type_expr (BE_Node1(_, Reserved "ceiling", x)) = 
      BE_Node1(SOME(BT_Integer), Reserved "ceiling", setType BT_Real x)
    | type_expr (BE_Node1(_, Reserved "real", x)) = 
      BE_Node1(SOME(BT_Real), Reserved "real", setType BT_Integer x)
    | type_expr (BE_Node1(_, Reserved "card", x)) = 
      BE_Node1(SOME(BT_Integer), Reserved "card", setType_opt (typeUnification (typeOf x) (SOME(BT_Power(NONE)))) x)
    | type_expr (BE_Node1(_, Reserved "size", x)) = 
      BE_Node1(SOME(BT_Integer), Reserved "size", setType_opt (typeUnification (typeOf x) (SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),NONE)))))) x)
    | type_expr (BE_Node1(_, Reserved "sizet", x)) = 
      BE_Node1(SOME(BT_Integer), Reserved "sizet", setType_opt (typeUnification (typeOf x) (SOME(BT_Power(SOME(BT_Pair(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),SOME(BT_Integer))))),NONE)))))) x)
    | type_expr (BE_Node1(yto, Reserved "max", x)) = type_minmax (yto, "max", x)
    | type_expr (BE_Node1(yto, Reserved "min", x)) = type_minmax (yto, "min", x)
    | type_expr (BE_Node1(yto, Reserved "FIN", x)) = type_pow (yto, "FIN", x)
    | type_expr (BE_Node1(yto, Reserved "FIN1", x)) = type_pow (yto, "FIN1", x)
    | type_expr (BE_Node1(yto, Reserved "POW", x)) = type_pow (yto, "POW", x)
    | type_expr (BE_Node1(yto, Reserved "POW1", x)) = type_pow (yto, "POW1", x)
    | type_expr (BE_Node1(yto, Reserved "id", x)) =
      let
        val xto = typeOf x
        val nato = (
            case (xto, yto) of
              (SOME(BT_Power(ato1)), SOME(BT_Power(SOME(BT_Pair(ato2, ato3))))) => typeUnification ato1 (typeUnification ato2 ato3)
            | (NONE, SOME(BT_Power(SOME(BT_Pair(ato2, ato3))))) => typeUnification ato2 ato3
            | (SOME(BT_Power(ato1)), _) => ato1
            | (NONE, _) => NONE
            | _ => raise BTypeError ""
          )
        val nxto = SOME(BT_Power(nato))
        val nyto = SOME(BT_Power(SOME(BT_Pair(nato, nato))))
      in
        BE_Node1(nyto, Reserved "id", setType_opt nxto x)
      end
    | type_expr (BE_Node1(yto, Reserved "first", x)) = type_flseq (yto, "first", x)
    | type_expr (BE_Node1(yto, Reserved "last", x)) = type_flseq (yto, "last", x)
    | type_expr (BE_Node1(yto, Reserved "union", x)) = type_uiset (yto, "union", x)
    | type_expr (BE_Node1(yto, Reserved "inter", x)) = type_uiset (yto, "inter", x)
    | type_expr (BE_Node1(dto, Reserved "dom", f)) = 
      let
        val fto = typeOf f
        val (nato, nbto) = (
            case (dto, fto) of
              (SOME(BT_Power(ato1)), SOME(BT_Power(SOME(BT_Pair(ato2, bto2))))) =>
                (typeUnification ato1 ato2, bto2)
            | (SOME(BT_Power(ato1)), _) =>
              (ato1, NONE)
            | (NONE, SOME(BT_Power(SOME(BT_Pair(ato2, bto2))))) =>
              (ato2, bto2)
            | (NONE, _) => (NONE, NONE)
            | _ => raise BTypeError ""
          )
        val ndto = SOME(BT_Power(nato))
        val nfto = SOME(BT_Power(SOME(BT_Pair(nato, nbto))))
      in
        BE_Node1(ndto, Reserved "dom", setType_opt nfto f)
      end
    | type_expr (BE_Node1(rto, Reserved "ran", f)) = 
      let
        val fto = typeOf f
        val (nato, nbto) = (
            case (rto, fto) of
              (SOME(BT_Power(bto1)), SOME(BT_Power(SOME(BT_Pair(ato2, bto2))))) =>
                (ato2, typeUnification bto1 bto2)
            | (SOME(BT_Power(bto1)), _) =>
              (NONE, bto1)
            | (NONE, SOME(BT_Power(SOME(BT_Pair(ato2, bto2))))) =>
              (ato2, bto2)
            | (NONE, _) => (NONE, NONE)
            | _ => raise BTypeError ""
          )
        val nrto = SOME(BT_Power(nbto))
        val nfto = SOME(BT_Power(SOME(BT_Pair(nato, nbto))))
      in
        BE_Node1(nrto, Reserved "ran", setType_opt nfto f)
      end
    | type_expr (BE_Node1(fto, Reserved "closure", g)) = type_closure (fto, "closure", g)
    | type_expr (BE_Node1(fto, Reserved "closure1", g)) = type_closure (fto, "closure1", g)
    
    | type_expr (BE_Node1(yto, Reserved "seq", x)) = type_seqset (yto, "seq", x)
    | type_expr (BE_Node1(yto, Reserved "seq1", x)) = type_seqset (yto, "seq1", x)
    | type_expr (BE_Node1(yto, Reserved "iseq", x)) = type_seqset (yto, "iseq", x)
    | type_expr (BE_Node1(yto, Reserved "iseq1", x)) = type_seqset (yto, "iseq1", x)
    | type_expr (BE_Node1(yto, Reserved "perm", x)) = type_seqset (yto, "perm", x)
    
    | type_expr (BE_Node1(yto, Reserved "rev", x)) = type_seqConvert (yto, "rev", x)
    | type_expr (BE_Node1(yto, Reserved "front", x)) = type_seqConvert (yto, "front", x)
    | type_expr (BE_Node1(yto, Reserved "tail", x)) = type_seqConvert (yto, "tail", x)

    | type_expr (BE_Node1(yto, Reserved "btree", x)) = type_trees (yto, "btree", x)
    | type_expr (BE_Node1(yto, Reserved "tree", x)) = type_trees (yto, "tree", x)

    | type_expr (BE_Node1(yto, Reserved "fnc", x)) = 
      let
        val xto = typeOf x
        val (nato, nbto) = (
            case (xto, yto) of
              (SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))), SOME(BT_Power(SOME(BT_Pair(ato2, SOME(BT_Power(bto2))))))) =>
                (typeUnification ato1 ato2, typeUnification bto1 bto2)
            | (SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))), SOME(BT_Power(SOME(BT_Pair(ato2, NONE))))) =>
              (typeUnification ato1 ato2, bto1)
            | (SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))), _) =>
              (ato1, bto1)
            | (_, SOME(BT_Power(SOME(BT_Pair(ato2, SOME(BT_Power(bto2))))))) =>
              (ato2, bto2)
            | (_, SOME(BT_Power(SOME(BT_Pair(ato2, NONE))))) =>
              (ato2, NONE)
            | _ =>
              (NONE, NONE) 
          )
        val nxto = SOME(BT_Power(SOME(BT_Pair(nato, nbto))))
        val nyto = SOME(BT_Power(SOME(BT_Pair(nato, SOME(BT_Power(nbto))))))
      in
        BE_Node1(nyto, Reserved "fnc", setType_opt nxto x)
      end
    | type_expr (BE_Node1(yto, Reserved "rel", x)) = 
      let
        val xto = typeOf x
        val (nato, nbto) = (
            case (yto, xto) of
              (SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))), SOME(BT_Power(SOME(BT_Pair(ato2, SOME(BT_Power(bto2))))))) =>
                (typeUnification ato1 ato2, typeUnification bto1 bto2)
            | (SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))), SOME(BT_Power(SOME(BT_Pair(ato2, NONE))))) =>
              (typeUnification ato1 ato2, bto1)
            | (SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))), _) =>
              (ato1, bto1)
            | (_, SOME(BT_Power(SOME(BT_Pair(ato2, SOME(BT_Power(bto2))))))) =>
              (ato2, bto2)
            | (_, SOME(BT_Power(SOME(BT_Pair(ato2, NONE))))) =>
              (ato2, NONE)
            | _ =>
              (NONE, NONE) 
          )
        val nyto = SOME(BT_Power(SOME(BT_Pair(nato, nbto))))
        val nxto = SOME(BT_Power(SOME(BT_Pair(nato, SOME(BT_Power(nbto))))))
      in
        BE_Node1(nyto, Reserved "rel", setType_opt nxto x)
      end
    | type_expr (BE_Node1(yto, Reserved "conc", x)) = 
      let
        val xto = typeOf x
        val neto = (
            case (xto, yto) of
              (SOME(BT_Power(SOME(BT_Pair(_, SOME(BT_Power(SOME(BT_Pair(_,eto1)))))))),
                SOME(BT_Power(SOME(BT_Pair(_, eto2))))) => typeUnification eto1 eto2
            | (SOME(BT_Power(SOME(BT_Pair(_, SOME(BT_Power(SOME(BT_Pair(_,eto1)))))))),_) => eto1
            | (_, SOME(BT_Power(SOME(BT_Pair(_, eto2))))) => eto2
            | _ => NONE 
          )
        val nxto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer), SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),neto))))))))
        val nyto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer), neto))))
      in
        BE_Node1(nyto, Reserved "conc", setType_opt nxto x)
      end
    | type_expr (BE_Node1(yto, Reserved "infix", x)) = type_tree2seq (yto, "infix", x)
    | type_expr (BE_Node1(yto, Reserved "prefix", x)) = type_tree2seq (yto, "prefix", x)
    | type_expr (BE_Node1(yto, Reserved "postfix", x)) = type_tree2seq (yto, "postfix", x)

    | type_expr (BE_Node1(yto, Reserved "left", x)) = type_tree2tree (yto, "left", x)
    | type_expr (BE_Node1(yto, Reserved "right", x)) = type_tree2tree (yto, "right", x)
    | type_expr (BE_Node1(yto, Reserved "mirror", x)) = type_tree2tree (yto, "mirror", x)

    | type_expr (BE_Node1(yto, Reserved "top", x)) =    
      let
        val xto = typeOf x
        val nyto = (
            case (xto, yto) of
              (SOME(BT_Power(SOME(BT_Pair(_, yto1)))), yto2) =>
                typeUnification yto1 yto2
            | (_, yto2) => yto2
          )
        val nxto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer), SOME(BT_Integer))))), nyto))))
      in
        BE_Node1(nyto, Reserved "top", setType_opt nxto x)
      end
    | type_expr (BE_Node1(yto, Reserved "sons", x)) =
      let
        val xto = typeOf x
        val neto = (
            case (xto, yto) of
              (SOME(BT_Power(SOME(BT_Pair(_, eto1)))), SOME(BT_Power(SOME(BT_Pair(_, SOME(BT_Power(SOME(BT_Pair(_, eto2))))))))) =>
                typeUnification eto1 eto2
            | (SOME(BT_Power(SOME(BT_Pair(_, eto1)))), _) => eto1
            | (_, SOME(BT_Power(SOME(BT_Pair(_, SOME(BT_Power(SOME(BT_Pair(_, eto2))))))))) => eto2
            | _ => NONE
          )
        val nxto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer), SOME(BT_Integer))))), neto))))
        val nyto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer), nxto))))
      in
        BE_Node1(nyto, Reserved "sons", setType_opt nxto x)
      end
    | type_expr (BE_Struct(SOME(BT_Power(NONE)), lst)) = type_expr (BE_Struct(NONE, lst))
    | type_expr (BE_Struct(NONE, lst)) = (*要素からstruct(e)への型付けのみ、逆はなし*)
      let
        fun typestruct_sub [] = []
          | typestruct_sub ((n, e)::rest) =
            let
              val to = typeOf e
              fun elt (SOME(BT_Power(x))) = x
                | elt NONE = NONE
                | elt _ = raise BTypeError ""
            in
              (elt(to), n)::(typestruct_sub rest)
            end
        val tonlst = typestruct_sub lst
      in
        if List.exists (fn (to, _) => (to = NONE)) tonlst then
          BE_Struct(SOME(BT_Power((NONE))), lst)
        else
          BE_Struct(SOME(BT_Power(SOME(BT_Struct(List.map (fn (to, e) => (valOf(to), e)) tonlst)))), lst)
      end
    | type_expr (BE_Node2(_, Reserved "arity", x, y)) =
      let
        val nxto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),SOME(BT_Integer))))),NONE))))
        val nyto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer), SOME(BT_Integer)))))
        val nzto = SOME(BT_Integer)
      in
        BE_Node2(nzto, Reserved "arity", setType_opt nxto x, setType_opt nyto y)
      end
    | type_expr (BE_Node2(zto, Reserved "const", x, y)) =
      let
        val xto = typeOf x
        val yto = typeOf y
        val nxto = (
            case (yto, zto) of
              (SOME(BT_Power(SOME(BT_Pair(_,SOME(BT_Power(SOME(BT_Pair(_, xto1)))))))),SOME(BT_Power(SOME(BT_Pair(_,xto2))))) => typeUnification (typeUnification xto1 xto2) xto
            | (SOME(BT_Power(SOME(BT_Pair(_,SOME(BT_Power(SOME(BT_Pair(_, xto1)))))))),_) => typeUnification xto xto1
            | (_, SOME(BT_Power(SOME(BT_Pair(_,xto2))))) => typeUnification xto xto2
            | _ => xto
          )
        val nyto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer), SOME(BT_Power(SOME(BT_Pair(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),SOME(BT_Integer))))), nxto))))))))
        val nzto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),SOME(BT_Integer))))),xto))))
      in
        BE_Node2(nzto, Reserved "const", setType_opt xto x, setType_opt yto y)
      end
    | type_expr (BE_Node2(zto, Reserved "father", x, y)) = 
      let
        val nxto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),SOME(BT_Integer))))),NONE))))
        val nyto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),SOME(BT_Integer)))))
        val nzto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),SOME(BT_Integer))))) 
      in
        BE_Node2(nzto, Reserved "father", setType_opt nyto y, setType_opt nxto x)
      end
    | type_expr (BE_Node2(zto, Reserved "iterate", x, y)) = 
      let
        val xto = typeOf x
        val nato = (
            case (xto, zto) of
              (SOME(BT_Power(SOME(BT_Pair(ato1, ato2)))), SOME(BT_Power(SOME(BT_Pair(ato3, ato4))))) => List.foldl (Utils.uncurry typeUnification) NONE [ato1, ato2, ato3, ato4]
            | (_, SOME(BT_Power(SOME(BT_Pair(ato3, ato4))))) => typeUnification ato3 ato4
            | (SOME(BT_Power(SOME(BT_Pair(ato1, ato2)))),_) => typeUnification ato1 ato2
            | _ => NONE
          )
        val nxto = SOME(BT_Power(SOME(BT_Pair(nato, nato))))
        val nyto = SOME(BT_Integer)
        val nzto = SOME(BT_Power(SOME(BT_Pair(nato, nato))))
      in
        BE_Node2(nzto, Reserved "iterate", setType_opt nxto x, setType_opt nyto y)
      end
    | type_expr (BE_Node2(zto, Reserved "prj1", x, y)) = 
      let
        val xto = typeOf x
        val yto = typeOf y
        val (nato, nbto) = (
            case (xto, yto, zto) of
              (SOME(BT_Power(ato1)), SOME(BT_Power(bto1)), SOME(BT_Power(SOME(BT_Pair(SOME(BT_Pair(ato2, bto2)),ato3))))) => (typeUnification ato1 (typeUnification ato2 ato3), typeUnification bto1 bto2)
            | (SOME(BT_Power(ato1)), SOME(BT_Power(bto1)), _) => (ato1, bto1)
            | (SOME(BT_Power(ato1)), NONE, SOME(BT_Power(SOME(BT_Pair(SOME(BT_Pair(ato2, bto2)),ato3))))) => (typeUnification ato1 (typeUnification ato2 ato3), bto2)
            | (NONE, SOME(BT_Power(bto1)), SOME(BT_Power(SOME(BT_Pair(SOME(BT_Pair(ato2, bto2)),ato3))))) => (typeUnification ato2 ato3, typeUnification bto1 bto2)
            | (SOME(BT_Power(ato1)), NONE, _) => (ato1, NONE)
            | (NONE, NONE, SOME(BT_Power(SOME(BT_Pair(SOME(BT_Pair(ato2, bto2)),ato3))))) => (typeUnification ato2 ato3, bto2)
            | (NONE, SOME(BT_Power(bto1)), _) => (NONE, bto1)
            | (NONE, NONE, _) => (NONE, NONE)
            | _ => raise BTypeError ""
          )
        val nxto = SOME(BT_Power(nato))
        val nyto = SOME(BT_Power(nbto))
        val nzto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Pair(nato, nbto)),nato))))
      in
        BE_Node2(nzto, Reserved "prj1", setType_opt nxto x, setType_opt nyto y)
      end
    | type_expr (BE_Node2(zto, Reserved "prj2", x, y)) = 
      let
        val xto = typeOf x
        val yto = typeOf y
        val (nato, nbto) = (
            case (xto, yto, zto) of
              (SOME(BT_Power(ato1)), SOME(BT_Power(bto1)), SOME(BT_Power(SOME(BT_Pair(SOME(BT_Pair(ato2, bto2)),bto3))))) => (typeUnification ato1 ato2, typeUnification bto1 (typeUnification bto2 bto3))
            | (SOME(BT_Power(ato1)), SOME(BT_Power(bto1)), _) => (ato1, bto1)
            | (SOME(BT_Power(ato1)), NONE, SOME(BT_Power(SOME(BT_Pair(SOME(BT_Pair(ato2, bto2)),bto3))))) => (typeUnification ato1 ato2, typeUnification bto2 bto3)
            | (NONE, SOME(BT_Power(bto1)), SOME(BT_Power(SOME(BT_Pair(SOME(BT_Pair(ato2, bto2)),bto3))))) => (ato2, typeUnification bto1 (typeUnification bto2 bto3))
            | (SOME(BT_Power(ato1)), NONE, _) => (ato1, NONE)
            | (NONE, NONE, SOME(BT_Power(SOME(BT_Pair(SOME(BT_Pair(ato2, bto2)),bto3))))) => (ato2, typeUnification bto2 bto3)
            | (NONE, SOME(BT_Power(bto1)), _) => (NONE, bto1)
            | (NONE, NONE, _) => (NONE, NONE)
            | _ => raise BTypeError ""
          )
        val nxto = SOME(BT_Power(nato))
        val nyto = SOME(BT_Power(nbto))
        val nzto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Pair(nato, nbto)),nbto))))
      in
        BE_Node2(nzto, Reserved "prj2", setType_opt nxto x, setType_opt nyto y)
      end
    | type_expr (BE_Node2(zto, Reserved "rank", x, y)) = 
      let
        val xto = typeOf x
        val xto1 = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),SOME(BT_Integer))))),NONE))))
        val nxto = typeUnification xto xto1
        val nyto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),SOME(BT_Integer)))))
        val nzto = SOME(BT_Integer)
      in
        BE_Node2(nzto, Reserved "rank", setType_opt nxto x, setType_opt nyto y)
      end
    | type_expr (BE_Node2(zto, Reserved "subtree", x, y)) = 
      let
        val xto = typeOf x
        val nato = (
            case (xto, zto) of
              (SOME(BT_Power(SOME(BT_Pair(_,ato1)))),SOME(BT_Power(SOME(BT_Pair(_,ato2))))) => (typeUnification ato1 ato2)
            | (SOME(BT_Power(SOME(BT_Pair(_,ato1)))),_) => ato1
            | (_,SOME(BT_Power(SOME(BT_Pair(_,ato2))))) => ato2
            | _ => NONE
          )
        val nxto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),SOME(BT_Integer))))),nato))))
        val nyto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),SOME(BT_Integer)))))
        val nzto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),SOME(BT_Integer))))),nato))))
      in
        BE_Node2(nzto, Reserved "subtree", setType_opt nxto x, setType_opt nyto y)
      end
    | type_expr (BE_NodeN(yto, Reserved "bin", [x])) = 
      let
        val xto = typeOf x
        val nxto = (
            case yto of
              (SOME(BT_Power(SOME(BT_Pair(_,xto1))))) => typeUnification xto xto1
            | _ => NONE
          )
        val nyto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),SOME(BT_Integer))))),nxto))))
      in
        BE_NodeN(nyto, Reserved "bin", [setType_opt nxto x])
      end
    | type_expr (BE_NodeN(yto, Reserved "bin", [l,x,r])) =
      let
        val xto = typeOf x
        val lto = typeOf l
        val rto = typeOf r
        val nxto = (
            case (lto, rto, yto) of
              ((SOME(BT_Power(SOME(BT_Pair(_,xto1))))),(SOME(BT_Power(SOME(BT_Pair(_,xto2))))),(SOME(BT_Power(SOME(BT_Pair(_,xto3)))))) => 
                List.foldl (Utils.uncurry typeUnification) xto [xto1, xto2, xto3]
            | ((SOME(BT_Power(SOME(BT_Pair(_,xto1))))),(SOME(BT_Power(SOME(BT_Pair(_,xto2))))),_) => 
              List.foldl (Utils.uncurry typeUnification) xto [xto1, xto2]
            | ((SOME(BT_Power(SOME(BT_Pair(_,xto1))))),_,(SOME(BT_Power(SOME(BT_Pair(_,xto3)))))) => 
              List.foldl (Utils.uncurry typeUnification) xto [xto1, xto3]
            | (_,(SOME(BT_Power(SOME(BT_Pair(_,xto2))))),(SOME(BT_Power(SOME(BT_Pair(_,xto3)))))) => 
              List.foldl (Utils.uncurry typeUnification) xto [xto2, xto3]
            | ((SOME(BT_Power(SOME(BT_Pair(_,xto1))))),_,_) => 
              typeUnification xto xto1
            | (_,(SOME(BT_Power(SOME(BT_Pair(_,xto2))))),_) => 
              typeUnification xto xto2
            | (_,_,(SOME(BT_Power(SOME(BT_Pair(_,xto3)))))) => 
              typeUnification xto xto3
            | _ => raise BTypeError ""
          )
        val nyto = (SOME(BT_Power(SOME(BT_Pair(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),SOME(BT_Integer))))),nxto)))))
        val nlto = (SOME(BT_Power(SOME(BT_Pair(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),SOME(BT_Integer))))),nxto)))))
        val nrto = (SOME(BT_Power(SOME(BT_Pair(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),SOME(BT_Integer))))),nxto)))))
      in
        BE_NodeN(nyto, Reserved "bin", [setType_opt nlto l, setType_opt nxto x, setType_opt nrto r])
      end
    | type_expr (BE_NodeN(_, Reserved "bin", _)) = raise BTypeError ""
    | type_expr (BE_NodeN(sto, Reserved "son", [x, y, z])) = 
      let
        val xto = typeOf x
        val nxto = typeUnification xto (SOME(BT_Power(SOME(BT_Pair(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),SOME(BT_Integer))))),NONE)))))
        val nyto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),SOME(BT_Integer)))))
        val nzto = SOME(BT_Integer)
        val nsto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),SOME(BT_Integer)))))
      in
        BE_NodeN(nsto, Reserved "son", [setType_opt nxto x, setType_opt nyto y, setType_opt nzto z])
      end
    | type_expr (BE_NodeN(_, Reserved "son", _)) = raise BTypeError ""

    (*ラベル付きの要素の型からレコード全体の型への推論*)
    | type_expr (x as (BE_Rec(NONE, (l as ((SOME(_),_)::rest))))) = 
      let
        val lo = List.map (fn xx => case xx of (SOME(s),e) => (typeOf e,s) | _ => raise BTypeError "") l
      in
        if List.exists (fn (to,ss) => to=NONE) lo then
          x          
        else
          let
            val nl = List.map (fn xx => case xx of (SOME(t), s) => (t,s) | _ => raise BTypeError "") lo
          in
            BE_Rec(SOME(BT_Struct(nl)), l)
          end
      end
    (*レコード全体の型と要素の型の相互への推論*)
    | type_expr (x as (BE_Rec(SOME(BT_Struct(l1)), l2))) = 
      let
        val tl1 = List.map (fn (t, s) => (SOME(t),s)) l1
        val tl2 = List.map (fn (_, e) => ((typeOf e),e)) l2
        val tl12 = ListPair.zip (tl1, tl2)
        val nl2 = List.map (fn ((to1, s), (to2, e)) => let val to = typeUnification to1 to2 in (SOME(s),setType_opt to e) end) tl12
        val nl1 = List.map (fn xx => (case xx of (SOME(s), e) => (case typeOf e of NONE => raise BTypeError "" | SOME(t) => (t, s)) | _ => raise BTypeError "")) nl2
      in
        BE_Rec(SOME(BT_Struct(nl1)), nl2)
      end
    
    (*BE_Rec of BType option * (string option * BExpr) list*)(**)
    (*BT_Struct of (BType(*option*) * string) list*)
    | type_expr (x as (BE_Rec(_))) = x
    | type_expr (BE_ExSet(sto, es)) =
      let
        val eto = List.foldl (Utils.uncurry typeUnification) NONE (List.map typeOf es)
        val neto = (case sto of
              SOME(BT_Power(eto1)) => typeUnification eto eto1
            | NONE => eto
            | _ => raise BTypeError ""
          )
        val nsto = SOME(BT_Power(neto))
      in
        BE_ExSet(nsto, List.map (setType_opt neto) es)
      end
    | type_expr (BE_InSet(sto, vlst, BP_list(ps))) = (*Predicateから全体の型への推論のみ*)
      let
        val oenv = List.map (fn v => (v, NONE)) vlst
        val nenv = getEnvFromPredicate oenv ps
        val tlst = List.map (fn (x,to) => to) nenv
        fun typeTree x [] = x
          | typeTree x (y::ys) = typeTree (SOME(BT_Pair(x, y))) ys
        val nto = typeUnification sto (typeTree (hd tlst) (tl tlst))
      in
        BE_InSet(nto, vlst, BP_list(ps))
      end
    | type_expr (BE_Seq(sto, es)) =
      let
        val eto = List.foldl (Utils.uncurry typeUnification) NONE (List.map typeOf es)
        val neto = (case sto of
              SOME(BT_Power(SOME(BT_Pair(_,eto1)))) => typeUnification eto eto1
            | SOME(BT_Power(NONE)) => eto
            | NONE => eto
            | _ => raise BTypeError ""
          )
        val nsto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),neto))))
      in
        BE_Seq(nsto, List.map (setType_opt neto) es)
      end
    | type_expr (BE_Lambda(lto, vlst, BP_list(ps), e)) =
      let
        val oenv = List.map (fn v => (v, NONE)) vlst
        val nenv = getEnvFromPredicate oenv ps
        val tlst = List.map (fn (x, to) => to) nenv
        fun typeTree x [] = x
          | typeTree x (y::ys) = typeTree (SOME(BT_Pair(x,y))) ys
        val domto = typeTree (hd tlst) (tl tlst)
        val ne = type_exprTree (setEnv nenv e)
        val ranto = typeOf ne
        val (ndomto, nranto) =
          case lto of
            SOME(BT_Power(SOME(BT_Pair(dto,rto)))) => (typeUnification dto domto, typeUnification rto ranto)
          | _ => (domto, ranto)
        val nlto = SOME(BT_Power(SOME(BT_Pair(ndomto, nranto))))
      in
        BE_Lambda(nlto, vlst, BP_list(ps), setType_opt nranto ne)
      end
    | type_expr (BE_Sigma(to, x, BP_list(ps), e)) = 
      let
        val eto = typeOf e
        val nto = List.foldl (Utils.uncurry typeUnification) eto (List.map (fn p => #2(hd (getEnv [(x, to)] p))) ps)
      in
        BE_Sigma(nto, x, BP_list(ps), setType_opt nto e)
      end
    | type_expr (BE_Pi(to, x, BP_list(ps), e)) = 
      let
        val eto = typeOf e
        val nto = List.foldl (Utils.uncurry typeUnification) eto (List.map (fn p => #2(hd (getEnv [(x, to)] p))) ps)
      in
        BE_Pi(nto, x, BP_list(ps), setType_opt nto e)
      end
    | type_expr (BE_Inter(to, vlst, BP_list ps, e)) = type_quantified "INTER" to vlst ps e
    | type_expr (BE_Union(to, vlst, BP_list ps, e)) = type_quantified "UNION" to vlst ps e

    | type_expr x = x(*型推論できないものはスルー*)
  and
    type_quantified kind to vlst ps e =
      let
        val oenv = List.map (fn v => (v, NONE)) vlst
        val nenv = getEnvFromPredicate oenv ps
        val ne = type_exprTree (setEnv nenv e)
        val nto = typeUnification to (typeOf ne)
      in
        case kind of
          "INTER" => BE_Inter(nto, vlst, BP_list ps, setType_opt nto ne)
        | "UNION" => BE_Union(nto, vlst, BP_list ps, setType_opt nto ne)
        | _ => raise BTypeError ""
      end
  and
    getEnvFromPredicate env1 [] = env1
    | getEnvFromPredicate env1 (pp::pps) =
      let
        val env2 = getEnv env1 pp
      in
        getEnvFromPredicate env2 pps
      end
  and
    type_tree2tree (yto, s, x) =
      let
        val xto = typeOf x
        val neto = (
            case (xto, yto) of
              (SOME(BT_Power(SOME(BT_Pair(_, eto1)))), SOME(BT_Power(SOME(BT_Pair(_, eto2))))) =>
                typeUnification eto1 eto2
            | (SOME(BT_Power(SOME(BT_Pair(_, eto1)))), _) => eto1
            | (_, SOME(BT_Power(SOME(BT_Pair(_, eto2))))) => eto2
            | _ => NONE
          )
        val nxto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer), SOME(BT_Integer))))), neto))))
        val nyto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer), SOME(BT_Integer))))), neto))))
      in
        BE_Node1(nyto, Reserved s, setType_opt nxto x)
      end

  and
    type_tree2seq (yto, s, x) =
      let
        val xto = typeOf x
        val neto = (
            case (xto, yto) of
              (SOME(BT_Power(SOME(BT_Pair(_, eto1)))), SOME(BT_Power(SOME(BT_Pair(_, eto2))))) =>
                typeUnification eto1 eto2
            | (SOME(BT_Power(SOME(BT_Pair(_, eto1)))), _) => eto1
            | (_, SOME(BT_Power(SOME(BT_Pair(_, eto2))))) => eto2
            | _ => NONE
          )
        val nxto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer), SOME(BT_Integer))))), neto))))
        val nyto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer), neto))))
      in
        BE_Node1(nyto, Reserved s, setType_opt nxto x)
      end
  and
    type_trees (yto, s, x) =
      let
        val xto = typeOf x
        val neto = (
            case (xto, yto) of
              (SOME(BT_Power(eto1)), SOME(BT_Power(SOME(BT_Power(SOME(BT_Pair(_, eto2))))))) =>
                typeUnification eto1 eto2
            | (NONE, SOME(BT_Power(SOME(BT_Power(SOME(BT_Pair(_, eto2))))))) => eto2
            | (SOME(BT_Power(eto1)), _) => eto1
            | (NONE, _) => NONE
            | _ => raise BTypeError ""
          )
        val nxto = SOME(BT_Power(neto))
        val nyto = SOME(BT_Power(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer), SOME(BT_Integer))))), neto))))))
      in
        BE_Node1(nyto, Reserved s, setType_opt nxto x)
      end
  and
    type_seqConvert (yto, s, x) =
      let 
        val xto = typeOf x
        val neto = (
            case (xto, yto) of
              (SOME(BT_Power(SOME(BT_Pair(_, eto1)))), SOME(BT_Power(SOME(BT_Pair(_, eto2))))) =>
                typeUnification eto1 eto2
            | (SOME(BT_Power(SOME(BT_Pair(_, eto1)))), _) => eto1
            | (_, SOME(BT_Power(SOME(BT_Pair(_, eto2))))) => eto2
            | _ => NONE
          )
        val nxto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer), neto))))
        val nyto = nxto
      in
        BE_Node1(nyto, Reserved s, setType_opt nxto x)
      end
  and
    type_seqset (yto, s, x) =
      let
        val xto = typeOf x
        val neto = (
            case (xto, yto) of
              (SOME(BT_Power(eto1)), SOME(BT_Power(SOME(BT_Power(SOME(BT_Pair(_, eto2))))))) => 
                typeUnification eto1 eto2
            |(NONE, SOME(BT_Power(SOME(BT_Power(SOME(BT_Pair(_, eto2))))))) => eto2
            |(SOME(BT_Power(eto1)), _) => eto1
            |(NONE, _) => NONE
            | _ => raise BTypeError ""
          )
        val nxto = SOME(BT_Power(neto))
        val nyto = SOME(BT_Power(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer), neto))))))
      in
        BE_Node1(nyto, Reserved s, setType_opt nxto x)
      end
  and
    type_closure (fto, s, g) = 
      let
        val gto = typeOf g
        val nxto = (
            case (fto, gto) of
              (SOME(BT_Power(SOME(BT_Pair(xto1, xto2)))), SOME(BT_Power(SOME(BT_Pair(xto3, xto4))))) =>
                typeUnification xto1 (typeUnification xto2 (typeUnification xto3 xto4))
            | (SOME(BT_Power(SOME(BT_Pair(xto1, xto2)))), _) =>
              typeUnification xto1 xto2
            | (_, SOME(BT_Power(SOME(BT_Pair(xto3, xto4))))) =>
              typeUnification xto3 xto4
            | _ => NONE
          )
        val nfto = SOME(BT_Power(SOME(BT_Pair(nxto, nxto))))
        val ngto = nfto
      in
        BE_Node1(nfto, Reserved s, setType_opt ngto g)
      end
  and
    type_uiset (yto, s, x) =
      let
        val xto = typeOf x
        val neto = (
            case (xto, yto) of
              (SOME(BT_Power(SOME(BT_Power(eto1)))), (SOME(BT_Power(eto2)))) =>
                typeUnification eto1 eto2
            | (_, (SOME(BT_Power(eto2)))) => eto2
            | (SOME(BT_Power(SOME(BT_Power(eto1)))), _) =>  eto1
            | (_, NONE) => NONE
            | _ => raise BTypeError ""
          )
        val nxto = SOME(BT_Power(SOME(BT_Power(neto))))
        val nyto = SOME(BT_Power(neto))
      in
        BE_Node1(nyto, Reserved s, setType_opt nxto x)
      end
  and
    type_flseq (yto, s, x) = 
      let
        val xto = typeOf x
        val nyto = (
            case xto of
              (SOME(BT_Power(SOME(BT_Pair(_, eto))))) => typeUnification yto eto
            | _ => yto
          )
        val nxto = SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer), nyto))))
      in
        BE_Node1(nyto, Reserved s, setType_opt nxto x)
      end
  and
    type_pow (yto, s, x) =
      let
        val xto = typeOf x
        val nato = (
            case (xto, yto) of
              (SOME(BT_Power(ato1)), SOME(BT_Power(SOME(BT_Power(ato2))))) => typeUnification ato1 ato2
            | (SOME(BT_Power(ato1)), _) => ato1
            | (NONE, SOME(BT_Power(SOME(BT_Power(ato2))))) => ato2
            | (NONE, _) => NONE
            | _ => raise BTypeError ""
          )
        val nxto = SOME(BT_Power(nato))
        val nyto = SOME(BT_Power(nxto))
      in
        BE_Node1(nyto, Reserved s, setType_opt nxto x)
      end
  and
    type_minmax (yto, s, x) = 
      let
        val xto = typeOf x
        val nyto = (
            case xto of
              SOME(BT_Power(bto)) => typeUnification bto yto
            | NONE => yto
            | _ => raise BTypeError ""
          )
        val nxto = SOME(BT_Power(nyto))
      in
        BE_Node1(nyto, Reserved s, setType_opt nxto x)
      end
  and
    type_rseq (zto, x, y, s) =
      let
        val nxto = (
            case typeUnification (typeOf x) zto of
              (SOME(BT_Power(SOME(BT_Pair(_,eto))))) => (SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer), eto)))))
            | _ => (SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer), NONE)))))
          )
      in
        BE_Node2(nxto, Keyword s, setType_opt nxto x, setType BT_Integer y)
      end
  and
    type_ranOperations (zto, x, y, s) =
      let
        val xto = typeOf x
        val yto = typeOf y
        val (nato, nbto) = 
          (case (xto, yto, zto) of
              (SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))), SOME(BT_Power(bto2)), SOME(BT_Power(SOME(BT_Pair(ato3, bto3))))) =>
                (typeUnification ato1 ato3, typeUnification bto1 (typeUnification bto2 bto3))
            | (_, SOME(BT_Power(bto2)), SOME(BT_Power(SOME(BT_Pair(ato3, bto3))))) => 
              (ato3, typeUnification bto2 bto3)
            | (SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))), NONE, SOME(BT_Power(SOME(BT_Pair(ato3, bto3))))) =>
              (typeUnification ato1 ato3, typeUnification bto1 bto3)
            | (SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))), SOME(BT_Power(bto2)), _) =>
              (ato1, typeUnification bto1 bto2)
            | (SOME(BT_Power(SOME(BT_Pair(ato1, bto1)))), NONE, _) =>
              (ato1, bto1)
            | (_, SOME(BT_Power(bto2)), _) =>
              (NONE, bto2)
            | (_, NONE, SOME(BT_Power(SOME(BT_Pair(ato3, bto3))))) =>
              (ato3, bto3)
            | (_, NONE, _) =>
              (NONE, NONE)
            | _ => raise BTypeError ""
          )
        val nxto = SOME(BT_Power(SOME(BT_Pair(nato, nbto))))
        val nyto = SOME(BT_Power(nbto))
        val nzto = nxto
      in
        BE_Node2(nzto, Keyword s, setType_opt nxto x, setType_opt nyto y)
      end
  and
    type_domOperations (zto, x, y, s) =
      let
        val xto = typeOf x
        val yto = typeOf y
        val (nato, nbto) = 
          (case (xto, yto, zto) of
              (SOME(BT_Power(ato1)), SOME(BT_Power(SOME(BT_Pair(ato2, bto2)))), SOME(BT_Power(SOME(BT_Pair(ato3, bto3))))) =>
                (typeUnification ato1 (typeUnification ato2 ato3), typeUnification bto2 bto3)
            | (SOME(BT_Power(ato1)), _, SOME(BT_Power(SOME(BT_Pair(ato3, bto3))))) => 
              (typeUnification ato1 ato3, bto3)
            | (NONE, SOME(BT_Power(SOME(BT_Pair(ato2, bto2)))), SOME(BT_Power(SOME(BT_Pair(ato3, bto3))))) =>
              (typeUnification ato2 ato3, typeUnification bto2 bto3)
            | (SOME(BT_Power(ato1)), SOME(BT_Power(SOME(BT_Pair(ato2, bto2)))), _) =>
              (typeUnification ato1 ato2, bto2)
            | (NONE, SOME(BT_Power(SOME(BT_Pair(ato2, bto2)))), _) =>
              (ato2, bto2)
            | (SOME(BT_Power(ato1)), _, _) =>
              (ato1, NONE)
            | (NONE, _, SOME(BT_Power(SOME(BT_Pair(ato3, bto3))))) =>
              (ato3, bto3)
            | (NONE, NONE, _) =>
              (NONE, NONE)
            | _ => raise BTypeError ""
          )
        val nxto = SOME(BT_Power(nato))
        val nyto = SOME(BT_Power(SOME(BT_Pair(nato, nbto))))
        val nzto = nyto
      in
        BE_Node2(nzto, Keyword s, setType_opt nxto x, setType_opt nyto y)
      end
  and
    type_relationsets (zto, x, y, s) = 
      let
        val xto = typeOf x
        val yto = typeOf y
        val (nato, nbto) = 
          (case (xto, yto, zto) of
              (SOME(BT_Power(ato1)), SOME(BT_Power(bto1)), SOME(BT_Power(SOME(BT_Power(SOME(BT_Pair(ato2, bto2))))))) =>
                (typeUnification ato1 ato2, typeUnification bto1 bto2)
            | (NONE,                 SOME(BT_Power(bto1)), SOME(BT_Power(SOME(BT_Power(SOME(BT_Pair(ato2, bto2))))))) =>
              (ato2, typeUnification bto1 bto2)
            | (SOME(BT_Power(ato1)), NONE,                 SOME(BT_Power(SOME(BT_Power(SOME(BT_Pair(ato2, bto2))))))) =>
              (typeUnification ato1 ato2, bto2)
            | (NONE,                 NONE,                 SOME(BT_Power(SOME(BT_Power(SOME(BT_Pair(ato2, bto2))))))) =>
              (ato2, bto2)
            | (SOME(BT_Power(ato1)), SOME(BT_Power(bto1)), _) =>
              (ato1, bto1)
            | (SOME(BT_Power(ato1)), NONE,                 _) =>
              (ato1, NONE)
            | (NONE,                 SOME(BT_Power(bto1)), _) =>
              (NONE, bto1)
            | (NONE,                 NONE,                 _) => 
              (NONE,NONE)
            | _ => raise BTypeError ""
          )
        val nxto = SOME(BT_Power(nato))
        val nyto = SOME(BT_Power(nbto))
        val nzto = SOME(BT_Power(SOME(BT_Power(SOME(BT_Pair(nato, nbto))))))
      in
        BE_Node2(nzto, Keyword s, setType_opt nxto x, setType_opt nyto y)
      end
  and
    kw_xxx (x, y, zto, s) = (* x x -> x *)
      let
        fun sameType3 (a, b, cto) = (* x x -> x *)
            let
              val ato = typeOf a
              val bto = typeOf b
              val to = typeUnification cto (typeUnification ato bto)
            in
              (setType_opt to a, setType_opt to b, to)
            end

        val (nx, ny, nzto) = sameType3 (x, y, zto)
      in
        BE_Node2(nzto, Keyword s, nx, ny)
      end
  and
    kw_xxp (x, y, s) = (* x x -> p *)
      let
        fun sameType2 (a, b) = (* x x -> p *)
            let
              val ato = typeOf a
              val bto = typeOf b
              val resto = typeUnification ato bto
            in
              (setType_opt resto a, setType_opt resto b)
            end 
        val (nx, ny) = sameType2 (x, y)
      in
        BE_Node2(SOME BT_Predicate, Keyword s, nx, ny)
      end
end
