signature PRINTCOMPONENT =
sig
  exception BPrintError of string
  val componentToString : BComponent -> string
end
(*|->に変換可能な,は全て変換済みとする*)
structure PrintComponent :> PRINTCOMPONENT =
struct
  exception BPrintError of string
  fun tabs depth = 
      if depth < 0 then 
        (raise BPrintError "") 
      else 
        if depth = 0 then 
          ("") 
        else 
          ("\t"^(tabs (depth - 1)))
  and
    priOf (BE_Leaf(_, token)) = (400, Priority.N)
    | priOf (BE_Node1(_, Keyword "Reverse", _)) = (230, Priority.L)
    | priOf (BE_Node1(_, Keyword "UMinus", _)) = (210, Priority.N)
    | priOf (BE_Node1(_)) = (400, Priority.N)
  
    | priOf (BE_Node2(_,Reserved s,_,_)) =
      (case s of
          "mod" => (190, Priority.L)
        | _ => (400, Priority.N))
    | priOf (BE_Node2(_,t,_,_)) = priOf_t t

    | priOf (BE_NodeN(_))     = (400, Priority.N)
    | priOf (BE_Fnc(_))   = (230, Priority.L)
    | priOf (BE_Img(_)) = (230, Priority.R)
    | priOf (BE_Bool(_))      = (400, Priority.N)
    | priOf (BE_ExSet(_))     = (400, Priority.N)
    | priOf (BE_InSet(_))     = (400, Priority.N)
    | priOf (BE_Seq(_))       = (400, Priority.N)
    | priOf (BE_ForAny(_))    = (400, Priority.N)
    | priOf (BE_Exists(_))    = (400, Priority.N)
    | priOf (BE_Lambda(_))    = (400, Priority.N)
    | priOf (BE_Sigma(_))     = (400, Priority.N)
    | priOf (BE_Pi(_))        = (400, Priority.N)
    | priOf (BE_Inter(_))     = (400, Priority.N)
    | priOf (BE_Union(_))     = (400, Priority.N)
    | priOf (BE_Struct(_))    = (400, Priority.N)
    | priOf (BE_Rec(_))       = (400, Priority.N)
    | priOf (BE_RcAc(_))      = (250, Priority.L)
  and
    getKeywordOp (token as (Keyword k)) =
      let 
        val kwi_opt = List.find (fn x => #2(x)=token) Priority.exprOperators
      in
        case kwi_opt of
          NONE => raise BPrintError ("Keyword \""^k^"\" is not an operator")
        | SOME(strOp, _,_,_) => strOp
      end
    | getKeywordOp _ = raise BPrintError ""
  and
    priOf_t t = 
      let
        val e = List.find (fn x => #2(x)=t) Priority.exprOperators
      in
        case e of 
          NONE => raise BPrintError "unknown operator"
        | SOME(x) => (#3(x),#4(x))(*優先順位と結合規則*)
      end
  and
    componentToString (BMch(name, [], clauses)) = "MACHINE\n\t"^name^"\n\n"^(clauseList2s clauses)^"END\n"
    | componentToString (BMch(name, params, clauses)) = "MACHINE\n\t"^name^"("^(tokenList2s params)^")\n\n"^(clauseList2s clauses)^"END\n"
    | componentToString _ = raise BPrintError "this component is not a abstract machine"
  and
    clauseList2s clauses =
      let
        val sortedClauses = ListMergeSort.sort (fn ((s1,_),(s2,_)) => #2(valOf(List.find (fn (ss1, _) => s1=ss1) Keywords.clauseKeywords)) >= #2(valOf(List.find (fn (ss2, _) => s2=ss2) Keywords.clauseKeywords))) clauses
        fun clauseList2s_sub [] = ""
          | clauseList2s_sub (x::xs) = (clause2s x)^(clauseList2s_sub xs)
      in
        clauseList2s_sub sortedClauses
      end
  and
    clause2s (clauseName, BC_CONSTRAINTS(p)) = clauseName^"\n"^(predicate2s 1 p)^"\n"
    | clause2s (clauseName, BC_PROPERTIES(p)) = clauseName^"\n"^(predicate2s 1 p)^"\n"
    | clause2s (clauseName, BC_INVARIANT(p)) = clauseName^"\n"^(predicate2s 1 p)^"\n"
    | clause2s (clauseName, BC_ASSERTIONS(p)) = clauseName^"\n"^(predicate2s 1 p)^"\n"

    | clause2s (clauseName, BC_SEES(l)) = clauseName^"\n"^(machines2s l)^"\n"
    | clause2s (clauseName, BC_INCLUDES(l)) = clauseName^"\n"^(machines2s l)^"\n"
    | clause2s (clauseName, BC_PROMOTES(l)) = clauseName^"\n"^(machines2s l)^"\n"
    | clause2s (clauseName, BC_EXTENDS(l)) = clauseName^"\n"^(machines2s l)^"\n"
    | clause2s (clauseName, BC_USES(l)) = clauseName^"\n"^(machines2s l)^"\n"

    | clause2s (clauseName, BC_CCONSTANTS(l)) = clauseName^"\n\t"^(tokenList2s l)^"\n\n"
    | clause2s (clauseName, BC_ACONSTANTS(l)) = clauseName^"\n\t"^(tokenList2s l)^"\n\n"
    | clause2s (clauseName, BC_CVARIABLES(l)) = clauseName^"\n\t"^(tokenList2s l)^"\n\n"
    | clause2s (clauseName, BC_AVARIABLES(l)) = clauseName^"\n\t"^(tokenList2s l)^"\n\n"

    | clause2s (clauseName, BC_SETS(l)) = 
      let
        fun  set2s (BT_Deferred(s)) = s
          | set2s (BT_Enum(s, elts)) = s^" = {"^(Utils.concatWith ", " elts)^"}"
          | set2s _ = raise BPrintError "unknown type in SETS"
      in
        clauseName^"\n\t"^(Utils.concatWith "; " (List.map set2s l))^"\n\n"
      end
    | clause2s (clauseName, BC_OPERATIONS(l)) = clauseName^"\n"^(Utils.concatWith ";\n\n" (List.map operation2s l))^"\n"
    | clause2s (clauseName, BC_INITIALISATION(s)) = clauseName^"\n"^(substitution2s 1 s)^"\n\n"

  and
    operation2s (BOp(name, [], [], subs)) =
      (tabs 1)^name^" =\n"^
      (substitution2s 2 subs)
    | operation2s (BOp(name, [], inputs, subs)) =
      (tabs 1)^name^"("^(tokenList2s inputs)^") =\n"^
      (substitution2s 2 subs)
    | operation2s (BOp(name, outputs, [], subs)) =
      (tabs 1)^(tokenList2s outputs)^" <-- "^name^" =\n"^
      (substitution2s 2 subs)
    | operation2s (BOp(name, outputs, inputs, subs)) = 
      (tabs 1)^(tokenList2s outputs)^" <-- "^name^"("^(tokenList2s inputs)^") =\n"^
      (substitution2s 2 subs)
  and
    substitution2s n (BS_Block(s)) =
      (tabs n)^"BEGIN\n"^
      (substitution2s (n+1) s)^"\n"^
      (tabs n)^"END"
    | substitution2s n (BS_Identity) = (tabs n)^"skip\n"
    | substitution2s n (BS_Precondition(p, s)) = 
      (tabs n)^"PRE\n"^
      (predicate2s (n+1) p)^
      (tabs n)^"THEN\n"^
      (substitution2s (n+1) s)^"\n"^
      (tabs n)^"END"
    | substitution2s n (BS_Assertion(p, s)) =
      (tabs n)^"PRE\n"^
      (predicate2s (n+1) p)^
      (tabs n)^"THEN\n"^
      (substitution2s (n+1) s)^"\n"^
      (tabs n)^"END"
    | substitution2s n (BS_Choice(l)) = 
      let
        fun choice_sub [] = raise BPrintError ""
          | choice_sub [s] = (substitution2s (n+1) s)^"\n"
          | choice_sub (s::ss) = 
            (substitution2s (n+1) s)^"\n"^
            (tabs n)^"OR\n"^(choice_sub ss)
      in
        (tabs n)^"CHOICE\n"^
        (choice_sub l)^
        (tabs n)^"END"
      end
    | substitution2s n (BS_If([(p, s)])) = 
      (tabs n)^"IF\n"^
      (predicate2s (n+1) p)^
      (tabs n)^"THEN\n"^
      (substitution2s (n+1) s)^"\n"^
      (tabs n)^"END"
    | substitution2s n (BS_If((p,s)::l)) =
      let
        fun if_sub [(BP_list([]),ss)] =
            (tabs n)^"ELSE\n"^
            (substitution2s (n+1) ss)^"\n"^
            (tabs n)^"END"
          | if_sub [(pp, ss)] =
            (tabs n)^"ELSIF\n"^
            (predicate2s (n+1) pp)^
            (tabs n)^"THEN\n"^
            (substitution2s (n+1) ss)^"\n"^
            (tabs n)^"END"
          | if_sub ((pp,ss)::ll) =
            (tabs n)^"ELSIF\n"^
            (predicate2s (n+1) pp)^
            (tabs n)^"THEN\n"^
            (substitution2s (n+1) ss)^"\n"^
            (if_sub ll)
          | if_sub _ = raise BPrintError ""
      in
        (tabs n)^"IF\n"^
        (predicate2s (n+1) p)^
        (tabs n)^"THEN\n"^
        (substitution2s (n+1) s)^"\n"^
        (if_sub l)
      end 

    | substitution2s n (BS_Select([(p, s)])) = 
      (tabs n)^"SELECT\n"^
      (predicate2s (n+1) p)^
      (tabs n)^"THEN\n"^
      (substitution2s (n+1) s)^"\n"^
      (tabs n)^"END"
    | substitution2s n (BS_Select((p,s)::l)) =
      let
        fun select_sub [(BP_list([]),ss)] =
            (tabs n)^"ELSE\n"^
            (substitution2s (n+1) ss)^"\n"^
            (tabs n)^"END"
          | select_sub [(pp, ss)] =
            (tabs n)^"WHEN\n"^
            (predicate2s (n+1) pp)^
            (tabs n)^"THEN\n"^
            (substitution2s (n+1) ss)^"\n"^
            (tabs n)^"END"
          | select_sub ((pp,ss)::ll) =
            (tabs n)^"WHEN\n"^
            (predicate2s (n+1) pp)^
            (tabs n)^"THEN\n"^
            (substitution2s (n+1) ss)^"\n"^
            (select_sub ll)
          | select_sub _ = raise BPrintError ""
      in
        (tabs n)^"SELECT\n"^
        (predicate2s (n+1) p)^
        (tabs n)^"THEN\n"^
        (substitution2s (n+1) s)^"\n"^
        (select_sub l)
      end 
    
    | substitution2s n (BS_Case(ex,[(es, s)])) =
      (tabs n)^"CASE "^(expr2s ex)^" OF\n"^
      (tabs (n+1))^"EITHER "^(exprList2s es)^" THEN\n"^
      (substitution2s (n+2) s)^"\n"^
      (tabs (n+1))^"END\n"^
      (tabs n)^"END"
    | substitution2s n (BS_Case(ex, ((es,s)::l))) =
      let
        fun case_sub [([], ss)] =
            (tabs (n+1))^"ELSE\n"^
            (substitution2s (n+2) ss)^"\n"^
            (tabs (n+1))^"END\n"^
            (tabs n)^"END"
          | case_sub [(ees, ss)] =
            (tabs (n+1))^"OR "^(exprList2s ees)^"THEN\n"^
            (substitution2s (n+2) ss)^"\n"^
            (tabs (n+1))^"END\n"^
            (tabs n)^"END"
          | case_sub ((ees, ss)::l) = 
            (tabs (n+1))^"OR "^(exprList2s ees)^"THEN\n"^
            (substitution2s (n+2) ss)^"\n"^
            (case_sub l)
          | case_sub _ = raise BPrintError ""
      in
        (tabs n)^"CASE "^(expr2s ex)^" OF\n"^
        (tabs (n+1))^"EITHER "^(exprList2s es)^" THEN\n"^
        (substitution2s (n+2) s)^"\n"^
        (case_sub l)
      end

    | substitution2s n (BS_Any(tlst, p, s)) =
      (tabs n)^"ANY\n"^
      (tabs (n+1))^(tokenList2s tlst)^"\n"^
      (tabs n)^"WHERE\n"^
      (predicate2s (n+1) p)^
      (tabs n)^"THEN\n"^
      (substitution2s (n+1) s)^"\n"^
      (tabs n)^"END"

    | substitution2s n (BS_Let(l,s)) =
      (tabs n)^"LET\n"^
      (tabs n)^(tokenList2s (List.map (fn (x,e) => (Var [x])) l))^"\n"^
      (tabs n)^"BE\n"^
      (Utils.concatWith "\n" (List.map (fn (x,e) => ((tabs (n+1))^x^" = "^(expr2s e))) l))^"\n"^
      (tabs n)^"IN\n"^
      (substitution2s (n+1) s)^"\n"^
      (tabs n)^"END"

    | substitution2s n (BS_BecomesElt(e1,e2)) =
      (tabs n)^(expr2s e1)^" :: "^(expr2s e2)

    | substitution2s n (BS_BecomesSuchThat(es, BP_list(p))) =
      (tabs n)^(exprList2s es)^" :( "^(predicate2s_non p)^")"

    | substitution2s n (BS_Call(outputs, operation, inputs)) =
      (tabs n)^(exprList2s outputs)^" <-- "^(token2s operation)^"("^(exprList2s inputs)^")"

    | substitution2s n (BS_BecomesEqual(e1, e2)) =
      (tabs n)^(expr2s e1)^" := "^(expr2s e2)

    | substitution2s n (BS_BecomesEqual_list(e1, e2)) =
      (tabs n)^(exprList2s e1)^" := "^(exprList2s e2)

    | substitution2s n (BS_Simultaneous l) =
      Utils.concatWith " ||\n" (List.map (substitution2s n) l)

    | substitution2s _ _ = raise BPrintError "unknown substitution"
    
  and
    machines2s [] = raise BPrintError "empty machine list"
    | machines2s [BMchInst(v, es)] = "\t"^(token2s v)^(if es = [] then "" else "("^(exprList2s es)^")")^"\n"
    | machines2s ((BMchInst(v, es))::rest) = "\t"^(token2s v)^(if es = [] then "" else "("^(exprList2s es)^")")^",\n"^(machines2s rest)
  and
    predicate2s _ (BP_list([])) = raise BPrintError "empty predicate"
    | predicate2s n (BP_list([e])) = (tabs n)^(expr2s e)^"\n"
    | predicate2s n (BP_list(e::es)) = 
      let
        val s = if #1(priOf e) < 40 then (tabs n)^"("^(expr2s e)^")" else (tabs n)^(expr2s e)
        val ss = List.map (fn x => if #1(priOf x) <= 40 then (tabs n)^"("^(expr2s x)^")" else (tabs n)^(expr2s x)) es
      in
        (Utils.concatWith " &\n" (s::ss))^"\n"
      end
        
  and
    expr2s (BE_Leaf(_, token)) = token2s token

    | expr2s (BE_Node1(_, Keyword "Reverse", e)) = 
      if #1(priOf e) <= 230 then
        "("^(expr2s e)^")~"
      else
        (expr2s e)^"~"
    | expr2s (BE_Node1(_, Keyword "UMinus", e)) = 
      if #1(priOf e) <= 210 then
        "-("^(expr2s e)^")"
      else
        "-"^(expr2s e)
    | expr2s (BE_Node1(_, Reserved s, e)) = s^"("^(expr2s e)^")"

    | expr2s (BE_Node2(_, Reserved "mod", e1, e2)) =
      let
        val p1 = #1(priOf e1)
        val p2 = #1(priOf e2)
      in
        (if p1 < 190 then "("^(expr2s e1)^")" else expr2s e1)^" mod "^
        (if p2 <= 190 then "("^(expr2s e2)^")" else expr2s e2)
      end
    | expr2s (BE_Node2(_, Reserved s, e1, e2)) = s^"("^(expr2s e1)^", "^(expr2s e2)^")"
    | expr2s (BE_Node2(_, Keyword s, e1, e2)) =
      let
        val (p, a) = priOf_t (Keyword s)
        val p1 = #1(priOf e1)
        val p2 = #1(priOf e2)
        val opr = getKeywordOp (Keyword s)
      in
        if a = Priority.L then
          (if p1 < p then "("^(expr2s e1)^")" else expr2s e1)^" "^opr^" "^
          (if p2 <= p then "("^(expr2s e2)^")" else expr2s e2)
        else
          (if p1 <= p then "("^(expr2s e1)^")" else expr2s e1)^" "^opr^" "^
          (if p2 < p then "("^(expr2s e2)^")" else expr2s e2)
      end

    
    | expr2s (BE_Fnc(_, e1, e2)) = (
        if #1(priOf e1) < 230 then 
          "("^(expr2s e1)^")" 
        else
          case e1 of
            BE_RcAc(_) => "("^(expr2s e1)^")"
          | BE_Img(_) => "("^(expr2s e1)^")"
          | _ => expr2s e1)^"("^(expr2s e2)^")"
    | expr2s (BE_Img(_, e1, e2)) = (
        if #1(priOf e1) < 230 then 
          "("^(expr2s e1)^")" 
        else
          case e1 of
            BE_RcAc(_) => "("^(expr2s e1)^")"
          | BE_Img(_) => "("^(expr2s e1)^")"
          | _ => expr2s e1)^"["^(expr2s e2)^"]"
    | expr2s (BE_NodeN(_, Reserved s, es)) = s^"("^(exprList2s es)^")"
    | expr2s (BE_Bool(BP_list(l))) = "bool("^(predicate2s_non l)^")"
    
    | expr2s (BE_ExSet(_, [])) = "{}"
    | expr2s (BE_ExSet(_, l)) = "{"^(exprList2s l)^"}"

    | expr2s (BE_InSet(_, v, BP_list(p))) = "{"^(tokenList2s v)^" | "^(predicate2s_non p)^"}"
    
    | expr2s (BE_Seq(_, [])) = "[]"
    | expr2s (BE_Seq(_, e)) = "["^(exprList2s e)^"]"

    | expr2s (BE_ForAny([],_,_)) = raise BPrintError "missing variables of \"!\""
    | expr2s (BE_ForAny([x], BP_list(p1), BP_list(p2))) = "!"^(token2s x)^".("^(predicate2s_non p1)^" => "^(predicate2s_non p2)^")"
    | expr2s (BE_ForAny(xs, BP_list(p1), BP_list(p2))) = "!("^(tokenList2s xs)^").("^(predicate2s_non p1)^" => "^(predicate2s_non p2)^")"

    | expr2s (BE_Exists([],_)) = raise BPrintError "missing variables of \"#\""
    | expr2s (BE_Exists([x], BP_list(p))) = "#"^(token2s x)^".("^(predicate2s_non p)^")"
    | expr2s (BE_Exists(xs, BP_list(p))) = "#("^(tokenList2s xs)^").("^(predicate2s_non p)^")"

    | expr2s (BE_Lambda(_, xs, BP_list p, e)) = lambdas2s "%" xs p e
    | expr2s (BE_Sigma(_, xs, BP_list p, e)) = sigmas2s "SIGMA" xs p e
    | expr2s (BE_Pi(_, xs, BP_list p, e)) = sigmas2s "PI" xs p e
    | expr2s (BE_Inter(_, xs, BP_list p, e)) = lambdas2s "INTER" xs p e
    | expr2s (BE_Union(_, xs, BP_list p, e)) = lambdas2s "UNION" xs p e

    | expr2s (BE_Struct(_, l)) =
      let
        fun fields [] = raise BPrintError "empty struct"
          | fields [(s,e)] = 
            if #1(priOf e) < 120 then s^":("^(expr2s e)^")" else s^":"^(expr2s e)
          | fields ((s,e)::rest) =
            if #1(priOf e) < 120 then s^":("^(expr2s e)^"), " else s^":"^(expr2s e)^", "^(fields rest)
      in
        "struct("^(fields l)^")"
      end
    
    | expr2s (BE_Rec(_,l)) =
      let
        fun unwrapLabel NONE = ""
          | unwrapLabel (SOME s) = s^":" 
        fun fields [] = raise BPrintError "empty struct"
          | fields [(s_opt,e)] = 
            if #1(priOf e) < 120 then (unwrapLabel s_opt)^"("^(expr2s e)^")" else (unwrapLabel s_opt)^(expr2s e)
          | fields ((s_opt,e)::rest) =
            if #1(priOf e) < 120 then (unwrapLabel s_opt)^"("^(expr2s e)^"), " else (unwrapLabel s_opt)^(expr2s e)^", "^(fields rest)
      in
        "rec("^(fields l)^")"
      end
    | expr2s (BE_RcAc(_, e, s)) = (expr2s e)^s
    | expr2s _ = raise BPrintError "unknown expression"

  and
    sigmas2s kw x p e = kw^" "^(token2s x)^".("^(predicate2s_non p)^" | "^(expr2s e)^")"
  and
    lambdas2s "%" [x] p e = "%"^(token2s x)^".("^(predicate2s_non p)^" | "^(expr2s e)^")"
    | lambdas2s kw xs p e = kw^"("^(tokenList2s xs)^".("^(predicate2s_non p)^" | "^(expr2s e)^")"
  and
    predicate2s_non [] = raise BPrintError "empty predicate"
    | predicate2s_non (e::es) =
      let
        val s = if #1(priOf e) < 40 then "("^(expr2s e)^")" else expr2s e
        val ss = List.map (fn x => if #1(priOf x) <=40 then "("^(expr2s x)^")" else expr2s x) es
      in
        Utils.concatWith " & " (s::ss)
      end
  and
    exprList2s el =
      let
        val sl = List.map (fn x => if #1(priOf x) <=115 then "("^(expr2s x)^")" else expr2s x) el
      in
        Utils.concatWith ", " sl
      end
  and
    tokenList2s l = Utils.concatWith ", " (List.map token2s l)
  and
    token2s (Var l) = renamed2s l
    | token2s (IntegerLiteral n) = IntInf.toString n
    | token2s (StringLiteral s) = "\""^s^"\""
    | token2s (RealLiteral r) = BReal.toString r
    | token2s (Reserved s) = s
    (*     | token2s (Keyword "EmpSet") = "{}"
    | token2s (Keyword "EmpSeq") = "[]" *)
    | token2s _ = raise BPrintError ""
  and
    renamed2s [] = raise BPrintError "empty variable name"
    | renamed2s [x] = x
    | renamed2s (x::xs) = x^"."^(renamed2s xs)
end


