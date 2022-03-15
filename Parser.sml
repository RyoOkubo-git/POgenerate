signature PARSER =
sig
  exception ParserParseError of string
  val parse : BToken list -> BComponent
  val p_expr : BToken list -> BToken list * BExpr
end

structure Parser :> PARSER =
struct
  exception ParserParseError of string
  fun rmend alltks = 
      case (rev alltks) of 
        ((Reserved "END")::tks) => (rev tks)
      | _ => raise ParserParseError "missing END"
  and (* val parse : BToken list -> BComponent *)
    parse ((Reserved "MACHINE")::(Var [machinename])::LBracket::btokens) = 
      let
        fun parse_sub ((Var x)::(Keyword "Comma")::rest) =
            let
              val (vv,rr) = parse_sub rest
            in
              (((Var x)::vv),rr)
            end
          | parse_sub ((Var x)::RBracket::rest) = ([Var x], rest)
          | parse_sub _ = raise ParserParseError "parse error in MACHINE parameter"
        val (v,r) = parse_sub btokens 
      in
        BMch (machinename, v, (p_clauses (rmend r)))
      end

    | parse ((Reserved "MACHINE")::(Var [machinename])::btokens) = BMch (machinename, [],(p_clauses (rmend btokens)))
    | parse _ = raise ParserParseError "parse error in MACHINE parameter"
  and
    (* val p_clauses : BToken list -> BClause list *)
    p_clauses [] = [] 
    | p_clauses btokens =
      let
        fun separateClauses btks =
            let
              fun sc_sub ((Reserved x)::xs) =
                  let
                    val ret = sc_sub xs
                  in 
                    if ret = [] then
                      [[Reserved x]]
                    else
                      if List.exists (fn (s,pri) => x=s) Keywords.clauseKeywords then
                        []::((Reserved x)::(hd ret))::(tl ret)
                      else
                        ((Reserved x)::(hd ret))::(tl ret)
                  end
                | sc_sub (x::xs) = 
                  let
                    val ret = sc_sub xs
                  in
                    if ret = [] then
                      [[x]]
                    else
                      (x::(hd ret))::(tl ret)
                  end
                | sc_sub [] = [[]]
            in
              tl (sc_sub btks)
            end
        fun clauses_sub [] = []
          | clauses_sub btkslst =
            case (hd btkslst) of
              (Reserved "CONSTRAINTS")::rest        => ("CONSTRAINTS",p_constraints rest) :: (clauses_sub (tl btkslst))
            | (Reserved "PROPERTIES")::rest         => ("PROPERTIES",p_properties rest) :: (clauses_sub (tl btkslst))
            | (Reserved "INVARIANT")::rest          => ("INVARIANT",p_invariant rest) :: (clauses_sub (tl btkslst))
            | (Reserved "ASSERTIONS")::rest         => ("ASSERTIONS",p_assertions rest) :: (clauses_sub (tl btkslst))

            | (Reserved "SEES")::rest               => ("SEES",p_sees rest) :: (clauses_sub (tl btkslst))
            | (Reserved "INCLUDES")::rest           => ("INCLUDES",p_includes rest) :: (clauses_sub (tl btkslst))
            | (Reserved "PROMOTES")::rest           => ("PROMOTES",p_promotes rest) :: (clauses_sub (tl btkslst))
            | (Reserved "EXTENDS")::rest            => ("EXTENDS",p_extends rest) :: (clauses_sub (tl btkslst))
            | (Reserved "USES")::rest               => ("USES",p_uses rest) :: (clauses_sub (tl btkslst))

            | (Reserved "CONCRETE_CONSTANTS")::rest => ("CONCRETE_CONSTANTS",p_cconstants rest) :: (clauses_sub (tl btkslst))
            | (Reserved "ABSTRACT_CONSTANTS")::rest => ("ABSTRACT_CONSTANTS",p_aconstants rest) :: (clauses_sub (tl btkslst))
            | (Reserved "CONSTANTS")::rest          => ("CONCRETE_CONSTANTS",p_cconstants rest) :: (clauses_sub (tl btkslst))
            | (Reserved "CONCRETE_VARIABLES")::rest => ("CONCRETE_VARIABLES",p_cvariables rest) :: (clauses_sub (tl btkslst))
            | (Reserved "ABSTRACT_VARIABLES")::rest => ("ABSTRACT_VARIABLES",p_avariables rest) :: (clauses_sub (tl btkslst))
            | (Reserved "VARIABLES")::rest          => ("ABSTRACT_VARIABLES",p_avariables rest) :: (clauses_sub (tl btkslst))

            | (Reserved "SETS")::rest               => ("SETS",p_sets rest) :: (clauses_sub (tl btkslst))
            | (Reserved "INITIALISATION")::rest     => ("INITIALISATION",p_initialisation rest) :: (clauses_sub (tl btkslst))
            | (Reserved "OPERATIONS")::rest         => ("OPERATIONS",p_operations rest) :: (clauses_sub (tl btkslst))
            | _ => raise ParserParseError "unknown clause keyword"
      in
        clauses_sub (separateClauses btokens)
      end
  and
    p_constraints btokens = 
      let
        val (rest, p) = p_predicate_list btokens 
      in
        if rest = [] then
          BC_CONSTRAINTS p
        else
          raise ParserParseError "extra tokens in CONSTRAINTS clause"
      end
  and
    p_properties btokens = 
      let
        val (rest, p) = p_predicate_list btokens 
      in
        if rest = [] then
          BC_PROPERTIES p
        else
          raise ParserParseError "extra tokens in PROPERTIES clause"
      end
  and
    p_invariant btokens = 
      let
        val (rest, p) = p_predicate_list btokens 
      in
        if rest = [] then
          BC_INVARIANT p
        else
          raise ParserParseError "extra tokens in INVARIANT clause"
      end
  and
    p_assertions btokens = 
      let
        val (rest, p) = p_predicate_list btokens 
      in
        if rest = [] then
          BC_ASSERTIONS p
        else
          raise ParserParseError "extra tokens in ASSERTIONS clause"
      end
  and
    p_sees btokens = BC_SEES(p_machine_list btokens)
  and
    p_includes btokens = BC_INCLUDES(p_machine_list btokens)
  and
    p_promotes btokens = BC_PROMOTES(p_machine_list btokens)
  and
    p_extends btokens = BC_EXTENDS(p_machine_list btokens)
  and
    p_uses btokens = BC_USES(p_machine_list btokens)
  and
    p_cconstants btokens = BC_CCONSTANTS(p_var_list btokens)
  and
    p_aconstants btokens = BC_ACONSTANTS(p_var_list btokens)
  and
    p_cvariables btokens = BC_CVARIABLES(p_var_list btokens)
  and
    p_avariables btokens = BC_AVARIABLES(p_var_list btokens)
  and
    p_sets btokens = 
      let
        fun sets_sub [] = []
          |sets_sub ((Var [x])::(Keyword "Eq")::(Keyword "StartSet")::rest) =
            let
              fun sets_enum_elements ((Var [xx])::(Keyword "EndSet")::rr) = (rr,[xx])
                | sets_enum_elements ((Var [xx])::(Keyword "Semicoron")::rr) = 
                  let
                    val (rnext, enext) = sets_enum_elements rr
                  in
                    (rnext, xx::enext)
                  end
                | sets_enum_elements _ = raise ParserParseError "parse error in enumset in SETS"
              val (r,e) = sets_enum_elements rest
            in
              (BT_Enum (x,e)) :: sets_sub r
            end
          | sets_sub ((Var [x])::rest) = (BT_Deferred x)::(sets_sub rest)
          | sets_sub ((Keyword "Semicoron")::rest) = sets_sub rest
          | sets_sub _ = raise ParserParseError "parse error in SETS"
      in
        BC_SETS(sets_sub btokens)
      end
  and
    p_initialisation btokens =
      let
        val (rest, s) = p_substitution btokens
      in
        if rest = [] then
          BC_INITIALISATION (s)
        else
          raise ParserParseError "extra tokens in INITIALISATION"
      end
  and
    p_operations btokens = 
      let
        fun operations_sub [] = []
          (*操作間のセミコロンは飛ばす*)
          (*合成関数のセミコロン演算子を飛ばさないよう要改良*)
          | operations_sub ((Keyword "Semicoron")::rest) = operations_sub rest
          (*outputなし、inputなし*)
          | operations_sub ((Var [x])::(Keyword "Eq")::rest) =
            let
              val (r,s) = p_substitution rest
            in
              BOp(x,[],[],s) :: operations_sub r
            end
          (*output複数*)
          | operations_sub ((Var x)::(Keyword "Comma")::rest) = 
            let
              val (BOp(n,oo,i,s)::ops) = (operations_sub rest)
            in
              BOp(n,(Var x)::oo,i,s)::ops
            end
          (*output1個*)
          | operations_sub ((Var x)::(Keyword "Output")::rest) =
            let
              val (BOp(n,_,i,s)::ops) = operations_sub rest
            in
              BOp(n,[Var x],i,s)::ops
            end
          (*outputなし、inputあり*)
          | operations_sub ((Var [x])::LBracket::rest) =
            let
              fun input_parameters ((Var y)::RBracket::(Keyword "Eq")::rr) = (rr,[Var y])
                | input_parameters ((Var y)::(Keyword "Comma")::rr) =
                  let
                    val (rrr,ee) = input_parameters rr
                  in
                    (rrr,(Var y)::ee)
                  end
                | input_parameters _ = raise ParserParseError "failed to parse OPERATION header"
              val (rs,e) = input_parameters rest
              val (r,s) = p_substitution rs
            in
              BOp(x,[],e,s) :: (operations_sub r)
            end
          | operations_sub _ = raise ParserParseError "error in OPERATIONS clause"
      in  
        BC_OPERATIONS(operations_sub btokens)
      end
  and
    (*末尾まで*)
    p_var_list btokens = List.filter (Utils.neqto (Keyword "Comma")) btokens
  and
    p_machine_list ((Var x)::LBracket::btokens) = 
      let
        val (rest1, ex1) = get_next_ee 115 btokens
        fun paramlist ((Keyword "Comma")::btks) =
            let
              val (r, e) = get_next_ee 115 btks
              val (rr, es) = paramlist r
            in
              (rr, e::es)
            end
          | paramlist (RBracket::btks) = (btks, [])
          | paramlist _ = raise ParserParseError ""
        val (rest2, exs) = paramlist rest1
        val mc = BMchInst(Var x, ex1::exs)
      in
        case rest2 of
          [] => [mc]
        | ((Keyword "Comma")::btks) => mc::(p_machine_list btks)
        | _ => raise ParserParseError "failed to parse instanciated machine parameter"
      end
    | p_machine_list ((Var x)::(Keyword "Comma")::btokens) = (BMchInst(Var x, []))::(p_machine_list btokens)
    | p_machine_list [Var x] = [BMchInst(Var x, [])]
    | p_machine_list _ = raise ParserParseError "failed to parse machine list"
  and
    (*該当部分のみ*)(* BToken list -> (BToken list * BSubstitution)*)
    p_substitution [] = raise ParserParseError "missing Substitution"
    | p_substitution btokens = 
      let 
        fun substitution_sub btks = 
            let
              val (r,s) = p_substitution_simple btks 
            in
              if r <> [] andalso hd r = Keyword "Parallel" then 
                let
                  val (rr,ss) = substitution_sub (tl r) 
                in
                  (rr,s::ss)
                end
              else
                (r,[s])
            end
        fun flattenParallel [] = []
          | flattenParallel ((BS_Simultaneous x)::xs) = x@(flattenParallel xs)
          | flattenParallel (x::xs) = x::(flattenParallel xs)
        val (rest, subs) = substitution_sub btokens 
      in
        if length subs = 1 then (rest,(hd subs)) else (rest, BS_Simultaneous (Utils.repeatApply flattenParallel subs))
      end
  and
    p_substitution_simple ((Reserved "BEGIN")::btokens) =
      let
        val (r,s) = p_substitution btokens
      in
        if hd r = Reserved "END" then
          (tl r, BS_Block s)
        else
          raise ParserParseError "missing END"
      end
    | p_substitution_simple ((Reserved "skip")::rest) = (rest, BS_Identity)
    | p_substitution_simple ((Reserved "PRE")::rest) = 
      let
        val (r, ptoken) = Utils.firstSlice (Utils.eqto (Reserved "THEN")) rest
        val p = #2(p_predicate_list ptoken)
        val (rr, s) = p_substitution r
      in
        if hd rr = Reserved "END" then
          (tl rr, BS_Precondition (p,s))
        else
          raise ParserParseError "missing END of PRE"
      end
    | p_substitution_simple ((Reserved "Assertion")::btokens) =
      let
        val (rest, ptoken) = Utils.firstSlice (Utils.eqto (Reserved "THEN")) btokens
        val p = #2(p_predicate_list ptoken)
        val (r, s) = p_substitution rest
      in
        if hd r = Reserved "END" then
          (tl r, BS_Assertion (p,s))
        else
          raise ParserParseError "missing END of ASSERT"
      end
    | p_substitution_simple ((Reserved "CHOICE")::btokens) = 
      let
        val (r1, s1) = p_substitution btokens
        fun
          choicesublist ((Reserved "OR")::btks) =
            let
              val (r,s) = p_substitution btks
              val (rr, ss) = choicesublist r
            in
              (rr, (s::ss))
            end
          | choicesublist ((Reserved "END")::btks) = (btks, [])
          | choicesublist _ = raise ParserParseError "missing END of CHOICE"
        val (r2, s2) = choicesublist r1
      in
        (r2, BS_Choice(s1::s2))
      end
    | p_substitution_simple ((Reserved "IF")::btokens) =
      let
        fun
          substitution_if_sub ((Reserved "IF")::rest) = substitution_if_sub ((Reserved "ELSIF")::rest)
          | substitution_if_sub ((Reserved "ELSIF")::rest) =
            let
              val (((Reserved "THEN")::r), p) = p_predicate_list rest
              val (rr, s) = p_substitution r
              val (rrr, nextbranch) = substitution_if_sub rr
            in
              (rrr,((p,s)::nextbranch))
            end
          | substitution_if_sub ((Reserved "ELSE")::rest) =
            let
              val (rr, s) = p_substitution rest
              val (rrr, nextbranch) = substitution_if_sub rr
            in
              (rrr, (((BP_list []),s)::nextbranch))
            end
          | substitution_if_sub ((Reserved "END")::rest) = (rest, [])
          | substitution_if_sub _ = raise ParserParseError "parse error in IF"
        val (resttokens, ifbranches) = substitution_if_sub ((Reserved "IF")::btokens)
      in
        (resttokens, (BS_If (ifbranches)))
      end   
    | p_substitution_simple ((Reserved "ANY")::btokens) = 
      let
        val (rest, itoken) = Utils.firstSlice (Utils.eqto(Reserved "WHERE")) btokens
        val i = p_var_list itoken
        val (r, ptoken) = Utils.firstSlice (Utils.eqto(Reserved "THEN")) rest
        val p = #2(p_predicate_list ptoken)
        val (rr, s) = p_substitution r
      in
        if hd rr = Reserved "END" then
          (tl rr, BS_Any (i,p,s))
        else 
          raise ParserParseError "missing END of ANY"
      end
    | p_substitution_simple ((Reserved "LET")::btokens) =
      let
        val (rest, itoken) = Utils.firstSlice (Utils.eqto (Reserved "BE")) btokens
        (*LET～BEは要らないので捨てる*)
        val (r,ptoken) = Utils.firstSlice (Utils.eqto (Reserved "IN")) rest
        fun tmpf ((Var [x])::(Keyword "Eq")::es) = (x,#2(p_expr es))
          | tmpf _ = raise ParserParseError "invalid equation in BE of LET"
        val p = List.map tmpf (Utils.chopList (Utils.eqto (Keyword "And")) ptoken)
        val (rr, s) = p_substitution r
      in
        if hd rr = Reserved "END" then
          (tl rr, BS_Let(p,s))
        else
          raise ParserParseError "missing END of LET"
      end
    | p_substitution_simple ((Var x)::resttokens) = 
      let
        fun 
          lvar_list ((Var y)::LBracket::r) =
            let
              fun 
                lvar_fpara (LBracket::rr) =
                  let
                    val (rrr, ex) = p_expr rr
                  in
                    if (hd rrr)=RBracket then
                      let
                        val (rrrr, lfps) = lvar_fpara (tl rrr)
                      in
                        (rrrr, ex::lfps)
                      end
                    else
                      raise ParserParseError "missing RIGHT BRACKET"
                  end
                | lvar_fpara rr = (rr,[])
              fun 
                lvar_ftree f [] = f
                | lvar_ftree f (e::es) = lvar_ftree (BE_Fnc (NONE, f, e)) es
              val fps = lvar_fpara (LBracket::r)
              val res = lvar_list (#1(fps))
            in
              (#1(res),(lvar_ftree (BE_Leaf(NONE,Var y)) (#2(fps)))::(#2(res))) 
            end
          | lvar_list (recordtokens as ((Var y)::(Keyword "AccessRecordField")::btokens)) =
            let
              fun 
                lvar_rfield ((Var [z])::(Keyword "AccessRecordField")::rr) =
                  let
                    val (rrr, flst) = lvar_rfield rr
                  in
                    (rrr, z::flst)
                  end
                | lvar_rfield ((Var [z])::rr) = (rr,[z])
                | lvar_rfield rr = raise ParserParseError "missing record field identifier"
              fun
                lvar_rtree rf [] = rf
                |  lvar_rtree rf (e::es) = lvar_rtree (BE_RcAc (NONE,rf, e)) es
              val (r1, rfs) = lvar_rfield recordtokens
              val (r2, res) = lvar_list r1
            in
              (r2, (lvar_rtree (BE_Leaf(NONE, Var [hd rfs])) (tl rfs))::res)
            end
          | lvar_list (Keyword "Comma"::r) = lvar_list r
          | lvar_list ((Var y)::r) = 
            let
              val (rr, lvs) = lvar_list r
            in
              (rr, (BE_Leaf (NONE, Var y))::lvs)
            end 
          | lvar_list r = (r, [])
        val ((sop::rest),lvars) = lvar_list ((Var x)::resttokens)
        fun 
          lrvar lvs (Keyword "Coron") (LBracket::btks) =
            let
              val (r,p) = p_predicate_list btks
            in
              if (hd r) = RBracket then
                (tl r, BS_BecomesSuchThat(lvars, p))
              else
                raise ParserParseError "missing RIGHT BRACKET"
            end
          | lrvar lvs (Keyword "BeEqualTo") btks =
            let
              fun rvar_list (bts as (z::zs)) =(*コンマで繋がれた右辺のリスト化*)
                  let
                    val (rr, rextree) = p_expr bts
                    fun listing_rex (BE_Node2(_, Keyword "Comma", e1, e2)) = (listing_rex e1) @ [e2]
                      | listing_rex e = [e]
                  in
                    (rr, listing_rex rextree)
                  end
                | rvar_list [] = raise ParserParseError "missing Lhs of substitution"
              val (r, rvs) = rvar_list btks
              fun listing_substitutions [] [] = []
                | listing_substitutions (lv::lvs) (rv::rvs) =  BS_BecomesEqual(lv,rv)::(listing_substitutions lvs rvs)
                | listing_substitutions _ _ = raise ParserParseError "unbalance substitution"
            in
              (r, BS_Simultaneous(listing_substitutions lvs rvs))
            end
          | lrvar lvs (Keyword "BeEltOf") btks =
            let
              fun make_maplet_tree e1 [] = e1
                | make_maplet_tree e1 (e2::es) = make_maplet_tree (BE_Node2(NONE, Keyword "Maplet",e1, e2)) es
              val (r, rex) = p_expr btks
            in
              (r, BS_BecomesElt(make_maplet_tree (hd lvs) (tl lvs), rex))
            end
          | lrvar lvs (Keyword "Output") ((Var y)::LBracket::btks) =
            let
              val (r, extree) = p_expr btks
              fun listing_inputs (BE_Node2(_, Keyword "Comma", e1, e2)) = (listing_inputs e1) @ [e2]
                | listing_inputs e = [e]
            in
              if (hd r) = RBracket then
                (r, BS_Call(lvs, Var y, listing_inputs extree))
              else
                raise ParserParseError "missing RIGHT BRACKET"
            end
          | lrvar lvs (Keyword "Output") ((Var y)::btks) = (btks, BS_Call(lvs, Var y, []))
          | lrvar lvs (Keyword "Output") _ = raise ParserParseError "invalid operation calling"
          | lrvar _ _ _ = raise ParserParseError "invalid substitution operator"(**)(*DEFINITIONS節で利用する*)
      in
        lrvar lvars sop rest
      end
    | p_substitution_simple ((Reserved "SELECT")::btokens) =
      let
        fun
          substitution_select_sub ((Reserved "SELECT")::rest) = substitution_select_sub ((Reserved "WHEN")::rest)
          | substitution_select_sub ((Reserved "WHEN")::rest) =
            let
              val (((Reserved "THEN")::r), p) = p_predicate_list rest
              val (rr, s) = p_substitution r
              val (rrr, nextbranch) = substitution_select_sub rr
            in
              (rrr,((p,s)::nextbranch))
            end
          | substitution_select_sub ((Reserved "ELSE")::rest) =
            let
              val (rr, s) = p_substitution rest
              val (rrr, nextbranch) = substitution_select_sub rr
            in
              (rrr, (((BP_list []),s)::nextbranch))
            end
          | substitution_select_sub ((Reserved "END")::rest) = (rest, [])
          | substitution_select_sub _ = raise ParserParseError "parse error in SELECT"
        val (resttokens, selectbranches) = substitution_select_sub ((Reserved "SELECT")::btokens)
      in
        (resttokens, (BS_Select (selectbranches)))
      end
    | p_substitution_simple ((Reserved "CASE")::rest) =
      let
        val (((Reserved "OF")::r1), e) = p_expr rest
        fun 
          simple_term_list ((Reserved "THEN")::r) = (r, [])
          | simple_term_list ((Keyword "Comma")::r) = simple_term_list r
          | simple_term_list (stx::r) = 
            let
              val res = simple_term_list r
            in
              ((#1(res)),(BE_Leaf(NONE, stx))::(#2(res)))
            end
          | simple_term_list [] = raise ParserParseError "missing THEN of CASE"
        fun
          substitution_case_sub ((Reserved "EITHER")::r) = substitution_case_sub ((Reserved "OR")::r)
          | substitution_case_sub ((Reserved "OR")::r) =
            let
              val (rr, stl) = simple_term_list r
              val (rrr, ss) = p_substitution rr
              val (rrrr, ncase) = substitution_case_sub rrr
            in
              (rrrr, ((stl, ss)::ncase))
            end
          | substitution_case_sub ((Reserved "ELSE")::r) =
            let
              val (rrr, ss) = p_substitution r
              val (rrrr, ncase) = substitution_case_sub rrr
            in
              (rrrr, (([], ss)::ncase))
            end
          | substitution_case_sub ((Reserved "END")::(Reserved "END")::r) = (r, [])
          | substitution_case_sub _ = raise ParserParseError "missing END of CASE"
        val caseResult = substitution_case_sub r1
      in
        ((#1(caseResult)),BS_Case(e,(#2(caseResult))))
      end
    | p_substitution_simple _ = raise ParserParseError "failed to parse substitution"
  and
    (*p_expr BToken list -> (BToken list * BExpr *)
    p_expr [] = raise ParserParseError "missing Expression"
    | p_expr btokens = p_eeleft 20 btokens
  and
    p_eeleft _ [] = raise ParserParseError "missing Expression"
    | p_eeleft pri btokens = 
      let
        val oplst = List.map (fn x=> (#2(x))) (List.filter (fn x => (#3(x))=pri) Priority.exprOperators)
        val pnext = get_next_ee pri
        fun eeleft_sub_lst [] = ([], [])
          | eeleft_sub_lst (opleft::btks) = 
            if
              List.exists (Utils.eqto opleft) oplst
            then
              let
                val (rr,ee) = pnext btks
                val (rrr, nexte) = eeleft_sub_lst rr
              in
                (rrr, (opleft,ee)::nexte)
              end
            else
              ((opleft::btks), [])
        fun eeleft_sub_tree e1 ((opleft, e2)::roe) = eeleft_sub_tree (BE_Node2(NONE, opleft, e1, e2)) roe
          | eeleft_sub_tree e1 [] = e1
        val (rest1, firstexpr) = pnext btokens
        val (rest2, exprs) = eeleft_sub_lst rest1
      in
        (rest2, eeleft_sub_tree firstexpr exprs)
      end
  and
    p_eeright pri [] = raise ParserParseError "missing expresspion"
    | p_eeright pri btokens = 
      let
        val oplst = List.map (fn x=> (#2(x))) (List.filter (fn x => (#3(x))=pri) Priority.exprOperators)
        val pnext = get_next_ee pri
        val (rest1, firstexpr) = pnext btokens
      in
        if rest1 = [] orelse (not (List.exists (Utils.eqto (hd rest1)) oplst)) then
          (rest1, firstexpr)
        else
          let
            val (opright::rest) = rest1
            val (rest2, exprs) = p_eeright pri rest
          in
            (rest2, (BE_Node2(NONE, opright, firstexpr, exprs)))
          end
      end
  and
    p_funcs btokens =
      let
        datatype P_FUNCS_DATA = PF_Evl of BExpr | PF_Img of BExpr | PF_Rvs
        val (rest1, funcexpr) = p_recordaccess btokens
        fun
          funcs_sub_lst (LBracket::btks) = 
            let
              val (r, e) = p_expr btks
            in
              if r=[] orelse (hd r)<>RBracket then
                raise ParserParseError "missing RIGHT BRACKET of function parameter"
              else
                let
                  val (rr, elst) = funcs_sub_lst (tl r)
                in
                  (rr, (PF_Evl(e))::elst)
                end
            end
          | funcs_sub_lst ((Keyword "StartSeq")::btks) = 
            let
              val (r, e) = p_expr btks
            in
              if r=[] orelse (hd r)<>(Keyword "EndSeq") then
                raise ParserParseError "missing \"]\" of function image"
              else
                let
                  val (rr, elst) = funcs_sub_lst (tl r)
                in
                  (rr, (PF_Img(e))::elst)
                end
            end
          | funcs_sub_lst ((Keyword "Reverse")::btks) = 
            let
              val (r, elst) = funcs_sub_lst btks
            in
              (r, PF_Rvs::elst)
            end
          | funcs_sub_lst x = (x, [])
        fun funcs_sub_tree f [] = f
          | funcs_sub_tree f ((PF_Evl(e))::es) = funcs_sub_tree (BE_Fnc (NONE, f, e)) es
          | funcs_sub_tree f ((PF_Img(e))::es) = funcs_sub_tree (BE_Img (NONE, f, e)) es
          | funcs_sub_tree f (PF_Rvs::es) = funcs_sub_tree (BE_Node1(NONE, Keyword "Reverse", f)) es
        val (rest2, paramlst) = funcs_sub_lst rest1
      in
        (rest2, funcs_sub_tree funcexpr paramlst)
      end
  and
    p_uminus ((Keyword "Minus")::btokens) = 
      let
        val (rest, ex) = (get_next_ee 210) btokens
      in
        (rest, BE_Node1(NONE,(Keyword "UMinus"),ex))
      end
    | p_uminus btokens = (get_next_ee 210) btokens
  and
    p_recordaccess [] = raise ParserParseError "missing Expression"
    | p_recordaccess btokens = 
      let
        val pnext = get_next_ee 250
        fun ra_sub_lst ((Keyword "AccessRecordField")::(Var [x])::btks) = 
            let
              val (rr, nextx) = ra_sub_lst btks
            in
              (rr, x::nextx)
            end
          | ra_sub_lst btks = (btks, [])
        fun ra_sub_tree e (x::xs) = ra_sub_tree (BE_RcAc(NONE,e,x)) xs
          | ra_sub_tree e [] = e
        val (rest1, firstexpr) = pnext btokens
        val (rest2, ss) = ra_sub_lst rest1
      in
        (rest2, ra_sub_tree firstexpr ss)
      end
  and
    p_primary (LBracket::btokens) = 
      let
        val (rest, brexpr) = p_expr btokens
      in
        if rest = [] orelse (hd rest)<>RBracket then
          raise ParserParseError "missing RIGHT BRACKET"
        else
          ((tl rest), brexpr)
      end
    | p_primary ((Var x)::btokens) = (btokens, BE_Leaf(NONE, (Var x)))
    
    | p_primary ((IntegerLiteral x)::btokens) = (btokens, BE_Leaf(SOME(BT_Integer), (IntegerLiteral x)))
    | p_primary ((Reserved "MAXINT")::btokens) = (btokens, BE_Leaf(SOME(BT_Integer), (Reserved "MAXINT")))
    | p_primary ((Reserved "MININT")::btokens) = (btokens, BE_Leaf(SOME(BT_Integer), (Reserved "MININT")))
    | p_primary ((Reserved "INTEGER")::btokens) = (btokens, BE_Leaf(SOME(BT_Power(SOME(BT_Integer))), (Reserved "INTEGER")))
    | p_primary ((Reserved "NATURAL")::btokens) = (btokens, BE_Leaf(SOME(BT_Power(SOME(BT_Integer))), (Reserved "NATURAL")))
    | p_primary ((Reserved "NATURAL1")::btokens) = (btokens, BE_Leaf(SOME(BT_Power(SOME(BT_Integer))), (Reserved "NATURAL1")))
    | p_primary ((Reserved "INT")::btokens) = (btokens, BE_Leaf(SOME(BT_Power(SOME(BT_Integer))), (Reserved "INT")))
    | p_primary ((Reserved "NAT")::btokens) = (btokens, BE_Leaf(SOME(BT_Power(SOME(BT_Integer))), (Reserved "NAT")))
    | p_primary ((Reserved "NAT1")::btokens) = (btokens, BE_Leaf(SOME(BT_Power(SOME(BT_Integer))), (Reserved "NAT1")))

    | p_primary ((StringLiteral x)::btokens) = (btokens, BE_Leaf(SOME(BT_String), (StringLiteral x)))
    | p_primary ((Reserved "STRING")::btokens) = (btokens, BE_Leaf(SOME(BT_Power(SOME(BT_String))), (Reserved "STRING")))
    
    | p_primary ((RealLiteral x)::btokens) = (btokens, BE_Leaf(SOME(BT_Real), (RealLiteral x)))
    | p_primary ((Reserved "REAL")::btokens) = (btokens, BE_Leaf(SOME(BT_Power(SOME(BT_Real))), (Reserved "REAL")))

    | p_primary ((Reserved "TRUE")::btokens) = (btokens, BE_Leaf(SOME(BT_Bool), (Reserved "TRUE")))
    | p_primary ((Reserved "FALSE")::btokens) = (btokens, BE_Leaf(SOME(BT_Bool), (Reserved "FALSE")))
    | p_primary ((Reserved "BOOL")::btokens) = (btokens, BE_Leaf(SOME(BT_Power(SOME(BT_Bool))), (Reserved "BOOL")))

    | p_primary ((Keyword "EmpSet")::btokens) = (btokens, BE_ExSet(SOME(BT_Power(NONE)), []))
    | p_primary ((Keyword "EmpSeq")::btokens) = (btokens, BE_Seq(SOME(BT_Power(SOME(BT_Pair(SOME(BT_Integer),NONE)))), []))

    | p_primary ((Keyword "StartSet")::btokens) = 
      let
        val (rest1, expr) = p_expr btokens
        fun listing_elements (BE_Node2(_,(Keyword "Comma"),e1,e2)) = (listing_elements e1)@[e2]
          | listing_elements e = [e]
      in
        case rest1 of
          ((Keyword "EndSet")::rest2) => (rest2, BE_ExSet(NONE, listing_elements expr))
        | ((Keyword "VBar")::rest2) => 
          let
            val (rest3, p) = p_predicate_list rest2
          in
            if rest3 = [] orelse (hd rest3) <> (Keyword "EndSet") then
              raise ParserParseError "missing \"}\" of set"
            else
              (tl rest3, BE_InSet(NONE, List.map (fn x => case x of (BE_Leaf(_, v)) => v | _ => raise ParserParseError "")(listing_elements expr), p))
          end
        | _ => raise ParserParseError "missing \"}\" of set"        
      end
    | p_primary ((Keyword "StartSeq")::btokens) = 
      let
        val (rest, expr) = p_expr btokens
        fun listing_elements (BE_Node2(_,(Keyword "Comma"),e1,e2)) = (listing_elements e1)@[e2]
          | listing_elements e = [e]
      in
        if rest = [] orelse (hd rest) <> (Keyword "EndSeq") then
          raise ParserParseError "missing \"]\" of seq"
        else
          (tl rest, BE_Seq(NONE, listing_elements expr))
      end
    | p_primary ((Keyword "ForAny")::(Var x)::(Keyword "Dot")::LBracket::btokens) = 
      let
        val (rest, allp) = p_predicate btokens
      in
        case allp of
          BE_Node2(_, Keyword "Implies", p1, p2) =>
            if rest = [] orelse (hd rest)<>RBracket then
              raise ParserParseError "missing RIGHT BRACKET in Predicate of \"!\""
            else
              (tl rest, BE_ForAny([Var x],listing_predicates p1, listing_predicates p2))
        | _ => raise ParserParseError "\"=>\" is not used in Predicate of \"!\""
      end
    | p_primary ((Keyword "ForAny")::LBracket::(Var x)::btokens) =
      let
        fun bindexprlist ((Keyword "Comma")::(Var y)::r) = 
            let 
              val (rr, lst) = bindexprlist r
            in
              (rr, (Var y)::lst)
            end
          | bindexprlist (RBracket::(Keyword "Dot")::LBracket::r) = (r, [])
          | bindexprlist _ = raise ParserParseError "failed to parse binding of \"!\""
        val (rest1, exls) = bindexprlist btokens
        val (rest2, allp) = p_predicate rest1
      in
        case allp of
          BE_Node2(_, Keyword "Implies", p1, p2) =>
            if rest2=[] orelse (hd rest2)<>RBracket then
              raise ParserParseError "missing RIGHT BRACKET of Predicate of \"!\""
            else
              (tl rest2, BE_ForAny(((Var x)::exls),listing_predicates p1,listing_predicates p2))
        | _ => raise ParserParseError "\"=>\" is not used in Predicate of \"!\""
      end
    | p_primary ((Keyword "ForAny"):: _ ) = 
      raise ParserParseError "failed to parse contents of \"!\""

    | p_primary ((Keyword "Exists")::(Var x)::(Keyword "Dot")::LBracket::btokens) = 
      let
        val (rest, allp) = p_predicate_list btokens
      in
        if rest = [] orelse (hd rest)<>RBracket then
          raise ParserParseError "missing RIGHT BRACKET in Predicate of \"#\""
        else
          (tl rest, BE_Exists([Var x],allp))
      end
    | p_primary ((Keyword "Exists")::LBracket::(Var x)::btokens) =
      let
        fun bindexprlist ((Keyword "Comma")::(Var y)::r) = 
            let 
              val (rr, lst) = bindexprlist r
            in
              (rr, ((Var y)::lst))
            end
          | bindexprlist (RBracket::(Keyword "Dot")::LBracket::r) = (r, [])
          | bindexprlist _ = raise ParserParseError "failed to parse binding of \"#\""
        val (rest1, exls) = bindexprlist btokens
        val (rest2, allp) = p_predicate_list rest1
      in
        if rest2=[] orelse (hd rest2)<>RBracket then
          raise ParserParseError "missing RIGHT BRACKET of Predicate of \"#\""
        else
          (tl rest2, BE_Exists(((Var x)::exls),allp))
      end
    | p_primary ((Keyword "Exists"):: _ ) = 
      raise ParserParseError "failed to parse contents of \"#\""
    | p_primary (btokens as ((Keyword "Lambda"):: _)) = p_lambdas btokens
    | p_primary (btokens as ((Reserved "SIGMA"):: _)) = p_sigmas btokens
    | p_primary (btokens as ((Reserved "PI"):: _)) = p_sigmas btokens
    | p_primary (btokens as ((Reserved "INTER"):: _)) = p_lambdas btokens
    | p_primary (btokens as ((Reserved "UNION"):: _)) = p_lambdas btokens
    | p_primary ((Reserved "not")::(Reserved "not")::btokens) = (*二重否定の時は外のnotの括弧は省略可能*)
      let
        val (rest, ex) = p_expr ((Reserved "not")::btokens)
      in
        (rest, BE_Node1(SOME(BT_Predicate), Reserved "not", ex))
      end
    | p_primary ((Reserved f)::LBracket::btokens) =
      if List.exists (Utils.eqto f) BuiltinFnc.biSimpleFnc_str then
        let
          val (rest, ex) = p_expr btokens
        in
          if rest = [] orelse (hd rest)<>RBracket then
            raise ParserParseError ("missing RIGHT BRACKET of "^f)
          else
            ((tl rest), BE_Node1(NONE, Reserved f, ex))
        end
      else
        if List.exists (Utils.eqto f) BuiltinFnc.bi2Fnc_str then
          let
            val (rest, eall) = p_expr btokens
          in
            if rest = [] orelse (hd rest)<>RBracket then
              raise ParserParseError ("missing RIGHT BRACKET of "^f)
            else
              case eall of
                BE_Node2(_, Keyword "Comma", e1,e2) => ((tl rest), BE_Node2(NONE, (Reserved f), e1, e2))
              | _ => raise ParserParseError ("invalid parameter of "^f)
          end
        else
          let
            fun listingCommaExprs btks =
                let
                  val (r1,e) = (get_next_ee 115) btks
                  fun lce_sub (RBracket::bt) = (bt, [])
                    | lce_sub ((Keyword "Comma")::bt) =
                      let
                        val (rr, ee) = (get_next_ee 115) bt
                        val (rrr, ees) = lce_sub rr
                      in
                        (rrr, ee::ees)
                      end
                    | lce_sub _ = raise ParserParseError "failed to parse comma-separated expressions"
                  val (r2, es) = lce_sub r1
                in
                  (r2, e::es)                  
                end
          in
            (case f of
                "son" => 
                  let
                    val (rest, exs) = listingCommaExprs btokens
                  in
                    if length exs = 3 then
                      (rest, BE_NodeN(NONE, Reserved "son", exs))
                    else
                      raise ParserParseError "invalid number of \"son()\" parameter"
                  end
              | "bin" => 
                let
                  val (rest, exs) = listingCommaExprs btokens
                in
                  if length exs = 1 orelse length exs = 3 then
                    (rest, BE_NodeN(NONE, Reserved "bin", exs))
                  else
                    raise ParserParseError "invalid number of \"bin()\" parameter"
                end
              | "struct" => 
                (case btokens of
                    ((Var x)::(Keyword "Coron")::btks)=>
                      let
                        fun pstruct_sub ((Keyword "Comma")::(Var y)::(Keyword "Coron")::bt) = 
                            let
                              val (r1, ee) = (get_next_ee 115) bt
                              val (r2, pps) = pstruct_sub r1
                            in 
                              (r2, (hd y,ee)::pps)
                            end
                          | pstruct_sub (RBracket::bt) = (bt,[])
                          | pstruct_sub _ = raise ParserParseError "failed to parse \"struct\" contents"
                        val (rest1, e) = (get_next_ee 115) btks
                        val (rest2, ps) = pstruct_sub rest1
                      in
                        (rest2, BE_Struct(NONE,(hd x, e)::ps))
                      end
                  | _ => raise ParserParseError "invalid \"struct\" contents")
              | "rec" =>
                let
                  fun prec_sub ((Keyword "Comma")::(Var y)::(Keyword "Coron")::bt) = 
                      let
                        val (r1, ee) = (get_next_ee 115) bt
                        val (r2, pps) = prec_sub r1
                      in 
                        (r2, (SOME(hd y),ee)::pps)
                      end
                    | prec_sub (RBracket::bt) = (bt,[])
                    | prec_sub bt = 
                      let
                        val (r1, ee) = (get_next_ee 115) bt
                        val (r2, pps) = prec_sub r1
                      in
                        (r2,(NONE,ee)::pps)
                      end
                in 
                  (case btokens of
                      ((Var x)::(Keyword "Coron")::btks) => 
                        let
                          val (rest1, e) = (get_next_ee 115) btks
                          val (rest2, ps) = prec_sub rest1
                        in 
                          (rest2, BE_Rec(NONE,(SOME(hd x), e)::ps))
                        end
                    | btks =>
                      let
                        val (rest1, e) = (get_next_ee 115) btks
                        val (rest2, ps) = prec_sub rest1
                      in
                        (rest2, BE_Rec(NONE,(NONE, e)::ps))
                      end
                  )
                end
              | _ => raise ParserParseError "unknown reserved token")
          end
    | p_primary _ = raise ParserParseError "failed to parse a primary expression"
  and
    p_sigmas (kw::LBracket::(Var x)::RBracket::btokens) = p_sigmas (kw::(Var x)::btokens)
    | p_sigmas (kw::(Var x)::(Keyword "Dot")::LBRacket::btokens) = 
      let
        val (rest1, p) = p_predicate_list btokens
      in
        if rest1 = [] orelse (hd rest1)<>(Keyword "VBar") then
          raise ParserParseError "missing \"|\""
        else
          let
            val (rest2, e) = p_expr (tl rest1)
          in
            if rest2 = [] orelse (hd rest2)<>RBracket then
              raise ParserParseError "missing RIGHT BRACKET"
            else
              case kw of
                (Keyword "SIGMA") => (tl rest2, BE_Sigma(NONE, Var x, p, e))
              | (Keyword "PI") => (tl rest2, BE_Pi(NONE, Var x, p, e))
              | _ => raise ParserParseError ""
          end
      end
    | p_sigmas _ = raise ParserParseError ""
  and
    p_lambdas (kw::(Var x)::(Keyword "Dot")::LBracket::btokens) = 
      let
        val (rest1, p) = p_predicate_list btokens
      in
        if rest1 = [] orelse (hd rest1)<>(Keyword "VBar") then
          raise ParserParseError "missing \"|\""
        else
          let
            val (rest2, e) = p_expr (tl rest1)
          in
            if rest2 = [] orelse (hd rest2)<>RBracket then
              raise ParserParseError "missing RIGHT BRACKET"
            else
              (tl rest2,p_lambdas2 kw [Var x] p e)
          end 
      end
    | p_lambdas (kw::LBracket::(Var x)::btokens) =
      let
        fun bindexprlist ((Keyword "Comma")::(Var y)::r) = 
            let 
              val (rr, lst) = bindexprlist r
            in
              (rr, ((Var y)::lst))
            end
          | bindexprlist (RBracket::(Keyword "Dot")::LBracket::r) = (r, [])
          | bindexprlist _ = raise ParserParseError "failed to parse binding"
        val (rest1, vls) = bindexprlist btokens
        val (rest2, p) = p_predicate_list rest1
      in
        if rest2=[] orelse (hd rest2)<>(Keyword "VBar") then
          raise ParserParseError "missing \"|\""
        else
          let
            val es = (Var x)::vls
            val (rest3, e) = p_expr (tl rest2)
          in
            if rest3 = [] orelse (hd rest3)<>RBracket then
              raise ParserParseError "missing RIGHT BRACKET"
            else
              (tl rest3, p_lambdas2 kw es p e)
          end
      end
    | p_lambdas _ = raise ParserParseError "failed to parse binding"
  and
    p_lambdas2 kw vs p e = 
      case kw of
        (Keyword "Lambda") => BE_Lambda(NONE, vs, p, e)
      | (Reserved "INTER") => BE_Inter(NONE, vs, p, e)
      | (Reserved "UNION") => BE_Union(NONE, vs, p, e)
      | _ => raise ParserParseError "unknown Lambdas"
  and
    get_next_ee 20 = p_eeleft 30
    | get_next_ee 30 = p_eeleft 40
    | get_next_ee 40 = p_eeleft 60
    | get_next_ee 60 = p_eeleft 110
    | get_next_ee 110 = p_eeleft 115
    | get_next_ee 115 = p_eeleft 125
    | get_next_ee 125 = p_eeleft 130
    | get_next_ee 130 = p_eeleft 160
    | get_next_ee 160 = p_eeleft 170
    | get_next_ee 170 = p_eeleft 180
    | get_next_ee 180 = p_eeleft 190
    | get_next_ee 190 = p_eeright 200
    | get_next_ee 200 = p_uminus
    | get_next_ee 210 = p_funcs(*f()とf~とf[]全部同じ優先順位*)
    | get_next_ee 230 = p_recordaccess
    | get_next_ee 250 = p_primary
    | get_next_ee _ = raise ParserParseError "unknown priority of operator"
  and
    p_predicate_list btokens = 
      let
        val res = p_predicate btokens
      in
        (#1(res), listing_predicates (#2(res)))
      end
  and
    listing_predicates e = 
      let
        fun listing_predicates_sub (BE_Node2(_, Keyword "And", e1, e2)) = (listing_predicates_sub e1)@(listing_predicates_sub e2)
          | listing_predicates_sub x = [x]
      in
        BP_list(listing_predicates_sub e)
      end
  and
    p_predicate btokens = p_eeleft 30 btokens
end
