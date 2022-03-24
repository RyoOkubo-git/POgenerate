structure Replace =
struct
	exception ReplaceError of string
  fun replace_values comp eqlist =
      case comp of
        (BMch (mname, params, clauses))        => BMch (mname, params, (replace_values_sub clauses eqlist))
      | (BImp (mname, rname, params, clauses)) => BImp (mname, rname, params, (replace_values_sub clauses eqlist))
  and
    replace_values_sub [] _ = []
    | replace_values_sub (clause :: clauselist) eqlist =
      case clause of
        (cname, BC_INVARIANT (BP_list exprlist))  => (cname, BC_INVARIANT (BP_list (replace_expr_list eqlist exprlist))) :: (replace_values_sub clauselist eqlist)
      | (cname, BC_ASSERTIONS (BP_list exprlist)) => (cname, BC_ASSERTIONS (BP_list (replace_expr_list eqlist exprlist))) :: (replace_values_sub clauselist eqlist)
      | (cname, BC_SEES mchlist)                  => (cname, BC_SEES (replace_mch_list eqlist mchlist)) :: (replace_values_sub clauselist eqlist)
      | (cname, BC_INCLUDES mchlist)              => (cname, BC_INCLUDES (replace_mch_list eqlist mchlist)) :: (replace_values_sub clauselist eqlist)
      | (cname, BC_PROMOTES mchlist)              => (cname, BC_PROMOTES (replace_mch_list eqlist mchlist)) :: (replace_values_sub clauselist eqlist)
      | (cname, BC_EXTENDS mchlist)               => (cname, BC_EXTENDS (replace_mch_list eqlist mchlist)) :: (replace_values_sub clauselist eqlist)
      | (cname, BC_USES mchlist)                  => (cname, BC_USES (replace_mch_list eqlist mchlist)) :: (replace_values_sub clauselist eqlist)
      | (cname, BC_IMPORTS mchlist)               => (cname, BC_IMPORTS (replace_mch_list eqlist mchlist)) :: (replace_values_sub clauselist eqlist)
      | (cname, BC_CCONSTANTS tknlist)            => (cname, BC_CCONSTANTS (List.map (replace_token eqlist) tknlist)) :: (replace_values_sub clauselist eqlist)
      | (cname, BC_ACONSTANTS tknlist)            => (cname, BC_ACONSTANTS (List.map (replace_token eqlist) tknlist)) :: (replace_values_sub clauselist eqlist)
      | (cname, BC_CVARIABLES tknlist)            => (cname, BC_CVARIABLES (List.map (replace_token eqlist) tknlist)) :: (replace_values_sub clauselist eqlist)
      | (cname, BC_AVARIABLES tknlist)            => (cname, BC_AVARIABLES (List.map (replace_token eqlist) tknlist)) :: (replace_values_sub clauselist eqlist)
      | (cname, BC_INITIALISATION subst)          => (cname, BC_INITIALISATION (replace_subst eqlist subst)) :: (replace_values_sub clauselist eqlist)
      | (cname, BC_OPERATIONS oplist)             => (cname, BC_OPERATIONS (replace_op_list eqlist oplist)) :: (replace_values_sub clauselist eqlist)
      | other                                     => other :: (replace_values_sub clauselist eqlist)
  and
    replace_expr ("_", BE_Leaf(_, Var [prefix])) (BE_Leaf(btype, Var [varname])) =
      BE_Leaf(btype, Var [prefix ^ varname])
    | replace_expr (ident, rep) expr =
        case expr of
            BE_Leaf(btype, Var [prefix, varname])                  => BE_Leaf(btype, Var [prefix ^ "_" ^ varname])
          | BE_Leaf(btype, Var varlist)                            => if (hd varlist) = ident then rep else BE_Leaf(btype, Var varlist)
          | BE_Node1(btype, key, node)                             => BE_Node1(btype, key, replace_expr (ident, rep) node)
          | BE_Node2(btype, key, left, right)                      => BE_Node2(btype, key, replace_expr (ident, rep) left, replace_expr (ident, rep) right)
          | BE_NodeN(btype, key, nodelist)                         => BE_NodeN(btype, key, List.map (replace_expr (ident, rep)) nodelist)
          | BE_Fnc(btype,  node1, node2)                           => BE_Fnc(btype, replace_expr (ident, rep) node1, replace_expr (ident, rep) node2)
          | BE_Img(btype,  node1, node2)                           => BE_Img(btype, replace_expr (ident, rep) node1, replace_expr (ident, rep) node2)
          | BE_ExSet(btype, nodelist)                              => BE_ExSet(btype, List.map (replace_expr (ident, rep)) nodelist)
          | BE_InSet(btype, tkn, BP_list nodelist)                 => BE_InSet(btype, tkn, BP_list (List.map (replace_expr (ident, rep)) nodelist))
          | BE_Seq(btype, nodelist)                                => BE_Seq(btype, List.map (replace_expr (ident, rep)) nodelist)
          | BE_ForAny(btype, BP_list nodelist1, BP_list nodelist2) => BE_ForAny(btype, BP_list (List.map (replace_expr (ident, rep)) nodelist1), BP_list (List.map (replace_expr (ident, rep)) nodelist2))
          | BE_Exists(btype, BP_list nodelist)                     => BE_Exists(btype, BP_list (List.map (replace_expr (ident, rep)) nodelist))
          | BE_Lambda(btype, tkn, BP_list nodelist, node)          => BE_Lambda(btype, tkn, BP_list (List.map (replace_expr (ident, rep)) nodelist), replace_expr (ident, rep) node)
          | BE_Sigma(btype, tkn, BP_list nodelist, node)           => BE_Sigma(btype, tkn, BP_list (List.map (replace_expr (ident, rep)) nodelist), replace_expr (ident, rep) node)
          | BE_Pi(btype, tkn, BP_list nodelist, node)              => BE_Pi(btype, tkn, BP_list (List.map (replace_expr (ident, rep)) nodelist), replace_expr (ident, rep) node)
          | BE_Inter(btype, tkn, BP_list nodelist, node)           => BE_Inter(btype, tkn, BP_list (List.map (replace_expr (ident, rep)) nodelist), replace_expr (ident, rep) node)
          | BE_Union(btype, tkn, BP_list nodelist, node)           => BE_Union(btype, tkn, BP_list (List.map (replace_expr (ident, rep)) nodelist), replace_expr (ident, rep) node)
          | other                                                  => other
  and
    replace_expr_list eqlist (expr :: exprlist) =
      (replace_expr_eqlist eqlist expr) :: (replace_expr_list eqlist exprlist)
    | replace_expr_list _ [] = []
  and
    replace_mch_list eqlist ((BMchInst (mname, exprlist)) :: mchlist) =
      (BMchInst (mname, replace_expr_list eqlist exprlist)) :: (replace_mch_list eqlist mchlist)
    | replace_mch_list _ [] = []
  and
    replace_expr_eqlist (eq :: eqlist) expr =
      replace_expr_eqlist eqlist (replace_expr eq expr)
    | replace_expr_eqlist [] expr = expr
  and
    replace_subst eqlist subst =
      case subst of
        BS_Block(sub)                                    => BS_Block(replace_subst eqlist sub)
      | BS_Identity                                      => BS_Identity
      | BS_Precondition(BP_list exprlist, sub)           => BS_Precondition(BP_list (replace_expr_list eqlist exprlist), (replace_subst eqlist sub))
      | BS_Assertion(BP_list exprlist, sub)              => BS_Assertion(BP_list (replace_expr_list eqlist exprlist), (replace_subst eqlist sub))
      | BS_Choice(e)                                     => replace_choice eqlist e
      | BS_If(iflist)                                    => BS_If(List.map (fn ((BP_list x), y) => ((BP_list (replace_expr_list eqlist x)), replace_subst eqlist y)) iflist)
      | BS_Select(selist)                                => BS_Select(List.map (fn ((BP_list x), y) => ((BP_list (replace_expr_list eqlist x)), replace_subst eqlist y)) selist)
      | BS_Case(e)                                       => replace_case eqlist e
      | BS_Any(tkn, BP_list exprlist, sub)               => BS_Any((List.map (replace_token eqlist) tkn), BP_list (replace_expr_list eqlist exprlist), (replace_subst eqlist sub))
      | BS_Let(e)                                        => replace_let eqlist e
      | BS_BecomesElt(e)                                 => replace_becomeselt eqlist e
      | BS_BecomesSuchThat(e)                            => replace_becomessuchthat eqlist e
      | BS_Call(exprlist1, tkn, exprlist2)               => BS_Call((replace_expr_list eqlist exprlist1), tkn, (replace_expr_list eqlist exprlist2))
      | BS_BecomesEqual(e)                               => replace_becomesequal eqlist e
      | BS_BecomesEqual_list(e)                          => replace_becomesequallist eqlist e
      | BS_Simultaneous(sublist)                         => BS_Simultaneous(List.map (replace_subst eqlist) sublist)
  and
    replace_choice eqlist sublist =
      replace_subst eqlist (BS_Select(List.map (fn x => (BP_list [], x)) sublist))
  and
    replace_case eqlist (expr, calist) =
      let
        fun deploy_case e (p::plist) =
          BE_Node2(NONE, Keyword "Eq", e, p) :: (deploy_case e plist)
        | deploy_case _ [] = []
        fun link_predicate_and_substitution e (exprlist, subst) =
          let
            val prelist = deploy_case e exprlist
          in
            (BP_list prelist, subst)
          end
      in
        replace_subst eqlist (BS_If(List.map (link_predicate_and_substitution expr) calist))
      end
  and
    replace_let eqlist (lelist, sub) =
      replace_subst (lelist @ eqlist) sub
  and
    replace_becomesequal eqlist (BE_Fnc(btype1, BE_Leaf(btype2, tkn), expr2), expr3) =
      BS_BecomesEqual(BE_Leaf(btype2, replace_token eqlist tkn), BE_Node2(btype2, Keyword "OverWrite", BE_Leaf(btype2, replace_token eqlist tkn), BE_ExSet(btype2, [BE_Node2(btype2, Keyword "Maplet", replace_expr_eqlist eqlist expr2, replace_expr_eqlist eqlist expr3)])))
    | replace_becomesequal eqlist (expr1, expr2) = 
      BS_BecomesEqual(replace_expr_eqlist eqlist expr1, replace_expr_eqlist eqlist expr2)
  and
    replace_becomesequallist eqlist (exprlist1, exprlist2) =
      let
        val el1 = replace_expr_list eqlist exprlist1
        val el2 = replace_expr_list eqlist exprlist2
        fun replace_becomesequallist_sub el ((e1 :: elist1), (e2 :: elist2)) =
          BS_BecomesEqual(e1, e2) :: (replace_becomesequallist_sub el (elist1, elist2))
        | replace_becomesequallist_sub _ ([], []) = []
        | replace_becomesequallist_sub _ _ = raise ReplaceError "wrong number of becomes equal"
      in
        BS_Simultaneous(replace_becomesequallist_sub eqlist (el1, el2))
      end
  and
    replace_becomeselt eqlist (BE_Leaf(btype, Var [varname]), expr) =
      let
        val anyvar = "ANY_"^varname
      in
        BS_Any([Var [anyvar]], BP_list [BE_Node2(btype, Keyword "Coron", BE_Leaf(btype, Var [anyvar]), replace_expr_eqlist eqlist expr)], BS_BecomesEqual(BE_Leaf(btype, Var [varname]), BE_Leaf(btype, Var [anyvar]))) 
      end
  and
    replace_becomessuchthat eqlist (exprlist, BP_list prelist) =
      let
        fun expr2token eqlist (BE_Leaf(btype, vartkn) :: el) =
          let
            val (tl, anyel, sublst) = expr2token eqlist el
            val Var [newvarname] = replace_token eqlist vartkn
            val anyvar = "ANY_"^newvarname
          in
            (((Var [anyvar]) :: tl), ((newvarname, BE_Leaf(btype, Var[anyvar])) :: anyel), ((BS_BecomesEqual(BE_Leaf(btype, Var [newvarname]), BE_Leaf(btype, Var [anyvar]))) :: sublst))
          end
        | expr2token _ [] = ([], [], [])
        | expr2token _ _ = raise ReplaceError "no leaf in left of becomes such that"
        val (anytkn, anyeqlist, sublist) = expr2token eqlist exprlist
      in
        BS_Any(anytkn, BP_list(replace_expr_list (eqlist@anyeqlist) prelist),  BS_Simultaneous(sublist)) 
      end
  and
    replace_op_list eqlist (BOp(opname, ret, arg, sub) :: oplist) =
      BOp(opname, (List.map (replace_token eqlist) ret), (List.map (replace_token eqlist) arg), (replace_subst eqlist sub)) :: (replace_op_list eqlist oplist)
    | replace_op_list _ [] = []
  and
    replace_token (("_", BE_Leaf(_, Var [prefix])) :: eqlist) (Var [varname]) =
      Var [prefix ^ varname]
    | replace_token (eq :: eqlist) tkn = replace_token eqlist tkn
    | replace_token [] tkn = tkn
end