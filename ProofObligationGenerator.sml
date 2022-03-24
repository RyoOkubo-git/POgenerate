structure ProofObligationGenerator =
struct
	exception ProofObligationGeneratorError of string
  fun po_generate (model as BMch(_, mchparams, _)) imp =
    let
        val velist = values_equal_list imp
        val rwmch = replace_values model velist
        val rwimp = replace_values imp velist
        val modelvar = model_var_list model
        val linkinv = link_invariant modelvar rwimp
        val importmchs = imports_machine_list rwimp
        val linkvars = List.map (remove_not_variables mchparams) (List.map remove_same_variables (List.map variables_from_expression linkinv))
        val vlinkl = link_vars_and_libraries modelvar linkvars importmchs
        val modelopinfo = model_operation_info (hd modelvar) rwmch
        val liboplist = candidate_library_operation (hd modelvar) modelopinfo vlinkl
    in
      liboplist
    end
  and
    find_clause cname clauses =
    let
      val clause = List.find (fn (s, _) => s=cname) clauses
    in
      if clause <> NONE then
        valOf(clause)
      else
        raise ProofObligationGeneratorError ("POG error : missing " ^ cname ^ " clause in model")
      end
  and
    model_var_list (BMch(machinename, _, clauses)) =
      let
        val avclause = find_clause "ABSTRACT_VARIABLES" clauses
        fun extract_var_list (BC_AVARIABLES ((Var [mvar]) :: varlist)) = 
          mvar :: extract_var_list (BC_AVARIABLES varlist)
        | extract_var_list (BC_AVARIABLES []) = []
      in
        extract_var_list (#2(avclause))
      end
    | model_var_list _ = raise ProofObligationGeneratorError "POG error : this is not model"
  and
    link_invariant varlist (BImp(_, _, _, clauses)) =
      let
        val invclause = find_clause "INVARIANT" clauses
        fun extract_linkinv mvar (inv :: invlist) =
          if (is_tree_member mvar inv) then
            inv :: extract_linkinv mvar invlist
          else
            extract_linkinv mvar invlist
        | extract_linkinv _ [] = []
        fun extract_linkinv_list (mvar :: vlist) (Inv as (BC_INVARIANT (BP_list invlist))) =
          extract_linkinv mvar invlist @ extract_linkinv_list vlist Inv
        | extract_linkinv_list [] _ = []
      in
        extract_linkinv_list  varlist (#2(invclause))
      end
  and
    is_tree_member elem tree =
      case tree of
        BE_Leaf(_, Var varlist)                               => List.exists (fn x => x=elem) varlist
      | BE_Node1(_, _, node)                                  => is_tree_member elem node
      | BE_Node2(_, _, left, right)                           => (is_tree_member elem left) orelse (is_tree_member elem right)
      | BE_NodeN(_, _, nodelist)                              => List.foldr (fn (x, y) => x orelse y) false (List.map (is_tree_member elem) nodelist)
      | BE_Fnc(_,  node1, node2)                              => (is_tree_member elem node1) orelse (is_tree_member elem node2)
      | BE_Img(_,  node1, node2)                              => (is_tree_member elem node1) orelse (is_tree_member elem node2)
      | BE_ExSet(_, nodelist)                                 => List.foldr (fn (x, y) => x orelse y) false (List.map (is_tree_member elem) nodelist)
      | BE_InSet(_, _, BP_list nodelist)                      => List.foldr (fn (x, y) => x orelse y) false (List.map (is_tree_member elem) nodelist)
      | BE_Seq(_, nodelist)                                   => List.foldr (fn (x, y) => x orelse y) false (List.map (is_tree_member elem) nodelist)
      | BE_ForAny(_, BP_list nodelist1, BP_list nodelist2)    => List.foldr (fn (x, y) => x orelse y) false (List.map (is_tree_member elem) (nodelist1 @ nodelist2))
      | BE_Exists(_, BP_list nodelist)                        => List.foldr (fn (x, y) => x orelse y) false (List.map (is_tree_member elem) nodelist)
      | BE_Lambda(_, _, BP_list nodelist, node)               => List.foldr (fn (x, y) => x orelse y) false (List.map (is_tree_member elem) (node :: nodelist))
      | BE_Sigma(_, _, BP_list nodelist, node)                => List.foldr (fn (x, y) => x orelse y) false (List.map (is_tree_member elem) (node :: nodelist))
      | BE_Pi(_, _, BP_list nodelist, node)                   => List.foldr (fn (x, y) => x orelse y) false (List.map (is_tree_member elem) (node :: nodelist))
      | BE_Inter(_, _, BP_list nodelist, node)                => List.foldr (fn (x, y) => x orelse y) false (List.map (is_tree_member elem) (node :: nodelist))
      | BE_Union(_, _, BP_list nodelist, node)                => List.foldr (fn (x, y) => x orelse y) false (List.map (is_tree_member elem) (node :: nodelist))
      | _                                                     => false
  and
    values_equal_list (BImp (_, _, _, clauses)) =
      let
        val valclause = find_clause "VALUES" clauses
        fun extract_values ((BE_Node2 (_, Keyword "Eq", BE_Leaf (_, Var varlist), expr)) :: vallist) = (hd(varlist), expr) :: extract_values vallist
        | extract_values [] = []
        | extract_values _ = raise ProofObligationGeneratorError "POG error : including expression except \"Eq\" in VALUES"
      in
        case #2(valclause) of
          (BC_VALUES (BP_list vallist)) => extract_values vallist
        | _                             => raise ProofObligationGeneratorError "POG error : missing expression list in VALUES clause"
      end
  and
    replace_values comp eqlist =
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
        BS_BecomesEqual(BE_Fnc(btype1, BE_Leaf(btype2, tkn), expr2), expr3) => BS_BecomesEqual(BE_Leaf(btype2, replace_token eqlist tkn), BE_Node2(btype2, Keyword "OverWrite", BE_Leaf(btype2, replace_token eqlist tkn), BE_ExSet(btype2, [BE_Node2(btype2, Keyword "Maplet", replace_expr_eqlist eqlist expr2, replace_expr_eqlist eqlist expr3)])))
      | BS_Block(sub)                                    => BS_Block(replace_subst eqlist sub)
      | BS_Identity                                      => BS_Identity
      | BS_Precondition(BP_list exprlist, sub)           => BS_Precondition(BP_list (replace_expr_list eqlist exprlist), (replace_subst eqlist sub))
      | BS_Assertion(BP_list exprlist, sub)              => BS_Assertion(BP_list (replace_expr_list eqlist exprlist), (replace_subst eqlist sub))
      | BS_Choice(sublist)                               => BS_Choice(List.map (replace_subst eqlist) sublist)
      | BS_If(iflist)                                    => BS_If(List.map (fn ((BP_list x), y) => ((BP_list (replace_expr_list eqlist x)), replace_subst eqlist y)) iflist)
      | BS_Select(selist)                                => BS_Select(List.map (fn ((BP_list x), y) => ((BP_list (replace_expr_list eqlist x)), replace_subst eqlist y)) selist)
      | BS_Case(expr, calist)                            => BS_Case((replace_expr_eqlist eqlist expr), (List.map (fn (x, y) => (replace_expr_list eqlist x, replace_subst eqlist y)) calist))
      | BS_Any(tkn, BP_list exprlist, sub)               => BS_Any((List.map (replace_token eqlist) tkn), BP_list (replace_expr_list eqlist exprlist), (replace_subst eqlist sub))
      | BS_Let(lelist, sub)                              => BS_Let((List.map (fn (x, y) => (x, replace_expr_eqlist eqlist y)) lelist), (replace_subst eqlist sub))
      | BS_BecomesElt(expr1, expr2)                      => BS_BecomesElt((replace_expr_eqlist eqlist expr1), (replace_expr_eqlist eqlist expr2))
      | BS_BecomesSuchThat(exprlist1, BP_list exprlist2) => BS_BecomesSuchThat((replace_expr_list eqlist exprlist1), BP_list (replace_expr_list eqlist exprlist2))
      | BS_Call(exprlist1, tkn, exprlist2)               => BS_Call((replace_expr_list eqlist exprlist1), tkn, (replace_expr_list eqlist exprlist2))
      | BS_BecomesEqual(expr1, expr2)                    => BS_BecomesEqual(replace_expr_eqlist eqlist expr1, replace_expr_eqlist eqlist expr2)
      | BS_BecomesEqual_list(exprlist1, exprlist2)       => BS_BecomesEqual_list((replace_expr_list eqlist exprlist1), (replace_expr_list eqlist exprlist2))
      | BS_Simultaneous(sublist)                         => BS_Simultaneous(List.map (replace_subst eqlist) sublist)
  and
    replace_op_list eqlist (BOp(opname, ret, arg, sub) :: oplist) =
      BOp(opname, (List.map (replace_token eqlist) ret), (List.map (replace_token eqlist) arg), (replace_subst eqlist sub)) :: (replace_op_list eqlist oplist)
    | replace_op_list _ [] = []
  and
    replace_token (("_", BE_Leaf(_, Var [prefix])) :: eqlist) (Var [varname]) =
      Var [prefix ^ varname]
    | replace_token (eq :: eqlist) tkn = replace_token eqlist tkn
    | replace_token [] tkn = tkn
  and
    imports_machine_list (BImp (_, _, _, clauses)) =
      let
        val impclause = find_clause "IMPORTS" clauses
      in
        case impclause of
          (_, (BC_IMPORTS mchlist)) => lib_tree_list mchlist
      end
  and
    lib_tree (varlist) =
    case List.length(varlist) of
        1 => (("_", BE_Leaf(NONE, Var [""])), Parser.parse(lexer (Utils.fileToString ((hd varlist) ^ ".mch"))))
      | 2 => (("_", BE_Leaf(NONE, Var [(hd varlist) ^ "_"])), Parser.parse(lexer (Utils.fileToString ((hd (tl varlist)) ^ ".mch"))))
      | _ => raise ProofObligationGeneratorError "POG error : wrong machine name in IMPORTS clause"
  and
    lib_tree_list [] = []
    | lib_tree_list (BMchInst(Var varlist, arglist) :: mchlist) =
      let
        val (libname, libtree) = lib_tree varlist
        val pelist = lib_param_eqlist libtree arglist
        val rwlibtree = replace_values libtree (pelist @ [libname])
      in
        rwlibtree :: (lib_tree_list mchlist)
      end
  and
    lib_param_eqlist (BMch(_, paramlist, _)) arglist =
      let
        fun arg_eq_param ((Var [param]) :: paramlist) (arg :: alist) =
          (param, arg) :: (arg_eq_param paramlist alist)
        | arg_eq_param [] [] = []
        | arg_eq_param _ _ = raise ProofObligationGeneratorError "POG error : wrong number argument for imported machine"
      in
        arg_eq_param paramlist arglist
      end
  and
    variables_from_expression expr =
      case expr of
            BE_Leaf(_, Var [ident])                                    => [ident]
          | BE_Node1(_, _, node)                                       => variables_from_expression node
          | BE_Node2(_, _, left, right)                                => (variables_from_expression left) @ (variables_from_expression right)
          | BE_NodeN(_, _, nodelist)                                   => List.foldr (fn (x,y) => x @ y) [] (List.map variables_from_expression nodelist)
          | BE_Fnc(_,  node1, node2)                                   => (variables_from_expression node1) @ (variables_from_expression node2)
          | BE_Img(_,  node1, node2)                                   => (variables_from_expression node1) @ (variables_from_expression node2)
          | BE_ExSet(_, nodelist)                                      => List.foldr (fn (x,y) => x @ y) [] (List.map variables_from_expression nodelist)
          | BE_InSet(_, tokenlist, BP_list nodelist)                   => remove_not_variables tokenlist (List.foldr (fn (x,y) => x @ y) [] (List.map variables_from_expression nodelist))
          | BE_Seq(_, nodelist)                                        => List.foldr (fn (x,y) => x @ y) [] (List.map variables_from_expression nodelist)
          | BE_ForAny(tokenlist, BP_list nodelist1, BP_list nodelist2) => remove_not_variables tokenlist (List.foldr (fn (x,y) => x @ y) [] (List.map variables_from_expression (nodelist1 @ nodelist2)))
          | BE_Exists(tokenlist, BP_list nodelist)                     => remove_not_variables tokenlist (List.foldr (fn (x,y) => x @ y) [] (List.map variables_from_expression nodelist))
          | BE_Lambda(_, tokenlist, BP_list nodelist, node)            => remove_not_variables tokenlist (List.foldr (fn (x,y) => x @ y) [] (List.map variables_from_expression (node :: nodelist)))
          | BE_Sigma(_, token, BP_list nodelist, node)                 => remove_not_variables [token] (List.foldr (fn (x,y) => x @ y) [] (List.map variables_from_expression (node :: nodelist)))
          | BE_Pi(_, token, BP_list nodelist, node)                    => remove_not_variables [token] (List.foldr (fn (x,y) => x @ y) [] (List.map variables_from_expression (node :: nodelist)))
          | BE_Inter(_, tokenlist, BP_list nodelist, node)             => remove_not_variables tokenlist (List.foldr (fn (x,y) => x @ y) [] (List.map variables_from_expression (node :: nodelist)))
          | BE_Union(_, tokenlist, BP_list nodelist, node)             => remove_not_variables tokenlist (List.foldr (fn (x,y) => x @ y) [] (List.map variables_from_expression (node :: nodelist)))
          | _                                                          => []
  and
    remove_not_variables (((Var [nvname]) :: tokenlist) : BToken list) (varlist : string list) =
      remove_not_variables tokenlist (List.filter (fn x => x<>nvname) varlist)
    | remove_not_variables [] varlist = varlist
  and
    remove_same_variables ((v :: varlist) : string list) =
      v :: (remove_same_variables (List.filter (fn x => x<>v) varlist))
    | remove_same_variables [] = []
  and
    link_vars_and_libraries ((mvar :: modelvar) : string list) (linklists : string list list) (libraries : BComponent list) =
      let
        val link = List.find (fn x => (List.exists (fn y => y=mvar) x)) linklists
        fun link_vars_and_libraries_sub mv ll libs =
          let
            val lv = hd (List.filter (fn x => x<>mv) ll)
            val lib = List.find (fn x => (List.exists (fn y => y=lv) (model_var_list x))) libs
          in
            (mv, lv, lib)
          end
      in 
        if link = NONE then
          link_vars_and_libraries modelvar linklists libraries
        else if (List.length (valOf link)) = 2 then
          (link_vars_and_libraries_sub mvar (valOf link) libraries) :: (link_vars_and_libraries modelvar linklists libraries)
        else
          raise ProofObligationGeneratorError "POG error : model variable and implementation variable are not one-to-one correspondence"
      end
    | link_vars_and_libraries [] _ _ = []
  and
    model_operation_info (targetvar : string) (BMch(_, _, clauses)) =
      let
        val opclause = find_clause "OPERATIONS" clauses
        val modelop = case opclause of (_, BC_OPERATIONS[mo]) => mo
        val modelopinfo = operation_info targetvar modelop
      in
        if List.length modelopinfo = 1 then
          hd modelopinfo
        else
          raise ProofObligationGeneratorError "POG error : multiple substitution or no subsutitution including target var in model"
      end
  and
    library_operation_infolist (targetvar : string) (BMch(_, _, clauses)) =
      let
        val opclause = find_clause "OPERATIONS" clauses
        val libop = case opclause of (_, BC_OPERATIONS lo) => lo
      in
        List.foldr (fn (x,y) => x @ y) [] (List.map (operation_info targetvar) libop)
      end
  and
    operation_info (targetvar : string)  (BOp(opname, ret, arg, subst) : BOperation) =
    let
      val sublist = substitution_including_targetvar targetvar subst
      val precon = precondition_of_operation subst
    in
      List.map (fn x => (targetvar, #1(x), precon, #2(x), opname, ret, arg, subst)) sublist
      (* (1.目的の変数, 2.代入or参照, 3.事前条件, 4.(x:=y)の形の代入文, 5.操作名, 6.返り値, 7.引数, 8.操作全体) *)
    end
  and
    substitution_including_targetvar (targetvar : string) (subst : BSubstitution) =
    case subst of
        BS_BecomesEqual(BE_Leaf(btype, Var [defvar]), expr2) => if targetvar=defvar then [("dainyu", BS_BecomesEqual(BE_Leaf(btype, Var [defvar]), expr2))] 
                                                                else if is_tree_member targetvar expr2 then [("sanshou", BS_BecomesEqual(BE_Leaf(btype, Var [defvar]), expr2))]
                                                                else []
      | BS_Call(exprlist1, tkn, exprlist2)                   => if List.foldr (fn (x, y) => x orelse y) false (List.map (is_tree_member targetvar) exprlist1) then [("dainyu", BS_Call(exprlist1, tkn, exprlist2))] 
                                                                else if List.foldr (fn (x, y) => x orelse y) false (List.map (is_tree_member targetvar) exprlist2) then [("sanshou", BS_Call(exprlist1, tkn, exprlist2))]
                                                                else []
      | BS_BecomesEqual_list(exprlist1, exprlist2)           => if List.foldr (fn (x, y) => x orelse y) false (List.map (is_tree_member targetvar) exprlist1) then [("dainyu", BS_BecomesEqual_list(exprlist1, exprlist2))]
                                                                else if List.foldr (fn (x, y) => x orelse y) false (List.map (is_tree_member targetvar) exprlist2) then [("sanshou", BS_BecomesEqual_list(exprlist1, exprlist2))]
                                                                else []
      | BS_Block(sub)                                        => substitution_including_targetvar targetvar sub
      | BS_Identity                                          => []
      | BS_Precondition(_, sub)                              => substitution_including_targetvar targetvar sub
      | BS_Assertion(_, sub)                                 => substitution_including_targetvar targetvar sub
      | BS_Choice(sublist)                                   => List.foldr (fn (x, y) => x @ y) [] (List.map (substitution_including_targetvar targetvar) sublist)
      | BS_If(iflist)                                        => List.foldr (fn (x, y) => x @ y) [] (List.map (fn (_, x) => (substitution_including_targetvar targetvar x)) iflist)
      | BS_Select(selist)                                    => List.foldr (fn (x, y) => x @ y) [] (List.map (fn (_, x) => (substitution_including_targetvar targetvar x)) selist)
      | BS_Case(_, calist)                                   => List.foldr (fn (x, y) => x @ y) [] (List.map (fn (_, x) => (substitution_including_targetvar targetvar x)) calist)
      | BS_Any(_, _, sub)                                    => substitution_including_targetvar targetvar sub
      | BS_Let(_, sub)                                       => substitution_including_targetvar targetvar sub
      | BS_BecomesElt(_, _)                                  => []
      | BS_BecomesSuchThat(_, _)                             => []
      | BS_Simultaneous(sublist)                             => List.foldr (fn (x, y) => x @ y) [] (List.map (substitution_including_targetvar targetvar) sublist)
      | _                                                    => []
  and
    precondition_of_operation subst =
      case subst of
        BS_Precondition(BP_list plist, _) => plist
      | _ => []
  and
    candidate_library_operation modelvar modelopinfo vlinkl =
      let
        val mll = List.find (fn (x, _, _) => x=modelvar) vlinkl
        val (_, linkvar, lib) = if mll<>NONE then (valOf mll) else ("", "", NONE)
        val liboplist = if mll<>NONE then (library_operation_infolist linkvar (valOf lib)) else []
        fun number_of_parameter_in_substitution mvar (BS_BecomesEqual(_, expr)) =
          List.length (remove_not_variables [Var [mvar]] (variables_from_expression expr))
        fun equal_var (Var varname1) (Var varname2) = (varname1 = varname2)
        fun define_or_refine mdr (_, ldr, _, BS_BecomesEqual(BE_Leaf(_, varname),_), _, ret, _, _) =
          if mdr = "dainyu" andalso ldr = "dainyu" then true
          else if mdr = "sanshou" andalso ldr = "sanshou" andalso List.exists (fn x => equal_var x varname) ret then true
          else false
        val nofp = number_of_parameter_in_substitution modelvar (#4(modelopinfo))
        val liboplist2 = List.filter (fn x => ((List.length (#7(x))) = nofp) ) liboplist
      in
        List.filter (define_or_refine (#2(modelopinfo))) liboplist
      end
end