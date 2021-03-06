structure Extract =
struct
	exception ExtractError of string
  fun find_clause cname clauses =
    let
      val clause = List.find (fn (s, _) => s=cname) clauses
    in
      if clause <> NONE then
        valOf(clause)
      else
        raise ExtractError ("POG error : missing " ^ cname ^ " clause in model")
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
    | model_var_list _ = raise ExtractError "POG error : this is not model"
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
        | extract_values _ = raise ExtractError "POG error : including expression except \"Eq\" in VALUES"
      in
        case #2(valclause) of
          (BC_VALUES (BP_list vallist)) => extract_values vallist
        | _                             => raise ExtractError "POG error : missing expression list in VALUES clause"
      end
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
      | _ => raise ExtractError "POG error : wrong machine name in IMPORTS clause"
  and
    lib_tree_list [] = []
    | lib_tree_list (BMchInst(Var varlist, arglist) :: mchlist) =
      let
        val (libname, libtree) = lib_tree varlist
        val pelist = lib_param_eqlist libtree arglist
        val rwlibtree = Replace.replace_values libtree (pelist @ [libname])
      in
        rwlibtree :: (lib_tree_list mchlist)
      end
  and
    lib_param_eqlist (BMch(_, paramlist, _)) arglist =
      let
        fun arg_eq_param ((Var [param]) :: paramlist) (arg :: alist) =
          (param, arg) :: (arg_eq_param paramlist alist)
        | arg_eq_param [] [] = []
        | arg_eq_param _ _ = raise ExtractError "POG error : wrong number argument for imported machine"
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
          raise ExtractError "POG error : model variable and implementation variable are not one-to-one correspondence"
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
          raise ExtractError "POG error : multiple substitution or no subsutitution including target var in model"
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
      (* (1.???????????????, 2.??????or??????, 3.????????????, 4.(x:=y)??????????????????, 5.?????????, 6.?????????, 7.??????, 8.????????????) *)
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
    candidate_library_operation modelvar (modelopinfo : (string * string * BExpr list * BSubstitution * string * BToken list * BToken list * BSubstitution)) vlinkl =
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
  and
    candidate_library_operation2 modelvar (modelopinfo : (string * string * BExpr list * BSubstitution * string * BToken list * BToken list * BSubstitution)) vlinkl =
      let
        val mll = List.find (fn (x, _, _) => x=modelvar) vlinkl
        val (_, linkvar, lib) = if mll<>NONE then (valOf mll) else ("", "", NONE)
        val liboplist = if mll<>NONE then (library_operation_infolist linkvar (valOf lib)) else []
        (* val liboplist = if mll<>NONE then (library_operation_infolist linkvar (valOf lib)) else [] *)
        
        
      in
        List.filter (define_or_refine (#2(modelopinfo))) liboplist
      end
end