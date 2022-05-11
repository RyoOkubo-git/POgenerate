structure ProofObligationGenerator =
struct
	exception ProofObligationGeneratorError of string
  fun po_generate (model as BMch(_, mchparams, _)) imp =
    let
      val velist = Extract.values_equal_list imp
      val rwmch = Replace.replace_values model velist
      val rwimp = Replace.replace_values imp velist
      val modelvar = Extract.model_var_list model
      val linkinv = Extract.link_invariant modelvar rwimp
      val importmchs = Extract.imports_machine_list rwimp
      val linkvars = List.map (Extract.remove_not_variables mchparams) (List.map Extract.remove_same_variables (List.map Extract.variables_from_expression linkinv))
      val vlinkl = Extract.link_vars_and_libraries modelvar linkvars importmchs
      val modelopinfo = Extract.model_operation_info (hd modelvar) rwmch
      val constraints = ("CONSTRAINTS", Extract.model_constraints model)
      val variables = ("ABSTRACT_VARIABLES", BC_AVARIABLES ((Extract.model_variables model) @ List.foldr (fn (x, y) => x @ y) [] (List.map Extract.model_variables importmchs)))
      val invaliant = ("INVARIANT", BC_INVARIANT (BP_list ((Extract.model_invariant model) @ List.foldr (fn (x, y) => x @ y) [] (List.map Extract.model_invariant importmchs) @ linkinv)))
      val inits = (Extract.model_initialisation model) @ (List.foldr (fn (x, y) => x @ y) [] (List.map Extract.model_initialisation importmchs))
      val initialisation = if (length inits) > 1 then ("INITIALISATION", BC_INITIALISATION (BS_Simultaneous inits))
                           else if (length inits) = 1 then ("INITIALISATION", BC_INITIALISATION (hd inits))
                           else ("INITIALISATION", BC_INITIALISATION (BS_Simultaneous [])) 
      val liboplist = Extract.candidate_library_operation2 (hd modelvar) modelopinfo vlinkl
      val libopinfolist = List.map (po_generate_individual_operation modelopinfo) liboplist
    in
      libopinfolist
    end
  and
    po_generate_individual_operation modelopinfo (libop as OPInfo(opname, returns, arguments, subs) : PGType) =
      let
        val mparams = Extract.model_substitution_parameter (#4(modelopinfo))
        val replacelistlist = combination_params arguments mparams
      in
        List.map (aplly_replace_library_substitutions opname returns arguments subs) replacelistlist
      end
  and
    aplly_replace_library_substitutions opname returns arguments subs replacelist =
      let
        fun replace_PGInfo ((PGInfo(subtype, prelist, (idlist, anyconstraints), iflist, subst)) :: ls) rl =
          let
            val npre = Replace.replace_expr_list rl prelist
            val nany = Replace.replace_expr_list rl anyconstraints
            val nif = Replace.replace_expr_list rl iflist
            val nsub = Replace.replace_subst rl subst
          in
            (PGInfo(subtype, npre, (idlist, nany), nif, nsub) :: (replace_PGInfo ls rl))
          end
        | replace_PGInfo [] _ = []
      in
        OPInfo(opname, returns, arguments, replace_PGInfo subs replacelist)
      end
  and
    combination_params (lparams : BToken list) (mparams : BExpr list) =
    let
      fun token2string (Var [x] :: tl) =  x :: (token2string tl)
      | token2string [] = []
      val lstring = token2string lparams
      fun comb nlist [] _ = [nlist]
      | comb (nlist : string list) (slist : string list) (next : string option) =
        if next = NONE then List.foldr (fn (x, y) => x @ y) [] (List.map (comb nlist slist) (List.map (fn (x) => SOME(x)) slist))
        else
          let 
            val nextslist = List.filter (fn x => x<>(valOf next)) slist
          in
            if nextslist = nil then [nlist @ [(valOf next)]]
            else List.foldr (fn (x, y) => x @ y) [] (List.map (comb (nlist @ [(valOf next)]) nextslist)  (List.map (fn (x) => SOME(x)) nextslist))
          end
      val permutation = comb [] lstring NONE
      fun make_pair (a :: al) (b :: bl) =
        (b, a) :: (make_pair al bl)
      | make_pair [] [] = []
      | make_pair _ _ = raise ProofObligationGeneratorError "wrong arguments and parameter"
      val listforreplace = List.map (make_pair mparams) permutation
    in
      listforreplace
      (* lstring *)
    end
end