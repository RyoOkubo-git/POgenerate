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
      val liboplist = Extract.candidate_library_operation2 (hd modelvar) modelopinfo vlinkl
    in
      liboplist
    end
end