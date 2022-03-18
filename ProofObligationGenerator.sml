structure ProofObligationGenerator =
struct
exception ProofObligationGeneratorError of string
	fun model_var_list (BMch(machinename, _, clauses)) =
  	let
      val avar = List.find (fn (s, _) => s="ABSTRACT_VARIABLES") clauses
    in
      if avar = NONE then
        raise ProofObligationGeneratorError "POG error : missing \"ABSTRACT_VARIABLES\" clause" 
      else
        let
          fun extract_var_list (BC_AVARIABLES varlist) = varlist
        in
          extract_var_list (#2(valOf(avar)))
        end
    end
  | model_var_list _ = raise ProofObligationGeneratorError "POG error : this is not model"
  (* and
    link_invariant ((Var x) :: varlist) *)
end