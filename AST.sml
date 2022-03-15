datatype BToken =
  LBracket 
| RBracket 
| Var of string list 
| IntegerLiteral of IntInf.int 
| StringLiteral of string 
| RealLiteral of BReal.bReal 
| Keyword of string 
| Reserved of string 
| Other of string 
| Bbtrue 
| Bbfalse
and
  BType = 
  BT_Real 
| BT_Integer 
| BT_String 
| BT_Float 
| BT_Bool 
| BT_Power of BType option 
| BT_Pair of BType option * BType option 
| BT_Struct of (BType(*option*) * string) list 
| BT_Deferred of string 
| BT_Enum of string * string list 
| BT_Predicate
  (*関数、関係はBT_Power(BT_Pair)*)
  (* 集合定数"INTEGER"の型はBT_Power(BT_Integer) *)
and
  BExpr =
  BE_Leaf of (BType option * BToken) (* リテラル, 変数*)
| BE_Node1 of (BType option * BToken * BExpr) (*単項演算子、card、bool等*)
| BE_Node2 of (BType option * BToken * BExpr * BExpr) (*二項演算式,2引数組込関数*)
| BE_NodeN of (BType option * BToken * BExpr list) (*son(),bin()*)
| BE_Fnc of (BType option * BExpr * BExpr) (*関数適用*)
| BE_Img of (BType option * BExpr * BExpr) (*像*)
| BE_Bool of BPredicate
| BE_ExSet of (BType option * BExpr list) (*集合の外延表記*)
| BE_InSet of (BType option * BToken list * BPredicate) (*集合の内包表記*)(**)
| BE_Seq of (BType option * BExpr list) (*シーケンス*)
| BE_ForAny of (BToken list * BPredicate * BPredicate)
| BE_Exists of (BToken list * BPredicate)
| BE_Lambda of (BType option * BToken list * BPredicate * BExpr)(**)
| BE_Sigma of (BType option * BToken * BPredicate * BExpr)(**)
| BE_Pi of (BType option * BToken * BPredicate * BExpr)(**)
| BE_Inter of (BType option * BToken list * BPredicate * BExpr)(**)
| BE_Union of (BType option * BToken list * BPredicate * BExpr)(**)
| BE_Struct of BType option * (string * BExpr) list
| BE_Rec of BType option * (string option * BExpr) list(**)
| BE_RcAc of BType option * BExpr * string
and
  BPredicate = BP_list of BExpr list (*&...*)
and
  BClause = 
  (*制約条件系・Assertion*)
  BC_CONSTRAINTS of BPredicate 
| BC_PROPERTIES of BPredicate
| BC_INVARIANT of BPredicate
| BC_ASSERTIONS of BPredicate

(*モジュール系*)
(*モデル展開後にはこれらは登場しない*)
| BC_SEES of BMchInstanciation list 
| BC_INCLUDES of BMchInstanciation list
| BC_PROMOTES of BMchInstanciation list
| BC_EXTENDS of BMchInstanciation list
| BC_USES of BMchInstanciation list

(*変数導入系*)
| BC_CCONSTANTS of BToken list
| BC_ACONSTANTS of BToken list
| BC_CVARIABLES of BToken list
| BC_AVARIABLES of BToken list

(*その他*)
| BC_SETS of BType list
| BC_INITIALISATION of BSubstitution
| BC_OPERATIONS of BOperation list
  (* 操作名, output parameters, input parameters, 操作 *)
and
  BComponent = BMch of string * BToken list * (string * BClause) list 
| BRef of string * string * BToken list * BClause list 
| BImp of string * string * BToken list * BClause list
and
  BOperation = BOp of string * BToken list * BToken list * BSubstitution
and
  BMchInstanciation = BMchInst of BToken * BExpr list
and
  BSubstitution = 
  BS_Block of BSubstitution(*BEGIN*)
| BS_Identity(*skip*)
| BS_Precondition of BPredicate * BSubstitution
| BS_Assertion of BPredicate * BSubstitution
| BS_Choice of BSubstitution list
| BS_If of (BPredicate * BSubstitution) list
| BS_Select of (BPredicate * BSubstitution) list
| BS_Case of BExpr * (BExpr list * BSubstitution) list
| BS_Any of (BToken list) * BPredicate * BSubstitution
| BS_Let of (string * BExpr) list * BSubstitution
| BS_BecomesElt of BExpr * BExpr
| BS_BecomesSuchThat of (BExpr list) * BPredicate
| BS_Call of (BExpr list) * BToken * (BExpr list)
| BS_BecomesEqual of BExpr * BExpr
| BS_BecomesEqual_list of (BExpr list) * (BExpr list) (* a,b := c,d *)
| BS_Simultaneous of BSubstitution list

structure AST =
struct
  fun ttos NONE = "?"
    | ttos (SOME(BT_Power(x))) = "pow("^(ttos x)^")"
    | ttos (SOME(BT_Pair(x, y))) = (ttos x)^"*"^(ttos y)
    | ttos (SOME(BT_Integer)) = "int"
    | ttos (SOME(BT_Predicate)) = "predicate"
    | ttos (SOME(BT_Real)) = "real"
    | ttos (SOME(BT_String)) = "string"
    | ttos (SOME(BT_Deferred(s))) = s
    | ttos (SOME(_)) = "other"(**)

  fun applyExprTree f (BE_Leaf(t, token)) = f (BE_Leaf(t, token))
    | applyExprTree f (BE_Node1(t, e, x)) = f (BE_Node1(t, e, applyExprTree f x))
    | applyExprTree f (BE_Node2(t, e, x, y)) = f (BE_Node2(t, e, applyExprTree f x, applyExprTree f y))
    | applyExprTree f (BE_Fnc(t, g, x)) = f (BE_Fnc(t, applyExprTree f g, applyExprTree f x))
    | applyExprTree f (BE_Img(t, g, x)) = f (BE_Img(t, applyExprTree f g, applyExprTree f x))
    | applyExprTree f (BE_NodeN(t, token, l)) = f (BE_NodeN(t, token, List.map (applyExprTree f) l))
    | applyExprTree f (BE_Bool(BP_list(l))) = f (BE_Bool(BP_list(List.map (applyExprTree f) l)))
    | applyExprTree f (BE_ExSet(t, l)) = f (BE_ExSet(t, List.map (applyExprTree f) l))
    | applyExprTree f (BE_InSet(t, l1, BP_list(l2))) = f (BE_InSet(t, l1, BP_list(List.map (applyExprTree f) l2)))
    | applyExprTree f (BE_Seq(t, l)) = f (BE_Seq(t, List.map (applyExprTree f) l))
    | applyExprTree f (BE_ForAny(l1, BP_list(l2), BP_list(l3))) = f (BE_ForAny(l1, BP_list(List.map (applyExprTree f) l2), BP_list(List.map (applyExprTree f) l3)))
    | applyExprTree f (BE_Lambda(t, l1, BP_list(l2), e)) = f (BE_Lambda(t, l1, BP_list(List.map (applyExprTree f) l2),applyExprTree f e))
    | applyExprTree f (BE_Exists(l1, BP_list(l2))) = f (BE_Exists(l1, BP_list(List.map (applyExprTree f) l2)))
    | applyExprTree f (BE_Sigma(t, l1, BP_list(l2), e)) = f (BE_Sigma(t, l1, BP_list(List.map (applyExprTree f) l2),applyExprTree f e))
    | applyExprTree f (BE_Pi(t, l1, BP_list(l2), e)) = f (BE_Pi(t, l1, BP_list(List.map (applyExprTree f) l2),applyExprTree f e))
    | applyExprTree f (BE_Inter(t, l1, BP_list(l2), e)) = f (BE_Inter(t, l1, BP_list(List.map (applyExprTree f) l2),applyExprTree f e))
    | applyExprTree f (BE_Union(t, l1, BP_list(l2), e)) = f (BE_Union(t, l1, BP_list(List.map (applyExprTree f) l2),applyExprTree f e))
    | applyExprTree f (BE_Struct(t, l)) = f (BE_Struct(t, List.map (fn (s, e) => (s, applyExprTree f e)) l))
    | applyExprTree f (BE_Rec(t, l)) = f (BE_Rec(t, List.map (fn (s, e) => (s, applyExprTree f e)) l))
    | applyExprTree f (BE_RcAc(t, e, s)) = f (BE_RcAc(t, applyExprTree f e, s))

  fun subExprTrees (BE_Leaf(t, token)) = [] : BExpr list
    | subExprTrees (BE_Node1(t, e, x)) = [x]
    | subExprTrees (BE_Node2(t, e, x, y)) = [x, y]
    | subExprTrees (BE_Fnc(t, g, x)) = [g, x]
    | subExprTrees (BE_Img(t, g, x)) = [g, x]
    | subExprTrees (BE_NodeN(t, token, l)) = l
    | subExprTrees (BE_Bool(BP_list(l))) = l
    | subExprTrees (BE_ExSet(t, l)) = l
    | subExprTrees (BE_InSet(t, l1, BP_list(l2))) = l2
    | subExprTrees (BE_Seq(t, l)) = l
    | subExprTrees (BE_ForAny(l1, BP_list(l2), BP_list(l3))) = l2@l3
    | subExprTrees (BE_Lambda(t, l1, BP_list(l2), e)) = e::l2
    | subExprTrees (BE_Exists(l1, BP_list(l2))) = l2
    | subExprTrees (BE_Sigma(t, l1, BP_list(l2), e)) = e::l2
    | subExprTrees (BE_Pi(t, l1, BP_list(l2), e)) = e::l2
    | subExprTrees (BE_Inter(t, l1, BP_list(l2), e)) = e::l2
    | subExprTrees (BE_Union(t, l1, BP_list(l2), e)) = e::l2
    | subExprTrees (BE_Struct(t, l)) = List.map (fn (s, e) => e) l
    | subExprTrees (BE_Rec(t, l)) = List.map (fn (s, e) => e) l
    | subExprTrees (BE_RcAc(t, e, s)) = [e]

  fun findExprTree f e = 
      if f e then 
        SOME(e) 
      else 
        let
          val tmp = List.find (fn x => case x of NONE => false | _=> true) (List.map (findExprTree f) (subExprTrees e))
        in
          if tmp = NONE then
            NONE
          else
            valOf(tmp)
        end

  fun findExprs f e = 
      let
        val tmp = List.foldr (op@) [] (List.map (findExprs f) (subExprTrees e))
      in
        if f e then
          e::tmp
        else
          tmp
      end
end
