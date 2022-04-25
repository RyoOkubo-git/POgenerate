datatype PGType =
	OPInfo of (string * BToken list * BToken list * PGOp list)
	(* (操作名, 返り値, 引数, 各代入文の情報) *)
and
	PGOp =
	PGInfo of (string * BExpr list * (BToken list * BExpr list) * BExpr list * BSubstitution)
	(* (代入or参照, PRE系制約, (ANY識別子, ANY系制約), IF系制約, 代入文) *)