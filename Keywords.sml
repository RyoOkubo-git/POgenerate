signature KEYWORDS =
sig
  val clauseKeywords : (string * int) list
  val keywords : (string * BToken) list
  val alphaKeywords : string list
  val isSymbol : char -> bool
end

structure Keywords :> KEYWORDS =
struct
  val clauseKeywords = [(*2個目の要素は節のソート用の数*)
      ("CONSTRAINTS",10), 
      ("SEES",20), 
      ("INCLUDES",30), 
      ("PROMOTES",40), 
      ("EXTENDS",50), 
      ("USES",60), 
      ("SETS",70), 
      ("IMPORTS", 75), (* ちょっと追加させてもらいました by 大久保 *)
      ("CONCRETE_CONSTANTS",80), 
      ("ABSTRACT_CONSTANTS",90), 
      ("CONSTANTS",80), 
      ("PROPERTIES",100), 
      ("VALUES", 105), (* ちょっと追加させてもらいましたagain by 大久保 *)
      ("CONCRETE_VARIABLES",110), 
      ("ABSTRACT_VARIABLES",120), 
      ("VARIABLES",120),
      ("INVARIANT",130), 
      ("ASSERTIONS",140), 
      ("INITIALISATION",150), 
      ("OPERATIONS",160)
    ]

  (*アルファベットや数字を除いた記号(アンダーバーを含む)*)

  val symbolChars = [#"!", #"\"", #"#", #".", #"$", #"%", #"&", #"'", #"(", #")", #"*", #"+", #",", #"-", #".", #"/", #":", #";", #"<", #"=", #">", #"_", #"?", #"@", #"[", #"\\", #"]", #"^", #"`", #"{", #"|", #"}", #"~" ]

  (*記号を用いた予約語*)
  val keywords = [
      (*4文字*)
      ("+->>",Keyword "PSur"),
      ("-->>",Keyword "Sur"),
      ("/<<:",Keyword "SNInc"),
      (">->>",Keyword "TBij"),
      (*3文字*)
      ("+->",Keyword "PFun"),
      ("-->",Keyword "TFun"),
      ("/<:",Keyword "NInc"),
      ("/|\\",Keyword "RSeqH"),
      ("<->",Keyword "Rel"),
      ("<--",Keyword "Output"),
      ("<<:",Keyword "SInc"),
      ("<<|",Keyword "SubDom"),  
      ("<=>",Keyword "Equiv"),
      (">+>",Keyword "PInj"),
      (">->",Keyword "TInj"),
      ("\\|/",Keyword "RSeqE"),
      ("|->",Keyword "Maplet"),
      ("|>>", Keyword "SubRan"),
      (*2文字*)
      ("$0", Keyword "IniVal"),
      ("**", Keyword "Power"),
      ("->", Keyword "InsSeqStart"),
      ("..", Keyword "Interval"),
      ("/:", Keyword "NBelong"),
      ("/=", Keyword "NEq"),
      ("/\\", Keyword "Inter"), 
      ("::", Keyword "BeEltOf"), 
      (":=", Keyword "BeEqualTo"),
      ("<+", Keyword "OverWrite"),
      ("<-", Keyword "InsSeqEnd"),
      ("<:", Keyword "Inclusion"),
      ("<=", Keyword "LEq"),
      ("<|", Keyword "ResDom"), 
      ("==", Keyword "Def"),
      ("=>", Keyword "Implies"),
      ("><", Keyword "DProductRel"), 
      (">=", Keyword "GEq"),
      ("[]", Keyword "EmpSeq"),
      ("\\/", Keyword "Union"),
      ("{}", Keyword "EmpSet"),
      ("|>", Keyword "ResRan"),
      ("||", Keyword "Parallel"),
      (*1文字*)
      ("!", Keyword "ForAny"),
      ("#", Keyword "Exists"),
      ("%", Keyword "Lambda"),
      ("&", Keyword "And"),
      ("'", Keyword "AccessRecordField"),
      ("!", Keyword "ForAny"),
      ("(", LBracket),
      (")", RBracket),
      ("*", Keyword "Asta"),
      ("+", Keyword "Plus"),
      (",", Keyword "Comma"),
      ("-", Keyword "Minus"),
      (".", Keyword "Dot"),
      ("/", Keyword "Slash"),
      (":", Keyword "Coron"),
      (";", Keyword "Semicoron"),
      ("=", Keyword "Eq"),
      ("<", Keyword "Lt"),
      (">", Keyword "Gt"),
      ("[", Keyword "StartSeq"),
      ("]", Keyword "EndSeq"),
      ("^", Keyword "ConcatSeq"),
      ("{", Keyword "StartSet"),
      ("|", Keyword "VBar"),
      ("}", Keyword "EndSet"),
      ("~", Keyword "Reverse")
    ]
  (*alphaKeywordsRは辞書順、alphaKeywordsはその逆*)
  val alphaKeywordsR = [
      "ABSTRACT_CONSTANTS",
      "ABSTRACT_VARIABLES",
      "ANY",
      "ASSERT",
      "ASSERTIONS",
      "BE",
      "BEGIN",
      "BOOL",
      "CASE",
      "CHOICE",
      "CONCRETE_CONSTANTS",
      "CONCRETE_VARIABLES",
      "CONSTANTS",
      "CONSTRAINTS",
      "DEFINITIONS",
      "DO",
      "EITHER",
      "ELSE",
      "ELSIF",
      "END",
      "EXTENDS",
      "FALSE",
      "FIN",      (*e*)
      "FIN1",     (*e*)
      "IF",
      "IMPLEMENTATION",
      "IMPORTS",
      "IN",
      "INCLUDES",
      "INITIALISATION",
      "INT",
      "INTEGER",
      "INTER",(*.*)
      "INVARIANT",
      "LET",
      "LOCAL_OPERATIONS",
      "MACHINE",
      "MAXINT",
      "MININT",
      "NAT",
      "NAT1",
      "NATURAL",
      "NATURAL1",
      "OF",
      "OPERATIONS",
      "OR",
      "PI",       (*.*)
      "POW",      (*e*)
      "POW1",     (*e*)
      "PRE",
      "PROMOTES",
      "PROPERTIES",
      "REFINES",
      "REFINEMENT",
      "SEES",
      "SELECT",
      "SETS",
      "SIGMA",    (*.*)
      "STRING",
      "THEN",
      "TRUE",
      "UNION",    (*.*)
      "USES",
      "VALUES",
      "VAR",
      "VARIANT",
      "VARIABLES",
      "WHEN",
      "WHERE",
      "WHILE",
      "arity",    (*,*)
      "bin",
      "bool",     (*e*)
      "btree",    (*e*)
      "card",     (*e*)
      "ceiling",  (*e*)
      "closure",
      "closure1",
      "conc",     (*e*)
      "const",
      "dom",      (*e*)
      "father",   (*,*)
      "first",    (*e*)
      "floor",    (*e*)
      "fnc",      (*e*)
      "front",    (*e*)
      "id",       (*e*)
      "infix",    (*e*)
      "inter",    (*e*)
      "iseq",     (*e*)
      "iseq1",    (*e*)
      "iterate",
      "last",     (*e*)
      "left",     (*e*)
      "max",      (*e*)
      "min",      (*e*)
      "mirror",   (*e*)
      "mod",
      "not",
      "or",
      "perm",     (*e*)
      "postfix",  (*e*)
      "pred",     (*e*)
      "prefix",   (*e*)
      "prj1",
      "prj2",
      "ran",      (*e*)
      "rank",     (*,*)
      "real",     (*e*)
      "rec",
      "rel",      (*e*)
      "rev",      (*e*)
      "right",    (*e*)
      "seq",      (*e*)
      "seq1",     (*e*)
      "size",     (*e*)
      "sizet",    (*e*)
      "skip",
      "son",      (*,*)
      "sons",     (*e*)
      "struct",
      "subtree",  (*,*)
      "succ",(*e*)
      "tail",(*e*)
      "top",(*e*)
      "tree",(*e*)
      "union"(*e*)
    ]
  val alphaKeywords = rev alphaKeywordsR
  fun isSymbol x = List.exists (fn y => y=x) symbolChars
end