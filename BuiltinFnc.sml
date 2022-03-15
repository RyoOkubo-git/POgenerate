structure BuiltinFnc =
struct
  val biSimpleFnc_str = [
      "FIN",      (*pd*)(* pow(x) -> pow(pow(x)) *)
      "FIN1",     (*c*)(* pow(x) -> pow(pow(x)) *)
      "POW",      (*pd*)(* pow(x) -> pow(pow(x)) *)
      "POW1",     (*c*)(* pow(x) -> pow(pow(x)) *)
      "btree",    (*t*)(* pow(x) -> pow(pow(pair(pow(pair(i,i)),x))) *)
      "card",     (*pd*)(* pow(x) -> i *)
      "ceiling",  (*pd*)(* r -> i *)
      "closure",  (*pd*)(* pow(pair(x,x)) -> pow(pair(x,x)) *)
      "closure1", (*pd*)(* pow(pair(x,x)) -> pow(pair(x,x)) *)
      "conc",     (*pd*)(* pow(pair(i,pow(pair(i,x)))) -> pow(pair(i,x)) *)
      "dom",      (*pd*)(* pow(pair(x,y)) -> pow(x) *)
      "first",    (*c*)(* pow(pair(i,x)) -> x *)
      "floor",    (*pd*)(* r -> i *)
      "fnc",      (*pd*)(* pow(pair(x,y)) -> pow(pair(x,pow(y))) *)
      "front",    (*c*)(* pow(pair(i,x)) -> pow(pair(i,x)) *)
      "id",       (*c*)(* pow(x) -> pow(pair(x,x)) *)
      "infix",    (*t*)(* pow(pair(pow(pair(i,i)),x)) -> pow(pair(i,x)) *)
      "inter",    (*c*)(* pow(pow(x)) -> pow(x) *)
      "iseq",     (*c*)(* pow(x) -> pow(pow(pair(i,x))) *)
      "iseq1",    (*pd*)(* pow(x) -> pow(pow(pair(i,x))) *)
      "last",     (*c*)(* pow(pair(i,x)) -> x *)
      "left",     (*t*)(* pow(pair(pow(pair(i,i)),x)) -> pow(pair(pow(pair(i,i)),x)) *)
      "max",      (*pd*)(* pow(x) -> x *)
      "min",      (*pd*)(* pow(x) -> x *)
      "mirror",   (*t*)(* pow(pair(pow(pair(i,i)),x)) -> pow(pair(pow(pair(i,i)),x)) *)
      "perm",     (*pd*)(* pow(x) -> pow(pow(pair(i,x))) *)
      "postfix",  (*t*)(* pow(pair(pow(pair(i,i)),x)) -> pow(pair(i,x)) *)
      "pred",     (*c*)(* i -> i *)
      "prefix",   (*t*)(* pow(pair(pow(pair(i,i)),x)) -> pow(pair(i,x)) *)
      "ran",      (*c*)(* pow(pair(x,y)) -> pow(y) *)
      "real",     (*pd*)(* i -> r *)
      "rel",      (*pd*)(* pow(pair(x,pow(y))) -> pow(pair(x,y)) *)
      "rev",      (*pd*)(* pow(pair(i,x)) -> pow(pair(i,x)) *)
      "right",    (*t*)(* pow(pair(pow(pair(i,i)),x)) -> pow(pair(pow(pair(i,i)),x)) *)
      "seq",      (*pd*)(* pow(x) -> pow(pow(pair(i,x))) *)
      "seq1",     (*pd*)(* pow(x) -> pow(pow(pair(i,x))) *)
      "size",     (*c*)(* pow(pair(i,x)) -> i *)
      "sizet",    (*t*)(* pow(pair(pow(pair(i,i)),x)) -> i *)
      "sons",     (*t*)(* pow(pair(pow(pair(i,i)),x)) -> pow(pair(i,pow(pair(pow(pair(i,i)),x)))) *)
      "succ",     (*c*)(* i -> i *)
      "tail",     (*c*)(* pow(pair(i,x)) -> pow(pair(i,x)) *)
      "top",      (*t*)(* pow(pair(pow(pair(i,i)),x)) -> x *)
      "tree",     (*t*)(* pow(x) -> pow(pow(pair(pow(pair(i,i)),x))) *)
      "union",    (*c*)(* pow(pow(x)) -> pow(x) *)


      "bool",     (*pd*)(*bp->b*)
      "not"       (*pd*)(*p->p*)
    ]


  val bi2Fnc_str = [
      "arity",    (*e,e*)(*t*) (* pow(pair(pow(pair(i,i)),x)) pow(pair(i,i)) -> i *)
      "const",    (*e,e*)(*t*) (* x pow(pair(i,pow(pair(pow(pair(i,i)),x)))) -> pow(pair(pow(pair(i,i)),x)) *) 
      "father",   (*e,e*)(*t*) (* pow(pair(pow(pair(i,i)),x)) pow(pair(i,i)) -> pow(pair(i,i)) *)
      "iterate",  (*e,e*)(*pd*) (* pow(pair(x,x)) i -> pow(pair(x,x)) *)
      "prj1",     (*e,e*)(*pd*) (* pow(x) pow(y) -> pow(pair(pair(x,y),x)) *)
      "prj2",     (*e,e*)(*pd*) (* pow(x) pow(y) -> pow(pair(pair(x,y),y)) *)
      "rank",     (*e,e*)(*t*) (* pow(pair(pow(pair(i,i)),x)) pow(pair(i,i)) -> i *)
      "subtree"   (*e,e*)(*t*) (* pow(pair(pow(pair(i,i)),x)) pow(pair(i,i)) -> pow(pair(pow(pair(i,i)),x)) *)
    ]



  val biMiscFnc_str = [
      "bin",      (*e*)      (*t*) (* x -> pow(pair(pow(pair(i,i)),x)) *)
      (*bin*)     (*e,e,e*)  (*t*) (* pow(pair(pow(pair(i,i)),x)) x pow(pair(pow(pair(i,i)),x)) -> pow(pair(pow(pair(i,i)),x)) *)
      "rec",                 (*pd*)
      "son",      (*e,e,e*)  (*t*) (* pow(pair(pow(pair(i,i)),x)) pow(pair(i,i)) i -> pow(pair(i,i)) *)
      "struct"               (*pd*)
    ]
end
