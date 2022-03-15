Control.Print.printDepth := 100;
Control.Print.printLength := 1000;
Control.Print.stringDepth := 3000;
Control.polyEqWarn := false;
use "Utils.sml";
use "BReal.sml";
use "AST.sml";
use "Keywords.sml";
use "Priority.sml";
use "BuiltinFnc.sml";
use "Lexer.sml";
use "Parser.sml";
use "TypeInference.sml";
use "PrintComponent.sml";


val fileName =
  let
    val x = valOf(TextIO.inputLine TextIO.stdIn)
  in   
    if 
      String.sub(x, (String.size x) -1) = #"\n" 
    then 
      String.extract(x, 0, SOME((String.size x) -1)) 
    else 
      x 
  end 



val syntaxTree = Parser.parse (lexer (Utils.fileToString fileName)) (*構文木生成*)

val typedSyntaxTree = TypeInference.type_component syntaxTree (*型付け*)

(*
ここに書き換えの処理を書く
*)

val () = Utils.outputFile((PrintComponent.componentToString typedSyntaxTree), "out.mch") (*出力*)

(*
現状
DEFINITIONS節、リファインメント、インプリメンテーションに未対応
*)
