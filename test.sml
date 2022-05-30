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
use "ImpParser.sml";
use "Info.sml";
use "Replace.sml";
use "Extract.sml";
use "ProofObligationGenerator.sml";


(* val fileName =
  let
    val x = valOf(TextIO.inputLine TextIO.stdIn)
  in   
    if 
      String.sub(x, (String.size x) -1) = #"\n" 
    then 
      String.extract(x, 0, SOME((String.size x) -1)) 
    else 
      x 
  end  *)


val impTree = ImpParser.parse (lexer (Utils.fileToString "Library_i.imp"))

val syntaxTree = Parser.parse (lexer (Utils.fileToString "Library.mch"))


(* val syntaxTree = Parser.parse (lexer (Utils.fileToString fileName)) *) (*構文木生成*)

val testVar = ProofObligationGenerator.po_generate syntaxTree impTree

(* val typedSyntaxTree = TypeInference.type_component syntaxTree *) (*型付け*)

(*
ここに書き換えの処理を書く
*)

(* val () = Utils.outputFile((PrintComponent.componentToString typedSyntaxTree), "out.mch") (*出力*) *)

(*
現状
DEFINITIONS節、リファインメント、インプリメンテーションに未対応
*)
