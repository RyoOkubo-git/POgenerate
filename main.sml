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

(*
val mfileName =
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

val ifileName =
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
*)


(* val impTree = ImpParser.parse (lexer (Utils.fileToString "Library_i.imp")) *)

(* val syntaxTree = Parser.parse (lexer (Utils.fileToString "Library.mch")) *)

fun plus1(SOME X) = X
|   plus1(NONE) = ""

val line = TextIO.stdIn
val coargs = CommandLine.arguments(); (*ファイル名の入力をコマンドライン引数も対応可能に*)
val mfile = if (length coargs) = 0 then (print "model file: ";plus1(TextIO.inputLine(line)))
                else hd(coargs)^"\n"
val mfileName = String.extract(mfile,0,(SOME (String.size(mfile)-1)))
	   
val ifile = if (length coargs) < 2  then (print "imprementation file: ";plus1(TextIO.inputLine(line)))
                else hd(tl coargs)^"\n"
val ifileName = String.extract(ifile,0,(SOME (String.size(ifile)-1)))

val syntaxTree = Parser.parse (lexer (Utils.fileToString mfileName)) (*構文木生成*)

val impTree = ImpParser.parse (lexer (Utils.fileToString ifileName)) (*構文木生成*)

val _ = ProofObligationGenerator.po_generate syntaxTree impTree

(* val typedSyntaxTree = TypeInference.type_component syntaxTree *) (*型付け*)

(*
ここに書き換えの処理を書く
*)

(* val () = Utils.outputFile((PrintComponent.componentToString typedSyntaxTree), "out.mch") (*出力*) *)

val _ = OS.Process.exit(OS.Process.success)

(*
現状
DEFINITIONS節、リファインメント、インプリメンテーションに未対応
*)
