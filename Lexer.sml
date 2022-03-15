exception LexerErr

(*getVarNのcodeの1文字目がアルファベットであることは呼び出し元で確認すること*)
fun getVarN code =
    if code = "" then 0 else
      let
        val c = String.sub(code,0)
      in
        (*ひとまずrenaming prefixは変数名の一部として扱う*)
        if c = #"." then
          let
            val c2 = String.sub(code,1)
          in
            if c2 = #"." orelse c2 = #"(" then
              0
            else
              1 + getVarN (String.extract(code,1,NONE))
          end  
        else
          if ((Char.isSpace) c) orelse ((Keywords.isSymbol c) andalso (c <> #"_")) then 
            0
          else
            1 + getVarN (String.extract(code,1,NONE))
      end

fun separateRenamingPrefix full = String.tokens (fn x => (x = #".")) full

fun getDigitsN code =
    if 
      code = "" 
    then 
      0 
    else
      let
        val c = String.sub(code,0)
      in
        if Char.isDigit c then
          1 + getDigitsN (String.extract(code,1,NONE))
        else
          0
      end

fun getStrN code =
    if code = "" then raise LexerErr else
      let val c = String.sub(code,0) in
        case c of
          #"\"" => 0
        | _ => 1 + getStrN (String.extract(code,1,NONE))
      end

(* val lexer : string -> [BToken] *)
(* ドットを使ったrenameされた識別子にもリストで対応しているが、モデル展開後のモデルにその記法が表れることはない *)
fun lexer code =
    if 
      code = ""
    then 
      [] 
    else
      let
        val c = String.sub(code,0)
      in
        if
          Char.isSpace c
        then
          lexer (String.extract(code,1,NONE))
        else
          if c = #"\"" then
            let
              val strN = getStrN (String.extract(code,1,NONE))
            in
              StringLiteral (String.extract(code,1,SOME(strN))) :: lexer (String.extract(code,2+strN,NONE))
            end
          else
            let 
              val klist = List.find (fn x => ((String.isPrefix (#1(x))) code)) Keywords.keywords
              val alist = List.find (fn x => (String.isPrefix x code)) Keywords.alphaKeywords
            in
              if 
                klist <> NONE
              then 
                let
                  val newBTokenPair = valOf(klist)
                in
                  #2(newBTokenPair) :: lexer (String.extract(code, size (#1(newBTokenPair)), NONE))
                end
              else
                if
                  alist <> NONE
                then
                  let
                    val newBTokenString = valOf(alist)
                    val rest = String.extract(code, size newBTokenString, NONE)
                  in
                    if
                      (rest = "") orelse ((Char.isSpace) (String.sub(rest,0))) orelse ((Keywords.isSymbol (String.sub(rest,0)))(*コード終端または次がスペースまたは次が記号*) 
                        andalso ((String.sub(rest,0))<> #"_"))(*次がアンダーバーでない*)
                    then
                      Reserved newBTokenString :: lexer rest(*アルファベット予約語*)
                    else
                      if
                        ((Char.isAlpha) (String.sub(rest,0))) orelse ((String.sub(rest,0))= #"_") orelse ((Char.isDigit) (String.sub(rest,0))) (*次がアルファベットか数字かアンダーバー*)
                      then
                        let        
                          val varN = getVarN code
                        in
                          Var (separateRenamingPrefix (String.extract(code,0,SOME(varN)))) :: lexer (String.extract(code,varN,NONE))
                        end
                      else
                        Other ((str c)^"?1") :: lexer (String.extract(code,1,NONE)) (*仮*)(*予約語のすぐ後に非ascii文字がある場合*)
                  end
                else
                  if Char.isDigit c then
                    let
                      val digitN = getDigitsN code
                      val rest = String.extract(code,digitN,NONE)
                    in
                      if rest = "" orelse String.sub(rest,0) <> #"." then
                        IntegerLiteral (valOf(IntInf.fromString(String.extract(code,0,SOME(digitN))))) :: lexer rest
                      else
                        if rest <> "." andalso (Char.isDigit) (String.sub(rest,1)) then(*restは非空文字列&restの先頭は"."&rest="."でない&"."の次は数字*)
                          let
                            val underpointRest = String.extract(rest,1,NONE)
                            val fractionalDigitN = getDigitsN underpointRest
                            val realRest = String.extract(underpointRest,fractionalDigitN,NONE)
                          in
                            RealLiteral (BReal.fromString(String.extract(code, 0, SOME(digitN + 1 + fractionalDigitN)))) :: lexer realRest
                          end
                        else
                          IntegerLiteral (valOf(IntInf.fromString(String.extract(code,0,SOME(digitN))))) :: lexer rest(*次が区間の".."の場合*)
                    end
                  else
                    if Char.isAlpha c then
                      let        
                        val varN = getVarN code
                      in
                        Var (separateRenamingPrefix(String.extract(code,0,SOME(varN)))) :: lexer (String.extract(code,varN,NONE))
                      end
                    else
                      Other ((str c)^"?2") :: lexer (String.extract(code,1,NONE)) (*仮*)(*非ascii文字や@、`など*)
            end
      end
