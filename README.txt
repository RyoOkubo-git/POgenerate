# 使い方
sml main.smlを実行
→いろいろロードされる
→止まったら入力ファイル名(.mch)を入力

# 実行結果
- 変数syntaxTree : 構文木
- 変数typedSyntaxTree : 型付け後の構文木
- ファイルout.mch : typedSyntaxTreeを再びBに戻したもの

# ソースファイル
- "main.sml"
全ての呼び出し元
- "Utils.sml"
あちこちで使える関数
- "BReal.sml"
B言語の実数を扱うためのデータ構造を定義
- "AST.sml"
構文木のデータ構造を定義
- "Keywords.sml"
Bの予約語
- "Priority.sml"
Bの演算子の優先順位
- "BuiltinFnc.sml"
Bの組込関数
- "Lexer.sml"
字句解析
- "Parser.sml"
構文解析
- "TypeInference.sml"
型推論
- "PrintComponent.sml"
構文木から文字列への変換
