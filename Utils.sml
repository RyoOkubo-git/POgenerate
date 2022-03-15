structure Utils =
struct
  fun fileToString filename =
      let
        val is = TextIO.openIn( filename )
        fun fts_sub NONE = ""
          | fts_sub(SOME s) = s^fts_sub(TextIO.inputLine is)
        val res = fts_sub(TextIO.inputLine is)
      in
        TextIO.closeIn is;
        res
      end

  fun firstSlice _ [] = ([],[])
    | firstSlice f (x::xs) = if (f x) then (xs,[]) else 
        let 
          val (r,nxs) = firstSlice f xs
        in
          (r,x::nxs)
        end

  fun chopList f [] = []
    | chopList f l = 
      let 
        fun chopList_sub f [] = [[]]
          | chopList_sub f (x::xs) =
            let
              val ret = chopList_sub f xs
            in
              if (f x) then []::ret else ((x::(hd ret))::(tl ret))
            end
      in
        List.filter (fn y => y<>[]) (chopList_sub f l)
      end

  fun curry f = 
      fn x => (fn y => f(x,y))
  fun uncurry f = 
      fn (x,y) => (f x y)
  fun isAllUpper s = 
      List.all (fn x => Char.isUpper x) (String.explode s)
  fun eqto x y = (x=y)(*List.find等の高階関数用*)
  fun neqto x y = (x<>y)
  fun repeatApply f x = 
      let
        val res = f x
      in
        if res = x then 
          x 
        else 
          repeatApply f res
      end
  fun concatWith _ [] = ""
    | concatWith _ [x] = x
    | concatWith s (x::xs) = x^s^(concatWith s xs)
  fun outputFile(stringData, fname) =
      let
        open TextIO
        val strm = openOut fname
      in
        output(strm, stringData);  
        closeOut strm
      end
end