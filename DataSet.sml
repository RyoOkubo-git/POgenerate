signature SET =
sig
  exception SetError of string
  type 'a set
  val ade : ('a * 'a -> bool) -> 'a -> 'a set -> 'a set
  val rme : ('a * 'a -> bool) -> 'a -> 'a set -> 'a set
  val isBelongTo : ('a * 'a -> bool) -> 'a -> 'a set -> bool
  val isPartOf : ('a * 'a -> bool) -> 'a set -> 'a set -> bool
  val eqTo : ('a * 'a -> bool) -> 'a set -> 'a set -> bool
  val inter : ('a * 'a -> bool) -> 'a set -> 'a set -> 'a set
  val union : ('a * 'a -> bool) -> 'a set -> 'a set -> 'a set
  val isEmp : 'a set -> bool
  val fromList : ('a * 'a -> bool) -> 'a list -> 'a set
  val toList : 'a set -> 'a list
end

structure Set :> SET =
struct
  exception SetError of string
  datatype 'a set = S of 'a list

  fun ade eqf e (S s) = 
      if List.exists (fn x => eqf(x, e)) s then
        S(s)
      else
        S(e::s)
  and
    rme _ _ (S []) = (S [])
    | rme eqf e (S(x::xs)) =
      let
        val S(next) = rme eqf e (S xs)
      in
        if eqf(e, x) then
          S(next)
        else
          S(x::next)
      end
  and
    isBelongTo eqf e (S s) = List.exists (fn x => eqf(e, x)) s
  and
    isPartOf _ (S []) _ = true
    | isPartOf eqf (S (x::xs)) s = (isBelongTo eqf x s) andalso (isPartOf eqf (S xs) s)
  and
    eqTo eqf s1 s2 = (isPartOf eqf s1 s2) andalso (isPartOf eqf s2 s1)
  and
    inter eqf (S []) s2 = S []
    | inter eqf (S (x::xs)) s2 =
      if isBelongTo eqf x s2 then
        ade eqf x (inter eqf (S xs) s2)
      else
        inter eqf (S xs) s2 
  and
    union eqf (S []) s2 = s2
    | union eqf (S (x::xs)) s2 =
      if isBelongTo eqf x s2 then
        union eqf (S xs) s2
      else
        union eqf (S xs) (ade eqf x s2)
  and
    isEmp (S []) = true
    | isEmp _ = false
  and 
    fromList eqf l = 
      let
        fun rmDouble [] = []
          | rmDouble (e::es) =
            if List.exists (fn x => eqf(x, e)) es then
              rmDouble es
            else
              e::(rmDouble es)
      in
        S (rmDouble l)
      end
  and
    toList (S l) = l
end
