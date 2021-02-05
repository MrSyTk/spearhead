open Type
open TDB
open Shift

type 'g used =
  | Empty : unit used
  | Used : 'a typ * 'g used -> ('a -> 'g) used
  | NUsed : 'a typ * 'g used -> ('a -> 'g) used

open Format
let rec p_used : type g. int -> Format.formatter -> g used -> unit =
  fun i ppf ->
  function
  | Empty -> fprintf ppf "[]"
  | Used(_, u) -> fprintf ppf "%dU::%a" i (p_used (i+1)) u
  | NUsed(_, u) -> fprintf ppf "%dN::%a" i (p_used (i+1)) u


let rec vsearch : type g a d. g used -> (g, d, a) tTerm -> g used =
  let rec write : type g a d. g used -> (g, d, a) index -> g used =
    fun u i ->
    match u, i with
    | NUsed(t, u), S i -> NUsed(t, write u i)
    | Used(t, u), S i -> Used(t, write u i)
    | NUsed(t, u), _ -> Used(t, u)
    | _, _ -> u
  in
  let pick : type g a. (a -> g) used -> g used =
    function
    | NUsed(_, u) -> u
    | Used(_, u) -> u
  in 
  fun u term ->
  match term with    
  | TVar(i) -> write u i
  | TApp(f, arg) ->
     let u' = vsearch u arg in
     vsearch u' f
  | TApp1(f, arg0) -> vsearch u (TApp(f, arg0))
  | TApp2(f, arg0, arg1) -> vsearch u (TApp(TApp(f, arg0), arg1))
  | TApp3(f, arg0, arg1, arg2) -> vsearch u (TApp(TApp(TApp(f, arg0), arg1), arg2))
  | TApp4(f, arg0, arg1, arg2, arg3) -> vsearch u (TApp(TApp(TApp(TApp(f, arg0), arg1), arg2), arg3))
  | TApp5(f, arg0, arg1, arg2, arg3, arg4) -> vsearch u (TApp(TApp(TApp(TApp(TApp(f, arg0), arg1), arg2), arg3), arg4))
  | TLam(t, body) -> pick (vsearch (NUsed(t, u)) body)
  | TOr(t1, t2) -> 
     let u' = vsearch u t1 in
     vsearch u' t2
  | Fix(_, f) -> vsearch u f
  | Fix2(_, _, f, g) ->
     let u' = vsearch u f in
     vsearch u' g
  | Cons(h, tl) ->
     let u' = vsearch u h in
     vsearch u' tl
  | Case(typ, x, nil, cons) ->     
     let u' = vsearch u x in
     let u'' = vsearch u' nil in
     let u''' = NUsed(typ, NUsed(List(typ), u'')) in
     vsearch u''' cons |> pick |> pick
  | TIf(x1, x2, thn, els) ->
     let u' = vsearch u x1 in
     let u'' = vsearch u' x2 in
     let u''' = vsearch u'' thn in
     vsearch u''' els
  | Left(_, t) -> vsearch u t
  | Right(_, t) -> vsearch u t
  | Succ n -> vsearch u n
  | _ -> u

let t1 = TLam(Bool, TLam(Char, TVar(S (S (S Z)))))
let u1 = NUsed(List(Char), NUsed(Char, Empty))

let rec gen_used : type g d. (g, d) ctx -> g used =
  function
  | CtxZ -> Empty
  | CtxS(t, c) -> NUsed(t, gen_used c)
