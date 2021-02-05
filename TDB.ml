
open Type

type (_, _, _) index =
  | Z : ('a  -> 'g,  'd, 'a) index
  | S : ('g, 'd, 'b)  index -> ('a -> 'g, 'd,  'b)  index
  | P : 'a typ *  ('a  -> 'g, 'd, 'b)  index -> ('g, 'd, 'b)  index
type (_, _, _) findex =
  | Zf : ('g, 'a -> 'd, 'a) findex
  | Sf : ('g, 'd, 'b) findex -> ('g, 'a -> 'd, 'b) findex

type ('g, 'd) ctx =
  | CtxZ : (unit, 'd) ctx
  | CtxS : 'a typ * ('ctx, 'd) ctx -> ('a -> 'ctx, 'd) ctx


let rec int_index : type g d a. (g, d, a) index -> int =
  function
  | Z -> 0
  | S i -> 1 + int_index i
  | P(_, i) -> int_index i - 1

let rec int_findex : type g d a. (g, d, a) findex -> int =
  function
  | Zf -> 0
  | Sf i -> 1 + int_findex i
                 
type (_, _, _) tTerm =
  | TVar : ('g, 'd, 'a) index -> ('g, 'd, 'a) tTerm
  | TFVar : ('g, 'd, 'a) findex -> ('g, 'd, 'a) tTerm
  | Next : 'b typ * (unit, 'b -> 'd, 'b) tTerm -> ('g, 'd, 'b) tTerm
  | TLam : 'a typ * ('a -> 'g, 'd, 'b) tTerm -> ('g, 'd, ('a -> 'b)) tTerm
  | TLamNon : 'a typ * ('a -> 'g, 'd, 'b) tTerm -> ('g, 'd, ('a -> 'b)) tTerm
  | TApp : ('g, 'd, 'a -> 'b) tTerm * ('g, 'd, 'a) tTerm
           -> ('g, 'd, 'b) tTerm
  | TApp1 : (('g, 'd, 'a -> 'b) tTerm * ('g, 'd, 'a) tTerm)
           -> ('g, 'd, 'b) tTerm
  | TApp2 : ('g, 'd, 'a0 -> 'a1 -> 'b) tTerm
            * ('g, 'd, 'a0) tTerm
            * ('g, 'd, 'a1) tTerm
            -> ('g, 'd, 'b) tTerm
  | TApp3 : ('g, 'd, 'a0 -> 'a1 -> 'a2 -> 'b) tTerm
            * ('g, 'd, 'a0) tTerm
            * ('g, 'd, 'a1) tTerm
            * ('g, 'd, 'a2) tTerm
            -> ('g, 'd, 'b) tTerm
  | TApp4 : ('g, 'd, 'a0 -> 'a1 -> 'a2 -> 'a3 -> 'b) tTerm
            * ('g, 'd, 'a0) tTerm
            * ('g, 'd, 'a1) tTerm
            * ('g, 'd, 'a2) tTerm
            * ('g, 'd, 'a3) tTerm
            -> ('g, 'd, 'b) tTerm
  | TApp5 : ('g, 'd, 'a0 -> 'a1 -> 'a2 -> 'a3 -> 'a4 -> 'b) tTerm
            * ('g, 'd, 'a0) tTerm
            * ('g, 'd, 'a1) tTerm
            * ('g, 'd, 'a2) tTerm
            * ('g, 'd, 'a3) tTerm
            * ('g, 'd, 'a4) tTerm
            -> ('g, 'd, 'b) tTerm
  | TTrue : ('g, 'd, bool) tTerm
  | TFalse : ('g, 'd, bool) tTerm
  | Ch : char -> ('g, 'd, char) tTerm
  | TOr : (('g, 'd, bool) tTerm * ('g, 'd, bool) tTerm)
          -> ('g, 'd, bool) tTerm
  | Fix : ('a -> 'b) typ
          * ('g, 'd, ('a -> 'b) -> 'a -> 'b) tTerm
          -> ('g, 'd, 'a -> 'b) tTerm
  | Fix2 : ('a1 -> 'r1) typ * ('a2 -> 'r2) typ
           * ('g, 'd, ('a1 -> 'r1) * ('a2 -> 'r2) -> 'a1 -> 'r1) tTerm
           * ('g, 'd, ('a1 -> 'r1) * ('a2 -> 'r2) -> 'a2 -> 'r2) tTerm
           -> ('g, 'd, ('a1 -> 'r1) * ('a2 -> 'r2)) tTerm
  | Nil : ('g, 'd, char list) tTerm
  | Cons : ('g, 'd, 'a) tTerm * ('g, 'd, 'a list) tTerm
           -> ('g, 'd, 'a list) tTerm
  | Case : 'a typ
           * ('g, 'd, 'a list) tTerm
           * ('g, 'd, 'b) tTerm
           * ('a -> ('a list -> 'g), 'd, 'b) tTerm
           -> ('g, 'd, 'b) tTerm
  | TIf : ('g, 'd, 'a) tTerm * ('g, 'd, 'a) tTerm
          * ('g, 'd, 'b) tTerm
          * ('g, 'd, 'b) tTerm
          -> ('g, 'd, 'b) tTerm
  | Left : 'b typ * ('g, 'd, 'a * 'b) tTerm -> ('g, 'd, 'a) tTerm
  | Right : 'a typ * ('g, 'd, 'a * 'b) tTerm -> ('g, 'd, 'b) tTerm
  | Zero : ('g, 'd, int) tTerm
  | Succ : ('g, 'd, int) tTerm -> ('g, 'd, int) tTerm

type 'd functions =
  | FNil : unit functions
  | Fun : 'a typ * (unit, 'a -> 'd, 'a) tTerm * 'd functions -> ('a -> 'd) functions

let z_ = TVar(Z)
open Format

let rec p_term : type g d a. Format.formatter -> (g, d, a) tTerm -> unit =
  fun ppf -> 
  function
  | TVar(i) -> int_index i |> fprintf ppf "%d"
  | TFVar(i) -> int_findex i |> fprintf ppf "_%d"
  | Next(_, term) -> fprintf ppf "@[<v 2>N%a@]" p_term term
  | TLam(_, t) -> fprintf ppf "@[<hov 2>\\%a@]" p_term t
  | TLamNon(_, t) -> fprintf ppf "@[<hov 2>\\*%a@]" p_term t
  | TApp(t1, t2) -> fprintf ppf "@[<hov 2>(%a %a)@]" p_term t1 p_term t2
  | TApp1(t1, t2) -> fprintf ppf "@[<hov 2>(%a %a)@]" p_term t1 p_term t2
  | TApp2(t1, t2, t3) -> fprintf ppf "@[<hov 2>(%a %a %a)@]" p_term t1 p_term t2 p_term t3
  | TApp3(t1, t2, t3, t4) -> fprintf ppf "@[<hov 2>(%a %a %a %a)@]" p_term t1 p_term t2 p_term t3 p_term t4
  | TApp4(t1, t2, t3, t4, t5) -> fprintf ppf "@[<hov 2>(%a %a %a %a %a)@]" p_term t1 p_term t2 p_term t3 p_term t4 p_term t5
  | TApp5(t1, t2, t3, t4, t5, t6) -> fprintf ppf "@[<hov 2>(%a %a %a %a %a %a)@]" p_term t1 p_term t2 p_term t3 p_term t4 p_term t5 p_term t6
  | TTrue -> fprintf ppf "T"
  | TFalse -> fprintf ppf "F"
  | Ch(c) -> fprintf ppf "%c" c
  | TOr(t1, t2) -> fprintf ppf "@[<hov 2>%a||%a@]" p_term t1 p_term t2
  | Fix(_, f) -> fprintf ppf "@[<hov 4>Fix(%a)@]" p_term f
  | Fix2(_, _, f, g) -> fprintf ppf "@[<hov 5>Fix2(%a, @,%a)@]" p_term f p_term g
  | Nil -> fprintf ppf "[]"
  | Cons(h, tl) -> fprintf ppf "%a:%a" p_term h p_term tl
  | Case(_, x, nil, cons) -> fprintf ppf "@[<v 2>case %a of @,[] -> %a  @,0:1 -> %a@]"
                               p_term x p_term nil p_term cons
  | TIf(x, a, thn, els) -> fprintf ppf "@[<v 0>if  %a=%a @,then %a  @,else %a@]"
                             p_term x p_term a p_term thn p_term els
  | Left(_, t) -> fprintf ppf "@[<hov 2>%a.fst@]" p_term t
  | Right(_, t) -> fprintf ppf "@[<hov 2>%a.snd@]" p_term t
  | Zero -> fprintf ppf "Z"
  | Succ n -> fprintf ppf "1+(%a)" p_term n
              
type ('a1, 'g1, 'a2, 'g2) term_eq  = TermEq : ('a, 'g, 'a, 'g) term_eq
type ('a1, 'g1, 'a2, 'g2) index_eq  = IndexEq : ('a, 'g, 'a, 'g) index_eq
let rec eq_index : type g d a b. (g, d, a) index -> (g, d, b) index -> (a, g, b, g) index_eq option =
  fun i1 i2 ->
  match i1, i2 with
  | Z , Z -> Some IndexEq
  | S(i1), S(i2) ->
     begin
       match eq_index i1 i2 with
       | Some IndexEq -> Some IndexEq
       | None -> None
     end
  | P(t1, i1), P(t2, i2) ->     
     begin
       match eq_test t1 t2 with
       | Some Eq -> 
       begin         
         match eq_index i1 i2 with 
         | Some IndexEq -> Some IndexEq
         | None -> None
       end
       | None -> None
     end
  | _, _ -> None
type ('a1, 'g1, 'a2, 'g2) findex_eq  = FIndexEq : ('a, 'g, 'a, 'g) findex_eq
let rec eq_findex : type g d a b. (g, d, a) findex -> (g, d, b) findex -> (a, g, b, g) findex_eq option =
  fun i1 i2 ->
  match i1, i2 with
  | Zf , Zf -> Some FIndexEq
  | Sf(i1), Sf(i2) ->
     begin
       match eq_findex i1 i2 with
       | Some FIndexEq -> Some FIndexEq
       | None -> None
     end
  | _, _ -> None
           
let rec eq_term : type g d a b. (g, d, a) tTerm -> (g, d, b) tTerm -> (a, g, b, g) term_eq option =
  fun t1 t2 ->
  match t1, t2 with
  | TVar(i1), TVar(i2) ->
     begin
       match eq_index i1 i2 with
       | Some IndexEq -> 
          Some TermEq
       | None ->   None
     end
  | TFVar(i1), TFVar(i2) ->
     begin
       match eq_findex i1 i2 with
       | Some FIndexEq -> 
          Some TermEq
       | None ->   None
     end
  | Next(t1, _), Next(t2, _) ->
     begin
       match eq_test t1 t2 with
       | Some Eq -> Some TermEq
       | None -> None
     end
  | TApp(f1, t1), TApp(f2, t2) ->
     begin
       match eq_term f1 f2, eq_term t1 t2 with
       | Some TermEq, Some TermEq -> Some TermEq
       | _, _ -> None
     end
  | TApp1(f1, t1), TApp1(f2, t2) ->
     begin
       match eq_term f1 f2, eq_term t1 t2 with
       | Some TermEq, Some TermEq -> 
          Some TermEq
       | _, _ -> None
     end
  | TApp2(f, arg0, arg1), TApp2(f', arg0', arg1') ->
     begin
       match eq_term f f', eq_term arg0 arg0', eq_term arg1 arg1' with
       | Some TermEq, Some TermEq, Some TermEq -> Some TermEq
       | _ -> None
     end
  | TApp3(f, arg0, arg1, arg2), TApp3(f', arg0', arg1', arg2') ->
     begin
       match eq_term f f', eq_term arg0 arg0', eq_term arg1 arg1', eq_term arg2 arg2' with
       | Some TermEq, Some TermEq, Some TermEq, Some TermEq -> Some TermEq
       | _ -> None
     end
  | TApp4(f, arg0, arg1, arg2, arg3), TApp4(f', arg0', arg1', arg2', arg3') ->
     begin
       match eq_term f f', eq_term arg0 arg0', eq_term arg1 arg1', eq_term arg2 arg2', eq_term arg3 arg3' with
       | Some TermEq, Some TermEq, Some TermEq, Some TermEq, Some TermEq -> Some TermEq
       | _ -> None
     end
  | TApp5(f, arg0, arg1, arg2, arg3, arg4), TApp5(f', arg0', arg1', arg2', arg3', arg4') ->
     begin
       match eq_term f f', eq_term arg0 arg0', eq_term arg1 arg1', eq_term arg2 arg2', eq_term arg3 arg3', eq_term arg4 arg4' with
       | Some TermEq, Some TermEq, Some TermEq, Some TermEq, Some TermEq, Some TermEq -> Some TermEq
       | _ -> None
     end
  | Fix(typ1, f1), Fix(typ2, f2) ->
     begin
       match eq_test typ1 typ2 with
       | Some Eq ->
          begin
            match eq_term f1 f2 with
            | Some TermEq -> Some TermEq               
            | None -> None
          end
       | _ -> None
     end
  | Fix2(typf1, typg1, f, g), Fix2(typf2, typg2, f', g') ->
     begin
       match eq_test typf1 typf2, eq_test typg1 typg2 with
       | Some Eq, Some Eq ->
          begin
            match eq_term f f', eq_term g g' with
            | Some TermEq, Some TermEq -> Some TermEq
            | _ -> None
          end
       | _, _ -> None
     end

  | Case(t1, x1, nil1, cons1), Case(t2, x2, nil2, cons2) ->
     begin
       match eq_test t1 t2 with
       | Some Eq -> 
          begin
            match eq_term x1 x2,
                  eq_term nil1 nil2,
                  eq_term cons1 cons2 with
            | Some TermEq, Some TermEq, Some TermEq -> Some TermEq               
            | _ -> None              
          end
       | _ -> None
     end
  | Cons(h1, tl1), Cons(h2, tl2) ->
     begin
       match eq_term h1 h2, eq_term tl1 tl2 with
       | Some TermEq, Some TermEq -> Some TermEq
       | _ -> None
     end
  | TOr(l1, r1), TOr(l2, r2) ->
     begin
       match eq_term l1 l2, eq_term r1 r2 with
       | Some TermEq, Some TermEq -> Some TermEq
       | _ -> None
     end
  | TIf(x1, v1, th1, el1), TIf(x2, v2, th2, el2) ->
     begin
       match eq_term x1 x2,
             eq_term v1 v2,
             eq_term th1 th2,
             eq_term el1 el2 with
       | Some TermEq, Some TermEq, Some TermEq, Some TermEq -> Some TermEq
       | _ -> None
     end
  | TTrue, TTrue -> Some TermEq
  | TFalse, TFalse -> Some TermEq
  | Ch(c), Ch(c') -> if c = c' then Some TermEq else None
  | TLam(t1, f1), TLam(t2, f2) ->
     begin
       match eq_test t1 t2 with
       | Some Eq -> 
          begin
            match eq_term f1 f2 with
            | Some TermEq -> Some TermEq
            | _ -> None
          end
       | _ -> None
     end
  | TLamNon(t1, f1), TLamNon(t2, f2) ->
     begin
       match eq_test t1 t2 with
       | Some Eq -> 
          begin
            match eq_term f1 f2 with
            | Some TermEq -> Some TermEq
            | _ -> None
          end
       | _ -> None
     end
  | Left(typ1, t1) , Left(typ2, t2) ->
      begin
        match eq_test typ1 typ2 with
        | Some Eq ->
           begin
             match eq_term t1 t2 with
             | Some TermEq -> Some TermEq
             | _ -> None
           end
        | _ -> None
      end
  | Right(typ1, t1) , Right(typ2, t2) ->
     begin
        match eq_test typ1 typ2 with
        | Some Eq ->
           begin
             match eq_term t1 t2 with
             | Some TermEq -> Some TermEq
             | _ -> None
           end
        | _ -> None
      end
  | Nil, Nil -> Some TermEq
  | Zero, Zero -> Some TermEq
  | Succ n, Succ n' ->
     begin
       match eq_term n n' with
       | Some TermEq -> Some TermEq
       | _ -> None
     end 
  | _ -> None

type (_(* ctx *), _(* ctx *)) ctx_eq =
  | CtxEq : ('a, 'a) ctx_eq

let rec ctx_test : type d c1 c2. (c1, d) ctx -> (c2, d) ctx
                        -> (c1, c2) ctx_eq option =
  fun c1 c2 ->
  match c1, c2 with
  | CtxZ, CtxZ -> Some CtxEq
  | CtxS(t1, c1), CtxS(t2, c2) ->
     begin
       match eq_test t1 t2 with
       | Some Eq ->
          begin
            match ctx_test c1 c2 with
            | Some CtxEq -> Some CtxEq
            | None -> None
          end
       | None -> None
     end
  | _, _ -> None
let rec dctx : type g d a. a typ -> (g, d) ctx -> (g, a -> d) ctx =
  fun typ ->
  function
  | CtxS(t, ctx) -> CtxS(t, dctx typ ctx)
  | CtxZ -> CtxZ

let tshift : type a j i d. (j, d) ctx -> (a-> i, d) ctx -> (j, d, a) index =
  let rec tshift'
        : type a j i d. int -> (j, d) ctx -> (a->i, d) ctx -> (j, d, a) index
    =
    fun n c1 c2 ->
    match n, c1, c2, ctx_test c1 c2 with
    | _, CtxZ, _, _ -> failwith "tshift failure"
    | 0, CtxS(_, _), CtxS(_, _) , Some CtxEq -> Z
    | n, CtxS(_, c1), c2, _ -> S(tshift' (n-1) c1 c2)
  in
  let rec len : type j d. (j, d) ctx -> int = function
    | CtxZ -> 0
    | CtxS(_, c) -> 1 + len c
  in 
  fun c1 c2 -> tshift' (len c1 - len c2) c1 c2

type ('g, 'd) tenv = ('g, 'd) ctx
type 'd fenv = 'd functions
let rec infer : type g d a. (g, d) tenv -> d fenv -> (g, d, a) tTerm -> a typ =
  fun tenv fenv term ->
  let rec lookup : type g d a. (g, d) tenv -> (g, d, a) index -> a typ =
    fun env i ->
    match env, i with
    | CtxS(t, _), Z -> t
    | CtxS(_, env), S i -> lookup env i
    | _, P(t, i) -> lookup (CtxS(t, env)) i
  in
  let rec flookup : type g d a. d fenv -> (g, d, a) findex -> a typ =
    fun fenv j ->
    match fenv, j with      
    | Fun(t, _, _), Zf -> t
    | Fun(_, _, fenv), Sf j -> flookup fenv j
  in 
  match term with
  | TVar(i) -> lookup tenv i
  | TFVar(j) -> flookup fenv j
  | Next(t, _) -> t
  | TLam(t, body) -> t => infer (CtxS(t, tenv)) fenv body 
  | TLamNon(t, body) -> t => infer (CtxS(t, tenv)) fenv body
  | TApp(f, x) -> let Arrow(_, t) = infer tenv fenv f in t
  | TApp1(f, x0) -> infer tenv fenv (TApp(f, x0))
  | TApp2(f, x0, x1) -> infer tenv fenv (TApp(TApp(f, x0), x1))
  | TApp3(f, x0, x1, x2) -> infer tenv fenv (TApp(TApp(TApp(f, x0), x1), x2))
  | TApp4(f, x0, x1, x2, x3) -> infer tenv fenv (TApp(TApp(TApp(TApp(f, x0), x1), x2), x3))
  | TApp5(f, x0, x1, x2, x3, x4) -> infer tenv fenv (TApp(TApp(TApp(TApp(TApp(f, x0), x1), x2), x3), x4))
  | TTrue -> Bool
  | TFalse -> Bool
  | Ch _ -> Char
  | TOr _ -> Bool
  | Fix(t, _) -> t
  | Fix2(tl, tr, _, _) -> tl =* tr
  | Nil -> List(Char)
  | Cons(h, tl) -> List(infer tenv fenv h)
  | Case(t, x, nil, cons) -> infer tenv fenv nil
  | TIf(x, a, thn, els) -> infer tenv fenv thn
  | Left(_, left) -> let Pair(l, _) = infer tenv fenv left in l
  | Right(_, right) -> let Pair(_, r) = infer tenv fenv right in r
  | Succ n -> Int
  | Zero -> Int
