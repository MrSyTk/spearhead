open TDB
open Type
(* agdaを元にshiftを実装 *)
(* https://plfa.github.io/DeBruijn/ *)
type ('g1, 'g2, 'd) inx_inx = {rho : 'a. (('g1, 'd, 'a) index -> ('g2, 'd, 'a) index)}
let rec ext : type g1 g2 b d. (g1, g2, d) inx_inx
                   -> b typ
                   -> (b -> g1, b -> g2, d) inx_inx =
  fun rho t -> (* Don't omit this type definition. *)
  let f : type a. (b -> g1, d, a) index -> (b -> g2, d, a) index =
    function
    | S x -> S (rho.rho x)
    | Z -> Z
    | P(t', i) -> P(t', (ext (ext rho t) t').rho i)
  in {rho = f}

type ('g1, 'g2, 'd) term_term = {shift : 'a. ('g1, 'd, 'a) tTerm -> ('g2, 'd, 'a) tTerm}

let rec rename : type g1 g2 d. (g1, g2, d) inx_inx -> (g1, g2, d) term_term =
  let rec rename_findex : type a d. (g1, d, a) findex -> (g2, d, a) findex =
    function
    | Zf -> Zf
    | Sf(i) -> Sf(rename_findex i)
  in 
  fun rho -> (* Don't omit this type definition. *)
  let f : type a. (g1, d, a) tTerm -> (g2, d, a) tTerm = 
    function
    | TVar(i) -> TVar(rho.rho i)
    | TFVar(i) -> TFVar(rename_findex i)
    | Next(t, f) -> Next(t, f)
    | TLam(typ, t) ->
       let rn = rename (ext rho typ) in
       TLam(typ, rn.shift t)
    | TLamNon(typ, t) ->
       let rn = rename (ext rho typ) in
       TLamNon(typ, rn.shift t)
    | TApp(t1, t2) ->
       let rn = rename rho in
       TApp(rn.shift t1, rn.shift t2)
    | TApp1(t1, t2) ->
       let rn = rename rho in
       TApp1(rn.shift t1, rn.shift t2)
    | TApp2(t1, t2, t3) ->
       let rn = rename rho in
       TApp2(rn.shift t1, rn.shift t2, rn.shift t3)
    | TApp3(t1, t2, t3, t4) ->
       let rn = rename rho in
       TApp3(rn.shift t1, rn.shift t2, rn.shift t3, rn.shift t4)
    | TApp4(t1, t2, t3, t4, t5) ->
       let rn = rename rho in
       TApp4(rn.shift t1, rn.shift t2, rn.shift t3, rn.shift t4, rn.shift t5)
    | TApp5(t1, t2, t3, t4, t5, t6) ->
       let rn = rename rho in
       TApp5(rn.shift t1, rn.shift t2, rn.shift t3, rn.shift t4, rn.shift t5, rn.shift t6)
    | TOr(t1, t2) ->
       let rn = rename rho in
       TOr(rn.shift t1, rn.shift t2)
    | TTrue -> TTrue
    | TFalse -> TFalse
    | Ch(c) -> Ch(c)
    | Fix(typ, t) ->
       let rn = rename rho in
       Fix(typ, rn.shift t)
    | Fix2(typf, typg, f, g) ->
       let rn = rename rho in
       Fix2(typf, typg, rn.shift f, rn.shift g)
    | Nil -> Nil
    | Cons(h, tl) ->
       let rn = rename rho in
       Cons(rn.shift h, rn.shift tl)
    | Case(typ, x, nil, cons) ->
       let (rn, rnc) = rename rho, rename (ext (ext rho (List(typ))) typ) in
       Case(typ, rn.shift x, rn.shift nil, rnc.shift cons)
    | TIf(x1, x2, thn, els) ->
       let rn = rename rho in
       TIf(rn.shift x1, rn.shift x2, rn.shift thn, rn.shift els)
    | Left(typ, t) -> Left(typ, (rename rho).shift t)
    | Right(typ, t) -> Right(typ, (rename rho).shift t)
    | Zero -> Zero
    | Succ n -> Succ ((rename rho).shift n)
               
   in {shift = f}

type ('g1, 'g2, 'd) inx_term = {mapto : 'a. ('g1, 'd, 'a) index -> ('g2, 'd, 'a) tTerm}
let shift_term : type g d b a. b typ -> (g, b -> g, d) term_term =
  fun t -> 
  let s : type a g. (g, d, a) index -> (b -> g, d, a) index =
    function
    | Z -> S Z
    | P(t', x) ->
       begin
         match eq_test t t' with
         | Some Eq -> x
         | None -> S (P(t', x))
       end
    | S x -> S (S x)
  in
  rename {rho = s}
let deshift_term : type g d b a. b typ -> (b -> g, g, d) term_term =
  fun t -> 
  let s : type a g. (b -> g, d, a) index -> (g, d, a) index =
    function
    | S i -> i
    | i -> P(t, i)
  in
  rename {rho = s}

let rec exts : type g1 g2 b d. (g1, g2, d) inx_term
                    -> b typ
                    -> (b -> g1, b -> g2, d) inx_term = 
  fun rho t ->
  let shift =
    let s : type a g. (g, d, a) index -> (b -> g, d, a) index =
    function
    | Z -> S Z
    | P(t', x) ->
       begin
         match eq_test t t' with
         | Some Eq -> x
         | None -> failwith "Index type was miss-match"
       end
    | S x -> S (S x)
  in
  rename {rho = s} in
  let f : type a. (b -> g1, d, a) index -> (b -> g2, d, a) tTerm =
    function
    | Z -> TVar(Z)
    | S x -> shift.shift (rho.mapto x)
    | P(t', x) -> shift.shift (rho.mapto (P(t, P(t', x))))
       
  in {mapto = f}


let rec subst : type g1 g2 d. (g1, g2, d) inx_term
                     -> (g1, g2, d) term_term =
  let rec rename_findex : type a d. (g1, d, a) findex -> (g2, d, a) findex =
    function
    | Zf -> Zf
    | Sf(i) -> Sf(rename_findex i)
  in 
  fun mapto ->   (* 代入される項 *) (* 代入後の項 *)
  let f : type a. (g1, d, a) tTerm -> (g2, d, a) tTerm = 
    function
    | TVar(i) -> mapto.mapto i
    | TFVar(i) -> TFVar(rename_findex i)
    | Next(t, funs) -> Next(t, funs)
    | TLam(typ, t) ->
       let subst = subst (exts mapto typ) in
       TLam(typ, subst.shift t)
    | TLamNon(typ, t) ->
       let subst = subst (exts mapto typ) in
       TLamNon(typ, subst.shift t)
    | TApp(t1, t2) ->
       let subst = subst mapto in
       TApp(subst.shift t1, subst.shift t2)
    | TApp1(t1, t2) ->
       let subst = subst mapto in
       TApp1(subst.shift t1, subst.shift t2)
    | TApp2(t1, t2, t3) ->
       let subst = subst mapto in
       TApp2(subst.shift t1, subst.shift t2, subst.shift t3)
    | TApp3(t1, t2, t3, t4) ->
       let subst = subst mapto in
       TApp3(subst.shift t1, subst.shift t2, subst.shift t3, subst.shift t4)
    | TApp4(t1, t2, t3, t4, t5) ->
       let subst = subst mapto in
       TApp4(subst.shift t1, subst.shift t2, subst.shift t3, subst.shift t4, subst.shift t5)
    | TApp5(t1, t2, t3, t4, t5, t6) ->
       let subst = subst mapto in
       TApp5(subst.shift t1, subst.shift t2, subst.shift t3, subst.shift t4, subst.shift t5, subst.shift t6)
    | TOr(t1, t2) ->
       let subst = subst mapto in
       TOr(subst.shift t1, subst.shift t2)
    | TTrue -> TTrue
    | TFalse -> TFalse
    | Ch(c) -> Ch(c)
    | Fix(typ, t) ->
       let subst = subst mapto in
       Fix(typ, subst.shift t)
    | Fix2(typf, typg, f, g) ->
       let subst = subst mapto in
       Fix2(typf, typg, subst.shift f, subst.shift g)   
    | Nil -> Nil
    | Cons(h, tl) ->
       let subst = subst mapto in
       Cons(subst.shift h, subst.shift tl)
    | Case(typ, x, nil, cons) ->
       let (st, stc) = subst mapto, subst (exts (exts mapto (List(typ))) typ) in
       Case(typ, st.shift x, st.shift nil, stc.shift cons)
    | TIf(x1, x2, thn, els) ->
       let subst = subst mapto in
       TIf(subst.shift x1, subst.shift x2, subst.shift thn, subst.shift els)
    | Left(typ, t) -> Left(typ, (subst mapto).shift t)
    | Right(typ, t) -> Right(typ, (subst mapto).shift t)
    | Zero -> Zero
    | Succ n -> Succ ((subst mapto).shift n)
  in {shift = f}


let subst0 : type g a b d. b typ -> (b -> g, d, a) tTerm -> (g, d, b) tTerm -> (g, d, a) tTerm =
  fun typ t v ->    (* vvvvv this a is also quantified. *)
  let rec mapto : type a. (b -> g, d, a) index -> (g, d, a) tTerm =
    function
    | Z ->  v
    | S x -> TVar(x)
    | P(t, x) -> TVar(P(typ, P(t, x)))
  in 
  (subst {mapto = mapto}).shift t

let substitute0 : type g a b d. (b -> g, d, a) tTerm -> (b -> g, d, b) tTerm -> (b -> g, d, a) tTerm =
  fun t v ->    (* vvvvv this a is also quantified. *)
  let rec mapto : type a. (b -> g, d, a) index -> (b -> g, d, a) tTerm =
    function
    | Z -> v
    | S x -> TVar(S x)
    | P(t, x) -> TVar(P(t, x))
  in 
  (subst {mapto = mapto}).shift t

(* type 'g unifier =  ('g, 'g) inx_term list *)
(* データ構造の意味が分かりにくいsubstitutionの型と、インデックス0に対応すること *)
type (_, _) unifier =
  | UNil : (unit, 'd) unifier
  | UCons : 'a typ * ('a -> 'g, 'd, 'a) tTerm * ('g, 'd) unifier -> ('a -> 'g, 'd) unifier             
              
let mapto0 : type a b g d. (b -> g, d, b) tTerm -> (b -> g, b -> g, d) inx_term =
  fun v ->
  let f : type a. (b -> g, d, a) index -> (b -> g, d, a) tTerm =
    function 
    | Z -> v
    | S x -> TVar(S x)
    | P(t, x) -> TVar(P(t, x))
  in {mapto = f}
(* let two : ((bool -> unit), 'd, bool) tTerm = TVar(S (S Z))
 * let _ = subst0 (Bool) (TVar(Z)) (TVar(Z)) *)
let shift_up t = (shift_term t).shift
let shift_down t = (deshift_term t).shift

(* let minus1 = TVar(P(Bool, Z))
 * let u1 : ((bool -> bool) -> (bool -> unit), 'd) unifier =
 *   UCons(Arrow(Bool, Bool), TLam(Bool, TVar(Z)),  UCons(Bool, two, UNil)) *)
let cons1 : (char -> char list -> char -> unit, unit, char list) tTerm = Cons(TVar(Z), Cons(TVar(S (S Z)), TVar(S Z)))
let subst_1 : type g a b d. b typ -> (g, d, b) tTerm -> (b -> g, g, d) inx_term =
  fun typ v ->    (* vvvvv this a is also quantified. *)
  let rec mapto : type a. (b -> g, d, a) index -> (g, d, a) tTerm =
    function
    | Z ->  v
    | S x -> TVar(x)
    | P(t, x) -> TVar(P(typ, P(t, x)))
  in 
  {mapto = mapto}
let mapto_1 : (char -> unit, unit, unit) inx_term = subst_1 Char (TVar(P(List(Char), P(Char, P(Char, Z)))))
let mapto2 : (char -> char list -> char -> unit, char -> char list -> unit, unit) inx_term = exts (exts mapto_1 (List(Char))) (Char)
let hole_cons : (char -> char -> char list -> unit, unit, char list) tTerm =
  (subst mapto2).shift cons1 |> shift_up Char
(* let _ = Format.printf "hole_cons = %a@." p_term hole_cons *)
type ('g, 'd) unils = ('g, 'g, 'd) inx_term list
let rec gen_unils : type a g d. (g, d) unifier -> (g, d) unils =
  let rec exunfier : type a g d. a typ -> (g, d) unils -> (a -> g, d) unils =
    fun t ->
    function
    | [] -> []
    | h :: tl -> exts h t :: exunfier t tl
  in 
  function
  | UNil -> []
  | UCons(typ, h, tl) ->
     mapto0 h :: (gen_unils tl |> exunfier typ)
let unify : type a g d. (g, d) unifier -> (g, d, a) tTerm -> (g, d, a) tTerm =
  fun x -> gen_unils x |> List.fold_right (fun a b -> (subst a).shift b)

let rec ctx_to_unifier : type g d. (g, d) ctx -> (g, d) unifier =
  function
  | CtxZ -> UNil
  | CtxS(t, ctx) -> UCons(t, TVar(Z), ctx_to_unifier ctx)
open Format
let rec p_unifier : type g d. int -> Format.formatter -> (g, d) unifier -> unit =
  fun i ppf ->
  function
  | UNil -> fprintf ppf "EOU"
  | UCons(typ, term, tl) ->
     fprintf ppf "%d |-> %a :: @. %a" i p_term term (p_unifier (i+1)) tl

let rec gen_index : type g b d. b typ -> (g, d) unifier -> int -> (g, d, b) index =
  fun t ctx n ->
  match ctx, n with
  | UCons(t', _, _), 0 ->
     begin
       match eq_test t' t with       
       | Some Eq -> Z
       | None -> failwith "gen_index"
     end 
  | UCons(_, _, ctx), n -> S (gen_index t ctx (n-1))
  | UNil, _ -> failwith "gen_index"

let rec dshift : type g d a b. a typ -> (g, d, b) tTerm -> (g, a -> d, b) tTerm =
  let rec dshift_index : type g b. (g, d, b) index -> (g, a -> d, b) index =
    function
    | Z -> Z
    | S i -> S (dshift_index i)
    | P(t, i) -> P(t, dshift_index i)
  in
  fun t ->
  function
  | TVar(i) -> TVar(dshift_index i)
  | TFVar(i) -> TFVar(Sf i)
  | Next _ -> failwith "dshift Next"
  | TLam(typ, term) ->
     TLam(typ, dshift t term)
  | TLamNon(typ, term) ->
     TLamNon(typ, dshift t term)
  | TApp(t1, t2) ->
     TApp(dshift t t1, dshift t t2)
  | TApp1(t1, t2) ->
     TApp1(dshift t t1, dshift t t2)
  | TApp2(t1, t2, t3) ->
     TApp2(dshift t t1, dshift t t2, dshift t t3)
  | TApp3(t1, t2, t3, t4) ->
     TApp3(dshift t t1, dshift t t2, dshift t t3, dshift t t4)
  | TApp4(t1, t2, t3, t4, t5) ->
     TApp4(dshift t t1, dshift t t2, dshift t t3, dshift t t4, dshift t t5)
  | TApp5(t1, t2, t3, t4, t5, t6) ->
     TApp5(dshift t t1, dshift t t2, dshift t t3, dshift t t4, dshift t t5, dshift t t6)
  | TOr(t1, t2) ->
     TOr(dshift t t1, dshift t t2)
  | TTrue -> TTrue
  | TFalse -> TFalse
  | Ch(c) -> Ch(c)
  | Fix(typ, term) ->
     Fix(typ, dshift t term)
  | Fix2(typf, typg, f, g) ->
     Fix2(typf, typg, dshift t f, dshift t g)   
  | Nil -> Nil
  | Cons(h, tl) ->
     Cons(dshift t h, dshift t tl)
  | Case(typ, x, nil, cons) ->
     Case(typ, dshift t x, dshift t nil, dshift t cons)
  | TIf(x1, x2, thn, els) ->
     TIf(dshift t x1, dshift t x2, dshift t thn, dshift t els)
  | Left(typ, term) -> Left(typ, dshift t term)
  | Right(typ, term) -> Right(typ, dshift t term)
  | Zero -> Zero
  | Succ n -> Succ (dshift t n)

type ('d1, 'd2) dinx_dinx = {drho : 'a 'g. ('g, 'd1, 'a) findex -> ('g, 'd2, 'a) findex}
let rec dext : type g d1 d2. (d1, d2) dinx_dinx -> ('b -> d1, 'b -> d2) dinx_dinx =
  fun drho ->
  let f : type a g b. (g, b -> d1, a) findex -> (g, b -> d2, a) findex =
    function
    | Sf x -> Sf (drho.drho x)
    | Zf -> Zf
  in {drho = f}
type ('d1, 'd2) dterm_dterm = {dshift : 'a 'g. ('g, 'd1, 'a) tTerm -> ('g, 'd2, 'a) tTerm}
let rec rename_index : type a g d1 d2. (g, d1, a) index -> (g, d2, a) index =
  function
  | Z -> Z
  | S i -> S (rename_index i)
  | P(t, i) -> P(t, rename_index i)
  
let rec rename_ctx : type g d1 d2. (g, d1) ctx -> (g, d2) ctx =
  function
  | CtxZ -> CtxZ
  | CtxS(t, c) -> CtxS(t, rename_ctx c)
  

let rec drename : type d1 d2. (d1, d2) dinx_dinx -> (d1, d2) dterm_dterm =
  fun drho ->
  let f : type g a. (g, d1, a) tTerm -> (g, d2, a) tTerm =
    function
    | TVar(i) -> TVar(rename_index i)
    | Next(t, f) -> Next(t, (drename (dext drho)).dshift f)
    | TLam(typ, t) -> TLam(typ, (drename drho).dshift t)
    | TLamNon(typ, t) -> TLamNon(typ, (drename drho).dshift t)
    | TApp(f, x) -> TApp((drename drho).dshift f, (drename drho).dshift x)
    | TApp1(f, x) -> TApp1((drename drho).dshift f, (drename drho).dshift x)
    | TApp2(f, x0, x1) -> TApp2((drename drho).dshift f, (drename drho).dshift x0, (drename drho).dshift x1)
    | TApp3(f, x0, x1, x2) -> TApp3((drename drho).dshift f, (drename drho).dshift x0, (drename drho).dshift x1, (drename drho).dshift x2)
    | TApp4(f, x0, x1, x2, x3) -> TApp4((drename drho).dshift f, (drename drho).dshift x0, (drename drho).dshift x1, (drename drho).dshift x2, (drename drho).dshift x3)
    | TApp5(f, x0, x1, x2, x3, x4) -> TApp5((drename drho).dshift f, (drename drho).dshift x0, (drename drho).dshift x1, (drename drho).dshift x2, (drename drho).dshift x3, (drename drho).dshift x4)
    | TOr(t1, t2) -> TOr((drename drho).dshift t1, (drename drho).dshift t2)
    | Nil -> Nil
    | Cons(h, tl) -> Cons((drename drho).dshift h, (drename drho).dshift tl)
    | Case(typ, x, nil, cons) -> Case(typ, (drename drho).dshift x, (drename drho).dshift nil, (drename drho).dshift cons)
    | TIf(x1, x2, thn, els) -> TIf((drename drho).dshift x1, (drename drho).dshift x2, (drename drho).dshift thn, (drename drho).dshift els)
    | TTrue -> TTrue
    | TFalse -> TFalse
    | TFVar(i) -> TFVar(drho.drho i)
    | Ch(c) -> Ch(c)
    | Fix(typ, t) -> Fix(typ, (drename drho).dshift t)
    | Fix2(lt, rt, f, g) -> Fix2(lt, rt, (drename drho).dshift f, (drename drho).dshift g)
    | Left(rt, left) -> Left(rt, (drename drho).dshift left)
    | Right(lt, right) -> Right(lt, (drename drho).dshift right)
    | Zero -> Zero
    | Succ n -> Succ ((drename drho).dshift n)
  in {dshift = f}

let rec dshift_dterm : type d. unit -> (d, 'b -> d) dterm_dterm =
  let s : type a g. (g, d, a) findex -> (g, 'b -> d, a) findex =
    function
    | Zf -> Sf Zf
    | Sf x -> Sf (Sf x)
  in fun _ -> drename {drho = s}
let dshift_ term = (dshift_dterm ()).dshift term
exception NotValue
let undshift_dterm : type d. unit -> ('b -> d, d) dterm_dterm =
  let s : type a g d. (g, 'b -> d, a) findex -> (g, d, a) findex =
    function
    | Sf x -> x
    | _ -> raise NotValue
  in fun _ -> drename {drho = s}
let undshift term = (undshift_dterm ()).dshift term
(* type ('d1, 'd2) dinx_dterm = {dmapto : 'a 'g. ('g, 'd1, 'a) findex -> ('g, 'd2, 'a) tTerm} *)
(* let rec exts : type d1 d2. (d1, d2) dinx_dterm
 *                     -> ('b -> d1, 'b -> d2) dinx_dterm = 
 *   fun drho ->
 *   let dshift =
 *     let s : type a g d. (g, d, a) findex -> (g, 'b -> d, a) findex = fun x -> Sf x
 *     in drename {drho = s}
 *   in
 *   let f : type a d g. (g, 'b -> d1, a) findex -> (g, 'b -> d2, a) tTerm =
 *     function
 *     | Zf -> TFVar(Zf)
 *     | Sf x -> dshift.dshift (drho.dmapto x)       
 *   in {dmapto = f} *)
   

let rec dunify : type a g d. a typ -> (g, d) unifier -> (g, a -> d) unifier =
  fun typ -> 
  function
  | UCons(t, v, ctx) -> UCons(t, dshift typ v, dunify typ ctx)
  | UNil -> UNil

type 'g env =
  | ENil : unit env
  | ECons : 'a * 'g env -> ('a -> 'g) env
let rec eval : type g d a. g env -> (g, d) ctx -> d functions -> (g, d, a) tTerm -> a =
  let rec lookup : type g d a. g env -> (g, d, a) index -> a =
    fun env i ->
    match env, i with
    | ENil, i -> failwith "free variable"
    | ECons(v, _), Z -> v
    | ECons(v, env), S i -> lookup env i
    | ECons _, P _ -> failwith "minus variable"
  in
  fun env ctx funs -> 
  function
  | TVar(i) -> lookup env i             
  | TFVar(i) -> lookupf env ctx funs i
  | Next(t, term) -> eval ENil CtxZ (Fun(t, term, funs)) term
  | TLam(t, body) -> fun x -> eval (ECons(x, env)) (CtxS(t, ctx)) funs body
  | TLamNon(t, body) -> fun x -> eval (ECons(x, env)) (CtxS(t, ctx)) funs body
  | TApp(t1, t2) -> eval env ctx funs t2 |> eval env ctx funs t1
  | TApp1(t1, t2) -> eval env ctx funs t2 |> eval env ctx funs t1
  | TApp2(t1, t2, t3) -> eval env ctx funs t3 |> (eval env ctx funs t2 |> eval env ctx funs t1)
  | TApp3(t1, t2, t3, t4) -> eval env ctx funs t4 |> (eval env ctx funs t3 |>  (eval env ctx funs t2 |> eval env ctx funs t1))
  | TApp4(t1, t2, t3, t4, t5) -> eval env ctx funs t5 |> (eval env ctx funs t4 |> (eval env ctx funs t3 |>  (eval env ctx funs t2 |> eval env ctx funs t1)))
  | TApp5(t1, t2, t3, t4, t5, t6) -> eval env ctx funs t6 |> (eval env ctx funs t5 |> (eval env ctx funs t4 |> (eval env ctx funs t3 |>  (eval env ctx funs t2 |> eval env ctx funs t1))))
  | TTrue -> true
  | TFalse -> false
  | Ch(c) -> c
  | TOr(t1, t2) -> eval env ctx funs t1 ||  eval env ctx funs t2
  | Fix(_, f) ->
     let rec self x = (eval env ctx funs f) self x in self
  | Fix2(_, _, f, g) ->
     let rec self_f x =
       (eval env ctx funs f) (self_f, self_g) x
     and self_g y =
       (eval env ctx funs g) (self_f, self_g) y
     in (self_f, self_g)
  | Nil -> []
  | Cons(h, tl) -> (eval env ctx funs h) :: (eval env ctx funs tl)
  | Case(t, x, nil, cons) ->
     begin
       match eval env ctx funs x with
       | [] -> eval env ctx funs nil
       | x :: xs -> eval (ECons(x, ECons(xs, env))) (CtxS(t, CtxS(List(t), ctx))) funs cons
     end         
  | TIf(x, a, thn, els) ->
     if eval env ctx funs x = eval env ctx funs a 
     then eval env ctx funs thn
     else eval env ctx funs els
  | Left(_, t) -> fst (eval env ctx funs t)
  | Right(_, t) -> snd (eval env ctx funs t)
  | Zero -> 0
  | Succ n -> 1 + eval env ctx funs n
and lookupf : type g d a. g env -> (g, d)  ctx -> d functions -> (g, d, a) findex -> a =
  fun env inner_ctx funs i ->
  let rec shift : type g g' d d' a. (g, d) ctx -> (g', d') ctx -> (g', d', a) tTerm -> (g, d', a) tTerm =
    fun inner_ctx outer_ctx f ->
    match inner_ctx, outer_ctx with
    | CtxZ, CtxZ -> f
    | CtxZ, _ -> failwith ""
    | CtxS(t, inner_ctx), outer_ctx -> shift inner_ctx outer_ctx f |> shift_up t
  in     
  let rec dd : type g d a. (g, a -> d) ctx -> (g, d) ctx =
    function
    | CtxZ -> CtxZ
    | CtxS(t, ctx) -> CtxS(t, dd ctx)
  in 
  match funs, i with
  | FNil, i -> failwith "free function"
  | Fun(t, f, _), Zf -> shift inner_ctx CtxZ f |> eval env inner_ctx funs 
  | Fun(t, _, funs), Sf i -> lookupf env (dd inner_ctx) funs i
