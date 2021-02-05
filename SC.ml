open Type
open TDB
open Shift
open Used
type ('g, 'd) context = ('g, 'd) unifier

type ahead =
  | Temae  
  | Just
(* fun_type が関数型の時のみ、すなわち、自由変数が１つ以上必要 *)
(* let bind_call : type g g' d a b. (g, a -> d) context -> a typ -> b typ -> (g, a -> d, b) tTerm =
 *   fun context fun_type ret_type ->
 *   let rec down_shift : type g a d b. (a -> g, d, b) findex -> (g, d, b) findex =
 *     function
 *     | Zf -> Zf
 *     | Sf i -> Sf (down_shift i)
 *   in
 *   let rec bottom : type g a' b. (g, a -> d) context -> a' typ -> (g, a -> d, a') tTerm * (g, a -> d) context =
 *     fun ctx atyp ->
 *     match ctx with
 *     | UNil -> failwith "type not match"
 *     | UCons(t, _, UNil) ->
 *        begin
 *          match eq_test t atyp with
 *          | Some Eq -> TVar(Z), ctx
 *          | None -> failwith "fun_type is not correct"
 *        end
 *     | UCons(t, v, UCons(t', v', ctx)) ->
 *        let (term, ctx) = bottom (UCons(t', v', ctx)) atyp in
 *        (shift_up t term, UCons(t, v, ctx))
 *   in 
 *   let rec loop : type f a0 g. (g, a -> d) context -> f typ -> (g, a -> d, f) tTerm -> (g, a -> d, b) tTerm =
 *     fun ctx f_type term ->
 *     match f_type, eq_test f_type ret_type with
 *     | Arrow(t, f_type), _ ->
 *        let (arg, ctx) = bottom ctx t in
 *        loop ctx f_type (TApp(term, arg))
 *     | _, Some Eq -> term
 *     | _, None -> failwith "memo error"
 *   and next : type g. (g, a -> d) context -> (g, a -> d, a) findex -> (g, a -> d, b) tTerm =
 *     fun ctx index ->
 *     match step ctx fun_type, ctx with
 *     | Temae, UCons(t, _, tl) -> next tl (down_shift index) |> shift_up t
 *     | Just, _ ->
 *        (\* let _ = Format.printf "ftyp = %a@." p_type fun_type   in
 *         * let _ = Format.printf "ctx = %a@." (p_unifier 0) ctx  in *\)
 *        loop ctx fun_type (TFVar(index)) 
 *     | _, _ -> failwith "bind_call"
 *   and step : type g b0 d. (g, d) context -> b0 typ -> ahead =
 *     fun ctx call ->
 *     match ctx, call with
 *     | UCons(_, _, ctx), Arrow(_, call) -> step ctx call
 *     | UCons(_, _, ctx), _ -> Temae
 *     | UNil, _ -> Just                  
 *   in
 *   next context Zf *)
let bind_call : type g d a return.
                     (g, a -> d) context ->
                     a typ ->
                     return typ ->
                     (g, a -> d, return) tTerm =
  fun context fun_type ret_type ->
  let rec countA : type a. a typ -> int =
    function
    | Arrow(_, t) -> countA t + 1
    | _ -> 0
  in
  let rec pick : type g t. t typ -> (g, a -> d) context -> int -> (g, a -> d, t) tTerm =
    fun t ->
    function
    | UCons(t', term, tl) ->
       fun n -> if n = 0 then
                  begin
                    match eq_test t' t with
                    | Some Eq -> term
                    | None -> failwith "fun_type is not correct"
                  end
                else pick t tl (n-1) |> shift_up t'
    | UNil -> failwith "fun_type is not correct"
  in
  let rec next : type g. (g, a -> d) context -> (g, a -> d, return) tTerm =
    let rec step : type g b0 d. (g, d) context -> b0 typ -> ahead =
      fun ctx call ->
      match ctx, call with
      | UCons(_, _, ctx), Arrow(_, call) -> step ctx call
      | UCons(_, _, ctx), _ -> Temae
      | UNil, _ -> Just                  
    in
    fun ctx ->
    match step ctx fun_type, ctx with
    | Just, _ -> 
       let rec gen_app : type t. t typ -> (g, a -> d, t) tTerm -> (g, a -> d, return) tTerm =
         fun t term ->
         match t with
         | Arrow(tn, tn_1) ->
            TApp(term, pick tn ctx (countA t - 1)) |> gen_app tn_1
         | _ ->
            begin
              match eq_test t ret_type with
              | Some Eq -> term
              | None -> failwith "gen_app error"
            end
       in gen_app fun_type (TFVar(Zf))
    | Temae, UCons(t, _, tl) ->
       next tl |> shift_up t
    | _, _  -> failwith "bind_call"
  in
  next context
(* let context1 = UCons(Bool, TVar(Z), UCons(Char, TVar(Z), UNil))
 * let fun_type = Char => (Bool => List(Char))
 * let _ = bind_call context1 fun_type (List(Char)) |> Format.printf "%a@." p_term *)
(* 
    f0 xs x'
let f1 (xs:list) (ys:bool) = 
and f2 xs ys x' xs' =
let z = ... in        [_:bool, _:list]
     f xs ys (* ctx = [z:int; x':bool; xs':list; x':bool; ys:bool; xs:list;] *)
ftyp = ([C])->([C])->([C])->([C])->(C)->([C])->(C)->B
         xs     ys     zs     ys'   y'        xs'   x'
        f xs ys zs ys' y' xs' x'
        match xs with
          |       x' :: xs' -> _______ [0 |-> x'; 1 |-> xs'; ....] 
 *)
type ('g, 'd, 'return) call =
  (* 'function_type = a0 -> a1 -> ... -> 'return *)
  | Call : ('g, 'd, 'return) tTerm -> ('g, 'd, 'return) call
  | PC : 'a typ * ('a -> 'g, 'd, 'return) call -> ('g, 'd, 'return) call
let rec p_call : type g d r. Format.formatter -> (g, d, r) call -> unit =
  fun ppf ->
  function
  | PC(t, call) -> Format.fprintf ppf "PC(%a, %a)" p_type t p_call call
  | Call(term) -> Format.fprintf ppf "term";
type ('g1, 'g2, 'd) call_call = {cshift : 'a. ('g1, 'd, 'a) call -> ('g2, 'd, 'a) call}
let rec call_rename : type g1 g2 d. (g1, g2, d) inx_inx -> (g1, g2, d) call_call =
  fun rho ->
  let f : type a g. (g1, d, a) call -> (g2, d, a) call =
    function
    | Call(term) -> Call((rename rho).shift term)
    | PC(t, call) -> PC(t, (call_rename (ext rho t)).cshift call)
  in {cshift = f}
let downshift_call : type g a b d. (b -> g, d, a) call -> (g, d, a) call =
  fun call -> 
    let s : type a g. (b -> g, d, a) index -> (g, d, a) index =
    function
    | S i -> i
    | i -> failwith "downshift"
  in
  (call_rename {rho = s}).cshift call

type 'd memo =
  | MNil : unit memo
  | MCons : (unit, 'd, 'return) call * 'd memo -> ('f_typ -> 'd) memo
  
(* type ('g, 'd) memo = (\* brachで共有しない *\)
 *   | EOM : ('g, 'd) memo
 *   | Memo1 : ('g, 'd, 'a0 -> 'return) tTerm
 *             * (('g, 'd, 'a0) tTerm * ('g, 'd, 'return) call) list
 *             * ('g, 'd) memo
 *             -> ('g, 'd) memo
 *   | Memo2 : ('g, 'd, 'a0 -> 'a1 -> 'return) tTerm
 *             * (('g, 'd, 'a0) tTerm * ('g, 'd, 'a1) tTerm * ('g, 'd, 'return) call) list
 *             * ('g, 'd) memo
 *             -> ('g, 'd) memo
 *   | Memo3 : ('g, 'd, 'a0 -> 'a1 -> 'a2 -> 'return) tTerm
 *             * (('g, 'd, 'a0) tTerm * ('g, 'd, 'a1) tTerm * ('g, 'd, 'a2) tTerm * ('g, 'd, 'return) call) list
 *             * ('g, 'd) memo
 *             -> ('g, 'd) memo
 *   | Memo4 : ('g, 'd, 'a0 -> 'a1 -> 'a2 -> 'a3 -> 'return) tTerm
 *             * (('g, 'd, 'a0) tTerm * ('g, 'd, 'a1) tTerm * ('g, 'd, 'a2) tTerm * ('g, 'd, 'a3) tTerm * ('g, 'd, 'return) call) list
 *             * ('g, 'd) memo
 *             -> ('g, 'd) memo
 *   | Memo5 : ('g, 'd, 'a0 -> 'a1 -> 'a2 -> 'a3 -> 'a4 -> 'return) tTerm
 *             * (('g, 'd, 'a0) tTerm * ('g, 'd, 'a1) tTerm * ('g, 'd, 'a2) tTerm * ('g, 'd, 'a3) tTerm * ('g, 'd, 'a4) tTerm * ('g, 'd, 'return) call) list
 *             * ('g, 'd) memo
 *             -> ('g, 'd) memo
 *   | SMemo : 'a typ * ('g, 'd) memo -> ('a -> 'g, 'd) memo *)
(* let rec ctx_to_memo : type g d. (g, d) ctx -> (g, d) memo =
 *   function
 *   | CtxZ -> EOM
 *   | CtxS(t, ctx) -> SMemo(t, ctx_to_memo ctx) *)
let rec ctx_to_memo : type g d. (g, unit) ctx -> unit memo = fun _ -> MNil

(* (\* 安易に正規化しないように *\)
 * let rec normalize_memo : type g d. (g, d) memo -> (g, d) memo =
 *   let shift_call : type a g d b. a typ -> (g, d, b) call -> (a -> g, d, b) call =
 *     let rec shift_findex : type g d b. (g, d, b) findex -> (a -> g, d, b) findex =
 *       function
 *       | Zf -> Zf
 *       | Sf i -> Sf (shift_findex i)
 *     in 
 *     fun typ (Call(return, fun_type, index)) ->
 *     Call(return, fun_type, shift_findex index)
 *   in
 *   let rec ex_memo : type a g d. a typ -> (g, d) memo -> (a -> g, d) memo =
 *     fun t ->
 *     function
 *     | Memo1(f, memo, tl) ->
 *        Memo1(shift_up t f, List.map (fun (a0, c) -> shift_up t a0, shift_call t c) memo,  ex_memo t tl)
 *     | Memo2(f, memo, tl) ->
 *        Memo2(shift_up t f,
 *              List.map (fun (a0, a1, c) -> shift_up t a0, shift_up t a1, shift_call t c) memo,
 *              ex_memo t tl)        
 *     | Memo3(f, memo, tl) ->
 *        Memo3(shift_up t f,
 *              List.map (fun (a0, a1, a2, c) -> shift_up t a0, shift_up t a1, shift_up t a2, shift_call t c) memo,
 *              ex_memo t tl)        
 *     | Memo4(f, memo, tl) ->
 *        Memo4(shift_up t f,
 *              List.map (fun (a0, a1, a2, a3, c) -> shift_up t a0, shift_up t a1, shift_up t a2, shift_up t a3, shift_call t c) memo,
 *              ex_memo t tl)
 *     | Memo5(f, memo, tl) ->
 *        Memo5(shift_up t f,
 *              List.map (fun (a0, a1, a2, a3, a4, c) -> shift_up t a0, shift_up t a1, shift_up t a2, shift_up t a3 , shift_up t a4, shift_call t c) memo,
 *              ex_memo t tl)
 *     | SMemo(t', memo) -> ex_memo t' memo |> ex_memo t
 *     | EOM -> EOM
 *   in
 *   function
 *   | SMemo(t, memo) -> ex_memo t memo
 *   | memo -> memo
 * 
 * let rec p_memo : type g d. Format.formatter -> (g, d) memo -> unit =
 *   fun ppf ->
 *   let p_arg1 ppf =
 *     List.fold_left (fun _ (a0, call) -> Format.fprintf ppf "(%a) :m: " p_term a0) ()
 *   in
 *   let p_arg2 ppf =
 *     List.fold_left (fun _ (a0, a1, call) -> Format.fprintf ppf "(%a, %a) :m: " p_term a0 p_term a1) ()
 *   in
 *   let p_arg3 ppf =
 *     List.fold_left (fun _ (a0, a1, a2, call) -> Format.fprintf ppf "(%a, %a, %a) :m: " p_term a0 p_term a1 p_term a2) ()
 *   in
 *   let p_arg4 ppf =
 *     List.fold_left (fun _ (a0, a1, a2, a3, call) -> Format.fprintf ppf "(%a, %a, %a, %a) :m: " p_term a0 p_term a1 p_term a2 p_term a3) ()
 *   in
 *   let p_arg5 ppf =
 *     List.fold_left (fun _ (a0, a1, a2, a3, a4, call) -> Format.fprintf ppf "(%a, %a, %a, %a, %a) :m: " p_term a0 p_term a1 p_term a2 p_term a3 p_term a4) ()
 *   in  
 *   function
 *   | EOM -> Format.fprintf ppf "EOM"
 *   | Memo1(f, memo, tl) ->
 *      Format.fprintf ppf "@[<v 2> %a with [%a] @] %a" p_term f p_arg1 memo p_memo tl
 *   | Memo2(f, memo, tl) ->
 *      Format.fprintf ppf "@[<v 2> %a with [%a] @] %a" p_term f p_arg2 memo p_memo tl
 *   | Memo3(f, memo, tl) ->
 *      Format.fprintf ppf "@[<v 2> %a with [%a] @] %a" p_term f p_arg3 memo p_memo tl
 *   | Memo4(f, memo, tl) ->
 *      Format.fprintf ppf "@[<v 2> %a with [%a] @] %a" p_term f p_arg4 memo p_memo tl
 *   | Memo5(f, memo, tl) ->
 *      Format.fprintf ppf "@[<v 2> %a with [%a] @] %a" p_term f p_arg5 memo p_memo tl
 *   | SMemo(t, memo) -> failwith "print SMemo" *)

(* let rec d_memo : type g d a. a typ -> (g, d) memo -> (g, a -> d) memo =
 *   fun t -> 
 *   function
 *   | Memo1(f, memo, tl) ->
 *      Memo1(dshift t f, List.map (fun (a0, (Call(ret, ftyp, i))) -> dshift t a0, Call(ret, ftyp, Sf i)) memo,  d_memo t tl)
 *   | Memo2(f, memo, tl) ->
 *      Memo2(dshift t f,
 *            List.map (fun (a0, a1, (Call(ret, ftyp, i))) -> dshift t a0, dshift t a1, Call(ret, ftyp, Sf i)) memo,
 *            d_memo t tl)        
 *   | Memo3(f, memo, tl) ->
 *      Memo3(dshift t f,
 *            List.map (fun (a0, a1, a2, (Call(ret, ftyp, i))) -> dshift t a0, dshift t a1, dshift t a2, Call(ret, ftyp, Sf i)) memo,
 *            d_memo t tl)        
 *   | Memo4(f, memo, tl) ->
 *      Memo4(dshift t f,
 *            List.map (fun (a0, a1, a2, a3, (Call(ret, ftyp, i))) -> dshift t a0, dshift t a1, dshift t a2, dshift t a3, Call(ret, ftyp, Sf i)) memo,
 *            d_memo t tl)
 *   | Memo5(f, memo, tl) ->
 *      Memo5(dshift t f,
 *            List.map (fun (a0, a1, a2, a3, a4, (Call(ret, ftyp, i))) -> dshift t a0, dshift t a1, dshift t a2, dshift t a3, dshift t a4, Call(ret, ftyp, Sf i)) memo,
 *            d_memo t tl)
 *   | SMemo(t', memo) -> SMemo(t', d_memo t memo)
 *   | EOM -> EOM *)
     
let assuming_eq_fun = eq_term
type ('g, 'd) renaming = ('g, 'd) unifier

let rec flush : type g d. (g, d) unifier -> (g, d) renaming =
  function
  | UNil -> UNil
  | UCons(t, _, tl) -> UCons(t, TVar(Z), flush tl)
let rec renaming_to_ctx : type g d. (g, d) renaming -> (g, d) ctx =
    function
    | UNil -> CtxZ
    | UCons(t, _, tl) -> CtxS(t, renaming_to_ctx tl)

let rec assuming_eq_arg : type g a b d. (g, d) renaming -> d functions -> (g, d, a) tTerm -> (g, d, a) tTerm -> (g, d) renaming option =
  let rec cut : type g a. (a -> g, d) renaming option -> (g, d) renaming option =
    function
    | Some(UCons(_, _, rho)) -> Some(rho)
    | None -> None
  in
  let rec gen_rho :  type a b g d. (g, d) renaming -> (g, d, a) index -> (g, d, a) index -> (g, d) renaming option =
  fun rho inx inx' ->                                                         
  match rho, inx, inx' with
  | UNil, _, _ -> failwith "free varriable"                  
  | UCons(typ, TVar(Z), tl), i, Z -> Some(UCons(typ, TVar(i), tl))
  | UCons(typ, TVar(i'), tl), i, Z ->
     begin
       match eq_index i i' with
       | Some IndexEq -> Some(UCons(typ, TVar(i), tl))
       | None -> None
     end
  | UCons(typ, _, tl), i, Z -> None (* Exists other renaming *)
  | UCons(typ, v, tl), S i, S i' -> gen' typ v tl i i'
  | UCons(typ, v, tl), i, S i' -> gen' typ v tl (P(typ, i)) i'
  | _, _, P _ -> failwith "down rename"
  and gen' : type a b g d. a typ -> (a -> g, d, a) tTerm
                  -> (g, d) renaming
                  -> (g, d, b) index
                  -> (g, d, b) index
                  -> (a -> g, d) renaming option = 
                  
    fun typ v tl i i' -> 
    match gen_rho tl i i' with
    | Some(tl) -> Some(UCons(typ, v, tl))
    | None -> None
  in
  fun rho funs t1 t2 ->
  (* let _ = Format.printf "arg = %a, arg' = %a@." p_term t1 p_term t2 in *)
  (* let _ = Format.printf "t1 = %a, t2 = %a@." p_term t1 p_term t2 in *)
  match t1, t2 with                                                             
  | Cons(h1, t1), Cons(h2, t2) ->
     begin
       match assuming_eq_arg rho funs h1 h2 with
       | Some(rho) -> assuming_eq_arg rho funs t1 t2
       | None -> None
     end     
  | TTrue, TTrue -> Some(rho)                                                        
  | TFalse, TFalse -> Some(rho)                                                      
  | Ch(c), Ch(c') -> if c = c' then Some(rho) else None
  | TVar(i1), TVar(i2) -> gen_rho rho i1 i2                     
  | Nil, Nil -> Some(rho)                                                  
  | TApp(f1, x1) , TApp(f2, x2) -> (* 禁じ手 *)
     begin
       match eq_test (infer (renaming_to_ctx rho) funs x1)
               (infer (renaming_to_ctx rho) funs x2) with
       | Some Eq -> 
          begin
            match assuming_eq_arg rho funs f1 f2 with
            | Some(rho) -> assuming_eq_arg rho funs x1 x2
            | None -> None
          end
       | None -> None
     end
  | TLam(t1, b1), TLam(t2, b2) ->
     begin
       match eq_test t1 t2 with
       | Some Eq -> assuming_eq_arg (UCons(t1, TVar(Z), rho)) funs b1 b2 |> cut
       | None -> None
     end
  | TLamNon(t1, b1), TLamNon(t2, b2) ->
     begin
       match eq_test t1 t2 with
       | Some Eq -> assuming_eq_arg (UCons(t1, TVar(Z), rho)) funs b1 b2 |> cut
       | None -> None
     end
  | Case(t1, x1, nil1, cons1), Case(t2, x2, nil2, cons2) ->
     begin
       match eq_test t1 t2 with
       | Some Eq ->
          begin
            match assuming_eq_arg rho funs x1 x2 with
            | Some(rho) ->
               begin
                 match assuming_eq_arg rho funs nil1 nil2 with
                 | Some(rho) ->  assuming_eq_arg (UCons(t1, TVar(Z), UCons(List(t1), TVar(Z), rho))) funs cons1 cons2 |> cut |> cut
                 | None -> None
               end
            | None -> None
          end
       | None -> None
     end
  | TIf(x1, v1, thn1, els1), TIf(x2, v2, thn2, els2) ->
     begin
       match eq_test (infer (renaming_to_ctx rho) funs x1)
               (infer (renaming_to_ctx rho) funs x2) with
       | Some Eq -> 

          begin
            match assuming_eq_arg rho funs x1 x2 with
            | Some(rho) ->
               begin
                 match eq_test (infer (renaming_to_ctx rho) funs v1)
                         (infer (renaming_to_ctx rho) funs v2) with
                 | Some Eq -> 
                    begin
                      match assuming_eq_arg rho funs v1 v2 with
                      | Some(rho) ->
                         begin
                           match assuming_eq_arg rho funs thn1 thn2 with
                           | Some(rho) ->  assuming_eq_arg rho funs els1 els2
                           | None -> None
                         end
                      | None -> None
                    end
                 | None -> None
               end
            | None -> None
          end
       | None -> None               
     end
  | TApp1(f1, x1) , TApp1(f2, x2) ->
     assuming_eq_arg rho funs 
       (TApp(f1, x1))
       (TApp(f2, x2))
  | TApp2(f1, x1, y1), TApp2(f2, x2, y2) ->
     assuming_eq_arg rho funs 
       (TApp(TApp(f1, x1), y1))
       (TApp(TApp(f2, x2), y2))
  | TApp3(f1, x1, y1, z1), TApp3(f2, x2, y2, z2) ->
     assuming_eq_arg rho funs
       (TApp(TApp(TApp(f1, x1), y1), z1))
       (TApp(TApp(TApp(f2, x2), y2), z2))
  | TApp4(f1, x1, y1, z1, w1), TApp4(f2, x2, y2, z2, w2) ->
     assuming_eq_arg rho funs 
       (TApp(TApp(TApp(TApp(f1, x1), y1), z1), w1))
       (TApp(TApp(TApp(TApp(f2, x2), y2), z2), w2))
  | TApp5(f1, x1, y1, z1, w1, u1), TApp5(f2, x2, y2, z2, w2, u2) ->
     assuming_eq_arg rho funs
       (TApp(TApp(TApp(TApp(TApp(f1, x1), y1), z1), w1), u1))
       (TApp(TApp(TApp(TApp(TApp(f2, x2), y2), z2), w2), u2))
  | Fix2(lt1, rt1, l1, r1), Fix2(lt2, rt2, l2, r2) ->
     begin
       match eq_test lt1 lt2, eq_test rt1 rt2 with
       | Some Eq, Some Eq ->
          begin
            match assuming_eq_arg rho funs l1 l2 with
            | Some(rho) -> assuming_eq_arg rho funs r1 r2
            | None -> None
          end
       | _, _ -> None
     end
  | Fix(t1, f1), Fix(t2, f2) -> 
     begin
       match eq_test t1 t2 with
       | Some Eq -> assuming_eq_arg rho funs f1 f2
       | None -> None
     end
  | Left(rt1, left1), Left(rt2, left2) ->
     begin
       match eq_test rt1 rt2 with
       | Some Eq -> assuming_eq_arg rho funs left1 left2
       | None -> None
     end 
  | Right(lt1, right1), Right(lt2, right2) ->
     begin
       match eq_test lt1 lt2 with
       | Some Eq -> assuming_eq_arg rho funs right1 right2
       | None -> None
     end
  | Zero, Zero -> Some(rho)
  | Succ n, Succ n' -> assuming_eq_arg rho funs n n'
  | _, _ -> None
                 

(* let _ = 
 *   let (arg0, arg1) = TVar(Z), TVar(S Z) in
 *   let u1 = UCons(Bool, TVar(Z), UCons(Bool, TVar(P(Bool, Z)), UNil)) in
 *   let Some(rho) = assuming_eq_arg u1 arg0 arg1 in
 *   Format.printf "hit! %a@." (p_unifier 0) rho *)

(* let unify : type g a. g unifier -> (g, a) tTerm -> (g, a) tTerm =
 *   fun unifier term ->
 *   let rec loop i =
 *     let i' = unify unifier i in 
 *     if  i' = i then i else loop i'
 *   in loop term
 * 
 * type 'g linker = 'g unifier
 * let ex_link : type a g. a typ -> g linker -> (a -> g) linker =
 *   fun t u -> UCons(t, TVar(Z), u)
 * let redirect : type a g. g linker -> (g, a) tTerm -> (g, a) tTerm =
 *   fun x term -> gen_unils x |> List.fold_left (fun b a -> (subst a).shift b) term *)


(* let ushort = UCons(Char, TVar(Z), UNil)
 * let ulong = UCons(Bool, TVar(Z), UCons(Char, TVar(Z), UCons(Arrow(Char, Bool), TVar(Z), ushort)))
 * let _ = Format.printf "%a@." p_term (bind_call ulong ushort Bool) *)
let rec und_rename : type g d f. (g, f -> d) renaming -> (g, d) renaming =
    function
    | UNil -> UNil
    | UCons(t, term, tl) -> UCons(t, undshift term, und_rename tl)
    
let rec d_rename : type g d. (g, d) renaming -> (g, 'f -> d) renaming =
    function
    | UNil -> UNil
    | UCons(t, term, tl) -> UCons(t, dshift_ term, d_rename tl)

let rec assuming_eq : type g b d. (g, d) renaming -> d memo -> d functions -> (g, d, b) tTerm ->
                           (g, d, b) tTerm option =
  let rec dshift_call : type a g d f b. (g, d, b) call -> (g, f -> d, b) call =
    function
    | PC(t, call) -> PC(t, dshift_call call)
    | Call(term) -> Call(dshift_ term)
  in 
  let rec shift_call : type a g d f. a typ -> (g, d, f) call -> (a -> g, d, f) call =
    fun atyp ->
    function
    | PC(t, call) ->
       begin 
         match eq_test t atyp with
         | Some Eq -> call
         | None -> failwith "shift_call"
       end
    | Call(term) -> Call(shift_up atyp term)
  in
  let rec normalize : type g d b. (g, d) renaming -> (unit, d, b) call -> (g, d, b) call  = 
    fun rho call ->
    match rho with
    | UNil -> call
    | UCons(t, _, tl) -> normalize tl call |> shift_call t 
  in
  fun rho memo funs call ->
  match memo, funs with
  | MNil, _ -> (* Format.printf "----------@."; *) None
  | MCons(call', tl), Fun(t, _, funs') ->
     let Call(call'') = normalize rho (dshift_call call') in
     let typ_call'' = infer (renaming_to_ctx rho) funs call'' in
     begin
       match eq_test (infer (renaming_to_ctx rho) funs call) typ_call'' with
       | Some Eq ->
          (* Format.printf "call = %a@.memo = %a@." p_term call p_term call''; *)
          begin
            match assuming_eq_arg rho funs call call'' with
            | Some(rho) ->
               let call_form = bind_call rho t typ_call'' |> unify rho in
               (* Format.printf "hit!@.%a@." p_term call_form; *)
               Some(call_form)
            | None -> next rho funs' tl call
          end
       | None -> next rho funs' tl call
     end 
and next : type g d a b. (g, b -> d) renaming -> d functions -> d memo -> (g, b -> d, a) tTerm ->
                (g, b -> d, a) tTerm option = 
  fun rho funs tl call ->
  match assuming_eq (und_rename rho) tl funs (undshift call) with
  | Some(call) -> Some(dshift_ call)
  | None -> None
  
(* kind of tail recursion *)
let rec case_ext : type a g d.
                        (g, d) unifier ->
                        (g, d, a list) index ->
                        (g, d, a) index ->
                        (g, d, a list) index ->
                        (g, d) unifier =
  fun unifier inx ->
  match unifier, inx with
  | UNil, _ -> failwith "free varriable"
  | UCons(typ, _, tl), Z ->
     fun x xs -> 
     UCons(typ, Cons(TVar(x), TVar(xs)), tl)
  | UCons(typ, v, tl), S i ->
     fun x xs -> 
     UCons(typ, v, case_ext tl i (P(typ, x)) (P(typ, xs)))
  | _ -> failwith "case with minus index"
let rec case_ext_nil : type a g d. (g, d) unifier -> a typ -> (g, d, a list) index -> (g, d) unifier =
  fun unifier t inx ->
  match unifier, inx with
  | UNil, _ -> failwith "free varriable"
  | UCons(typ, _, tl), Z ->
     let _ = Format.printf "case_ext_nil %a@." p_type in
     begin
       match eq_test typ (List(Char)) with
       | Some Eq -> UCons(typ, Nil, tl)
       | None -> failwith "char list"
     end
  | UCons(typ, v, tl), S x -> UCons(typ, v, case_ext_nil tl t x)
  | _ -> failwith "case with minus index"
       
let rec if_ext :  type a g d. (g, d) unifier -> bool -> (g, d, bool) index -> (g, d) unifier =
  fun unifier b inx ->
  match unifier, inx with
  | UNil, _ -> failwith "free varriable"
  | UCons(typ, _, tl), Z ->
     UCons(typ, (if b then TTrue else TFalse), tl)
  | UCons(typ, v, tl), S x -> UCons(typ, v, if_ext tl b x)
  | _ -> failwith "if with minus index"

let rec if_ext_c :  type a g d. (g, d) unifier -> char -> (g, d, char) index -> (g, d) unifier =
  fun unifier c inx ->
  match unifier, inx with
  | UNil, _ -> failwith "free varriable"
  | UCons(typ, _, tl), Z ->
     UCons(typ, Ch(c), tl)
  | UCons(typ, v, tl), S x -> UCons(typ, v, if_ext_c tl c x)
  | _ -> failwith "if with minus index"
       

(* let rec bind_free : type g a. g unifier -> (g, a) tTerm -> (g, a) tTerm =
 *   function
 *   | UNil -> fun t -> t
 *   | UCons(typ, v, tl) ->
 *      fun t ->
 *      let f = TLam(typ, t) |> bind_free tl |> shift_up typ
 *      in TApp(f, v) *)
   
(* type (_, _) app =
 *   | Body : ('g, 'a -> 'b) tTerm -> ('g, 'a -> 'b) app
 *   | App : 'a typ * ('g, 'a -> 'b) app * ('a -> 'g, 'a) tTerm -> ('a -> 'g, 'b) app
 * 
 * 
 * let rec bind_free_type : type g a. g unifier -> (g, a) tTerm -> (g, a) app =
 *   function
 *   | UNil ->
 *      begin
 *        function
 *        | TLam(typ, body) -> Body(TLam(typ, body))
 *        | _ -> failwith ""
 *      end    
 *   | UCons(typ, v, tl) ->
 *      fun t ->
 *      let f = TLam(typ, t) |> bind_free_type tl
 *      in App(typ, f, v)
 * 
 * let rec addfix : type g a. a typ -> (g, a) app -> (g, a) tTerm =
 *   fun typ ->
 *   function
 *   | Body lambda -> Fix(typ, TLam(typ, shift_up typ lambda))
 *   | App(typ', f, v) ->
 *      TApp(addfix (Arrow(typ', typ)) f |> shift_up typ', v) *)
(* let rec run_arg : type a g d. (g, d) ctx -> d functions -> (g, d, a) tTerm -> (g, d, a) tTerm option =
 *   let dd = rename_ctx in
 *   let rec shift : type g g' d d' a. (g, d) ctx -> (g', d') ctx -> (g', d', a) tTerm -> (g, d', a) tTerm =
 *     fun inner_ctx outer_ctx f ->
 *     match inner_ctx, outer_ctx with
 *     | CtxZ, CtxZ -> f
 *     | CtxZ, _ -> failwith ""
 *     | CtxS(t, inner_ctx), outer_ctx -> shift inner_ctx outer_ctx f |> shift_up t
 *   in
 *   let rec flookup : type g d a. d functions -> (g, d, a) findex -> (unit, d, a) tTerm =
 *     fun funs i ->
 *     match funs, i with
 *     | FNil, _ -> .
 *     | Fun(_, f, _), Zf -> f
 *     | Fun(_, _, funs), Sf i -> dshift_ (flookup funs i)
 *   in 
 *   fun ctx funs ->
 *   function
 *   | Next(t, f) ->
 *      begin
 *        try
 *          begin
 *            match shift ctx CtxZ f |> run_arg (dd ctx) (Fun(t, f, funs)) with
 *            | Some(v) -> Some(undshift v)
 *            | None -> None
 *          end 
 *        with
 *        | NotValue -> None
 *        | e -> None
 *      end 
 *   | TFVar(i) -> Some(flookup funs i |> shift ctx CtxZ)
 *   | TVar(i) -> Some(TVar(i))          (\* run after subst  *\)
 *   | TLam(t, body) -> Some(TLam(t, body))
 *   | TLamNon(t, body) -> Some(TLamNon(t, body))
 *   | TApp(f, x) ->
 *      begin
 *        match run_arg ctx funs f, run_arg ctx funs x with
 *        | Some(TLam(t, body)), Some(x) -> subst0 t body x |> run_arg ctx funs
 *        | Some(TLamNon(t, body)), Some(x) -> subst0 t body x |> run_arg ctx funs
 *        | t, _ -> None          
 *      end      
 *   | TOr(t1, t2) ->
 *      begin 
 *        match run_arg ctx funs t1, run_arg ctx funs t2 with 
 *        | Some(t1), Some(t2) -> Some(TOr(t1, t2))
 *        | _, _ -> None
 *      end 
 *   | Cons(h, tl) ->
 *      begin 
 *        match run_arg ctx funs h, run_arg ctx funs tl with 
 *        | Some(t1), Some(t2) -> Some(Cons(t1, t2))
 *        | _, _ -> None
 *      end 
 *   | Nil -> Some(Nil)
 *   | Ch(c) -> Some(Ch(c))
 *   | TTrue -> Some(TTrue)
 *   | TFalse -> Some(TFalse)
 *   | term ->
 *      Format.printf "others like %a@." p_term term;
 *      None *)
let isobserval : type a g d. (g, a, d) tTerm -> bool =
  function
  | TLam _ -> true
  | TLamNon _ -> true
  | Cons _ -> true
  | Nil -> true
  | Succ _ -> true
  | Zero -> true
  | TTrue -> true
  | TFalse -> true
  | TVar _ -> true              (* unifierを適用した後 *)
  | TOr _ -> false
  | TApp _ -> false
  | TApp1 _ -> false
  | TApp2 _ -> false
  | TApp3 _ -> false
  | TApp4 _ -> false
  | TApp5 _ -> false
  | Ch _ -> false
  | Next _ -> false
  | TFVar _ -> false
  | TIf _ -> false
  | Case _ -> false
  | Fix _ -> false
  | Fix2 _ -> false
  | Left _ -> false
  | Right _ -> false
let rec gen_context_f : type a c g g' d f. a typ -> (g, f -> d) ctx -> (f -> d) functions -> (a -> g, d, c) tTerm -> (g, f -> d, c) tTerm -> (a -> g, f -> d, c) tTerm =
  fun etyp ctx funs old_e fn ->
  let rec loop : type c. (a -> g, d, c) tTerm -> (g, f -> d, c) tTerm -> (a -> g, f -> d, c) tTerm =
    fun old_e fn -> 
    match old_e, fn with
    | TVar(Z), _ -> TVar(Z)
    | TApp1(f, a0), TApp1(f', a0') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs (dshift_ f)) (infer ctx funs f') with
         | Some Eq -> 
            TApp1(shift_up etyp f', loop a0 a0')
         | None -> failwith "gen_context"
       end 
    | TApp2(f, a0, a1), TApp2(f', a0', a1') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs (dshift_ f)) (infer ctx funs f') with
         | Some Eq -> 
            TApp2(shift_up etyp f', loop a0 a0', loop a1 a1')
         | None -> failwith "gen_context"
       end
    | TApp3(f, a0, a1, a2), TApp3(f', a0', a1', a2') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs (dshift_ f)) (infer ctx funs f') with
         | Some Eq -> 
            TApp3(shift_up etyp f', loop a0 a0', loop a1 a1', loop a2 a2')
         | None -> failwith "gen_context"
       end 
    | TApp4(f, a0, a1, a2, a3), TApp4(f', a0', a1', a2', a3') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs (dshift_ f)) (infer ctx funs f') with
         | Some Eq -> 
            TApp4(shift_up etyp f', loop a0 a0', loop a1 a1', loop a2 a2', loop a3 a3')
         | None -> failwith "gen_context"
       end 
    | TApp5(f, a0, a1, a2, a3, a4), TApp5(f', a0', a1', a2', a3', a4') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs (dshift_ f)) (infer ctx funs f') with
         | Some Eq -> 
            TApp5(shift_up etyp f', loop a0 a0', loop a1 a1', loop a2 a2', loop a3 a3', loop a4 a4')
         | None -> failwith "gen_context"
       end
    | Case(t, x, _, _), Case(t', x', nil', cons') ->
       begin
         match eq_test t t' with
         | Some Eq ->
            let s : type b g. (g, f -> d, b) index -> (a -> g, f -> d, b) index = fun i -> S i in
            let shift_cons = (rename (ext (ext {rho = s} (List(t))) t)).shift in
            Case(t', loop x x', shift_up etyp nil', shift_cons cons')
       end
    | _, t' -> shift_up etyp t'
  in loop old_e fn
let gen_term_f : type a c g g' d f. a typ -> (g, f -> d) ctx -> (f -> d) functions -> (a -> g, d, c) tTerm -> (g, f -> d, c) tTerm -> (g, f -> d, a) tTerm =
  fun etyp ctx funs old_e fn ->
  let rec find : type c. (a -> g, d, c) tTerm -> (g, f -> d, c) tTerm -> (g, f -> d, a) tTerm option =
    fun t t' -> 
    match t, t' with
    | TVar(Z), _ -> Some(t')
    | TVar(_), _ -> None
    | TApp1(f, a0), TApp1(f', a0') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs (dshift_ f)) (infer ctx funs f') with
         | Some Eq ->
            begin
              match find a0 a0' with
              | Some(t) -> Some(t)
              | None -> None
            end
         | None -> None
       end 
    | TApp2(f, a0, a1), TApp2(f', a0', a1') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs (dshift_ f)) (infer ctx funs f') with
         | Some Eq ->
            begin
              match find a0 a0', find a1 a1' with
              | Some(t), _ -> Some(t)
              | _, Some(t) -> Some(t)
              | _, _ -> None
            end
         | None -> failwith "gen_context"
       end
    | TApp3(f, a0, a1, a2), TApp3(f', a0', a1', a2') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs (dshift_ f)) (infer ctx funs f') with
         | Some Eq ->
            begin
              match find a0 a0', find a1 a1', find a2 a2' with
              | Some(t), _, _ -> Some(t)
              | _, Some(t), _ -> Some(t)
              | _, _, Some(t) -> Some(t)
              | _, _, _ -> None
            end
         | None -> failwith "gen_context"
       end 
    | TApp4(f, a0, a1, a2, a3), TApp4(f', a0', a1', a2', a3') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs (dshift_ f)) (infer ctx funs f') with
         | Some Eq ->
            begin
              match find a0 a0', find a1 a1', find a2 a2', find a3 a3' with
              | Some(t), _, _, _ -> Some(t)
              | _, Some(t), _, _ -> Some(t)
              | _, _, Some(t), _ -> Some(t)
              | _, _, _, Some(t) -> Some(t)
              | _, _, _, _ -> None
            end
         | None -> failwith "gen_context"
       end 
    | TApp5(f, a0, a1, a2, a3, a4), TApp5(f', a0', a1', a2', a3', a4') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs (dshift_ f)) (infer ctx funs f') with
         | Some Eq ->
            begin
              match find a0 a0', find a1 a1', find a2 a2', find a3 a3', find a4 a4' with
              | Some(t), _, _, _, _ -> Some(t)
              | _, Some(t), _, _, _ -> Some(t)
              | _, _, Some(t), _, _ -> Some(t)
              | _, _, _, Some(t), _ -> Some(t)
              | _, _, _, _, Some(t) -> Some(t)
              | _, _, _, _, _ -> None
            end
         | None -> failwith "gen_context"
       end
    | Case(t, x, _, _), Case(t', x', nil', cons') ->
       begin
         match eq_test t t' with
         | Some Eq -> find x x'
         | None -> failwith "gen_hole"
       end
    | Cons(h, tl), Cons(h', tl') ->
       begin
         match find h h', find tl tl' with
         | Some(t), _ -> Some(t)
         | _, Some(t) -> Some(t)
         | _, _ -> None
       end
    | Nil, Nil -> None
    | Ch(c), Ch(c') -> None
    | t, t' ->
       Format.printf "t = %a@. t' = %a@." p_term t p_term t';
       failwith "hole?"
  in let Some(t) = find old_e fn in t

let rec gen_context : type a c g g' d f. a typ -> (g, d) ctx -> d functions -> (a -> g, d, c) tTerm -> (g, d, c) tTerm -> (a -> g, d, c) tTerm =
  fun etyp ctx funs old_e fn ->
  let rec loop : type c. (a -> g, d, c) tTerm -> (g, d, c) tTerm -> (a -> g, d, c) tTerm =
    fun old_e fn -> 
    match old_e, fn with
    | TVar(Z), _ -> TVar(Z)
    | TApp1(f, a0), TApp1(f', a0') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs f) (infer ctx funs f') with
         | Some Eq -> 
            TApp1(shift_up etyp f', loop a0 a0')
         | None -> failwith "gen_context"
       end 
    | TApp2(f, a0, a1), TApp2(f', a0', a1') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs f) (infer ctx funs f') with
         | Some Eq -> 
            TApp2(shift_up etyp f', loop a0 a0', loop a1 a1')
         | None -> failwith "gen_context"
       end
    | TApp3(f, a0, a1, a2), TApp3(f', a0', a1', a2') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs f) (infer ctx funs f') with
         | Some Eq -> 
            TApp3(shift_up etyp f', loop a0 a0', loop a1 a1', loop a2 a2')
         | None -> failwith "gen_context"
       end 
    | TApp4(f, a0, a1, a2, a3), TApp4(f', a0', a1', a2', a3') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs f) (infer ctx funs f') with
         | Some Eq -> 
            TApp4(shift_up etyp f', loop a0 a0', loop a1 a1', loop a2 a2', loop a3 a3')
         | None -> failwith "gen_context"
       end 
    | TApp5(f, a0, a1, a2, a3, a4), TApp5(f', a0', a1', a2', a3', a4') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs f) (infer ctx funs f') with
         | Some Eq -> 
            TApp5(shift_up etyp f', loop a0 a0', loop a1 a1', loop a2 a2', loop a3 a3', loop a4 a4')
         | None -> failwith "gen_context"
       end
    | Case(t, x, _, _), Case(t', x', nil', cons') ->
       begin
         match eq_test t t' with
         | Some Eq ->
            let s : type b g. (g, d, b) index -> (a -> g, d, b) index = fun i -> S i in
            let shift_cons = (rename (ext (ext {rho = s} (List(t))) t)).shift in
            Case(t', loop x x', shift_up etyp nil', shift_cons cons')
       end
    | _, t' -> shift_up etyp t'
  in loop old_e fn
let gen_term : type a c g g' d f. a typ -> (g, d) ctx -> d functions -> (a -> g, d, c) tTerm -> (g, d, c) tTerm -> (g, d, a) tTerm =
  fun etyp ctx funs old_e fn ->
  let rec find : type c. (a -> g, d, c) tTerm -> (g, d, c) tTerm -> (g, d, a) tTerm option =
    fun t t' -> 
    match t, t' with
    | TVar(Z), _ -> Some(t')
    | TVar(_), _ -> None
    | TApp1(f, a0), TApp1(f', a0') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs f) (infer ctx funs f') with
         | Some Eq ->
            begin
              match find a0 a0' with
              | Some(t) -> Some(t)
              | None -> None
            end
         | None -> None
       end 
    | TApp2(f, a0, a1), TApp2(f', a0', a1') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs f) (infer ctx funs f') with
         | Some Eq ->
            begin
              match find a0 a0', find a1 a1' with
              | Some(t), _ -> Some(t)
              | _, Some(t) -> Some(t)
              | _, _ -> None
            end
         | None -> failwith "gen_context"
       end
    | TApp3(f, a0, a1, a2), TApp3(f', a0', a1', a2') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs f) (infer ctx funs f') with
         | Some Eq ->
            begin
              match find a0 a0', find a1 a1', find a2 a2' with
              | Some(t), _, _ -> Some(t)
              | _, Some(t), _ -> Some(t)
              | _, _, Some(t) -> Some(t)
              | _, _, _ -> None
            end
         | None -> failwith "gen_context"
       end 
    | TApp4(f, a0, a1, a2, a3), TApp4(f', a0', a1', a2', a3') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs f) (infer ctx funs f') with
         | Some Eq ->
            begin
              match find a0 a0', find a1 a1', find a2 a2', find a3 a3' with
              | Some(t), _, _, _ -> Some(t)
              | _, Some(t), _, _ -> Some(t)
              | _, _, Some(t), _ -> Some(t)
              | _, _, _, Some(t) -> Some(t)
              | _, _, _, _ -> None
            end
         | None -> failwith "gen_context"
       end 
    | TApp5(f, a0, a1, a2, a3, a4), TApp5(f', a0', a1', a2', a3', a4') ->
       begin
         match eq_test (infer (CtxS(etyp, ctx)) funs f) (infer ctx funs f') with
         | Some Eq ->
            begin
              match find a0 a0', find a1 a1', find a2 a2', find a3 a3', find a4 a4' with
              | Some(t), _, _, _, _ -> Some(t)
              | _, Some(t), _, _, _ -> Some(t)
              | _, _, Some(t), _, _ -> Some(t)
              | _, _, _, Some(t), _ -> Some(t)
              | _, _, _, _, Some(t) -> Some(t)
              | _, _, _, _, _ -> None
            end
         | None -> failwith "gen_context"
       end
    | Case(t, x, _, _), Case(t', x', nil', cons') ->
       begin
         match eq_test t t' with
         | Some Eq -> find x x'
         | None -> failwith "gen_hole"
       end
    | Cons(h, tl), Cons(h', tl') ->
       begin
         match find h h', find tl tl' with
         | Some(t), _ -> Some(t)
         | _, Some(t) -> Some(t)
         | _, _ -> None
       end
    | Nil, Nil -> None
    | Ch(c), Ch(c') -> None
    | t, t' ->
       Format.printf "t = %a@. t' = %a@." p_term t p_term t';
       failwith "hole?"
  in let Some(t) = find old_e fn in t
                                  
(* let rec search_z : type g d a b. (a -> g, d, b) tTerm -> bool =
 *   function
 *   | TApp1(f, a0) -> search_z f || search_z arg0
 *   | TApp2(f, a0, a1) -> search_z f || search_z a0 || search_z arg1
 *   | TApp3(f, a0, a1, a2) -> search_z f || search_z a0 || search_z arg1 || search_z arg2
 *   | TApp4(f, a0, a1, a2, a3) -> search_z f || search_z a0 || search_z arg1 || search_z arg2 || search_z arg3
 *   | TApp5(f, a0, a1, a2, a3, a4) -> search_z f || search_z a0 || search_z arg1 || search_z arg2 || search_z arg4
 *   | TIf(x, a, _, _) -> search_z x
 *   | Case(_, x, _, _) -> search_z x
 *   | TVar(Z) -> true
 *   | _ -> false *)
                          
                                  
(* 停止性が保存するか証明 *)
let sc : type a g d. bool -> bool -> (g, d) unifier -> d memo -> (g, d) ctx -> d functions -> (g, d, a) tTerm  -> (g, d, a) tTerm =
  fun elim propagating unifier memo ctx funs term ->
  (* let exte : type a b c g d.
   *                 b typ ->
   *                 ((g, d, a) tTerm -> (g, d, c) tTerm) ->
   *                 (b -> g, d, a) tTerm -> (b -> g, d, c) tTerm =
   *   fun t e -> (
   *     fun e' ->
   *     let fn = e (shift_down t e') in
   *     Format.printf "fn = %a@." p_term fn;
   *     e (shift_down t e') |> shift_up t)
   * in  *)
  let rec sc : type a b g d.
                    (g, d) unifier ->
                    d memo ->
                    (g, d) ctx ->
                    d functions ->
                    (g, d, a) tTerm -> 
                    (a -> g, d, b) tTerm ->
                    (g, d, b) tTerm =
    fun unifier memo ctx funs term e ->
    let atyp = infer ctx funs term in
    let continue : (g, d, a) tTerm -> (g, d, b) tTerm =
      fun term ->
      match e with
      | TVar(Z) -> term
      | _ -> 
         subst0 atyp e term |> fun t -> sc unifier memo ctx funs t z_
    in
    (* Format.printf "here' = %a@.e<Z> = %a@." p_term term p_term e; *)
    match subst0 atyp e term  with
    | TFVar(i) -> continue term 
    | TLam(typ, t) -> subst0 atyp e term 
    | TLamNon(typ, t) -> subst0 atyp e term 
    | TTrue -> continue term
    | TFalse -> continue term
    | Ch(c) -> continue term
    | Zero -> continue term
    | Succ(n) ->
       let n = sc unifier memo ctx funs n z_ in
       Succ(n)
    | Fix(t, f) -> subst0 atyp e term 
    | Fix2(l, r, f, g) -> subst0 atyp e term 
    | Nil -> continue term
    | Cons(h, tl) ->
       Cons(sc unifier memo ctx funs h z_,
            sc unifier memo ctx funs tl z_)
    | Left(typ, t) -> subst0 atyp e term 
       (* let t = sc unifier memo ctx funs t in
        * Left(typ, t) *)
    | Right(typ, t) -> subst0 atyp e term 
       (* let t = sc unifier memo ctx funs t in
        * Right(typ, t) *)
    | TApp(f, v) -> subst0 atyp e term 
    | Next(t, n) -> subst0 atyp e term 
    | _ ->
       begin
         match term with
         | TApp1(f, arg0) ->
            let arg0' = unify unifier arg0 in
            (* Format.printf "arg0 = %a@." p_term arg0'; *)
            if isobserval arg0' then
              let fn = subst0 atyp e (TApp1(f, arg0')) in
                match assuming_eq (flush unifier) memo funs fn with
                | Some(call) ->
                   (* let _ = Format.printf "hit! %a@." p_term call in *) call
                | None ->
                   (* let _ = Format.printf "miss! @." in  *)
                   let c_typ = infer ctx funs fn in
                   let used = fn |> vsearch (gen_used ctx) in                   
                   sc_app1 c_typ unifier memo ctx used funs f arg0' e
            else
              let typ0 = infer ctx funs arg0' in
              let e' = subst0 atyp e (TApp1(f, TVar(P(typ0, Z)))) |> shift_up typ0 in
              sc unifier memo ctx funs arg0' e'
         | TApp2(f, arg0, arg1) ->
            let arg0' = unify unifier arg0 in
            let arg1' = unify unifier arg1 in
            (* Format.printf "arg0 = %a@." p_term arg0';
             * Format.printf "arg1 = %a@." p_term arg1'; *)
            if isobserval arg0' then
              if isobserval arg1' then
                let fn = subst0 atyp e (TApp2(f, arg0', arg1')) in
                match assuming_eq (flush unifier) memo funs fn with
                | Some(call) ->
                   (* let _ = Format.printf "hit! %a@." p_term call in *) call
                | None ->
                   (* let _ = Format.printf "miss! @." in  *)
                   let c_typ = infer ctx funs fn in
                   let used = fn |> vsearch (gen_used ctx) in
                   sc_app2 c_typ unifier memo ctx used funs f arg0' arg1' e
              else
                let typ1 = infer ctx funs arg1' in
                let e' = subst0 atyp e (TApp2(f, arg0', TVar(P(typ1, Z)))) |> shift_up typ1 in
                sc unifier memo ctx funs arg1' e'
            else
              (* arg1'は値ではないかもしれないが、次のeの消化時に計算される *)
              let typ0 = infer ctx funs arg0' in
              let e' = subst0 atyp e (TApp2(f, TVar(P(typ0, Z)), arg1')) |> shift_up typ0 in
              sc unifier memo ctx funs arg0' e'
         | TApp3(f, arg0, arg1, arg2) ->
            let arg0' = unify unifier arg0 in
            let arg1' = unify unifier arg1 in
            let arg2' = unify unifier arg2 in
            (* Format.printf "arg0 = %a@." p_term arg0';
             * Format.printf "arg1 = %a@." p_term arg1';
             * Format.printf "arg2 = %a@." p_term arg2'; *)
            if isobserval arg0' then
              if isobserval arg1' then
                if isobserval arg2' then
                  let fn = subst0 atyp e (TApp3(f, arg0', arg1', arg2')) in
                  match assuming_eq (flush unifier) memo funs fn with
                  | Some(call) ->
                     (* let _ = Format.printf "hit! %a@." p_term call in *) call
                  | None ->
                     (* let _ = Format.printf "miss! @." in  *)
                     let c_typ = infer ctx funs fn in
                     let used = fn |> vsearch (gen_used ctx) in
                     sc_app3 c_typ unifier memo ctx used funs f arg0' arg1' arg2' e
                else
                  let typ2 = infer ctx funs arg2' in
                  let e' = subst0 atyp e (TApp3(f, arg0', arg1', TVar(P(typ2, Z)))) |> shift_up typ2 in
                  sc unifier memo ctx funs arg2' e'
              else
                let typ1 = infer ctx funs arg1' in
                let e' = subst0 atyp e (TApp3(f, arg0', TVar(P(typ1, Z)), arg2')) |> shift_up typ1 in
                sc unifier memo ctx funs arg1' e'
            else
              (* arg1'は値ではないかもしれないが、次のeの消化時に計算される *)
              let typ0 = infer ctx funs arg0' in
              let e' = subst0 atyp e (TApp3(f, TVar(P(typ0, Z)), arg1', arg2')) |> shift_up typ0 in
              sc unifier memo ctx funs arg0' e'
         | TApp4(f, arg0, arg1, arg2, arg3) ->
            let arg0' = unify unifier arg0 in
            let arg1' = unify unifier arg1 in
            let arg2' = unify unifier arg2 in
            let arg3' = unify unifier arg3 in
            (* Format.printf "arg0 = %a@." p_term arg0';
             * Format.printf "arg1 = %a@." p_term arg1';
             * Format.printf "arg2 = %a@." p_term arg2';
             * Format.printf "arg3 = %a@." p_term arg3'; *)
            if isobserval arg0' then
              if isobserval arg1' then
                if isobserval arg2' then
                  if isobserval arg3' then
                    let fn = subst0 atyp e (TApp4(f, arg0', arg1', arg2', arg3')) in
                    match assuming_eq (flush unifier) memo funs fn with
                    | Some(call) ->
                       (* let _ = Format.printf "hit! %a@." p_term call in *) call
                    | None ->
                       (* let _ = Format.printf "miss! @." in  *)
                       let c_typ = infer ctx funs fn in
                       let used = fn |> vsearch (gen_used ctx) in
                       sc_app4 c_typ unifier memo ctx used funs f arg0' arg1' arg2' arg3' e
                  else
                    let typ3 = infer ctx funs arg3' in
                    let e' = subst0 atyp e (TApp4(f, arg0', arg1', arg2', TVar(P(typ3, Z)))) |> shift_up typ3 in
                    sc unifier memo ctx funs arg3' e'
                else
                  let typ2 = infer ctx funs arg2' in
                  let e' = subst0 atyp e (TApp4(f, arg0', arg1', TVar(P(typ2, Z)), arg3')) |> shift_up typ2 in
                  sc unifier memo ctx funs arg2' e'
              else
                let typ1 = infer ctx funs arg1' in
                let e' = subst0 atyp e (TApp4(f, arg0', TVar(P(typ1, Z)), arg2', arg3')) |> shift_up typ1 in
                sc unifier memo ctx funs arg1' e'
            else
              let typ0 = infer ctx funs arg0' in
              let e' = subst0 atyp e (TApp4(f, TVar(P(typ0, Z)), arg1', arg2', arg3')) |> shift_up typ0 in
              sc unifier memo ctx funs arg0' e'              
         | TApp5(f, arg0, arg1, arg2, arg3, arg4) ->
            let arg0' = unify unifier arg0 in
            let arg1' = unify unifier arg1 in
            let arg2' = unify unifier arg2 in
            let arg3' = unify unifier arg3 in
            let arg4' = unify unifier arg4 in
            (* Format.printf "arg0 = %a@." p_term arg0';
             * Format.printf "arg1 = %a@." p_term arg1';
             * Format.printf "arg2 = %a@." p_term arg2';
             * Format.printf "arg3 = %a@." p_term arg3';
             * Format.printf "arg4 = %a@." p_term arg4'; *)
            if isobserval arg0' then
              if isobserval arg1' then
                if isobserval arg2' then
                  if isobserval arg3' then
                    if isobserval arg4' then
                      let fn = subst0 atyp e (TApp5(f, arg0', arg1', arg2', arg3', arg4')) in
                      match assuming_eq (flush unifier) memo funs fn with
                      | Some(call) ->
                         (* let _ = Format.printf "hit! %a@." p_term call in *) call
                      | None ->
                         (* let _ = Format.printf "miss! @." in  *)
                         let c_typ = infer ctx funs fn in
                         let used = fn |> vsearch (gen_used ctx) in
                         (* Format.printf "fn = %a@." p_term fn;
                          * Format.printf "used = %a@." (p_used 0) (vsearch used fn); *)
                         sc_app5 c_typ unifier memo ctx used funs f arg0' arg1' arg2' arg3' arg4' e
                    else
                      let typ4 = infer ctx funs arg4' in
                      let e' = subst0 atyp e (TApp5(f, arg0', arg1', arg2', arg3', TVar(P(typ4, Z)))) |> shift_up typ4 in
                      sc unifier memo ctx funs arg4' e'
                  else
                    let typ3 = infer ctx funs arg3' in
                    let e' = subst0 atyp e (TApp5(f, arg0', arg1', arg2', TVar(P(typ3, Z)), arg4')) |> shift_up typ3 in
                    sc unifier memo ctx funs arg3' e'
                else
                  let typ2 = infer ctx funs arg2' in
                  let e' = subst0 atyp e (TApp5(f, arg0', arg1', TVar(P(typ2, Z)), arg3', arg4')) |> shift_up typ2 in
                  sc unifier memo ctx funs arg2' e'
              else
                let typ1 = infer ctx funs arg1' in
                let e' = subst0 atyp e (TApp5(f, arg0', TVar(P(typ1, Z)), arg2', arg3', arg4')) |> shift_up typ1 in
                sc unifier memo ctx funs arg1' e'
            else
              let typ0 = infer ctx funs arg0' in
              let e' = subst0 atyp e (TApp5(f, TVar(P(typ0, Z)), arg1', arg2', arg3', arg4')) |> shift_up typ0 in
              sc unifier memo ctx funs arg0' e'
         | TOr(t1, t2) ->
            let hole1 = TVar(P(Bool, P(Bool, Z))) in
            let hole2 = TVar(P(Bool, Z)) in
            let e1 = subst0 atyp e (TOr(hole1, hole2)) |> shift_up Bool |> shift_up Bool in
            let e2 = sc (UCons(Bool, z_, unifier)) memo (CtxS(Bool, ctx)) funs (shift_up Bool t1) e1 in
            sc unifier memo ctx funs t2 e2
            (* 
             * let e1 hole1 =
             *   let e2 hole2 = 
             *     e (TOr(hole1, hole2)) in
             *   sc unifier memo ctx funs t2 e2 in
             * sc unifier memo ctx funs t1 e1 *)
         | Case(typ, x, nil, cons) ->
            (* case e of ...の処理は実装していない *)
            begin
              let x' = unify unifier x in
              match x' with
              | Nil -> sc unifier memo ctx funs nil e
              | Cons(h, tl) ->
                 let lifted_h = shift_up (List(typ)) h in
                 sc unifier memo ctx funs  (subst0 (List(typ)) (subst0 typ cons lifted_h) tl) e
              | TVar(i) ->
                 let tl = P(List(typ), Z) in
                 let h = P(List(typ), P(typ, Z)) in
                 let cons_unifier =
                   if propagating then
                     UCons(typ, TVar(Z), UCons(List(typ), TVar(Z), case_ext unifier i h tl))
                   else
                     UCons(typ, TVar(Z), UCons(List(typ), TVar(Z), unifier))
                 in
                 let nil_unifier =
                   (* Format.printf "%b@." propagating; *)
                   if propagating then
                     case_ext_nil unifier typ i
                   else
                     unifier
                 in
                 let nil = sc nil_unifier memo ctx funs nil e in
                 let ctx = CtxS(typ, CtxS((List(typ)), ctx)) in
                 let e' = shift_up (List(typ)) e |> shift_up typ in
                 let mapto_1 = subst_1 atyp (TVar(P(List(typ), P(typ, P(atyp, Z))))) in
                 let mapto2 = exts (exts mapto_1 (List(typ))) (typ) in
                 let e = (subst mapto2).shift e' |> shift_up atyp in
                 let cons = sc cons_unifier memo ctx funs cons e in
                 Case(typ, x, nil, cons)
              | x -> continue term
            end
         | TIf(x1, x2, thn, els) ->
            let x2' = unify unifier x2 in
            let x1' = unify unifier x1 in
            begin                      (* little effort *)
              match x1', x2' with
              | TVar(i), TTrue ->
                 let true_unifier = if propagating then (if_ext unifier true i) else unifier in
                 let thn = sc true_unifier memo ctx funs thn e in
                 let els = sc unifier memo ctx funs els e in
                 TIf(x1, x2, thn, els)
              | TVar(i), Ch(c) ->
                 let c_unifier = if propagating then (if_ext_c unifier c i) else unifier in
                 let thn = sc c_unifier memo ctx funs thn e in
                 let els = sc unifier memo ctx funs els e in
                 TIf(x1, x2, thn, els)
              | TVar(i), TFalse ->
                 let false_unifier = if propagating then (if_ext unifier false i) else unifier in
                 let thn = sc false_unifier memo ctx funs thn e in
                 let els = sc unifier memo ctx funs els e in
                 TIf(x1, x2, thn, els)
              | t, t' ->
                 if t = t' then sc unifier memo ctx funs thn e
                 else sc unifier memo ctx funs els e
            end
         | t -> if isobserval t then
                  continue term
                else subst0 atyp e term
       end         
         
  and sc_app1 : type a0 b c g d.
                     c typ -> 
                     (g, d) unifier ->
                     d memo ->
                     (g, d) ctx ->
                     g used -> 
                     d functions ->
                     (g, d, a0 -> b) tTerm ->
                     (g, d, a0) tTerm -> 
                     (b -> g, d, c) tTerm -> 
                     (g, d, c) tTerm =     
    fun c_typ unifier memo ctx used funs fn arg0 e ->
    match unify unifier fn with
    | TLam(t, body) ->
       sc unifier memo ctx funs (subst0 t body arg0) e
    | Fix(Arrow(a0, b), TLam(this_typ, TLam(_, body))) ->
       let arg0' = shift_up this_typ arg0 in
       let term : (g, d, b) tTerm =  arg0' |> subst0 a0 body |> fun t -> subst0 this_typ t fn in
       let fn = TApp1(fn, arg0) in
       let body = subst0 b e term in
       let call = Call(subst0 b e fn) in
       call_next unifier ctx funs memo used body call c_typ c_typ b ctx e
    | _ -> failwith "partial application"
  and sc_app2 : type a0 a1 b c g d.                     
                     c typ -> 
                     (g, d) unifier ->
                     d memo ->
                     (g, d) ctx ->
                     g used -> 
                     d functions -> 
                     (g, d, a0 -> a1 -> b) tTerm ->
                     (g, d, a0) tTerm ->
                     (g, d, a1) tTerm ->
                     (b -> g, d, c) tTerm -> 
                     (g, d, c) tTerm  =
    fun c_typ unifier memo ctx used funs fn arg0 arg1 e ->
    match unify unifier fn with
    | TLam(t0, TLam(t1, body)) ->
       let arg1' = shift_up t0 arg1 in
       let arg0' = arg0 in
       let body = subst0 t0 (subst0 t1 body arg1') arg0'
       in sc unifier memo ctx funs body e       
    | Fix(Arrow(t0, Arrow(t1, b)), TLam(this_typ, TLam(_, TLam(_, body)))) ->
       let arg1' = shift_up this_typ arg1 |> shift_up t0 in
       let arg0' = shift_up this_typ arg0 in
       let term0 : (a0 -> ((a0 -> a1 -> b) -> g), d, b) tTerm = subst0 t1 body arg1' in
       let term : (g, d, b) tTerm = subst0 t0 term0 arg0' |> fun t -> subst0 this_typ t fn in
       let fn = TApp2(fn, arg0, arg1) in
       let body = subst0 b e term in
       let call = Call(subst0 b e fn) in
       call_next unifier ctx funs memo used body call c_typ c_typ b ctx e
    | Left(r, Fix2(Arrow(t0, Arrow(t1, b)), _, TLam(this_typ, TLam(_, TLam(_, body))), right)) ->
       let arg1' = shift_up this_typ arg1 |> shift_up t0 in
       let arg0' = shift_up this_typ arg0 in
       let f = Fix2(Arrow(t0, Arrow(t1, b)), r, TLam(this_typ, TLam(t0, TLam(t1, body))), right) in
       let term0 = subst0 t1 body arg1' in
       let term = subst0 t0 term0 arg0' |> fun t -> subst0 this_typ t f in
       let fn = TApp2(fn, arg0, arg1) in
       let body = subst0 b e term in
       let call = Call(subst0 b e fn) in
       call_next unifier ctx funs memo used body call c_typ c_typ b ctx e
    | Right(l, Fix2(_, Arrow(t0, Arrow(t1, b)), left, TLam(this_typ, TLam(_, TLam(_, body))))) ->
       let arg1' = shift_up this_typ arg1 |> shift_up t0 in
       let arg0' = shift_up this_typ arg0 in
       let f = Fix2(l, Arrow(t0, Arrow(t1, b)), left, TLam(this_typ, TLam(t0, TLam(t1, body)))) in
       let term0 = subst0 t1 body arg1' in
       let term = subst0 t0 term0 arg0' |> fun t -> subst0 this_typ t f in
       let fn = TApp2(fn, arg0, arg1) in
       let body = subst0 b e term in
       let call = Call(subst0 b e fn) in
       call_next unifier ctx funs memo used body call c_typ c_typ b ctx e
    | _ -> failwith "partial application"
  and sc_app3 : type a0 a1 a2 b c g d.
                     c typ -> 
                     (g, d) unifier ->
                     d memo ->
                     (g, d) ctx ->
                     g used -> 
                     d functions -> 
                     (g, d, a0 -> a1 -> a2 -> b) tTerm ->
                     (g, d, a0) tTerm ->
                     (g, d, a1) tTerm ->
                     (g, d, a2) tTerm ->
                     (b -> g, d, c) tTerm -> 
                     (g, d, c) tTerm  =
    fun c_typ unifier memo ctx used funs fn arg0 arg1 arg2 e ->
    match fn with
    | TLam(t0, TLam(t1, TLam(t2, body))) ->
       let arg2' = shift_up t0 arg2 |> shift_up t1 in
       let arg1' = shift_up t0 arg1 in
       let arg0' = arg0 in
       let body = subst0 t0 (subst0 t1 (subst0 t2 body arg2') arg1') arg0' in
       sc unifier memo ctx funs body e
    | Fix(Arrow(t0, Arrow(t1, Arrow(t2, b))), TLam(this_typ, TLam(_, TLam(_, TLam(_, body))))) ->
       let arg2' = shift_up this_typ arg2 |> shift_up t0 |> shift_up t1 in
       let arg1' = shift_up this_typ arg1 |> shift_up t0 in
       let arg0' = shift_up this_typ arg0 in
       let term1 = subst0 t2 body arg2' in
       let term0 = subst0 t1 term1 arg1' in
       let term : (g, d, b) tTerm = subst0 t0 term0 arg0' |> fun t -> subst0 this_typ t fn in
       let fn = TApp3(fn, arg0, arg1, arg2) in
       let body = subst0 b e term in
       let call = Call(subst0 b e fn) in
       call_next unifier ctx funs memo used body call c_typ c_typ b ctx e
    | Left(r, Fix2(Arrow(t0, Arrow(t1, Arrow(t2, b))), _, TLam(this_typ, TLam(_, TLam(_, TLam(_, body)))), right)) ->
       let arg2' = shift_up this_typ arg2 |> shift_up t0 |> shift_up t1 in
       let arg1' = shift_up this_typ arg1 |> shift_up t0 in
       let arg0' = shift_up this_typ arg0 in
       let f = Fix2(Arrow(t0, Arrow(t1, Arrow(t2, b))), r, TLam(this_typ, TLam(t0, TLam(t1, TLam(t2, body)))), right) in
       let term1 = subst0 t2 body arg2' in
       let term0 = subst0 t1 term1 arg1' in
       let term = subst0 t0 term0 arg0' |> fun t -> subst0 this_typ t f in
       let fn = TApp3(fn, arg0, arg1, arg2) in
       let body = subst0 b e term in
       let call = Call(subst0 b e fn) in
       call_next unifier ctx funs memo used body call c_typ c_typ b ctx e
    | Right(l, Fix2(_, Arrow(t0, Arrow(t1, Arrow(t2, b))), left, TLam(this_typ, TLam(_, TLam(_, TLam(_, body)))))) ->
       let arg2' = shift_up this_typ arg2 |> shift_up t0 |> shift_up t1 in
       let arg1' = shift_up this_typ arg1 |> shift_up t0 in
       let arg0' = shift_up this_typ arg0 in
       let f = Fix2(l, Arrow(t0, Arrow(t1, Arrow(t2, b))), left, TLam(this_typ, TLam(t0, TLam(t1, TLam(t2, body))))) in
       let term1 = subst0 t2 body arg2' in
       let term0 = subst0 t1 term1 arg1' in
       let term = subst0 t0 term0 arg0' |> fun t -> subst0 this_typ t f in
       let fn = TApp3(fn, arg0, arg1, arg2) in
       let body = subst0 b e term in
       let call = Call(subst0 b e fn) in
       call_next unifier ctx funs memo used body call c_typ c_typ b ctx e
    | _ -> failwith "partial application"
  and sc_app4 : type a0 a1 a2 a3 b c g d.
                     c typ -> 
                     (g, d) unifier ->
                     d memo ->
                     (g, d) ctx ->
                     g used -> 
                     d functions ->                     
                     (g, d, a0 -> a1 -> a2 -> a3 -> b) tTerm ->
                     (g, d, a0) tTerm ->
                     (g, d, a1) tTerm ->
                     (g, d, a2) tTerm ->
                     (g, d, a3) tTerm ->
                     (b -> g, d, c) tTerm -> 
                     (g, d, c) tTerm  =
    fun c_typ unifier memo ctx used funs fn arg0 arg1 arg2 arg3 e ->
    match fn with
    | TLam(t0, TLam(t1, TLam(t2, TLam(t3, body)))) ->
       let arg3' = shift_up t0 arg3 |> shift_up t1 |> shift_up t2 in
       let arg2' = shift_up t0 arg2 |> shift_up t1 in
       let arg1' = shift_up t0 arg1 in
       let arg0' = arg0 in
       let body = subst0 t0 (subst0 t1 (subst0 t2 (subst0 t3 body arg3') arg2') arg1') arg0' in
       sc unifier memo ctx funs body e       
    | Fix(Arrow(t0, Arrow(t1, Arrow(t2, Arrow(t3, b)))), TLam(this_typ, TLam(_, TLam(_, TLam(_, TLam(_, body)))))) ->
       let arg3' = shift_up this_typ arg3 |> shift_up t0 |> shift_up t1 |> shift_up t2 in
       let arg2' = shift_up this_typ arg2 |> shift_up t0 |> shift_up t1 in
       let arg1' = shift_up this_typ arg1 |> shift_up t0 in
       let arg0' = shift_up this_typ arg0 in
       let term2 = subst0 t3 body arg3' in
       let term1 = subst0 t2 term2 arg2' in
       let term0 = subst0 t1 term1 arg1' in
       let term : (g, d, b) tTerm = subst0 t0 term0 arg0' |> fun t -> subst0 this_typ t fn in
       let fn = TApp4(fn, arg0, arg1, arg2, arg3) in
       let body = subst0 b e term in
       let call = Call(subst0 b e fn) in
       call_next unifier ctx funs memo used body call c_typ c_typ b ctx e
    | Left(r, Fix2(Arrow(t0, Arrow(t1, Arrow(t2, Arrow(t3, b)))), _, TLam(this_typ, TLam(_, TLam(_, TLam(_, TLam(_, body))))), right)) ->
       let arg3' = shift_up this_typ arg3 |> shift_up t0 |> shift_up t1 |> shift_up t2 in
       let arg2' = shift_up this_typ arg2 |> shift_up t0 |> shift_up t1 in
       let arg1' = shift_up this_typ arg1 |> shift_up t0 in
       let arg0' = shift_up this_typ arg0 in
       let f = Fix2(Arrow(t0, Arrow(t1, Arrow(t2, Arrow(t3, b)))), r, TLam(this_typ, TLam(t0, TLam(t1, TLam(t2, TLam(t3, body))))), right) in
       let term2 = subst0 t3 body arg3' in
       let term1 = subst0 t2 term2 arg2' in
       let term0 = subst0 t1 term1 arg1' in
       let term = subst0 t0 term0 arg0' |> fun t -> subst0 this_typ t f in
       let fn = TApp4(fn, arg0, arg1, arg2, arg3) in
       let body = subst0 b e term in
       let call = Call(subst0 b e fn) in
       call_next unifier ctx funs memo used body call c_typ c_typ b ctx e
    | Right(l, Fix2(_, Arrow(t0, Arrow(t1, Arrow(t2, Arrow(t3, b)))), left, TLam(this_typ, TLam(_, TLam(_, TLam(_, TLam(_, body))))))) ->
       let arg3' = shift_up this_typ arg3 |> shift_up t0 |> shift_up t1 |> shift_up t2 in
       let arg2' = shift_up this_typ arg2 |> shift_up t0 |> shift_up t1 in
       let arg1' = shift_up this_typ arg1 |> shift_up t0 in
       let arg0' = shift_up this_typ arg0 in
       let f = Fix2(l, Arrow(t0, Arrow(t1, Arrow(t2, Arrow(t3, b)))), left, TLam(this_typ, TLam(t0, TLam(t1, TLam(t2, TLam(t3, body)))))) in
       let term2 = subst0 t3 body arg3' in
       let term1 = subst0 t2 term2 arg2' in
       let term0 = subst0 t1 term1 arg1' in
       let term = subst0 t0 term0 arg0' |> fun t -> subst0 this_typ t f in
       let fn = TApp4(fn, arg0, arg1, arg2, arg3) in
       let body = subst0 b e term in
       let call = Call(subst0 b e fn) in
       call_next unifier ctx funs memo used body call c_typ c_typ b ctx e
    | _ -> failwith "partial application"
  and sc_app5 : type a0 a1 a2 a3 a4 b c g d.
                     c typ -> 
                     (g, d) unifier ->
                     d memo ->
                     (g, d) ctx ->
                     g used -> 
                     d functions -> 
                     (g, d, a0 -> a1 -> a2 -> a3 -> a4 -> b) tTerm ->
                     (g, d, a0) tTerm ->
                     (g, d, a1) tTerm ->
                     (g, d, a2) tTerm ->
                     (g, d, a3) tTerm ->
                     (g, d, a4) tTerm ->
                     (b -> g, d, c) tTerm -> 
                     (g, d, c) tTerm = 
    fun c_typ unifier memo ctx used funs fn arg0 arg1 arg2 arg3 arg4 e ->
    match fn with
    | TLam(t0, TLam(t1, TLam(t2, TLam(t3, TLam(t4, body))))) ->
       let arg4' = shift_up t0 arg4 |> shift_up t1 |> shift_up t2 |> shift_up t3 in
       let arg3' = shift_up t0 arg3 |> shift_up t1 |> shift_up t2 in
       let arg2' = shift_up t0 arg2 |> shift_up t1 in
       let arg1' = shift_up t0 arg1 in
       let arg0' = arg0 in
       let body = subst0 t0 (subst0 t1 (subst0 t2 (subst0 t3 (subst0 t4 body arg4') arg3') arg2') arg1') arg0' in       
       sc unifier memo ctx funs body e
    | Fix(Arrow(t0, Arrow(t1, Arrow(t2, Arrow(t3, Arrow(t4, b))))), TLam(this_typ, TLam(_, TLam(_, TLam(_, TLam(_, TLam(_, body))))))) ->
       let arg4' = shift_up this_typ arg4 |> shift_up t0 |> shift_up t1 |> shift_up t2 |> shift_up t3 in
       let arg3' = shift_up this_typ arg3 |> shift_up t0 |> shift_up t1 |> shift_up t2 in
       let arg2' = shift_up this_typ arg2 |> shift_up t0 |> shift_up t1 in
       let arg1' = shift_up this_typ arg1 |> shift_up t0 in
       let arg0' = shift_up this_typ arg0 in
       let term3 = subst0 t4 body arg4' in
       let term2 = subst0 t3 term3 arg3' in
       let term1 = subst0 t2 term2 arg2' in
       let term0 = subst0 t1 term1 arg1' in
       let term : (g, d, b) tTerm = subst0 t0 term0 arg0' |> fun t -> subst0 this_typ t fn in
       let fn = TApp5(fn, arg0, arg1, arg2, arg3, arg4) in
       let body = subst0 b e term in
       let call = Call(subst0 b e fn) in
       call_next unifier ctx funs memo used body call c_typ c_typ b ctx e
    | Left(r, Fix2(Arrow(t0, Arrow(t1, Arrow(t2, Arrow(t3, Arrow(t4, b))))), _, TLam(this_typ, TLam(_, TLam(_, TLam(_, TLam(_, TLam(_, body)))))), right)) ->
       let arg4' = shift_up this_typ arg4 |> shift_up t0 |> shift_up t1 |> shift_up t2 |> shift_up t3 in
       let arg3' = shift_up this_typ arg3 |> shift_up t0 |> shift_up t1 |> shift_up t2 in
       let arg2' = shift_up this_typ arg2 |> shift_up t0 |> shift_up t1 in
       let arg1' = shift_up this_typ arg1 |> shift_up t0 in
       let arg0' = shift_up this_typ arg0 in
       let f = Fix2(Arrow(t0, Arrow(t1, Arrow(t2, Arrow(t3, Arrow(t4, b))))), r, TLam(this_typ, TLam(t0, TLam(t1, TLam(t2, TLam(t3, TLam(t4, body)))))), right) in
       let term3 = subst0 t4 body arg4' in
       let term2 = subst0 t3 term3 arg3' in
       let term1 = subst0 t2 term2 arg2' in
       let term0 = subst0 t1 term1 arg1' in
       let term = subst0 t0 term0 arg0' |> fun t -> subst0 this_typ t f in
       let fn = TApp5(fn, arg0, arg1, arg2, arg3, arg4) in
       let body = subst0 b e term in
       let call = Call(subst0 b e fn) in
       call_next unifier ctx funs memo used body call c_typ c_typ b ctx e
    | Right(l, Fix2(_, Arrow(t0, Arrow(t1, Arrow(t2, Arrow(t3, Arrow(t4, b))))), left, TLam(this_typ, TLam(_, TLam(_, TLam(_, TLam(_, TLam(_, body)))))))) ->
       let arg4' = shift_up this_typ arg4 |> shift_up t0 |> shift_up t1 |> shift_up t2 |> shift_up t3 in
       let arg3' = shift_up this_typ arg3 |> shift_up t0 |> shift_up t1 |> shift_up t2 in
       let arg2' = shift_up this_typ arg2 |> shift_up t0 |> shift_up t1 in
       let arg1' = shift_up this_typ arg1 |> shift_up t0 in
       let arg0' = shift_up this_typ arg0 in
       let f = Fix2(l, Arrow(t0, Arrow(t1, Arrow(t2, Arrow(t3, Arrow(t4, b))))), left, TLam(this_typ, TLam(t0, TLam(t1, TLam(t2, TLam(t3, TLam(t4, body))))))) in
       let term3 = subst0 t4 body arg4' in
       let term2 = subst0 t3 term3 arg3' in
       let term1 = subst0 t2 term2 arg2' in
       let term0 = subst0 t1 term1 arg1' in
       let term = subst0 t0 term0 arg0' |> fun t -> subst0 this_typ t f in
       let fn = TApp5(fn, arg0, arg1, arg2, arg3, arg4) in
       let body = subst0 b e term in
       let call = Call(subst0 b e fn) in
       call_next unifier ctx funs memo used body call c_typ c_typ b ctx e
    | _ -> failwith "partial application"
  and recall : type g d g' a b fn b c.
                    b typ -> 
                    fn typ ->
                    c typ -> 
                    (g, a -> d) unifier -> 
                    (a -> d) memo -> 
                    (g, a -> d) ctx -> 
                    (a -> d) functions -> 
                    (g, a -> d, fn) tTerm ->
                    (g', a -> d) ctx ->
                    (b -> g', d, c) tTerm -> 
                    (g, a -> d, fn) tTerm =
    fun htyp ftyp rtyp unifier memo c funs fnc ctx e ->
    match fnc, ftyp with 
    | TLam(t, fnc), Arrow(t', ftyp) ->
       TLam(t, recall htyp ftyp rtyp (UCons(t, TVar(Z), unifier)) memo (CtxS(t, c)) funs fnc ctx e)
    | TLamNon(t, fnc), Arrow(t', ftyp) ->
       TLamNon(t, recall htyp ftyp rtyp (UCons(t, TVar(Z), unifier)) memo (CtxS(t, c)) funs fnc ctx e)
    | body, _ ->
       begin 
         match eq_test ftyp rtyp, ctx_test c ctx with
         | Some Eq, Some CtxEq ->
            gen_context_f htyp ctx funs e body |> sc unifier memo c funs (gen_term_f htyp ctx funs e body)
         | _ -> failwith "ctx miss match"
       end      
  and call_next : type g g' d f return b.
                       (g, d) context
                       -> (g, d) ctx
                       -> d functions
                       -> d memo                  
                       -> g used 
                       -> (g, d, f) tTerm
                       -> (g, d, return) call
                       -> f typ
                       -> return typ
                       -> b typ
                       -> (g', d) ctx
                       -> (b -> g', d, return) tTerm (* evaluation context *)
                       -> (g, d, f) tTerm =
    fun unifier ctx funs memo used f fm ->
    match unifier, ctx, used with
    | UCons(t, v, unifier), CtxS(t', ctx), Used(t''', used) ->
       fun typ rtyp htyp ctx' e  ->
       begin 
         match eq_test t t', eq_test t t''' with
         | Some Eq, Some Eq ->
            let typ = Arrow(t, typ) in
            let f = TLam(t, f) in
            let fm = PC(t, fm) in
            let term = call_next unifier ctx funs memo used f fm typ rtyp htyp ctx' e |> shift_up t 
            in TApp(term, TVar(Z))
         | _ -> failwith ""
       end
    | UCons(t, v, unifier), CtxS(t', ctx), NUsed(t''', used) ->
       fun typ rtyp htyp ctx' e ->
       begin 
         match eq_test t t', eq_test t t''' with
         | Some Eq, Some Eq ->
            (* let typ = typ in
             * let f = shift_down t f in (\* エラーは起こらないはず *\)
             * let fm = downshift_call fm in (\* 同上 *\)
             * let term = call_next unifier ctx funs memo used f fm typ rtyp
             * in shift_up t term *)
            let typ = Arrow(t, typ) in
            let f = TLamNon(t, f) in
            let fm = PC(t, fm) in
            let term = call_next unifier ctx funs memo used f fm typ rtyp htyp ctx' e |> shift_up t 
            in TApp(term, TVar(Z))
         | _ -> failwith ""
       end
    (* begin 
     *   match eq_test t t', eq_test t t'', eq_test t t''' with
     *   | Some Eq, Some Eq, Some Eq ->
     *      let typ = Arrow(t, typ) in
     *      let f = if elim then TLamNon(t, f) else TLam(t, f) in
     *      let term = call_next unifier ctx funs memo used f typ rtyp |> shift_up t 
     *      in TApp(term, TVar(Z))
     *   | _ -> failwith ""
     * end *) 
    | UCons _, _, _ -> .
    | UNil, CtxZ, used ->
       fun typ rtyp htyp ctx' e ->
       (* Format.printf "@."; *)
       let f = dshift typ f in
       let funs' : (f -> d) functions = Fun(typ, f, funs) in
       let memo : (f -> d) memo = MCons(fm, memo) in
       let ctx' =
         let rec dd : type g d. (g, d) ctx -> (g, f -> d) ctx =
           function
           | CtxZ -> CtxZ
           | CtxS(t, ctx) -> CtxS(t, dd ctx)
         in dd ctx'
       in 
       let newf : (g, f -> d, f) tTerm = recall htyp typ rtyp UNil memo CtxZ funs' f ctx' e
       in Next(typ, newf)
    | UNil, _, _ -> .
  in sc unifier memo ctx funs term z_
  
(* let u1 = UCons(Bool, TVar(Z), UNil)
 * let fun1 = Fix(Arrow(Bool, Bool),
 *              TLam(Arrow(Bool, Bool),
 *                   TLam(Bool, TApp1(TVar(S Z), TVar(S (S Z))))
 *                )
 *              ) *)
(* let _ =
 *   let t1 = sc u1 EOM (TApp1(fun1, TTrue)) in
 *   Format.printf "%a@." p_term t1 *) 
  (*
 * let case1  =
 *   Case ((Bool), (TVar (S Z)),
 *      (TVar (S Z)),
 *      (TIf ((TVar Z), (TTrue),
 *              (TVar (S (S (S Z)))),
 *              (TVar (S Z)))
 *     ))
 * let case2  =
 *   Case ((Bool), (TVar Z),
 *      Nil,
 *      (TIf ((TVar Z), (TTrue),
 *              (Cons(TTrue, TVar(S Z))),
 *              (TVar (S Z)))
 *     ))
 * let u1 = UCons(Bool, TVar(Z), UCons(List(Bool), TVar(Z), UNil))
 * let dcase1 () = sc u1 [] case1
 * (\* (\\* in cons clause *\\)
 *)
let (x, xs, ys, rc) = TVar(Z), TVar(S Z), TVar(S (S Z)), TVar(S (S (S (S Z))))

                    
let append1 = Fix (Arrow((List Bool), (Arrow(List Bool, List Bool))),
                  (TLam(Arrow(List(Bool), Arrow(List(Bool), List(Bool))),
                        (TLam(List Bool, 
                              (TLam(List Bool,
                                    Case(Bool, TVar(S Z), (* xs *)
                                         TVar(Z), (* ys *)                            
                                         Cons(x, TApp2(rc, xs, ys))
                                      )
                                 )
                           ))
                        )
                     )
                  )
               )
let append2 = TApp2(append1, Cons(TFalse, TVar(Z)), TVar(S Z))            
(* let _ = Format.printf "append2 = \n%a@." p_term append2 *)
(* let f_non = Fix((List Char => (List Char => List Char)),
 *                 TLam((List Char => (List Char => List Char)),
 *                      TLam(List Char, (\* ys *\)
 *                           TLam(List Char, (\* zs *\)
 *                                Case(Char, TVar(S Z),
 *                                     TVar(Z),
 *                                     TApp2(TVar(S (S (S (S Z)))), TVar(S Z), TVar(S (S (S Z))))
 *                                  )
 *                             )
 *                        )
 *                   )
 *               ) *)
(* let f_non_app = TApp2(f_non, TVar(Z), TVar(Z)) *)
let _ =
  (* let env_append = CtxS(List(Bool), CtxS(List(Bool), CtxZ)) in
   * let unf_append = ctx_to_unifier env_append in
   * let memo_append = ctx_to_memo env_append in *)
  (* let append3 = sc true true unf_append memo_append env_append FNil append2 in () *)
  (* Format.printf "append3 = \n%a@." p_term append3 *)
  ()
let rec loop pp ss op os =
  match pp with
  | [] -> true
  | p :: pp' ->
     begin
       match ss with
       | [] -> false
       | s :: ss -> if s = p
                             (* loop AB ss AAB (A::ss) *)
                             (* os = (A :: ss) はどうやって導出できたのか? *)
                             (* os |-> str *)
                             (* str |-> s :: ss *)
                             (* s |-> A*)
                    then loop pp' ss op os                      
                    else next op op
     end
  and
    next op os =
    match os with
    | [] -> false
    | s :: ss -> loop op ss op ss
let search_aab s = loop ['A';'A';'B'] s ['A';'A';'B'] s
(* let _ =
 *   let foo z w =
 *     (foo (x, x) (x, x))     let f z w x =  [u |-> (x, x); y |-> (x, x); x |-> s :: ss] in f z w x
 * 
 *   [foo_m = Memo(f, foo, (x, x), (x, x), (int * int) -> ); goo_m = ]
 * let y = ...
 *   (foo (a, a) (a, a), (int * int) -> ) =>  f z w a *) 

let bl = List(Char)
let left = Arrow(bl, Arrow(bl, Arrow(bl, Arrow(bl, Bool))))
let right = Arrow(bl, Arrow(bl, Bool))
let fg = Pair(left, right)

let loop1 =
  let rc, ss', op, os, pp' =
    TVar(S (S (S (S (S (S (S (S  Z)))))))),
    TVar(S Z),
    TVar(S (S (S (S (S Z))))),
    TVar(S (S (S (S Z)))),
    TVar(S (S (S Z)))
  in
  TLam(fg,                      (* rc 8*)
       TLam(bl,                 (* pp 7*)
            TLam(bl,            (* ss 6*)
                 TLam(bl,       (* op 5*)
                      TLam(bl,  (* os 4*)
                           Case(Char, TVar(S (S (S Z))), TTrue,
                                Case(Char, TVar(S (S (S (S Z)))), TFalse,
                                     TIf(TVar(Z), TVar(S (S Z)),
                                         TApp4(Left(right, rc), pp', ss', op, os),
                                         TApp2(Right(left, rc), op, os)
                                       )
                                  )
                             )
                        )
                   )
              )
         )
    )
let next1 =
  let rc, op, ss =
    TVar(S (S (S (S Z)))),
    TVar(S (S (S Z))),
    TVar(S Z)
  in  
  TLam(fg,
       TLam(bl,                 (* op *)
            TLam(bl,            (* os *)
                 Case(Char, TVar(Z), TFalse,
                      TApp4(Left(right, rc), op, ss, op, ss)
                   )
              )
         )
  )
let search1 = Fix2(left, right, loop1, next1)
(* let _ =
 *   let time : (unit -> 'a) -> 'a * float =
 *     fun f ->
 *     let start = Sys.time () in
 *     let res   = f () in
 *     let end_  = Sys.time () in
 *     (res, end_ -. start)
 *   in
 *   let rec gen_pat n =
 *     if n = 0 then Nil
 *     else Cons(Ch(char_of_int (n+21)), gen_pat (n-1))
 *   in 
 *   (\* let pat = Cons(Ch('a'), Cons(Ch('b'), Cons(Ch('c'), Cons(Ch('d'), Cons(Ch('e'), Cons(Ch('f'), Cons(Ch('h'), Cons(Ch('i'), Cons(Ch('j'), Cons(Ch('k'), Nil)))))))))) in  *\)
 *   let pat_len = int_of_string Sys.argv.(1) in
 *   let head_len = int_of_string Sys.argv.(2) in
 *   (\* let head tail = Cons(Ch('a'), Cons(Ch('b'), Cons(Ch('c'), Cons(Ch('d'), Cons(Ch('e'), Cons(Ch('f'), Cons(Ch('g'), tail))))))) in *\)
 *   let rec head tail n =
 *     if n = 0 then tail
 *     else head (Cons(Ch(char_of_int (n+97)), tail)) (n-1)
 *   in 
 *   let pat = head (gen_pat pat_len) head_len in
 * 
 * (\* let pat = gen_pat pat_len in *\)
 *   let env = CtxS(bl, CtxZ) in
 *   let unf = ctx_to_unifier env in
 *   let memo = ctx_to_memo env in
 *   let t = 
 *     TApp4(Left(right, search1), pat, TVar(Z), pat, TVar(Z)) in
 *   let t' = sc unf memo env FNil t in
 *   (\* let rec gen_string n =
 *    *   if n = 0
 *    *   then Cons(Ch('c'), Cons(Ch('d'), Cons(Ch('e'), Cons(Ch('f'), Cons(Ch('h'), Cons(Ch('i'), Cons(Ch('j'), Cons(Ch('k'), Nil))))))))
 *    *   else Cons(Ch('a'), Cons(Ch('b'), gen_string (n-1)))
 *    * in *\)
 *   let rec gen_string n =
 *     if n = 0
 *     then gen_pat pat_len
 *     else head (gen_string (n-1)) head_len
 *   in
 * 
 *   let string = gen_string 10000 in
 *   let kmp () = eval (ENil) CtxZ FNil (TApp(TLam(bl, t'), string)) in
 * 
 *   let naive () = eval (ENil) CtxZ FNil (TApp(TLam(bl, t), string)) in
 *     let _ = Format.printf "%a@." p_term pat in
 *   let (ret_kmp, time_kmp) = time kmp in
 *   let (ret_naive, time_naive) = time naive in
 *   let _ = Format.printf "kmp = \n%b, time = %f@." ret_kmp time_kmp in
 *   let _ = Format.printf "naive = \n%b, time = %f@." ret_naive time_naive in
 *   () *)

(* let _ = Format.printf "search1 = \n%a@." p_term search1
 * let _ = Format.printf "loop = \n%a@." p_term loop1
 * let _ = Format.printf "search2 = \n%a@." p_term (search2 ()) *)

                
(*
 * let rec descend x y =
 *   match x with
 *   | [] -> y
 *   | x :: xs -> descend [] []
 *              
 * let rec descend' x y =
 *   match x with
 *   | [] -> y
 *   | x :: xs -> let rec f0 x y = []
 *                in f0 [] []
 * 
 * let rec descend'' x y =
 *   match x with
 *   | [] -> y
 *   | x :: xs -> f0 y
 * and f0 y = y 
 *)
(* let _ =
 *   let x0 = 0 in
 *   let x1 = 1 in
 *   let xs = [] in
 *   let rec rip xs =
 *     match xs with
 *     | [] -> rip xs
 *     | x' :: xs' -> rip xs'
 *   in
 *   (\* let r = rip (x0 :: x1 :: xs) in *\)
 *   let u = UCons(Bool, TVar(Z), UCons(Bool, TVar(Z), UCons(List(Bool), TVar(Z), UNil))) in
 *   let x = Cons(TVar(Z), Cons(TVar(S Z), TVar(S (S Z)))) in
 *   let typfun = Arrow(List(Bool), List(Bool)) in
 *   let rip' = Fix(typfun, 
 *                  TLam(typfun,
 *                      TLam(List(Bool),
 *                          Case(Bool, TVar(Z), TApp1(TVar(S Z), TVar(Z)),
 *                               TApp1(TVar(S (S (S Z))), TVar(S Z))
 *                            )
 *                        )
 *                    )
 *                )
 *   in
 *   (\* let rip'' = sc u EOM u (TApp1(rip', x)) in *\)
 *   Format.printf "rip'' = %a@." p_term rip' *)
(*
rip (x0 :: x1 :: xs)
V
let rec rip0 x0' x1' xs' <= 3
V
rip (x1 :: xs)
V
let rec rip1 x0' x1' xs' rip0' x0'' x1'' xs'' =  ... <= 7
V
rip xs
V
let rec rip2 x0' x1' xs' rip0'' x0''' x1''' xs'''
             rip1' x0'' x1'' xs'' rip0_'' x0_''' x1_''' xs_''' = ... <= 15
             
 *)
(* 
\ \ \ body :unit
SSSSSSZ    :G
      memo :unit
body       :G'
UNUNUN     :G
4, 6       :G
-2, 0      :unit
0, 2       :G'
 *)
(* let rec f0 x y = ... f1 x y ...
 * and f1 f0' x' y'  = ... f2 f1 f0 x' y' ... (\* f0, x, yも使用不可 *\)    
 * and f2 f1' f0'' x'' y'' = ... *)
(* append3 = 
 * ((N\\F:((N\\case 0  
 *                          [] -> 1  
 *                                  0:1 -> 0:((_0 3) 1)
 *                                           1) 0)
 *     1) 0)
 * append3 = 
 * ((Fix(\\\F:(((((Fix(\\\\\\case 3  
 *                                        [] -> 10  
 *                                                0:1 -> 0:(((((7 12) 1) 10) 12) 1)
 *                   ) 4) 3) 2) 4) 3)
 *                   
 *     ) 1) 0)
 * let _ = 
 *   let rec a0 x y = false :: a1 x y
 *   and a1 y x = match x with
 *   | [] -> y
 *   | x' :: xs' -> x' :: (a1 y xs') a2
 *   in a0 x y
 * let _ = 
 *   let rec a0 x y = false :: let rec a1 x' y' =  (\* x y を使用可能 let rec a2 x y x' y' =  *\) in a1 x y
 *   in a0 x y *)
                  
(* 
length ((case r of ...) l1 l2)
C(t1, C(t2, length (case l1 of ...))) : unit
C(Bool, C(Char, char -> bool -> g))
U(Char, Bool, [])
Char|Bool|[]| C(Bool, Char, char -> bool -> unit)
Char|Bool|C(Bool, Char, char -> bool -> unit)
Char|C(Char, char -> bool -> unit) : bool -> unit
length ((case r of ...) tl l2) : char -> char list -> char list -> char list -> unit
char list -> char list -> unit

 *)
