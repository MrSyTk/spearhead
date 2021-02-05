module type Trans = sig
  type 'a t
  type 'a f
  val fwd : 'a f -> 'a t
  val bwd : 'a t -> 'a f
end
module type SYMOBS = sig
  include THOAS.THOAS
  type 'a obs
  val observe : 'a exp -> 'a obs
end
module SYMT(X:Trans) (F : SYMOBS with type 'a exp = 'a X.f) = struct
  open X
  type 'a t = 'a X.t
  type 'a exp = 'a t
  type 'a fexp = 'a F.exp
  type 'a obs = 'a F.obs
  let fwd : 'a fexp -> 'a exp = fwd
  let bwd : 'a exp -> 'a fexp = bwd
  let tlam typ t = fwd (F.tlam typ (fun v -> fwd v |> t |> bwd))
  let tlam_non typ t = fwd (F.tlam_non typ (fun v -> fwd v |> t |> bwd))
  let tapp f v  = fwd (F.tapp (bwd f) (bwd v))
  let tor v1 v2  = fwd (F.tor (bwd v1) (bwd v2))
  let tt _ = fwd (F.tt ())
  let tf _ = fwd (F.tf ())
  let fix t f = fwd (F.fix t (bwd f))
  let fix2 t0 t1 f g = fwd (F.fix2 t0 t1 (bwd f) (bwd g))
  let nil _ = fwd (F.nil ())
  let cons h tl = fwd (F.cons (bwd h) (bwd tl))
  let case t x nil cons =
    F.case t (bwd x)
      (fun () -> bwd nil)
      (fun h tl -> cons (fwd h) (fwd tl) |> bwd)
    |> fwd
  let tif x a thn els =  F.tif (bwd x) (bwd a) (bwd thn) (bwd els) |> fwd   
  let left t term = fwd (F.left t (bwd term))
  let right t term = fwd (F.right t (bwd term))
  let zero _ = fwd (F.zero ())
  let succ n  = fwd (F.succ (bwd n))
  let observe t = F.observe (bwd t)
end
open Type
open TDB
open Shift
module DBLib(F : THOAS.THOAS) = struct
  module X = struct
    type 'a f = 'a F.exp
    type 'd funs = EMPTY : unit funs
    type 'a exp = {contents : 'c 'd. ('c, 'd) ctx -> 'd funs -> ('c, 'd, 'a) tTerm}
    type 'a t =
      | Term : 'a exp -> 'a t
      | Ukn : 'a f -> 'a t
    let fwd : type a. a f -> a t =
      fun t -> Ukn t
    (* type _ tenv =
     *   | TEmpty : unit tenv
     *   | TExtend : ('ctx tenv * 'b f) -> ('b -> 'ctx) tenv *)
    type 'g tenv =
      | TENil : unit tenv
      | TECons : 'a f * 'g tenv -> ('a -> 'g) tenv
    let rec lookup : type g d a. g tenv -> (g, d, a) index -> a f =
      fun env i ->
      match env, i with
      | TENil, i -> failwith "free variable"
      | TECons(v, _), Z -> v
      | TECons(_, env), S i -> lookup env i
      | _, P(t, i) -> lookup (TECons(failwith "minus variable", env)) i

    (* let rec lookT :  type a ctx. ctx tenv -> (ctx, a) index -> a f = 
     *   fun env inx ->
     *   match env, inx with
     *   | TExtend(_, v) , Z -> v
     *   | TExtend(env, _) , S(n) ->
     *      begin
     *        match env with
     *        | TEmpty -> failwith "var not found"
     *        | TExtend _ -> lookT env n
     *      end
     *   | _, P _ -> failwith "minus index" *)
    let rec shift_by_ctx : type g g' d d' a. (g, d) ctx -> (g', d') ctx -> (g', d', a) tTerm -> (g, d', a) tTerm =
        fun inner_ctx outer_ctx f ->
        match inner_ctx, outer_ctx with
        | CtxZ, CtxZ -> f
        | CtxZ, _ -> failwith ""
        | CtxS(t, inner_ctx), outer_ctx -> shift_by_ctx inner_ctx outer_ctx f |> shift_up t
    let dd = rename_ctx
    type 'd fenv =
      | TFNil : unit fenv
      | TFun : 'a f * 'd fenv -> ('a -> 'd) fenv
    let rec toHOAS : type a g d. g tenv -> (g, d) ctx -> d fenv -> (g, d, a) tTerm -> a f =
      fun env ctx funs ->
      function
      | TVar n -> lookup env n
      | TFVar(i) -> lookupf env ctx funs i
      | Next(t, f) ->
         let body = shift_by_ctx ctx CtxZ f |> shift_up t in
         let ctx = (CtxS(t, ctx)) |> dctx t in
         let f self = toHOAS (TECons(self, env)) ctx (TFun(self, funs)) body in
         begin match t with Arrow _ -> F.fix t @@ F.tlam t @@ f | _ -> failwith "" end
      | TLam(t, body) -> F.tlam t @@ fun x -> toHOAS (TECons(x, env)) (CtxS(t, ctx)) funs body
      | TLamNon(t, body) -> F.tlam_non t @@ fun x -> toHOAS (TECons(x, env)) (CtxS(t, ctx)) funs body
      | TApp(f, p) -> F.tapp (toHOAS env ctx funs f) (toHOAS env ctx funs p)
      | TTrue -> F.tt ()
      | TFalse -> F.tf ()
      | TOr(t1, t2) -> F.tor (toHOAS env ctx funs t1) (toHOAS env ctx funs t2)
      | Fix(t, f) -> F.fix t (toHOAS env ctx funs f)
      | Fix2(t0, t1, f, g) -> F.fix2 t0 t1 (toHOAS env ctx funs f) (toHOAS env ctx funs g)
      | Nil -> F.nil ()
      | Cons(h, tl) -> F.cons (toHOAS env ctx funs h) (toHOAS env ctx funs tl)
      | Case(t, x, nil, cons) ->
         let cons h tl = toHOAS (TECons(h, TECons(tl, env))) (CtxS(t, CtxS(List(t), ctx))) funs cons in
         F.case t (toHOAS env ctx funs x)
           (fun () -> toHOAS env ctx funs nil)
           cons
      | TApp1(f, arg0) -> F.tapp (toHOAS env ctx funs f) (toHOAS env ctx funs arg0)
      | TApp2(f, arg0, arg1) -> F.tapp (F.tapp (toHOAS env ctx funs f) (toHOAS env ctx funs arg0)) (toHOAS env ctx funs arg1)
      | TApp3(f, arg0, arg1, arg2) ->
         F.tapp (F.tapp (F.tapp (toHOAS env ctx funs f) (toHOAS env ctx funs arg0)) (toHOAS env ctx funs arg1)) (toHOAS env ctx funs arg2)
      | TApp4(f, arg0, arg1, arg2, arg3) ->
         F.tapp
           (F.tapp
              (F.tapp
                 (F.tapp
                    (toHOAS env ctx funs f) (toHOAS env ctx funs arg0))
                 (toHOAS env ctx funs arg1))
              (toHOAS env ctx funs arg2))
           (toHOAS env ctx funs arg3)
      | TApp5(f, arg0, arg1, arg2, arg3, arg4) ->
         F.tapp
           (F.tapp
              (F.tapp
                 (F.tapp
                    (F.tapp
                       (toHOAS env ctx funs f) (toHOAS env ctx funs arg0))
                    (toHOAS env ctx funs arg1))
                 (toHOAS env ctx funs arg2))
              (toHOAS env ctx funs arg3))
           (toHOAS env ctx funs arg4)
      | TIf(x, a, thn, els) ->
         F.tif (toHOAS env ctx funs x) (toHOAS env ctx funs a) (toHOAS env ctx funs thn) (toHOAS env ctx funs els)
      | Left(r, t) -> F.left r (toHOAS env ctx funs t)
      | Right(l, t) -> F.right l (toHOAS env ctx funs t)
      | Ch(c) -> F.char c
      | Succ n -> F.succ (toHOAS env ctx funs n)
      | Zero -> F.zero ()
    and lookupf : type g d a. g tenv -> (g, d)  ctx -> d fenv -> (g, d, a) findex -> a f =
      fun env inner_ctx funs i ->
      match funs, i with
      | TFNil, i -> failwith "free function"
      | TFun(f, _), Zf -> f (* shift_by_ctx inner_ctx ctx f |> eval env inner_ctx funs *)
      | TFun(_, funs), Sf i -> lookupf env (dd inner_ctx) funs i

    let bwd : type a. a t -> a f =
      function
      | Term({contents = c}) -> toHOAS TENil CtxZ TFNil (c CtxZ EMPTY)
      | Ukn t -> t
  end
  open X
  module IDelta = struct
    open F
    (* f に現在の型環境とインデックスを入れる *)
    let untdb {contents = x} = x                                   
    (* val tlam : 'a typ -> ('a exp -> 'b exp) ->  ('a -> 'b) exp *)
    let tlam : 'a typ -> ('a t -> 'b t) -> ('a -> 'b) t =
      fun t f ->
      let cnt : type i d. (i, d) ctx -> d funs -> (i, d, 'a -> 'b) tTerm =
        fun i funs ->
        let v : type j d'. (j, d') ctx -> d' funs -> (j, d', 'a) tTerm =
          fun j funs' ->
          match funs, funs' with
          | EMPTY, EMPTY -> TVar(tshift j (CtxS (t, i)))
        in              (* j+1 - (i+1) *)
        let body = match f (Term({contents = v})) with
          | Term(b) -> b
          | _ -> failwith "parse f"
        in TLam(t, untdb body (CtxS(t, i)) funs)
      in 
      Term({contents = cnt})
    let tlam_non : 'a typ -> ('a t -> 'b t) -> ('a -> 'b) t = tlam
    let tapp x y =
      match x, y with
      | Term({contents = f}), Term({contents = a}) ->
         begin
           Term({contents =
                   fun i funs ->
                   match f i funs with
                   | TApp4(f, a0, a1, a2, a3) -> TApp5(f, a0, a1, a2, a3, a i funs)
                   | TApp3(f, a0, a1, a2) -> TApp4(f, a0, a1, a2, a i funs)
                   | TApp2(f, a0, a1) -> TApp3(f, a0, a1, a i funs)
                   | TApp1(f, a0) -> TApp2(f, a0, a i funs)
                   | TApp(f, a0) -> TApp2(f, a0, a i funs)
                   | f -> TApp1(f, a i funs)    (* 6以上の引数の場合 *)
             })
         end
      | _ -> failwith "parse tapp"
    let tt _ = Term({contents = fun i funs -> TTrue})
    let tf _ = Term({contents = fun i funs -> TFalse})

    let tor t1 t2 =
      match t1, t2 with
      | Term({contents = t1}), Term({contents = t2}) -> 
         Term({contents =
                 fun i f -> TOr(t1 i f, t2 i f)       
           })
      | _ -> failwith "parse tor"
    let fix t f =
      match f with
      | Term({contents = f}) -> 
         Term({contents =
            fun i funs -> Fix(t, f i funs)
         })
      | _ -> failwith "parse fix"
    let fix2 t0 t1 f g =
      match f, g with
      | Term({contents = f}), Term({contents = g}) -> 
         Term({contents =
                 fun i funs -> Fix2(t0, t1, f i funs, g i funs)
           })
      | _ -> failwith "parse fix2"
    let nil _ = Term({contents = fun i funs -> Nil})
    let cons h tl =
      match h, tl with
      | Term({contents = h}), Term({contents = tl}) -> 
         Term({contents =
            fun i funs -> Cons(h i funs, tl i funs)
         })
      | _ -> failwith "parse cons"
    let case (t : 'a typ) (Term({contents = x})) nil cons =
        let cnt : type i d. (i, d) ctx -> d funs -> (i, d, 'b) tTerm  =
          fun i funs ->
          let h : type i d'. (i, d') ctx -> d' funs -> (i, d', 'a) tTerm =
            fun j funs' ->
            match funs, funs' with
            | EMPTY, EMPTY -> TVar(tshift j (CtxS(t, CtxS(List(t), i))))
          in                    
          let tl : type i d'. (i, d') ctx -> d' funs -> (i, d', 'a list) tTerm =
            fun j funs'  ->
            match funs, funs' with
            | EMPTY, EMPTY -> TVar(tshift j (CtxS(List(t), i)))                   
          in
          let cons_body =
            begin
              match cons (Term({contents = h})) (Term({contents = tl})) with
              | Term(b) -> b
              | _ -> failwith "parse case_cons"
            end
          in
          let nil_body =
            begin
              match nil () with
              | Term(b) -> b
              | _ -> failwith "parse case_nil"
            end
          in 
          Case(t, x i funs, untdb nil_body i funs, untdb cons_body (CtxS(t, CtxS(List(t), i))) funs)
        in 
        Term({contents = cnt})
    let tif x a thn els =
      match x, a, thn, els with
      | Term({contents = x}), Term({contents = a}), Term({contents = thn}), Term({contents = els}) ->
         Term({contents =
                 fun i f->
                 TIf(x i f, a i f, thn i f, els i f)
           })
      | _ -> failwith "parse tif"
    let left t l =
      match l with
      | Term({contents = l}) -> 
         Term({contents =
                 fun i f -> Left(t, l i f)
           })
      | _ -> failwith "parse left"
    let right t r =
      match r with
      | Term({contents = r}) -> 
         Term({contents =
                 fun i f -> Right(t, r i f)
           })
      | _ -> failwith "parse right"
    let char c = Term({contents = fun i f -> Ch(c)})
    let zero _ = Term({contents = fun i f -> Zero})
    let succ n =
      match n with
      | Term({contents = n}) ->
         Term({contents =
                 fun i f -> Succ(n i f)
           })
      | _ -> failwith "parse succ"
    let sc body =
      match body with
      | Term({contents = body}) -> 
         Term({contents =
                 fun i f -> body i f
           })
      | _ -> failwith "parse sc"
    (* let observe {contents = e} = e (CtxZ) *)
  end
end
module Unembedded(F:SYMOBS) = struct
  module OptM = DBLib(F)
  include SYMT(OptM.X)(F)
  include OptM.IDelta
end
