open Type
type value =
  | FunVal of int * term * value list * value list
  | RFunVal of int * term * value list * value list
  | R2FunVal of int * term * term * value list * value list
  | LeftVal of value
  | RightVal of value
  | PairVal of term * term
  | CharVal of char
  | IntVal of int
  | BoolVal of bool
  | ListVal of char list
type env = value list
type fenv = value list
let take_v : type a. int -> env -> value =
  fun i env -> List.nth env i
let take_f : type a. int -> fenv -> value =
  fun j fenv -> List.nth fenv j
  
        
let rec eval (i:int) (j:int) (env:env) (fenv:fenv) : term -> value =
  function
  | V n -> take_v n env
  | Vf n -> take_f n fenv
  | ChU c -> CharVal(c)
  | Lam t -> FunVal(i, t, env, fenv)
  | App(f, x) ->
     let x' = eval i j env fenv x in
     begin
       match eval i j env fenv f with
       | FunVal(i, t, env, fenv) ->
          eval (i+1) j (env@[x']) fenv t
       | RFunVal(j, Lam(body), env, fenv) ->
          eval (i+1) (j+1) (env@[x']) (fenv@[RFunVal(j, Lam(body), env, fenv)]) body
       | LeftVal(R2FunVal(j, Lam(f), Lam(g), env, fenv)) ->
          eval (i+1) (j+1) (env@[x']) (fenv@[R2FunVal(j, Lam(f), Lam(g), env, fenv)]) f
       | RightVal(R2FunVal(j, Lam(f), Lam(g), env, fenv)) ->
          eval (i+1) (j+1) (env@[x']) (fenv@[R2FunVal(j, Lam(f), Lam(g), env, fenv)]) g
       | _ -> failwith "function expected"
     end
  | Tr -> BoolVal(true)
  | Fa -> BoolVal(false)
  | Ze -> IntVal(0)
  | Su(t) ->
     begin
       match eval i j env fenv t with
       | IntVal(n) -> IntVal(n+1)
       | _ -> failwith "int expected"
     end 
  | Or(t1, t2) ->
     begin
       match eval i j env fenv t1, eval i j env fenv t2 with
       | BoolVal(t1), BoolVal(t2) -> BoolVal(t1 || t2)
       | _ -> failwith "bool expected"
     end
  | FixU(Lam(body)) -> RFunVal(j, body, env, fenv)
  | FixU(_) -> failwith "open recursion"
  | Fix2U(Lam(f), Lam(g)) -> R2FunVal(j, f, g, env, fenv)
  | Fix2U(_) -> failwith "open recursion"
  | NilU -> ListVal([])
  | ConsU(h, tl) ->
     begin 
       match eval i j env fenv h, eval i j env fenv tl with
       | CharVal(h), ListVal(tl) -> ListVal(h :: tl)
       | _ -> failwith "char list"
     end 
  | CaseU(x, nil, cons) ->
     begin
       match eval i j env fenv x with
       | ListVal(h :: tl) -> eval (i+2) j (env@[CharVal(h)]@[ListVal(tl)]) fenv cons
       | ListVal([]) -> eval i j env fenv nil
       | _ -> failwith "list expected"
     end
  | If(x, a, thn, els) ->
     begin
       match eval i j env fenv x, eval i j env fenv a with
       | CharVal(x), CharVal(a) ->
          if x = a then eval i j env fenv thn
          else eval i j env fenv els
       | _ -> failwith "bool?"
     end 
  | LeftU(t) -> LeftVal(eval i j env fenv t)
  | RightU(t) -> RightVal(eval i j env fenv t)     
let append =
  FixU(Lam(
           Lam((* 0 *)
               Lam( (* 1 *)
                   CaseU(V(0), V(1), (* 2, 3 *)
                         ConsU(V(2), App(App(Vf(0), V(3)), V(1)))
                     )
                 )
             )
    ))
let abcd = App(App(append,
                ConsU(ChU('a'), ConsU(ChU('b'), NilU))),
            ConsU(ChU('c'), ConsU(ChU('d'), NilU)))
       
                         
let _ = abcd |> eval 0 0 [] []

(* type 'g cenv =
 *   | CNil : unit cenv
 *   | CCons : 'a typ * 'a code * 'g cenv -> 'a * 'g cenv
 * let to_index i j term : term =
 *   match term with
 *   | Lam(t) -> Lam(to_index (i+1) j t)
 *   | App(f, x) -> App(to_index i j f, to_index i j x)
 *   | Vf(index) -> Vf(j-index)
 *   | V(index) -> V(i-index)
 * let (=>) : type a b. -> a typ -> b typ -> (a -> b) typ =
 *   fun t t' -> Arrow(t, t')
 * let index_to_c : type a. a typ -> term -> a code =
 *   let rec walk : type a g f. a typ -> g cenv -> f env -> term -> a code =
 *     fun typ env fenv term ->
 *     match term with
 *     | Lam(typ', t) -> .<fun x -> walk (typ'=>typ) CCons(typ', .<x>., env) fenv>.
 *     | App(f, x) -> .<walk *)

(* let _ = printf "%a@." ml_termU abcd *)
