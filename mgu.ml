open Type
open TDB
open Shift

type ('g, 'd) equation = E : ('g, 'd, 'a) tTerm * ('g, 'd, 'a) tTerm -> ('g, 'd) equation
let rec find_c : type g d. (g, d) equation list -> (g, d) equation list =
  function
  | [] -> []
  | E(TApp(f1, t1), TApp(f2, t2)) :: tl ->
     begin
       match eq_term f1 f2 with
       | Some TermEq -> find_c (E(t1, t2) :: tl)
       | _ -> find_c tl
     end       
  | E(TApp1(f1, t1), TApp1(f2, t2)) :: tl ->
     begin
       match eq_term f1 f2 with
       | Some TermEq -> find_c (E(t1, t2) :: tl)
       | _ -> find_c tl
     end
  | E(TApp2(f, arg0, arg1), TApp2(f', arg0', arg1')) :: tl ->
     begin
       match eq_term f f' with
       | Some TermEq -> find_c ((E(arg0, arg0')) :: (E(arg1, arg1')) :: tl)
       | _ -> find_c tl
     end
  | E(TApp3(f, arg0, arg1, arg2), TApp3(f', arg0', arg1', arg2')) :: tl ->
     begin
       match eq_term f f' with
       | Some TermEq -> find_c ((E(arg0, arg0')) :: (E(arg1, arg1')) :: (E(arg2, arg2')) :: tl)
       | _ -> find_c tl
     end
  | E(TApp4(f, arg0, arg1, arg2, arg3), TApp4(f', arg0', arg1', arg2', arg3')) :: tl ->
     begin
       match eq_term f f' with
       | Some TermEq -> find_c ((E(arg0, arg0')) :: (E(arg1, arg1')) :: (E(arg2, arg2')) :: (E(arg3, arg3')) :: tl)
       | _ -> find_c tl
     end
  | E(TApp5(f, arg0, arg1, arg2, arg3, arg4), TApp5(f', arg0', arg1', arg2', arg3', arg4')) :: tl ->
     begin
       match eq_term f f' with
       | Some TermEq -> find_c ((E(arg0, arg0')) :: (E(arg1, arg1')) :: (E(arg2, arg2')) :: (E(arg3, arg3')) :: (E(arg4, arg4')) :: tl)
       | _ -> find_c tl
     end
  | E(Case(t1, x1, nil1, cons1), Case(t2, x2, nil2, cons2)) :: tl ->
     begin
       match eq_test t1 t2 with
       | Some Eq -> 
          begin
            match eq_term nil1 nil2,
                  eq_term cons1 cons2 with
            | Some TermEq, Some TermEq -> find_c ((E(x1, x2)) :: tl)
            | _ -> find_c tl
          end
       | _ -> find_c tl
     end
  | E(Cons(h1, tl1), Cons(h2, tl2)) :: tl -> find_c (E(h1, h2) :: E(tl1, tl2) :: tl)
  | E(TOr(l1, r1), TOr(l2, r2)) :: tl -> find_c (E(l1, l2) :: E(r1, r2) :: tl)
  | E(Succ n, Succ n') :: tl -> find_c (E(n, n') :: tl)
  | h :: tl -> h :: find_c tl
let rec find_subst : type g d. (g, d) equation list -> (g, d) unifier -> (g, d) equation list * (g, d) unifier =
  let rec add_subst : type g d a. (g, d) unifier -> (g, d, a) index -> (g, d, a) tTerm -> (g, d) unifier =
    fun unifier i term ->
    match unifier, i with
    | _, P _ -> failwith "P in mgu"
    | UNil, _ -> .
    | UCons(t, v, tl), Z -> UCons(t, term, tl)
    | UCons(t, v, tl), S i -> UCons(t, v, add_subst tl i (shift_down t term))
  in
  let unify_all : type g d. (g, d) unifier ->
                          (g, d) equation list ->
                          (g, d) equation list =
    fun unifier -> 
    List.map (function E(t, t') -> E(unify unifier t, unify unifier t'))
  in 
  function
  | [] -> fun u -> [], u
  | E(TVar(i), TVar(j)) ::  tl ->
     begin
       match eq_index i j with
       | Some IndexEq -> fun unifier -> find_subst tl unifier
       | None ->
          fun unifier -> 
          let unifier = add_subst unifier i (TVar(j)) in
          find_subst (unify_all unifier tl) unifier
     end
  | E(TVar(i), t) :: tl ->
     fun unifier -> 
     let unifier = add_subst unifier i t in
     find_subst (unify_all unifier tl) unifier
  | _ :: tl -> fun unifier -> find_subst tl unifier
                 
     
        
let rec mgu : type a g d.
                   (g, d) equation list ->
                   (g, d) unifier ->
                   (g, d) unifier option =
  fun eqls unifier ->
  let eqls' = find_c eqls in
  let eqls'', unifier'  = find_subst eqls' unifier in
  match eqls'' with
  | [] -> Some(unifier')
  | _ ->
     if eqls'' = eqls then None
     else mgu eqls'' unifier'
  
let cx = Cons(TVar(Z), Nil)
let cy = Cons(TVar(S Z), Nil)
let uxy = UCons(Char, TVar(Z), UCons(Char, TVar(Z), UNil))
let uxy' : (char -> char -> unit, unit) unifier =
  match mgu [E(cx, cy)] uxy with
  | Some(u) -> u
  | None -> uxy
(* let _ = Format.printf "uxy' = %a@." (p_unifier 0) uxy' *)
