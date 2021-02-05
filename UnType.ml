open Type
module UnType = struct
  type un = U | N
  let rec p_un ppf =
    function
    | U -> Format.fprintf ppf "U"
    | N -> Format.fprintf ppf "N"
  type used =
    | Func
    | Un of un list
  let long = [U; U; U; U; U]
  type 'a exp = int -> int -> used list -> term * un list option
  let rec check_fix =
    function
    | Func :: [] -> true
    | h :: tl -> check_fix tl
    | [] -> false
  let rec add_used (u:un) =
    function
    | Un(ls) :: [] -> Un(ls @ [u]) :: []
    | h :: tl -> h :: (add_used u tl)
    | [] -> []
  let rec start_used =
    function
    | Func :: [] ->
       Un([]) :: []
    | h :: tl -> h :: start_used tl
    | _ -> failwith "check used list"
  
  let tlam _ f i j used =
    if check_fix used then      (* fix直下の時の例外処理 *)
      let body, used = f (fun i _ u -> Vf j, None) i (j+1) (start_used used) in
      Lam(body), used
    else
      let body, used = f (fun _ j u -> V i, None) (i+1) j (add_used (U) used) in
      match used with
      | Some(u) -> Lam(body), Some(U :: u)
      | None -> Lam(body), Some([U])      
  let tlam_non _ f i j used =
    let body, used =  f (fun _ j u -> V i, None) i j (add_used (N) used) in
    match used with
    | Some(u) -> body, Some(N :: u)
    | None -> body, Some([N])      
  let tapp f x = fun i j used ->
    let f = f i j used in
    (* let _ = Format.printf "f = %a@." p_termU (fst f) in *)
    let x' = x i j used |> fst in
    match f with
    | Vf(n), None ->
       begin
         match List.nth used n with
         | Un(U::tl) -> App(Vf(n), x'), Some(tl)
         | Un(N::tl) -> Vf(n), Some(tl)
         | _ -> failwith "more than one arg"
       (* let _ = Format.printf "j = %d : " n in
        * let _ = List.iter (Format.printf "%a" p_un) u in
        * let _ = Format.printf "@." in *)
       end 
    | LeftU(Vf(n)), _ ->
       let u = long in       
       begin
         match u with
         | U :: tl -> App(LeftU(Vf(n)), x'), Some(tl)
         | N :: tl -> LeftU(Vf(n)), Some(tl)
         | [] -> failwith "more than one arg"
       end 
    | RightU(Vf(n)), _ ->
       let u = long in       
       begin
         match u with
         | U :: tl -> App(RightU(Vf(n)), x'), Some(tl)
         | N :: tl -> RightU(Vf(n)), Some(tl)
         | [] -> failwith "more than one arg"
       end 
    | t, Some(U :: tl) -> App(t, x'), Some(tl)       
    | t, Some(N :: tl) -> t, Some(tl)       
    | t, _ -> failwith "first order"
  let char (c : char) _ _ _ = ChU(c) , None                       
  let tt _ _ _ _ = Tr, None
  let tf _ _ _ _ = Fa, None
  let tor t1 t2 i j used = Or(t1 i j used |> fst, t2 i j used |> fst), None
  let fix _ f i j used =
    let f, used = f i j (used @ [Func]) in
    FixU(f), used
  let fix2 _ _ f g i j used =
    let f, u = f i j (used @ [Func]) in (* 左をトップでは使う約束 *)
    let g, _ = g i j (used @ [Func]) in    (* こっちのusedは使わない *)
    Fix2U(f, g), u
  let nil () i j used = NilU, None
  let cons h tl i j used = ConsU(h i j used |> fst, tl i j used |> fst), None
  let case _ x nil cons i j used =
    let cons, _ = cons (fun _ j u -> V i, None) (fun _ j u -> V (i+1), None) (i+2) j used in
    CaseU(x i j used |> fst, nil () i j used |> fst, cons), None
  let tif x a thn els i j used =
    If(x i j used |> fst, a i j used |> fst, thn i j used |> fst, els i j used |> fst), None
  let left _ t i j used =
    let t, used = t i j used in
    LeftU(t), used
  let right _ t i j used =
    let t, used = t i j used in
    RightU(t), used
  let succ n i j used =
    let n, used = n i j used in
    Su(n), used
  let zero () i j used = Ze, None
  let sc t i j used = t i j used
end

module UnTypeObs(I:THOAS.THOAS) = struct
  include I
  type 'a obs = term
  let observe e = e 0 0 [] |> fst
end
