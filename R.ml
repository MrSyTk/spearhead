open Type
module R = struct
  type 'a exp = int ref -> 'a
  let char c _ = c
  let tlam _ (body : (int ref -> 'a) -> int ref -> 'b) cnt x =
    body (fun cnt -> x) cnt
  let tlam_non _ (body : (int ref -> 'a) -> int ref -> 'b) cnt x =
    body (fun cnt -> x) cnt

  let tapp f x cnt = (f cnt) (x cnt)
  let tt _ _ = true
  let tf _ _ = false
  let tor t1 t2 cnt = (t1 cnt) || (t2 cnt)
  let rec fix t f cnt =
    let rec self n = f cnt self n in self
    (* let y f = (fun x a -> f (out x x) a) (In (fun x a -> f (out x x) a))
     * (\* let z = fun f -> (fun x -> f (fun y -> x x y)) (fun x -> f (fun y -> x x y)) *\)
     * in y f *)
    (* let rec self n = f self n in self *)
    (* f (fun y -> (fix t f cnt) y) cnt *)
    
  let rec fix2 t0 t1 f g cnt =
    (* let y f g = (fun x a -> f (out x x) a) (In(fun (x, y) a -> f (out x x) a)), 
     *             (fun y a -> g (out y y) a) (In(fun (x, y) a -> g (out y y) a)) in
     * y f g *)
    (* ((fun x -> f (fix2 a0 r0 a1 r1 f g) x), (fun y -> g (fix2 a0 r0 a1 r1 f g) y)) *)
    (* .<let rec self_f x =
     * .~(f (.<self_f>., .<self_g>.) .<x>.)
     *   and self_g y =
     *     .~(g (.<self_f>., .<self_g>.) .<y>.)
     *       in (self_f, self_g)>. *) 
    let rec self_f x =
    f cnt (self_f, self_g) x
      and self_g y =
        g cnt (self_f, self_g) y
          in (self_f, self_g)
  (* pow (self, next)  n k = ...  *)
  let nil _ _ = []
  let cons h tl cnt = (h cnt) :: (tl cnt)
  let case _ x nil cons cnt =
    match (x cnt) with
    | [] -> nil () cnt
    | h :: tl -> cons (fun cnt -> h) (fun cnt -> tl) cnt
  let tif x a thn els cnt =
    let _ = cnt := !cnt+1 in
    if (x cnt) = (a cnt) then (thn cnt) else (els cnt)
  let left _ t cnt = fst (t cnt)
  let right _ t cnt = snd (t cnt)
  let succ n cnt = 1 + (n cnt)
  let zero _ cnt = 0
  let sc body cnt = (body cnt)
end
module RObs(I:THOAS.THOAS) = struct
  include I
  type 'a obs = int ref -> 'a
  let observe e = e
end
