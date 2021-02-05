open Type
(* open Codelib *)
module C = struct
  type 'a exp = 'a code

  let char (c:char) = .<c>.
  let tlam _ body = .<fun x -> .~(body .<x>.)>.
  let tlam_non _ body = .<fun x -> .~(body .<x>.)>.
  let tapp f x = .<.~f .~x>.
  let tt _ = .<true>.
  let tf _ = .<false>.
  let tor t1 t2 = .<.~t1 || .~t2>.
  type 'a recc = In of ('a recc -> 'a)
  let out (In x) = x
  let rec fix t f =    
    .<let rec self x = .~f self x in self>.
  let rec fix2 t0 t1 f g =
    (* let y f g = (fun x a -> f (out x x) a) (In(fun (x, y) a -> f (out x x) a)), 
     *             (fun y a -> g (out y y) a) (In(fun (x, y) a -> g (out y y) a)) in
     * y f g *)
    (* ((fun x -> f (fix2 a0 r0 a1 r1 f g) x), (fun y -> g (fix2 a0 r0 a1 r1 f g) y)) *)
    .<let rec self_f x =
      .~f (self_f, self_g) x
      and self_g y =
      .~g (self_f, self_g) y
      in (self_f, self_g)>. 
  (* pow (self, next)  n k = ...  *)
  let nil _ = .<[]>.
  let cons h tl = .<.~h :: .~tl>.
  let case _ x nil cons = .<match .~x with [] -> .~(nil ()) | h :: tl -> .~(cons .<h>. .<tl>.)>.
  let tif x a thn els = .<if .~x = .~a then .~thn else .~els>.
  let left _ pair = .<fst (.~pair)>.
  let right _ pair = .<snd (.~pair)>.
  let succ n = .<1 + .~n>.
  let zero _ = .<0>.
  let sc body = body
end
module CObs(I:THOAS.THOAS) = struct
  include I
  type 'a obs = 'a code
  let observe e = e
end
