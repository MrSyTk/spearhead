type _ typ =
  | Char : char typ
  | Bool : bool typ
  | Arrow : ('a typ * 'b typ) -> ('a -> 'b) typ
  | List : 'a typ -> 'a list typ
  | Pair : ('a typ * 'b typ) -> ('a * 'b) typ
  | Int : int typ
let (=>) = fun a b -> Arrow(a, b)
let (=*) = fun a b -> Pair(a, b)
type (_(* typ *) , _(* typ *)) eq_typ =
  | Eq : ('a, 'a) eq_typ
let rec eq_test : type a b. a typ -> b typ -> (a, b) eq_typ option =
  fun t1 t2 ->
  match t1, t2 with
  | Bool, Bool -> Some Eq
  | Int, Int -> Some Eq
  | Char, Char -> Some Eq
  | Arrow(t1', t1'') ,  Arrow(t2', t2'') ->
     begin
       match eq_test t1' t2' , eq_test t1'' t2'' with
       | Some Eq, Some Eq -> Some Eq
       | _ -> None
     end
  | List(t1') ,  List(t2') ->
     begin
       match eq_test t1' t2' with
       | Some Eq -> Some Eq
       | _ -> None
     end
  | Pair(t1', t1'') ,  Pair(t2', t2'') ->
     begin
       match eq_test t1' t2' , eq_test t1'' t2'' with
       | Some Eq, Some Eq -> Some Eq
       | _ -> None
     end
  | _ -> None
open Format
let rec p_type : type a. Format.formatter -> a typ -> unit =
  fun ppf ->
  function
  | Int -> fprintf ppf "I"
  | Bool -> fprintf ppf "B"
  | Char -> fprintf ppf "C"
  | List(t) -> fprintf ppf "[%a]" p_type t
  | Arrow(t1, t2) -> fprintf ppf "(%a)->%a" p_type t1 p_type t2
  | Pair(t1, t2) -> fprintf ppf "(%a, %a)" p_type t1 p_type t2

type term =
  | Su of term
  | Ze
  | V of int
  | Vf of int
  | ChU of char
  | Lam of term
  | App of term * term
  | Tr
  | Fa
  | Or of term * term
  | FixU of term
  | Fix2U of term * term
  | NilU
  | ConsU of term * term
  | If of term * term * term * term
  | LeftU of term
  | RightU of term
  | CaseU of term * term * term

open Format
let rec p_termU : formatter -> term -> unit =
  fun ppf -> 
  function
  | V(i) -> fprintf ppf "%d" i
  | Vf(i) -> fprintf ppf "_%d" i
  | Lam(t) -> fprintf ppf "@[<hov 2>\\%a@]" p_termU t
  | App(t1, t2) -> fprintf ppf "@[<hov 2>(%a %a)@]" p_termU t1 p_termU t2
  | Tr -> fprintf ppf "T"
  | Fa -> fprintf ppf "F"
  | Ze -> fprintf ppf "Z"
  | Su(t) -> fprintf ppf "S(%a)" p_termU t
  | ChU(c) -> fprintf ppf "%c" c
  | Or(t1, t2) -> fprintf ppf "@[<hov 2>%a||%a@]" p_termU t1 p_termU t2
  | FixU(f) -> fprintf ppf "@[<hov 4>Fix(%a)@]" p_termU f
  | Fix2U(f, g) -> fprintf ppf "@[<hov 5>Fix2(%a, @,%a)@]" p_termU f p_termU g
  | NilU -> fprintf ppf "[]"
  | ConsU(h, tl) -> fprintf ppf "%a:%a" p_termU h p_termU tl
  | CaseU(x, nil, cons) -> fprintf ppf "@[<v 2>case %a  @,[] -> %a  @,?:? -> %a@]"
                               p_termU x p_termU nil p_termU cons
  | If(x, a, thn, els) -> fprintf ppf "@[<v 0>if  %a=%a @,then %a  @,else %a@]"
                             p_termU x p_termU a p_termU thn p_termU els
  | LeftU(t) -> fprintf ppf "@[<hov 2>%a.fst@]" p_termU t
  | RightU(t) -> fprintf ppf "@[<hov 2>%a.snd@]" p_termU t
                             
type andls = string list ref
open Format
let rec to_s (jr : int list) (ls : andls) i (j : int ref) () =
  function
  | V(i) -> sprintf "x%d" i
  | Vf(j) -> sprintf "f%d" (List.nth jr j)
  | ChU(c) -> sprintf "'%c'" c
  | Lam(t) -> sprintf "(fun x%d -> %a)" i (to_s jr ls (i+1) j) t
  | App(f, x) -> sprintf "%a (%a)" (to_s jr ls i j) f (to_s jr ls i j) x
  | Tr -> sprintf "true"
  | Fa -> sprintf "false"
  | Ze -> sprintf "0"
  | Su t -> sprintf "1+(%a)" (to_s jr ls i j) t
  | Or(t1, t2) -> sprintf "%a || %a" (to_s jr ls i j) t1 (to_s jr ls i j) t2
  | FixU(Lam(body)) ->
     let rec loop i () =
       function
       | Lam(arg) -> sprintf "x%d %a" i (loop (i+1)) arg
       | body ->
          let jr = jr @ [!j] in
          j := !j + 1;
          sprintf "= @,%a" (to_s jr ls i j) body
     in
     (* printf "j = %d@." j; *)
     let j = !j in
     let k = sprintf "f%d %a" j (loop i) body in 
     ls := k :: !ls; sprintf "f%d" j
     (* List.iter
      *   (fun f -> printf "@[<hov 2>and %s@]@." f) !ls; *)
  | Fix2U(Lam(f), Lam(g)) ->
     let jr = jr @ [!j] in
     j := !j + 1;
     sprintf
       "@[<hov 4>let rec self_f x = (fun f%d -> %a) (self_f, self_g) x@]@,"
       (!j-1)
       (to_s jr ls i j) f ^ 
     sprintf
       "@[<hov 4> and self_g y = (fun f%d -> %a) (self_f, self_g) y in (self_f, self_g)@]"
       (!j-1)
       (to_s jr ls i j) g
  | NilU -> sprintf "[]"
  | ConsU(h, tl) -> sprintf "%a :: %a" (to_s jr ls i j) h (to_s jr ls i j) tl
  | If(x, a, thn, els) ->
     sprintf "@[<v 0>if  %a = %a @,then %a  @,else %a@]"
       (to_s jr ls i j) x (to_s jr ls i j) a (to_s jr ls i j) thn (to_s jr ls i j) els
  | LeftU(t) -> sprintf "@[<hov 2>fst (%a)@]" (to_s jr ls i j) t
  | RightU(t) -> sprintf "@[<hov 2>snd (%a)@]" (to_s jr ls i j) t
  | CaseU(x, nil, cons) -> sprintf "@[<v 2>(match %a with @,| [] -> %a  @,| x%d::x%d -> %a)@]" 
                             (to_s jr ls i j) x (to_s jr ls i j) nil i (i+1) (to_s jr ls (i+2) j) cons
  | _ -> failwith "fix, fix2"

let andls : andls = ref []
(* let _ = sprintf "%a" (to_s andls 0 0) abcd *)

let ml_termU () term =
  let andls : andls = ref [] in
  let k = to_s [] andls 0 (ref 0) () term in
  (* let _ = printf "%d@." (List.length !andls) in  *)
  match !andls with
  | h :: tl -> 
     List.fold_left
       (fun ls f -> sprintf "%s@.@[<hov 2>and %s@]" ls f)
       (sprintf "@[<hov 2>let rec %s@]" h) tl ^ 
       sprintf "@.in %s@." k
  | [] -> sprintf "%s@." k
