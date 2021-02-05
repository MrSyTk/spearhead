open Type
module type THOAS = sig
  type 'a exp
  (* type 'a obs *)
  val char : char -> char exp
  val tlam : 'a typ -> ('a exp -> 'b exp) -> ('a -> 'b) exp
  val tlam_non : 'a typ -> ('a exp -> 'b exp) -> ('a -> 'b) exp
  val tapp : ('a -> 'b) exp -> 'a exp -> 'b exp
  val tor : bool exp -> bool exp -> bool exp
  val tt : unit -> bool exp
  val tf : unit -> bool exp
  val fix : ('a -> 'b) typ -> (('a -> 'b) -> 'a -> 'b) exp ->
            ('a -> 'b) exp
  (* 
   * fix2の引数の数を固定すると、コードに定義を埋め込むことができるようになり高速化が可能
   * ただし、今回の場合引数が不定のため、https://github.com/yallop/metaocaml-letrec
   * を利用する
   *)
  val fix2 : ('a0 -> 'r0) typ -> ('a1 -> 'r1) typ ->
             ((('a0 -> 'r0) * ('a1 -> 'r1)) -> 'a0 -> 'r0) exp ->
               ((('a0 -> 'r0) * ('a1 -> 'r1)) -> 'a1 -> 'r1) exp
               -> (('a0 -> 'r0) * ('a1 -> 'r1)) exp
  val nil : unit -> char list exp
  val cons : 'a exp -> 'a list exp -> 'a list exp
  val case : 'a typ -> 'a list exp ->
             (unit -> 'b exp) -> 
             ('a exp -> 'a list exp -> 'b exp) -> 'b exp
  val tif : 'a exp -> 'a exp -> 'b exp -> 'b exp -> 'b exp
  val left : 'b typ -> ('a * 'b) exp -> 'a exp
  val right : 'a typ -> ('a * 'b) exp -> 'b exp
  val zero : unit -> int exp
  val succ : int exp -> int exp
  val sc : 'a exp -> 'a exp
  (* val observe : 'a exp -> 'a obs *)
end
