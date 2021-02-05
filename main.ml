(* 
 * for i in (number-sequence 1 20) {./search1.run $i $i $i $i}
 * for i in (number-sequence 1 20) {ocamlopt search$i\_naive.ml -o "naive$i"}
 * for i in (number-sequence 1 20) {ocamlopt search$i\_kmp.ml -o "kmp$i"}
 * for i in (number-sequence 1 20) {ocamlopt search$i\_kmp_elim.ml -o "kmp_elim$i"}
 * for i in (number-sequence 1 20) {./naive$i (* i 1000)}
 * for i in (number-sequence 1 20) {./kmp$i (* i 1000)}
 * for i in (number-sequence 1 20) {./kmp_elim$i (* i 1000)}
 *)
*)
*)
*)
open Type
let pat_len = (Sys.argv.(4) |> int_of_string) -1
let char_of_int n = char_of_int (n+65)
module Ex1(I:THOAS.THOAS) = struct
  open I
  let res = tlam (Type.Bool) (fun x -> tor (tt ()) (tf ()))
  let l = List(Char)
  let lt = Arrow(l, Arrow(l, Arrow(l, Arrow(l, Bool))))
  let rt = Arrow(l, Arrow(l, Bool))
  let fg = Pair(lt, rt)
  let loop1 =
    tlam fg (fun fg ->
        let loop, next = left rt fg, right lt fg in
        tlam l (fun pp ->
            tlam l (fun ss ->
                tlam l (fun op ->
                    tlam l (fun os ->
                        case (Char) pp (fun _ -> tt ()) (fun p pp ->
                            case (Char) ss (fun _ -> tf ()) (fun s ss ->
                                tif s p
                                  (tapp (tapp (tapp (tapp loop pp) ss) op) os)
                                  (tapp (tapp next op) os)
                              )
                          )
                      )
                  )
              )
          )
      )
  let next1 =
    tlam fg (fun fg ->
        let loop, next = left rt fg, right lt fg in
        tlam l (fun op ->
            tlam l (fun os ->
                case (Char) os (fun _ -> tf ()) (fun o os ->
                    (tapp (tapp (tapp (tapp loop op) os) op) os)
                  )
              )
          )
      )
  let search1 = fix2 lt 
                     rt
                     loop1 next1
  let lt' = Arrow(l, Arrow(l, Arrow(l, Arrow(l, Arrow(l, Bool)))))
  let rt' = Arrow(l, Arrow(l, Arrow(l, Bool)))
  let fg' = Pair(lt', rt')
  let append =
    fix (l => (l => l))
      (tlam (l => (l => l)) (fun append -> 
        tlam l (fun xs ->
            tlam l (fun ys ->
                case Char xs (fun () -> ys) (fun x xs' ->                     
                    (cons x (tapp (tapp append xs') ys))
                  )
              )
          )
         )
      )
  let tl = tlam l (fun ls ->
                case Char ls (fun () -> nil ()) (fun h tl -> tl)
             )
  let length =
    fix (l => Int)
      (tlam (l => Int) (fun length ->
           tlam l (fun xs ->
               case Char xs (fun () -> zero ())
                 (fun _ xs -> tapp length xs |> succ)
             )
         )
      )
    
  let loop_ob =
    tlam fg' (fun fg ->
        let loop, next = left rt' fg, right lt' fg in
        tlam l (fun pp ->
            tlam l (fun ss ->
                tlam l (fun op ->
                    tlam l (fun bb ->
                        tlam l (fun ob -> 
                            case (Char) pp (fun _ -> tt ()) (fun p pp ->
                                case Char bb (fun () ->
                                    case Char ss (fun () -> tf ()) (fun s ss' ->
                                        tif s p
                                          (tapp (tapp (tapp (tapp (tapp loop pp) ss') op) (nil ())) (tapp (tapp append ob) (cons p (nil ()))))
                                          (tapp (tapp (tapp next op) ss) ob)
                                      )
                                  ) (fun b bb ->
                                    tif b p
                                      (tapp (tapp (tapp (tapp (tapp loop pp) ss) op) bb) ob)
                                      (tapp (tapp (tapp (tapp (tapp loop op) ss) op) (tapp tl ob)) (tapp tl ob))
                                  )
                              )
                          )
                      )
                  )
              )
          )
      )
  let next_ob =
    tlam fg' (fun fg ->
        let loop, _ = left rt' fg, right lt' fg in
        tlam l (fun op ->
            tlam l (fun os ->
                tlam l (fun ob ->
                    case Char ob
                      (fun () ->   tapp (tapp (tapp (tapp (tapp loop op) os) op) (nil ())) (nil ()))
                      (fun o ob -> tapp (tapp (tapp (tapp (tapp loop op) os) op) ob) ob)
                  )
              )
          )
      )
  let search_ob = fix2 lt'
                    rt'
                    loop_ob next_ob

  (* ss = B, ob = AA, pp = [],  op = AAB *)
  (* ss = B, ob =  A  pp = AAB, op = AAB *)
  (* ss = B, ob = [], pp = AB,  op = AAB *)
  (* False *)

  (* ss = B, ob = AA, pp = [],  op = AAB *)
  (* ss = B, ob = AA  pp = AAB, op = AAB *)
  (* ss = B, ob = A   pp =  AB, op = AAB *)
  (* ss = B, ob = [], pp =   B, op = AAB *)
  (* True *)

  let aab =
    cons (char 'a') @@ cons (char 'a') @@ cons (char 'b') @@ nil ()
  let search_aab =
    tlam l (fun s ->
        tapp (tapp (tapp (tapp (left rt search1) aab) s) aab) s |> sc)

  let rec gen_pat n =
    if n > pat_len then cons (char 'B') (nil ())
    else cons (char 'A') @@ gen_pat (n+1)
  let pat = gen_pat 0
  (* let abcdef =
   *   cons (char 'a') @@ cons (char 'b') @@ cons (char 'c') @@ cons (char 'd') @@ cons (char 'e') @@ nil () *)
  let search_abcdef =
    tlam l (fun s ->
        tapp (tapp (tapp (tapp (left rt search1) pat) s) pat) s |> sc)
  let deforestation_abcdef =
    tlam l (fun s ->
        tapp (tapp (tapp (tapp (tapp (left rt' search_ob) pat) s) pat) (nil ())) (nil ()) |> sc)
  let length_append =
    tlam l (fun l1 ->
        tlam l (fun l2 ->
            tapp (length) (tapp (tapp append l1) l2) |> sc
          )
      )
end
let rec gen_string n =
  if n = 0 then ConsU(ChU('B'), NilU) else ConsU(ChU('A'), (gen_string (n-1)))
let rec gen_string n =
  if n = 0 then ['B'] else 'A' :: (gen_string (n-1))

let time : (unit -> 'a) -> 'a * float =
  fun f ->
  let start = Sys.time () in
  let res   = f () in
  let end_  = Sys.time () in
  (res, end_ -. start)
open Printf

let _ =
  let module CSh = C.CObs(C.C) in
  let module M1' = Ex1(CSh) in
  let module M2' = Ex1(Supercompiler.PSC(CSh)) in

  let module SCR = Supercompiler.PSC(CSh) in
  (* let naive_code = CSh.observe M1'.search_abcdef in
   * let kmp_code = SCR.observe M2'.search_abcdef in *)
  (* let module CSh = C.CObs(C.C) in
   * let module DCSh= Deforestation.DFE(CSh) in
   * let module M1' = Ex1(CSh) in
   * let module M2' = Ex1(DCSh) in *)
  let module USh = UnType.UnTypeObs(UnType.UnType) in
  let module USCR = Deforestation.DFE(USh) in
  (* let module USCR = Deforestation.DFE(USh) in *)
  let module USCER = SupercompilerE.PSCE(USh) in
  let module M4 = Ex1(USCER) in  
  let module MC = Ex1(CSh) in
  let length_append = USCER.observe (M4.length_append) in
  (* Format.printf "%s@." (ml_termU () length_append); *)
  (* Format.printf "length_append = %a" Print_code.print_code length_append; *)
  let module M2 = Ex1(SupercompilerE.PSCE(USh)) in
  let module M3 = Ex1(Deforestation.DFE(USh)) in
  let module M1 = Ex1(USh) in
  let prev = Sys.time() in
  (* for i = 1 to 10 do
   *   ignore (USCR.observe M2.search_abcdef)
   * done; *)
  let now = Sys.time() in
  (* let _ = Format.printf "%f@." (now -. prev) in *)
  (* let kmp = USCR.observe M2.search_abcdef in
   * let naive = USh.observe M1.search_abcdef in *)
  let kmp = USCR.observe M3.deforestation_abcdef in
  let naive = USh.observe M1.deforestation_abcdef in
  (* let kmp_code : (char list -> bool) code = DCSh.observe M2'.deforestation_abcdef in *)
  (* let naive = USh.observe M1.search_abcdef in
   * let prev = Sys.time() in
   * 
   * let now = Sys.time() in
   * let _ = Format.printf "%f@." (now -. prev) in *)
  (* let _ = Format.printf "let kmp = @[<hov 2>%a@]@." Print_code.print_code kmp_code in
   * let _ = Format.printf "let naive = @[<hov 2>%a@]@." Print_code.print_code naive_code in *)
  let length = (int_of_string Sys.argv.(3)) in
  let hop = (int_of_string Sys.argv.(2)) in
  let start = (int_of_string Sys.argv.(1)) in
  (* let cal1 str () =
   *   let rec loop n =
   *     if n > 0 then
   *       let _ = Runcode.run naive str in
   *       loop (n-1)
   *     else Runcode.run naive str
   *   in
   *   loop 0
   * in
   * (\* let cal2 str () = Runcode.run kmp str in *\)
   * let cal2 str () =
   *     let rec loop n =
   *     if n > 0 then
   *       let _ = Runcode.run kmp str in
   *       loop (n-1)
   *     else Runcode.run kmp str
   *   in
   *   loop 0
   * in *)
  (* let cal1 str () = Eval.eval 0 0 [] [] (App(naive, str)) in
   * let cal2 str () = Eval.eval 0 0 [] [] (App(kmp, str)) in
   * let cal3 str () = Eval.eval 0 0 [] [] (App(kmp_elim, str)) in   *)
  let filename = "search" ^ Sys.argv.(4) in
  (* let _ = Format.printf "%s@." Sys.argv.(4) in *)
  let file_naive = open_out (filename ^ "_naive.ml") in
  let file_kmp = open_out (filename ^ "_kmp.ml") in
  (* let file_kmp_elim = open_out (filename ^ "_kmp_elim.ml") in *)
  (* let str = gen_string length in *)
  let head = "let rec gen_string n ="
             ^ "   if n = 0 then ['B'] else 'A' :: (gen_string (n-1))\n"               
             ^ "let str = gen_string (int_of_string Sys.argv.(1))\n"
             
  in 
  let tail = "let time =
              let start = Sys.time () in
              for i = 1 to 1000 do ignore (f ()) done;
              let end_  = Sys.time () in
              Format.printf \"%f\\n\" (end_ -. start)";
  in 
  fprintf file_naive "%s" head;
  fprintf file_kmp "%s" head;
  (* fprintf file_kmp_elim "%s "head;   *)
  fprintf file_naive
    "let f () = (%s) str\n" (ml_termU () naive);
  fprintf file_kmp
    "let f () = (%s) str\n" (ml_termU () kmp);
  (* fprintf file_kmp_elim
   *   "let f () = (%s) str\n" (ml_termU () kmp_elim); *)
  fprintf file_naive "%s" tail;
  fprintf file_kmp "%s" tail;
  (* fprintf file_kmp_elim "%s" tail; *)

                                           
  (* let rec inc n =
   *   if n <= length then 
   *     let string = gen_string n in
   *     let (r1, t1) = cal1 string |> time in
   *     let (r2, t2) = cal2 string |> time in
   *     let (r3, t3) = cal3 string |> time in
   *     if r1 = r2 && r2 = r3 then
   *       (\* let _ = fprintf file "%f, %f\n" t1 t2 in *\)
   *       let _ = printf "%f, %f, %f\n" t1 t2 t3 in
   *       inc (n+hop)
   *     else failwith "return"
   *   else () *)
  (* flush file_naive; flush file_kmp; flush file_kmp_elim; *)
  flush file_naive; flush file_kmp;
  (* close_out file_naive; close_out file_kmp; close_out file_kmp_elim; *)
  close_out file_naive; close_out file_kmp;
  let module RSh = R.RObs(R.R) in
  let module M1 = Ex1(RSh) in
  let module M2 = Ex1(Deforestation.DFE(RSh)) in  
  let module DFR = Deforestation.DFE(RSh) in
  let naive = RSh.observe M1.deforestation_abcdef in
  let kmp = DFR.observe M2.deforestation_abcdef in
  (* let module M2 = Ex1(SupercompilerE.PSCE(RSh)) in  
   * let module SCR = SupercompilerE.PSCE(RSh) in
   * let naive = RSh.observe M1.search_abcdef in
   * let kmp = SCR.observe M2.search_abcdef in *)
  
  let rec inc n =
    if n <= length then 
      let string = gen_string n in
      let count_kmp, count_naive = ref 0, ref 0 in  
      let _ = naive count_naive string in
      let _ = kmp count_kmp string in
      Format.printf "%d, %d@." !count_naive !count_kmp;
      inc (n+hop)
    else ()
  in
  let _ = inc start in ()

  
                                                              
(* let _ =
 *   let module SCSh = Supercompiler.PSC(TDBObs(TDeBruijn)) in
 *   let module RSh = R.RObs(R.R) in
 *   let module M1 = Ex1(RSh) in
 *   (\* let module M2 = Ex1(Supercompiler.PSC(RSh)) in *\)  
 *   let module M = Ex1(SCSh) in
 *   (\* let _ = SCSh.observe M.search_b |> Format.printf "search_b = %a@." TDB.p_term in *\)
 *   let module SCR = Supercompiler.PSC(RSh) in
 *   let string = gen_string (int_of_string Sys.argv.(1)) in
 *   let naive = RSh.observe M1.search_abc in
 *   (\* let kmp = SCR.observe M2.search_b in *\)
 *     
 *   let cal1 () = naive string in
 *   (\* let cal2 () = kmp string in *\)
 *   let (_, t1) = time cal1 in
 *   (\* let (_, t2) = time cal2 in *\)
 *   let t2 = 0.0 in
 *   (\* let casetest () = RSh.observe M1.head in
 *    * let (_, t3)  = time casetest in
 *    * let appendtest () = RSh.observe M1.append string string in
 *    * let (_, t4)  = time appendtest in *\)
 *   
 *   Format.printf "naive = %f, kmp = %f@." t1 t2 *)
  
(*                                                              
let f w =
  x + y + z + (f w) (* 4 => x, y, z, w, f0, x', y', z', w', 9 => x, y, z, w, f0, x', y', z', w', f1, x'', y'', z'', w'' f0' x''', y''', z''', w''' => *)

before
g z = g (y+z) 
f x = 
 g y

after
f x =
 let rec g0 x' y' = 
   let rec g1 x' y' g0' x'' y'' =
    g (y+y)
 in g0 x y
*)
            (* 
kmp = \0(Fix(\_0\1case 1  
                [] -> F  
                2:3 -> if  2=A 
                       then (Fix(\_1\4case 4  
                                     [] -> F  
                                     5:6 -> if  5=B 
                                            then (Fix(\_2\7T) 6)  
                                            else ((Fix(\_2\7\8((Fix(\_3\9\10if  10=A 
                                                                   then _1  
                                                                   ((Fix(\\\(_0 11)) 9) 10)) 7) 8)) 6) 5)) 3)  
                                                                   else 
                       else ((Fix(\\\(_0 4)) 3) 2)) 0)

 *)
