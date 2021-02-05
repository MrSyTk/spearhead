open Type
open TDB
open Shift
open LibTDB
module SC(F : THOAS.THOAS) = struct
  module Lib = DBLib(F)
  module X = struct
    include Lib.X
  end
  open X
  module IDelta = struct
    include Lib.IDelta
    let sc body  =
      match body with
      | Term({contents = body}) ->
         let c : type g d. (g, d) ctx -> d funs -> (g, d, 'a) tTerm =
           fun i funs ->
           (* let _ = Format.printf "sc : %a@." p_term (body i funs) in *)
           match funs with EMPTY ->
             let unifier = ctx_to_unifier i in
             let memo = SC.ctx_to_memo i in           
             SC.sc true true unifier memo i FNil (body i funs) 
         in 
         Term({contents = c})          
      | _ -> failwith "parse sc in SC"
  end
end
                               
module PSCE(F : SYMOBS) = struct
  module OptM = SC(F)
  include SYMT(OptM.X)(F)
  include OptM.IDelta
end


