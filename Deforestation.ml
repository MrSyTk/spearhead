open Type
open TDB
open Shift
open LibTDB
module Deforestation(F : THOAS.THOAS) = struct
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
           match funs with EMPTY ->
             let unifier = ctx_to_unifier i in
             let memo = SC.ctx_to_memo i in
             let out = 
               SC.sc true false unifier memo i FNil (body i funs)
             in (* Format.printf "out = %a@." p_term out; *)
                out
         in
         Term({contents = c})           
      | _ -> failwith "parse sc in SC"
  end
end
                               
module DFE(F : SYMOBS) = struct
  module OptM = Deforestation(F)
  include SYMT(OptM.X)(F)
  include OptM.IDelta
end
