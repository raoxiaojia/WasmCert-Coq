type extracted_z = Z.t

let z_of_int x =
  Big_int_Z.big_int_of_int x

let int_of_z z =
  if Big_int_Z.is_int_big_int z then 
    Big_int_Z.int_of_big_int z
else invalid_arg "int_of_z overflow"

(*
let int_of_z : extracted_z -> int = Int64.to_int

let z_of_int: int -> extracted_z = Int64.of_int


let zero = Int64.zero

let one = Int64.one

let two = Int64.add Int64.one Int64.one

let neg = Int64.neg

let max = Int64.max

let add = Int64.add

let pred = Int64.pred

let succ = Int64.succ

let sub = Int64.sub

let mul = Int64.mul

let div = Int64.div

let rem = Int64.rem

let compare = Int64.compare

let divmod x y =
  (Int64.div x y, Int64.rem x y)

let eq = Int64.equal
*)
