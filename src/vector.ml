let length l = 
  CCVector.size l

let app l1 l2 = 
  let l = CCVector.copy l1 in 
  CCVector.iter (CCVector.push l) l2; l

let nth_error l n =
  try Some (CCVector.get l n)
  with | _ -> None

let nth n l d = 
  try CCVector.get l n
  with | _ -> d

let rev l = 
  CCVector.rev l

let in_dec eqb x l = 
  CCVector.member ~eq:eqb x l

let vec_eq_dec eqb l1 l2 = 
  CCVector.equal eqb l1 l2

let flatten vv = 
  let result = CCVector.create () in
  CCVector.iter
    (fun inner_vec ->
       CCVector.iter (fun x -> CCVector.push result x) inner_vec
    )
    vv;
  result

let map f l = 
  CCVector.map f l

let fold_left f l init =
  CCVector.fold f init l

let forallb f l = 
  let bs = map f l in 
  fold_left (&&) bs true

let combine l1 l2 =
  CCVector.monoid_product (,) l1 l2

let slice l start len =
  let result = CCVector.create () in
  CCVector.slice_iter v start len (fun x -> CCVector.push result x);
  result

let firstn n l = 
  slice l 0 n

let skipn n l = 
  let len = length l in
  if n < length l then
    slice l n (length l - n)
  else 
    CCVector.create ()
    
let nodup eqb l = 
  let result = CCVector.create () in
  CCVector.iter (fun x -> if not (in_dec eqb x l) then CCVector.push result x) l;
  result

let repeat x n = 
  CCVector.make n x

let rcons l x = 
  let l' = CCVector.copy l in
  CCVector.push l x;
  l

let unrcons l = 
  let len = length l in 
  if len = 0 then None
  else Some (firstn (len-1) l, CCVector.get l (len-1))

(* Very inefficient *)
let set_nth x l n y =
  let len = length l in
  if n < len then
    let l' = CCVector.copy l in 
      CCVector.set l' n y;
      l'
  else
    rcons (app l (repeat x (len - n))) y