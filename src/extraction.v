(** Extraction to OCaml. **)

From Coq Require Extraction.
From Wasm Require Import
  efficient_extraction
  datatypes_properties
  binary_format_parser
  text_format_parser
  instantiation_func
  interpreter_ctx
  type_checker
  pp
  host
  simd_execute
  extraction_instance
.

Require Import compcert.lib.Integers.
Require Import ZArith NArith.

From Coq Require PArray.
From Coq Require Import
  extraction.ExtrOcamlBasic
  extraction.ExtrOcamlNativeString
  extraction.ExtrOcamlZBigInt
.

Extraction Language OCaml.



(*
(* Overwrite the extraction target of binary integers due to a name clash with CompCert's `int` *)
Extract Inductive positive => "Extracted_z.extracted_z"
 [ "(fun x -> Extracted_z.succ (Extracted_z.add x x))"
   "(fun x -> Extracted_z.add x x)" "Extracted_z.one" ]
 "(fun f2p1 f2p f1 p -> if Extracted_z.compare p Extracted_z.one <= 0 then f1 () else let (q,r) = Extracted_z.divmod p Extracted_z.two in if Extracted_z.eq r Extracted_z.zero then f2p q else f2p1 q)".

Extract Inductive Z => "Extracted_z.extracted_z"
 [ "Extracted_z.zero" "" "Extracted_z.neg" ]
 "(fun fO fp fn z -> let s = Extracted_z.compare z Extracted_z.zero in if s = 0 then fO () else if s > 0 then fp z else fn (Extracted_z.neg z))".

Extract Inductive N => "Extracted_z.extracted_z"
 [ "Extracted_z.zero" "" ]
 "(fun fO fp n -> if Extracted_z.compare n Extracted_z.zero <= 0 then fO () else fp n)".

Extract Constant Pos.succ => "Extracted_z.succ".
Extract Constant Pos.pred => "fun x -> Extracted_z.max (Extracted_z.pred x) Extracted_z.one".
Extract Constant Pos.add => "Extracted_z.add".
Extract Constant Pos.sub => "fun x y -> Extracted_z.max (Extracted_z.sub x y) Extracted_z.one".
Extract Constant Pos.mul => "Extracted_z.mul".
Extract Constant Pos.max => "Extracted_z.max".
Extract Constant Pos.compare => "fun x y -> let s = Extracted_z.compare x y in if s=0 then Eq else if s<0 then Lt else Gt".

Extract Constant N.succ => "Extracted_z.succ".
Extract Constant N.pred => "fun x -> Extracted_z.max (Extracted_z.pred x) Extracted_z.zero".
Extract Constant N.add => "Extracted_z.add".
Extract Constant N.sub => "fun x y -> Extracted_z.max (Extracted_z.sub x y) Extracted_z.zero".
Extract Constant N.mul => "Extracted_z.mul".
Extract Constant N.div => "fun x y -> if Extracted_z.eq y Extracted_z.zero then x else Extracted_z.div x y".
Extract Constant N.max => "Extracted_z.max".
Extract Constant N.modulo => "fun x y -> if Extracted_z.eq y Extracted_z.zero then x else Extracted_z.rem x y".
Extract Constant N.compare => "fun x y -> let s = Extracted_z.compare x y in if s=0 then Eq else if s<0 then Lt else Gt".

Extract Constant Z.succ => "Extracted_z.succ".
Extract Constant Z.pred => "Extracted_z.pred".
Extract Constant Z.add => "Extracted_z.add".
Extract Constant Z.sub => "Extracted_z.sub".
Extract Constant Z.mul => "Extracted_z.mul".
Extract Constant Z.div => "fun x y -> if Extracted_z.eq y Extracted_z.zero then x else Extracted_z.div x y".
Extract Constant Z.max => "Extracted_z.max".
Extract Constant Z.opp => "Extracted_z.neg".
Extract Constant Z.compare => "fun x y -> let s = Extracted_z.compare x y in if s=0 then Eq else if s<0 then Lt else Gt".
*)


(* A bit ugly, but otherwise requires an entire copy of the lookup lemmas for Coq's list types *)
Extract Constant lookup_N => "EfficientExtraction.lookup_N_safe".

(* This could be done better using module types *)
Extract Constant memory_vec.array "'a" => "Parray_shim.t".
Extraction Inline memory_vec.array.

(* Requires some custom rerouting *)

Extract Constant memory_vec.arr_make => "Parray_shim.make".
Extract Constant memory_vec.arr_make_copy => "Parray_shim.make_copy".
Extract Constant memory_vec.arr_get => "Parray_shim.get".
Extract Constant memory_vec.arr_default => "Parray_shim.default".
Extract Constant memory_vec.arr_set => "Parray_shim.set".
Extract Constant memory_vec.arr_set_gen => "Parray_shim.set_gen".
Extract Constant memory_vec.arr_length => "Parray_shim.length".
Extract Constant memory_vec.arr_copy => "Parray_shim.copy".

Extract Constant SIMD_ops.app_vunop_str => "SIMD_ops.app_vunop_str".
Extract Constant SIMD_ops.app_vbinop_str => "SIMD_ops.app_vbinop_str".
Extract Constant SIMD_ops.app_vternop_str => "SIMD_ops.app_vternop_str".
Extract Constant SIMD_ops.app_vtestop_str => "SIMD_ops.app_vtestop_str".
Extract Constant SIMD_ops.app_vshiftop_str => "SIMD_ops.app_vshiftop_str".

Extraction "extract"
  EfficientExtraction
  run_parse_module_str
  run_parse_arg
  Extraction_instance
  Monadic_host
  Utility
  .
