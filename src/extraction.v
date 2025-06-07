(** Extraction to OCaml. **)

From Coq Require Extraction.
From Coq Require PArray.

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
  extraction_instance
.

From Coq Require Import
  extraction.ExtrOcamlBasic
  extraction.ExtrOcamlString
  ExtrOCamlInt63
.

Extraction Language OCaml.

(* A bit ugly, but otherwise requires an entire copy of the lookup lemmas for Coq's list types *)
Extract Constant lookup_N => "EfficientExtraction.lookup_N_safe".

(* This could be done better using module types *)
Extract Constant memory_vec.array "'a" => "Parray.t".
Extraction Inline memory_vec.array.

Extract Constant memory_vec.arr_make => "Parray.make".
Extract Constant memory_vec.arr_make_copy => "Parray.make_copy".
Extract Constant memory_vec.arr_get => "Parray.get".
Extract Constant memory_vec.arr_default => "Parray.default".
Extract Constant memory_vec.arr_set => "Parray.set".
Extract Constant memory_vec.arr_length => "Parray.length".
Extract Constant memory_vec.arr_copy => "Parray.copy".

Extraction "extract"
  EfficientExtraction
  run_parse_module
  run_parse_arg
  Extraction_instance
  Monadic_host
  Utility
  .
