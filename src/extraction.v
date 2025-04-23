(** Extraction to OCaml. **)
(* (C) M. Bodin, J. Pichon - see LICENSE.txt *)

From Coq Require Extraction.
From Coq Require Import List ZArith.

From Wasm Require Import
  datatypes_properties
  binary_format_parser
  text_format_parser
  instantiation_func
  interpreter_ctx
  type_checker
  pp
  host
  wast
.


From Coq Require Import
  extraction.ExtrOcamlString
  ExtrOcamlNatBigInt
.

(* Extracting lists to (hopefully) efficient ocaml vectors using containers *)
Extract Inductive list => "CCVector.vector"
  [
    "(CCVector.create ())"
    "CCVector.push"].

Extract Constant length => "Vector.length".
Extract Constant app => "Vector.app".
Extract Constant lookup_N => "Vector.nth_error".
Extract Constant nth_error => "Vector.nth_error".
Extract Constant nth => "Vector.nth".
Extract Constant rev => "Vector.rev".
Extract Constant in_dec => "Vector.in_dec".
Extract Constant list_eq_dec => "Vector.vec_eq_dec".
Extract Constant concat => "Vector.flatten".
Extract Constant map => "Vector.map".
Extract Constant fold_left => "Vector.fold_left".
Extract Constant forallb => "Vector.forallb".
Extract Constant combine => "Vector.combine".
Extract Constant firstn => "Vector.firstn".
Extract Constant skipn => "Vector.skipn".
Extract Constant nodup => "Vector.nodup".
Extract Constant repeat => "Vector.repeat".

(* now dealing with ssreflect functions *)
Extract Constant seq.size => "Vector.length".
Extract Constant seq.cat => "Vector.app".
Extract Constant seq.rcons => "Vector.rcons".
Extract Constant unrcons => "Vector.unrcons".
Extract Constant seq.set_nth => "Vector.set_nth".

Extraction Language OCaml.

Extraction "extract"
  run_parse_module
  run_parse_arg
  Instantiation_func_extract
  Interpreter_ctx_extract
  Wast_interface
  PP
  DummyHost
  empty_frame
  .
