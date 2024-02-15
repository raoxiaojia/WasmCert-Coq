(** Pretty-printer **)

Require Import Coq.Strings.String.
From compcert Require Import Floats.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import Coq.Init.Decimal.
Require Import bytes_pp datatypes interpreter_ppi.
Require Import BinNat.
Require Import ansi list_extra.

Open Scope string_scope.

Section Host.

Variable host_function: eqType.
  
Variable show_host_function : host_function -> string.


Definition newline_char : Ascii.ascii := Ascii.ascii_of_byte Byte.x0a.

Definition newline : string := String newline_char EmptyString.

(** Describe an indentation level. **)
Definition indentation := nat.

Fixpoint indent (i : indentation) (s : string) : string :=
  match i with
  | 0 => s
  | S i' => "  " ++ indent i' s
  end.

Definition type_style := FG_cyan.

Definition pp_value_type (vt : value_type) : string :=
  let s :=
    match vt with
    | T_i32 => "i32"
    | T_i64 => "i64"
    | T_f32 => "f32"
    | T_f64 => "f64"
    end in
  with_fg type_style s.

Definition pp_value_types (vts : list value_type) : string :=
  "[" ++ String.concat ", " (List.map pp_value_type vts) ++ "]".

Definition pp_function_type (tf : function_type) : string :=
  let '(Tf ts1 ts2) := tf in
  pp_value_types ts1 ++ " -> " ++ pp_value_types ts2.

Definition pp_block_tf (tf : function_type) : string :=
  match tf with
  | Tf nil nil => ""
  | Tf nil (cons vt nil) => " " ++ pp_value_type vt
  | Tf nil _ => " error!"
  | Tf _ _ => " error!"
  end.

Fixpoint string_of_uint (i : uint) : string :=
  match i with
  | Nil => ""
  | D0 i' => "0" ++ string_of_uint i'
  | D1 i' => "1" ++ string_of_uint i'
  | D2 i' => "2" ++ string_of_uint i'
  | D3 i' => "3" ++ string_of_uint i'
  | D4 i' => "4" ++ string_of_uint i'
  | D5 i' => "5" ++ string_of_uint i'
  | D6 i' => "6" ++ string_of_uint i'
  | D7 i' => "7" ++ string_of_uint i'
  | D8 i' => "8" ++ string_of_uint i'
  | D9 i' => "9" ++ string_of_uint i'
  end.

Definition pp_immediate (i : immediate) : string :=
  (* TODO: it's not clear that's the right way to print it, but hey *)
  string_of_uint (Nat.to_uint i).

Definition pp_N (n: N) : string :=
  string_of_uint (N.to_uint n).

Definition pp_positive (p: positive) : string :=
  string_of_uint (BinPos.Pos.to_uint p).

Definition pp_Z (z: Z) : string :=
  match z with
  | Z0 => "0"
  | Zpos p => pp_positive p
  | Zneg p => "-" ++ pp_positive p
  end.

Definition pp_i32 i :=
  pp_Z (Wasm_int.Int32.signed i).

Definition pp_i64 i :=
  pp_Z (Wasm_int.Int64.signed i).

(* TODO: all this printing of floats business is highly dubious,
   and completely untested *)
Fixpoint bool_list_of_pos (acc : list bool) (p : BinNums.positive) :=
  match p with
  | BinNums.xI p' => bool_list_of_pos (true :: acc) p'
  | BinNums.xO p' => bool_list_of_pos (false :: acc) p'
  | BinNums.xH => true :: acc
  end.

Open Scope list.

Fixpoint pp_bools (acc : list Byte.byte) (bools : list bool) : list Byte.byte :=
  (* TODO: I am ashamed I wrote this *)
  match bools with
  | nil => acc
  | b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: bools' =>
    pp_bools (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (b7, b8))))))) :: acc) bools'
  | b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::  nil =>
    Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (b7, false))))))) :: acc
  | b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: nil =>
    Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (false, false))))))) :: acc
  | b1 :: b2 :: b3 :: b4 :: b5 :: nil =>
    Byte.of_bits (b1, (b2, (b3, (b4, (b5, (false, (false, false))))))) :: acc
  | b1 :: b2 :: b3 :: b4 :: nil =>
    Byte.of_bits (b1, (b2, (b3, (b4, (false, (false, (false, false))))))) :: acc
  | b1 :: b2 :: b3 :: nil =>
    Byte.of_bits (b1, (b2, (b3, (false, (false, (false, (false, false))))))) :: acc
  | b1 :: b2 :: nil =>
    Byte.of_bits (b1, (b2, (false, (false, (false, (false, (false, false))))))) :: acc
  | b1 :: nil =>
    Byte.of_bits (b1, (false, (false, (false, (false, (false, (false, false))))))) :: acc
  end.

Definition pp_f32 (f : float32) : string :=
  match BinIntDef.Z.to_N ((Float32.to_bits f).(Integers.Int.intval)) with
  | BinNums.N0 => "0"
  | BinNums.Npos p =>
    bytes_pp.hex_small_no_prefix_of_bytes_compact (pp_bools nil (List.rev (bool_list_of_pos nil p)))
  end.

Definition pp_f64 (f : float) : string :=
  match BinIntDef.Z.to_N ((Float.to_bits f).(Integers.Int64.intval)) with
  | BinNums.N0 => "0"
  | BinNums.Npos p =>
    bytes_pp.hex_small_no_prefix_of_bytes_compact (pp_bools nil (List.rev (bool_list_of_pos nil p)))
  end.

Definition pp_value (v : value) : string :=
  match v with
  | VAL_int32 i => pp_value_type T_i32 ++ ".const " ++ with_fg FG_green (pp_i32 i) ++ newline
  | VAL_int64 i => pp_value_type T_i64 ++ ".const " ++ with_fg FG_green (pp_i64 i) ++ newline
  | VAL_float32 f => pp_value_type T_f32 ++ ".const " ++ with_fg FG_green (pp_f32 f) ++ newline
  | VAL_float64 f => pp_value_type T_f64 ++ ".const " ++ with_fg FG_green (pp_f64 f) ++ newline
  end.

Definition pp_values (vs : list value) : string :=
  String.concat " " (List.map pp_value vs).

Definition pp_values_hint_empty (vs : list value) : string :=
  match vs with
  | nil => "(empty)"
  | _ => pp_values vs
  end.

Definition pp_unary_op_i (uoi : unop_i) : string :=
  match uoi with
  | UOI_clz => "clz"
  | UOI_ctz => "ctz"
  | UOI_popcnt => "popcnt"
  end.

Definition pp_unary_op_f (uof : unop_f) : string :=
  match uof with
  | UOF_neg => "neg"
  | UOF_abs => "abs"
  | UOF_ceil => "ceil"
  | UOF_floor => "floor"
  | UOF_trunc => "trunc"
  | UOF_nearest => "nearest"
  | UOF_sqrt => "sqrt"
  end.

Definition pp_sx (s : sx) : string :=
  match s with
  | SX_U => "u"
  | SX_S => "s"
  end.

Definition pp_binary_op_i (boi : binop_i) : string :=
  match boi with
  | BOI_add => "add"
  | BOI_sub => "sub"
  | BOI_mul => "mul"
  | BOI_div s => "div_" ++ pp_sx s
  | BOI_rem s => "rem_" ++ pp_sx s
  | BOI_and => "and"
  | BOI_or => "or"
  | BOI_xor => "xor"
  | BOI_shl => "shl"
  | BOI_shr s => "shr_" ++ pp_sx s
  | BOI_rotl => "rotl"
  | BOI_rotr => "rotr"
  end.

Definition pp_binary_op_f (bof : binop_f) : string :=
  match bof with
  | BOF_add => "add"
  | BOF_sub => "sub"
  | BOF_mul => "mul"
  | BOF_div => "div"
  | BOF_min => "min"
  | BOF_max => "max"
  | BOF_copysign => "copysign"
  end.

Definition pp_rel_op_i (roi : relop_i) : string :=
  match roi with
  | ROI_eq => "eq"
  | ROI_ne => "ne"
  | ROI_lt s => "lt_" ++ pp_sx s
  | ROI_gt s => "gt_" ++ pp_sx s
  | ROI_le s => "le_" ++ pp_sx s
  | ROI_ge s => "ge_" ++ pp_sx s
  end.

Definition pp_rel_op_f (rof : relop_f) : string :=
  match rof with
  | ROF_eq => "eq"
  | ROF_ne => "ne"
  | ROF_lt => "lt"
  | ROF_gt => "gt"
  | ROF_le => "ne"
  | ROF_ge => "ge"
  end.

(* The alignment exponent is the exponent in both the spec and the binary, but needs to be the power in the text format. *)
Definition pp_memarg (a: alignment_exponent) (o: static_offset) : string :=
  "offset=" ++ pp_N o ++ " " ++ "align=" ++ pp_N (N.shiftl 1 a).

Definition pp_packing (p : packed_type) :=
  match p with
  | Tp_i8 => "8"
  | Tp_i16 => "16"
  | Tp_i32 => "32"
  end.

Definition pp_ps (ps : packed_type * sx) : string :=
  let '(p, s) := ps in
  pp_packing p ++ "_" ++ pp_sx s.

Definition be_style := FG_magenta.

Fixpoint pp_basic_instruction (i : indentation) (be : basic_instruction) : string :=
  let pp_basic_instructions bes i :=
    String.concat "" (List.map (pp_basic_instruction (S i)) bes) in
  match be with
  | BI_unreachable => indent i (with_fg be_style "unreachable" ++ newline)
  | BI_nop => indent i (with_fg be_style "nop" ++ newline)
  | BI_drop => indent i (with_fg be_style "drop" ++ newline)
  | BI_select => indent i (with_fg be_style "select" ++ newline)
  | BI_block tf bes =>
    indent i (with_fg be_style "block" ++ with_fg type_style (pp_block_tf tf) ++ newline)
    ++ pp_basic_instructions bes (S i)
    ++ indent i (with_fg be_style "end" ++ newline)
  | BI_loop tf bes =>
    indent i (with_fg be_style "loop" ++ with_fg type_style (pp_block_tf tf) ++ newline)
    ++ pp_basic_instructions bes (S i)
    ++ indent i (with_fg be_style "end" ++ newline)
  | BI_if tf bes nil =>
    indent i (with_fg be_style "if" ++ with_fg type_style (pp_block_tf tf) ++ newline)
    ++ pp_basic_instructions bes (S i)
    ++ indent i (with_fg be_style "end" ++ newline)
  | BI_if tf bes1 bes2 =>
    indent i (with_fg be_style "if" ++ with_fg type_style (pp_block_tf tf) ++ newline)
    ++ pp_basic_instructions bes1 (S i)
    ++ indent i (with_fg be_style "else" ++ newline)
    ++ pp_basic_instructions bes2 (S i)
    ++ indent i (with_fg be_style "end" ++ newline)
  | BI_br x =>
    indent i (with_fg be_style "br " ++ pp_immediate x ++ newline)
  | BI_br_if x =>
    indent i (with_fg be_style "br_if " ++ pp_immediate x ++ newline)
  | BI_br_table is_ i =>
    indent i (with_fg be_style "br_table " ++ String.concat " " (List.map pp_immediate is_) ++ " " ++ pp_immediate i ++ newline)
  | BI_return =>
    indent i (with_fg be_style "return" ++ newline)
  | BI_call x =>
    indent i (with_fg be_style "call " ++ pp_immediate x ++ newline)
  | BI_call_indirect x =>
    indent i (with_fg be_style "call_indirect " ++ pp_immediate x ++ newline)
  | BI_get_local x =>
    indent i (with_fg be_style "local.get " ++ pp_immediate x ++ newline)
  | BI_set_local x =>
    indent i (with_fg be_style "local.set " ++ pp_immediate x ++ newline)
  | BI_tee_local x =>
    indent i (with_fg be_style "local.tee " ++ pp_immediate x ++ newline)
  | BI_get_global x =>
    indent i (with_fg be_style "global.get " ++ pp_immediate x ++ newline)
  | BI_set_global x =>
    indent i (with_fg be_style "global.set " ++ pp_immediate x ++ newline)
  | BI_load vt None a o =>
    indent i (pp_value_type vt ++ ".load " ++ pp_memarg a o ++ newline)
  | BI_load vt (Some ps) a o =>
    indent i (pp_value_type vt ++ ".load" ++ pp_ps ps ++ " " ++ pp_memarg a o ++ newline)
  | BI_store vt None a o =>
    indent i (pp_value_type vt ++ ".store " ++ pp_memarg a o ++ newline)
  | BI_store vt (Some p) a o =>
    indent i (pp_value_type vt ++ ".store" ++ pp_packing p ++ " " ++ pp_memarg a o ++ newline)
  | BI_current_memory =>
    indent i (with_fg be_style "memory.size" ++ newline ++ newline)
  | BI_grow_memory =>
    indent i (with_fg be_style "memory.grow" ++ newline)
  | BI_const v =>
    indent i (pp_value v)
  | BI_unop vt (Unop_i uoi) =>
    indent i (pp_value_type vt ++ "." ++ pp_unary_op_i uoi ++ newline)
  | BI_unop vt (Unop_f uof) =>
    indent i (pp_value_type vt ++ "." ++ pp_unary_op_f uof ++ newline)
  | BI_binop vt (Binop_i boi) =>
    indent i (pp_value_type vt ++ "." ++ pp_binary_op_i boi ++ newline)
  | BI_binop vt (Binop_f bof) =>
    indent i (pp_value_type vt ++ "." ++ pp_binary_op_f bof ++ newline)
  | BI_testop vt Eqz =>
    indent i (pp_value_type vt ++ ".eqz" ++ newline)
  | BI_relop vt (Relop_i roi) =>
    indent i (pp_value_type vt ++ "." ++ pp_rel_op_i roi ++ newline)
  | BI_relop vt (Relop_f rof) =>
    indent i (pp_value_type vt ++ "." ++ pp_rel_op_f rof ++ newline)
  | BI_cvtop vt1 cvtop vt2 sxo => "?" ++ newline (* TODO: ??? *)
  end.

Definition pp_basic_instructions n bes :=
  String.concat "" (List.map (pp_basic_instruction n) bes).

Definition pp_function_closure (n : indentation) (fc : function_closure host_function) : string :=
  match fc with
  | FC_func_native i ft vs bes =>
    (* TODO: show instance? *)
    indent n ("native " ++ pp_function_type ft ++ newline) ++
    indent n ("value types " ++ pp_value_types vs ++ newline) ++
    indent n ("body" ++ newline) ++
    pp_basic_instructions (n.+1) bes ++
    indent n ("end native" ++ newline)
  | FC_func_host ft h =>
    indent n ("host " ++ show_host_function h
              ++ " : " ++ pp_function_type ft ++ newline)
  end.

Definition string_of_nat (n : nat) : string :=
  string_of_uint (Nat.to_uint (BinNatDef.N.of_nat n)).

Definition ae_style := FG_blue.

Fixpoint pp_administrative_instruction (n : indentation) (e : administrative_instruction) : string :=
  let pp_administrative_instructions (n : nat) (es : list administrative_instruction) : string :=
    String.concat "" (List.map (pp_administrative_instruction n) es) in
  match e with
  | AI_basic be => pp_basic_instruction n be
  | AI_trap => indent n (with_fg ae_style "trap" ++ newline)
  | AI_invoke a =>
    indent n (with_fg ae_style "invoke " ++ string_of_nat a ++ newline)
  (*    pp_function_closure (n.+1) fc*)
           
  | AI_label k es1 es2 =>
    indent n (with_fg ae_style "label " ++ string_of_nat k ++ newline) ++
    String.concat "" (List.map (pp_administrative_instruction (n.+1)) es1) ++
    indent n (with_fg ae_style "label_cont" ++ newline) ++
    String.concat "" (List.map (pp_administrative_instruction (n.+1)) es2) ++
    indent n (with_fg ae_style "end label" ++ newline)
  | AI_local n f es =>
    indent n (with_fg ae_style "local " ++ string_of_nat n ++ newline) ++
    (* TODO: inst? *)
    indent n (with_fg ae_style "with values " ++ pp_values_hint_empty f.(f_locs) ++ newline) ++
    pp_administrative_instructions (n.+1) es ++
    indent n (with_fg ae_style "end local" ++ newline)
  end.

Definition pp_administrative_instructions (n : nat) (es : list administrative_instruction) : string :=
  String.concat "" (List.map (pp_administrative_instruction n) es).

Definition pp_mutability (m : mutability) : string :=
  match m with
  | MUT_immut => "const"
  | MUT_mut => "var"
  end.

Definition pp_global (g : global) : string :=
  pp_mutability g.(g_mut) ++ " " ++ pp_value g.(g_val).

Definition pp_globals (n : indentation) (gs : list global) : string :=
  String.concat "" (mapi (fun i g => indent n (string_of_nat i ++ ": " ++ pp_global g ++ newline)) gs).

Definition pp_memories (n : indentation) (ms : list memory) : string :=
  String.concat "" (mapi (fun i m => indent n (string_of_nat i ++ ": " ++ "TODO: memory" ++ newline)) ms).

Definition pp_funcelem (elem: funcelem) : string :=
  match elem with
  | Some n => string_of_nat n
  | None => "none"
  end.

Definition pp_table (n: indentation) (t : tableinst) : string :=
  String.concat "" (mapi (fun i elem => indent n (string_of_nat i ++ ": " ++ pp_funcelem elem ++ newline)) t.(table_data)).

Definition pp_tables (n : indentation) (ms : list tableinst) : string :=
  String.concat "" (mapi (fun i t => indent n (string_of_nat i ++ ": " ++ pp_table n t)) ms).

Definition pp_store (n : indentation) (s : store_record host_function) : string :=
  indent n ("globals" ++ newline) ++
  pp_globals (n.+1) s.(s_globals) ++
  indent n ("memories" ++ newline) ++
  pp_memories (n.+1) s.(s_mems) ++
  indent n ("tables" ++ newline) ++
  pp_tables (n.+1) s.(s_tables).

(* Typing terms *)

Fixpoint pp_bet {C es tf} (p: be_typing C es tf) (n: indentation) : string :=
  indent n (
  match p with
  | bet_const _ _ => "const"
  | bet_unop _ _ _ _ => "unop"
  | bet_binop _ _ _ _ => "binop"
  | bet_testop _ _ _ _ => "testop"
  | bet_relop _ _ _ _ => "relop"
  | bet_convert _ _ _ _ _ => "convert"
  | bet_reinterpret _ _ _ _ _ => "reinterpret"
  | bet_unreachable _ _ _ => "unreachable"
  | bet_nop _ => "nop"
  | bet_drop _ _ => "drop"
  | bet_select _ _ => "select"
  | bet_block _ _ _ _ _ => "block"
  | bet_loop _ _ _ _ _ => "loop"
  | bet_if_wasm _ _ _ _ _ _ _ => "if"
  | bet_br _ _ _ _ _ _ _ => "br"
  | bet_br_if _ _ _ _ _ => "br_if"
  | bet_br_table _ _ _ _ _ _ _ => "br_table"
  | bet_return _ _ _ _ _ => "return"
  | bet_call _ _ _ _ _ => "call"
  | bet_call_indirect _ _ _ _ _ _ _ => "call_indirect"
  | bet_get_local _ _ _ _ _ => "get_local"
  | bet_set_local _ _ _ _ _ => "set_local"
  | bet_tee_local _ _ _ _ _ => "tee_local"
  | bet_get_global _ _ _ _ _ => "get_global"
  | bet_set_global _ _ _ _ _ _ _ _ => "set_global"
  | bet_load _ _ _ _ _ _ _ => "load"
  | bet_store _ _ _ _ _ _ _ => "store"
  | bet_current_memory _ _ => "current_memory"
  | bet_grow_memory _ _ => "grow_memory"
  | bet_empty _ => "empty"
  | bet_composition _ _ e _ _ _ pes pe => "be_composition with tail " ++ pp_basic_instruction 0 e ++ pp_bet pes (S n) ++ newline ++ pp_bet pe (S n)
  | bet_weakening _ _ ts _ _ pes => "be_weakening by " ++ pp_value_types ts ++ newline ++ pp_bet pes (S n)
  end).

Definition pp_clt {s: (store_record host_function)} {cl tf} (p: cl_typing s cl tf) (n: indentation) : string :=
  indent n (
  match p with
  | cl_typing_native _ _ _ _ _ _ _ _ _ pit _ _ pes => "cl_typing_native" ++ newline ++ pp_bet pes (S n)
  | cl_typing_host _ _ h => "cl_typing_host"
  end).

Fixpoint pp_et {s C es tf} (p: e_typing s C es tf) (n: indentation) : string :=
  indent n (
  match p with
  | ety_a _ _ bes _ pes => "bet" ++ newline ++ pp_bet pes (S n)
  | ety_composition _ _ es e _ _ _ pes pe => "e_composition with tail " ++ pp_administrative_instruction 0 e ++ pp_et pes (S n) ++ newline ++ pp_et pe (S n)
  | ety_weakening _ _ _ ts _ _ pes => "e_weakening by " ++ pp_value_types ts ++ newline ++ pp_et pes (S n)
  | ety_trap _ _ _ => "trap"
  | ety_local _ _ _ _ _ _ pes _ => "frame" ++ newline ++ pp_st pes (S n)
  | ety_invoke _ _ _ _ _ _ pclt => "invoke" ++ newline ++ pp_clt pclt (S n)
  | ety_label _ _ _ _ _ _ _ pes0 pes _ => "label" ++ newline ++ pp_et pes0 (S n) ++ newline ++ pp_et pes (S n)
  end)
with pp_st {s rs f es ts} (p: s_typing s rs f es ts) (n: indentation) : string :=
  indent n (
  match p with
  | mk_s_typing _ _ _ _ _ _ _ pft _ pet _ => "s_typing" ++ newline ++ pp_et pet n
  end).

Definition pp_cfgt {s f es ts} (p: config_typing s f es ts) (n: indentation) : string :=
  indent n (
  match p with
  | mk_config_typing _ _ _ _ pstoret pst => "config" ++ newline ++ pp_st pst n
  end).

(* XXX disambiguate between cfg/res tuple with/without hs? *)
Definition pp_config_tuple_except_store (cfg : store_record host_function * frame * list administrative_instruction) : string :=
  let '(s, f, es) := cfg in
  pp_administrative_instructions 0 es ++
  "with values " ++ pp_values_hint_empty f.(f_locs) ++ newline.

Let host := host host_function.

Variable host_instance : host.

Definition pp_res_tuple_except_store (cfg: @res_ppi host_function host_instance) : string :=
  match cfg with
  | RSP_exhaustion => "exhaustion"
  | RSP_terminal es _ => "termination with " ++ pp_administrative_instructions 0 es
  | RSP_cfg hs s f es ts _ => "step with " ++ newline ++ pp_administrative_instructions 0 es ++ " with values " ++ pp_values_hint_empty f.(f_locs) ++ newline
  end.

Definition pp_res_tuple_except_store_typed (cfg: @res_ppi host_function host_instance) : string :=
  match cfg with
  | RSP_exhaustion => "exhaustion"
  | RSP_terminal es _ => "termination with " ++ pp_administrative_instructions 0 es
  | RSP_cfg hs s f es ts pcfgt => "step with " ++ newline ++ pp_administrative_instructions 0 es ++ " with values " ++ pp_values_hint_empty f.(f_locs) ++ newline ++ "and typing term:" ++ newline ++ pp_cfgt pcfgt 0 ++ newline
  end.

End Host.

(** As-is, [eqType] tends not to extract well.
  This section provides alternative definitions for better extraction. **)
Module PP.

Import EmptyHost.
Import Interpreter_PPI_extract.

Section Show.

Definition pp_values : list value -> string := pp_values.

Definition pp_store : nat -> store_record -> string := pp_store host_function_eqType.

Definition pp_config_tuple_except_store : store_record * frame * list administrative_instruction -> string :=
  pp_config_tuple_except_store host_function_eqType.

Definition pp_res_tuple_except_store :=
  @pp_res_tuple_except_store host_function_eqType host_instance.

Definition pp_res_tuple_except_store_typed :=
  @pp_res_tuple_except_store_typed host_function_eqType host_instance.

Definition pp_administrative_instructions : nat -> list administrative_instruction -> string :=
  pp_administrative_instructions.

End Show.

End PP.

