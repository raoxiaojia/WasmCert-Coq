From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat.
From Coq Require Import BinInt BinNat NArith Lia Uint63 String.
From Wasm Require Import interpreter_ctx instantiation_sound type_preservation extraction_instance binary_format_printer type_checker.

From QuickChick Require Import QuickChick.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Extraction_instance.

Definition cfg := config_tuple.

Import QcDefaultNotation.
Open Scope qc_scope.

Definition gen_i32 : G i32 :=
  oneOf [ returnGen Wasm_int.Int32.zero;
           returnGen Wasm_int.Int32.one].

Instance Show_i32 : Show i32.
  constructor.
  refine (fun x => pp.pp_value_num (VAL_int32 x)).
Defined.

Global Instance Gen_i32 : Gen i32 :=
  {| arbitrary := gen_i32 |}.

Definition shrink_i32 (x: i32) : list i32 :=
  match x with
  | _ => nil
  end.

Instance Shrink_i32 : Shrink i32 :=
  {| shrink := shrink_i32 |}.

Instance Arbitrary_i32 : Arbitrary i32 :=
  Build_Arbitrary _ Gen_i32 Shrink_i32.

Definition gen_i64 : G i64 :=
  oneOf [ returnGen Wasm_int.Int64.zero;
           returnGen Wasm_int.Int64.one].

Instance Show_i64 : Show i64.
  constructor.
  refine (fun x => pp.pp_value_num (VAL_int64 x)).
Defined.

Global Instance Gen_i64 : Gen i64 :=
  {| arbitrary := gen_i64 |}.

Definition shrink_i64 (x: i64) : list i64 :=
  match x with
  | _ => nil
  end.

Instance Shrink_i64 : Shrink i64 :=
  {| shrink := shrink_i64 |}.

Instance Arbitrary_i64 : Arbitrary i64 :=
  Build_Arbitrary _ Gen_i64 Shrink_i64.

Print Wasm_float.FloatSize32.

Definition gen_f32 : G f32 :=
  oneOf [ returnGen Wasm_float.FloatSize32.zero;
           returnGen (Wasm_float.FloatSize32.of_int Integers.Int.one)].

Instance Show_f32 : Show f32.
  constructor.
  refine (fun x => pp.pp_value_num (VAL_float32 x)).
Defined.

Global Instance Gen_f32 : Gen f32 :=
  {| arbitrary := gen_f32 |}.

Definition shrink_f32 (x: f32) : list f32 :=
  match x with
  | _ => nil
  end.

Instance Shrink_f32 : Shrink f32 :=
  {| shrink := shrink_f32 |}.

Instance Arbitrary_f32 : Arbitrary f32 :=
  Build_Arbitrary _ Gen_f32 Shrink_f32.

Definition gen_f64 : G f64 :=
  oneOf [ returnGen Wasm_float.FloatSize64.zero;
           returnGen (Wasm_float.FloatSize64.of_int Integers.Int.one)].

Instance Show_f64 : Show f64.
  constructor.
  refine (fun x => pp.pp_value_num (VAL_float64 x)).
Defined.

Global Instance Gen_f64 : Gen f64 :=
  {| arbitrary := gen_f64 |}.

Definition shrink_f64 (x: f64) : list f64 :=
  match x with
  | _ => nil
  end.

Instance Shrink_f64 : Shrink f64 :=
  {| shrink := shrink_f64 |}.

Instance Arbitrary_f64 : Arbitrary f64 :=
  Build_Arbitrary _ Gen_f64 Shrink_f64.

Derive (Arbitrary, Show) for value_num.

Derive Arbitrary for reference_type.

Instance Show_value_ref : Show value_ref.
  constructor.
  refine (fun x => pp.pp_value_ref x).
Defined.

Derive Arbitrary for value_ref.

Definition gen_v128 : G v128 :=
  oneOf [ returnGen (List.repeat Integers.Byte.zero 16);
          returnGen (List.repeat Integers.Byte.one 16)
    ].

Instance Show_v128 : Show v128.
  constructor.
  refine (fun x => pp.pp_value_vec (VAL_vec128 x)).
Defined.

Global Instance Gen_v128 : Gen v128 :=
  {| arbitrary := gen_v128 |}.

Definition shrink_v128 (x: v128) : list v128 :=
  match x with
  | _ => nil
  end.

Instance Shrink_v128 : Shrink v128 :=
  {| shrink := shrink_v128 |}.

Instance Arbitrary_v128 : Arbitrary v128 :=
  Build_Arbitrary _ Gen_v128 Shrink_v128.

Derive (Arbitrary, Show) for value_vec.

Derive (Arbitrary, Show) for value.

Derive (Arbitrary, Show) for number_type.

Derive (Arbitrary, Show) for sx.

Derive (Arbitrary, Show) for packed_type.

Derive (Arbitrary, Show) for vector_type.

Instance Show_reference_type : Show reference_type.
  constructor.
  refine (fun x => pp.pp_reference_type x).
Defined.

Derive (Arbitrary, Show) for value_type.

Derive Arbitrary for unop_i.
Derive Arbitrary for unop_f.
Derive Arbitrary for unop.
Derive Arbitrary for binop_i.
Derive Arbitrary for binop_f.
Derive Arbitrary for binop.
Derive Arbitrary for testop.
Derive Arbitrary for relop_i.
Derive Arbitrary for relop_f.
Derive Arbitrary for relop.
Derive Arbitrary for cvtop.
Derive Arbitrary for vshape_i.
Derive Arbitrary for vshape_f.
Derive Arbitrary for vshape.

(* Derive arbitrary doesn't work for records. *)
Derive GenSized for memarg.
Instance Shrink_memarg: Shrink memarg.
  constructor.
  refine (fun x => cons x nil).
Defined.

Instance Arbitrary_memarg: Arbitrary memarg.
Defined.

Derive Arbitrary for load_vec_arg.
Derive Arbitrary for block_type.

Print arbitrarySized_impl_block_type.

(* Requires using thunkGen for laziness, else there would be exponential
 blowups? https://github.com/QuickChick/QuickChick/issues/370 *)
Definition qc_gen {T: Type} (x: T) :=
  thunkGen (fun _ => returnGen x).

Definition gen_basic_instruction0 : G basic_instruction :=
  oneOf [ qc_gen BI_nop;
          qc_gen BI_drop
    ].

Definition gen_list_ub {T: Type} (f: G T) (ub: nat) : G (list T) :=
  bindGen (choose (0, ub)) (fun n: nat =>
                       sequenceGen (List.repeat f n)).

Fixpoint G_basic_instruction (sz: nat) : G basic_instruction :=
  match sz with
  | 0 => gen_basic_instruction0
  | S sz' =>
      freq
        [ (sz',
             thunkGen (fun _ =>
                         bindGen arbitrary (fun bt: block_type =>
                                              (thunkGen (fun _ =>
                                                           bindGen (gen_list_ub (G_basic_instruction sz') sz') (fun bes => returnGen (BI_block bt bes)))))));
          (1, thunkGen (fun _ => gen_basic_instruction0))
        ]
         end.
         
Instance GenSized_basic_instruction: GenSized basic_instruction.
  constructor.
  refine G_basic_instruction.
Defined.

Instance Show_basic_instruction: Show basic_instruction.
  constructor.
  refine ((fun x => pp.pp_basic_instruction 0 x)).
Defined.

Parameter hs: host_state.

Definition basic_instruction_preserve (bes: basic_instruction) : bool :=
  (negb (b_e_type_checker empty_t_context [::bes] (Tf nil nil))) ||
    (
      match run_multi_step_raw Extraction_instance.host_application_impl_correct hs 100 empty_store_record empty_frame [::AI_basic bes] with
      | inl _ => false
      | inr _ => true
      end
    ).

Print SIMD_ops.app_vbinop_str.

(* SIMD execution needs concrete implementation in Rocq for this to work, it seems. *)

Definition app_vunop_str_proxy (op: vunop) (s: string) : string := s.

Extract Constant SIMD_ops.app_vunop_str => "app_vunop_str_proxy".
Extract Constant SIMD_ops.app_vbinop_str => "SIMD_ops.app_vbinop_str".
Extract Constant SIMD_ops.app_vternop_str => "SIMD_ops.app_vternop_str".
Extract Constant SIMD_ops.app_vtestop_str => "SIMD_ops.app_vtestop_str".
Extract Constant SIMD_ops.app_vshiftop_str => "SIMD_ops.app_vshiftop_str".

QuickChick (forAll (G_basic_instruction 5) basic_instruction_preserve).

Sample (G_basic_instruction 5).

Derive Arbitrary for basic_instruction.

Derive ArbitrarySizedSuchThat for (fun x => config_correct x).
