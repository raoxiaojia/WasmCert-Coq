From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat.
From Coq Require Import BinInt BinNat NArith Lia Uint63 String.
From Wasm Require Import interpreter_ctx instantiation_sound type_preservation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
  QC_Admin_Preservation.v
  ------------------------
  QuickChick example for WasmCert-Coq:
  - Random generation of *administrative* instructions
  - One-step preservation test: if config_tuple is well-typed and steps to config_tuple', then config_tuple' is well-typed.

  Minimal edits required:
    • Replace the five "ADAPT ME" notations below with the exact names from WasmCert-Coq.
    • If your step function has a different shape (relation vs. function), use the alternative checker near the end.

  Requires:
    opam install coq-quickchick
*)

From QuickChick Require Import QuickChick.
Import QcDefaultNotation.
Open Scope qc_scope.

(* === WasmCert-Coq imports (names can differ a bit between releases) === *)
(* Try these; if they don’t match your tree, search for the modules that define:
     - values, instructions (surface + administrative), configurations
     - the executable small-step function
     - the boolean typechecker for configurations (README mentions soundness+completeness)
   and adjust the "Require Import" lines and the five notations below. *)
From Wasm Require Import datatypes_properties opsem typing type_checker type_preservation interpreter_ctx extraction_instance memory_vec.

(* ---------- Small adapter: tweak these 5 lines to your repo ---------- *)
(* ADAPT ME: configuration type *)

Definition stack_limit : N := 65536%N.

Section qc.
  Import Extraction_instance.
  Import Memory_instance.
  
(*
Notation "<< hs , config_tuple , d >>" := (@RSC_normal _ _ _ hs config_tuple d).


Check RSC_normal.

Definition stepf (c: config_tuple) : option config_tuple :=
  match interp_config_tuple_of_wasm c with
  | exist _ c_ctx _ =>
    match run_one_step c_ctx stack_limit with
    | RSC_normal _ config_tuple' d' _ =>
        ctx_to_config_tuple config_tuple'
    | RSC_value _ _ vs =>
        to_e_list vs
    | _ => None
    end
  end.

  
Parameter stepf : config_tuple -> option config_tuple.
(* If you already have [stepf] in your repo, comment the Parameter and [Existing] it. *)
*)
(* ADAPT ME: boolean well-typedness checker for configurations *)
Parameter typecheck_config_tuple : config_tuple -> bool.
(* ADAPT ME: a simple constructor for an “empty-ish” configuration *)
Parameter empty_config_tuple : config_tuple.

(* If you have decidable types for “values”, “surface instr”, etc., import/derive them.
   Below are basic generators that don’t rely on deriving instances for Wasm’s big types. *)

(* === Small, size-bounded generators for Wasm numerics and values === *)

(* A tiny numeric generator to avoid huge terms that shrink slowly. *)
Definition gen_i32 : G Z :=
  freq [ (4%nat, returnGen 0%Z)
       ; (4%nat, returnGen 1%Z)
       ; (4%nat, returnGen (-1)%Z)
       ; (1%nat, fmap Z.of_nat (choose (0%nat, 256%nat)))
       ].

(* You likely have a [val] type with constructors like vi32/vi64/vf32/vf64.
   Replace/extend this as needed. *)

Definition vi32 z := VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m z)).

Definition gen_val : G value :=
  fmap vi32 gen_i32.

(* === Generating small surface instruction fragments (to embed in admin instrs) === *)

(* Replace these with your repo's concrete instruction constructors. *)
Parameter instr : Set.
Parameter I_const_i32 : Z -> instr.

(* Trivially well-formed small instruction lists. Extend with more instructions if desired. *)
Definition gen_small_instrs : G (list instr) :=
  sized (fun sz =>
    if sz is O then
      elements [ [AI_basic (BI_nop)]; [AI_basic (BI_drop)]; [I_const_i32 0%Z] ]
    else
      oneOf_
        [ returnGen [I_const_i32 0%Z; AI_basic (BI_drop)]
        ; returnGen [AI_basic (BI_nop)]
        ; returnGen [I_const_i32 1%Z]
        ]).

(* === Administrative instructions ===
   Typical constructors in WebAssembly mechanisations:
     • trap
     • invoke fidx
     • label n (cont : list instr) (body : list instr)
     • frame n (locals : list val) (code : list instr)
   Adjust names/arity to the ones in WasmCert-Coq. *)

Parameter AI_trap  : admin_instr.
Parameter AI_invoke : nat -> admin_instr.
Parameter AI_label : nat -> list instr -> list instr -> admin_instr.
Parameter AI_frame : nat -> list val  -> list instr -> admin_instr.

(* Helper for bounded-length lists of values/instr *)
Definition gen_list {A} (g : G A) (maxlen : nat) : G (list A) :=
  bindGen (choose (0, maxlen)) (fun n => vectorOf n g).

(* “Valid” admin instruction generator:
   - AI_trap is always valid.
   - AI_label k cont body: keep tiny arities and tiny code to ease shrinking.
   - AI_frame n locals code: generate locals with small length = n. *)
Definition gen_admin_instr : G admin_instr :=
  sized (fun sz =>
    let k := Nat.min 2 sz in
    oneOf_
      [ returnGen AI_trap
      ; fmap AI_invoke (choose (0, 0))                 (* only invoke 0; see config_tuple generator *)
      ; cont <- gen_small_instrs ;;
        bod  <- gen_small_instrs ;;
        returnGen (AI_label k cont bod)
      ; n <- choose (0, 2) ;;
        locs <- gen_list gen_val n ;;
        code <- gen_small_instrs ;;
        returnGen (AI_frame n locs code)
      ]).

(* Show instances so Sample works nicely *)
Parameter show_admin : admin_instr -> String.string.
Instance show_admin_instr : Show admin_instr := { show := show_admin }.

(* === Putting admin instructions inside a configuration === *)

(* You may already have a function to “inject” an admin instr as the current code in a config_tuple. *)
Parameter config_tuple_set_admin_code : config_tuple -> admin_instr -> config_tuple.

(* Construct a small, *valid* configuration for a generated admin instruction.
   The idea:
     - start from an “empty-ish but valid” configuration (module instantiated etc.) [empty_config_tuple]
     - ensure table[0] exists when we generate AI_invoke 0
   In many builds this will already be true in [empty_config_tuple]; if not, adapt [mk_config_tuple] here. *)

Definition mk_config_tuple (ai : admin_instr) : config_tuple :=
  config_tuple_set_admin_code empty_config_tuple ai.

(* === Preservation checker ===
   If config_tuple is well-typed and steps to config_tuple', then config_tuple' is well-typed. *)

Definition preservation1 (c : config_tuple) : bool :=
  if typecheck_config_tuple c then
    match stepf c with
    | None => true (* stuck or terminal ≈ nothing to check *)
    | Some c' => typecheck_config_tuple c'
    end
  else true.

(* Property over random *valid* admin instructions embedded in small configurations. *)
Definition prop_preservation_admin : Checker :=
  forAll gen_admin_instr (fun ai =>
    let c := mk_config_tuple ai in
    whenFail ("Counterexample admin instr:\n" ++ show ai)
             (checker (preservation1 c))).

(* A quick smoke test: generate a few admin instructions to see the distribution *)
Definition sample_admin : G admin_instr := gen_admin_instr.

(* === Shrinking (optional). QuickChick can handle without custom shrinkers for now. === *)

(* === Run examples === *)

(* Uncomment to see samples in CoqIDE/VSCoq:
     Sample sample_admin.
*)

(* The actual QuickChick run: *)
QuickChick prop_preservation_admin.

(* === Alternative: if you only have a *relational* step (c --> c'), and a “one-step executor”
       that tries to find a successor (or None if no step), swap [stepf] above accordingly.
   If you need to build it from a relation [stepR : config_tuple -> config_tuple -> Prop], give QuickChick a
   search bound or use the reference interpreter (the repo ships one). See README. *)

End qc.
