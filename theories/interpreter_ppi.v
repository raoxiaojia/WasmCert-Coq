From Wasm Require Import common properties tactic typing_inversion.
From Coq Require Import ZArith.BinInt Program.Equality.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Export operations host type_preservation type_progress.
Require Import BinNat.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensive.

(** Extraction **)
Module EmptyHost.

Definition host_function := void.

Definition host_function_eq_dec : forall f1 f2 : host_function, {f1 = f2} + {f1 <> f2}.
Proof. decidable_equality. Defined.

Definition host_function_eqb f1 f2 : bool := host_function_eq_dec f1 f2.
Definition host_functionP : Equality.axiom host_function_eqb :=
  eq_dec_Equality_axiom host_function_eq_dec.

Global Canonical Structure host_function_eqMixin := EqMixin host_functionP.
Global Canonical Structure host_function_eqType :=
  Eval hnf in EqType host_function host_function_eqMixin.

Definition host : Type := host host_function_eqType.

Definition store_record := store_record host_function_eqType.
Definition function_closure := function_closure host_function_eqType.

Definition host_instance : host.
Proof.
  by refine {|
      host_state := unit_eqType ;
      host_application _ _ _ _ _ _ _ := False
    |}.
Defined.

Definition config_tuple := config_tuple host_function.

Definition host_state := host_state host_instance.

End EmptyHost.


Module Interpreter_PPI_extract.

Import EmptyHost.

Let t_progress := @t_progress host_function_eqType host_instance.

Let t_preservation := @t_preservation host_function_eqType host_instance.

Let config_typing := @config_typing host_function_eqType.


Inductive res_ppi : Type :=
| RSP_exhaustion
| RSP_cfg: forall (hs: host_state) s f es ts,
    config_typing s f es ts ->
    res_ppi
| RSP_terminal: forall es,
    terminal_form es ->
    res_ppi
.

Definition run_one_step_ppi (cfg: res_ppi): res_ppi.
Proof.
  destruct cfg as [| hs s f es ts Htype | Hterm].
  - exact RSP_exhaustion.
  - destruct (t_progress hs Htype) as [Hterm | [s' [f' [es' [hs' Hred]]]]].
    + exact (RSP_cfg hs Htype).
    + specialize (t_preservation Hred Htype) as Htype'.
      by eapply RSP_cfg; eauto.
  - by eapply RSP_terminal; eauto.
Defined.

Print run_one_step_ppi.

Definition make_ppi_cfg s f es ts (Htype: config_typing s f es ts) : res_ppi :=
  RSP_cfg tt Htype.

(* This obviously terminate, but the only purpose of it is using the efficient N for extraction (instead of inserting extra proofs), so let's omit the proof *)
Unset Guard Checking.

Fixpoint run_multi_step_ppi (fuel: N) (cfg: res_ppi) {struct fuel}: res_ppi :=
  match fuel with
  | 0%N => RSP_exhaustion
  | Npos p =>
      match cfg with
      | RSP_cfg hs s f es ts Htype =>
          run_multi_step_ppi (Pos.pred_N p) (run_one_step_ppi (RSP_cfg hs Htype))
      | x => x
      end
  end.

Set Guard Checking.

End Interpreter_PPI_extract.
