From Wasm Require Import common properties tactic typing_inversion.
From Coq Require Import ZArith.BinInt Program.Equality.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Export operations host type_preservation type_progress type_checker type_checker_reflects_typing context_inference.
Require Import BinNat.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensive.

Section Host.

Variable host_function: eqType.

Let store_record := store_record host_function.
Let function_closure := function_closure host_function.
Let e_typing := @e_typing host_function.
Let s_typing := @s_typing host_function.
Let inst_typing := @inst_typing host_function.

Let host := host host_function.

Variable host_instance : host.

Let host_state := host_state host_instance.

Variable hs0: host_state.

Let host_application := @host_application host_function host_instance.

Let reduce := @reduce host_function host_instance.

Let t_progress := @t_progress host_function host_instance.

Let t_preservation := @t_preservation host_function host_instance.

Let config_typing := @config_typing host_function.

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
    + exact (@RSP_terminal es Hterm).
    + specialize (t_preservation Hred Htype) as Htype'.
      by eapply RSP_cfg; eauto.
  - by eapply RSP_terminal; eauto.
Defined.

Fixpoint run_multi_step_ppi (fuel: nat) (cfg: res_ppi) {struct fuel}: res_ppi :=
  match fuel with
  | 0 => RSP_exhaustion
  | (S fuel') =>
      match cfg with
      | RSP_cfg hs s f es ts Htype =>
          run_multi_step_ppi fuel' (run_one_step_ppi (RSP_cfg hs Htype))
      | x => x
      end
  end.
Definition make_ppi_cfg hs s f es ts (Htype: config_typing s f es ts) : res_ppi :=
  RSP_cfg hs Htype.

Definition run_multi_step (fuel: N) hs s f es ts (Htype: config_typing s f es ts) : res_ppi :=
  run_multi_step_ppi fuel (@make_ppi_cfg hs s f es ts Htype).

Definition cl_typing_inf (s: store_record) (f: function_closure): option (cl_type_check_single s f).
Proof.
  destruct f as [inst [ts1 ts2] ts bes | tf h]; last first.
  - apply Some.
    unfold cl_type_check_single.
    by apply cl_typing_host.
  - destruct (inst_typing_inf s inst) as [C | ] eqn:Hinf; last exact None.
    apply inst_typing_inf_impl in Hinf.
    destruct (b_e_type_checker (upd_local_label_return C (ts1 ++ ts) [::ts2] (Some ts2)) bes (Tf nil ts2)) eqn:Htypecheck; last exact None.
    apply b_e_tc_typing in Htypecheck.
    apply Some.
    eapply cl_typing_native; by eauto.
Defined.

Definition cls_typing_inf (s: store_record) (fs: list function_closure) : option (TProp.Forall (cl_type_check_single s) fs).
Proof.
  induction fs as [|f fs]; first by apply Some; econstructor.
  destruct (cl_typing_inf s f) as [clt | ]; last exact None.
  destruct IHfs as [clts | ]; last exact None.
  apply Some.
  by constructor.
Defined.

Definition store_typing_inf (s: store_record): option (store_typing s).
Proof.
  destruct (cls_typing_inf s s.(s_funcs)) as [clts | ]; last exact None.
  destruct (all (fun t => tab_agree s t) s.(s_tables)) eqn:Htabagree; last exact None.
  destruct (all mem_agree s.(s_mems)) eqn:Hmemagree; last exact None.
  destruct s as [fs tclss mss ?] => /=.
  by apply Some; split => //.
Defined.

Definition run_ppi_init (s: store_record) (f: frame) (bes: list basic_instruction) (ts: result_type) : option res_ppi.
Proof.
  destruct (frame_typing_inf s f) as [C | ] eqn:Hftinf; last exact None.
  destruct (store_typing_inf s) as [Hst | ]; last exact None.
  destruct (b_e_type_checker (upd_return C None) bes (Tf nil ts)) eqn:Htypecheck; last exact None.
  apply b_e_tc_typing in Htypecheck.
  apply frame_typing_inf_impl in Hftinf.
  apply Some.
  assert (config_typing s f (to_e_list bes) ts) as Htype.
  { constructor; first exact Hst.
    econstructor; first exact Hftinf; eauto.
    apply ety_a' with (es := (to_e_list bes)); first by apply to_e_list_basic.
    replace (to_b_list (to_e_list bes)) with bes; first exact Htypecheck.
    by apply b_e_elim.
  }
  exact (make_ppi_cfg hs0 Htype).
Defined.

(* Dealing with the invocation after instantiation, which is not a basic instruction *)
Definition run_ppi_init_invoke (s: store_record) (f: frame) (addr: funcaddr) : option res_ppi.
Proof.
  destruct (frame_typing_inf s f) as [C | ] eqn:Hftinf; last exact None.
  destruct (store_typing_inf s) as [Hst | ]; last exact None.
  destruct (List.nth_error s.(s_funcs) addr) as [cl | ] eqn:Hnth; last exact None.
  destruct (cl_typing_inf s cl) as [Hclt | ]; last exact None.
  destruct (cl_type cl) as [ts1 ts2] eqn:Hcltype.
  destruct ts1; last exact None.
  apply frame_typing_inf_impl in Hftinf.
  apply Some.
  assert (config_typing s f [::AI_invoke addr] ts2) as Htype.
  { constructor; first exact Hst.
    econstructor; first exact Hftinf; eauto.
    eapply ety_invoke; eauto.
    unfold cl_type_check_single in Hclt.
    by rewrite Hcltype in Hclt.
  }
  exact (make_ppi_cfg hs0 Htype).
Defined.

Definition run_multi_step' (fuel: N) (s: store_record) (f: frame) (bes: list basic_instruction) (ts: result_type) : option res_ppi.
Proof.
  destruct (run_ppi_init s f bes ts) as [cfg | ]; last exact None.
  exact (Some (run_multi_step_ppi fuel cfg)).
Defined.

End Host.

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

Definition res_ppi := @res_ppi host_function_eqType host_instance.

Definition run_one_step_ppi := @run_one_step_ppi host_function_eqType host_instance.

Definition run_ppi_init_invoke := @run_ppi_init_invoke host_function_eqType host_instance tt.

Definition run_multi_step' := @run_multi_step' host_function_eqType host_instance tt.

Definition is_const_list := e_to_v_list_opt.

End Interpreter_PPI_extract.
