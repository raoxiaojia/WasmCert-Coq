From Wasm Require Export datatypes_properties operations typing opsem common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Bool Program NArith ZArith Wf_nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section intro_opsem.
  
Context `{ho: host}.

(* Reduction of an instruction sequence.
   There's no explicit rule that allows this, yet this is certainly an expected behaviour. Prove the following by finding one/several appropriate reduction rule(s) that allows the reduction:
 *) 
Lemma opsem_reduce_seq1: forall hs1 s1 f1 es1 hs2 s2 f2 es2 es0,
      reduce hs1 s1 f1 es1 hs2 s2 f2 es2 ->
      reduce hs1 s1 f1 (es1 ++ es0) hs2 s2 f2 (es2 ++ es0).
Proof.
Admitted.
  
(* The same applies for attaching a list of values on the left. *)
Lemma opsem_reduce_seq2: forall hs1 s1 f1 es1 hs2 s2 f2 es2 vs,
    const_list vs ->
    reduce hs1 s1 f1 es1 hs2 s2 f2 es2 ->
    reduce hs1 s1 f1 (vs ++ es1) hs2 s2 f2 (vs ++ es2).
Proof.
Admitted.

Variable hs: host_state.

(* Is the above true without the const_list assumption?
   Prove or disprove it by establishing a witness to the following: *)
Lemma opsem_reduce_seq2':
    {forall s1 f1 es1 s2 f2 es2 es0,
    reduce hs s1 f1 es1 hs s2 f2 es2 ->
    reduce hs s1 f1 (es0 ++ es1) hs s2 f2 (es0 ++ es2)} +
    {exists s1 f1 es1 s2 f2 es2 es0,
    reduce hs s1 f1 es1 hs s2 f2 es2 ->
    (reduce hs s1 f1 (es0 ++ es1) hs s2 f2 (es0 ++ es2) -> False)}.
Proof.
Admitted.

End intro_opsem.

Section intro_types.

Context `{ho: host}.

(* The newer proposals of Wasm introduces a notion of a subtyping relation <:,
   which did not exist in Wasm 1.0 (and not even formally in Wasm 2.0).

   This is implemented in the Coq mechanisation, which complicates the type
   system slightly. If a program can be associated with a function type, then
   it can also be associated with any supertype of that function type
   (`bet_subtyping`).

   The following exercise helps to understand how instruction subtyping works.
 *)
Lemma subtypes_1:
  instr_subtyping (Tf nil [::T_num T_i32]) (Tf [::T_num T_i32] [::T_num T_i32; T_num T_i32]).
Proof.
Admitted.

Notation "$N v" := (BI_const_num v) (at level 20).

(* Establish the following typing derivation by applying the composition
   rule `bet_composition`, with appropriate rewrites and other typing rules
   in the `be_typing` inductive definition. *)
Lemma types_composition: forall C c1 c2,
  be_typing C [:: $N (VAL_int32 c1); $N (VAL_int32 c2); BI_binop T_i32 (Binop_i BOI_add)] (Tf nil [::T_num T_i32]).
Proof.
Admitted.

(* The following 2 are slightly more difficult *)
(* It is slightly awkward to apply the `bet_composition` rule, since it only
   allows appending one instruction at a time instead of allowing arbitrary
   concatenation of instruction lists. The following composition typing lemma
   is a more general version. Prove it by an appropriate induction.
*)
Lemma bet_composition2: forall C es1 es2 ts1 ts2 ts3,
    be_typing C es1 (Tf ts1 ts2) ->
    be_typing C es2 (Tf ts2 ts3) ->
    be_typing C (es1 ++ es2) (Tf ts1 ts3).
Proof.
Admitted.

(* The following 'typing inversion lemma' is some sort of a converse to the
   one above. Prove it by an appropriate induction.
   These typing inversion lemmas are key to proving the soundness properties,
   as they provide a way to extract information from the typing premises.
 *)
Lemma be_composition_inversion: forall C es1 es2 t1s t2s,
    be_typing C (es1 ++ es2) (Tf t1s t2s) ->
    exists t3s, be_typing C es1 (Tf t1s t3s) /\
           be_typing C es2 (Tf t3s t2s).
Proof.
Admitted.

End intro_types.
