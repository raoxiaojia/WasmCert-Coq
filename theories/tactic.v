From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import properties typing_inversion.

Ltac size_unequal H :=
  repeat rewrite length_is_size in H;
  revert H;
  repeat rewrite size_cat; repeat rewrite size_rev; repeat rewrite size_map; repeat rewrite size_drop; repeat rewrite size_take; simpl; lias.

(** A common pattern in the proof: using an hypothesis on the form [rev l = l'] to rewrite [l]. **)
Ltac subst_rev_const_list :=
 repeat lazymatch goal with
 | HRevConst: rev ?lconst = ?h :: ?t |- _ =>
   apply rev_move in HRevConst; rewrite HRevConst; rewrite -cat1s; rewrite rev_cat;
   rewrite -v_to_e_cat; rewrite -catA
 end.

(** Simplify the lists in the goal. **)
Ltac simplify_lists :=
  (** Common rewriting rules. **)
  repeat first [
      rewrite drop_rev
    | rewrite take_rev
    | rewrite revK
    | rewrite length_is_size
    | rewrite size_take
    | rewrite size_drop
    | rewrite size_rev
    | rewrite v_to_e_size
    | rewrite rev_cat
    | rewrite rev_cons -cats1
    | rewrite -v_to_e_cat
    | rewrite -v_to_e_rev
    | rewrite -v_to_e_take
    | rewrite -v_to_e_drop];
  (** Putting all the lists into a normal form, as concatenations of as many things.
    Because [cat1s] conflicts with [cats0], replacing any occurence of [[X]] to
    [[X] ++ [::]], it has to be done separately.
    Rewrite with the associated [math goal with] is avoid to deal with existential
    vairables. **)
  repeat match goal with
  |- context C [?x :: ?l] =>
     lazymatch l with [::] => fail | _ => rewrite -(cat1s x l) end
  end;
  repeat lazymatch goal with
  | |- context C [[::] ++ _] => rewrite cat0s
  | |- context C [_ ++ [::]] => rewrite cats0
  | |- context C [rcons _ _] => rewrite -cats1
  | |- context C [(_ ++ _) ++ _] => rewrite -catA
  | |- context C [rev [::]] => rewrite rev0
  | |- context C [v_to_e_list [::]] => simpl v_to_e_list at 1
  | |- context C [v_to_e_list [:: _]] => simpl v_to_e_list at 1
  end;
  try subst_rev_const_list.

(** A common scheme in the progress proof, with a continuation. **)
Ltac solve_progress_cont cont :=
  repeat eexists;
  solve [
      apply r_simple; solve [ eauto | constructor; eauto | cont; eauto ]
    | cont ].

(** The same, but without continuation. **)
Ltac solve_progress :=
  solve_progress_cont ltac:(fail).


(* Looking up from instances, stores, and contexts *)
Ltac inst_typing_lookup :=
  try multimatch goal with
  | H1: inst_typing ?s ?i = Some ?t,
    H2: lookup_N (inst_types ?i) ?n = Some _ |- _ =>
      let Hteq := fresh "Hteq" in
      specialize (Logic.eq_sym (inst_typing_type_lookup n H1)) as Hteq;
      rewrite H2 in Hteq
  | H1: inst_typing ?s ?i = Some ?t,
    H2: lookup_N (inst_funcs ?i) _ = Some _ |- _ =>
      let ft := fresh "ft" in
      let Hextft := fresh "Hextft" in
      let Hnthft := fresh "Hnthft" in
      specialize (inst_typing_func_lookup H1 H2) as [ft [Hextft Hnthft]];
      unfold ext_func_typing in Hextft
  | H1: inst_typing ?s ?i = Some ?t,
    H2: lookup_N (inst_tables ?i) _ = Some _ |- _ =>
      let tabt := fresh "tabt" in
      let Hexttabt := fresh "Hexttabt" in
      let Hnthtabt := fresh "Hnthtabt" in
      specialize (inst_typing_table_lookup H1 H2) as [tabt [Hexttabt Hnthtabt]];
      unfold ext_table_typing in Hexttabt
  | H1: inst_typing ?s ?i = Some ?t,
    H2: lookup_N (inst_mems ?i) _ = Some _ |- _ =>
      let mt := fresh "mt" in
      let Hextmt := fresh "Hextmt" in
      let Hnthmt := fresh "Hnthmt" in
      specialize (inst_typing_mem_lookup H1 H2) as [mt [Hextmt Hnthmt]];
      unfold ext_mem_typing in Hextmt
  | H1: inst_typing ?s ?i = Some ?t,
    H2: lookup_N (inst_globals ?i) _ = Some _ |- _ =>
      let gt := fresh "gt" in
      let Hextgt := fresh "Hextgt" in
      let Hnthgt := fresh "Hnthgt" in
      specialize (inst_typing_global_lookup H1 H2) as [gt [Hextgt Hnthgt]];
      unfold ext_global_typing in Hextgt
  | H1: inst_typing ?s ?i = Some ?t,
    H2: lookup_N (inst_elems ?i) _ = Some _ |- _ =>
      let et := fresh "et" in
      let ei := fresh "ei" in
      let Hnthselem := fresh "Hnthselem" in
      let Helemtype := fresh "Helemtype" in
      let Hnthet := fresh "Hnthet" in
      specialize (inst_typing_elem_lookup H1 H2) as [et [ei [Hnthselem [Helemtype Hnthet]]]]
  | H1: inst_typing ?s ?i = Some ?t,
    H2: lookup_N (inst_datas ?i) _ = Some _ |- _ =>
      let dt := fresh "et" in
      let di := fresh "di" in
      let Hnthsdata := fresh "Hnthsdata" in
      let Hdatatype := fresh "Hdatatype" in
      let Hnthdt := fresh "Hnthdt" in
      specialize (inst_typing_data_lookup H1 H2) as [dt [di [Hnthsdata [Hdatatype Hnthdt]]]]
  end.

Ltac store_typing_lookup :=
  try multimatch goal with
  | H1: store_typing ?s,
      H2: lookup_N (s_funcs ?s) _ = Some _ |- _ =>
      let ft := fresh "ft" in
      let Hft := fresh "Hft" in
      specialize (store_typing_func_lookup H1 H2) as [ft Hft];
      unfold funcinst_typing in Hft
  | H1: store_typing ?s,
      H2: lookup_N (s_tables ?s) _ = Some _ |- _ =>
      let tabt := fresh "tabt" in
      let Htabt := fresh "Htabt" in
      specialize (store_typing_table_lookup H1 H2) as [tabt Htabt];
      unfold tableinst_typing in Htabt
  | H1: store_typing ?s,
      H2: lookup_N (s_mems ?s) _ = Some _ |- _ =>
      let mt := fresh "mt" in
      let Hmt := fresh "Hmt" in
      specialize (store_typing_mem_lookup H1 H2) as [mt Hmt];
      unfold meminst_typing in Hmt
  | H1: store_typing ?s,
      H2: lookup_N (s_globals ?s) _ = Some _ |- _ =>
      let gt := fresh "gt" in
      let Hgt := fresh "Hgt" in
      specialize (store_typing_global_lookup H1 H2) as [gt Hgt];
      unfold globalinst_typing in Hgt
  | H1: store_typing ?s,
      H2: lookup_N (s_elems ?s) _ = Some _ |- _ =>
      let et := fresh "et" in
      let Het := fresh "Het" in
      specialize (store_typing_elem_lookup H1 H2) as [et Het];
      unfold eleminst_typing in Het
  | H1: store_typing ?s,
      H2: lookup_N (s_datas ?s) _ = Some _ |- _ =>
      let dt := fresh "dt" in
      let Hdt := fresh "Hdt" in
      specialize (store_typing_data_lookup H1 H2) as [dt Hdt];
      unfold datainst_typing in Hdt
  end.

Ltac resolve_store_inst_lookup :=
  store_typing_lookup; inst_typing_lookup.

Ltac unfold_store_operations :=
  repeat match goal with
    | _: context [ stab_update _ _ _ _ ] |- _ =>
        unfold stab_update in *; remove_bools_options
    | _: context [ supdate_glob _ _ _ _ ] |- _ =>
        unfold supdate_glob, supdate_glob_s, sglob_ind, option_bind, option_map in *; remove_bools_options
    | _: context [ sglob_val _ _ ] |- _ =>
        unfold sglob_val, sglob, sglob_ind in *; remove_bools_options
    | _: context [ stab_elem _ _ ] |- _ =>
        unfold stab_elem in *; remove_bools_options
    | _: context [ stab_grow _ _ ] |- _ =>
        unfold stab_grow, growtable in *; remove_bools_options
    | _: context [ mem_grow _ _ ] |- _ =>
        unfold mem_grow in *; remove_bools_options
    | _: context [ stab _ _ ] |- _ =>
        unfold stab in *; remove_bools_options
    | _: context [ smem _ _ ] |- _ =>
        unfold smem in *; remove_bools_options
    | _: context [ smem_ind _ _ ] |- _ =>
        unfold smem_ind in *; remove_bools_options
    | _: context [ selem _ _ ] |- _ =>
        unfold selem in *; remove_bools_options
    | _: context [ sdata _ _ ] |- _ =>
        unfold sdata in *; remove_bools_options
    | _: context [ selem_drop _ _ _ ] |- _ =>
        unfold selem_drop, selem in *; remove_bools_options
    | _: context [ sdata_drop _ _ _ ] |- _ =>
        unfold sdata_drop, sdata in *; remove_bools_options
    end.

Ltac resolve_e_typing :=
  repeat lazymatch goal with
    | _ : _ |- e_typing _ _ nil (Tf _ _) =>
        apply et_empty
    | _ : _ |- e_typing _ _ _ (Tf ?x (?x ++ _)) =>
        apply et_weakening_empty_1
    | H : value_ref_typing ?s ?tabv = Some ?t |-
        e_typing ?s _ (cons ($V (VAL_ref ?tabv)) nil) (Tf ?ts1 _) =>
        try apply et_weakening_empty_1; apply et_value_typing => /=; rewrite H => //=
    | H : value_typing ?s ?v = Some ?t |-
        e_typing ?s _ (cons ($V ?v) nil) (Tf ?ts1 _) =>
        try apply et_weakening_empty_1; apply et_value_typing => //=
    | H : value_ref_typing ?s ?tabv = Some ?t |-
        e_typing ?s _ (cons ($V (VAL_ref ?tabv)) ?l) (Tf ?ts1 _) =>
        rewrite -(cat1s ($V (VAL_ref tabv)) l); apply et_composition' with (t2s := ts1 ++ [::T_ref t]); first by try apply et_weakening_empty_1; apply et_value_typing => /=; rewrite H => //=
    | H : value_typing ?s ?v = Some ?t |-
        e_typing ?s _ (cons ($V ?v) ?l) (Tf ?ts1 _) =>
        rewrite -(cat1s ($V v) l); apply et_composition' with (t2s := ts1 ++ [::t]); first by try apply et_weakening_empty_1; apply et_value_typing => //=
    | _ : value_typing ?s ?v = Some ?t |-
        e_typing ?s _ [::($V ?v)] (Tf ?ts1 _) =>
        try apply et_weakening_empty_1; try by apply et_value_typing; eauto => /=
    | _ : _ |- e_typing _ _ (cons ($VN ?x) _) (Tf _ _) =>
        replace ($VN x) with ($V (VAL_num x)); last done
    | _ : _ |- e_typing  _ _ (cons (vref_to_e ?x) _) (Tf _ _) =>
        replace (vref_to_e x) with ($V (VAL_ref x)); last done
    | _ : _ |- e_typing _ _ [:: $V _] (Tf nil _) =>
        try apply et_value_typing => //=
    | _ : _ |- e_typing _ _ [:: $V _] (Tf ?x ?y) =>
        try apply et_weakening_empty_1; first by apply et_value_typing => //= 
    | _ : _ |- e_typing _ _ (cons ($V (VAL_num ?v)) ?l) (Tf ?ts1 _) =>
        rewrite -(cat1s ($V (VAL_num v)) l); apply et_composition' with (t2s := ts1 ++ [::T_num (typeof_num v)]); eauto; first by try apply et_weakening_empty_1; apply et_value_typing; eauto => //=
    | _ : _ |- e_typing _ _ (v_to_e_list _) (Tf _ _) =>
        try apply et_values_typing => /=
    | H : is_true (const_list _) |- _ =>
        let vs := fresh "vs" in
        apply const_es_exists in H as [vs ->]; invert_e_typing
    | _ => unfold_store_operations
    end.
