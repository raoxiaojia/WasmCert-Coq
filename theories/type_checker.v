(** Wasm type checker **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)
Require Import common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import BinNat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import operations typing datatypes_properties.

Section Host.

Context `{hfc: host_function_class}.

Inductive checker_type_aux : Type :=
(* An artificial type that is the supremum of all types; used for consumption only. In future proposals, this can be removed when 1 exists in the lattice of types. *)
| CTA_any : checker_type_aux
| CTA_some : value_type -> checker_type_aux.

Scheme Equality for checker_type_aux.
Definition checker_type_aux_eqb v1 v2 := is_left (checker_type_aux_eq_dec v1 v2).
Definition eqchecker_type_auxP  : Equality.axiom checker_type_aux_eqb :=
  eq_dec_Equality_axiom checker_type_aux_eq_dec.

Canonical Structure checker_type_aux_eqMixin := EqMixin eqchecker_type_auxP.
Canonical Structure checker_type_aux_eqType :=
  Eval hnf in EqType checker_type_aux checker_type_aux_eqMixin.

(* Operand stack is stored with the top at the head of list -- in general, the reversed order is sensible, else computation later suffers from looking up at the tail of list by indices. *)
Inductive checker_type : Type :=
| CT_top_type : list value_type -> checker_type
| CT_type : list value_type -> checker_type
| CT_error : checker_type.

Definition checker_type_eq_dec : forall v1 v2 : checker_type, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition checker_type_eqb v1 v2 : bool := checker_type_eq_dec v1 v2.
Definition eqchecker_typeP : Equality.axiom checker_type_eqb :=
  eq_dec_Equality_axiom checker_type_eq_dec.

Canonical Structure checker_type_eqMixin := EqMixin eqchecker_typeP.
Canonical Structure checker_type_eqType := Eval hnf in EqType checker_type checker_type_eqMixin.

Definition to_ct_list (ts : seq value_type) : seq checker_type_aux :=
  map CTA_some ts.

(* The actual type needs to be a subtype of the type being consumed. *)
Definition ct_compat (t_cons: checker_type_aux) (t: value_type) : bool :=
  match t_cons with
  | CTA_any => true
  | CTA_some vt1 => t <t: vt1
  end.

Definition ct_list_compat (ts_cons: list checker_type_aux) (ts: list value_type) : bool :=
  all2 ct_compat ts_cons ts.

Definition ct_consumable (ts_cons : list checker_type_aux) (ts: list value_type) : bool :=
  (size ts_cons <= size ts) && (ct_list_compat ts_cons (take (size ts_cons) ts)).

Definition consume (t : checker_type) (ts_cons : seq checker_type_aux) : checker_type :=
  match t with
  | CT_type ts =>
    if ct_consumable ts_cons ts
    then CT_type (drop (size ts_cons) ts)
    else CT_error
  | CT_top_type cts =>
    if ct_consumable (take (size cts) ts_cons) cts
    then CT_top_type (drop (size ts_cons) cts) (* Drops cts to nil if oversized *)
    else CT_error
  | _ => CT_error
  end.

Definition produce (t t_prod : checker_type) : checker_type :=
  match (t, t_prod) with
  | (CT_top_type ts, CT_type ts') => CT_top_type (rev ts' ++ ts)
  | (CT_type ts, CT_type ts') => CT_type (rev ts' ++ ts)
  | (_, CT_top_type ts) => CT_top_type (rev ts)
  | _ => CT_error
  end.

(* Updating the value stack (reversed) by a consumed and produced value list (not reversed, due to how label types are defiend *)
Definition type_update (curr_type : checker_type) (ts_cons : seq checker_type_aux) (prods : checker_type) : checker_type :=
  produce (consume curr_type (rev ts_cons)) prods.

Definition select_return (vt1 vt2 : value_type) : checker_type :=
  match (vt1, vt2) with
  | (_, T_bot) => CT_type [::vt1]
  | (T_bot, _) => CT_type [::vt2]
  | (t1, t2) =>
    if is_numeric_type t1 && (t1 == t2)
    then CT_type [::t1]
    else CT_error
  end.

Definition type_update_select (t : checker_type) (ots: option (list value_type)) : checker_type :=
  match ots with
  | Some [::vt] => type_update t (to_ct_list [:: vt; vt; T_num T_i32]) (CT_type [:: vt])
  | Some _ => CT_error
  | None =>
      match t with
      | CT_type ts =>
          match ts with
          | t0 :: t1 :: t2 :: ts' =>
              if (is_numeric_type t1 && (t1 == t2))
              then (type_update (CT_type ts) [::CTA_any; CTA_some (T_num T_i32)]) (CT_type nil)
              else CT_error
          | _ => CT_error
          end
      | CT_top_type ts =>
          match ts with
          | nil => CT_top_type [::T_bot]
          | t0 :: nil => type_update (CT_top_type ts) [::CTA_some (T_num T_i32)] (CT_top_type [::T_bot])
          | t0 :: t1 :: nil =>
            (* The consumed type needs to be a numeric type; therefore we cannot simply just consume everything and produce an i32 here *)
              if is_numeric_type t0
              then type_update (CT_top_type ts) [::CTA_some (T_num T_i32)] (CT_type nil)
              else CT_error
          | t0 :: t1 :: t2 :: _ =>
              type_update (CT_top_type ts) [::CTA_any; CTA_any; CTA_some (T_num T_i32)]
                (select_return t1 t2)
          end
      | CT_error => CT_error
      end
  end.

Fixpoint same_lab_h (iss : seq tableidx) (lab_c : seq (seq value_type)) (ts : seq value_type) : option (seq value_type) :=
  match iss with
  | [::] => Some ts
  | i :: iss' =>
      match lookup_N lab_c i with
      | None => None
      | Some xx =>
          if xx == ts then same_lab_h iss' lab_c xx
          else None
      end
  end.

(**
   Br_table iss i needs to make sure that Br (each element in iss) and Br i would 
     consume the same type. See section 3.3.5.8 in the official spec.
**)
Definition same_lab (iss : seq tableidx) (lab_c : seq (seq value_type)) : option (seq value_type) :=
  match iss with
  | [::] => None
  | i :: iss' =>
      match lookup_N lab_c i with
      | Some xx => same_lab_h iss' lab_c xx
      | None => None
      end
  end.

Definition c_types_agree (ct : checker_type) (ts': seq value_type) : bool :=
  match ct with
  | CT_type ts => ts <ts: ts'
  | CT_top_type ts => ct_consumable (to_ct_list (take (size ts) ts')) ts
  | CT_error => false
  end.

Definition type_update_ref_is_null (ct : checker_type) : checker_type :=
  match ct with
  | CT_type ts =>
      match ts with
      | t :: _ =>
          if is_ref_t t
          then (type_update ct [::CTA_any] (CT_type [::T_num T_i32]))
          else CT_error
      | _ => CT_error
      end
  | CT_top_type ts =>
      match ts with
      | nil => CT_top_type [::T_num T_i32]
      | t :: _ =>
          if is_ref_t t
          then (type_update ct [::CTA_any] (CT_type [::T_num T_i32]))
          else CT_error
      end
  | CT_error => CT_error
  end.    

Fixpoint check_single (C : t_context) (ts : checker_type) (be : basic_instruction) : checker_type :=
  let b_e_type_checker (C : t_context) (es : list basic_instruction) (tf : function_type) : bool :=
    let: (Tf tn tm) := tf in
      c_types_agree (List.fold_left (check_single C) es (CT_type (rev tn))) (rev tm)
in
  if ts == CT_error then CT_error
  else
  match be with
  | BI_const_num v => type_update ts [::] (CT_type [::T_num (typeof_num v)])
  | BI_const_vec v => type_update ts [::] (CT_type [::T_vec (typeof_vec v)])
  | BI_ref_null t => type_update ts [::] (CT_type [::T_ref t])
  | BI_ref_is_null => type_update_ref_is_null ts
  | BI_ref_func x =>
      match lookup_N C.(tc_funcs) x with
      | Some _ =>
          if x \in C.(tc_refs)
          then type_update ts [::] (CT_type [::T_ref T_funcref])
          else CT_error
      | _ => CT_error
      end
  | BI_unop t op =>
    match op with
    | Unop_i _ => if is_int_t t
                  then type_update ts [::CTA_some (T_num t)] (CT_type [::T_num t])
                  else CT_error
    | Unop_f _ => if is_float_t t
                  then type_update ts [::CTA_some (T_num t)] (CT_type [::T_num t])
                  else CT_error
    | Unop_extend _ =>
        (* Technically, this needs to check validity of the extend arg; but such instruction can never arise from parsing *)
                  if is_int_t t
                  then type_update ts [::CTA_some (T_num t)] (CT_type [::T_num t])
                  else CT_error
    end
  | BI_binop t op =>
    match op with
    | Binop_i _ => if is_int_t t
                  then type_update ts [::CTA_some (T_num t); CTA_some (T_num t)] (CT_type [::(T_num t)])
                  else CT_error
    | Binop_f _ => if is_float_t t
                  then type_update ts [::CTA_some (T_num t); CTA_some (T_num t)] (CT_type [::(T_num t)])
                  else CT_error
    end
  | BI_testop t _ =>
    if is_int_t t
    then type_update ts [::CTA_some (T_num t)] (CT_type [::(T_num T_i32)])
    else CT_error
  | BI_relop t op =>
    match op with
    | Relop_i _ => if is_int_t t
                  then type_update ts [::CTA_some (T_num t); CTA_some (T_num t)] (CT_type [::(T_num T_i32)])
                  else CT_error
    | Relop_f _ => if is_float_t t
                  then type_update ts [::CTA_some (T_num t); CTA_some (T_num t)] (CT_type [::(T_num T_i32)])
                  else CT_error
    end
  | BI_cvtop t2 op t1 sx =>
    if cvtop_valid t2 op t1 sx
    then type_update ts [::CTA_some (T_num t1)] (CT_type [::(T_num t2)])
    else CT_error
  | BI_unreachable => type_update ts [::] (CT_top_type [::])
  | BI_nop => ts
  | BI_drop => type_update ts [::CTA_any] (CT_type [::])
  | BI_select ot => type_update_select ts ot
  | BI_block bt es =>
      match expand_t C bt with
      | Some (Tf tn tm) =>
          if b_e_type_checker (upd_label C ([::tm] ++ tc_labels C)) es (Tf tn tm)
          then type_update ts (to_ct_list tn) (CT_type tm)
          else CT_error
      | None => CT_error
      end
  | BI_loop bt es =>
      match expand_t C bt with
      | Some (Tf tn tm) =>
          if b_e_type_checker (upd_label C ([::tn] ++ tc_labels C)) es (Tf tn tm)
          then type_update ts (to_ct_list tn) (CT_type tm)
          else CT_error
      | None => CT_error
      end
  | BI_if bt es1 es2 =>
      match expand_t C bt with
      | Some (Tf tn tm) =>
          if b_e_type_checker (upd_label C ([::tm] ++ tc_labels C)) es1 (Tf tn tm)
             && b_e_type_checker (upd_label C ([::tm] ++ tc_labels C)) es2 (Tf tn tm)
          then type_update ts (to_ct_list (tn ++ [::(T_num T_i32)])) (CT_type tm)
          else CT_error
      | None => CT_error
      end
  | BI_br i =>
      match lookup_N (tc_labels C) i with
      | Some xx => type_update ts (to_ct_list xx) (CT_top_type [::])
      | None => CT_error 
      end
  | BI_br_if i =>
      match lookup_N (tc_labels C) i with
      | Some xx => type_update ts (to_ct_list (xx ++ [::(T_num T_i32)])) (CT_type xx)
      | None => CT_error 
      end
  | BI_br_table iss i =>
    match same_lab (iss ++ [::i]) (tc_labels C) with
    | None => CT_error
    | Some tls => type_update ts (to_ct_list (tls ++ [::(T_num T_i32)])) (CT_top_type [::])
    end
  | BI_return =>
    match tc_return C with
    | None => CT_error
    | Some tls => type_update ts (to_ct_list tls) (CT_top_type [::])
    end
  | BI_call x =>
      match lookup_N (tc_funcs C) x with
      | None => CT_error 
      | Some (Tf tn tm) =>
          type_update ts (to_ct_list tn) (CT_type tm)
      end
  | BI_call_indirect x y =>
      match lookup_N C.(tc_tables) x with
      | Some tabt =>
          if tabt.(tt_elem_type) == T_funcref then
            match lookup_N (tc_types C) y with
            | Some (Tf tn tm) =>
                type_update ts (to_ct_list (tn ++ [::(T_num T_i32)])) (CT_type tm)
            | None => CT_error 
            end
          else CT_error
      | None => CT_error
      end
  | BI_local_get i =>
      match lookup_N (tc_locals C) i with
      | None => CT_error 
      | Some xx => type_update ts [::] (CT_type [::xx])
      end
  | BI_local_set i =>
      match lookup_N (tc_locals C) i with
      | None => CT_error 
      | Some xx => type_update ts [::CTA_some xx] (CT_type [::])
      end
  | BI_local_tee i =>
      match lookup_N (tc_locals C) i with
      | None => CT_error 
      | Some xx => type_update ts [::CTA_some xx] (CT_type [::xx])
      end
  | BI_global_get i =>
      match lookup_N (tc_globals C) i with
      | None => CT_error 
      | Some xx => type_update ts [::] (CT_type [::tg_t xx])
      end
  | BI_global_set i =>
      match lookup_N (tc_globals C) i with
      | None => CT_error 
      | Some xx =>
          if is_mut xx
          then type_update ts [::CTA_some (tg_t xx)] (CT_type [::])
          else CT_error
      end
  | BI_table_get x =>
      match lookup_N (tc_tables C) x with
      | None => CT_error 
      | Some tabt =>
          type_update ts [::CTA_some (T_num T_i32)] (CT_type [::T_ref tabt.(tt_elem_type)])
      end
  | BI_table_set x =>
      match lookup_N (tc_tables C) x with
      | None => CT_error 
      | Some tabt =>
          type_update ts [::CTA_some (T_num T_i32); CTA_some (T_ref tabt.(tt_elem_type))] (CT_type nil)
      end
  | BI_table_size x =>
      match lookup_N (tc_tables C) x with
      | None => CT_error 
      | Some tabt =>
          type_update ts nil (CT_type [::T_num T_i32])
      end
  | BI_table_grow x =>
      match lookup_N (tc_tables C) x with
      | None => CT_error 
      | Some tabt =>
          type_update ts [::CTA_some (T_ref tabt.(tt_elem_type)); CTA_some (T_num T_i32)] (CT_type [::T_num T_i32])
      end
  | BI_table_fill x =>
      match lookup_N (tc_tables C) x with
      | None => CT_error 
      | Some tabt =>
          type_update ts [::CTA_some (T_num T_i32); CTA_some (T_ref tabt.(tt_elem_type)); CTA_some (T_num T_i32)] (CT_type nil)
      end
  | BI_table_copy x y =>
      match lookup_N (tc_tables C) x with
      | None => CT_error 
      | Some tabt1 =>
          match lookup_N (tc_tables C) y with
          | Some tabt2 =>
              if tabt1.(tt_elem_type) == tabt2.(tt_elem_type)
              then type_update ts [::CTA_some (T_num T_i32); CTA_some (T_num T_i32); CTA_some (T_num T_i32)] (CT_type nil)
              else CT_error
          | None => CT_error
          end
      end
  | BI_table_init x y =>
      match lookup_N (tc_tables C) x with
      | None => CT_error 
      | Some tabt =>
          match lookup_N (tc_elems C) y with
          | Some t =>
              if tabt.(tt_elem_type) == t
              then type_update ts [::CTA_some (T_num T_i32); CTA_some (T_num T_i32); CTA_some (T_num T_i32)] (CT_type nil)
              else CT_error
          | None => CT_error
          end
      end
  | BI_elem_drop x =>
      match lookup_N (tc_elems C) x with
      | None => CT_error 
      | Some tabt => ts
      end
  | BI_load t tp_sx a off =>
      match lookup_N C.(tc_mems) 0%N with
      | Some _ =>
          if load_store_t_bounds a (option_projl tp_sx) t
          then type_update ts [::CTA_some (T_num T_i32)] (CT_type [::T_num t])
          else CT_error
      | None => CT_error
      end
  | BI_store t tp a off =>
      match lookup_N C.(tc_mems) 0%N with
      | Some _ =>
          if load_store_t_bounds a tp t
          then type_update ts [::CTA_some (T_num T_i32); CTA_some (T_num t)] (CT_type [::])
          else CT_error
      | None => CT_error
      end
  | BI_memory_size =>
      match lookup_N C.(tc_mems) 0%N with
      | Some _ =>
          type_update ts [::] (CT_type [::(T_num T_i32)])
      | None => CT_error
      end
  | BI_memory_grow =>
      match lookup_N C.(tc_mems) 0%N with
      | Some _ =>
          type_update ts [::CTA_some (T_num T_i32)] (CT_type [::(T_num T_i32)])
      | None => CT_error
      end
  | BI_memory_fill =>
      match lookup_N C.(tc_mems) 0%N with
      | Some _ =>
          type_update ts [::CTA_some (T_num T_i32); CTA_some (T_num T_i32); CTA_some (T_num T_i32)] (CT_type nil)
      | None => CT_error
      end
  | BI_memory_copy =>
      match lookup_N C.(tc_mems) 0%N with
      | Some _ =>
          type_update ts [::CTA_some (T_num T_i32); CTA_some (T_num T_i32); CTA_some (T_num T_i32)] (CT_type nil)
      | None => CT_error
      end
  | BI_memory_init x =>
      match lookup_N C.(tc_mems) 0%N with
      | Some _ =>
          match lookup_N C.(tc_datas) x with
          | Some _ =>
              type_update ts [::CTA_some (T_num T_i32); CTA_some (T_num T_i32); CTA_some (T_num T_i32)] (CT_type nil)
          | None => CT_error
          end
      | None => CT_error
      end
  | BI_data_drop x =>
      match lookup_N C.(tc_datas) x with
      | Some _ => ts
      | None => CT_error
      end
  end.

Definition check (C : t_context) (es : list basic_instruction) (ts : checker_type): checker_type :=
  List.fold_left (check_single C) es ts.

Definition b_e_type_checker (C : t_context) (es : list basic_instruction) (tf : function_type) : bool :=
  let: (Tf tn tm) := tf in
  c_types_agree (List.fold_left (check_single C) es (CT_type (rev tn))) (rev tm).

End Host.
