(* !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export syntax_ott.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme typ_ind' := Induction for typ Sort Prop.

Definition typ_mutind :=
  fun H1 H2 H3 H4 H5 =>
  typ_ind' H1 H2 H3 H4 H5.

Scheme typ_rec' := Induction for typ Sort Set.

Definition typ_mutrec :=
  fun H1 H2 H3 H4 H5 =>
  typ_rec' H1 H2 H3 H4 H5.

Scheme exp_ind' := Induction for exp Sort Prop
  with value_ind' := Induction for value Sort Prop.

Definition exp_value_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 =>
  (conj (exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17)
  (value_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17)).

Scheme exp_rec' := Induction for exp Sort Set
  with value_rec' := Induction for value Sort Set.

Definition exp_value_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 =>
  (pair (exp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17)
  (value_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17)).


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_exp_wrt_exp_rec (n1 : nat) (x1 : var) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | e_var_f x2 => if (x1 == x2) then (e_var_b n1) else (e_var_f x2)
    | e_var_b n2 => if (lt_ge_dec n2 n1) then (e_var_b n2) else (e_var_b (S n2))
    | e_top => e_top
    | e_lit i1 => e_lit i1
    | e_abs e2 A1 B1 => e_abs (close_exp_wrt_exp_rec (S n1) x1 e2) A1 B1
    | e_fixpoint e2 A1 => e_fixpoint (close_exp_wrt_exp_rec (S n1) x1 e2) A1
    | e_app e2 e3 => e_app (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | e_merge e2 e3 => e_merge (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | e_anno e2 A1 => e_anno (close_exp_wrt_exp_rec n1 x1 e2) A1
    | e_val v1 => e_val (close_value_wrt_exp_rec n1 x1 v1)
  end

with close_value_wrt_exp_rec (n1 : nat) (x1 : var) (v1 : value) {struct v1} : value :=
  match v1 with
    | v_top => v_top
    | v_lit i1 => v_lit i1
    | v_topv v2 => v_topv (close_value_wrt_exp_rec n1 x1 v2)
    | v_absv e1 A1 B1 => v_absv (close_exp_wrt_exp_rec (S n1) x1 e1) A1 B1
    | v_merge v2 v3 => v_merge (close_value_wrt_exp_rec n1 x1 v2) (close_value_wrt_exp_rec n1 x1 v3)
  end.

Definition close_exp_wrt_exp x1 e1 := close_exp_wrt_exp_rec 0 x1 e1.

Definition close_value_wrt_exp x1 v1 := close_value_wrt_exp_rec 0 x1 v1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | t_int => 1
    | t_top => 1
    | t_arrow A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_and A2 B1 => 1 + (size_typ A2) + (size_typ B1)
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | e_var_f x1 => 1
    | e_var_b n1 => 1
    | e_top => 1
    | e_lit i1 => 1
    | e_abs e2 A1 B1 => 1 + (size_exp e2) + (size_typ A1) + (size_typ B1)
    | e_fixpoint e2 A1 => 1 + (size_exp e2) + (size_typ A1)
    | e_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | e_merge e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | e_anno e2 A1 => 1 + (size_exp e2) + (size_typ A1)
    | e_val v1 => 1 + (size_value v1)
  end

with size_value (v1 : value) {struct v1} : nat :=
  match v1 with
    | v_top => 1
    | v_lit i1 => 1
    | v_topv v2 => 1 + (size_value v2)
    | v_absv e1 A1 B1 => 1 + (size_exp e1) + (size_typ A1) + (size_typ B1)
    | v_merge v2 v3 => 1 + (size_value v2) + (size_value v3)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_exp_wrt_exp : nat -> exp -> Prop :=
  | degree_wrt_exp_e_var_f : forall n1 x1,
    degree_exp_wrt_exp n1 (e_var_f x1)
  | degree_wrt_exp_e_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_exp_wrt_exp n1 (e_var_b n2)
  | degree_wrt_exp_e_top : forall n1,
    degree_exp_wrt_exp n1 (e_top)
  | degree_wrt_exp_e_lit : forall n1 i1,
    degree_exp_wrt_exp n1 (e_lit i1)
  | degree_wrt_exp_e_abs : forall n1 e1 A1 B1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (e_abs e1 A1 B1)
  | degree_wrt_exp_e_fixpoint : forall n1 e1 A1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (e_fixpoint e1 A1)
  | degree_wrt_exp_e_app : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (e_app e1 e2)
  | degree_wrt_exp_e_merge : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (e_merge e1 e2)
  | degree_wrt_exp_e_anno : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_anno e1 A1)
  | degree_wrt_exp_e_val : forall n1 v1,
    degree_value_wrt_exp n1 v1 ->
    degree_exp_wrt_exp n1 (e_val v1)

with degree_value_wrt_exp : nat -> value -> Prop :=
  | degree_wrt_exp_v_top : forall n1,
    degree_value_wrt_exp n1 (v_top)
  | degree_wrt_exp_v_lit : forall n1 i1,
    degree_value_wrt_exp n1 (v_lit i1)
  | degree_wrt_exp_v_topv : forall n1 v1,
    degree_value_wrt_exp n1 v1 ->
    degree_value_wrt_exp n1 (v_topv v1)
  | degree_wrt_exp_v_absv : forall n1 e1 A1 B1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_value_wrt_exp n1 (v_absv e1 A1 B1)
  | degree_wrt_exp_v_merge : forall n1 v1 v2,
    degree_value_wrt_exp n1 v1 ->
    degree_value_wrt_exp n1 v2 ->
    degree_value_wrt_exp n1 (v_merge v1 v2).

Scheme degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop
  with degree_value_wrt_exp_ind' := Induction for degree_value_wrt_exp Sort Prop.

Definition degree_exp_wrt_exp_degree_value_wrt_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 =>
  (conj (degree_exp_wrt_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17)
  (degree_value_wrt_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17)).

Hint Constructors degree_exp_wrt_exp : core lngen.

Hint Constructors degree_value_wrt_exp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_exp : exp -> Set :=
  | lc_set_e_var_f : forall x1,
    lc_set_exp (e_var_f x1)
  | lc_set_e_top :
    lc_set_exp (e_top)
  | lc_set_e_lit : forall i1,
    lc_set_exp (e_lit i1)
  | lc_set_e_abs : forall e1 A1 B1,
    (forall x1 : var, lc_set_exp (open_exp_wrt_exp e1 (e_var_f x1))) ->
    lc_set_exp (e_abs e1 A1 B1)
  | lc_set_e_fixpoint : forall e1 A1,
    (forall x1 : var, lc_set_exp (open_exp_wrt_exp e1 (e_var_f x1))) ->
    lc_set_exp (e_fixpoint e1 A1)
  | lc_set_e_app : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (e_app e1 e2)
  | lc_set_e_merge : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (e_merge e1 e2)
  | lc_set_e_anno : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_exp (e_anno e1 A1)
  | lc_set_e_val : forall v1,
    lc_set_value v1 ->
    lc_set_exp (e_val v1)

with lc_set_value : value -> Set :=
  | lc_set_v_top :
    lc_set_value (v_top)
  | lc_set_v_lit : forall i1,
    lc_set_value (v_lit i1)
  | lc_set_v_topv : forall v1,
    lc_set_value v1 ->
    lc_set_value (v_topv v1)
  | lc_set_v_absv : forall e1 A1 B1,
    (forall x1 : var, lc_set_exp (open_exp_wrt_exp e1 (e_var_f x1))) ->
    lc_set_value (v_absv e1 A1 B1)
  | lc_set_v_merge : forall v1 v2,
    lc_set_value v1 ->
    lc_set_value v2 ->
    lc_set_value (v_merge v1 v2).

Scheme lc_exp_ind' := Induction for lc_exp Sort Prop
  with lc_value_ind' := Induction for lc_value Sort Prop.

Definition lc_exp_lc_value_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 =>
  (conj (lc_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)
  (lc_value_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)).

Scheme lc_set_exp_ind' := Induction for lc_set_exp Sort Prop
  with lc_set_value_ind' := Induction for lc_set_value Sort Prop.

Definition lc_set_exp_lc_set_value_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 =>
  (conj (lc_set_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)
  (lc_set_value_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)).

Scheme lc_set_exp_rec' := Induction for lc_set_exp Sort Set
  with lc_set_value_rec' := Induction for lc_set_value Sort Set.

Definition lc_set_exp_lc_set_value_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 =>
  (pair (lc_set_exp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)
  (lc_set_value_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)).

Hint Constructors lc_exp : core lngen.

Hint Constructors lc_value : core lngen.

Hint Constructors lc_set_exp : core lngen.

Hint Constructors lc_set_value : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_exp_wrt_exp e1 := forall x1, lc_exp (open_exp_wrt_exp e1 (e_var_f x1)).

Definition body_value_wrt_exp v1 := forall x1, lc_value (open_value_wrt_exp v1 (e_var_f x1)).

Hint Unfold body_exp_wrt_exp.

Hint Unfold body_value_wrt_exp.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

Hint Resolve @plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_typ_min_mutual :
(forall A1, 1 <= size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_typ_min :
forall A1, 1 <= size_typ A1.
Proof.
pose proof size_typ_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_min : lngen.

(* begin hide *)

Lemma size_exp_min_size_value_min_mutual :
(forall e1, 1 <= size_exp e1) /\
(forall v1, 1 <= size_value v1).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_exp_min :
forall e1, 1 <= size_exp e1.
Proof.
pose proof size_exp_min_size_value_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_min : lngen.

Lemma size_value_min :
forall v1, 1 <= size_value v1.
Proof.
pose proof size_exp_min_size_value_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_value_min : lngen.

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec_size_value_close_value_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1) /\
(forall v1 x1 n1,
  size_value (close_value_wrt_exp_rec n1 x1 v1) = size_value v1).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1.
Proof.
pose proof size_exp_close_exp_wrt_exp_rec_size_value_close_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_close_exp_wrt_exp_rec : lngen.
Hint Rewrite size_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_value_close_value_wrt_exp_rec :
forall v1 x1 n1,
  size_value (close_value_wrt_exp_rec n1 x1 v1) = size_value v1.
Proof.
pose proof size_exp_close_exp_wrt_exp_rec_size_value_close_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_value_close_value_wrt_exp_rec : lngen.
Hint Rewrite size_value_close_value_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_exp_close_exp_wrt_exp :
forall e1 x1,
  size_exp (close_exp_wrt_exp x1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve size_exp_close_exp_wrt_exp : lngen.
Hint Rewrite size_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma size_value_close_value_wrt_exp :
forall v1 x1,
  size_value (close_value_wrt_exp x1 v1) = size_value v1.
Proof.
unfold close_value_wrt_exp; default_simp.
Qed.

Hint Resolve size_value_close_value_wrt_exp : lngen.
Hint Rewrite size_value_close_value_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_size_value_open_value_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1)) /\
(forall v1 e1 n1,
  size_value v1 <= size_value (open_value_wrt_exp_rec n1 e1 v1)).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_size_value_open_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_value_open_value_wrt_exp_rec :
forall v1 e1 n1,
  size_value v1 <= size_value (open_value_wrt_exp_rec n1 e1 v1).
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_size_value_open_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_value_open_value_wrt_exp_rec : lngen.

(* end hide *)

Lemma size_exp_open_exp_wrt_exp :
forall e1 e2,
  size_exp e1 <= size_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp : lngen.

Lemma size_value_open_value_wrt_exp :
forall v1 e1,
  size_value v1 <= size_value (open_value_wrt_exp v1 e1).
Proof.
unfold open_value_wrt_exp; default_simp.
Qed.

Hint Resolve size_value_open_value_wrt_exp : lngen.

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var_size_value_open_value_wrt_exp_rec_var_mutual :
(forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (e_var_f x1) e1) = size_exp e1) /\
(forall v1 x1 n1,
  size_value (open_value_wrt_exp_rec n1 (e_var_f x1) v1) = size_value v1).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var :
forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (e_var_f x1) e1) = size_exp e1.
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_var_size_value_open_value_wrt_exp_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp_rec_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_exp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_value_open_value_wrt_exp_rec_var :
forall v1 x1 n1,
  size_value (open_value_wrt_exp_rec n1 (e_var_f x1) v1) = size_value v1.
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_var_size_value_open_value_wrt_exp_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_value_open_value_wrt_exp_rec_var : lngen.
Hint Rewrite size_value_open_value_wrt_exp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_exp_open_exp_wrt_exp_var :
forall e1 x1,
  size_exp (open_exp_wrt_exp e1 (e_var_f x1)) = size_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_exp_var using solve [auto] : lngen.

Lemma size_value_open_value_wrt_exp_var :
forall v1 x1,
  size_value (open_value_wrt_exp v1 (e_var_f x1)) = size_value v1.
Proof.
unfold open_value_wrt_exp; default_simp.
Qed.

Hint Resolve size_value_open_value_wrt_exp_var : lngen.
Hint Rewrite size_value_open_value_wrt_exp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_exp_wrt_exp_S_degree_value_wrt_exp_S_mutual :
(forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1) /\
(forall n1 v1,
  degree_value_wrt_exp n1 v1 ->
  degree_value_wrt_exp (S n1) v1).
Proof.
apply_mutual_ind degree_exp_wrt_exp_degree_value_wrt_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_S :
forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_S_degree_value_wrt_exp_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_S : lngen.

Lemma degree_value_wrt_exp_S :
forall n1 v1,
  degree_value_wrt_exp n1 v1 ->
  degree_value_wrt_exp (S n1) v1.
Proof.
pose proof degree_exp_wrt_exp_S_degree_value_wrt_exp_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_value_wrt_exp_S : lngen.

Lemma degree_exp_wrt_exp_O :
forall n1 e1,
  degree_exp_wrt_exp O e1 ->
  degree_exp_wrt_exp n1 e1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_O : lngen.

Lemma degree_value_wrt_exp_O :
forall n1 v1,
  degree_value_wrt_exp O v1 ->
  degree_value_wrt_exp n1 v1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_value_wrt_exp_O : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_degree_value_wrt_exp_close_value_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1)) /\
(forall v1 x1 n1,
  degree_value_wrt_exp n1 v1 ->
  degree_value_wrt_exp (S n1) (close_value_wrt_exp_rec n1 x1 v1)).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_degree_value_wrt_exp_close_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_value_wrt_exp_close_value_wrt_exp_rec :
forall v1 x1 n1,
  degree_value_wrt_exp n1 v1 ->
  degree_value_wrt_exp (S n1) (close_value_wrt_exp_rec n1 x1 v1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_degree_value_wrt_exp_close_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_value_wrt_exp_close_value_wrt_exp_rec : lngen.

(* end hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  degree_exp_wrt_exp 0 e1 ->
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp : lngen.

Lemma degree_value_wrt_exp_close_value_wrt_exp :
forall v1 x1,
  degree_value_wrt_exp 0 v1 ->
  degree_value_wrt_exp 1 (close_value_wrt_exp x1 v1).
Proof.
unfold close_value_wrt_exp; default_simp.
Qed.

Hint Resolve degree_value_wrt_exp_close_value_wrt_exp : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_degree_value_wrt_exp_close_value_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1) /\
(forall v1 x1 n1,
  degree_value_wrt_exp (S n1) (close_value_wrt_exp_rec n1 x1 v1) ->
  degree_value_wrt_exp n1 v1).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_degree_value_wrt_exp_close_value_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_value_wrt_exp_close_value_wrt_exp_rec_inv :
forall v1 x1 n1,
  degree_value_wrt_exp (S n1) (close_value_wrt_exp_rec n1 x1 v1) ->
  degree_value_wrt_exp n1 v1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_degree_value_wrt_exp_close_value_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_value_wrt_exp_close_value_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_inv :
forall e1 x1,
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_exp 0 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_inv : lngen.

Lemma degree_value_wrt_exp_close_value_wrt_exp_inv :
forall v1 x1,
  degree_value_wrt_exp 1 (close_value_wrt_exp x1 v1) ->
  degree_value_wrt_exp 0 v1.
Proof.
unfold close_value_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_value_wrt_exp_close_value_wrt_exp_inv : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_degree_value_wrt_exp_open_value_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1)) /\
(forall v1 e1 n1,
  degree_value_wrt_exp (S n1) v1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_value_wrt_exp n1 (open_value_wrt_exp_rec n1 e1 v1)).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_degree_value_wrt_exp_open_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_value_wrt_exp_open_value_wrt_exp_rec :
forall v1 e1 n1,
  degree_value_wrt_exp (S n1) v1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_value_wrt_exp n1 (open_value_wrt_exp_rec n1 e1 v1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_degree_value_wrt_exp_open_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_value_wrt_exp_open_value_wrt_exp_rec : lngen.

(* end hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp :
forall e1 e2,
  degree_exp_wrt_exp 1 e1 ->
  degree_exp_wrt_exp 0 e2 ->
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma degree_value_wrt_exp_open_value_wrt_exp :
forall v1 e1,
  degree_value_wrt_exp 1 v1 ->
  degree_exp_wrt_exp 0 e1 ->
  degree_value_wrt_exp 0 (open_value_wrt_exp v1 e1).
Proof.
unfold open_value_wrt_exp; default_simp.
Qed.

Hint Resolve degree_value_wrt_exp_open_value_wrt_exp : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_degree_value_wrt_exp_open_value_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1) /\
(forall v1 e1 n1,
  degree_value_wrt_exp n1 (open_value_wrt_exp_rec n1 e1 v1) ->
  degree_value_wrt_exp (S n1) v1).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_degree_value_wrt_exp_open_value_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_value_wrt_exp_open_value_wrt_exp_rec_inv :
forall v1 e1 n1,
  degree_value_wrt_exp n1 (open_value_wrt_exp_rec n1 e1 v1) ->
  degree_value_wrt_exp (S n1) v1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_degree_value_wrt_exp_open_value_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_value_wrt_exp_open_value_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_inv :
forall e1 e2,
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_exp 1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_inv : lngen.

Lemma degree_value_wrt_exp_open_value_wrt_exp_inv :
forall v1 e1,
  degree_value_wrt_exp 0 (open_value_wrt_exp v1 e1) ->
  degree_value_wrt_exp 1 v1.
Proof.
unfold open_value_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_value_wrt_exp_open_value_wrt_exp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj_close_value_wrt_exp_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2) /\
(forall v1 v2 x1 n1,
  close_value_wrt_exp_rec n1 x1 v1 = close_value_wrt_exp_rec n1 x1 v2 ->
  v1 = v2).
Proof.
apply_mutual_ind exp_value_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj :
forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_exp_wrt_exp_rec_inj_close_value_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_value_wrt_exp_rec_inj :
forall v1 v2 x1 n1,
  close_value_wrt_exp_rec n1 x1 v1 = close_value_wrt_exp_rec n1 x1 v2 ->
  v1 = v2.
Proof.
pose proof close_exp_wrt_exp_rec_inj_close_value_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_value_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma close_exp_wrt_exp_inj :
forall e1 e2 x1,
  close_exp_wrt_exp x1 e1 = close_exp_wrt_exp x1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate close_exp_wrt_exp_inj : lngen.

Lemma close_value_wrt_exp_inj :
forall v1 v2 x1,
  close_value_wrt_exp x1 v1 = close_value_wrt_exp x1 v2 ->
  v1 = v2.
Proof.
unfold close_value_wrt_exp; eauto with lngen.
Qed.

Hint Immediate close_value_wrt_exp_inj : lngen.

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_close_value_wrt_exp_rec_open_value_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (e_var_f x1) e1) = e1) /\
(forall v1 x1 n1,
  x1 `notin` fv_value v1 ->
  close_value_wrt_exp_rec n1 x1 (open_value_wrt_exp_rec n1 (e_var_f x1) v1) = v1).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 x1 n1,
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (e_var_f x1) e1) = e1.
Proof.
pose proof close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_close_value_wrt_exp_rec_open_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.
Hint Rewrite close_exp_wrt_exp_rec_open_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_value_wrt_exp_rec_open_value_wrt_exp_rec :
forall v1 x1 n1,
  x1 `notin` fv_value v1 ->
  close_value_wrt_exp_rec n1 x1 (open_value_wrt_exp_rec n1 (e_var_f x1) v1) = v1.
Proof.
pose proof close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_close_value_wrt_exp_rec_open_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_value_wrt_exp_rec_open_value_wrt_exp_rec : lngen.
Hint Rewrite close_value_wrt_exp_rec_open_value_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 x1,
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp x1 (open_exp_wrt_exp e1 (e_var_f x1)) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve close_exp_wrt_exp_open_exp_wrt_exp : lngen.
Hint Rewrite close_exp_wrt_exp_open_exp_wrt_exp using solve [auto] : lngen.

Lemma close_value_wrt_exp_open_value_wrt_exp :
forall v1 x1,
  x1 `notin` fv_value v1 ->
  close_value_wrt_exp x1 (open_value_wrt_exp v1 (e_var_f x1)) = v1.
Proof.
unfold close_value_wrt_exp; unfold open_value_wrt_exp; default_simp.
Qed.

Hint Resolve close_value_wrt_exp_open_value_wrt_exp : lngen.
Hint Rewrite close_value_wrt_exp_open_value_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_open_value_wrt_exp_rec_close_value_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (e_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1) /\
(forall v1 x1 n1,
  open_value_wrt_exp_rec n1 (e_var_f x1) (close_value_wrt_exp_rec n1 x1 v1) = v1).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (e_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1.
Proof.
pose proof open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_open_value_wrt_exp_rec_close_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_exp_rec_close_exp_wrt_exp_rec : lngen.
Hint Rewrite open_exp_wrt_exp_rec_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_value_wrt_exp_rec_close_value_wrt_exp_rec :
forall v1 x1 n1,
  open_value_wrt_exp_rec n1 (e_var_f x1) (close_value_wrt_exp_rec n1 x1 v1) = v1.
Proof.
pose proof open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_open_value_wrt_exp_rec_close_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_value_wrt_exp_rec_close_value_wrt_exp_rec : lngen.
Hint Rewrite open_value_wrt_exp_rec_close_value_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  open_exp_wrt_exp (close_exp_wrt_exp x1 e1) (e_var_f x1) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve open_exp_wrt_exp_close_exp_wrt_exp : lngen.
Hint Rewrite open_exp_wrt_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma open_value_wrt_exp_close_value_wrt_exp :
forall v1 x1,
  open_value_wrt_exp (close_value_wrt_exp x1 v1) (e_var_f x1) = v1.
Proof.
unfold close_value_wrt_exp; unfold open_value_wrt_exp; default_simp.
Qed.

Hint Resolve open_value_wrt_exp_close_value_wrt_exp : lngen.
Hint Rewrite open_value_wrt_exp_close_value_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj_open_value_wrt_exp_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` fv_exp e2 ->
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp_rec n1 (e_var_f x1) e2 = open_exp_wrt_exp_rec n1 (e_var_f x1) e1 ->
  e2 = e1) /\
(forall v2 v1 x1 n1,
  x1 `notin` fv_value v2 ->
  x1 `notin` fv_value v1 ->
  open_value_wrt_exp_rec n1 (e_var_f x1) v2 = open_value_wrt_exp_rec n1 (e_var_f x1) v1 ->
  v2 = v1).
Proof.
apply_mutual_ind exp_value_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` fv_exp e2 ->
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp_rec n1 (e_var_f x1) e2 = open_exp_wrt_exp_rec n1 (e_var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_exp_wrt_exp_rec_inj_open_value_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_value_wrt_exp_rec_inj :
forall v2 v1 x1 n1,
  x1 `notin` fv_value v2 ->
  x1 `notin` fv_value v1 ->
  open_value_wrt_exp_rec n1 (e_var_f x1) v2 = open_value_wrt_exp_rec n1 (e_var_f x1) v1 ->
  v2 = v1.
Proof.
pose proof open_exp_wrt_exp_rec_inj_open_value_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_value_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma open_exp_wrt_exp_inj :
forall e2 e1 x1,
  x1 `notin` fv_exp e2 ->
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp e2 (e_var_f x1) = open_exp_wrt_exp e1 (e_var_f x1) ->
  e2 = e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate open_exp_wrt_exp_inj : lngen.

Lemma open_value_wrt_exp_inj :
forall v2 v1 x1,
  x1 `notin` fv_value v2 ->
  x1 `notin` fv_value v1 ->
  open_value_wrt_exp v2 (e_var_f x1) = open_value_wrt_exp v1 (e_var_f x1) ->
  v2 = v1.
Proof.
unfold open_value_wrt_exp; eauto with lngen.
Qed.

Hint Immediate open_value_wrt_exp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_of_lc_exp_degree_value_wrt_exp_of_lc_value_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1) /\
(forall v1,
  lc_value v1 ->
  degree_value_wrt_exp 0 v1).
Proof.
apply_mutual_ind lc_exp_lc_value_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1.
Proof.
pose proof degree_exp_wrt_exp_of_lc_exp_degree_value_wrt_exp_of_lc_value_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_of_lc_exp : lngen.

Lemma degree_value_wrt_exp_of_lc_value :
forall v1,
  lc_value v1 ->
  degree_value_wrt_exp 0 v1.
Proof.
pose proof degree_exp_wrt_exp_of_lc_exp_degree_value_wrt_exp_of_lc_value_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_value_wrt_exp_of_lc_value : lngen.

(* begin hide *)

Lemma lc_exp_of_degree_lc_value_of_degree_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1) /\
(forall v1,
  size_value v1 = i1 ->
  degree_value_wrt_exp 0 v1 ->
  lc_value v1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind exp_value_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_exp_of_degree :
forall e1,
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1.
Proof.
intros e1; intros;
pose proof (lc_exp_of_degree_lc_value_of_degree_size_mutual (size_exp e1));
intuition eauto.
Qed.

Hint Resolve lc_exp_of_degree : lngen.

Lemma lc_value_of_degree :
forall v1,
  degree_value_wrt_exp 0 v1 ->
  lc_value v1.
Proof.
intros v1; intros;
pose proof (lc_exp_of_degree_lc_value_of_degree_size_mutual (size_value v1));
intuition eauto.
Qed.

Hint Resolve lc_value_of_degree : lngen.

Ltac typ_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac exp_value_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_exp_wrt_exp_of_lc_exp in J1; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_value_wrt_exp_of_lc_value in J1; clear H
          end).

Lemma lc_e_abs_exists :
forall x1 e1 A1 B1,
  lc_exp (open_exp_wrt_exp e1 (e_var_f x1)) ->
  lc_exp (e_abs e1 A1 B1).
Proof.
intros; exp_value_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_e_fixpoint_exists :
forall x1 e1 A1,
  lc_exp (open_exp_wrt_exp e1 (e_var_f x1)) ->
  lc_exp (e_fixpoint e1 A1).
Proof.
intros; exp_value_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_v_absv_exists :
forall x1 e1 A1 B1,
  lc_exp (open_exp_wrt_exp e1 (e_var_f x1)) ->
  lc_value (v_absv e1 A1 B1).
Proof.
intros; exp_value_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_exp (e_abs _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_e_abs_exists x1).

Hint Extern 1 (lc_exp (e_fixpoint _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_e_fixpoint_exists x1).

Hint Extern 1 (lc_value (v_absv _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_v_absv_exists x1).

Lemma lc_body_exp_wrt_exp :
forall e1 e2,
  body_exp_wrt_exp e1 ->
  lc_exp e2 ->
  lc_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold body_exp_wrt_exp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
exp_value_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_exp_wrt_exp : lngen.

Lemma lc_body_value_wrt_exp :
forall v1 e1,
  body_value_wrt_exp v1 ->
  lc_exp e1 ->
  lc_value (open_value_wrt_exp v1 e1).
Proof.
unfold body_value_wrt_exp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
exp_value_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_value_wrt_exp : lngen.

Lemma lc_body_e_abs_1 :
forall e1 A1 B1,
  lc_exp (e_abs e1 A1 B1) ->
  body_exp_wrt_exp e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_e_abs_1 : lngen.

Lemma lc_body_e_fixpoint_1 :
forall e1 A1,
  lc_exp (e_fixpoint e1 A1) ->
  body_exp_wrt_exp e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_e_fixpoint_1 : lngen.

Lemma lc_body_v_absv_1 :
forall e1 A1 B1,
  lc_value (v_absv e1 A1 B1) ->
  body_exp_wrt_exp e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_v_absv_1 : lngen.

(* begin hide *)

Lemma lc_exp_unique_lc_value_unique_mutual :
(forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3) /\
(forall v1 (proof2 proof3 : lc_value v1), proof2 = proof3).
Proof.
apply_mutual_ind lc_exp_lc_value_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_exp_unique :
forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3.
Proof.
pose proof lc_exp_unique_lc_value_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_exp_unique : lngen.

Lemma lc_value_unique :
forall v1 (proof2 proof3 : lc_value v1), proof2 = proof3.
Proof.
pose proof lc_exp_unique_lc_value_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_value_unique : lngen.

(* begin hide *)

Lemma lc_exp_of_lc_set_exp_lc_value_of_lc_set_value_mutual :
(forall e1, lc_set_exp e1 -> lc_exp e1) /\
(forall v1, lc_set_value v1 -> lc_value v1).
Proof.
apply_mutual_ind lc_set_exp_lc_set_value_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_exp_of_lc_set_exp :
forall e1, lc_set_exp e1 -> lc_exp e1.
Proof.
pose proof lc_exp_of_lc_set_exp_lc_value_of_lc_set_value_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_exp_of_lc_set_exp : lngen.

Lemma lc_value_of_lc_set_value :
forall v1, lc_set_value v1 -> lc_value v1.
Proof.
pose proof lc_exp_of_lc_set_exp_lc_value_of_lc_set_value_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_value_of_lc_set_value : lngen.

(* begin hide *)

Lemma lc_set_exp_of_lc_exp_lc_set_value_of_lc_value_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  lc_exp e1 ->
  lc_set_exp e1) *
(forall v1,
  size_value v1 = i1 ->
  lc_value v1 ->
  lc_set_value v1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind exp_value_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_exp_of_lc_exp
 | apply lc_set_value_of_lc_value
 | apply lc_set_typ_of_lc_typ
 | apply lc_set_exp_of_lc_exp
 | apply lc_set_value_of_lc_value];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  lc_set_exp e1.
Proof.
intros e1; intros;
pose proof (lc_set_exp_of_lc_exp_lc_set_value_of_lc_value_size_mutual (size_exp e1));
intuition eauto.
Qed.

Hint Resolve lc_set_exp_of_lc_exp : lngen.

Lemma lc_set_value_of_lc_value :
forall v1,
  lc_value v1 ->
  lc_set_value v1.
Proof.
intros v1; intros;
pose proof (lc_set_exp_of_lc_exp_lc_set_value_of_lc_value_size_mutual (size_value v1));
intuition eauto.
Qed.

Hint Resolve lc_set_value_of_lc_value : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp_close_value_wrt_exp_rec_degree_value_wrt_exp_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1) /\
(forall v1 x1 n1,
  degree_value_wrt_exp n1 v1 ->
  x1 `notin` fv_value v1 ->
  close_value_wrt_exp_rec n1 x1 v1 = v1).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1.
Proof.
pose proof close_exp_wrt_exp_rec_degree_exp_wrt_exp_close_value_wrt_exp_rec_degree_value_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
Hint Rewrite close_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_value_wrt_exp_rec_degree_value_wrt_exp :
forall v1 x1 n1,
  degree_value_wrt_exp n1 v1 ->
  x1 `notin` fv_value v1 ->
  close_value_wrt_exp_rec n1 x1 v1 = v1.
Proof.
pose proof close_exp_wrt_exp_rec_degree_exp_wrt_exp_close_value_wrt_exp_rec_degree_value_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve close_value_wrt_exp_rec_degree_value_wrt_exp : lngen.
Hint Rewrite close_value_wrt_exp_rec_degree_value_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma close_exp_wrt_exp_lc_exp :
forall e1 x1,
  lc_exp e1 ->
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp x1 e1 = e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve close_exp_wrt_exp_lc_exp : lngen.
Hint Rewrite close_exp_wrt_exp_lc_exp using solve [auto] : lngen.

Lemma close_value_wrt_exp_lc_value :
forall v1 x1,
  lc_value v1 ->
  x1 `notin` fv_value v1 ->
  close_value_wrt_exp x1 v1 = v1.
Proof.
unfold close_value_wrt_exp; default_simp.
Qed.

Hint Resolve close_value_wrt_exp_lc_value : lngen.
Hint Rewrite close_value_wrt_exp_lc_value using solve [auto] : lngen.

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp_open_value_wrt_exp_rec_degree_value_wrt_exp_mutual :
(forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2) /\
(forall v1 e1 n1,
  degree_value_wrt_exp n1 v1 ->
  open_value_wrt_exp_rec n1 e1 v1 = v1).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2.
Proof.
pose proof open_exp_wrt_exp_rec_degree_exp_wrt_exp_open_value_wrt_exp_rec_degree_value_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
Hint Rewrite open_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_value_wrt_exp_rec_degree_value_wrt_exp :
forall v1 e1 n1,
  degree_value_wrt_exp n1 v1 ->
  open_value_wrt_exp_rec n1 e1 v1 = v1.
Proof.
pose proof open_exp_wrt_exp_rec_degree_exp_wrt_exp_open_value_wrt_exp_rec_degree_value_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve open_value_wrt_exp_rec_degree_value_wrt_exp : lngen.
Hint Rewrite open_value_wrt_exp_rec_degree_value_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma open_exp_wrt_exp_lc_exp :
forall e2 e1,
  lc_exp e2 ->
  open_exp_wrt_exp e2 e1 = e2.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve open_exp_wrt_exp_lc_exp : lngen.
Hint Rewrite open_exp_wrt_exp_lc_exp using solve [auto] : lngen.

Lemma open_value_wrt_exp_lc_value :
forall v1 e1,
  lc_value v1 ->
  open_value_wrt_exp v1 e1 = v1.
Proof.
unfold open_value_wrt_exp; default_simp.
Qed.

Hint Resolve open_value_wrt_exp_lc_value : lngen.
Hint Rewrite open_value_wrt_exp_lc_value using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_exp_close_exp_wrt_exp_rec_fv_value_close_value_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  fv_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (fv_exp e1)) /\
(forall v1 x1 n1,
  fv_value (close_value_wrt_exp_rec n1 x1 v1) [=] remove x1 (fv_value v1)).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  fv_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (fv_exp e1).
Proof.
pose proof fv_exp_close_exp_wrt_exp_rec_fv_value_close_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_close_exp_wrt_exp_rec : lngen.
Hint Rewrite fv_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_value_close_value_wrt_exp_rec :
forall v1 x1 n1,
  fv_value (close_value_wrt_exp_rec n1 x1 v1) [=] remove x1 (fv_value v1).
Proof.
pose proof fv_exp_close_exp_wrt_exp_rec_fv_value_close_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_value_close_value_wrt_exp_rec : lngen.
Hint Rewrite fv_value_close_value_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_exp_close_exp_wrt_exp :
forall e1 x1,
  fv_exp (close_exp_wrt_exp x1 e1) [=] remove x1 (fv_exp e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve fv_exp_close_exp_wrt_exp : lngen.
Hint Rewrite fv_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma fv_value_close_value_wrt_exp :
forall v1 x1,
  fv_value (close_value_wrt_exp x1 v1) [=] remove x1 (fv_value v1).
Proof.
unfold close_value_wrt_exp; default_simp.
Qed.

Hint Resolve fv_value_close_value_wrt_exp : lngen.
Hint Rewrite fv_value_close_value_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma fv_exp_open_exp_wrt_exp_rec_lower_fv_value_open_value_wrt_exp_rec_lower_mutual :
(forall e1 e2 n1,
  fv_exp e1 [<=] fv_exp (open_exp_wrt_exp_rec n1 e2 e1)) /\
(forall v1 e1 n1,
  fv_value v1 [<=] fv_value (open_value_wrt_exp_rec n1 e1 v1)).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  fv_exp e1 [<=] fv_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof fv_exp_open_exp_wrt_exp_rec_lower_fv_value_open_value_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_value_open_value_wrt_exp_rec_lower :
forall v1 e1 n1,
  fv_value v1 [<=] fv_value (open_value_wrt_exp_rec n1 e1 v1).
Proof.
pose proof fv_exp_open_exp_wrt_exp_rec_lower_fv_value_open_value_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_value_open_value_wrt_exp_rec_lower : lngen.

(* end hide *)

Lemma fv_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  fv_exp e1 [<=] fv_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve fv_exp_open_exp_wrt_exp_lower : lngen.

Lemma fv_value_open_value_wrt_exp_lower :
forall v1 e1,
  fv_value v1 [<=] fv_value (open_value_wrt_exp v1 e1).
Proof.
unfold open_value_wrt_exp; default_simp.
Qed.

Hint Resolve fv_value_open_value_wrt_exp_lower : lngen.

(* begin hide *)

Lemma fv_exp_open_exp_wrt_exp_rec_upper_fv_value_open_value_wrt_exp_rec_upper_mutual :
(forall e1 e2 n1,
  fv_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] fv_exp e2 `union` fv_exp e1) /\
(forall v1 e1 n1,
  fv_value (open_value_wrt_exp_rec n1 e1 v1) [<=] fv_exp e1 `union` fv_value v1).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  fv_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] fv_exp e2 `union` fv_exp e1.
Proof.
pose proof fv_exp_open_exp_wrt_exp_rec_upper_fv_value_open_value_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_value_open_value_wrt_exp_rec_upper :
forall v1 e1 n1,
  fv_value (open_value_wrt_exp_rec n1 e1 v1) [<=] fv_exp e1 `union` fv_value v1.
Proof.
pose proof fv_exp_open_exp_wrt_exp_rec_upper_fv_value_open_value_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_value_open_value_wrt_exp_rec_upper : lngen.

(* end hide *)

Lemma fv_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  fv_exp (open_exp_wrt_exp e1 e2) [<=] fv_exp e2 `union` fv_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve fv_exp_open_exp_wrt_exp_upper : lngen.

Lemma fv_value_open_value_wrt_exp_upper :
forall v1 e1,
  fv_value (open_value_wrt_exp v1 e1) [<=] fv_exp e1 `union` fv_value v1.
Proof.
unfold open_value_wrt_exp; default_simp.
Qed.

Hint Resolve fv_value_open_value_wrt_exp_upper : lngen.

(* begin hide *)

Lemma fv_exp_subst_exp_fresh_fv_value_subst_value_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` fv_exp e1 ->
  fv_exp (subst_exp e2 x1 e1) [=] fv_exp e1) /\
(forall v1 e1 x1,
  x1 `notin` fv_value v1 ->
  fv_value (subst_value e1 x1 v1) [=] fv_value v1).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_subst_exp_fresh :
forall e1 e2 x1,
  x1 `notin` fv_exp e1 ->
  fv_exp (subst_exp e2 x1 e1) [=] fv_exp e1.
Proof.
pose proof fv_exp_subst_exp_fresh_fv_value_subst_value_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_subst_exp_fresh : lngen.
Hint Rewrite fv_exp_subst_exp_fresh using solve [auto] : lngen.

Lemma fv_value_subst_value_fresh :
forall v1 e1 x1,
  x1 `notin` fv_value v1 ->
  fv_value (subst_value e1 x1 v1) [=] fv_value v1.
Proof.
pose proof fv_exp_subst_exp_fresh_fv_value_subst_value_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_value_subst_value_fresh : lngen.
Hint Rewrite fv_value_subst_value_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_exp_subst_exp_lower_fv_value_subst_value_lower_mutual :
(forall e1 e2 x1,
  remove x1 (fv_exp e1) [<=] fv_exp (subst_exp e2 x1 e1)) /\
(forall v1 e1 x1,
  remove x1 (fv_value v1) [<=] fv_value (subst_value e1 x1 v1)).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_subst_exp_lower :
forall e1 e2 x1,
  remove x1 (fv_exp e1) [<=] fv_exp (subst_exp e2 x1 e1).
Proof.
pose proof fv_exp_subst_exp_lower_fv_value_subst_value_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_subst_exp_lower : lngen.

Lemma fv_value_subst_value_lower :
forall v1 e1 x1,
  remove x1 (fv_value v1) [<=] fv_value (subst_value e1 x1 v1).
Proof.
pose proof fv_exp_subst_exp_lower_fv_value_subst_value_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_value_subst_value_lower : lngen.

(* begin hide *)

Lemma fv_exp_subst_exp_notin_fv_value_subst_value_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` fv_exp e1 ->
  x2 `notin` fv_exp e2 ->
  x2 `notin` fv_exp (subst_exp e2 x1 e1)) /\
(forall v1 e1 x1 x2,
  x2 `notin` fv_value v1 ->
  x2 `notin` fv_exp e1 ->
  x2 `notin` fv_value (subst_value e1 x1 v1)).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_subst_exp_notin :
forall e1 e2 x1 x2,
  x2 `notin` fv_exp e1 ->
  x2 `notin` fv_exp e2 ->
  x2 `notin` fv_exp (subst_exp e2 x1 e1).
Proof.
pose proof fv_exp_subst_exp_notin_fv_value_subst_value_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_subst_exp_notin : lngen.

Lemma fv_value_subst_value_notin :
forall v1 e1 x1 x2,
  x2 `notin` fv_value v1 ->
  x2 `notin` fv_exp e1 ->
  x2 `notin` fv_value (subst_value e1 x1 v1).
Proof.
pose proof fv_exp_subst_exp_notin_fv_value_subst_value_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_value_subst_value_notin : lngen.

(* begin hide *)

Lemma fv_exp_subst_exp_upper_fv_value_subst_value_upper_mutual :
(forall e1 e2 x1,
  fv_exp (subst_exp e2 x1 e1) [<=] fv_exp e2 `union` remove x1 (fv_exp e1)) /\
(forall v1 e1 x1,
  fv_value (subst_value e1 x1 v1) [<=] fv_exp e1 `union` remove x1 (fv_value v1)).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_subst_exp_upper :
forall e1 e2 x1,
  fv_exp (subst_exp e2 x1 e1) [<=] fv_exp e2 `union` remove x1 (fv_exp e1).
Proof.
pose proof fv_exp_subst_exp_upper_fv_value_subst_value_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_subst_exp_upper : lngen.

Lemma fv_value_subst_value_upper :
forall v1 e1 x1,
  fv_value (subst_value e1 x1 v1) [<=] fv_exp e1 `union` remove x1 (fv_value v1).
Proof.
pose proof fv_exp_subst_exp_upper_fv_value_subst_value_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_value_subst_value_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_exp_close_exp_wrt_exp_rec_subst_value_close_value_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_exp e1 ->
  subst_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_exp e1 x1 e2)) /\
(forall v1 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_exp e1 ->
  subst_value e1 x1 (close_value_wrt_exp_rec n1 x2 v1) = close_value_wrt_exp_rec n1 x2 (subst_value e1 x1 v1)).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_close_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_exp e1 ->
  subst_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_exp e1 x1 e2).
Proof.
pose proof subst_exp_close_exp_wrt_exp_rec_subst_value_close_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_close_exp_wrt_exp_rec : lngen.

Lemma subst_value_close_value_wrt_exp_rec :
forall v1 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_exp e1 ->
  subst_value e1 x1 (close_value_wrt_exp_rec n1 x2 v1) = close_value_wrt_exp_rec n1 x2 (subst_value e1 x1 v1).
Proof.
pose proof subst_exp_close_exp_wrt_exp_rec_subst_value_close_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_value_close_value_wrt_exp_rec : lngen.

Lemma subst_exp_close_exp_wrt_exp :
forall e2 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` fv_exp e1 ->
  subst_exp e1 x1 (close_exp_wrt_exp x2 e2) = close_exp_wrt_exp x2 (subst_exp e1 x1 e2).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_close_exp_wrt_exp : lngen.

Lemma subst_value_close_value_wrt_exp :
forall v1 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` fv_exp e1 ->
  subst_value e1 x1 (close_value_wrt_exp x2 v1) = close_value_wrt_exp x2 (subst_value e1 x1 v1).
Proof.
unfold close_value_wrt_exp; default_simp.
Qed.

Hint Resolve subst_value_close_value_wrt_exp : lngen.

(* begin hide *)

Lemma subst_exp_degree_exp_wrt_exp_subst_value_degree_value_wrt_exp_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_exp e2 x1 e1)) /\
(forall v1 e1 x1 n1,
  degree_value_wrt_exp n1 v1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_value_wrt_exp n1 (subst_value e1 x1 v1)).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_degree_exp_wrt_exp :
forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_exp e2 x1 e1).
Proof.
pose proof subst_exp_degree_exp_wrt_exp_subst_value_degree_value_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_degree_exp_wrt_exp : lngen.

Lemma subst_value_degree_value_wrt_exp :
forall v1 e1 x1 n1,
  degree_value_wrt_exp n1 v1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_value_wrt_exp n1 (subst_value e1 x1 v1).
Proof.
pose proof subst_exp_degree_exp_wrt_exp_subst_value_degree_value_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_value_degree_value_wrt_exp : lngen.

(* begin hide *)

Lemma subst_exp_fresh_eq_subst_value_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_exp e2 ->
  subst_exp e1 x1 e2 = e2) /\
(forall v1 e1 x1,
  x1 `notin` fv_value v1 ->
  subst_value e1 x1 v1 = v1).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fv_exp e2 ->
  subst_exp e1 x1 e2 = e2.
Proof.
pose proof subst_exp_fresh_eq_subst_value_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_fresh_eq : lngen.
Hint Rewrite subst_exp_fresh_eq using solve [auto] : lngen.

Lemma subst_value_fresh_eq :
forall v1 e1 x1,
  x1 `notin` fv_value v1 ->
  subst_value e1 x1 v1 = v1.
Proof.
pose proof subst_exp_fresh_eq_subst_value_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_value_fresh_eq : lngen.
Hint Rewrite subst_value_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_fresh_same_subst_value_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_exp (subst_exp e1 x1 e2)) /\
(forall v1 e1 x1,
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_value (subst_value e1 x1 v1)).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_fresh_same :
forall e2 e1 x1,
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_exp (subst_exp e1 x1 e2).
Proof.
pose proof subst_exp_fresh_same_subst_value_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_fresh_same : lngen.

Lemma subst_value_fresh_same :
forall v1 e1 x1,
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_value (subst_value e1 x1 v1).
Proof.
pose proof subst_exp_fresh_same_subst_value_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_value_fresh_same : lngen.

(* begin hide *)

Lemma subst_exp_fresh_subst_value_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` fv_exp e2 ->
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_exp (subst_exp e1 x2 e2)) /\
(forall v1 e1 x1 x2,
  x1 `notin` fv_value v1 ->
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_value (subst_value e1 x2 v1)).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fv_exp e2 ->
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_exp (subst_exp e1 x2 e2).
Proof.
pose proof subst_exp_fresh_subst_value_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_fresh : lngen.

Lemma subst_value_fresh :
forall v1 e1 x1 x2,
  x1 `notin` fv_value v1 ->
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_value (subst_value e1 x2 v1).
Proof.
pose proof subst_exp_fresh_subst_value_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_value_fresh : lngen.

Lemma subst_exp_lc_exp :
forall e1 e2 x1,
  lc_exp e1 ->
  lc_exp e2 ->
  lc_exp (subst_exp e2 x1 e1).
Proof.
default_simp.
Qed.

Hint Resolve subst_exp_lc_exp : lngen.

Lemma subst_value_lc_value :
forall v1 e1 x1,
  lc_value v1 ->
  lc_exp e1 ->
  lc_value (subst_value e1 x1 v1).
Proof.
default_simp.
Qed.

Hint Resolve subst_value_lc_value : lngen.

(* begin hide *)

Lemma subst_exp_open_exp_wrt_exp_rec_subst_value_open_value_wrt_exp_rec_mutual :
(forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (subst_exp e1 x1 e2) (subst_exp e1 x1 e3)) /\
(forall v1 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_value e1 x1 (open_value_wrt_exp_rec n1 e2 v1) = open_value_wrt_exp_rec n1 (subst_exp e1 x1 e2) (subst_value e1 x1 v1)).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_open_exp_wrt_exp_rec :
forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (subst_exp e1 x1 e2) (subst_exp e1 x1 e3).
Proof.
pose proof subst_exp_open_exp_wrt_exp_rec_subst_value_open_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_value_open_value_wrt_exp_rec :
forall v1 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_value e1 x1 (open_value_wrt_exp_rec n1 e2 v1) = open_value_wrt_exp_rec n1 (subst_exp e1 x1 e2) (subst_value e1 x1 v1).
Proof.
pose proof subst_exp_open_exp_wrt_exp_rec_subst_value_open_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_value_open_value_wrt_exp_rec : lngen.

(* end hide *)

Lemma subst_exp_open_exp_wrt_exp :
forall e3 e1 e2 x1,
  lc_exp e1 ->
  subst_exp e1 x1 (open_exp_wrt_exp e3 e2) = open_exp_wrt_exp (subst_exp e1 x1 e3) (subst_exp e1 x1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_open_exp_wrt_exp : lngen.

Lemma subst_value_open_value_wrt_exp :
forall v1 e1 e2 x1,
  lc_exp e1 ->
  subst_value e1 x1 (open_value_wrt_exp v1 e2) = open_value_wrt_exp (subst_value e1 x1 v1) (subst_exp e1 x1 e2).
Proof.
unfold open_value_wrt_exp; default_simp.
Qed.

Hint Resolve subst_value_open_value_wrt_exp : lngen.

Lemma subst_exp_open_exp_wrt_exp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_exp e1 ->
  open_exp_wrt_exp (subst_exp e1 x1 e2) (e_var_f x2) = subst_exp e1 x1 (open_exp_wrt_exp e2 (e_var_f x2)).
Proof.
intros; rewrite subst_exp_open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_open_exp_wrt_exp_var : lngen.

Lemma subst_value_open_value_wrt_exp_var :
forall v1 e1 x1 x2,
  x1 <> x2 ->
  lc_exp e1 ->
  open_value_wrt_exp (subst_value e1 x1 v1) (e_var_f x2) = subst_value e1 x1 (open_value_wrt_exp v1 (e_var_f x2)).
Proof.
intros; rewrite subst_value_open_value_wrt_exp; default_simp.
Qed.

Hint Resolve subst_value_open_value_wrt_exp_var : lngen.

(* begin hide *)

Lemma subst_exp_spec_rec_subst_value_spec_rec_mutual :
(forall e1 e2 x1 n1,
  subst_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1)) /\
(forall v1 e1 x1 n1,
  subst_value e1 x1 v1 = open_value_wrt_exp_rec n1 e1 (close_value_wrt_exp_rec n1 x1 v1)).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_spec_rec :
forall e1 e2 x1 n1,
  subst_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof subst_exp_spec_rec_subst_value_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_value_spec_rec :
forall v1 e1 x1 n1,
  subst_value e1 x1 v1 = open_value_wrt_exp_rec n1 e1 (close_value_wrt_exp_rec n1 x1 v1).
Proof.
pose proof subst_exp_spec_rec_subst_value_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_value_spec_rec : lngen.

(* end hide *)

Lemma subst_exp_spec :
forall e1 e2 x1,
  subst_exp e2 x1 e1 = open_exp_wrt_exp (close_exp_wrt_exp x1 e1) e2.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_spec : lngen.

Lemma subst_value_spec :
forall v1 e1 x1,
  subst_value e1 x1 v1 = open_value_wrt_exp (close_value_wrt_exp x1 v1) e1.
Proof.
unfold close_value_wrt_exp; unfold open_value_wrt_exp; default_simp.
Qed.

Hint Resolve subst_value_spec : lngen.

(* begin hide *)

Lemma subst_exp_subst_exp_subst_value_subst_value_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` fv_exp e2 ->
  x2 <> x1 ->
  subst_exp e2 x1 (subst_exp e3 x2 e1) = subst_exp (subst_exp e2 x1 e3) x2 (subst_exp e2 x1 e1)) /\
(forall v1 e1 e2 x2 x1,
  x2 `notin` fv_exp e1 ->
  x2 <> x1 ->
  subst_value e1 x1 (subst_value e2 x2 v1) = subst_value (subst_exp e1 x1 e2) x2 (subst_value e1 x1 v1)).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_subst_exp :
forall e1 e2 e3 x2 x1,
  x2 `notin` fv_exp e2 ->
  x2 <> x1 ->
  subst_exp e2 x1 (subst_exp e3 x2 e1) = subst_exp (subst_exp e2 x1 e3) x2 (subst_exp e2 x1 e1).
Proof.
pose proof subst_exp_subst_exp_subst_value_subst_value_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_subst_exp : lngen.

Lemma subst_value_subst_value :
forall v1 e1 e2 x2 x1,
  x2 `notin` fv_exp e1 ->
  x2 <> x1 ->
  subst_value e1 x1 (subst_value e2 x2 v1) = subst_value (subst_exp e1 x1 e2) x2 (subst_value e1 x1 v1).
Proof.
pose proof subst_exp_subst_exp_subst_value_subst_value_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_value_subst_value : lngen.

(* begin hide *)

Lemma subst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_subst_value_close_value_wrt_exp_rec_open_value_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` fv_exp e2 ->
  x2 `notin` fv_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_exp e1 x1 (open_exp_wrt_exp_rec n1 (e_var_f x2) e2))) *
(forall v1 e1 x1 x2 n1,
  x2 `notin` fv_value v1 ->
  x2 `notin` fv_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_value e1 x1 v1 = close_value_wrt_exp_rec n1 x2 (subst_value e1 x1 (open_value_wrt_exp_rec n1 (e_var_f x2) v1))).
Proof.
apply_mutual_ind exp_value_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` fv_exp e2 ->
  x2 `notin` fv_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_exp e1 x1 (open_exp_wrt_exp_rec n1 (e_var_f x2) e2)).
Proof.
pose proof subst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_subst_value_close_value_wrt_exp_rec_open_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_value_close_value_wrt_exp_rec_open_value_wrt_exp_rec :
forall v1 e1 x1 x2 n1,
  x2 `notin` fv_value v1 ->
  x2 `notin` fv_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_value e1 x1 v1 = close_value_wrt_exp_rec n1 x2 (subst_value e1 x1 (open_value_wrt_exp_rec n1 (e_var_f x2) v1)).
Proof.
pose proof subst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_subst_value_close_value_wrt_exp_rec_open_value_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_value_close_value_wrt_exp_rec_open_value_wrt_exp_rec : lngen.

(* end hide *)

Lemma subst_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e2 e1 x1 x2,
  x2 `notin` fv_exp e2 ->
  x2 `notin` fv_exp e1 ->
  x2 <> x1 ->
  lc_exp e1 ->
  subst_exp e1 x1 e2 = close_exp_wrt_exp x2 (subst_exp e1 x1 (open_exp_wrt_exp e2 (e_var_f x2))).
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma subst_value_close_value_wrt_exp_open_value_wrt_exp :
forall v1 e1 x1 x2,
  x2 `notin` fv_value v1 ->
  x2 `notin` fv_exp e1 ->
  x2 <> x1 ->
  lc_exp e1 ->
  subst_value e1 x1 v1 = close_value_wrt_exp x2 (subst_value e1 x1 (open_value_wrt_exp v1 (e_var_f x2))).
Proof.
unfold close_value_wrt_exp; unfold open_value_wrt_exp; default_simp.
Qed.

Hint Resolve subst_value_close_value_wrt_exp_open_value_wrt_exp : lngen.

Lemma subst_exp_e_abs :
forall x2 e2 A1 B1 e1 x1,
  lc_exp e1 ->
  x2 `notin` fv_exp e1 `union` fv_exp e2 `union` singleton x1 ->
  subst_exp e1 x1 (e_abs e2 A1 B1) = e_abs (close_exp_wrt_exp x2 (subst_exp e1 x1 (open_exp_wrt_exp e2 (e_var_f x2)))) (A1) (B1).
Proof.
default_simp.
Qed.

Hint Resolve subst_exp_e_abs : lngen.

Lemma subst_exp_e_fixpoint :
forall x2 e2 A1 e1 x1,
  lc_exp e1 ->
  x2 `notin` fv_exp e1 `union` fv_exp e2 `union` singleton x1 ->
  subst_exp e1 x1 (e_fixpoint e2 A1) = e_fixpoint (close_exp_wrt_exp x2 (subst_exp e1 x1 (open_exp_wrt_exp e2 (e_var_f x2)))) (A1).
Proof.
default_simp.
Qed.

Hint Resolve subst_exp_e_fixpoint : lngen.

Lemma subst_value_v_absv :
forall x2 e2 A1 B1 e1 x1,
  lc_exp e1 ->
  x2 `notin` fv_exp e1 `union` fv_exp e2 `union` singleton x1 ->
  subst_value e1 x1 (v_absv e2 A1 B1) = v_absv (close_exp_wrt_exp x2 (subst_exp e1 x1 (open_exp_wrt_exp e2 (e_var_f x2)))) (A1) (B1).
Proof.
default_simp.
Qed.

Hint Resolve subst_value_v_absv : lngen.

(* begin hide *)

Lemma subst_exp_intro_rec_subst_value_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = subst_exp e2 x1 (open_exp_wrt_exp_rec n1 (e_var_f x1) e1)) /\
(forall v1 x1 e1 n1,
  x1 `notin` fv_value v1 ->
  open_value_wrt_exp_rec n1 e1 v1 = subst_value e1 x1 (open_value_wrt_exp_rec n1 (e_var_f x1) v1)).
Proof.
apply_mutual_ind exp_value_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = subst_exp e2 x1 (open_exp_wrt_exp_rec n1 (e_var_f x1) e1).
Proof.
pose proof subst_exp_intro_rec_subst_value_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_intro_rec : lngen.
Hint Rewrite subst_exp_intro_rec using solve [auto] : lngen.

Lemma subst_value_intro_rec :
forall v1 x1 e1 n1,
  x1 `notin` fv_value v1 ->
  open_value_wrt_exp_rec n1 e1 v1 = subst_value e1 x1 (open_value_wrt_exp_rec n1 (e_var_f x1) v1).
Proof.
pose proof subst_exp_intro_rec_subst_value_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_value_intro_rec : lngen.
Hint Rewrite subst_value_intro_rec using solve [auto] : lngen.

Lemma subst_exp_intro :
forall x1 e1 e2,
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp e1 e2 = subst_exp e2 x1 (open_exp_wrt_exp e1 (e_var_f x1)).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_intro : lngen.

Lemma subst_value_intro :
forall x1 v1 e1,
  x1 `notin` fv_value v1 ->
  open_value_wrt_exp v1 e1 = subst_value e1 x1 (open_value_wrt_exp v1 (e_var_f x1)).
Proof.
unfold open_value_wrt_exp; default_simp.
Qed.

Hint Resolve subst_value_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
