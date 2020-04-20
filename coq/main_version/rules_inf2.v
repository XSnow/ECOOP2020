Require Import Coq.Arith.Wf_nat.
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

Scheme dexp_ind' := Induction for dexp Sort Prop.

Definition dexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  dexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme dexp_rec' := Induction for dexp Sort Set.

Definition dexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  dexp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_dexp_wrt_dexp_rec (n1 : nat) (x1 : var) (ee1 : dexp) {struct ee1} : dexp :=
  match ee1 with
    | de_var_f x2 => if (x1 == x2) then (de_var_b n1) else (de_var_f x2)
    | de_var_b n2 => if (lt_ge_dec n2 n1) then (de_var_b n2) else (de_var_b (S n2))
    | de_top => de_top
    | de_lit i1 => de_lit i1
    | de_abs ee2 => de_abs (close_dexp_wrt_dexp_rec (S n1) x1 ee2)
    | de_app ee2 ee3 => de_app (close_dexp_wrt_dexp_rec n1 x1 ee2) (close_dexp_wrt_dexp_rec n1 x1 ee3)
    | de_merge ee2 ee3 => de_merge (close_dexp_wrt_dexp_rec n1 x1 ee2) (close_dexp_wrt_dexp_rec n1 x1 ee3)
    | de_fixpoint ee2 => de_fixpoint (close_dexp_wrt_dexp_rec (S n1) x1 ee2)
  end.

Definition close_dexp_wrt_dexp x1 ee1 := close_dexp_wrt_dexp_rec 0 x1 ee1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_dexp (ee1 : dexp) {struct ee1} : nat :=
  match ee1 with
    | de_var_f x1 => 1
    | de_var_b n1 => 1
    | de_top => 1
    | de_lit i1 => 1
    | de_abs ee2 => 1 + (size_dexp ee2)
    | de_app ee2 ee3 => 1 + (size_dexp ee2) + (size_dexp ee3)
    | de_merge ee2 ee3 => 1 + (size_dexp ee2) + (size_dexp ee3)
    | de_fixpoint ee2 => 1 + (size_dexp ee2)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_dexp_wrt_dexp : nat -> dexp -> Prop :=
  | degree_wrt_dexp_de_var_f : forall n1 x1,
    degree_dexp_wrt_dexp n1 (de_var_f x1)
  | degree_wrt_dexp_de_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_dexp_wrt_dexp n1 (de_var_b n2)
  | degree_wrt_dexp_de_top : forall n1,
    degree_dexp_wrt_dexp n1 (de_top)
  | degree_wrt_dexp_de_lit : forall n1 i1,
    degree_dexp_wrt_dexp n1 (de_lit i1)
  | degree_wrt_dexp_de_abs : forall n1 ee1,
    degree_dexp_wrt_dexp (S n1) ee1 ->
    degree_dexp_wrt_dexp n1 (de_abs ee1)
  | degree_wrt_dexp_de_app : forall n1 ee1 ee2,
    degree_dexp_wrt_dexp n1 ee1 ->
    degree_dexp_wrt_dexp n1 ee2 ->
    degree_dexp_wrt_dexp n1 (de_app ee1 ee2)
  | degree_wrt_dexp_de_merge : forall n1 ee1 ee2,
    degree_dexp_wrt_dexp n1 ee1 ->
    degree_dexp_wrt_dexp n1 ee2 ->
    degree_dexp_wrt_dexp n1 (de_merge ee1 ee2)
  | degree_wrt_dexp_de_fixpoint : forall n1 ee1,
    degree_dexp_wrt_dexp (S n1) ee1 ->
    degree_dexp_wrt_dexp n1 (de_fixpoint ee1).

Scheme degree_dexp_wrt_dexp_ind' := Induction for degree_dexp_wrt_dexp Sort Prop.

Definition degree_dexp_wrt_dexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  degree_dexp_wrt_dexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Hint Constructors degree_dexp_wrt_dexp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_dexp : dexp -> Set :=
  | lc_set_de_var_f : forall x1,
    lc_set_dexp (de_var_f x1)
  | lc_set_de_top :
    lc_set_dexp (de_top)
  | lc_set_de_lit : forall i1,
    lc_set_dexp (de_lit i1)
  | lc_set_de_abs : forall ee1,
    (forall x1 : var, lc_set_dexp (open_dexp_wrt_dexp ee1 (de_var_f x1))) ->
    lc_set_dexp (de_abs ee1)
  | lc_set_de_app : forall ee1 ee2,
    lc_set_dexp ee1 ->
    lc_set_dexp ee2 ->
    lc_set_dexp (de_app ee1 ee2)
  | lc_set_de_merge : forall ee1 ee2,
    lc_set_dexp ee1 ->
    lc_set_dexp ee2 ->
    lc_set_dexp (de_merge ee1 ee2)
  | lc_set_de_fixpoint : forall ee1,
    (forall x1 : var, lc_set_dexp (open_dexp_wrt_dexp ee1 (de_var_f x1))) ->
    lc_set_dexp (de_fixpoint ee1).

Scheme lc_dexp_ind' := Induction for lc_dexp Sort Prop.

Definition lc_dexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  lc_dexp_ind' H1 H2 H3 H4 H5 H6 H7 H8.

Scheme lc_set_dexp_ind' := Induction for lc_set_dexp Sort Prop.

Definition lc_set_dexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  lc_set_dexp_ind' H1 H2 H3 H4 H5 H6 H7 H8.

Scheme lc_set_dexp_rec' := Induction for lc_set_dexp Sort Set.

Definition lc_set_dexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  lc_set_dexp_rec' H1 H2 H3 H4 H5 H6 H7 H8.

Hint Constructors lc_dexp : core lngen.

Hint Constructors lc_set_dexp : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_dexp_wrt_dexp ee1 := forall x1, lc_dexp (open_dexp_wrt_dexp ee1 (de_var_f x1)).

Hint Unfold body_dexp_wrt_dexp : core.


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

Lemma size_dexp_min_mutual :
(forall ee1, 1 <= size_dexp ee1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_dexp_min :
forall ee1, 1 <= size_dexp ee1.
Proof.
pose proof size_dexp_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dexp_min : lngen.

(* begin hide *)

Lemma size_dexp_close_dexp_wrt_dexp_rec_mutual :
(forall ee1 x1 n1,
  size_dexp (close_dexp_wrt_dexp_rec n1 x1 ee1) = size_dexp ee1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dexp_close_dexp_wrt_dexp_rec :
forall ee1 x1 n1,
  size_dexp (close_dexp_wrt_dexp_rec n1 x1 ee1) = size_dexp ee1.
Proof.
pose proof size_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dexp_close_dexp_wrt_dexp_rec : lngen.
Hint Rewrite size_dexp_close_dexp_wrt_dexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_dexp_close_dexp_wrt_dexp :
forall ee1 x1,
  size_dexp (close_dexp_wrt_dexp x1 ee1) = size_dexp ee1.
Proof.
unfold close_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve size_dexp_close_dexp_wrt_dexp : lngen.
Hint Rewrite size_dexp_close_dexp_wrt_dexp using solve [auto] : lngen.

(* begin hide *)

Lemma size_dexp_open_dexp_wrt_dexp_rec_mutual :
(forall ee1 ee2 n1,
  size_dexp ee1 <= size_dexp (open_dexp_wrt_dexp_rec n1 ee2 ee1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dexp_open_dexp_wrt_dexp_rec :
forall ee1 ee2 n1,
  size_dexp ee1 <= size_dexp (open_dexp_wrt_dexp_rec n1 ee2 ee1).
Proof.
pose proof size_dexp_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dexp_open_dexp_wrt_dexp_rec : lngen.

(* end hide *)

Lemma size_dexp_open_dexp_wrt_dexp :
forall ee1 ee2,
  size_dexp ee1 <= size_dexp (open_dexp_wrt_dexp ee1 ee2).
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve size_dexp_open_dexp_wrt_dexp : lngen.

(* begin hide *)

Lemma size_dexp_open_dexp_wrt_dexp_rec_var_mutual :
(forall ee1 x1 n1,
  size_dexp (open_dexp_wrt_dexp_rec n1 (de_var_f x1) ee1) = size_dexp ee1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dexp_open_dexp_wrt_dexp_rec_var :
forall ee1 x1 n1,
  size_dexp (open_dexp_wrt_dexp_rec n1 (de_var_f x1) ee1) = size_dexp ee1.
Proof.
pose proof size_dexp_open_dexp_wrt_dexp_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dexp_open_dexp_wrt_dexp_rec_var : lngen.
Hint Rewrite size_dexp_open_dexp_wrt_dexp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_dexp_open_dexp_wrt_dexp_var :
forall ee1 x1,
  size_dexp (open_dexp_wrt_dexp ee1 (de_var_f x1)) = size_dexp ee1.
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve size_dexp_open_dexp_wrt_dexp_var : lngen.
Hint Rewrite size_dexp_open_dexp_wrt_dexp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_dexp_wrt_dexp_S_mutual :
(forall n1 ee1,
  degree_dexp_wrt_dexp n1 ee1 ->
  degree_dexp_wrt_dexp (S n1) ee1).
Proof.
apply_mutual_ind degree_dexp_wrt_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_dexp_wrt_dexp_S :
forall n1 ee1,
  degree_dexp_wrt_dexp n1 ee1 ->
  degree_dexp_wrt_dexp (S n1) ee1.
Proof.
pose proof degree_dexp_wrt_dexp_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dexp_wrt_dexp_S : lngen.

Lemma degree_dexp_wrt_dexp_O :
forall n1 ee1,
  degree_dexp_wrt_dexp O ee1 ->
  degree_dexp_wrt_dexp n1 ee1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_dexp_wrt_dexp_O : lngen.

(* begin hide *)

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_mutual :
(forall ee1 x1 n1,
  degree_dexp_wrt_dexp n1 ee1 ->
  degree_dexp_wrt_dexp (S n1) (close_dexp_wrt_dexp_rec n1 x1 ee1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec :
forall ee1 x1 n1,
  degree_dexp_wrt_dexp n1 ee1 ->
  degree_dexp_wrt_dexp (S n1) (close_dexp_wrt_dexp_rec n1 x1 ee1).
Proof.
pose proof degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec : lngen.

(* end hide *)

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dexp :
forall ee1 x1,
  degree_dexp_wrt_dexp 0 ee1 ->
  degree_dexp_wrt_dexp 1 (close_dexp_wrt_dexp x1 ee1).
Proof.
unfold close_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve degree_dexp_wrt_dexp_close_dexp_wrt_dexp : lngen.

(* begin hide *)

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_inv_mutual :
(forall ee1 x1 n1,
  degree_dexp_wrt_dexp (S n1) (close_dexp_wrt_dexp_rec n1 x1 ee1) ->
  degree_dexp_wrt_dexp n1 ee1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_inv :
forall ee1 x1 n1,
  degree_dexp_wrt_dexp (S n1) (close_dexp_wrt_dexp_rec n1 x1 ee1) ->
  degree_dexp_wrt_dexp n1 ee1.
Proof.
pose proof degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_inv : lngen.

(* end hide *)

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dexp_inv :
forall ee1 x1,
  degree_dexp_wrt_dexp 1 (close_dexp_wrt_dexp x1 ee1) ->
  degree_dexp_wrt_dexp 0 ee1.
Proof.
unfold close_dexp_wrt_dexp; eauto with lngen.
Qed.

Hint Immediate degree_dexp_wrt_dexp_close_dexp_wrt_dexp_inv : lngen.

(* begin hide *)

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_mutual :
(forall ee1 ee2 n1,
  degree_dexp_wrt_dexp (S n1) ee1 ->
  degree_dexp_wrt_dexp n1 ee2 ->
  degree_dexp_wrt_dexp n1 (open_dexp_wrt_dexp_rec n1 ee2 ee1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec :
forall ee1 ee2 n1,
  degree_dexp_wrt_dexp (S n1) ee1 ->
  degree_dexp_wrt_dexp n1 ee2 ->
  degree_dexp_wrt_dexp n1 (open_dexp_wrt_dexp_rec n1 ee2 ee1).
Proof.
pose proof degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec : lngen.

(* end hide *)

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dexp :
forall ee1 ee2,
  degree_dexp_wrt_dexp 1 ee1 ->
  degree_dexp_wrt_dexp 0 ee2 ->
  degree_dexp_wrt_dexp 0 (open_dexp_wrt_dexp ee1 ee2).
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve degree_dexp_wrt_dexp_open_dexp_wrt_dexp : lngen.

(* begin hide *)

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_inv_mutual :
(forall ee1 ee2 n1,
  degree_dexp_wrt_dexp n1 (open_dexp_wrt_dexp_rec n1 ee2 ee1) ->
  degree_dexp_wrt_dexp (S n1) ee1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_inv :
forall ee1 ee2 n1,
  degree_dexp_wrt_dexp n1 (open_dexp_wrt_dexp_rec n1 ee2 ee1) ->
  degree_dexp_wrt_dexp (S n1) ee1.
Proof.
pose proof degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_inv : lngen.

(* end hide *)

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dexp_inv :
forall ee1 ee2,
  degree_dexp_wrt_dexp 0 (open_dexp_wrt_dexp ee1 ee2) ->
  degree_dexp_wrt_dexp 1 ee1.
Proof.
unfold open_dexp_wrt_dexp; eauto with lngen.
Qed.

Hint Immediate degree_dexp_wrt_dexp_open_dexp_wrt_dexp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_dexp_wrt_dexp_rec_inj_mutual :
(forall ee1 ee2 x1 n1,
  close_dexp_wrt_dexp_rec n1 x1 ee1 = close_dexp_wrt_dexp_rec n1 x1 ee2 ->
  ee1 = ee2).
Proof.
apply_mutual_ind dexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dexp_wrt_dexp_rec_inj :
forall ee1 ee2 x1 n1,
  close_dexp_wrt_dexp_rec n1 x1 ee1 = close_dexp_wrt_dexp_rec n1 x1 ee2 ->
  ee1 = ee2.
Proof.
pose proof close_dexp_wrt_dexp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_dexp_wrt_dexp_rec_inj : lngen.

(* end hide *)

Lemma close_dexp_wrt_dexp_inj :
forall ee1 ee2 x1,
  close_dexp_wrt_dexp x1 ee1 = close_dexp_wrt_dexp x1 ee2 ->
  ee1 = ee2.
Proof.
unfold close_dexp_wrt_dexp; eauto with lngen.
Qed.

Hint Immediate close_dexp_wrt_dexp_inj : lngen.

(* begin hide *)

Lemma close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec_mutual :
(forall ee1 x1 n1,
  x1 `notin` fv_dexp ee1 ->
  close_dexp_wrt_dexp_rec n1 x1 (open_dexp_wrt_dexp_rec n1 (de_var_f x1) ee1) = ee1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec :
forall ee1 x1 n1,
  x1 `notin` fv_dexp ee1 ->
  close_dexp_wrt_dexp_rec n1 x1 (open_dexp_wrt_dexp_rec n1 (de_var_f x1) ee1) = ee1.
Proof.
pose proof close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec : lngen.
Hint Rewrite close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_dexp_wrt_dexp_open_dexp_wrt_dexp :
forall ee1 x1,
  x1 `notin` fv_dexp ee1 ->
  close_dexp_wrt_dexp x1 (open_dexp_wrt_dexp ee1 (de_var_f x1)) = ee1.
Proof.
unfold close_dexp_wrt_dexp; unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve close_dexp_wrt_dexp_open_dexp_wrt_dexp : lngen.
Hint Rewrite close_dexp_wrt_dexp_open_dexp_wrt_dexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_dexp_wrt_dexp_rec_close_dexp_wrt_dexp_rec_mutual :
(forall ee1 x1 n1,
  open_dexp_wrt_dexp_rec n1 (de_var_f x1) (close_dexp_wrt_dexp_rec n1 x1 ee1) = ee1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dexp_wrt_dexp_rec_close_dexp_wrt_dexp_rec :
forall ee1 x1 n1,
  open_dexp_wrt_dexp_rec n1 (de_var_f x1) (close_dexp_wrt_dexp_rec n1 x1 ee1) = ee1.
Proof.
pose proof open_dexp_wrt_dexp_rec_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_dexp_wrt_dexp_rec_close_dexp_wrt_dexp_rec : lngen.
Hint Rewrite open_dexp_wrt_dexp_rec_close_dexp_wrt_dexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_dexp_wrt_dexp_close_dexp_wrt_dexp :
forall ee1 x1,
  open_dexp_wrt_dexp (close_dexp_wrt_dexp x1 ee1) (de_var_f x1) = ee1.
Proof.
unfold close_dexp_wrt_dexp; unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve open_dexp_wrt_dexp_close_dexp_wrt_dexp : lngen.
Hint Rewrite open_dexp_wrt_dexp_close_dexp_wrt_dexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_dexp_wrt_dexp_rec_inj_mutual :
(forall ee2 ee1 x1 n1,
  x1 `notin` fv_dexp ee2 ->
  x1 `notin` fv_dexp ee1 ->
  open_dexp_wrt_dexp_rec n1 (de_var_f x1) ee2 = open_dexp_wrt_dexp_rec n1 (de_var_f x1) ee1 ->
  ee2 = ee1).
Proof.
apply_mutual_ind dexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dexp_wrt_dexp_rec_inj :
forall ee2 ee1 x1 n1,
  x1 `notin` fv_dexp ee2 ->
  x1 `notin` fv_dexp ee1 ->
  open_dexp_wrt_dexp_rec n1 (de_var_f x1) ee2 = open_dexp_wrt_dexp_rec n1 (de_var_f x1) ee1 ->
  ee2 = ee1.
Proof.
pose proof open_dexp_wrt_dexp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_dexp_wrt_dexp_rec_inj : lngen.

(* end hide *)

Lemma open_dexp_wrt_dexp_inj :
forall ee2 ee1 x1,
  x1 `notin` fv_dexp ee2 ->
  x1 `notin` fv_dexp ee1 ->
  open_dexp_wrt_dexp ee2 (de_var_f x1) = open_dexp_wrt_dexp ee1 (de_var_f x1) ->
  ee2 = ee1.
Proof.
unfold open_dexp_wrt_dexp; eauto with lngen.
Qed.

Hint Immediate open_dexp_wrt_dexp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_dexp_wrt_dexp_of_lc_dexp_mutual :
(forall ee1,
  lc_dexp ee1 ->
  degree_dexp_wrt_dexp 0 ee1).
Proof.
apply_mutual_ind lc_dexp_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_dexp_wrt_dexp_of_lc_dexp :
forall ee1,
  lc_dexp ee1 ->
  degree_dexp_wrt_dexp 0 ee1.
Proof.
pose proof degree_dexp_wrt_dexp_of_lc_dexp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dexp_wrt_dexp_of_lc_dexp : lngen.

(* begin hide *)

Lemma lc_dexp_of_degree_size_mutual :
forall i1,
(forall ee1,
  size_dexp ee1 = i1 ->
  degree_dexp_wrt_dexp 0 ee1 ->
  lc_dexp ee1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind dexp_mutind;
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

Lemma lc_dexp_of_degree :
forall ee1,
  degree_dexp_wrt_dexp 0 ee1 ->
  lc_dexp ee1.
Proof.
intros ee1; intros;
pose proof (lc_dexp_of_degree_size_mutual (size_dexp ee1));
intuition eauto.
Qed.

Hint Resolve lc_dexp_of_degree : lngen.

Ltac dexp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_dexp_wrt_dexp_of_lc_dexp in J1; clear H
          end).

Lemma lc_de_abs_exists :
forall x1 ee1,
  lc_dexp (open_dexp_wrt_dexp ee1 (de_var_f x1)) ->
  lc_dexp (de_abs ee1).
Proof.
intros; dexp_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_de_fixpoint_exists :
forall x1 ee1,
  lc_dexp (open_dexp_wrt_dexp ee1 (de_var_f x1)) ->
  lc_dexp (de_fixpoint ee1).
Proof.
intros; dexp_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_dexp (de_abs _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_de_abs_exists x1) : core.

Hint Extern 1 (lc_dexp (de_fixpoint _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_de_fixpoint_exists x1) : core.

Lemma lc_body_dexp_wrt_dexp :
forall ee1 ee2,
  body_dexp_wrt_dexp ee1 ->
  lc_dexp ee2 ->
  lc_dexp (open_dexp_wrt_dexp ee1 ee2).
Proof.
unfold body_dexp_wrt_dexp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
dexp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_dexp_wrt_dexp : lngen.

Lemma lc_body_de_abs_1 :
forall ee1,
  lc_dexp (de_abs ee1) ->
  body_dexp_wrt_dexp ee1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_de_abs_1 : lngen.

Lemma lc_body_de_fixpoint_1 :
forall ee1,
  lc_dexp (de_fixpoint ee1) ->
  body_dexp_wrt_dexp ee1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_de_fixpoint_1 : lngen.

(* begin hide *)

Lemma lc_dexp_unique_mutual :
(forall ee1 (proof2 proof3 : lc_dexp ee1), proof2 = proof3).
Proof.
apply_mutual_ind lc_dexp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_dexp_unique :
forall ee1 (proof2 proof3 : lc_dexp ee1), proof2 = proof3.
Proof.
pose proof lc_dexp_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_dexp_unique : lngen.

(* begin hide *)

Lemma lc_dexp_of_lc_set_dexp_mutual :
(forall ee1, lc_set_dexp ee1 -> lc_dexp ee1).
Proof.
apply_mutual_ind lc_set_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_dexp_of_lc_set_dexp :
forall ee1, lc_set_dexp ee1 -> lc_dexp ee1.
Proof.
pose proof lc_dexp_of_lc_set_dexp_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_dexp_of_lc_set_dexp : lngen.

(* begin hide *)

Lemma lc_set_dexp_of_lc_dexp_size_mutual :
forall i1,
(forall ee1,
  size_dexp ee1 = i1 ->
  lc_dexp ee1 ->
  lc_set_dexp ee1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind dexp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_dexp_of_lc_dexp];
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

Lemma lc_set_dexp_of_lc_dexp :
forall ee1,
  lc_dexp ee1 ->
  lc_set_dexp ee1.
Proof.
intros ee1; intros;
pose proof (lc_set_dexp_of_lc_dexp_size_mutual (size_dexp ee1));
intuition eauto.
Qed.

Hint Resolve lc_set_dexp_of_lc_dexp : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp_mutual :
(forall ee1 x1 n1,
  degree_dexp_wrt_dexp n1 ee1 ->
  x1 `notin` fv_dexp ee1 ->
  close_dexp_wrt_dexp_rec n1 x1 ee1 = ee1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp :
forall ee1 x1 n1,
  degree_dexp_wrt_dexp n1 ee1 ->
  x1 `notin` fv_dexp ee1 ->
  close_dexp_wrt_dexp_rec n1 x1 ee1 = ee1.
Proof.
pose proof close_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp_mutual as H; intuition eauto.
Qed.

Hint Resolve close_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp : lngen.
Hint Rewrite close_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp using solve [auto] : lngen.

(* end hide *)

Lemma close_dexp_wrt_dexp_lc_dexp :
forall ee1 x1,
  lc_dexp ee1 ->
  x1 `notin` fv_dexp ee1 ->
  close_dexp_wrt_dexp x1 ee1 = ee1.
Proof.
unfold close_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve close_dexp_wrt_dexp_lc_dexp : lngen.
Hint Rewrite close_dexp_wrt_dexp_lc_dexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp_mutual :
(forall ee2 ee1 n1,
  degree_dexp_wrt_dexp n1 ee2 ->
  open_dexp_wrt_dexp_rec n1 ee1 ee2 = ee2).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp :
forall ee2 ee1 n1,
  degree_dexp_wrt_dexp n1 ee2 ->
  open_dexp_wrt_dexp_rec n1 ee1 ee2 = ee2.
Proof.
pose proof open_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp_mutual as H; intuition eauto.
Qed.

Hint Resolve open_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp : lngen.
Hint Rewrite open_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp using solve [auto] : lngen.

(* end hide *)

Lemma open_dexp_wrt_dexp_lc_dexp :
forall ee2 ee1,
  lc_dexp ee2 ->
  open_dexp_wrt_dexp ee2 ee1 = ee2.
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve open_dexp_wrt_dexp_lc_dexp : lngen.
Hint Rewrite open_dexp_wrt_dexp_lc_dexp using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_dexp_close_dexp_wrt_dexp_rec_mutual :
(forall ee1 x1 n1,
  fv_dexp (close_dexp_wrt_dexp_rec n1 x1 ee1) [=] remove x1 (fv_dexp ee1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_dexp_close_dexp_wrt_dexp_rec :
forall ee1 x1 n1,
  fv_dexp (close_dexp_wrt_dexp_rec n1 x1 ee1) [=] remove x1 (fv_dexp ee1).
Proof.
pose proof fv_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dexp_close_dexp_wrt_dexp_rec : lngen.
Hint Rewrite fv_dexp_close_dexp_wrt_dexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_dexp_close_dexp_wrt_dexp :
forall ee1 x1,
  fv_dexp (close_dexp_wrt_dexp x1 ee1) [=] remove x1 (fv_dexp ee1).
Proof.
unfold close_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve fv_dexp_close_dexp_wrt_dexp : lngen.
Hint Rewrite fv_dexp_close_dexp_wrt_dexp using solve [auto] : lngen.

(* begin hide *)

Lemma fv_dexp_open_dexp_wrt_dexp_rec_lower_mutual :
(forall ee1 ee2 n1,
  fv_dexp ee1 [<=] fv_dexp (open_dexp_wrt_dexp_rec n1 ee2 ee1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_dexp_open_dexp_wrt_dexp_rec_lower :
forall ee1 ee2 n1,
  fv_dexp ee1 [<=] fv_dexp (open_dexp_wrt_dexp_rec n1 ee2 ee1).
Proof.
pose proof fv_dexp_open_dexp_wrt_dexp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dexp_open_dexp_wrt_dexp_rec_lower : lngen.

(* end hide *)

Lemma fv_dexp_open_dexp_wrt_dexp_lower :
forall ee1 ee2,
  fv_dexp ee1 [<=] fv_dexp (open_dexp_wrt_dexp ee1 ee2).
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve fv_dexp_open_dexp_wrt_dexp_lower : lngen.

(* begin hide *)

Lemma fv_dexp_open_dexp_wrt_dexp_rec_upper_mutual :
(forall ee1 ee2 n1,
  fv_dexp (open_dexp_wrt_dexp_rec n1 ee2 ee1) [<=] fv_dexp ee2 `union` fv_dexp ee1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_dexp_open_dexp_wrt_dexp_rec_upper :
forall ee1 ee2 n1,
  fv_dexp (open_dexp_wrt_dexp_rec n1 ee2 ee1) [<=] fv_dexp ee2 `union` fv_dexp ee1.
Proof.
pose proof fv_dexp_open_dexp_wrt_dexp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dexp_open_dexp_wrt_dexp_rec_upper : lngen.

(* end hide *)

Lemma fv_dexp_open_dexp_wrt_dexp_upper :
forall ee1 ee2,
  fv_dexp (open_dexp_wrt_dexp ee1 ee2) [<=] fv_dexp ee2 `union` fv_dexp ee1.
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve fv_dexp_open_dexp_wrt_dexp_upper : lngen.

(* begin hide *)

Lemma fv_dexp_subst_dexp_fresh_mutual :
(forall ee1 ee2 x1,
  x1 `notin` fv_dexp ee1 ->
  fv_dexp (subst_dexp ee2 x1 ee1) [=] fv_dexp ee1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_dexp_subst_dexp_fresh :
forall ee1 ee2 x1,
  x1 `notin` fv_dexp ee1 ->
  fv_dexp (subst_dexp ee2 x1 ee1) [=] fv_dexp ee1.
Proof.
pose proof fv_dexp_subst_dexp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dexp_subst_dexp_fresh : lngen.
Hint Rewrite fv_dexp_subst_dexp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_dexp_subst_dexp_lower_mutual :
(forall ee1 ee2 x1,
  remove x1 (fv_dexp ee1) [<=] fv_dexp (subst_dexp ee2 x1 ee1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_dexp_subst_dexp_lower :
forall ee1 ee2 x1,
  remove x1 (fv_dexp ee1) [<=] fv_dexp (subst_dexp ee2 x1 ee1).
Proof.
pose proof fv_dexp_subst_dexp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dexp_subst_dexp_lower : lngen.

(* begin hide *)

Lemma fv_dexp_subst_dexp_notin_mutual :
(forall ee1 ee2 x1 x2,
  x2 `notin` fv_dexp ee1 ->
  x2 `notin` fv_dexp ee2 ->
  x2 `notin` fv_dexp (subst_dexp ee2 x1 ee1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_dexp_subst_dexp_notin :
forall ee1 ee2 x1 x2,
  x2 `notin` fv_dexp ee1 ->
  x2 `notin` fv_dexp ee2 ->
  x2 `notin` fv_dexp (subst_dexp ee2 x1 ee1).
Proof.
pose proof fv_dexp_subst_dexp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dexp_subst_dexp_notin : lngen.

(* begin hide *)

Lemma fv_dexp_subst_dexp_upper_mutual :
(forall ee1 ee2 x1,
  fv_dexp (subst_dexp ee2 x1 ee1) [<=] fv_dexp ee2 `union` remove x1 (fv_dexp ee1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_dexp_subst_dexp_upper :
forall ee1 ee2 x1,
  fv_dexp (subst_dexp ee2 x1 ee1) [<=] fv_dexp ee2 `union` remove x1 (fv_dexp ee1).
Proof.
pose proof fv_dexp_subst_dexp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dexp_subst_dexp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_dexp_close_dexp_wrt_dexp_rec_mutual :
(forall ee2 ee1 x1 x2 n1,
  degree_dexp_wrt_dexp n1 ee1 ->
  x1 <> x2 ->
  x2 `notin` fv_dexp ee1 ->
  subst_dexp ee1 x1 (close_dexp_wrt_dexp_rec n1 x2 ee2) = close_dexp_wrt_dexp_rec n1 x2 (subst_dexp ee1 x1 ee2)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dexp_close_dexp_wrt_dexp_rec :
forall ee2 ee1 x1 x2 n1,
  degree_dexp_wrt_dexp n1 ee1 ->
  x1 <> x2 ->
  x2 `notin` fv_dexp ee1 ->
  subst_dexp ee1 x1 (close_dexp_wrt_dexp_rec n1 x2 ee2) = close_dexp_wrt_dexp_rec n1 x2 (subst_dexp ee1 x1 ee2).
Proof.
pose proof subst_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_close_dexp_wrt_dexp_rec : lngen.

Lemma subst_dexp_close_dexp_wrt_dexp :
forall ee2 ee1 x1 x2,
  lc_dexp ee1 ->  x1 <> x2 ->
  x2 `notin` fv_dexp ee1 ->
  subst_dexp ee1 x1 (close_dexp_wrt_dexp x2 ee2) = close_dexp_wrt_dexp x2 (subst_dexp ee1 x1 ee2).
Proof.
unfold close_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve subst_dexp_close_dexp_wrt_dexp : lngen.

(* begin hide *)

Lemma subst_dexp_degree_dexp_wrt_dexp_mutual :
(forall ee1 ee2 x1 n1,
  degree_dexp_wrt_dexp n1 ee1 ->
  degree_dexp_wrt_dexp n1 ee2 ->
  degree_dexp_wrt_dexp n1 (subst_dexp ee2 x1 ee1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dexp_degree_dexp_wrt_dexp :
forall ee1 ee2 x1 n1,
  degree_dexp_wrt_dexp n1 ee1 ->
  degree_dexp_wrt_dexp n1 ee2 ->
  degree_dexp_wrt_dexp n1 (subst_dexp ee2 x1 ee1).
Proof.
pose proof subst_dexp_degree_dexp_wrt_dexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_degree_dexp_wrt_dexp : lngen.

(* begin hide *)

Lemma subst_dexp_fresh_eq_mutual :
(forall ee2 ee1 x1,
  x1 `notin` fv_dexp ee2 ->
  subst_dexp ee1 x1 ee2 = ee2).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dexp_fresh_eq :
forall ee2 ee1 x1,
  x1 `notin` fv_dexp ee2 ->
  subst_dexp ee1 x1 ee2 = ee2.
Proof.
pose proof subst_dexp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_fresh_eq : lngen.
Hint Rewrite subst_dexp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_dexp_fresh_same_mutual :
(forall ee2 ee1 x1,
  x1 `notin` fv_dexp ee1 ->
  x1 `notin` fv_dexp (subst_dexp ee1 x1 ee2)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dexp_fresh_same :
forall ee2 ee1 x1,
  x1 `notin` fv_dexp ee1 ->
  x1 `notin` fv_dexp (subst_dexp ee1 x1 ee2).
Proof.
pose proof subst_dexp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_fresh_same : lngen.

(* begin hide *)

Lemma subst_dexp_fresh_mutual :
(forall ee2 ee1 x1 x2,
  x1 `notin` fv_dexp ee2 ->
  x1 `notin` fv_dexp ee1 ->
  x1 `notin` fv_dexp (subst_dexp ee1 x2 ee2)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dexp_fresh :
forall ee2 ee1 x1 x2,
  x1 `notin` fv_dexp ee2 ->
  x1 `notin` fv_dexp ee1 ->
  x1 `notin` fv_dexp (subst_dexp ee1 x2 ee2).
Proof.
pose proof subst_dexp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_fresh : lngen.

Lemma subst_dexp_lc_dexp :
forall ee1 ee2 x1,
  lc_dexp ee1 ->
  lc_dexp ee2 ->
  lc_dexp (subst_dexp ee2 x1 ee1).
Proof.
default_simp.
Qed.

Hint Resolve subst_dexp_lc_dexp : lngen.

(* begin hide *)

Lemma subst_dexp_open_dexp_wrt_dexp_rec_mutual :
(forall ee3 ee1 ee2 x1 n1,
  lc_dexp ee1 ->
  subst_dexp ee1 x1 (open_dexp_wrt_dexp_rec n1 ee2 ee3) = open_dexp_wrt_dexp_rec n1 (subst_dexp ee1 x1 ee2) (subst_dexp ee1 x1 ee3)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_dexp_open_dexp_wrt_dexp_rec :
forall ee3 ee1 ee2 x1 n1,
  lc_dexp ee1 ->
  subst_dexp ee1 x1 (open_dexp_wrt_dexp_rec n1 ee2 ee3) = open_dexp_wrt_dexp_rec n1 (subst_dexp ee1 x1 ee2) (subst_dexp ee1 x1 ee3).
Proof.
pose proof subst_dexp_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_open_dexp_wrt_dexp_rec : lngen.

(* end hide *)

Lemma subst_dexp_open_dexp_wrt_dexp :
forall ee3 ee1 ee2 x1,
  lc_dexp ee1 ->
  subst_dexp ee1 x1 (open_dexp_wrt_dexp ee3 ee2) = open_dexp_wrt_dexp (subst_dexp ee1 x1 ee3) (subst_dexp ee1 x1 ee2).
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve subst_dexp_open_dexp_wrt_dexp : lngen.

Lemma subst_dexp_open_dexp_wrt_dexp_var :
forall ee2 ee1 x1 x2,
  x1 <> x2 ->
  lc_dexp ee1 ->
  open_dexp_wrt_dexp (subst_dexp ee1 x1 ee2) (de_var_f x2) = subst_dexp ee1 x1 (open_dexp_wrt_dexp ee2 (de_var_f x2)).
Proof.
intros; rewrite subst_dexp_open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve subst_dexp_open_dexp_wrt_dexp_var : lngen.

(* begin hide *)

Lemma subst_dexp_spec_rec_mutual :
(forall ee1 ee2 x1 n1,
  subst_dexp ee2 x1 ee1 = open_dexp_wrt_dexp_rec n1 ee2 (close_dexp_wrt_dexp_rec n1 x1 ee1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_dexp_spec_rec :
forall ee1 ee2 x1 n1,
  subst_dexp ee2 x1 ee1 = open_dexp_wrt_dexp_rec n1 ee2 (close_dexp_wrt_dexp_rec n1 x1 ee1).
Proof.
pose proof subst_dexp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_spec_rec : lngen.

(* end hide *)

Lemma subst_dexp_spec :
forall ee1 ee2 x1,
  subst_dexp ee2 x1 ee1 = open_dexp_wrt_dexp (close_dexp_wrt_dexp x1 ee1) ee2.
Proof.
unfold close_dexp_wrt_dexp; unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve subst_dexp_spec : lngen.

(* begin hide *)

Lemma subst_dexp_subst_dexp_mutual :
(forall ee1 ee2 ee3 x2 x1,
  x2 `notin` fv_dexp ee2 ->
  x2 <> x1 ->
  subst_dexp ee2 x1 (subst_dexp ee3 x2 ee1) = subst_dexp (subst_dexp ee2 x1 ee3) x2 (subst_dexp ee2 x1 ee1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dexp_subst_dexp :
forall ee1 ee2 ee3 x2 x1,
  x2 `notin` fv_dexp ee2 ->
  x2 <> x1 ->
  subst_dexp ee2 x1 (subst_dexp ee3 x2 ee1) = subst_dexp (subst_dexp ee2 x1 ee3) x2 (subst_dexp ee2 x1 ee1).
Proof.
pose proof subst_dexp_subst_dexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_subst_dexp : lngen.

(* begin hide *)

Lemma subst_dexp_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec_mutual :
(forall ee2 ee1 x1 x2 n1,
  x2 `notin` fv_dexp ee2 ->
  x2 `notin` fv_dexp ee1 ->
  x2 <> x1 ->
  degree_dexp_wrt_dexp n1 ee1 ->
  subst_dexp ee1 x1 ee2 = close_dexp_wrt_dexp_rec n1 x2 (subst_dexp ee1 x1 (open_dexp_wrt_dexp_rec n1 (de_var_f x2) ee2))).
Proof.
apply_mutual_ind dexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_dexp_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec :
forall ee2 ee1 x1 x2 n1,
  x2 `notin` fv_dexp ee2 ->
  x2 `notin` fv_dexp ee1 ->
  x2 <> x1 ->
  degree_dexp_wrt_dexp n1 ee1 ->
  subst_dexp ee1 x1 ee2 = close_dexp_wrt_dexp_rec n1 x2 (subst_dexp ee1 x1 (open_dexp_wrt_dexp_rec n1 (de_var_f x2) ee2)).
Proof.
pose proof subst_dexp_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec : lngen.

(* end hide *)

Lemma subst_dexp_close_dexp_wrt_dexp_open_dexp_wrt_dexp :
forall ee2 ee1 x1 x2,
  x2 `notin` fv_dexp ee2 ->
  x2 `notin` fv_dexp ee1 ->
  x2 <> x1 ->
  lc_dexp ee1 ->
  subst_dexp ee1 x1 ee2 = close_dexp_wrt_dexp x2 (subst_dexp ee1 x1 (open_dexp_wrt_dexp ee2 (de_var_f x2))).
Proof.
unfold close_dexp_wrt_dexp; unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve subst_dexp_close_dexp_wrt_dexp_open_dexp_wrt_dexp : lngen.

Lemma subst_dexp_de_abs :
forall x2 ee2 ee1 x1,
  lc_dexp ee1 ->
  x2 `notin` fv_dexp ee1 `union` fv_dexp ee2 `union` singleton x1 ->
  subst_dexp ee1 x1 (de_abs ee2) = de_abs (close_dexp_wrt_dexp x2 (subst_dexp ee1 x1 (open_dexp_wrt_dexp ee2 (de_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_dexp_de_abs : lngen.

Lemma subst_dexp_de_fixpoint :
forall x2 ee2 ee1 x1,
  lc_dexp ee1 ->
  x2 `notin` fv_dexp ee1 `union` fv_dexp ee2 `union` singleton x1 ->
  subst_dexp ee1 x1 (de_fixpoint ee2) = de_fixpoint (close_dexp_wrt_dexp x2 (subst_dexp ee1 x1 (open_dexp_wrt_dexp ee2 (de_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_dexp_de_fixpoint : lngen.

(* begin hide *)

Lemma subst_dexp_intro_rec_mutual :
(forall ee1 x1 ee2 n1,
  x1 `notin` fv_dexp ee1 ->
  open_dexp_wrt_dexp_rec n1 ee2 ee1 = subst_dexp ee2 x1 (open_dexp_wrt_dexp_rec n1 (de_var_f x1) ee1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dexp_intro_rec :
forall ee1 x1 ee2 n1,
  x1 `notin` fv_dexp ee1 ->
  open_dexp_wrt_dexp_rec n1 ee2 ee1 = subst_dexp ee2 x1 (open_dexp_wrt_dexp_rec n1 (de_var_f x1) ee1).
Proof.
pose proof subst_dexp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_intro_rec : lngen.
Hint Rewrite subst_dexp_intro_rec using solve [auto] : lngen.

Lemma subst_dexp_intro :
forall x1 ee1 ee2,
  x1 `notin` fv_dexp ee1 ->
  open_dexp_wrt_dexp ee1 ee2 = subst_dexp ee2 x1 (open_dexp_wrt_dexp ee1 (de_var_f x1)).
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve subst_dexp_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
