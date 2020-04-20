Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf.

Require Import List. Import ListNotations.
Require Import Coq.Strings.String.


Definition relation (X:Type) := X -> X -> Prop.

Section Star.

  Variable A : Type.
  Variable R : relation A.

  Inductive star: relation A:=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

  Lemma star_one:
    forall a b, R a b -> star a b.
  Proof.
    eauto using star.
  Qed.

  Lemma star_trans:
    forall a b, star a b -> forall c, star b c -> star a c.
  Proof.
    induction 1; eauto using star.
  Qed.


  Hypothesis R_functional:
    forall a b c, R a b -> R a c -> b = c.

  Lemma star_star_inv:
    forall a b, star a b -> forall c, star a c -> star b c \/ star c b.
  Proof.
    induction 1; intros.
    - auto.
    - inversion H1; subst.
      + right. eauto using star.
      + assert (b = b0) by (eapply R_functional; eauto). subst b0.
        apply IHstar; auto.
  Qed.

  Definition irred a : Prop := forall b, ~(R a b).

  Lemma finseq_unique:
    forall a b b',
      star a b -> irred b ->
      star a b' -> irred b' ->
      b = b'.
  Proof.
    intros. destruct (star_star_inv _ _ H _ H1).
    - inversion H3; subst. auto. elim (H0 _ H4).
    - inversion H3; subst. auto. elim (H2 _ H4).
  Qed.


End Star.

Hint Constructors star.

Hint Resolve star_trans star_one.


Definition mul_dstep := star dexp DunfieldStep.
Notation "e ->>* e'" := ((star dexp DunfieldStep) e e') (at level 68).

Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 0).
Notation "t ^^ u"       := (open_exp_wrt_exp t u) (at level 67).
Notation "e ^ x"        := (open_exp_wrt_exp e (e_var_f x)).

Notation "G |= t ~: T" := (Etyping G t T) (at level 69).

Notation "v ~-> A v'" := (TypedReduce v A v') (at level 68).

Notation "R 'star'" := (star exp R) (at level 69).

Notation "t ->* t'" := (step star t t') (at level 68).

(** [x # E] to be read x fresh from E captures the fact that
    x is unbound in E . *)

Notation "x '#' E" := (x \notin (dom E)) (at level 67) : env_scope.

Definition env := list (atom * exp).

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  let E := gather_atoms_with (fun x : ctx => dom x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  constr:(A `union` B `union` C `union` D `union` F).
(*
Definition typed e A : Prop := Dtyping nil e A.
Definition well_typed e : Prop := exists A, Dtyping nil e A.
*)
(* ********************************************************************** *)
(** ** Regularity of relations *)

(** A typing relation holds only if the environment has no
   duplicated keys and the pre-term is locally-closed. *)


Lemma typing_regular_2 : forall G e T, Etyping G e T -> uniq G.
Proof.
  intros. induction* H.
  pick fresh y.
  assert (uniq ((y, A) :: G)) by auto.
  solve_uniq.
  
  pick fresh y.
  assert (uniq ((y, A) :: G)) by auto.
  solve_uniq.
Qed.

Hint Resolve typing_regular_2.

Require Import Omega.

Lemma typing_regular_1_exp :
  forall e, forall G T, Etyping G e T -> lc_exp e
with typing_regular_1_val :
  forall v, forall T, Vtyping v T -> lc_value v.
Proof.
  intros e G T H.
  induction H;
    clear typing_regular_1_exp;
    eauto.
  intros v T H.
  induction H;
    clear typing_regular_1_val;
    eauto.
Qed.

Hint Resolve typing_regular_1_exp typing_regular_1_val.

(** Other properties *)
Lemma fv_in_dom:
  forall e,
  forall G T, Etyping G e T -> fv_exp e [<=] dom G
with value_no_fv : forall v T,
    Vtyping v T -> fv_value v [<=] empty.
Proof.
  intros e G T H.
  induction H; simpl; try fsetdec.
  - Case "value".
    forwards*: value_no_fv H0.
    fsetdec.
  - Case "typing_var".
    apply binds_In in H0.
    fsetdec.
  - Case "typing_abs".
    pick fresh x.
    assert (Fx : fv_exp (e ^ x) [<=] dom ([(x,A)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_exp e [<=] fv_exp (e ^ x)) by
        eapply fv_exp_open_exp_wrt_exp_lower.
    fsetdec.
  - Case "typing_fix".
    pick fresh x.
    assert (Fx : fv_exp (e ^ x) [<=] dom ([(x,A)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_exp e [<=] fv_exp (e ^ x)) by
        eapply fv_exp_open_exp_wrt_exp_lower.
    fsetdec.
  - intros v T H.
  induction H; simpl; try fsetdec.
  pick fresh x.
  assert (Fx : fv_exp (e ^ x) [<=] dom ([(x,A)] ++ []))
    by eauto.
  simpl in Fx.
  assert (Fy : fv_exp e [<=] fv_exp (e ^ x)) by
      eapply fv_exp_open_exp_wrt_exp_lower.
  fsetdec.
Qed.


Lemma step_not_value: forall (v:value),
    irred exp step (e_val v).
Proof.
  introv.
  unfold irred.
  induction v; introv H;
    inverts* H.
Qed.


Lemma value_no_step : forall (v1:value) (v2:value),
    (e_val v1) ->* (e_val v2) ->
    v2 = v1.
Proof.
  introv Red.
  remember (e_val v1).
  remember (e_val v2).
  induction* Red.
  congruence.
  rewrite Heqe in H.
  lets : step_not_value H.
  tryfalse.
Qed.


Lemma multi_red_app : forall v t t',
    lc_value v -> t ->* t' -> (e_app (e_val v) t) ->* (e_app (e_val v) t').
Proof.
  introv ? Red.
  induction* Red.
Qed.


Lemma multi_red_app2 : forall t1 t2 t1',
    lc_exp t2 -> t1 ->* t1' -> (e_app t1 t2) ->* (e_app t1' t2).
Proof.
  introv ? Red.
  induction* Red.
Qed.


Lemma multi_red_merge1 : forall t1 t2 t1',
    lc_exp t2 ->
    t1 ->* t1' ->
    (e_merge t1 t2) ->* (e_merge t1' t2).
Proof.
  introv ? Red.
  induction* Red. 
Qed.


Lemma multi_red_merge2 : forall v1 t2 t2',
    lc_value v1 ->
    t2 ->* t2' ->
    (e_merge (e_val v1) t2) ->* (e_merge (e_val v1) t2').
Proof.
  introv ? Red.
  induction* Red.
Qed.

Lemma multi_red_merge : forall t1 t2 v1 v2,
    lc_value v1 -> lc_exp t2 ->
    t1 ->* (e_val v1) -> t2 ->* (e_val v2) ->
    (e_merge t1 t2) ->* (e_merge (e_val v1) (e_val v2)).
Proof.
  intros.
  apply star_trans with (b := e_merge (e_val v1) t2).
  sapply* multi_red_merge1.
  sapply* multi_red_merge2.
Qed.


Lemma Etyping_weaken : forall G E F t T,
    Etyping (E ++ G) t T ->
    uniq (E ++ F ++ G) ->
    Etyping (E ++ F ++ G) t T.
Proof.
  introv Typ; gen F;
    inductions Typ; introv Ok; autos*.
    + (* abs *)
      pick fresh x and apply Etyp_abs.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
      auto.
      auto.
    + (* fix *)
      pick fresh x and apply Etyp_fix.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
Qed.

Lemma Etyping_weakening : forall (E F : ctx)  e T,
    Etyping E e T ->
    uniq (F ++ E) ->
    Etyping (F ++ E) e T.
Proof.
  intros E F e T H J.
  rewrite_env (nil ++ F ++ E).
  apply~ Etyping_weaken.
Qed.

(** Typing is preserved by substitution. *)

Lemma subst_value : forall v T z u,
    Vtyping v T -> subst_value u z v = v.
Proof.
  intros v T z u Typ.
  lets* Fv: value_no_fv Typ.
  forwards*: subst_value_fresh_eq.
  rewrite Fv.
  fsetdec.
Qed.

Lemma Etyping_subst : forall (E F : ctx) e u S T (z : atom),
    Etyping (F ++ [(z,S)] ++ E) e T ->
    Etyping E u S ->
    Etyping (F ++ E) ([z ~> u] e) T.
Proof.
  intros.
  remember (F ++ [(z,S)] ++ E) as E'.
  generalize dependent F.
  induction H; intros F Eq; subst; simpl; autos*;
    lets Lc  : typing_regular_1_exp H0;
    lets Uni : typing_regular_2 H0.

  - (* value *)
    lets : subst_value H1.
    rewrite H2.
    constructor.
    solve_uniq.
    assumption.
  -
    case_if*.
    substs.
    assert (A = S).
    eapply binds_mid_eq; eauto.
    substs.
    apply~ Etyping_weakening.
    solve_uniq.
  -
    pick fresh x and apply Etyp_abs.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H1.
    auto.
    auto.
  -
    pick fresh x and apply Etyp_fix.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H1.
Qed.

Lemma typing_value: forall G v A,
    G |= (e_val v) ~: A -> Vtyping v A.
Proof.
  intros G v A TG.
  inverts* TG.
Qed.
(*
Lemma typing_uniq: forall G e A B,
    G |= e ~: A -> G |= e ~: B -> A = B.
Proof.
  intros G e A B Typ1 Typ2.
  gen B.
  induction Typ1;
    introv Typ2;
    try solve [inverts* Typ2].
  - inverts* Typ2.
    gen B.
    induction H0;
      introv Typ2;
      inverts* Typ2.
    forwards*: IHVtyping1.
    forwards*: IHVtyping2.
    congruence.
  - (* f_var *)
    inverts* Typ2.
    forwards*: binds_unique H0 H4 H2.
  - (* e_app *)
    inverts* Typ2.
    forwards*: IHTyp1_1.
    forwards*: IHTyp1_2.
    subst.
    inverts* H0.
  - (* and *)
    inverts* Typ2.
    forwards*: IHTyp1_1.
    forwards*: IHTyp1_2.
    congruence.
Qed. *)

(* typing canonical *)
Lemma intersection_canonical : forall v A B,
    nil |= (e_val v) ~: t_and A B->
    exists v1 v2, v = v_merge v1 v2.
Proof.
  introv Typ. lets Typ' : Typ.
  inductions Typ.
  inverts* H0.
Qed.
(*
Lemma unit_canonical : forall v,
    nil |= (e_val v) ~: t_top ->
    v = v_top.
Proof.
  introv Typ. lets Typ' : Typ. inductions Typ; inverts* H0.
Qed.
*)
