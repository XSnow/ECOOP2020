Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Subtyping_inversion
        Deterministic
        Type_Safety
        rules_inf2.
Require Import Coq.Strings.String.

Fixpoint erase_anno (e:exp) : dexp :=
  match e with
  | (e_var_b nat) => de_var_b nat
  | (e_var_f x) => de_var_f x
  | e_top => de_top
  | (e_lit i5) => de_lit i5
  | (e_abs A e B) => de_abs (erase_anno e)
  | (e_fixpoint e A) => de_fixpoint (erase_anno e)
  | (e_app e1 e2) => de_app (erase_anno e1) (erase_anno e2)
  | (e_merge e1 e2) => de_merge (erase_anno e1) (erase_anno e2)
  | (e_anno e A) => erase_anno e
  end.

Notation "| e |" := (erase_anno e) (at level 30, e at level 39).

Require Import Omega.

Ltac size_ind_auto :=
  ( eapply_first_lt_hyp ;
    try reflexivity;
    try omega ;
    try eauto ).


Lemma erasure_open_aux : forall i,
    forall e, (size_exp e = i -> forall t n, | open_exp_wrt_exp_rec n t e | = open_dexp_wrt_dexp_rec n (| t |) (| e |)).
Proof.
  intros i. pattern i. apply lt_wf_rec.
    clear i; intros i H;
      apply_mutual_ind exp_mutind;
      default_simp; size_ind_auto.
Qed.

(*
Lemma erasure_open_aux: forall e v n,
    | open_exp_wrt_exp_rec n (e_val v) e | = open_dexp_wrt_dexp_rec n (|| v ||) (| e |).
Proof.
  intro e.
  induction e;
    introv;
    try solve [
          unfold open_dexp_wrt_dexp_rec;
          simpl;
          auto ].
  - (* var_b *)
    remember (lt_eq_lt_dec n n0).
    unfold open_dexp_wrt_dexp_rec.
    unfold open_exp_wrt_exp_rec.
    simpl.
    rewrite <- Heqs.
    destruct s;
    try destruct s;
    simpl;
    auto.
  - (* abs *)
    simpl.
    lets: IHe v (S n).
    congruence.
  - (* app *)
    simpl.
    lets: IHe1 v n.
    lets: IHe2 v n.
    congruence.
  - (* merge *)
    simpl.
    lets: IHe1 v n.
    lets: IHe2 v n.
    congruence.
  - (* val *)
    induction v;
      unfold open_dexp_wrt_dexp_rec;
      unfold open_exp_wrt_exp_rec;
      simpl;
      auto.
  *)

Lemma erasure_open : forall e t,
    | e ^^ t | = open_dexp_wrt_dexp (| e |)  (| t |).
Proof.
  intros e v.
  pose proof (erasure_open_aux (size_exp e)).
  intuition eauto.
Qed.


Lemma erasure_lc_aux : forall i,
   forall e, (size_exp e = i -> lc_exp e -> lc_dexp (| e |) ).
Proof.
  intros i. pattern i. apply lt_wf_rec.
    clear i; intros i H;
      apply_mutual_ind exp_mutind;
      default_simp;
      try solve [ size_ind_auto ];
      try solve [
            constructor;
            size_ind_auto
          ].
  - (* abs *)
    pick fresh x.
    apply (lc_de_abs_exists x).
    assert ( |e_var_f x| = de_var_f x ) by auto.
    rewrite <- H1.
    rewrite <- erasure_open.
    eapply_first_lt_hyp;
    try (apply size_exp_open_exp_wrt_exp_var);
    try omega.
    apply H3.
  - (* fix *)
    pick fresh x.
    apply (lc_de_fixpoint_exists x).
    assert ( |e_var_f x| = de_var_f x ) by auto.
    rewrite <- H1.
    rewrite <- erasure_open.
    eapply_first_lt_hyp;
    try (apply size_exp_open_exp_wrt_exp_var);
    try omega.
    apply H3.
Qed.

Lemma erasure_lc : forall e,
    lc_exp e -> lc_dexp (erase_anno e).
Proof.
  intros e H.
  pose proof erasure_lc_aux (size_exp e).
  intuition eauto.
Qed.

Lemma erasure_val : forall v,
    value v -> DValue (erase_anno v).
Proof.
  intros v H.
  induction H;
    simpl;
    try constructor*.
  forwards*: erasure_lc H.
Qed.

Lemma value_lc : forall v,
    DValue v -> lc_dexp v.
Proof.
  intros v H.
  induction H;
    simpl;
    try solve [constructor*].
  auto.
Qed.

Lemma TypedReduce_lc: forall v A v',
    TypedReduce v A v'-> lc_exp v /\ lc_exp v'.
Proof.
  introv Red.
  induction Red;
    try solve [constructor*].
  - Case "absv".
    inverts H.
    auto.
Qed.

Hint Resolve erasure_lc TypedReduce_lc.

Lemma star_onestep : forall a b,
    DunfieldStep a b -> a ->>*  b.
Proof.
  intros a b H.
  eapply star_trans.
  apply star_refl.
  auto.
Qed.

(* eval ctxt *)
Lemma step_mergel : forall e1 e2 e1',
    e1 ->>* e1' -> lc_dexp e2 -> (de_merge e1 e2) ->>* (de_merge e1' e2).
Proof.
  intros e1 e2 e1' H LC.
  induction H.
  auto.
  eapply star_trans.
  apply star_onestep.
  apply DStep_mergel.
  auto.
  apply H.
  auto.
Qed.


Lemma step_merger : forall v1 e2 e2',
    e2 ->>* e2' -> lc_dexp v1 -> DValue v1 -> (de_merge v1 e2) ->>* (de_merge v1 e2').
Proof.
  intros v1 e2 e2' H LC Val.
  induction H.
  auto.
  eapply star_trans.
  apply star_onestep.
  apply DStep_merger.
  auto.
  apply H.
  auto.
Qed.


Lemma step_appl : forall e1 e1' e2,
    e1 ->>* e1' -> lc_dexp e2 -> (de_app e1 e2) ->>* (de_app e1' e2).
Proof.
  intros e1 e1' e2 H LC.
  induction H.
  auto.
  eapply star_trans.
  apply star_onestep.
  apply DStep_appl.
  auto.
  apply H.
  auto.
Qed.


Lemma step_appr : forall v1 e2 e2',
    e2 ->>* e2' -> DValue v1 -> (de_app v1 e2) ->>* (de_app v1 e2').
Proof.
  intros v1 e2 e2' H Val.
  induction H.
  auto.
  eapply star_trans.
  apply star_onestep.
  apply DStep_appr.
  auto.
  apply H.
  auto.
Qed.


Lemma tred_soundness : forall v A v',
    value v -> TypedReduce v A v' -> (erase_anno v) ->>* (erase_anno v').
Proof.
  intros v A v' Val Red.
  lets Red': Red.
  induction Red;
    lets [Lc Lc']: TypedReduce_lc Red';
    simpl; auto;
      try solve [inverts Val; inverts* Lc].
  - lets : erasure_lc Lc.
    lets : erasure_val Val.
    eapply star_trans.
    apply star_onestep.
    eapply DStep_split.
    auto.
    eapply star_trans.
    apply step_mergel.
    forwards*: IHRed1.
    auto.
    inverts* Lc'.
    forwards*: erasure_lc H3.
    apply~ step_merger.
    apply~ erasure_val.
    forwards*: TypedReduce_prv_value Red1.
Qed.

Theorem reduction_soundness : forall e e',
    step e e' -> (erase_anno e) ->>* (erase_anno e').
Proof.
  intros e e' Red.
  induction Red;
    try solve [
        simpl;
        apply star_refl ].
  -
    simpl.
    lets : tred_soundness H0 H1.
    lets Lc: erasure_lc H.
    lets Val: erasure_val H0.
    simpl in Lc.
    lets [Lc_v Lc_v']: TypedReduce_lc H1.
    eapply star_trans.
    eapply step_appr.
    apply H2.
    auto. auto.

    apply star_onestep.
    assert (| e ^^ v'| = open_dexp_wrt_dexp (| e |)  (| v' |)) by apply erasure_open.
    simpl.
    rewrite H3.
    apply~ DStep_beta.
    apply~ erasure_val.
    forwards*: TypedReduce_prv_value H1.
  -
    simpl.
    lets* : tred_soundness H.
  -
    simpl.
    apply~ step_appl.
  -
    simpl.
    lets Val: erasure_val H.
    lets Lc: erasure_lc.
    apply~ step_appr.
  -
    simpl.
    apply~ step_mergel.
  -
    simpl.
    lets Val: erasure_val H.
    apply~ step_merger.
    apply~ value_lc.
  -
    simpl.
    auto.
  -
    apply erasure_lc in H.
    apply star_onestep.
    assert (| e ^^ e_fixpoint e A | = open_dexp_wrt_dexp (| e |)  (| e_fixpoint e A |)) by apply erasure_open.
    rewrite H0.
    apply~ DStep_fix.
Qed.
