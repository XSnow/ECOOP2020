Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Subtyping_inversion
        Deterministic
        rules_inf2.

Require Import Coq.Strings.String.

Fixpoint erase_anno (e:exp) : dexp :=
  match e with
  | (e_var_b nat) => de_var_b nat
  | (e_var_f x) => de_var_f x
  | e_top => de_top
  | (e_lit i5) => de_lit i5
  | (e_abs e A B) => de_abs (erase_anno e)
  | (e_fixpoint e A) => de_fixpoint (erase_anno e)
  | (e_app e1 e2) => de_app (erase_anno e1) (erase_anno e2)
  | (e_merge e1 e2) => de_merge (erase_anno e1) (erase_anno e2)
  | (e_anno e A) => erase_anno e
  | (e_val v) => erase_anno_v v
  end
with erase_anno_v (v:value) : dexp :=
       match v with
       | v_top => de_top
       | (v_topv v) => erase_anno_v v
       | (v_lit i5) => de_lit i5
       | (v_absv e B D) => de_abs (erase_anno e)
       | (v_merge v1 v2) => de_merge (erase_anno_v v1) (erase_anno_v v2)
       end.

Notation "| e |" := (erase_anno e) (at level 30, e at level 39).
Notation "|| v ||" := (erase_anno_v v) (at level 30, v at level 39).


Require Import Omega.

Ltac size_ind_auto :=
  ( eapply_first_lt_hyp ;
    try reflexivity;
    try omega ;
    try eauto ).


Lemma erasure_open_aux : forall i,
    (forall e, (size_exp e = i -> forall t n, | open_exp_wrt_exp_rec n t e | = open_dexp_wrt_dexp_rec n (| t |) (| e |))) /\
    (forall ve, (size_value ve = i -> forall t n, | open_exp_wrt_exp_rec n t (e_val ve) | = open_dexp_wrt_dexp_rec n (|t|) (| (e_val ve) |))).
Proof.
  intros i. pattern i. apply lt_wf_rec.
    clear i; intros i H;
      apply_mutual_ind exp_value_mutind;
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
    (forall e, (size_exp e = i -> lc_exp e -> lc_dexp (| e |) )) /\
    (forall v, (size_value v = i -> lc_value v -> lc_dexp (||v||) /\ DValue (|| v ||))).
Proof.
  intros i. pattern i. apply lt_wf_rec.
    clear i; intros i H;
      apply_mutual_ind exp_value_mutind;
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
  - (* absv *)
    split;
      [ auto | constructor ];
      pick fresh x;
      apply (lc_de_abs_exists x);
      assert ( |e_var_f x| = de_var_f x ) by auto;
      rewrite <- H1;
      rewrite <- erasure_open;
      eapply_first_lt_hyp;
      try (apply size_exp_open_exp_wrt_exp_var);
      try omega;
      apply H3.
  - (* merge *)
    split; constructor;
    size_ind_auto.
Qed.
                                      
Lemma erasure_lc_exp : forall e,
    lc_exp e -> lc_dexp (erase_anno e).
Proof.
  intros e H.
  pose proof erasure_lc_aux (size_exp e).
  intuition eauto.
Qed.

Lemma erasure_lc_val : forall v,
    lc_value v -> lc_dexp (erase_anno_v v) /\ DValue (erase_anno_v v).
Proof.
  intros v H.
  pose proof erasure_lc_aux (size_value v).
  eapply H0; auto.
Qed.

Lemma TypedReduce_lc: forall v A v',
    TypedReduce v A v'-> lc_value v /\ lc_value v'.
Proof.
  introv Red.
  induction Red;
    try solve [constructor*].
  - Case "absv".
    inverts H.
    auto.
Qed.

Hint Resolve erasure_lc_exp erasure_lc_val TypedReduce_lc.

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
    e2 ->>* e2' -> lc_dexp v1 -> DValue v1 -> (de_app v1 e2) ->>* (de_app v1 e2').
Proof.
  intros v1 e2 e2' H LC Val.
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
    TypedReduce v A v' -> (erase_anno_v v) ->>* (erase_anno_v v').
Proof.
  intros v A v' Red.
  lets Red': Red.
  induction Red;
    lets [Lc Lc']: TypedReduce_lc Red';
    simpl; auto.
  - inverts* Lc.
    eapply star_trans.
    apply star_onestep.
    eapply DStep_unmergel.
    forwards*: erasure_lc_val H4.
    forwards*: erasure_lc_val H3.
    forwards*: IHRed.
  - inverts* Lc.
    eapply star_trans.
    apply star_onestep.
    eapply DStep_unmerger.
    forwards*: erasure_lc_val H3.
    forwards*: erasure_lc_val H4.
    forwards*: IHRed.
  - lets [Lc_e Val]: erasure_lc_val Lc.
    eapply star_trans.
    apply star_onestep.
    eapply DStep_split.
    auto.
    eapply star_trans.
    apply step_mergel.
    forwards*: IHRed1.
    auto.
    inverts* Lc'.
    forwards* [? ?]: erasure_lc_val H1.
    apply~ step_merger.
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
    lets : tred_soundness H0.
    lets [Lc Val]: erasure_lc_val H.
    lets [Lc_v Lc_v']: TypedReduce_lc H0.
    simpl in Lc. simpl in Val.
    eapply star_trans.
    eapply step_appr.
    apply H1.
    auto. auto.
    
    apply star_onestep.
    assert (| e ^^ e_val v'| = open_dexp_wrt_dexp (| e |)  (| e_val v' |)) by apply erasure_open.
    assert ( | e_val v' | = || v' || ) by auto.
    rewrite H2. rewrite H3.
    apply~ DStep_beta.
    apply~ erasure_lc_val.
  -
    simpl.
    lets* : tred_soundness H.
  -
    simpl.
    apply~ step_appl.
  -
    simpl.
    lets [Lc Val]: erasure_lc_val H.
    apply~ step_appr.
  -
    simpl.
    apply~ step_mergel.
  -
    simpl.
    lets [Lc Val]: erasure_lc_val H.
    apply~ step_merger.
  -
    simpl.
    auto.
  -
    apply erasure_lc_exp in H.
    apply star_onestep.
    assert (| e ^^ e_fixpoint e A | = open_dexp_wrt_dexp (| e |)  (| e_fixpoint e A |)) by apply erasure_open.
    rewrite H0.
    apply~ DStep_fix.
Qed.
