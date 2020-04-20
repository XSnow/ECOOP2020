Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Key_Properties
        Subtyping_inversion
        Deterministic.

Require Import List. Import ListNotations.
Require Import Arith Omega.
Require Import Coq.Strings.String.


Lemma TypedReduce_toparr_normal_typed : forall A B,
    topLike (t_arrow A B) -> Etyping nil (e_abs t_top e_top B) (t_arrow A B).
Proof.
  intros Ht A B.
  eapply Etyp_abs.
  intros x H.
  apply Etyp_top.
  solve_uniq.
  auto.
  inverts B.
  apply toplike_super_top.
  auto.
  Unshelve.
  pick fresh x.
  exact (singleton x).
Qed.


(* requires sub Top A -> toplike A *)
Lemma TypedReduce_trans : forall v v1 v2 A B,
    value v -> TypedReduce v A v1 -> TypedReduce v1 B v2 -> TypedReduce v B v2.
Proof.
  introv Val Red1 Red2.
  lets Lc: value_lc Val.
  gen B v2.
  induction* Red1;
    introv Red2.
  - (* v1 = v_top *)
    remember e_top.
    induction* Red2;
      try solve [inversion Heqe].
  - (* toparr *)
    remember (e_abs t_top e_top B).
    induction* Red2;
      inversion Heqe.
    subst.
    exfalso.
    apply H2.
    forwards*: toplike_sub H0 H4.
  - (* v1 = abs A e D *)
    remember (e_abs A e D).
    induction* Red2;
      try solve [inversion Heqe0];
      try solve [inversion Ord].
    inverts* Heqe0.
    constructor.
    inverts* H2.
    assumption.
    assumption.
    auto_sub.
  - (* v = v1,,v2 v1'~->v0 *)
    inverts* Val.
    inverts* Lc.
    induction Red2;
      eauto.
  - (* v = v1,,v2 v2'~->v0 *)
    inverts* Val.
    inverts* Lc.
    induction Red2;
      eauto.
  - (* and *)
    gen v0.
    induction B0; introv Red2;
      try solve [inverts* Red2];
      try solve [inversion Ord].
Qed.


Lemma consistent_afterTR : forall v A B C v1 v2, value v -> Etyping nil v C -> TypedReduce v A v1 -> TypedReduce v B v2 -> consistencySpec v1 v2.
Proof.
  intros v A B C v1 v2 Val Typ Red1 Red2.
  unfold consistencySpec.
  intros D v1' v2' Red1' Red2'.
  lets Lc: typing_regular_1 Typ.
  forwards*: TypedReduce_trans Red1 Red1'.
  forwards*: TypedReduce_trans Red2 Red2'.
  forwards*: TypedReduce_unique H H0.
Qed.

Lemma TypedReduce_prv_value: forall v A v',
    value v -> TypedReduce v A v' -> value v'.
Proof.
  intros v A v' Val Red.
  induction* Red.
  - inverts* Val.
    inverts* H4.
  - inverts* Val.
  - inverts* Val.
Qed.

Lemma TypedReduce_preservation: forall v A v' B,
    value v -> TypedReduce v A v'-> Etyping nil v B -> Etyping nil v' A.
Proof.
  introv Val Red.
  lets Red': Red.
  gen B.
  induction Red; introv Typ;
    lets Lc  : typing_regular_1 Typ;
    try solve [constructor*].
  - Case "toparr".
    forwards*: TypedReduce_toparr_normal_typed.
  - Case "absv".
    inverts Lc.
    assert (lc_exp (e_abs A e D)) by eauto.
    inverts Typ.
    sapply~ Etyp_abs;
      auto_sub.
  - Case "mergel".
    inverts Val.
    inverts Typ;
    forwards*: IHRed.
  - Case "merger".
    inverts Val.
    inverts Typ;
    forwards*: IHRed.
  - Case "merge_and".
    forwards: IHRed1 Val Red1 Typ.
    forwards: IHRed2 Val Red2 Typ.
    lets Con: consistent_afterTR Val Typ Red1 Red2.
    apply~ Etyp_mergev.
    constructor.
    forwards*: TypedReduce_prv_value Val Red1.
    forwards*: TypedReduce_prv_value Val Red2.
Qed.


Theorem preservation : forall e e' A,
    Etyping nil e A ->
    step e e' ->
    Etyping nil e' A.
Proof.
  introv Typ. gen e'.
  lets Typ' : Typ.
  inductions Typ;
    try solve [introv J; inverts* J].
  - Case "typing_app".
    introv J.
    inverts* J.
    (* e_absv A0 . e : B0->D  v *)
    inverts Typ2.
    eapply Etyp_anno.
    pick_fresh x.
    rewrite* (@subst_exp_intro x).
    remember nil as G.
    rewrite_env(nil++G).
    sapply* Etyping_subst.
    subst.
    forwards*: TypedReduce_preservation H4.
    auto.
  - Case "typing_anno".
    introv J.
    inverts J.
    + forwards*: TypedReduce_preservation H4.
    + forwards*: IHTyp.
  - Case "typing_fix".
    introv J.
    inverts* J.
    pick_fresh x.
    rewrite* (@subst_exp_intro x).
    remember nil as G.
    rewrite_env(nil++G).
    sapply* Etyping_subst.
  - Case "typing_mergev".
    introv J.
    inverts J.
    + inverts H0.
      forwards*: step_not_value H5 H6.
    + inverts H0.
      forwards*: step_not_value H7 H6.
Qed.


Lemma TypedReduce_progress: forall v A B,
    value v -> Etyping [] v A -> sub A B -> exists v', TypedReduce v B v'.
Proof.
  introv Val Typ Sub.
  gen A B.
  induction v; try solve [inverts* Val];
    intros;
    try solve [
      inverts Typ;
      match goal with
      | |- ( exists _ , TypedReduce _ ?B  _ ) =>
        induction B
      end;
      inverts* Sub;
      try solve [
      match goal with
      | _ : (sub t_top _) |- ( exists _ , TypedReduce _ (t_arrow _ _) _ ) =>
        ( exists;
          apply~ TReduce_toparr;
          apply~ toplike_super_top;
          destruct~ IHB2 as [v2 Tyr2] )
      | |- ( exists _ , TypedReduce _ (t_and _ _ ) _ ) =>
        ( destruct~ IHB1 as [v1 Tyr1];
          destruct~ IHB2 as [v2 Tyr2];
          exists*                     )
      end ] ].
  - Case "e_absv".
    lets* [C [? ?]]: abs_typing_canonical Typ.
    subst.
    lets Lc: value_lc Val.
    induction B0;
      try solve [inverts* Sub].
    + SCase "t_arr".
      lets [St | [S1 S2]]: sub_inversion_arrow Sub;
        destruct (toplike_decidable(t_arrow B0_1 B0_2));
        exists;
        try solve [
              apply~ TReduce_toparr;
              inverts* H ].
      * exfalso.
        apply H.
        constructor.
        apply~ toplike_super_top.
      * (* not toplike case *)
        apply~ TReduce_arrow.
        auto_sub.
      Unshelve.
      eauto.
    + SCase "t_and".
      destruct~ IHB0_1 as [v1 Tyr1].
      auto_sub.
      destruct~ IHB0_2 as [v2 Tyr2].
      auto_sub.
      exists*.
  - Case "e_merge".
    lets Lc: value_lc Val.
    inverts Val.
    induction B.
    + SSCase "B:=Int".
      inverts Typ;
      inverts* Sub.
      lets* [? ?]: IHv1 H6.
      lets* [? ?]: IHv2 H6.
      lets* [? ?]: IHv1 H8.
      lets* [? ?]: IHv2 H8.
    + SSCase "B:=Top".
      inverts Typ;
      assert (sub A0 t_top) by auto;
      lets* [? ?]: IHv1 H1 H.
    + SSCase "B:=Arrow".
      inverts Typ;
      try solve [lets* [S | S]: sub_inversion_andl_arrr Sub;
      [ forwards* [? ?]: IHv1 S | forwards* [? ?]: IHv2 S ] ].
    + SSCase "B:=B1&B2".
      inverts Typ;
      (lets* [vb1' Tyrb1] : IHB1; try auto_sub;
       lets* [vb2' Tyrb2] : IHB2; try auto_sub).
Qed.

Theorem progress : forall e A,
    Etyping nil e A ->
    value e \/ exists e', step e e'.
Proof.
  introv Typ. lets Typ': Typ.
  inductions Typ;
      lets Lc  : typing_regular_1 Typ';
      try solve [left*];
      try solve [right*].
  - Case "var".
    invert H0.
  - Case "app".
    right.
    destruct~ IHTyp2 as [Val1 | [e1' Red2]].
    destruct~ IHTyp1 as [Val2 | [e2' Red1]].
    inverts* Typ2;
      try solve [
            inverts Val1 ].
    + SCase "e_app (e_absv _ _) v2".
      lets* (v2' & Tyr): TypedReduce_progress Typ1 H4.
    + SCase "e_app v1 e2".
      inverts Lc.
      inverts* H1.
    + SCase "e_app e1 e2".
      forwards*: typing_regular_1 Typ1.
  - Case "merge".
    forwards*: typing_regular_1 Typ1.
    forwards*: typing_regular_1 Typ2.
    destruct~ IHTyp1 as [ Val1 | [t1' Red1]];
      destruct~ IHTyp2 as [ Val2 | [t2' Red2]];
      subst.
    + SCase "e_merge v1 e2".
      inverts* Typ1.
    + SCase "e_merge e1 v2".
      inverts* Typ2.
    + SCase "e_merge e1 e2".
      inverts* Typ2.
  - Case "anno".
    right.
    destruct~ IHTyp as [ Val | [t' Red]].
    + SCase "e_anno v A".
      lets* (v1' & Tyr) : TypedReduce_progress Val Typ H.
    + SCase "e_anno e A".
      forwards*: Step_anno Red.
Qed.



Theorem preservation_multi_step : forall e e' A,
    nil |= e ~: A ->
    e ->* e' ->
    nil |= e' ~: A.
Proof.
  introv Typ Red.
  induction* Red.
  lets*: preservation Typ H.
Qed.


Theorem type_safety : forall e e' A,
    nil |= e ~: A ->
    e ->* e' ->
    value e \/ exists e'', step e e''.
Proof.
  introv Typ Red.
  induction Red.
  lets*: progress Typ.
  lets*: preservation Typ H.
Qed.
