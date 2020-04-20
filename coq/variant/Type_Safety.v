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


Lemma TypedReduce_trans : forall v v1 v2 A B,
    TypedReduce v A v1 -> ord B -> TypedReduce v1 B v2 -> TypedReduce v B v2.
Proof.
  introv Red1 Ord Red2.
  gen B v2.
  induction* Red1;
    introv Ord Red2.
  - (* v1 = v_topv v *)
    remember (v_topv v).
    induction* Red2;
      try solve [inversion Heqv0];
      try solve [inversion Ord].
  - (* v1 = v_absv e A D *)
    remember (v_absv e A D).
    induction* Red2;
      try solve [inversion Heqv];
      try solve [inversion Ord].
    inverts* Heqv.
    constructor*.
    auto_sub.
  - (* and *)
    inverts* Red2;
      try solve [inverts* Ord].
Qed.
                                            
Lemma consistent_afterTR : forall v A B C v1 v2, Vtyping v C -> TypedReduce v A v1 -> TypedReduce v B v2 -> consistencySpec v1 v2.
Proof.
  intros v A B C v1 v2 Typ Red1 Red2.
  unfold consistencySpec.
  intros D v1' v2' Ord Red1' Red2'.
  lets Lc: typing_regular_1_val Typ.
  forwards*: TypedReduce_trans Red1 Red1'.
  forwards*: TypedReduce_trans Red2 Red2'.
  forwards*: TypedReduce_unique H H0.
Qed.


Lemma TypedReduce_preservation: forall v A v',
    TypedReduce v A v'-> forall B, Vtyping v B -> sub B A -> Vtyping v' A.
Proof.
  introv Red.
  induction Red; introv Typ Sub;
    lets Lc  : typing_regular_1_val Typ;
    try solve [constructor*].
  - Case "topv".
    eapply Vtyp_topv.
    eauto.
  - Case "absv".
    inverts Typ.
    apply~ Vtyp_absv.
    auto_sub.
  - Case "mergel".
    inverts Typ.
    lets: TypedReduce_sub Red.
    lets: principal_type_checks H3.
    forwards*: IHRed.
  - Case "merger".
    inverts Typ.
    lets: TypedReduce_sub Red.
    lets: principal_type_checks H4.
    forwards*: IHRed.
  - Case "merge_and".
    assert (sub B0 A) by auto_sub.
    assert (sub B0 B) by auto_sub.
    forwards*: IHRed1.
    forwards*: IHRed2.
    constructor*.
    lets* Con: consistent_afterTR Typ Red1 Red2.
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
    inverts H4.
    eapply Etyp_anno.
    pick_fresh x.
    rewrite* (@subst_exp_intro x).
    remember nil as G.
    rewrite_env(nil++G).
    sapply* Etyping_subst.
    subst.
    inverts Typ1.
    forwards*: TypedReduce_preservation H3.
    auto. 
  - Case "typing_merge".
    introv J.
    inverts J.
    + forwards*: IHTyp1.
    + forwards*: IHTyp2.
    + inverts Typ1.
      inverts Typ2.
      constructor*.
      constructor*.
      forwards*: disjoint_val_consistent.
  - Case "typing_anno".
    introv J.
    inverts* J.
    + SCase "e:A".
      inverts Typ.
      forwards*: TypedReduce_preservation H3 H4.
  - Case "typing_fix".
    introv J.
    inverts* J.
    pick_fresh x.
    rewrite* (@subst_exp_intro x).
    remember nil as G.
    rewrite_env(nil++G).
    sapply* Etyping_subst.
Qed.


Lemma TypedReduce_progress: forall v A B,
    Vtyping v A -> sub A B -> exists v', TypedReduce v B v'.
Proof.
  introv Typ Sub.
  gen A B.
  induction v; try solve [inverts* Val];
    intros.
  - Case "e_top".
    inverts Typ.
    induction B; inverts* Sub.
    destruct~ IHB1 as [v1 Tyr1].
    destruct~ IHB2 as [v2 Tyr2].
    exists*.
  - Case "e_lit".
    inverts Typ.
    induction B; inverts* Sub.
    destruct~ IHB1 as [v1 Tyr1].
    destruct~ IHB2 as [v2 Tyr2].
    exists*.
  - Case "v_topv".
    inverts Typ.
    induction B; inverts* Sub.
    destruct~ IHB1 as [v1 Tyr1].
    destruct~ IHB2 as [v2 Tyr2].
    exists*.
  - Case "e_absv".
    lets S: principal_type_sub Typ.
    lets T: principal_type_checks Typ.
    simpl in S. simpl in T.
    lets S2: sub_transtivity S Sub.
    induction B0; inverts* S2.
    + SCase "t_and".
      destruct~ IHB0_1 as [v1 Tyr1].
      auto_sub.
      destruct~ IHB0_2 as [v2 Tyr2].
      auto_sub.
      exists*.
  - Case "e_merge".
    lets Typ' : Typ.
    inverts* Typ.
    + SCase "consistent merge".
      lets Lc  : typing_regular_1_val H1.
      lets Lc2  : typing_regular_1_val H2.
      induction B.
      * SSCase "B:=Int".
        inverts Sub.
        lets* [? ?]: IHv1 H5.
        lets* [? ?]: IHv2 H5.
      * SSCase "B:=Top".
        assert (sub A0 t_top) by auto.
        lets* [? ?]: IHv1 H1 H.
      * SSCase "B:=Arrow".
        inverts Sub.
        lets* [? ?]: IHv1 H1 H5.
        lets* [? ?]: IHv2 H2 H5.
      * SSCase "B:=B1&B2".
        lets* [vb1' Tyrb1] : IHB1.
        auto_sub.
        lets* [vb2' Tyrb2] : IHB2.
        auto_sub.
Qed.

Theorem progress : forall e A,
    Etyping nil e A ->
    (exists v, e = (e_val v)) \/ exists e', step e e'.
Proof.
  introv Typ. lets Typ': Typ.
  inductions Typ; 
      lets Lc  : typing_regular_1_exp Typ';
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
      lets (v1' & Eqn): Val1;
      inverts* Eqn ].
    + SCase "e_app (e_absv _ _) v2".
      inverts Val2.
      inverts H0.
      inverts Typ1.
      lets* (v2' & Tyr): TypedReduce_progress H4 H6.
    + SCase "e_app v1 e2".
      destruct Val1.
      subst.
      inverts Lc.
      inverts* H1.
    + SCase "e_app e1 e2".
      forwards*: typing_regular_1_exp Typ1.
  - Case "merge".
    forwards*: typing_regular_1_exp Typ1.
    forwards*: typing_regular_1_exp Typ2.
    destruct~ IHTyp1 as [ (v1' & Val1) | [t1' Red1]];
      destruct~ IHTyp2 as [ (v2' & Val2) | [t2' Red2]];
      subst.
    + SCase "v1 v2".
      right.
      inverts* Typ1.
      inverts* Typ2.
    + SCase "e_merge v1 e2".
      inverts* Typ1.
    + SCase "e_merge e1 v2".
      inverts* Typ2.
    + SCase "e_merge e1 e2".
      inverts* Typ2.
  - Case "anno".
    right.
    destruct~ IHTyp as [ (v' & Val) | [t' Red]].
    + SCase "e_anno v A".
      subst.
      inverts* Typ.
      lets* (v1' & Tyr) : TypedReduce_progress H3 H.
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
    (exists v, e' = (e_val v)) \/ exists e'', step e e''.
Proof.
  introv Typ Red.
  induction Red.
  lets*: progress Typ.
  lets*: preservation Typ H.
Qed.
