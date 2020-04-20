Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf
               Subtyping_inversion.


(* TypedReduce *)
Lemma TypedReduce_toplike :
  forall A, topLike A ->
            forall (v v1 v2: value), TypedReduce v A v1 -> TypedReduce v A v2 -> v1 = v2.
Proof.
  intros A Typ.
  induction Typ;
    introv Red1 Red2.
  - inverts* Red1; try solve [inverts* H1].
    inverts* Red2; try solve [inverts* H2].
  - inversion Red1; subst;
      try solve [invert* H1].
    inversion Red2; subst;
      try solve [invert* H1].
    forwards: IHTyp1 H2 H3.
    forwards: IHTyp2 H4 H6.
    subst*.
Qed.



(* topLike *)
Lemma toplike_not_ord: forall A,
    topLike A -> ord A -> False.
Proof.
  intros A H H0.
  induction H;
  inversion H0.
Qed.

Lemma toplike_super_top: forall A,
    topLike A <-> sub t_top A.
Proof.
  intro A.
  split.
  - intro H.
    induction H.
    + apply sub_reflexivity.
    + apply~ S_andr.
  - intro H.
    induction A;
      try solve [inverts* H].
Qed.

Lemma toplike_sub: forall A B,
    topLike A -> sub A B -> topLike B.
Proof.
  intros A B H H0.
  apply toplike_super_top in H.
  apply toplike_super_top.
  auto_sub.
Qed.


Lemma toplike_decidable : forall A,
    topLike A \/ ~topLike A.
Proof.
  induction A.
  - right.
    unfold not.
    intros H.
    inversion H.
  - left*.
  - right.
    unfold not.
    intros H.
    inversion H.
  - destruct IHA1.
    + destruct IHA2.
      * left*.
      * right.
        unfold not.
        intros H1.
        inverts H1.
        auto.
    + right.
      unfold not.
      intros H0.
      inverts H0.
      auto.
Qed.   
        
(* disjoint *)

Lemma disjoint_eqv: forall A B,
    disjointSpec A B <-> disjoint A B.
Proof.
  intros A B.
  unfold disjointSpec.
  split.
  - gen B.
    induction A;
      introv H;
      induction B;
      try solve [constructor*].
    + (* int int *)
      assert (~topLike t_int). {
        unfold not.
        intro F.
        inversion F.
      }
      forwards: (H t_int); auto_sub.
      contradiction.
    + (* arr arr *)
      exfalso.
      assert (topLike (t_arrow (t_and A1 B1) t_top)). {
        apply H;
        constructor*;
        [apply S_andl1 | apply S_andl2];
        auto_sub.
      }
      inversion H0.
  - intros H C S1 S2.
    apply toplike_super_top.
    gen B C.
    induction* A;
      intros B H;
      [ induction* B | induction* B | skip ];
      intros C S1 S2;
      try solve [inverts H].
    + (* int arr *)
      induction* C;
        inverts S1;
        inverts* S2.
    + (* int and *)
      induction* C;
      inverts H;
      inverts* S1;
      try solve [
        inverts S2;
        [ forwards*: IHB1 |
          forwards*: IHB2 ]
          ].
      assert (T1 : sub (t_and B1 B2) C1) by auto_sub.
      forwards*: IHC1 T1.
      assert (T2 : sub (t_and B1 B2) C2) by auto_sub.
      forwards*: IHC2 T2.
    + (* arr int *)
      induction* C;
        inverts S1;
        inverts* S2.
    + (* arr and *)
      induction* C;
      inverts* H;
      inverts* S1.
      *
        inverts S2;
        forwards*: IHB1.
      * 
      assert (T1 : sub (t_and B1 B2) C1) by auto_sub. 
      forwards*: IHC1 T1.
      assert (T2 : sub (t_and B1 B2) C2) by auto_sub.
      forwards*: IHC2 T2.
Qed.

    
Lemma disjoint_domain_type: forall A B C B',
    disjointSpec (t_arrow B C) A -> disjointSpec (t_arrow B' C) A.
Proof.
  intros A B C B' H.
  apply disjoint_eqv in H.
  apply disjoint_eqv.
  induction* A;
    invert* H.
Qed.
  

Lemma disjoint_and: forall A B C,
    disjointSpec (t_and B C) A <-> disjointSpec B A /\ disjointSpec C A.
Proof.
  split;
  intro H.
  - apply disjoint_eqv in H.
    split;
      apply disjoint_eqv;
      induction A;
      invert* H.
  - destruct H.
    apply disjoint_eqv in H.
    apply disjoint_eqv in H0.
    apply disjoint_eqv.
    induction* A.
Qed.

Lemma disjoint_symmetric: forall A B,
    disjointSpec A B -> disjointSpec B A.
Proof.
  intros A B H.
  unfold disjointSpec in H.
  unfold disjointSpec.
  intros C H0 H1.
  forwards*: H.
Qed.


(* principal types for values*)
Fixpoint principal_type (v:value) : typ :=
  match v with
  | v_top => t_top
  | (v_topv _) => t_top
  | (v_lit i5) => t_int
  | (v_absv e A B) => t_arrow A B
  | (v_merge v1 v2) => t_and (principal_type v1) (principal_type v2)
  end.

Lemma principal_type_disjoint: forall v A B,
    Vtyping v A -> disjointSpec A B -> disjointSpec (principal_type v) B.
Proof.
  intros v A B. gen A B.
  induction v;
    intros C D Typ Dis;
    inverts* Typ;
    simple.
  - forwards*: disjoint_domain_type.
  - apply disjoint_and in Dis.
    lets [DA DB]: Dis.
    forwards Dv1: IHv1 H1 DA.
    forwards Dv2: IHv2 H2 DB.
    apply~ disjoint_and.
Qed.

Lemma principal_types_disjoint: forall v1 A v2 B,
    Vtyping v1 A -> Vtyping v2 B -> disjointSpec A B -> disjointSpec (principal_type v1) (principal_type v2).
Proof.
  intros v1 A v2 B Typ1 Typ2 Dis.
  forwards* D1: principal_type_disjoint Typ1 Dis.
  apply disjoint_symmetric in D1.
  forwards* D2: principal_type_disjoint Typ2 D1.
  apply~ disjoint_symmetric.
Qed.


Lemma absv_typing_principal : forall A B D e,
    Vtyping (v_absv e A D) B -> Vtyping (v_absv e A D) (t_arrow A D).
Proof.
  intros A B D e H.
  inverts H.
  eapply Vtyp_absv.
  apply H3.
  auto.
  auto_sub.
Qed.

Lemma principal_type_checks: forall v A,
    Vtyping v A -> Vtyping v (principal_type v).
Proof.
  intros v A. gen A.
  induction v;
    intros C Typ;
    simple;
    try solve [constructor*].
  - inverts* Typ.
  - forwards*: absv_typing_principal.
  - inverts Typ.
    constructor*.
Qed.

Lemma principal_type_sub: forall v A,
    Vtyping v A -> sub (principal_type v) A.
Proof.
  intros v A H.
  induction H;
    simple;
    try solve [auto_sub].
  - apply~ S_arr.
    auto_sub.
  - assert (S1: sub (t_and (principal_type v1) (principal_type v2)) A) by constructor*.
    assert (S2: sub (t_and (principal_type v1) (principal_type v2)) B) by constructor*.
    forwards*: S_andr S1 S2.
Qed.


(* it requires Top<:Top->Top *)
(* changes. abs doesn't have unique type now *)
Lemma TypedReduce_sub: forall v v' A,
    TypedReduce v A v' -> sub (principal_type v) A.
Proof. 
  introv Red.
  induction Red;
    simple;
    try solve [inverts* Typ];
    try solve [auto_sub].
Qed.

Lemma disjoint_val_consistent: forall A B v1 v2,
    disjointSpec A B -> Vtyping v1 A -> Vtyping v2 B -> consistencySpec v1 v2.
Proof.
  intros A B v1 v2 Dis Typ1 Typ2.
  introv Ord Red1 Red2.
  forwards* Sub1': TypedReduce_sub Red1.
  forwards* Sub2': TypedReduce_sub Red2.
  forwards* Dis': principal_types_disjoint Typ1 Typ2.
  assert (Top: topLike A0). {
    unfold disjointSpec in Dis'.
    apply Dis'; assumption.
  }
  exfalso.
  forwards*: toplike_not_ord Top Ord.
Qed.
