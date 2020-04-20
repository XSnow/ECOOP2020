Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf
               Subtyping_inversion.


Lemma abs_typing_principal : forall G A B D e,
    Etyping G (e_abs A e D) B -> Etyping G (e_abs A e D) (t_arrow A D).
Proof.
  intros G A B D e H.
  inverts H.
  eapply Etyp_abs.
  apply H4.
  auto_sub.
  auto.
Qed.


(* TypedReduce *)
(*
Lemma TypedReduce_top : forall (v v1 v2 : value), TypedReduce v t_top v1 -> TypedReduce v t_top v2 -> v1 = v2.
Proof.
  introv R1 R2.
  inverts* R1; try solve [inversion H2];
    inverts* R2; try solve [inversion H2];
      try solve [inversion H1].
Qed.
 *)
  
Lemma TypedReduce_top_normal : forall (v v': exp),
    TypedReduce v t_top v' -> v' = e_top.
Proof.
  intros v v' H.
  remember t_top.
  induction H;
    try solve [inverts* Heqt].
Qed.

Lemma TypedReduce_toparr_normal : forall (v v': exp) (A B: typ),
    topLike (t_arrow A B) -> TypedReduce v (t_arrow A B) v' -> v' = e_abs t_top e_top B.
Proof.
  intros v v' A B H H0.
  remember (t_arrow A B).
  induction H0;
    try solve [inverts* Heqt];
    try inverts* H.
Qed.
  
Lemma TypedReduce_toplike :
  forall A, topLike A ->
            forall (v1 v2 v1' v2' : exp), TypedReduce v1 A v1' -> TypedReduce v2 A v2' -> v1' = v2'.
Proof.
  intros A Typ.
  induction Typ;
    introv Red1 Red2.
  - apply TypedReduce_top_normal in Red1.
    apply TypedReduce_top_normal in Red2.
    subst*.
  - inversion Red1; subst;
      try solve [invert* H1].
    inversion Red2; subst;
      try solve [invert* H1].
    forwards: IHTyp1 H2 H3.
    forwards: IHTyp2 H4 H6.
    subst*.
  - assert (topLike (t_arrow A B)) by constructor*.
    apply TypedReduce_toparr_normal in Red1.
    apply TypedReduce_toparr_normal in Red2.
    subst*.
    assumption.
    assumption.
Qed.


(* topLike *)
Lemma toplike_super_top: forall A,
    topLike A <-> sub t_top A.
Proof.
  intro A.
  split.
  - intro H.
    induction H.
    + apply sub_reflexivity.
    + apply~ S_andr.
    + apply~ S_toparr.
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
  - destruct IHA2.
    + left*.
    + right.
      unfold not.
      intros H0.
      inverts H0.
      auto.
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
      constructor.
      clear IHA1 IHB1.
      apply IHA2.
      intros.
      remember (t_arrow (t_and A1 B1) C).
      assert (TL: topLike t). {
        apply H;
          subst;
          constructor*;
          [apply S_andl1 | apply S_andl2];
          auto_sub.
      }
      subst.
      inverts* TL.
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
    + (* arr arr *)
      inverts H.
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
Fixpoint principal_type (v:exp) : typ :=
  match v with
  | e_top => t_top
  | (e_lit i5) => t_int
  | (e_abs A e B) => t_arrow A B
  | (e_merge v1 v2) => t_and (principal_type v1) (principal_type v2)
  | _ => t_top
  end.

Lemma principal_type_disjoint: forall v A B,
    value v -> Etyping nil v A -> disjointSpec A B -> disjointSpec (principal_type v) B.
Proof.
  intros v A B Val. gen A B.
  induction Val;
    intros C D Typ Dis;
    inverts* Typ;
    simple.
  - forwards*: disjoint_domain_type.
  - apply disjoint_and in Dis.
    lets [DA DB]: Dis.
    forwards Dv1: IHVal1 H1 DA.
    forwards Dv2: IHVal2 H3 DB.
    apply~ disjoint_and.
  - apply disjoint_and in Dis.
    lets [DA DB]: Dis.
    forwards Dv1: IHVal1 H3 DA.
    forwards Dv2: IHVal2 H5 DB.
    apply~ disjoint_and.
Qed.

Lemma principal_types_disjoint: forall v1 A v2 B,
    value v1 -> Etyping nil v1 A -> value v2 -> Etyping nil v2 B -> disjointSpec A B -> disjointSpec (principal_type v1) (principal_type v2).
Proof.
  intros v1 A v2 B Val1 Typ1 Val2 Typ2 Dis.
  forwards* D1: principal_type_disjoint Typ1 Dis.
  apply disjoint_symmetric in D1.
  forwards* D2: principal_type_disjoint Typ2 D1.
  apply~ disjoint_symmetric.
Qed.

Lemma principal_type_checks: forall v A,
    value v -> Etyping nil v A -> Etyping nil v (principal_type v).
Proof.
  intros v A Val. gen A.
  induction Val;
    intros C Typ;
    simple;
    try solve [constructor*].
  - forwards*: abs_typing_principal.
  - inverts Typ.
    +
      constructor*.
      forwards*: principal_types_disjoint H1 H3 H5.
    +
      apply~ Etyp_mergev.
      forwards*: IHVal1.
      forwards*: IHVal2.
Qed.

Lemma principal_type_sub: forall v A,
    value v -> Etyping nil v A -> sub (principal_type v) A.
Proof.
  intros v A Val H.
  induction H;
    inverts* Val;
    simple;
    try solve auto_sub.
  - apply~ S_arr.
    auto_sub.
  - assert (S1: sub (t_and (principal_type e1) (principal_type e2)) A) by constructor*.
    assert (S2: sub (t_and (principal_type e1) (principal_type e2)) B) by constructor*.
    forwards*: S_andr S1 S2.
  - assert (S1: sub (t_and (principal_type v1) (principal_type v2)) A) by constructor*.
    assert (S2: sub (t_and (principal_type v1) (principal_type v2)) B) by constructor*.
    forwards*: S_andr S1 S2.
Qed.


(* it requires Top<:Top->Top *)
(* changes. abs doesn't have unique type now *)
Lemma TypedReduce_sub: forall v v' A,
    value v -> TypedReduce v A v' -> sub (principal_type v) A.
Proof. 
  introv Val Red.
  induction Red;
    simple;
    try solve [inverts Val; inverts* Typ];
    try solve [auto_sub];
    try solve [inverts* Val].
  - (* toparr *)
    eapply (sub_transtivity _ t_top).
    constructor.
    apply toplike_super_top.
    auto.
Qed.

Lemma disjoint_val_consistent: forall A B v1 v2,
    disjointSpec A B -> value v1 -> value v2 -> Etyping nil v1 A -> Etyping nil v2 B -> consistencySpec v1 v2.
Proof.
  intros A B v1 v2 Dis Val1 Val2 Typ1 Typ2.
  unfold consistencySpec.
  introv Red1 Red2.
  forwards* Sub1': TypedReduce_sub Red1.
  forwards* Sub2': TypedReduce_sub Red2.
  forwards* Dis': principal_types_disjoint Typ1 Typ2.
  assert (Top: topLike A0). {
    unfold disjointSpec in Dis'.
    apply Dis'; assumption.
  }
  forwards*: TypedReduce_toplike Top Red1 Red2.
Qed.
