Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Import syntax_ott
               rules_inf.
Require Import Omega.



Lemma sub_inversion_arrow : forall A1 A2 B1 B2,
    sub (t_arrow A1 A2) (t_arrow B1 B2) -> sub B1 A1 /\ sub A2 B2.
Proof.
  intros.
  inversion H.
  subst.
  auto.
Qed.


Lemma sub_reflexivity : forall A,
    sub A A.
Proof.
  intros A.
  induction* A.
Qed.

Lemma sub_transtivity_aux : forall i,
    forall A B C,
      size_typ A + size_typ B + size_typ C = i ->
      sub A B -> sub B C -> sub A C.
Proof.
  intros i. pattern i. apply lt_wf_rec.
  clear i; intros i H.
  intros A B C He S1.
  lets S1':S1.
  gen H C.
  induction* S1;
    intros H C Hs S2.
  - (* B:=t_top *)
    remember t_top.
    gen i.
    induction* S2;
      try solve [inverts Heqt].
    intros i H Hs.
    constructor;
      eapply_first_lt_hyp;
      eauto;
      default_simp;
      omega.
  - (* arr *)
    remember (t_arrow B1 B2).
    lets S2': S2.
    gen i.
    induction S2;
      intros;
      inverts* Heqt.
    + apply S_arr;
      eapply_first_lt_hyp;
        eauto;
        default_simp;
        omega.
    + constructor;
        eapply_first_lt_hyp;
        eauto;
        default_simp;
        omega.
  - (* andl1 *)
    apply S_andl1.
      eapply_first_lt_hyp;
        eauto;
        default_simp;
        omega.
  - (* andl2 *)
    apply S_andl2.
      eapply_first_lt_hyp;
        eauto;
        default_simp;
        omega.
  - (* andr *)
    remember (t_and A2 A3).
    lets S2': S2.
    gen i.
    induction S2;
      intros;
      inverts* Heqt.
    + forwards: H S1_1 S2;
        eauto;
        default_simp;
        omega.
    + forwards: H S1_2 S2;
        eauto;
        default_simp;
        omega.
    + constructor;
      eapply_first_lt_hyp;
        eauto;
        default_simp;
        omega.
Qed.

Lemma sub_transtivity : forall A B C,
    sub A B -> sub B C -> sub A C.
Proof.
  intros A B C.
  pose proof (sub_transtivity_aux).
  intuition eauto.
Qed.


Ltac auto_sub :=
  try match goal with
      | [ |- sub ?A ?A ] => apply sub_reflexivity
      | [ |- sub (t_and ?A ?B) ?A ] => (apply~ S_andl1; auto_sub)
      | [ |- sub (t_and ?A ?B) ?B ] => (apply~ S_andl2; auto_sub)
      | [ H: sub ?A ?C |- sub (t_and ?A ?B) ?C ] => apply~ S_andl1
      | [ H: sub ?B ?C |- sub (t_and ?A ?B) ?C ] => apply~ S_andl2
      | [ H: sub ?A (t_and ?B ?C) |- sub ?A ?B ] => (
        eapply sub_transtivity;
        try apply H;
        try apply S_andl1;
        try apply sub_reflexivity)
      | [ H: sub ?A (t_and ?B ?C) |- sub ?A ?C ] => (
        try eapply sub_transtivity;
        try apply H;
        try apply S_andl2;
        try apply sub_reflexivity)
      | [ H: sub (t_arrow _ _) (t_arrow _ _) |- sub _ _ ] => (inverts H; auto_sub)
      | [ H1: sub ?A ?B, H2: sub ?B ?C |- sub ?A ?C ] => forwards*: sub_transtivity H1 H2
      | [ H1: sub ?A ?B, H2: sub ?B ?C |- sub ?A ?C ] => forwards*: sub_transtivity H1 H2
    | |- _ => try constructor*
      end.
