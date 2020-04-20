Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Logic. Import Decidable.
Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Key_Properties.
Require Import Coq.Strings.String.


Lemma TypedReduce_unique: forall (v v1 v2 : value) (A: typ),
    (exists B, Vtyping v B) -> TypedReduce v A v1 -> TypedReduce v A v2 -> v1 = v2.
Proof.
  intros v v1 v2 A H R1 R2.
  gen v2.
  induction R1; introv R2;
    try solve [inverts* R2].
  - (* top *)
    forwards*: TypedReduce_toplike R2.
  - (* mergel *)
    inverts* R2.
    +
      inversion H1.
    +
      lets [B H']: H.
      inverts* H'.
    +
      lets [B H']: H.
      inversion H'.
      forwards*: H10 R1 H5.
    +
      inverts* H1.
  - (* merger *)
    lets [B H']: H;
      inverts* R2;
      inverts* H'.
    + inversion H1.
    + forwards*: H10 H5 R1.
    + inverts* H1.
  - (* and *)
    inverts* R2;
      try solve [inversion H2]. (* inversion ord (t_and _ _) *)
    forwards*: IHR1_1.
    forwards*: IHR1_2.
    congruence.
Qed.


Theorem step_unique: forall A (e e1 e2 : exp),
    Etyping nil e A -> step e e1 -> step e e2 -> e1 = e2.
Proof.
  introv Typ Red1.
  gen A e2.
  lets Red1' : Red1.
  induction Red1;
    introv Typ Red2.
  - Case "absv".
    inverts* Red2. 
  - Case "beta". 
    inverts* Red2.
    + SCase "beta".
      inverts* Typ.
      inverts* H4. (* Typing condition for the following assert *)
      assert (v' = v'0) by forwards*: TypedReduce_unique H0 H7.
      congruence.
    + SCase "app1".
      inverts* H5.
    + SCase "app2".
      forwards*: step_not_value H5.
  - Case "annov".
    inverts* Red2.
    + SCase "annov".
      forwards*: TypedReduce_unique H H3.
      inverts* Typ.
      inverts* H4.
      congruence.
    + SCase "anno".
      forwards*: step_not_value H3.
  - Case "appl".
    inverts* Red2.
    + SCase "absv".
      forwards*: step_not_value Red1.
    + SCase "appl".
      inverts* Typ.
      forwards*: IHRed1.
      congruence.
    + SCase "appr".
      forwards*: step_not_value Red1.
  - Case "appr".
    inverts* Red2;
      try solve [forwards*: step_not_value Red1].
    + SCase "appl".
      forwards*: step_not_value H4.
    + SCase "appr".
      inverts* Typ.
      forwards*: IHRed1.
      congruence.
  - Case "mergel".
    inverts* Red2;
      try solve [forwards*: step_not_value Red1].
    + SCase "mergel".
      inverts* Typ.
      * SSCase "disjoint".
        forwards*: IHRed1.
        congruence.
  - Case "merger".
    inverts* Red2;
      try solve [forwards*: step_not_value Red1].
    + SCase "mergel".
      forwards*: step_not_value H4.
    + SCase "merger".
      inverts* Typ.
      * SSCase "disjoint".
        forwards*: IHRed1.
        congruence.
  - Case "anno".
    inverts* Red2;
      inverts* Typ;
      try solve [inverts* Red1];
      try solve [lets*: step_not_value Red1].
    forwards*: IHRed1.
    congruence.
  - Case "e_val (v_merge _ _ )".
    inverts* Red2;
      forwards*: step_not_value H5.
  - Case "e_val (v_lit _ )".
    inverts* Red2.
  - Case "e_val (v_top)".
    inverts* Red2.
  - Case "fix".
    inverts* Red2. 
Qed.
