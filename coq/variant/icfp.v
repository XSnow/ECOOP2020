Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Subtyping_inversion
        rules_inf2
        dunfield.

Require Import Omega.

Lemma open_dexp_eqn_aux :
                forall ee1 ee2 x n,
       x `notin` fv_dexp ee1 ->
       x `notin` fv_dexp ee2 ->
       open_dexp_wrt_dexp_rec n (de_var_f x) ee1 = open_dexp_wrt_dexp_rec n (de_var_f x) ee2
       -> ee1 = ee2.
Proof.
  apply_mutual_ind dexp_mutind;
  apply_mutual_ind dexp_mutind;
  default_simp;
  try solve [eapply_first_hyp; eauto].
  omega.
Qed.
  
Lemma open_dexp_eqn : forall x ee1 ee2,
       x `notin` fv_dexp ee1 ->
       x `notin` fv_dexp ee2 ->
       open_dexp_wrt_dexp ee1 (de_var_f x) = open_dexp_wrt_dexp ee2 (de_var_f x)
       -> ee1 = ee2.
Proof.
  intros x ee1 ee2 H H0 H1.
  unfold open_dexp_wrt_dexp in H1.
  pose proof open_dexp_eqn_aux.
  eauto.
Qed.


Lemma subtyping_completeness : forall A B,
    isub A B -> sub A B.
Proof.
  intros A B H.
  induction* H.
Qed.


(* completeness of typing with respect to the type system in ICFP 2016 *)
Theorem typing_completeness : forall G ee A e,
    ITyping G ee A e -> Etyping G e A /\ |e| = ee.
Proof with auto.
  intros G ee A e Typ.
  induction Typ...
  -
    split.
    eapply Etyp_abs.
    intros. 
    forwards* [? ?]: H1 H2.
    auto_sub.
    auto_sub.
    simpl.
    pick fresh x for (union L (union (fv_dexp (|e|)) (fv_dexp ee))).
    forwards* [? ?]: H1.
    rewrite erasure_open in H3.
    simpl in H3.
    forwards*: open_dexp_eqn H3.
    congruence.
  -
    lets [HT1 Era1]: IHTyp1.
    lets [HT2 Era2]: IHTyp2.
    split*.
    simpl.
    congruence.
  -
    lets [HT1 Era1]: IHTyp1.
    lets [HT2 Era2]: IHTyp2.
    simpl.
    split...
    congruence.
  -
    destruct IHTyp.
    apply subtyping_completeness in H.
    split*.
Qed.
