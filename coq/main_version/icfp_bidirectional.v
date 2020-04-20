Require Import Metalib.Metatheory.
Require Import syntax_ott
               Subtyping_inversion.

(* lambda_i bidirectional system + fixpoint*)
Inductive dexp : Set :=  (* lambda_i expressions *)
 | de_var_b (_:nat) (* bound variables *)
 | de_var_f (x:var) (* free variables *)
 | de_top : dexp (* top *)
 | de_lit (i5:i) (* lit *)
 | de_abs (ee:dexp) (* abstractions *)
 | de_app (ee1:dexp) (ee2:dexp) (* applications *)
 | de_merge (ee1:dexp) (ee2:dexp) (* merge *)
 | de_ann (ee:dexp) (A:typ) (* annotation *)
 | de_fixpoint (ee:dexp) (* fixpoint *).

Inductive dirflag : Set :=  (* type checking direction *)
 | Inf : dirflag
 | Chk : dirflag.

(* lambdai type wellformedness using our disjointness *)
Inductive WF : ctx -> typ -> Prop :=
 | Wf_int : forall (G:ctx),
     WF G t_int
 | Wf_top : forall (G:ctx),
     WF G t_top
 | Wf_arr : forall (G:ctx) (A B:typ),
     WF G A ->
     WF G B ->
     WF G (t_arrow A B)
 | Wf_and : forall (G:ctx) (A B:typ),
     WF G A ->
     WF G B ->
     disjointSpec A B  ->
     WF G (t_and A B).

(* opening up abstractions under locally nameless encoding *)
Fixpoint open_dexp_wrt_dexp_rec (k:nat) (ee_5:dexp) (ee__6:dexp) {struct ee__6}: dexp :=
  match ee__6 with
  | (de_var_b nat) =>
      match lt_eq_lt_dec nat k with
        | inleft (left _) => de_var_b nat
        | inleft (right _) => ee_5
        | inright _ => de_var_b (nat - 1)
      end
  | (de_var_f x) => de_var_f x
  | de_top => de_top
  | (de_lit i5) => de_lit i5
  | (de_abs ee) => de_abs (open_dexp_wrt_dexp_rec (S k) ee_5 ee)
  | (de_app ee1 ee2) => de_app (open_dexp_wrt_dexp_rec k ee_5 ee1) (open_dexp_wrt_dexp_rec k ee_5 ee2)
  | (de_merge ee1 ee2) => de_merge (open_dexp_wrt_dexp_rec k ee_5 ee1) (open_dexp_wrt_dexp_rec k ee_5 ee2)
  | (de_ann ee A) => de_ann (open_dexp_wrt_dexp_rec k ee_5 ee) A
  | (de_fixpoint ee) => de_fixpoint (open_dexp_wrt_dexp_rec (S k) ee_5 ee)
  end.

Definition open_dexp_wrt_dexp ee_5 ee__6 := open_dexp_wrt_dexp_rec 0 ee__6 ee_5.

(* lambdai bidirectional typing *)
Inductive IBTyping : ctx -> dexp -> dirflag -> typ -> exp -> Prop :=
 | IBTyp_top : forall (G:ctx),
      uniq  G  ->
     IBTyping G de_top Inf t_top e_top
 | IBTyp_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     IBTyping G (de_lit i5) Inf t_int (e_lit i5)
 | IBTyp_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     IBTyping G (de_var_f x) Inf A (e_var_f x)
 | IBTyp_lam : forall (L:vars) (G:ctx) (ee:dexp) (A B:typ) (e:exp),
     WF G A ->
      ( forall x , x \notin  L  -> IBTyping  (cons ( x , A )  G )   ( open_dexp_wrt_dexp ee (de_var_f x) )  Chk B  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     IBTyping G (de_abs ee) Chk (t_arrow A B)  ( (e_abs A e B) )
 | IBTyp_app : forall (G:ctx) (ee1 ee2:dexp) (B:typ) (e1 e2:exp) (A:typ),
     IBTyping G ee1 Inf (t_arrow A B) e1 ->
     IBTyping G ee2 Chk A e2 ->
     IBTyping G (de_app ee1 ee2) Inf B (e_app e1 e2)
 | IBTyp_merge : forall (G:ctx) (ee1 ee2:dexp) (A B:typ) (e1 e2:exp),
     IBTyping G ee1 Inf A e1 ->
     IBTyping G ee2 Inf B e2 ->
      disjointSpec A B  ->
     IBTyping G (de_merge ee1 ee2) Inf (t_and A B) (e_merge e1 e2)
 | IBTyp_anno : forall (G:ctx) (ee:dexp) (A:typ) (e:exp),
     IBTyping G ee Chk A e ->
     IBTyping G (de_ann ee A) Inf A e
 | IBTyp_sub : forall (G:ctx) (ee:dexp) (B:typ) (e:exp) (A:typ),
     IBTyping G ee Inf A e ->
     sub A B ->
     IBTyping G ee Chk B (e_anno e B)
 | IBTyp_fix : forall (L:vars) (G:ctx) (ee:dexp) (A:typ) (e:exp),
     WF G A ->
      ( forall x , x \notin  L  -> IBTyping  (cons ( x , A )  G )   ( open_dexp_wrt_dexp ee (de_var_f x) )  Chk A  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     IBTyping G (de_fixpoint ee) Chk A (e_fixpoint e A).

(** infrastructure *)
Hint Constructors WF IBTyping lc_exp : core.

(* completeness of typing with respect to the bidirectional type system in ICFP 2016 *)
Theorem typing_completeness : forall G ee dir A e,
    IBTyping G ee dir A e -> Etyping G e A.
Proof with eauto.
  intros G ee dir A e Typ.
  induction Typ...
  - (* abs *)
    eapply Etyp_abs.
    intros. apply H1 in H2...
    apply sub_reflexivity. apply sub_reflexivity.
Qed.
