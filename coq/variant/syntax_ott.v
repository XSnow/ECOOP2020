(* !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! *)
Require Import Metalib.Metatheory.
(** syntax *)
Definition i := nat.

Inductive typ : Set :=  (*r types *)
 | t_int : typ (*r int *)
 | t_top : typ (*r top *)
 | t_arrow (A:typ) (B:typ) (*r function types *)
 | t_and (A:typ) (B:typ) (*r intersection *).

Inductive dexp : Set :=  (*r expressions *)
 | de_var_b (_:nat) (*r variables *)
 | de_var_f (x:var) (*r variables *)
 | de_top : dexp (*r top *)
 | de_lit (i5:i) (*r lit *)
 | de_abs (ee:dexp) (*r abstractions *)
 | de_app (ee1:dexp) (ee2:dexp) (*r applications *)
 | de_merge (ee1:dexp) (ee2:dexp) (*r merge *)
 | de_fixpoint (ee:dexp) (*r fixpoint *).

Inductive st : Set :=  (*r input type or projection label *)
 | st_ty (A:typ).

Definition ctx : Set := list ( atom * typ ).

Inductive exp : Set :=  (*r expressions *)
 | e_var_b (_:nat) (*r variables *)
 | e_var_f (x:var) (*r variables *)
 | e_top : exp (*r top *)
 | e_lit (i5:i) (*r lit *)
 | e_abs (e:exp) (A:typ) (B:typ) (*r abstractions *)
 | e_fixpoint (e:exp) (A:typ) (*r fixpoint *)
 | e_app (e1:exp) (e2:exp) (*r applications *)
 | e_merge (e1:exp) (e2:exp) (*r merge *)
 | e_anno (e:exp) (A:typ) (*r annotation *)
 | e_val (v:value) (*r value *)
with value : Set :=  (*r values *)
 | v_top : value (*r top *)
 | v_lit (i5:i) (*r lit *)
 | v_topv (v:value) (*r topv *)
 | v_absv (e:exp) (A:typ) (B:typ) (*r abstractions *)
 | v_merge (v1:value) (v2:value) (*r merge *).

Definition ls : Set := list st.

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
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
  | (de_fixpoint ee) => de_fixpoint (open_dexp_wrt_dexp_rec (S k) ee_5 ee)
end.

Fixpoint open_value_wrt_exp_rec (k:nat) (e5:exp) (v_5:value) {struct v_5}: value :=
  match v_5 with
  | v_top => v_top 
  | (v_lit i5) => v_lit i5
  | (v_topv v) => v_topv (open_value_wrt_exp_rec k e5 v)
  | (v_absv e A B) => v_absv (open_exp_wrt_exp_rec (S k) e5 e) A B
  | (v_merge v1 v2) => v_merge (open_value_wrt_exp_rec k e5 v1) (open_value_wrt_exp_rec k e5 v2)
end
with open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => e_var_b nat
        | inleft (right _) => e_5
        | inright _ => e_var_b (nat - 1)
      end
  | (e_var_f x) => e_var_f x
  | e_top => e_top 
  | (e_lit i5) => e_lit i5
  | (e_abs e A B) => e_abs (open_exp_wrt_exp_rec (S k) e_5 e) A B
  | (e_fixpoint e A) => e_fixpoint (open_exp_wrt_exp_rec (S k) e_5 e) A
  | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_merge e1 e2) => e_merge (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_anno e A) => e_anno (open_exp_wrt_exp_rec k e_5 e) A
  | (e_val v) => e_val (open_value_wrt_exp_rec k e_5 v)
end.

Definition open_dexp_wrt_dexp ee_5 ee__6 := open_dexp_wrt_dexp_rec 0 ee__6 ee_5.

Definition open_value_wrt_exp e5 v_5 := open_value_wrt_exp_rec 0 v_5 e5.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_dexp *)
Inductive lc_dexp : dexp -> Prop :=    (* defn lc_dexp *)
 | lc_de_var_f : forall (x:var),
     (lc_dexp (de_var_f x))
 | lc_de_top : 
     (lc_dexp de_top)
 | lc_de_lit : forall (i5:i),
     (lc_dexp (de_lit i5))
 | lc_de_abs : forall (ee:dexp),
      ( forall x , lc_dexp  ( open_dexp_wrt_dexp ee (de_var_f x) )  )  ->
     (lc_dexp (de_abs ee))
 | lc_de_app : forall (ee1 ee2:dexp),
     (lc_dexp ee1) ->
     (lc_dexp ee2) ->
     (lc_dexp (de_app ee1 ee2))
 | lc_de_merge : forall (ee1 ee2:dexp),
     (lc_dexp ee1) ->
     (lc_dexp ee2) ->
     (lc_dexp (de_merge ee1 ee2))
 | lc_de_fixpoint : forall (ee:dexp),
      ( forall x , lc_dexp  ( open_dexp_wrt_dexp ee (de_var_f x) )  )  ->
     (lc_dexp (de_fixpoint ee)).

(* defns LC_value_exp *)
Inductive lc_value : value -> Prop :=    (* defn lc_value *)
 | lc_v_top : 
     (lc_value v_top)
 | lc_v_lit : forall (i5:i),
     (lc_value (v_lit i5))
 | lc_v_topv : forall (v:value),
     (lc_value v) ->
     (lc_value (v_topv v))
 | lc_v_absv : forall (e:exp) (A B:typ),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_value (v_absv e A B))
 | lc_v_merge : forall (v1 v2:value),
     (lc_value v1) ->
     (lc_value v2) ->
     (lc_value (v_merge v1 v2))
with lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_e_var_f : forall (x:var),
     (lc_exp (e_var_f x))
 | lc_e_top : 
     (lc_exp e_top)
 | lc_e_lit : forall (i5:i),
     (lc_exp (e_lit i5))
 | lc_e_abs : forall (e:exp) (A B:typ),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs e A B))
 | lc_e_fixpoint : forall (e:exp) (A:typ),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_fixpoint e A))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_merge : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_merge e1 e2))
 | lc_e_anno : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_exp (e_anno e A))
 | lc_e_val : forall (v:value),
     (lc_value v) ->
     (lc_exp (e_val v)).
(** free variables *)
Fixpoint fv_value (v_5:value) : vars :=
  match v_5 with
  | v_top => {}
  | (v_lit i5) => {}
  | (v_topv v) => (fv_value v)
  | (v_absv e A B) => (fv_exp e)
  | (v_merge v1 v2) => (fv_value v1) \u (fv_value v2)
end
with fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {{x}}
  | e_top => {}
  | (e_lit i5) => {}
  | (e_abs e A B) => (fv_exp e)
  | (e_fixpoint e A) => (fv_exp e)
  | (e_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_merge e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_anno e A) => (fv_exp e)
  | (e_val v) => (fv_value v)
end.

Fixpoint fv_dexp (ee_5:dexp) : vars :=
  match ee_5 with
  | (de_var_b nat) => {}
  | (de_var_f x) => {{x}}
  | de_top => {}
  | (de_lit i5) => {}
  | (de_abs ee) => (fv_dexp ee)
  | (de_app ee1 ee2) => (fv_dexp ee1) \u (fv_dexp ee2)
  | (de_merge ee1 ee2) => (fv_dexp ee1) \u (fv_dexp ee2)
  | (de_fixpoint ee) => (fv_dexp ee)
end.

(** substitutions *)
Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (if eq_var x x5 then e_5 else (e_var_f x))
  | e_top => e_top 
  | (e_lit i5) => e_lit i5
  | (e_abs e A B) => e_abs (subst_exp e_5 x5 e) A B
  | (e_fixpoint e A) => e_fixpoint (subst_exp e_5 x5 e) A
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_merge e1 e2) => e_merge (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_anno e A) => e_anno (subst_exp e_5 x5 e) A
  | (e_val v) => e_val (subst_value e_5 x5 v)
end
with subst_value (e5:exp) (x5:var) (v_5:value) {struct v_5} : value :=
  match v_5 with
  | v_top => v_top 
  | (v_lit i5) => v_lit i5
  | (v_topv v) => v_topv (subst_value e5 x5 v)
  | (v_absv e A B) => v_absv (subst_exp e5 x5 e) A B
  | (v_merge v1 v2) => v_merge (subst_value e5 x5 v1) (subst_value e5 x5 v2)
end.

Fixpoint subst_dexp (ee_5:dexp) (x5:var) (ee__6:dexp) {struct ee__6} : dexp :=
  match ee__6 with
  | (de_var_b nat) => de_var_b nat
  | (de_var_f x) => (if eq_var x x5 then ee_5 else (de_var_f x))
  | de_top => de_top 
  | (de_lit i5) => de_lit i5
  | (de_abs ee) => de_abs (subst_dexp ee_5 x5 ee)
  | (de_app ee1 ee2) => de_app (subst_dexp ee_5 x5 ee1) (subst_dexp ee_5 x5 ee2)
  | (de_merge ee1 ee2) => de_merge (subst_dexp ee_5 x5 ee1) (subst_dexp ee_5 x5 ee2)
  | (de_fixpoint ee) => de_fixpoint (subst_dexp ee_5 x5 ee)
end.


(** definitions *)

(* defns TopLikeType *)
Inductive topLike : typ -> Prop :=    (* defn topLike *)
 | TL_top : 
     topLike t_top
 | TL_and : forall (A B:typ),
     topLike A ->
     topLike B ->
     topLike (t_and A B).

(* defns OrdinaryType *)
Inductive ord : typ -> Prop :=    (* defn ord *)
 | O_int : 
     ord t_int
 | O_arrow : forall (A B:typ),
     ord (t_arrow A B).

(* defns Disjoint *)
Inductive disjoint : typ -> typ -> Prop :=    (* defn disjoint *)
 | D_topL : forall (A:typ),
     disjoint t_top A
 | D_topR : forall (A:typ),
     disjoint A t_top
 | D_andL : forall (A1 A2 B:typ),
     disjoint A1 B ->
     disjoint A2 B ->
     disjoint (t_and A1 A2) B
 | D_andR : forall (A B1 B2:typ),
     disjoint A B1 ->
     disjoint A B2 ->
     disjoint A (t_and B1 B2)
 | D_axIntArr : forall (A1 A2:typ),
     disjoint t_int (t_arrow A1 A2)
 | D_axArrInt : forall (A1 A2:typ),
     disjoint (t_arrow A1 A2) t_int.

(* defns Subtyping *)
Inductive sub : typ -> typ -> Prop :=    (* defn sub *)
 | S_z : 
     sub t_int t_int
 | S_top : forall (A:typ),
     sub A t_top
 | S_arr : forall (A1 A2 B1 B2:typ),
     sub B1 A1 ->
     sub A2 B2 ->
     sub (t_arrow A1 A2) (t_arrow B1 B2)
 | S_andl1 : forall (A1 A2 A3:typ),
     sub A1 A3 ->
     sub (t_and A1 A2) A3
 | S_andl2 : forall (A1 A2 A3:typ),
     sub A2 A3 ->
     sub (t_and A1 A2) A3
 | S_andr : forall (A1 A2 A3:typ),
     sub A1 A2 ->
     sub A1 A3 ->
     sub A1 (t_and A2 A3).

(* defns Semantics *)
Inductive TypedReduce : value -> typ -> value -> Prop :=    (* defn TypedReduce *)
 | TReduce_lit : forall (i5:i),
     TypedReduce (v_lit i5) t_int (v_lit i5)
 | TReduce_top : forall (v:value),
     lc_value v ->
     TypedReduce v t_top (v_topv v)
 | TReduce_arrow : forall (e:exp) (A B C D:typ),
     lc_value (v_absv e A B) ->
     sub C A ->
     sub B D ->
     TypedReduce (v_absv e A B)  (t_arrow C D)  (v_absv e A D)
 | TReduce_mergevl : forall (v1 v2:value) (A:typ) (v1':value),
     lc_value v2 ->
     TypedReduce v1 A v1' ->
     ord A ->
     TypedReduce (v_merge v1 v2) A v1'
 | TReduce_mergevr : forall (v1 v2:value) (A:typ) (v2':value),
     lc_value v1 ->
     TypedReduce v2 A v2' ->
     ord A ->
     TypedReduce (v_merge v1 v2) A v2'
 | TReduce_and : forall (v:value) (A B:typ) (v1 v2:value),
     TypedReduce v A v1 ->
     TypedReduce v B v2 ->
     TypedReduce v (t_and A B) (v_merge v1 v2)
with step : exp -> exp -> Prop :=    (* defn step *)
 | Step_abs : forall (e:exp) (A B:typ),
     lc_exp (e_abs e A B) ->
     step (e_abs e A B) (e_val (v_absv e A B))
 | Step_beta : forall (e:exp) (A B:typ) (v v':value),
     lc_value (v_absv e A B) ->
     TypedReduce v A v' ->
     step (e_app  ( (e_val (v_absv e A B)) )  (e_val v)) (e_anno  (  (open_exp_wrt_exp  e (e_val v') )  )  B)
 | Step_annov : forall (v:value) (A:typ) (v':value),
     TypedReduce v A v' ->
     step (e_anno (e_val v) A) (e_val v')
 | Step_appl : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (e_app e1 e2) (e_app e1' e2)
 | Step_appr : forall (v1:value) (e2 e2':exp),
     lc_value v1 ->
     step e2 e2' ->
     step (e_app (e_val v1) e2) (e_app (e_val v1) e2')
 | Step_mergel : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (e_merge e1 e2) (e_merge e1' e2)
 | Step_merger : forall (v1:value) (e2 e2':exp),
     lc_value v1 ->
     step e2 e2' ->
     step (e_merge (e_val v1) e2) (e_merge (e_val v1) e2')
 | Step_anno : forall (e:exp) (A:typ) (e':exp),
     step e e' ->
     step (e_anno e A) (e_anno e' A)
 | Step_mergev : forall (v1 v2:value),
     lc_value v1 ->
     lc_value v2 ->
     step (e_merge (e_val v1) (e_val v2)) (e_val (v_merge v1 v2))
 | Step_litv : forall (i5:i),
     step (e_lit i5) (e_val (v_lit i5))
 | Step_topv : 
     step e_top (e_val v_top)
 | Step_fix : forall (e:exp) (A:typ),
     lc_exp (e_fixpoint e A) ->
     step (e_fixpoint e A)  (open_exp_wrt_exp  e (e_fixpoint e A) ) .



Definition disjointSpec A B :=
  forall C, sub A C -> sub B C -> topLike C.
  
Definition consistencySpec v1 v2 :=
  forall A v1' v2', ord A -> TypedReduce v1 A v1' -> TypedReduce v2 A v2' -> v1' = v2'.

(* defns Consistency *)
Inductive consistent : value -> value -> Prop :=    (* defn consistent *)
 | C_topL : forall (v:value),
     lc_value v ->
     consistent v_top v
 | C_topR : forall (v:value),
     lc_value v ->
     consistent v v_top
 | C_lit : forall (i5:i),
     consistent (v_lit i5) (v_lit i5)
 | C_absOne : forall (e:exp) (B C:typ),
     lc_value (v_absv e B C) ->
     consistent (v_absv e B C) (v_absv e B C)
 | C_litAbs : forall (i5:i) (e:exp) (B C:typ),
     lc_value (v_absv e B C) ->
     consistent (v_lit i5) (v_absv e B C)
 | C_absLit : forall (e:exp) (B C:typ) (i5:i),
     lc_value (v_absv e B C) ->
     consistent (v_absv e B C) (v_lit i5)
 | C_mergeL : forall (v1 v2 v:value),
     consistent v1 v ->
     consistent v2 v ->
     consistent (v_merge v1 v2) v
 | C_mergeR : forall (v v1 v2:value),
     consistent v v1 ->
     consistent v v2 ->
     consistent v (v_merge v1 v2).

(* defns Typing *)
Inductive Etyping : ctx -> exp -> typ -> Prop :=    (* defn Etyping *)
 | Etyp_val : forall (G:ctx) (v:value) (A:typ),
      uniq  G  ->
     Vtyping v A ->
     Etyping G (e_val v) A
 | Etyp_top : forall (G:ctx),
      uniq  G  ->
     Etyping G e_top t_top
 | Etyp_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     Etyping G (e_lit i5) t_int
 | Etyp_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     Etyping G (e_var_f x) A
 | Etyp_abs : forall (L:vars) (G:ctx) (e:exp) (A D C B:typ),
      ( forall x , x \notin  L  -> Etyping  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  B )  ->
     sub B D ->
     sub C A ->
     Etyping G  ( (e_abs e A D) )   (t_arrow C D) 
 | Etyp_app : forall (G:ctx) (e1 e2:exp) (B A:typ),
     Etyping G e2 A ->
     Etyping G e1 (t_arrow A B) ->
     Etyping G (e_app e1 e2) B
 | Etyp_merge : forall (G:ctx) (e1 e2:exp) (A B:typ),
     Etyping G e1 A ->
     Etyping G e2 B ->
      disjointSpec A B  ->
     Etyping G (e_merge e1 e2) (t_and A B)
 | Etyp_anno : forall (G:ctx) (e:exp) (A B:typ),
     Etyping G e B ->
     sub B A ->
     Etyping G  ( (e_anno e A) )  A
 | Etyp_fix : forall (L:vars) (G:ctx) (e:exp) (A:typ),
      ( forall x , x \notin  L  -> Etyping  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  A )  ->
     Etyping G  ( (e_fixpoint e A) )  A
with Vtyping : value -> typ -> Prop :=    (* defn Vtyping *)
 | Vtyp_top : 
     Vtyping v_top t_top
 | Vtyp_topv : forall (v:value) (A:typ),
     Vtyping v A ->
     Vtyping  ( (v_topv v) )  t_top
 | Vtyp_lit : forall (i5:i),
     Vtyping (v_lit i5) t_int
 | Vtyp_absv : forall (L:vars) (e:exp) (A D C B:typ),
      ( forall x , x \notin  L  -> Etyping  (cons ( x , A )   nil  )   ( open_exp_wrt_exp e (e_var_f x) )  B )  ->
     sub B D ->
     sub C A ->
     Vtyping  ( (v_absv e A D) )   (t_arrow C D) 
 | Vtyp_merge : forall (v1 v2:value) (A B:typ),
     Vtyping v1 A ->
     Vtyping v2 B ->
      consistencySpec v1 v2  ->
     Vtyping (v_merge v1 v2) (t_and A B).

(* defns DValue *)
Inductive DValue : dexp -> Prop :=    (* defn DValue *)
 | DVal_var : forall (x:var),
     DValue (de_var_f x)
 | DVal_top : 
     DValue de_top
 | DVal_nat : forall (i5:i),
     DValue (de_lit i5)
 | DVal_abs : forall (ee:dexp),
     lc_dexp (de_abs ee) ->
     DValue (de_abs ee)
 | DVal_merge : forall (vv1 vv2:dexp),
     DValue vv1 ->
     DValue vv2 ->
     DValue (de_merge vv1 vv2).

(* defns DSemantics *)
Inductive DunfieldStep : dexp -> dexp -> Prop :=    (* defn DunfieldStep *)
 | DStep_appl : forall (ee1 ee2 ee1':dexp),
     lc_dexp ee2 ->
     DunfieldStep ee1 ee1' ->
     DunfieldStep (de_app ee1 ee2) (de_app ee1' ee2)
 | DStep_appr : forall (vv1 ee2 ee2':dexp),
     DValue vv1 ->
     DunfieldStep ee2 ee2' ->
     DunfieldStep (de_app vv1 ee2) (de_app vv1 ee2')
 | DStep_beta : forall (ee vv:dexp),
     lc_dexp (de_abs ee) ->
     DValue vv ->
     DunfieldStep (de_app  ( (de_abs ee) )  vv)  (  (open_dexp_wrt_dexp  ee vv )  ) 
 | DStep_fix : forall (ee:dexp),
     lc_dexp (de_fixpoint ee) ->
     DunfieldStep (de_fixpoint ee)  (open_dexp_wrt_dexp  ee (de_fixpoint ee) ) 
 | DStep_unmergel : forall (ee1 ee2:dexp),
     lc_dexp ee2 ->
     lc_dexp ee1 ->
     DunfieldStep (de_merge ee1 ee2) ee1
 | DStep_unmerger : forall (ee1 ee2:dexp),
     lc_dexp ee1 ->
     lc_dexp ee2 ->
     DunfieldStep (de_merge ee1 ee2) ee2
 | DStep_mergel : forall (ee1 ee2 ee1':dexp),
     lc_dexp ee2 ->
     DunfieldStep ee1 ee1' ->
     DunfieldStep (de_merge ee1 ee2) (de_merge ee1' ee2)
 | DStep_merger : forall (vv1 ee2 ee2':dexp),
     DValue vv1 ->
     DunfieldStep ee2 ee2' ->
     DunfieldStep (de_merge vv1 ee2) (de_merge vv1 ee2')
 | DStep_split : forall (ee:dexp),
     lc_dexp ee ->
     DunfieldStep ee (de_merge ee ee).

(* defns WellformedType *)
Inductive WF : ctx -> typ -> Prop :=    (* defn WF *)
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

(* defns ISubtyping *)
Inductive isub : typ -> typ -> Prop :=    (* defn isub *)
 | IS_z : 
     isub t_int t_int
 | IS_top : forall (A:typ),
     isub A t_top
 | IS_arr : forall (A1 A2 B1 B2:typ),
     isub B1 A1 ->
     isub A2 B2 ->
     isub (t_arrow A1 A2) (t_arrow B1 B2)
 | IS_andl1 : forall (A1 A2 A3:typ),
     isub A1 A3 ->
     isub (t_and A1 A2) A3
 | IS_andl2 : forall (A1 A2 A3:typ),
     isub A2 A3 ->
     isub (t_and A1 A2) A3
 | IS_andr : forall (A1 A2 A3:typ),
     isub A1 A2 ->
     isub A1 A3 ->
     isub A1 (t_and A2 A3).

(* defns ITyping *)
Inductive ITyping : ctx -> dexp -> typ -> exp -> Prop :=    (* defn ITyping *)
 | ITyp_top : forall (G:ctx),
      uniq  G  ->
     ITyping G de_top t_top e_top
 | ITyp_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     ITyping G (de_lit i5) t_int (e_lit i5)
 | ITyp_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     ITyping G (de_var_f x) A (e_var_f x)
 | ITyp_lam : forall (L:vars) (G:ctx) (ee:dexp) (A B:typ) (e:exp),
     WF G A ->
      ( forall x , x \notin  L  -> ITyping  (cons ( x , A )  G )   ( open_dexp_wrt_dexp ee (de_var_f x) )  B  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     ITyping G  ( (de_abs ee) )  (t_arrow A B) (e_abs e A B)
 | ITyp_app : forall (G:ctx) (ee1 ee2:dexp) (B:typ) (e1 e2:exp) (A:typ),
     ITyping G ee1 (t_arrow A B) e1 ->
     ITyping G ee2 A e2 ->
     ITyping G (de_app ee1 ee2) B (e_app e1 e2)
 | ITyp_merge : forall (G:ctx) (ee1 ee2:dexp) (A B:typ) (e1 e2:exp),
     ITyping G ee1 A e1 ->
     ITyping G ee2 B e2 ->
      disjointSpec A B  ->
     ITyping G (de_merge ee1 ee2) (t_and A B) (e_merge e1 e2)
 | ITyp_sub : forall (G:ctx) (ee:dexp) (B:typ) (e:exp) (A:typ),
     ITyping G ee A e ->
     isub A B ->
     ITyping G ee B (e_anno e B).


(** infrastructure *)
Hint Constructors topLike ord disjoint sub TypedReduce step consistent Etyping Vtyping DValue DunfieldStep WF isub ITyping lc_dexp lc_value lc_exp.


