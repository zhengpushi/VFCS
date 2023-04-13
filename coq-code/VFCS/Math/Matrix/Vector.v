(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector implemented with matrix
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. A vector vec(n) is considered as a matrix mat(n,1)
 *)


Require Export Matrix.


Generalizable Variable A Aeq Aadd Aopp Amul Ainv.

(** Control the scope *)
Open Scope nat_scope.
Open Scope A_scope.
Open Scope mat_scope.
Open Scope vec_scope.

(* ======================================================================= *)
(** ** Vector type *)
Section def.
  Context `{Equiv_Aeq : Equivalence A Aeq}.

  (** A vector vec(n) is considered as a matrix mat(n,1) *)
  Definition vec {A : Type} (n : nat) := @mat A n 1.

  (** matrix equality *)
  Definition veq {n} (v1 v2 : vec n) := meq (Aeq:=Aeq) v1 v2.
  Infix "==" := veq : vec_scope.

  Definition mk_vec {A : Type} {n : nat} (f : nat -> A) : @vec A n :=
    @mk_mat A n 1 (fun i j => f i). (* Note, we won't limit "j" now. *)
  
End def.


(* ======================================================================= *)
(** ** Vector automation *)

(** Convert vec to function *)
Ltac vec_to_fun :=
  repeat match goal with
    | v:vec ?n |- _ => destruct v as [v]; simpl in *
    end.

(** Linear vector arithmetic *)
Ltac lva :=
  vec_to_fun;
  lma.

(* ======================================================================= *)
(** ** Vector theory on general type *)
Section vec_basic.
  Context `{Equiv_Aeq : Equivalence A Aeq} {A0:A}.
  
  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Infix "==" := (veq (Aeq:=Aeq)) : vec_scope.
  Notation "m ! i ! j " := (mnth A0 m i j) : mat_scope.

  (** --------------------------------------------------- *)
  (** *** Get element of vector *)

  (** get element from raw data, unsafe *)
  Notation "v $ i " := (v $ i $ 0) : vec_scope.
  
  (** get element, safe *)
  Definition vnth {n} (v : vec n) i : A := v!i!0.
  Notation "v ! i " := (vnth v i) : vec_scope.

  Lemma vnth_eq_vnth_raw : forall {n : nat} (v : vec n), (forall i, i < n -> (v!i == v$i)%A).
  Proof. intros. unfold vnth. apply mnth_eq_mnth_raw; auto. Qed.

  (** veq, iff vnth. Note: left side is unsafe, right side is safe *)
  Lemma veq_iff_vnth : forall {n : nat} (v1 v2 : vec n),
      v1 == v2 <-> (forall i, i < n -> (v1!i == v2!i)%A).
  Proof.
    unfold vec, vnth, veq. intros; split; intros.
    - rewrite (meq_iff_mnth (A0:=A0)) in H. apply H; auto.
    - rewrite (meq_iff_mnth (A0:=A0)). intros.
      assert (j = 0) by lia. subst; auto.
  Qed.
  
  (** --------------------------------------------------- *)
  (** *** List like operations for vector *)
  
  (** a :: v  *)
  Definition vcons {n} (a : A) (v : vec n) : vec (S n) :=
    mk_vec (fun i => match i with 0 => a | S i' => v $ i' end).

  Lemma vcons_spec : forall n a (v : vec n) i,
      let v' := vcons a v in
      (v' $ 0 == a)%A /\ (i < n -> (v $ i == v' $ (S i))%A).
  Proof. intros. unfold vcons. split; intros; solve_mnth. Qed.

  (** Get a vector from a given vector by remove k-th element *)
  Definition vremove {n : nat} (v : @vec A (S n)) (k : nat) : vec n :=
    mk_vec (fun i => if i <? k then v $ i else v $ (S i)).

  (** --------------------------------------------------- *)
  (** *** Convert between list and vector *)
  (* Definition v2l {n} (v : vec n) : list A := @Matrix.mcol _ n 1 0 v. *)
  (* Definition l2v {n} (l : list A) : vec n := l2m (A0:=A0) (row2col l). *)

  Definition v2l {n} (v : vec n) : list A := map (fun i : nat => v $ i) (seq 0 n).

  Definition l2v n (l : list A) : vec n :=
    (* mk_mat (fun i j => if (i <? n) && (j =? 0) then nth i l A0 else A0). *)
    mk_vec (fun i => nth i l A0).

  (** list of vector to dlist *)
  Definition vl2dl {n} (l : list (vec n)) : dlist A := map v2l l.

  Lemma v2l_length : forall {n} (v : vec n), length (v2l v) = n.
  Proof. intros. unfold v2l. rewrite map_length, seq_length; auto. Qed.

  Lemma v2l_l2v_id : forall {n} (l : list A), length l = n -> (v2l (l2v n l) == l)%list.
  Proof.
    intros. unfold l2v,v2l. simpl.
    apply nth_ext with (d1:=A0)(d2:=A0); intros; auto.
    - rewrite map_length, seq_length; auto.
    - rewrite map_length, seq_length in *. rewrite ?nth_map_seq; auto. f_equiv. lia.
  Qed.

  Lemma l2v_v2l_id : forall {n} (v : vec n), l2v n (v2l v) == v.
  Proof. lva. unfold v2l. rewrite nth_map_seq; auto. f_equiv. easy. Qed.

  (** --------------------------------------------------- *)
  (** *** Make concrete vector *)
  Definition mk_vec2 (a0 a1 : A) : vec 2 := l2v 2 [a0;a1].
  Definition mk_vec3 (a0 a1 a2 : A) : vec 3 := l2v 3 [a0;a1;a2].
  Definition mk_vec4 (a0 a1 a2 a3 : A) : vec 4 := l2v 4 [a0;a1;a2;a3].

  (** --------------------------------------------------- *)
  (** *** Convert between tuples and vector *)
  Definition t2v_2 (t : @T2 A) : vec 2 := let '(a,b) := t in l2v 2 [a;b].
  Definition t2v_3 (t : @T3 A) : vec 3 := let '(a,b,c) := t in l2v 3 [a;b;c].
  Definition t2v_4 (t : @T4 A) : vec 4 := let '(a,b,c,d) := t in l2v 4 [a;b;c;d].

  Definition v2t_2 (v : vec 2) : @T2 A := (v$0, v$1).
  Definition v2t_3 (v : vec 3) : @T3 A := (v$0, v$1, v$2).
  Definition v2t_4 (v : vec 4) : @T4 A := (v$0, v$1, v$2, v$3).

  (* Lemma v2t_t2v_id_2 : forall (t : A * A), v2t_2 (t2v_2 t) == t. *)
  (* Proof. intros. destruct t. simpl. unfold v2t_2. f_equal. Qed. *)

  Lemma t2v_v2t_id_2 : forall (v : vec 2), t2v_2 (v2t_2 v) == v.
  Proof. lva. Qed.

  (** --------------------------------------------------- *)
  (** *** vector mapping *)
  Definition vmap {n} (v : vec n) (f : A -> A) : vec n := mmap f v.
  Definition vmap2 {n} (v1 v2 : vec n) (f : A -> A -> A) : vec n := mmap2 f v1 v2.

  (** --------------------------------------------------- *)
  (** *** vector folding *)
  (* Definition vfold : forall {B : Type} {n} (v : vec n) (f : A -> B) (b : B), B. *)

End vec_basic.

Arguments vnth {A} A0 {n}.
Arguments l2v {A}.

Arguments mk_vec2 {A}.
Arguments mk_vec3 {A}.
Arguments mk_vec4 {A}.
Arguments t2v_2 {A}.
Arguments t2v_3 {A}.
Arguments t2v_4 {A}.

Notation "v $ i " := (v $ i $ 0) : vec_scope.

Section test.
  Notation "v ! i " := (vnth 0 v i) : vec_scope.
  Let v1 : vec 3 := l2v 0 3 [1;2].
  Let m1 : mat 3 3 := l2m 0 [[10;11];[15;16]].
  (* Compute v1!0. *)
  (* Compute v1!(v1!0). *)
  (* Compute m2l (mconsc v1 m1). *)
End test.


(* ======================================================================= *)
(** ** Vector theory on element of ring type *)
Section vec_ring.
  Context `{AG : AGroup}.

  Infix "==" := Aeq : A_scope.
  Infix "==" := (eqlistA Aeq) : list_scope.
  Notation veq := (veq (Aeq:=Aeq)).
  Infix "==" := (veq) : vec_scope.
  Infix "+" := Aadd : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "-" := (fun a b => a + (-b)) : A_scope.

  (* Infix "+" := (ladd (Aadd:=Aadd)) : list_scope. *)

  (** *** Zero vector *)

  (** Make a zero vector *)
  Definition vec0 {n} : vec n := mat0 A0.

  (** A vector is a zero vector. *)
  Definition vzero {n} (v : vec n) : Prop := v == vec0.

  (** A vector is a non-zero vector. *)
  Definition vnonzero {n} (v : vec n) : Prop := ~(vzero v).
  
  (** vec0 is equal to mat0 with column 1 *)
  Lemma vec0_eq_mat0 : forall n, (vec0 : vec n) == mat0 A0.
  Proof. intros. easy. Qed.
  
  
  (** *** Vector addition *)

  Definition vadd {n} (v1 v2 : vec n) : vec n := madd (Aadd:=Aadd) v1 v2.
  Infix "+" := vadd : vec_scope.

  (** v1 + v2 = v2 + v1 *)
  Lemma vadd_comm : forall {n} (v1 v2 : vec n), (v1 + v2) == (v2 + v1).
  Proof. intros. apply madd_comm. Qed.

  (** (v1 + v2) + v3 = v1 + (v2 + v3) *)
  Lemma vadd_assoc : forall {n} (v1 v2 v3 : vec n), (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof. intros. apply madd_assoc. Qed.

  (** vec0 + v = v *)
  Lemma vadd_0_l : forall {n} (v : vec n), vec0 + v == v.
  Proof. intros. apply madd_0_l. Qed.

  (** v + vec0 = v *)
  Lemma vadd_0_r : forall {n} (v : vec n), v + vec0 == v.
  Proof. intros. apply madd_0_r. Qed.

  
  (** *** Vector opposition *)
  
  Definition vopp {n} (v : vec n) : vec n := mopp (Aopp:=Aopp) v.
  Notation "- v" := (vopp v) : vec_scope.

  (** (- v) + v = vec0 *)
  Lemma vadd_opp_l : forall {n} (v : vec n), (- v) + v == vec0.
  Proof. intros. apply madd_opp_l. Qed.

  (** v + (- v) = vec0 *)
  Lemma vadd_opp_r : forall {n} (v : vec n), v + (- v) == vec0.
  Proof. intros. apply madd_opp_r. Qed.
  

  (** *** Vector subtraction *)

  Definition vsub {n} (v1 v2 : vec n) : vec n := v1 + (- v2).
  Infix "-" := vsub : vec_scope.

  
  (** Let's have a ring *)
  Context `{R : Ring A Aadd A0 Aopp Amul A1 Aeq}.
  Add Ring ring_inst : (make_ring_theory R).
  Infix "*" := Amul : A_scope.
  

  (** *** Vector scalar multiplication *)

  Definition vcmul {n} a (v : vec n) : vec n := mcmul (Amul:=Amul) a v.
  Infix "c*" := vcmul : vec_scope.

  (** vcmul is a proper morphism *)
  Global Instance vcmul_mor : forall n, Proper (Aeq ==> veq ==> veq) (vcmul (n:=n)).
  Proof. intros. unfold veq. apply mcmul_mor. Qed.

  (** a c* (b c* v) = (a * b) c* v *)
  Lemma vcmul_assoc : forall {n} a b (v : vec n), a c* (b c* v) == (a * b) c* v.
  Proof. intros. apply mcmul_assoc. Qed.

  (** a c* (b c* v) = b c* (a c* v) *)
  Lemma vcmul_perm : forall {n} a b (v : vec n), a c* (b c* v) == b c* (a c* v).
  Proof. intros. apply mcmul_perm. Qed.

  (** (a + b) c* v = (a c* v) + (b c* v) *)
  Lemma vcmul_add_distr_l : forall {n} a b (v : vec n),
      (a + b)%A c* v == (a c* v) + (b c* v).
  Proof. intros. apply mcmul_add_distr_r. Qed.

  (** a c* (v1 + v2) = (a c* v1) + (a c* v2) *)
  Lemma vcmul_add_distr_r : forall {n} a (v1 v2 : vec n), 
      a c* (v1 + v2) == (a c* v1) + (a c* v2).
  Proof. intros. apply mcmul_add_distr_l. Qed.

  (** 1 c* v = v *)
  Lemma vcmul_1_l : forall {n} (v : vec n), A1 c* v == v.
  Proof. intros. apply mcmul_1_l. Qed.

  (** 0 c* v = vec0 *)
  Lemma vcmul_0_l : forall {n} (v : vec n), A0 c* v == vec0.
  Proof. intros. apply mcmul_0_l. Qed.

  Definition vmulc {n} (v : vec n) a : vec n := mmulc (Amul:=Amul) v a.
  Infix "*c" := vmulc : vec_scope.

  (** v *c a = a c* v *)
  Lemma vmulc_eq_vcmul : forall {n} a (v : vec n), (v *c a) == (a c* v).
  Proof. intros. apply mmulc_eq_mcmul. Qed.

  
  (** *** Vector dot product *)

  (** version 1, by {fold_left,map,seq} *)
  Definition vdot_old {n : nat} (v1 v2 : vec n) : A :=
    fold_left Aadd (map (fun i => v1$i * v2$i) (seq 0 n)) A0.

  (** dot production of two vectors. *)
  Definition vdot {n : nat} (v1 v2 : vec n) : A :=
    seqsum (fun i => v1$i * v2$i) n (Aadd:=Aadd) (A0:=A0).
  
  Infix "⋅" := vdot : vec_scope.

  (** dot production is commutative *)
  Lemma vdot_comm : forall {n} (v1 v2 : vec n), (v1 ⋅ v2 == v2 ⋅ v1)%A.
  Proof. intros. apply seqsum_eq. intros. ring. Qed.

  Lemma vdot_add_distr_l : forall {n} (v1 v2 v3 : vec n),
      ((v1 + v2)%V ⋅ v3 == v1 ⋅ v3 + v2 ⋅ v3)%A.
  Proof.
    intros n [v1] [v2] [v3]. unfold vdot; simpl.
    revert v1 v2 v3. induction n; intros; simpl; auto. ring. rewrite IHn. ring.
  Qed.

  Lemma vdot_add_distr_r : forall {n} (v1 v2 v3 : vec n),
      (v1 ⋅ (v2 + v3)%V == v1 ⋅ v2 + v1 ⋅ v3)%A.
  Proof.
    intros n [v1] [v2] [v3]. unfold vdot; simpl.
    revert v1 v2 v3. induction n; intros; simpl; auto. ring. rewrite IHn. ring.
  Qed.

  Lemma vdot_cmul_l : forall {n} (v1 v2 : vec n) (a : A),
      ((a c* v1) ⋅ v2 == a * (v1 ⋅ v2))%A.
  Proof.
    intros n [v1] [v2] a. unfold vdot; simpl.
    rewrite seqsum_cmul_l. apply seqsum_eq; intros; ring.
  Qed.
  
  Lemma vdot_cmul_r : forall {n} (v1 v2 : vec n) (a : A),
      (v1 ⋅ (a c* v2) == a * (v1 ⋅ v2))%A.
  Proof.
    intros n [v1] [v2] a. unfold vdot; simpl.
    rewrite seqsum_cmul_l. apply seqsum_eq; intros; ring.
  Qed.

  (** 0 * v = 0 *)
  Lemma vdot_0_l : forall {n} (v : vec n), (vec0 ⋅ v == A0)%A.
  Proof. intros. apply seqsum_seq0. intros. cbv. ring. Qed.

  (** v * 0 = 0 *)
  Lemma vdot_0_r : forall {n} (v : vec n), (v ⋅ vec0 == A0)%A.
  Proof. intros. rewrite vdot_comm, vdot_0_l. easy. Qed.

End vec_ring.

Section test.
  Import ZArith.
  Open Scope Z_scope.
  Open Scope vec_scope.
  
  Infix "+" := (vadd (Aadd:=Z.add)) : vec_scope.
  Notation "- v" := (vopp (Aopp:=Z.opp) v) : vec_scope.
  Infix "-" := (vsub (Aadd:=Z.add)(Aopp:=Z.opp)) : vec_scope.
  Infix "c*" := (vcmul (Amul:=Z.mul)) : vec_scope.
  Infix "⋅" := (vdot (A0:=0) (Aadd:=Z.add) (Amul:=Z.mul)) : vec_scope.

  Let v1 := l2v 0 3 [1;2;3].
  Let v2 := l2v 0 3 [4;5;6].
  (* Compute v2l (-v1). *)
  (* Compute v2l (v1 + v2). *)
  (* Compute v2l (v2 - v1). *)
  (* Compute v2l (3 c* v1). *)
  (* Compute v1⋅v2. *)

End test.


(* ======================================================================= *)
(** ** Vector theory on element of field type *)

Section vec_field.

  Context `{F : Field}.
  Infix "*" := (fun x y => Amul x y) : A_scope.
  Infix "/" := (fun x y => Amul x (Ainv y)) : A_scope.
  Infix "c*" := (vcmul (Amul:=Amul)) : vec_scope.

  (* Lemma vec_eq_vcmul_imply_coef_neq0 : forall {n} (v1 v2 : vec n) k, *)
  (*   vnonzero v1 -> vnonzero v2 -> v1 = k c* v2 -> k <> A0. *)
  (* Proof. *)
  (*   intros. intro. subst. rewrite vcmul_0_l in H. destruct H. easy. *)
  (* Qed. *)
  
  (** ** 2-dim vector operations *)
  (* Definition vlen2 (v : vec 2) : A := *)
  (*   let '(x,y) := v2t_2 v in *)
  (*     (x * x + y * y)%A. *)
  
  (* (** ** 3-dim vector operations *) *)
  (* Definition vlen3 (v : vec 3) : A := *)
  (*   let '(x,y,z) := v2t_3 v in *)
  (*     (x * x + y * y + z * z)%A. *)
      
  (* Definition vdot3 (v0 v1 : vec 3) : A := *)
  (*   let '(a0,b0,c0) := v2t_3 v0 in *)
  (*   let '(a1,b1,c1) := v2t_3 v1 in *)
  (*     (a0 * a1 + b0 * b1 + c0 * c1)%A. *)

End vec_field.
