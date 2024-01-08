(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector implemented with matrix
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. There are two types of vectors, column vector and row vector.

  reference :
  1. Vector Calculus - Michael Corral
  2. https://github.com/coq/coq/blob/master/test-suite/success/Nsatz.v
     Note: there are geometrys in coq, including point, parallel, collinear, etc.
n  3. (in Chinese) Higher Mathematics Study Manual - Xu Xiao Zhan, p173
     《高等数学学习手册》徐小湛，p173
 *)

Require Export Matrix.

Generalizable Variable T Teq Tadd Topp Tmul Tinv.

Open Scope nat_scope.
Open Scope T_scope.
Open Scope mat_scope.


(** ######################################################################### *)
(** * Row Vector Theory *)
Open Scope rvec_scope.

(* ======================================================================= *)
(** ** Vector type *)

(** A vector rvec(n) is a colum vector, equal to a matrix mat(n,1) *)
Definition rvec {T} (n : nat) := @mat T 1 n.

(** Convert between function and vector *)
Definition f2rv {T} {n} (f : nat -> T) : rvec n := f2m (fun i j => f j).
Definition rv2f {T} {n} (m : rvec n) : nat -> T := fun i => (m2f m) 0 i.


(* ======================================================================= *)
(** ** Vector automation *)

(** Convert vec to function *)
Ltac rvec2fun :=
  repeat match goal with
    | v : rvec ?n |- _ => destruct v as [v]; simpl in *
    end.

(** Linear vector arithmetic *)
Ltac rlva :=
  rvec2fun;
  lma.


(* ======================================================================= *)
(** ** Vector theory on general type *)
Section rvec_basic.
  Context `{Equiv_Teq : Equivalence T Teq} {T0 : T}.
  
  Infix "==" := Teq : T_scope.
  Infix "==" := (eqlistA Teq) : list_scope.
  Infix "==" := (meq (Teq:=Teq)) : mat_scope.
  Notation "m ! i ! j " := (mnth T0 m i j) : mat_scope.

  (** --------------------------------------------------- *)
  (** *** Get element of vector *)

  (** get element from raw data, unsafe *)
  Notation "v $ i " := (v $ 0 $ i) : rvec_scope.
  Notation "v .1" := (v $ 0) : rvec_scope.
  Notation "v .2" := (v $ 1) : rvec_scope.
  Notation "v .3" := (v $ 2) : rvec_scope.
  Notation "v .4" := (v $ 3) : rvec_scope.
  (** get element for 3D vector *)
  Notation "v .x" := (v $ 0) : rvec_scope.
  Notation "v .y" := (v $ 1) : rvec_scope.
  Notation "v .z" := (v $ 2) : rvec_scope.
  
  (** get element, safe *)
  Definition rvnth {n} (v : rvec n) i : T := v ! 0 ! i.
  Notation "v ! i " := (rvnth v i) : rvec_scope.

  Lemma rvnth_spec : forall {n : nat} (v : rvec n) i ,
      i < n -> (v ! i == v $ i)%T.
  Proof. intros. unfold rvnth. apply mnth_eq_mnth_raw; auto. Qed.

  (** veq, iff vnth *)
  Lemma veq_iff_rvnth : forall {n : nat} (v1 v2 : rvec n),
      v1 == v2 <-> (forall i, i < n -> (v1 ! i == v2 ! i)%T).
  Proof.
    unfold rvec, rvnth. intros; split; intros.
    - rewrite (meq_iff_mnth (T0:=T0)) in H. apply H; auto.
    - rewrite (meq_iff_mnth (T0:=T0)). intros.
      assert (i = 0) by lia. subst; auto.
  Qed.

  (** --------------------------------------------------- *)
  (** *** Get row-vector of a matrix *)
  Definition mrow {r c : nat} (m : @mat T r c) (ri : nat) : rvec c :=
    f2rv (fun i => m $ ri $ i).

  
  (** --------------------------------------------------- *)
  (** *** List like operations for vector *)
  
  (** a :: v  *)
  Definition rvcons {n} (a : T) (v : rvec n) : rvec (S n) :=
    f2rv (fun i => match i with 0 => a | S i' => v $ i' end).

  Lemma rvcons_spec : forall n a (v : rvec n) i,
      let v' := rvcons a v in
      (v' $ 0 == a)%T /\ (i < n -> (v $ i == v' $ (S i))%T).
  Proof. intros. unfold rvcons. split; intros; solve_mnth. Qed.

  (** Get a vector from a given vector by remove k-th element *)
  Definition rvremove {n : nat} (v : @rvec T (S n)) (k : nat) : rvec n :=
    f2rv (fun i => if i <? k then v $ i else v $ (S i)).

  
  (** --------------------------------------------------- *)
  (** *** Convert between list and vector *)
  Definition rv2l {n} (v : rvec n) : list T := map (fun i : nat => v $ i) (seq 0 n).
  Definition l2rv n (l : list T) : rvec n := f2rv (fun i => nth i l T0).

  (** list of vector to dlist *)
  Definition rvl2dl {n} (l : list (rvec n)) : dlist T := map rv2l l.

  Lemma rv2l_length : forall {n} (v : rvec n), length (rv2l v) = n.
  Proof. intros. unfold rv2l. rewrite map_length, seq_length; auto. Qed.

  Lemma rv2l_l2rv_id : forall {n} (l : list T),
      length l = n -> (rv2l (l2rv n l) == l)%list.
  Proof.
    intros. unfold l2rv,rv2l. simpl.
    apply nth_ext with (d1:=T0)(d2:=T0); intros; auto.
    - rewrite map_length, seq_length; auto.
    - rewrite map_length, seq_length in *. rewrite ?nth_map_seq; auto. f_equiv. lia.
  Qed.

  Lemma l2rv_rv2l_id : forall {n} (v : rvec n), l2rv n (rv2l v) == v.
  Proof. lma. unfold rv2l. rewrite nth_map_seq; auto. f_equiv. easy. Qed.

  
  (** --------------------------------------------------- *)
  (** *** Make concrete vector *)
  Definition mk_rvec2 (a1 a2 : T) : rvec 2 := l2rv 2 [a1;a2].
  Definition mk_rvec3 (a1 a2 a3 : T) : rvec 3 := l2rv 3 [a1;a2;a3].
  Definition mk_rvec4 (a1 a2 a3 a4 : T) : rvec 4 := l2rv 4 [a1;a2;a3;a4].

  
  (** --------------------------------------------------- *)
  (** *** Convert between tuples and vector *)
  Definition t2rv_2 (t : @T2 T) : rvec 2 := let '(a,b) := t in l2rv 2 [a;b].
  Definition t2rv_3 (t : @T3 T) : rvec 3 := let '(a,b,c) := t in l2rv 3 [a;b;c].
  Definition t2rv_4 (t : @T4 T) : rvec 4 := let '(a,b,c,d) := t in l2rv 4 [a;b;c;d].

  Definition rv2t_2 (v : rvec 2) : @T2 T := (v.1, v.2).
  Definition rv2t_3 (v : rvec 3) : @T3 T := (v.1, v.2, v.3).
  Definition rv2t_4 (v : rvec 4) : @T4 T := (v.1, v.2, v.3, v.4).

  (* Lemma rv2t_t2rv_id_2 : forall (t : T * T), rv2t_2 (t2rv_2 t) == t. *)
  (* Proof. intros. destruct t. simpl. unfold v2t_2. f_equal. Qed. *)

  Lemma t2rv_rv2t_id_2 : forall (v : rvec 2), t2rv_2 (rv2t_2 v) == v.
  Proof. lma. Qed.

  
  (** --------------------------------------------------- *)
  (** *** vector mapping *)
  Definition rvmap {n} (v : rvec n) (f : T -> T) : rvec n := mmap f v.
  Definition rvmap2 {n} (v1 v2 : rvec n) (f : T -> T -> T) : rvec n := mmap2 f v1 v2.

  (** --------------------------------------------------- *)
  (** *** vector folding *)
  (* Definition rvfold {U} {n} (v : @rvec T n) (f : T -> U) (b0 : U) : U := b0. *)

  (** *** Zero vector *)

  (** Make a zero vector *)
  Definition rvec0 {n} : rvec n := mat0 T0.

  (** A vector is a zero vector. *)
  Definition rvzero {n} (v : rvec n) : Prop := v == rvec0.

  (** A vector is a non-zero vector. *)
  Definition rvnonzero {n} (v : rvec n) : Prop := ~(rvzero v).
  
  (** vec0 is equal to mat0 with column 1 *)
  Lemma rvec0_eq_mat0 : forall n, (@rvec0 n) == mat0 T0.
  Proof. intros. easy. Qed.

End rvec_basic.

Arguments rvnth {T} T0 {n}.
Arguments l2rv {T}.
Arguments mk_rvec2 {T}.
Arguments mk_rvec3 {T}.
Arguments mk_rvec4 {T}.
Arguments t2rv_2 {T}.
Arguments t2rv_3 {T}.
Arguments t2rv_4 {T}.

Notation "v $ i " := (v $ 0 $ i) : rvec_scope.
Notation "v .1" := (v $ 0) : rvec_scope.
Notation "v .2" := (v $ 1) : rvec_scope.
Notation "v .3" := (v $ 2) : rvec_scope.
Notation "v .4" := (v $ 3) : rvec_scope.
(** get element for 3D vector *)
Notation "v .x" := (v $ 0) : rvec_scope.
Notation "v .y" := (v $ 1) : rvec_scope.
Notation "v .z" := (v $ 2) : rvec_scope.

Section test.
  Notation "v ! i " := (rvnth 0 v i) : rvec_scope.
  Let v1 : rvec 3 := l2rv 0 3 [1;2].
  Let m1 : mat 2 3 := l2m 0 [[10;11];[15;16]].
  (** These notations could be mixed use *)
  (* Compute v1.1. *)
  (* Compute v1$(v1$0). *)
  (* Compute v1!(v1!0). *)
  (* Compute v1$(v1!0). *)
  (* Compute v1!(v1.1). *)
  (* Compute m2l (mconsr v1 m1). *)
End test.


(* ======================================================================= *)
(** ** Vector theory on element of ring type *)
Section rvec_ring.
  Context `{AG : AGroup}.

  Infix "==" := Teq : T_scope.
  Infix "+" := Tadd : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Infix "-" := (fun a b => a + (-b)) : T_scope.

  Infix "==" := (eqlistA Teq) : list_scope.
  Notation meq := (meq (Teq:=Teq)).
  Infix "==" := (meq) : mat_scope.
  Notation rvec0 := (@rvec0 _ T0 _).
  
  (* Infix "+" := (ladd (Tadd:=Tadd)) : list_scope. *)

  (** *** Vector addition *)

  Definition rvadd {n} (v1 v2 : rvec n) : rvec n := madd (Tadd:=Tadd) v1 v2.
  Infix "+" := rvadd : rvec_scope.

  (** v1 + v2 = v2 + v1 *)
  Lemma rvadd_comm : forall {n} (v1 v2 : rvec n), (v1 + v2) == (v2 + v1).
  Proof. intros. apply madd_comm. Qed.

  (** (v1 + v2) + v3 = v1 + (v2 + v3) *)
  Lemma rvadd_assoc : forall {n} (v1 v2 v3 : rvec n), (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof. intros. apply madd_assoc. Qed.

  (** vec0 + v = v *)
  Lemma rvadd_0_l : forall {n} (v : rvec n), rvec0 + v == v.
  Proof. intros. apply madd_0_l. Qed.

  (** v + vec0 = v *)
  Lemma rvadd_0_r : forall {n} (v : rvec n), v + rvec0 == v.
  Proof. intros. apply madd_0_r. Qed.

  
  (** *** Vector opposition *)
  
  Definition rvopp {n} (v : rvec n) : rvec n := mopp (Topp:=Topp) v.
  Notation "- v" := (rvopp v) : rvec_scope.

  (** (- v) + v = vec0 *)
  Lemma rvadd_vopp_l : forall {n} (v : rvec n), (- v) + v == rvec0.
  Proof. intros. apply madd_mopp_l. Qed.

  (** v + (- v) = vec0 *)
  Lemma rvadd_vopp_r : forall {n} (v : rvec n), v + (- v) == rvec0.
  Proof. intros. apply madd_mopp_r. Qed.
  

  (** *** Vector subtraction *)

  Definition rvsub {n} (v1 v2 : rvec n) : rvec n := v1 + (- v2).
  Infix "-" := rvsub : rvec_scope.

  
  (** Let's have a ring *)
  Context `{R : Ring T Tadd T0 Topp Tmul T1 Teq}.
  Add Ring ring_inst : (make_ring_theory R).
  Infix "*" := Tmul : T_scope.
  

  (** *** Vector scalar multiplication *)

  Definition rvcmul {n} a (v : rvec n) : rvec n := mcmul (Tmul:=Tmul) a v.
  Infix "c*" := rvcmul : rvec_scope.

  (* (** vcmul is a proper morphism *) *)
  (* Global Instance rvcmul_mor : forall n, Proper (Teq ==> meq ==> meq) (rvcmul (n:=n)). *)
  (* Proof. intros. apply mcmul_mor. Qed. *)

  (** a c* (b c* v) = (a * b) c* v *)
  Lemma rvcmul_assoc : forall {n} a b (v : rvec n), a c* (b c* v) == (a * b) c* v.
  Proof. intros. apply mcmul_assoc. Qed.

  (** a c* (b c* v) = b c* (a c* v) *)
  Lemma rvcmul_perm : forall {n} a b (v : rvec n), a c* (b c* v) == b c* (a c* v).
  Proof. intros. apply mcmul_perm. Qed.

  (** (a + b) c* v = (a c* v) + (b c* v) *)
  Lemma rvcmul_add_distr : forall {n} a b (v : rvec n),
      (a + b)%T c* v == (a c* v) + (b c* v).
  Proof. intros. apply mcmul_add_distr. Qed.

  (** a c* (v1 + v2) = (a c* v1) + (a c* v2) *)
  Lemma rvcmul_vadd_distr : forall {n} a (v1 v2 : rvec n), 
      a c* (v1 + v2) == (a c* v1) + (a c* v2).
  Proof. intros. apply mcmul_madd_distr. Qed.

  (** 1 c* v = v *)
  Lemma rvcmul_1_l : forall {n} (v : rvec n), T1 c* v == v.
  Proof. intros. apply mcmul_1_l. Qed.

  (** 0 c* v = rvec0 *)
  Lemma rvcmul_0_l : forall {n} (v : rvec n), T0 c* v == rvec0.
  Proof. intros. apply mcmul_0_l. Qed.

  Definition rvmulc {n} (v : rvec n) a : rvec n := mmulc (Tmul:=Tmul) v a.
  Infix "*c" := rvmulc : rvec_scope.

  (** v *c a = a c* v *)
  Lemma rvmulc_eq_vcmul : forall {n} a (v : rvec n), (v *c a) == (a c* v).
  Proof. intros. apply mmulc_eq_mcmul. Qed.

  (** (v *c a) *c b = v *c (a * b) *)
  Lemma rvmulc_assoc : forall {n} (v : rvec n) (a b : T), (v *c a) *c b == v *c (a * b).
  Proof. intros. apply mmulc_assoc. Qed.

  (** (v *c a) *c b = (v *c b) c* a *)
  Lemma rvmulc_perm : forall {n} (v : rvec n) (a b : T), (v *c a) *c b == (v *c b) *c a.
  Proof. intros. apply mmulc_perm. Qed.

  
  (** *** Vector dot product *)

  (* (** version 1, by {fold_left,map,seq} *) *)
  (* Definition vdot_old {n : nat} (v1 v2 : rvec n) : T := *)
  (*   fold_left Tadd (map (fun i => v1$i * v2$i) (seq 0 n)) T0. *)

  (** dot production of two vectors. *)
  Definition rvdot {n : nat} (v1 v2 : rvec n) : T :=
    seqsum (fun i => v1$i * v2$i) n (Tadd:=Tadd) (T0:=T0).
  Notation "< a , b >" := (rvdot a b) : rvec_scope.
  
  #[export] Instance rvdot_mor {n} : Proper (meq ==> meq ==> Teq) (@rvdot n).
  Proof.
    simp_proper. intros. unfold rvdot. apply seqsum_eq. intros. f_equiv; auto.
  Qed.

  (** <v1,v2> = <v2,v1> *)
  Lemma rvdot_comm : forall {n} (v1 v2 : rvec n), (<v1,v2> == <v2,v1>)%T.
  Proof. intros. apply seqsum_eq. intros. ring. Qed.

  (** <v1 + v2,v3> = <v1,v3> + <v2,v3> *)
  Lemma rvdot_add_distr_l : forall {n} (v1 v2 v3 : rvec n),
      (<(v1 + v2)%RV,v3> == <v1,v3> + <v2,v3>)%T.
  Proof.
    intros n [v1] [v2] [v3]. unfold rvdot; simpl.
    revert v1 v2 v3. induction n; intros; simpl; auto. ring. rewrite IHn. ring.
  Qed.

  (** <v1, v2 + v3> = <v1,v2> + <v1,v3> *)
  Lemma rvdot_add_distr_r : forall {n} (v1 v2 v3 : rvec n),
      (<v1,(v2 + v3)%RV> == <v1,v2> + <v1,v3>)%T.
  Proof.
    intros n [v1] [v2] [v3]. unfold rvdot; simpl.
    revert v1 v2 v3. induction n; intros; simpl; auto. ring. rewrite IHn. ring.
  Qed.

  (** <a c* v1, v2> = a * <v1,v2> *)
  Lemma rvdot_cmul_l : forall {n} (v1 v2 : rvec n) (a : T),
      (<a c* v1,v2> == a * <v1,v2>)%T.
  Proof.
    intros n [v1] [v2] a. unfold rvdot; simpl.
    rewrite seqsum_cmul_l. apply seqsum_eq; intros; ring.
  Qed.
  
  (** <v1, a c* v2> == a * <v1,v2> *)
  Lemma rvdot_cmul_r : forall {n} (v1 v2 : rvec n) (a : T),
      (<v1, a c* v2> == a * <v1,v2>)%T.
  Proof.
    intros n [v1] [v2] a. unfold rvdot; simpl.
    rewrite seqsum_cmul_l. apply seqsum_eq; intros; ring.
  Qed.

  (** <0,v> = 0 *)
  Lemma rvdot_0_l : forall {n} (v : rvec n), (<rvec0,v> == T0)%T.
  Proof. intros. apply seqsum_eq0. intros. cbv. ring. Qed.

  (** <v,0> = 0 *)
  Lemma rvdot_0_r : forall {n} (v : rvec n), (<v,rvec0> == T0)%T.
  Proof. intros. rewrite rvdot_comm, rvdot_0_l. easy. Qed.
  
End rvec_ring.

Section test.
  Import ZArith.
  Open Scope Z_scope.
  Open Scope rvec_scope.
  
  Infix "+" := (@rvadd _ Z.add _) : rvec_scope.
  Notation "- v" := (@rvopp _ Z.opp _ v) : rvec_scope.
  Infix "-" := (@rvsub _ Z.add Z.opp _) : rvec_scope.
  Infix "c*" := (@rvcmul _ Z.mul _) : rvec_scope.
  Notation "< a , b >" := (@rvdot _ Z.add 0 Z.mul _ a b) : rvec_scope.

  Let v1 := l2rv 0 3 [1;2;3].
  Let v2 := l2rv 0 3 [4;5;6].
  (* Compute rv2l (-v1). *)
  (* Compute rv2l (v1 + v2). *)
  (* Compute rv2l (v2 - v1). *)
  (* Compute rv2l (3 c* v1). *)
  (* Compute <v1,v2>. *)

End test.


(* ======================================================================= *)
(** ** Vector theory on element of field type *)

Section rvec_field.

  Context `{F : Field}.
  Infix "*" := (fun x y => Tmul x y) : T_scope.
  Infix "/" := (fun x y => Tmul x (Tinv y)) : T_scope.
  Infix "c*" := (rvcmul (Tmul:=Tmul)) : rvec_scope.

  (* Lemma vec_eq_vcmul_imply_coef_neq0 : forall {n} (v1 v2 : vec n) k, *)
  (*   vnonzero v1 -> vnonzero v2 -> v1 = k c* v2 -> k <> T0. *)
  (* Proof. *)
  (*   intros. intro. subst. rewrite vcmul_0_l in H. destruct H. easy. *)
  (* Qed. *)
  
  (** ** 2-dim vector operations *)
  (* Definition vlen2 (v : vec 2) : T := *)
  (*   let '(x,y) := v2t_2 v in *)
  (*     (x * x + y * y)%T. *)
  
  (* (** ** 3-dim vector operations *) *)
  (* Definition vlen3 (v : vec 3) : T := *)
  (*   let '(x,y,z) := v2t_3 v in *)
  (*     (x * x + y * y + z * z)%T. *)
  
  (* Definition vdot3 (v0 v1 : vec 3) : T := *)
  (*   let '(a0,b0,c0) := v2t_3 v0 in *)
  (*   let '(a1,b1,c1) := v2t_3 v1 in *)
  (*     (a0 * a1 + b0 * b1 + c0 * c1)%T. *)

End rvec_field.


(** ######################################################################### *)
(** * Column Vector Theory *)
Open Scope cvec_scope.

(* ======================================================================= *)
(** ** Vector type *)

(** A vector cvec(n) is a colum vector, equal to a matrix mat(n,1) *)
Definition cvec {T} (n : nat) := @mat T n 1.

(** Convert between function and vector *)
Definition f2cv {T} {n} (f : nat -> T) : cvec n := f2m (fun i j => f i).
Definition cv2f {T} {n} (m : cvec n) : nat -> T := fun i => (m2f m) i 0.


(* ======================================================================= *)
(** ** Vector automation *)

(** Convert vec to function *)
Ltac cvec2fun :=
  repeat match goal with
    | v : cvec ?n |- _ => destruct v as [v]; simpl in *
    end.

(** Linear vector arithmetic *)
Ltac clva :=
  cvec2fun;
  lma.

(* ======================================================================= *)
(** ** Vector theory on general type *)
Section cvec_basic.
  Context `{Equiv_Teq : Equivalence T Teq} {T0 : T}.
  
  Infix "==" := Teq : T_scope.
  Infix "==" := (eqlistA Teq) : list_scope.
  Infix "==" := (meq (Teq:=Teq)) : mat_scope.
  Notation "m ! i ! j " := (mnth T0 m i j) : mat_scope.

  (** --------------------------------------------------- *)
  (** *** Get element of vector *)

  (** get element from raw data, unsafe *)
  Notation "v $ i " := (v $ i $ 0) : cvec_scope.
  Notation "v .1" := (v $ 0) : cvec_scope.
  Notation "v .2" := (v $ 1) : cvec_scope.
  Notation "v .3" := (v $ 2) : cvec_scope.
  Notation "v .4" := (v $ 3) : cvec_scope.
  (** get element for 3D vector *)
  Notation "v .x" := (v $ 0) : cvec_scope.
  Notation "v .y" := (v $ 1) : cvec_scope.
  Notation "v .z" := (v $ 2) : cvec_scope.
  
  (** get element, safe *)
  Definition cvnth {n} (v : cvec n) i : T := v ! i ! 0.
  Notation "v ! i " := (cvnth v i) : cvec_scope.

  Lemma cvnth_spec : forall {n : nat} (v : cvec n) i ,
      i < n -> (v ! i == v $ i)%T.
  Proof. intros. unfold cvnth. apply mnth_eq_mnth_raw; auto. Qed.

  (** veq, iff vnth *)
  Lemma veq_iff_cvnth : forall {n : nat} (v1 v2 : cvec n),
      v1 == v2 <-> (forall i, i < n -> (v1 ! i == v2 ! i)%T).
  Proof.
    unfold cvec, cvnth. intros; split; intros.
    - rewrite (meq_iff_mnth (T0:=T0)) in H. apply H; auto.
    - rewrite (meq_iff_mnth (T0:=T0)). intros.
      assert (j = 0) by lia. subst; auto.
  Qed.

  (** veq, iff {top n-1 elements equal, and the n-th elements equal} *)
  
  
  (** --------------------------------------------------- *)
  (** *** Get column-vector of a matrix *)
  Definition mcol {r c : nat} (m : @mat T r c) (ci : nat) : cvec r :=
    f2cv (fun i => m $ i $ ci).

  
  (** --------------------------------------------------- *)
  (** *** List like operations for vector *)
  
  (** a :: v  *)
  Definition cvcons {n} (a : T) (v : cvec n) : cvec (S n) :=
    f2cv (fun i => match i with 0 => a | S i' => v $ i' end).

  Lemma cvcons_spec : forall n a (v : cvec n) i,
      let v' := cvcons a v in
      (v' $ 0 == a)%T /\ (i < n -> (v $ i == v' $ (S i))%T).
  Proof. intros. unfold cvcons. split; intros; solve_mnth. Qed.

  (** Get a vector from a given vector by remove k-th element *)
  Definition cvremove {n : nat} (v : @cvec T (S n)) (k : nat) : cvec n :=
    f2cv (fun i => if i <? k then v $ i else v $ (S i)).

  (** cons v.0 v.remove(0) = v *)
  Lemma cvcons_remove : forall {n} (v : @cvec T (S n)),
      cvcons (v$0) (cvremove v 0) == v.
  Proof. lma. Qed.
  
  (** --------------------------------------------------- *)
  (** *** Convert between list and vector *)
  Definition cv2l {n} (v : cvec n) : list T := map (fun i : nat => v $ i) (seq 0 n).
  Definition l2cv n (l : list T) : cvec n := f2cv (fun i => nth i l T0).

  (** list of vector to dlist *)
  Definition cvl2dl {n} (l : list (cvec n)) : dlist T := map cv2l l.

  Lemma cv2l_length : forall {n} (v : cvec n), length (cv2l v) = n.
  Proof. intros. unfold cv2l. rewrite map_length, seq_length; auto. Qed.

  Lemma cv2l_l2cv_id : forall {n} (l : list T),
      length l = n -> (cv2l (l2cv n l) == l)%list.
  Proof.
    intros. unfold l2cv,cv2l. simpl.
    apply nth_ext with (d1:=T0)(d2:=T0); intros; auto.
    - rewrite map_length, seq_length; auto.
    - rewrite map_length, seq_length in *. rewrite ?nth_map_seq; auto. f_equiv. lia.
  Qed.

  Lemma l2cv_cv2l_id : forall {n} (v : cvec n), l2cv n (cv2l v) == v.
  Proof. lma. unfold cv2l. rewrite nth_map_seq; auto. f_equiv. easy. Qed.

  
  (** --------------------------------------------------- *)
  (** *** Make concrete vector *)
  Definition mk_cvec2 (a1 a2 : T) : cvec 2 := l2cv 2 [a1;a2].
  Definition mk_cvec3 (a1 a2 a3 : T) : cvec 3 := l2cv 3 [a1;a2;a3].
  Definition mk_cvec4 (a1 a2 a3 a4 : T) : cvec 4 := l2cv 4 [a1;a2;a3;a4].

  
  (** --------------------------------------------------- *)
  (** *** Convert between tuples and vector *)
  Definition t2cv_2 (t : @T2 T) : cvec 2 := let '(a,b) := t in l2cv 2 [a;b].
  Definition t2cv_3 (t : @T3 T) : cvec 3 := let '(a,b,c) := t in l2cv 3 [a;b;c].
  Definition t2cv_4 (t : @T4 T) : cvec 4 := let '(a,b,c,d) := t in l2cv 4 [a;b;c;d].

  Definition cv2t_2 (v : cvec 2) : @T2 T := (v.1, v.2).
  Definition cv2t_3 (v : cvec 3) : @T3 T := (v.1, v.2, v.3).
  Definition cv2t_4 (v : cvec 4) : @T4 T := (v.1, v.2, v.3, v.4).

  (* Lemma cv2t_t2cv_id_2 : forall (t : T * T), cv2t_2 (t2cv_2 t) == t. *)
  (* Proof. intros. destruct t. simpl. unfold v2t_2. f_equal. Qed. *)

  Lemma t2cv_cv2t_id_2 : forall (v : cvec 2), t2cv_2 (cv2t_2 v) == v.
  Proof. lma. Qed.

  
  (** --------------------------------------------------- *)
  (** *** vector mapping *)
  Definition cvmap {n} (v : cvec n) (f : T -> T) : cvec n := mmap f v.
  Definition cvmap2 {n} (v1 v2 : cvec n) (f : T -> T -> T) : cvec n := mmap2 f v1 v2.


  (** --------------------------------------------------- *)
  (** *** vector folding *)
  Definition cvfold {n} {B:Type} (v : @cvec T n) (f : B -> T -> B) (b0 : B) : B :=
    seqfold (fun i => v$i) n f b0.

  (** *** Zero vector *)

  (** Make a zero vector *)
  Definition cvec0 {n} : cvec n := mat0 T0.

  (** A vector is a zero vector. *)
  Definition cvzero {n} (v : cvec n) : Prop := v == cvec0.

  (** A vector is a non-zero vector. *)
  Definition cvnonzero {n} (v : cvec n) : Prop := ~(cvzero v).
  
  (** vec0 is equal to mat0 with column 1 *)
  Lemma cvec0_eq_mat0 : forall n, (@cvec0 n) == mat0 T0.
  Proof. intros. easy. Qed.

  (** Any zero vector is vec0 *)
  Lemma cvzero_imply_vec0 : forall {n} (v : cvec n), cvzero v -> v == cvec0.
  Proof. intros. auto. Qed.
  

End cvec_basic.

Arguments cvnth {T} T0 {n}.
Arguments l2cv {T}.
Arguments mk_cvec2 {T}.
Arguments mk_cvec3 {T}.
Arguments mk_cvec4 {T}.
Arguments t2cv_2 {T}.
Arguments t2cv_3 {T}.
Arguments t2cv_4 {T}.

Notation "v $ i " := (v $ i $ 0) : cvec_scope.
Notation "v .1" := (v $ 0) : cvec_scope.
Notation "v .2" := (v $ 1) : cvec_scope.
Notation "v .3" := (v $ 2) : cvec_scope.
Notation "v .4" := (v $ 3) : cvec_scope.
(** get element for 3D vector *)
Notation "v .x" := (v $ 0) : cvec_scope.
Notation "v .y" := (v $ 1) : cvec_scope.
Notation "v .z" := (v $ 2) : cvec_scope.

Section test.
  Notation "v ! i " := (cvnth 0 v i) : cvec_scope.
  Let v1 : cvec 3 := l2cv 0 3 [1;2].
  Let m1 : mat 3 3 := l2m 0 [[10;11];[15;16]].
  (* Compute v1.1. *)
  (* Compute v1!(v1.1). *)
  (* Compute m2l (mconsc v1 m1). *)
End test.


(* ======================================================================= *)
(** ** Vector theory on element of ring type *)
Section cvec_ring.
  Context `{AG : AGroup}.

  Infix "==" := Teq : T_scope.
  Infix "!=" := (fun a b => ~(a == b)) : T_scope.
  Infix "+" := Tadd : T_scope.
  Notation "- a" := (Topp a) : T_scope.
  Infix "-" := (fun a b => a + (-b)) : T_scope.

  Infix "==" := (eqlistA Teq) : list_scope.

  Notation meq := (meq (Teq:=Teq)).
  Infix "==" := (meq) : mat_scope.

  Notation cvec0 := (@cvec0 _ T0 _).
  Notation cvzero := (@cvzero _ Teq T0 _).
  Notation cvnonzero := (@cvnonzero _ Teq T0 _).

  Notation seqsum := (seqsum (Tadd:=Tadd)(T0:=T0)).
  
  (* Infix "+" := (ladd (Tadd:=Tadd)) : list_scope. *)

  (** *** Vector addition *)

  Definition cvadd {n} (v1 v2 : cvec n) : cvec n := madd (Tadd:=Tadd) v1 v2.
  Infix "+" := cvadd : cvec_scope.

  (** v1 + v2 = v2 + v1 *)
  Lemma cvadd_comm : forall {n} (v1 v2 : cvec n), (v1 + v2) == (v2 + v1).
  Proof. intros. apply madd_comm. Qed.

  (** (v1 + v2) + v3 = v1 + (v2 + v3) *)
  Lemma cvadd_assoc : forall {n} (v1 v2 v3 : cvec n), (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof. intros. apply madd_assoc. Qed.

  (** (v1 + v2) + v3 = (v1 + v3) + v2 *)
  Lemma cvadd_perm : forall {n} (v1 v2 v3 : cvec n), (v1 + v2) + v3 == (v1 + v3) + v2.
  Proof. intros. apply madd_perm. Qed.

  (** vec0 + v = v *)
  Lemma cvadd_0_l : forall {n} (v : cvec n), cvec0 + v == v.
  Proof. intros. apply madd_0_l. Qed.

  (** v + vec0 = v *)
  Lemma cvadd_0_r : forall {n} (v : cvec n), v + cvec0 == v.
  Proof. intros. apply madd_0_r. Qed.

  
  (** *** Vector opposition *)
  
  Definition cvopp {n} (v : cvec n) : cvec n := mopp (Topp:=Topp) v.
  Notation "- v" := (cvopp v) : cvec_scope.

  (** (- v) + v = vec0 *)
  Lemma cvadd_vopp_l : forall {n} (v : cvec n), (- v) + v == cvec0.
  Proof. intros. apply madd_mopp_l. Qed.

  (** v + (- v) = vec0 *)
  Lemma cvadd_vopp_r : forall {n} (v : cvec n), v + (- v) == cvec0.
  Proof. intros. apply madd_mopp_r. Qed.

  (** - (v1 + v2) = (- v1) + (- v2) *)
  Lemma cvopp_vadd : forall {n} (v1 v2 : cvec n), - (v1 + v2) == (- v1) + (- v2).
  Proof. intros. apply mopp_madd. Qed.

  (** - (- v) = v *)
  Lemma cvopp_vopp : forall {n} (v : cvec n), - (- v) == v.
  Proof. intros. apply mopp_mopp. Qed.


  (** *** Vector subtraction *)

  Definition cvsub {n} (v1 v2 : cvec n) : cvec n := v1 + (- v2).
  Infix "-" := cvsub : cvec_scope.

  (** Rewrite vsub: v1 - v2 = v1 + (-v2) *)
  Lemma cvsub_rw : forall {n} (v1 v2 : cvec n), v1 - v2 == v1 + (-v2).
  Proof. intros. apply msub_rw. Qed.

  (** v1 - v2 = -(v2 - v1) *)
  Lemma cvsub_comm : forall {n} (v1 v2 : cvec n), v1 - v2 == - (v2 - v1).
  Proof. intros. apply msub_comm. Qed.

  (** (v1 - v2) - v3 = v1 - (v2 + v3) *)
  Lemma cvsub_assoc : forall {n} (v1 v2 v3 : cvec n), (v1 - v2) - v3 == v1 - (v2 + v3).
  Proof. intros. apply msub_assoc. Qed.

  (** (v1 + v2) - v3 = v1 + (v2 - v3) *)
  Lemma cvsub_assoc1 : forall {n} (v1 v2 v3 : cvec n), (v1 + v2) - v3 == v1 + (v2 - v3).
  Proof. intros. apply msub_assoc1. Qed.

  (** (v1 - v2) - v3 = v1 - (v3 - v2) *)
  Lemma cvsub_assoc2 : forall {n} (v1 v2 v3 : cvec n), (v1 - v2) - v3 == (v1 - v3) - v2.
  Proof. intros. apply msub_assoc2. Qed.

  (** vec0 - v = - v *)
  Lemma cvsub_0_l : forall {n} (v : cvec n), cvec0 - v == - v.
  Proof. intros. apply msub_0_l. Qed.

  (** v - vec0 = v *)
  Lemma cvsub_0_r : forall {n} (v : cvec n), v - cvec0 == v.
  Proof. intros. apply msub_0_r. Qed.

  (** v - v = vec0 *)
  Lemma cvsub_self : forall {n} (v : cvec n), v - v == cvec0.
  Proof. intros. apply msub_self. Qed.

  (* Section test. *)
  (*   Goal forall n (v1 v2 : cvec n), cvec0 + v1 + (-v2) + v2 == v1. *)
  (*     intros. *)
  (*     rewrite identityLeft. *)
  (*     (* rewrite associative. *) *)
  (*     (* rewrite inverseLeft. *) *)
  (*     group_simp. *)
  (*   Qed. *)
  (* End test. *)

  (* (** *** Group structure over {vadd,vec0,vopp,meq} *) *)
  (* Global Instance Group_VecAdd : forall n, Group (@cvadd n) (cvec0) cvopp meq. *)
  (* intros. apply Group_MatTadd. Qed. *)

  
  (** Let's have a ring *)
  Context `{R : Ring T Tadd T0 Topp Tmul T1 Teq}.
  Add Ring ring_inst : (make_ring_theory R).
  Infix "*" := Tmul : T_scope.
  
  Infix "*" := (@mmul _ Tadd T0 Tmul _ _ _) : mat_scope.
  Infix "c*" := (mcmul (Tmul:=Tmul)) : mat_scope.
  Infix "*c" := (mmulc (Tmul:=Tmul)) : mat_scope.

  (** *** Vector scalar multiplication *)

  Definition cvcmul {n} a (v : cvec n) : cvec n := mcmul (Tmul:=Tmul) a v.
  Infix "c*" := cvcmul : cvec_scope.

  (* (** vcmul is a proper morphism *) *)
  (* Global Instance cvcmul_mor : forall n, Proper (Teq ==> meq ==> meq) (cvcmul (n:=n)). *)
  (* Proof. intros. apply mcmul_mor. Qed. *)

  (** (a * v)[i] = a * [i] *)
  Lemma cvcmul_nth : forall {n} (v : cvec n) (a : T) i,
      i < n -> (a c* v)$i = (a * (v$i))%T.
  Proof. intros. auto. Qed.

  (** a c* (b c* v) = (a * b) c* v *)
  Lemma cvcmul_assoc : forall {n} a b (v : cvec n), a c* (b c* v) == (a * b)%T c* v.
  Proof. intros. apply mcmul_assoc. Qed.

  (** a c* (b c* v) = b c* (a c* v) *)
  Lemma cvcmul_perm : forall {n} a b (v : cvec n), a c* (b c* v) == b c* (a c* v).
  Proof. intros. apply mcmul_perm. Qed.

  (** (a + b) c* v = (a c* v) + (b c* v) *)
  Lemma cvcmul_add_distr : forall {n} a b (v : cvec n),
      (a + b)%T c* v == (a c* v) + (b c* v).
  Proof. intros. apply mcmul_add_distr. Qed.

  (** a c* (v1 + v2) = (a c* v1) + (a c* v2) *)
  Lemma cvcmul_vadd_distr : forall {n} a (v1 v2 : cvec n), 
      a c* (v1 + v2) == (a c* v1) + (a c* v2).
  Proof. intros. apply mcmul_madd_distr. Qed.

  (** 1 c* v = v *)
  Lemma cvcmul_1_l : forall {n} (v : cvec n), T1 c* v == v.
  Proof. intros. apply mcmul_1_l. Qed.

  (** 0 c* v = cvec0 *)
  Lemma cvcmul_0_l : forall {n} (v : cvec n), T0 c* v == cvec0.
  Proof. intros. apply mcmul_0_l. Qed.

  (** a c* 0 = cvec0 *)
  Lemma cvcmul_0_r : forall {n:nat} a, a c* cvec0 == (@Vector.cvec0 _ T0 n).
  Proof. intros. apply mcmul_0_r. Qed.

  (** - (a c* v) = (-a) c* v *)
  Lemma cvopp_cmul : forall {n} a (v : cvec n), - (a c* v) == (-a)%T c* v.
  Proof. lma. Qed.

  (** a c* (v1 - v2) = (a c* v1) - (a c* v2) *)
  Lemma cvcmul_sub : forall {n} a (v1 v2 : cvec n),
      a c* (v1 - v2) == (a c* v1) - (a c* v2).
  Proof. lma. Qed.

  (** a c* (m * v) = (a c* m) * v *)
  Lemma cvcmul_mmul_assoc_l : forall {r c} (a : T) (m : mat r c) (v : cvec c), 
      a c* (m * v) == (a c* m)%M * v.
  Proof. intros. apply mcmul_mmul_assoc_l. Qed.

  (** a c* (m * v) = m c* (a c* v) *)
  Lemma cvcmul_mmul_assoc_r : forall {r c} (a : T) (m : mat r c) (v : cvec c), 
      a c* (m * v) == m * (a c* v).
  Proof. intros. apply mcmul_mmul_assoc_r. Qed.
  
  (** If k times a non-zero vector equal to zero vector, then k must be not zero *)
  Lemma cvcmul_vnonzero_neq0_imply_neq0 : forall {n} (v : cvec n) k,
      cvnonzero v -> ~(k c* v == cvec0) -> (k != T0)%T.
  Proof.
    intros. intro. rewrite H1 in H0. rewrite cvcmul_0_l in H0. destruct H0. easy.
  Qed.

  (** Two non-zero vectors has k-times relation, then k is not zero *)
  Lemma cvec_eq_vcmul_imply_coef_neq0 : forall {n} (v1 v2 : cvec n) k,
      cvnonzero v1 -> cvnonzero v2 -> v1 == k c* v2 -> (k != T0)%T.
  Proof. intros. intro. rewrite H2 in H1. rewrite cvcmul_0_l in H1. easy. Qed.
  
  Definition cvmulc {n} (v : cvec n) a : cvec n := mmulc (Tmul:=Tmul) v a.
  Infix "*c" := cvmulc : cvec_scope.

  (** v *c a = a c* v *)
  Lemma cvmulc_eq_vcmul : forall {n} a (v : cvec n), (v *c a) == (a c* v).
  Proof. intros. apply mmulc_eq_mcmul. Qed.

  (** (v *c a) *c b = v *c (a * b) *)
  Lemma cvmulc_assoc : forall {n} (v : cvec n) (a b : T), (v *c a) *c b == v *c (a * b)%T.
  Proof. intros. apply mmulc_assoc. Qed.

  (** (v *c a) *c b = (v *c b) c* a *)
  Lemma cvmulc_perm : forall {n} (v : cvec n) (a b : T), (v *c a) *c b == (v *c b) *c a.
  Proof. intros. apply mmulc_perm. Qed.

  
  (** *** Vector dot product *)

  (* (** version 1, by {fold_left,map,seq} *) *)
  (* Definition vdot_old {n : nat} (v1 v2 : cvec n) : T := *)
  (*   fold_left Tadd (map (fun i => v1$i * v2$i) (seq 0 n)) T0. *)

  (** dot production of two vectors. *)
  Definition cvdot {n : nat} (v1 v2 : cvec n) : T :=
    seqsum (fun i => v1$i * v2$i)%T n.
  Notation "< a , b >" := (cvdot a b) : cvec_scope.

  #[export] Instance cvdot_mor {n} : Proper (meq ==> meq ==> Teq) (@cvdot n).
  Proof.
    simp_proper. intros. unfold cvdot. apply seqsum_eq. intros. f_equiv; auto.
  Qed.

  (** <row(m1,i)\T, col(m2,j)> = [m1 * m2].ij *)
  Lemma cvdot_row_col_eq_mnth : forall {r c s} (m1 : mat r c) (m2 : mat c s) i j,
      i < r -> j < s -> (<(mrow m1 i)\T, mcol m2 j> == (m1 * m2)%M $ i $ j)%T.
  Proof. intros. mat2fun. unfold mrow,mcol,cvdot. simpl. easy. Qed.

  (** <v1,v2> = v1\T * v2 *)
  Lemma cvdot_eq_mul_trans : forall {n} (v1 v2 : cvec n),
      (<v1,v2> == scalar_of_mat (v1\T * v2)%M)%T.
  Proof. intros. simpl. apply seqsum_eq. intros. easy. Qed.

  (** <v1,v2> = <v2,v1> *)
  Lemma cvdot_comm : forall {n} (v1 v2 : cvec n), (<v1,v2> == <v2,v1>)%T.
  Proof. intros. apply seqsum_eq. intros. ring. Qed.

  (** <v1 + v2, v3> = <v1,v3> + <v2,v3> *)
  Lemma cvdot_add_distr_l : forall {n} (v1 v2 v3 : cvec n),
      (<(v1 + v2)%CV,v3> == <v1,v3> + <v2,v3>)%T.
  Proof.
    intros n [v1] [v2] [v3]. unfold cvdot; simpl.
    revert v1 v2 v3. induction n; intros; simpl; auto. ring. rewrite IHn. ring.
  Qed.

  (** <v1, v2 + v3> = <v1,v2> + <v1,v3> *)
  Lemma cvdot_add_distr_r : forall {n} (v1 v2 v3 : cvec n),
      (<v1, (v2 + v3)%CV> == <v1,v2> + <v1,v3>)%T.
  Proof.
    intros n [v1] [v2] [v3]. unfold cvdot; simpl.
    revert v1 v2 v3. induction n; intros; simpl; auto. ring. rewrite IHn. ring.
  Qed.

  (** <a c* v1, v2> = a * <v1,v2> *)
  Lemma cvdot_vcmul_l : forall {n} (v1 v2 : cvec n) (a : T),
      (<a c* v1, v2> == a * <v1,v2>)%T.
  Proof.
    intros n [v1] [v2] a. unfold cvdot; simpl.
    rewrite seqsum_cmul_l. apply seqsum_eq; intros; ring.
  Qed.
  
  (** <v1, a c* v2> == a * <v1,v2> *)
  Lemma cvdot_vcmul_r : forall {n} (v1 v2 : cvec n) (a : T),
      (<v1, a c* v2> == a * <v1,v2>)%T.
  Proof.
    intros n [v1] [v2] a. unfold cvdot; simpl.
    rewrite seqsum_cmul_l. apply seqsum_eq; intros; ring.
  Qed.

  (** <0,v> = 0 *)
  Lemma cvdot_0_l : forall {n} (v : cvec n), (<cvec0,v> == T0)%T.
  Proof. intros. apply seqsum_eq0. intros. cbv. ring. Qed.

  (** <v,0> = 0 *)
  Lemma cvdot_0_r : forall {n} (v : cvec n), (<v,cvec0> == T0)%T.
  Proof. intros. rewrite cvdot_comm, cvdot_0_l. easy. Qed.

  (** < - v1, v2> = - <v1,v2> *)
  Lemma cvdot_vopp_l : forall {n} (v1 v2 : cvec n), (< (-v1)%CV, v2> == - <v1,v2>)%T.
  Proof.
    intros n [v1] [v2]. unfold cvdot; simpl.
    rewrite seqsum_opp. apply seqsum_eq; intros; ring.
  Qed.
  
  (** < v1, - v2> = - <v1,v2> *)
  Lemma cvdot_vopp_r : forall {n} (v1 v2 : cvec n), (< v1, (-v2)%CV> == - <v1,v2>)%T.
  Proof.
    intros n [v1] [v2]. unfold cvdot; simpl.
    rewrite seqsum_opp. apply seqsum_eq; intros; ring.
  Qed.
  
End cvec_ring.


Section test.
  Import ZArith.
  Open Scope Z_scope.
  Open Scope cvec_scope.
  
  Infix "+" := (@cvadd _ Z.add _) : cvec_scope.
  Notation "- v" := (@cvopp _ Z.opp _ v) : cvec_scope.
  Infix "-" := (@cvsub _ Z.add Z.opp _) : cvec_scope.
  Infix "c*" := (@cvcmul _ Z.mul _) : cvec_scope.
  Notation "< a , b >" := (@cvdot _ Z.add 0 Z.mul _ a b) : cvec_scope.

  Let v1 := l2cv 0 3 [1;2;3].
  Let v2 := l2cv 0 3 [4;5;6].
  (* Compute cv2l (-v1). *)
  (* Compute cv2l (v1 + v2). *)
  (* Compute cv2l (v2 - v1). *)
  (* Compute cv2l (3 c* v1). *)
  (* Compute <v1,v2>. *)

End test.


(* ======================================================================= *)
(** ** Vector theory on element of field type *)

Section cvec_field.

  Context `{F : Field}.
  Infix "*" := (fun x y => Tmul x y) : T_scope.
  Infix "/" := (fun x y => Tmul x (Tinv y)) : T_scope.
  Infix "c*" := (cvcmul (Tmul:=Tmul)) : cvec_scope.

  (* Lemma vec_eq_vcmul_imply_coef_neq0 : forall {n} (v1 v2 : vec n) k, *)
  (*   vnonzero v1 -> vnonzero v2 -> v1 = k c* v2 -> k <> T0. *)
  (* Proof. *)
  (*   intros. intro. subst. rewrite vcmul_0_l in H. destruct H. easy. *)
  (* Qed. *)
  
  (** ** 2-dim vector operations *)
  (* Definition vlen2 (v : vec 2) : T := *)
  (*   let '(x,y) := v2t_2 v in *)
  (*     (x * x + y * y)%T. *)
  
  (* (** ** 3-dim vector operations *) *)
  (* Definition vlen3 (v : vec 3) : T := *)
  (*   let '(x,y,z) := v2t_3 v in *)
  (*     (x * x + y * y + z * z)%T. *)
  
  (* Definition vdot3 (v0 v1 : vec 3) : T := *)
  (*   let '(a0,b0,c0) := v2t_3 v0 in *)
  (*   let '(a1,b1,c1) := v2t_3 v1 in *)
  (*     (a0 * a1 + b0 * b1 + c0 * c1)%T. *)

End cvec_field.


(** ######################################################################### *)
(** * Connection between rvec and cvec *)

(* ======================================================================= *)
(** ** Convertion between rvec and cvec *)
Section cvt.
  Context `{Equiv_Teq : Equivalence T Teq} {T0 : T}.
  
  Infix "==" := Teq : T_scope.
  Infix "==" := (meq (Teq:=Teq)) : mat_scope.

  Definition cv2rv {n} (v : cvec n) : rvec n :=
    f2rv (fun i => cvnth T0 v i).

  Lemma cv2rv_spec : forall {n} (v : cvec n), cv2rv v == v\T.
  Proof. lma. rewrite cvnth_spec; easy. Qed.

  Definition rv2cv {n} (v : rvec n) : cvec n :=
    f2cv (fun i => rvnth T0 v i).

  Lemma rv2cv_spec : forall {n} (v : rvec n), rv2cv v == v\T.
  Proof. lma. rewrite rvnth_spec; easy. Qed.

End cvt.


(* ======================================================================= *)
(** ** Equivalence between rvec and cvec *)
Section veq.
  
  (* Open Scope vec_scope. *)

  (* (* Here, we need only a set T equiped with an equivalence reation Teq *) *)
  (* Context `{Equiv_Teq : Equivalence T Teq} {T0 : T}. *)
  (* Infix "==" := Teq : T_scope. *)
  (* Notation cv2rv := (@cv2rv T T0 _). *)
  (* Notation rv2cv := (@rv2cv T T0 _). *)
  
  (* (** Equivalence between rvec and cvec: they are mathematical equivalent *) *)
  (* (** Note that, veq is not reflexive, not symmetric, and not transitive, *)
  (*     due to the type mismatch. *) *)
  (* Definition veq {n} (rv : rvec n) (cv : cvec n) : Prop := *)
  (*   forall i : nat, i < n -> rvnth T0 rv i == cvnth T0 cv i. *)
  
  (* Infix "==" := veq : vec_scope. *)

  (* (** cv2rv satisfy veq relation *) *)
  (* Lemma cv2rv_veq : forall {n} (v : cvec n), cv2rv v == v. *)
  (* Proof. *)
  (*   intros. hnf. intros. repeat unfold rvnth,cvnth,cv2rv,f2rv,f2m,mnth; simpl. *)
  (*   bdestruct (n >? i); bdestruct (1 >? 0); simpl; easy. *)
  (* Qed. *)

  (* (** rv2cv satisfy veq relation *) *)
  (* Lemma rv2cv_veq : forall {n} (v : rvec n), v == rv2cv v. *)
  (* Proof. *)
  (*   intros. hnf. intros. *)
  (*   unfold rvnth,cvnth,rv2cv,mnth,f2cv,f2m,rvnth,mnth. simpl. *)
  (*   bdestruct (n >? i); bdestruct (1 >? 0); simpl; try easy. lia. *)
  (* Qed. *)
  
End veq.


(* ======================================================================= *)
(** ** Equivalence of Left multiply a Rvec (LR) and Right multiply a Cvec (RC) *) 
Section LR_RC.
  (* (* we need a ring structure *) *)
  (* Context `{R : Ring T Tadd T0 Topp Tmul T1 Teq}. *)
  (* Add Ring ring_inst : (make_ring_theory R). *)
  (* Infix "==" := (@meq _ Teq _ _). *)
  (* Infix "*" := (@mmul _ Tadd T0 Tmul _ _ _). *)
  (* Notation cv2rv := (@cv2rv T T0 _). *)
  (* Notation rv2cv := (@rv2cv T T0 _). *)

  (* (** v * M == M\T * v' *) *)
  (* Lemma mvm_eq_mtmv : forall {r c : nat} (v : rvec r) (M : mat r c), *)
  (*     let v' : cvec r := v\T in *)
  (*     (* matrix right multiply a vector *) *)
  (*     let u1 : rvec c := v * M in *)
  (*     (* matrix left multiply a vector (the matrix need to be transposed) *) *)
  (*     let u2 : cvec c := M\T * v' in *)
  (*     (* Treat the column vector u2 as a row vector *) *)
  (*     let u2' : rvec c := u2\T in *)
  (*     (* The result must be same *) *)
  (*     u1 == u2'. *)
  (* Proof. lma. apply seqsum_eq. intros. ring. Qed. *)

  (* (** M * v = v * M\T *) *)
  (* Lemma mmv_eq_vmmt : forall {r c : nat} (M : mat r c) (v : cvec c), *)
  (*     (* Treat the column vector v as a row vector *) *)
  (*     let v' : rvec c := v\T in *)
  (*     (* matrix left multiply a vector *) *)
  (*     let u1 : cvec r := M * v in *)
  (*     (* matrix right multiply a vector (the matrix need to be transposed) *) *)
  (*     let u2 : rvec r := v' * M\T in *)
  (*     (* Treat the row vector u2 as a column vector *) *)
  (*     let u2' : cvec r := u2\T in *)
  (*     (* The result must be same *) *)
  (*     u1 == u2'. *)
  (* Proof. lma. apply seqsum_eq. intros. ring. Qed. *)

  (* Thus, we proved that, row vector and column vector are different but similar *)
End LR_RC.


Section test.
  Infix "==" := (meq (Teq:=eq)) : mat_scope.

  Let cv1 : cvec 3 := l2cv 0 3 [1;2;3].
  Let rv1 : rvec 3 := l2rv 0 3 [1;2;3].
  (* Compute cv1. *)
  (* Compute cv1. *)

  Goal cv2rv (T0:=0) cv1 == rv1.
    lma. Qed.
  Goal rv2cv (T0:=0) rv1 == cv1.
    lma. Qed.

End test.
