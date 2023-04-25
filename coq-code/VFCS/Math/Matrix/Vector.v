(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector implemented with matrix
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. There are two types of vectors, column vector and row vector.
 *)

Require Export Matrix.

Generalizable Variable A Aeq Aadd Aopp Amul Ainv.

Open Scope nat_scope.
Open Scope A_scope.
Open Scope mat_scope.


Module Export RowVector.
  Open Scope rvec_scope.

  (* ======================================================================= *)
  (** ** Vector type *)

  (** A vector rvec(n) is a colum vector, equal to a matrix mat(n,1) *)
  Definition rvec {A : Type} (n : nat) := @mat A 1 n.

  Definition mk_rvec {A : Type} {n : nat} (f : nat -> A) : @rvec A n :=
    @mk_mat A _ _ (fun i j => f j). (* Note, we won't limit "j" now. *)


  (* ======================================================================= *)
  (** ** Vector automation *)

  (** Convert vec to function *)
  Ltac rvec_to_fun :=
    repeat match goal with
      | v : rvec ?n |- _ => destruct v as [v]; simpl in *
      end.

  (** Linear vector arithmetic *)
  Ltac lva :=
    rvec_to_fun;
    lma.

  
  (* ======================================================================= *)
  (** ** Vector theory on general type *)
  Section basic.
    Context `{Equiv_Aeq : Equivalence A Aeq} {A0:A}.
    
    Infix "==" := Aeq : A_scope.
    Infix "==" := (eqlistA Aeq) : list_scope.
    Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
    Notation "m ! i ! j " := (mnth A0 m i j) : mat_scope.

    (** --------------------------------------------------- *)
    (** *** Get element of vector *)

    (** get element from raw data, unsafe *)
    Notation "v $ i " := (v $ 0 $ i) : rvec_scope.
    Notation "v .1" := (v $ 0) : rvec_scope.
    Notation "v .2" := (v $ 1) : rvec_scope.
    Notation "v .3" := (v $ 2) : rvec_scope.
    Notation "v .4" := (v $ 3) : rvec_scope.
    
    (** get element, safe *)
    Definition rvnth {n} (v : rvec n) i : A := v ! 0 ! i.
    Notation "v ! i " := (rvnth v i) : rvec_scope.

    Lemma rvnth_spec : forall {n : nat} (v : rvec n) i ,
        i < n -> (v ! i == v $ i)%A.
    Proof. intros. unfold rvnth. apply mnth_eq_mnth_raw; auto. Qed.

    (** veq, iff vnth *)
    Lemma veq_iff_rvnth : forall {n : nat} (v1 v2 : rvec n),
        v1 == v2 <-> (forall i, i < n -> (v1 ! i == v2 ! i)%A).
    Proof.
      unfold rvec, rvnth. intros; split; intros.
      - rewrite (meq_iff_mnth (A0:=A0)) in H. apply H; auto.
      - rewrite (meq_iff_mnth (A0:=A0)). intros.
        assert (i = 0) by lia. subst; auto.
    Qed.

    (** --------------------------------------------------- *)
    (** *** Get row-vector of a matrix *)
    Definition mrow {r c : nat} (m : @mat A r c) (ri : nat) : rvec c :=
      mk_rvec (fun i => m $ ri $ i).

    
    (** --------------------------------------------------- *)
    (** *** List like operations for vector *)
    
    (** a :: v  *)
    Definition rvcons {n} (a : A) (v : rvec n) : rvec (S n) :=
      mk_rvec (fun i => match i with 0 => a | S i' => v $ i' end).

    Lemma rvcons_spec : forall n a (v : rvec n) i,
        let v' := rvcons a v in
        (v' $ 0 == a)%A /\ (i < n -> (v $ i == v' $ (S i))%A).
    Proof. intros. unfold rvcons. split; intros; solve_mnth. Qed.

    (** Get a vector from a given vector by remove k-th element *)
    Definition rvremove {n : nat} (v : @rvec A (S n)) (k : nat) : rvec n :=
      mk_rvec (fun i => if i <? k then v $ i else v $ (S i)).

    
    (** --------------------------------------------------- *)
    (** *** Convert between list and vector *)
    Definition rv2l {n} (v : rvec n) : list A := map (fun i : nat => v $ i) (seq 0 n).
    Definition l2rv n (l : list A) : rvec n := mk_rvec (fun i => nth i l A0).

    (** list of vector to dlist *)
    Definition rvl2dl {n} (l : list (rvec n)) : dlist A := map rv2l l.

    Lemma rv2l_length : forall {n} (v : rvec n), length (rv2l v) = n.
    Proof. intros. unfold rv2l. rewrite map_length, seq_length; auto. Qed.

    Lemma rv2l_l2rv_id : forall {n} (l : list A),
        length l = n -> (rv2l (l2rv n l) == l)%list.
    Proof.
      intros. unfold l2rv,rv2l. simpl.
      apply nth_ext with (d1:=A0)(d2:=A0); intros; auto.
      - rewrite map_length, seq_length; auto.
      - rewrite map_length, seq_length in *. rewrite ?nth_map_seq; auto. f_equiv. lia.
    Qed.

    Lemma l2rv_rv2l_id : forall {n} (v : rvec n), l2rv n (rv2l v) == v.
    Proof. lva. unfold rv2l. rewrite nth_map_seq; auto. f_equiv. easy. Qed.

    
    (** --------------------------------------------------- *)
    (** *** Make concrete vector *)
    Definition mk_rvec2 (a0 a1 : A) : rvec 2 := l2rv 2 [a0;a1].
    Definition mk_rvec3 (a0 a1 a2 : A) : rvec 3 := l2rv 3 [a0;a1;a2].
    Definition mk_rvec4 (a0 a1 a2 a3 : A) : rvec 4 := l2rv 4 [a0;a1;a2;a3].

    
    (** --------------------------------------------------- *)
    (** *** Convert between tuples and vector *)
    Definition t2rv_2 (t : @T2 A) : rvec 2 := let '(a,b) := t in l2rv 2 [a;b].
    Definition t2rv_3 (t : @T3 A) : rvec 3 := let '(a,b,c) := t in l2rv 3 [a;b;c].
    Definition t2rv_4 (t : @T4 A) : rvec 4 := let '(a,b,c,d) := t in l2rv 4 [a;b;c;d].

    Definition rv2t_2 (v : rvec 2) : @T2 A := (v.1, v.2).
    Definition rv2t_3 (v : rvec 3) : @T3 A := (v.1, v.2, v.3).
    Definition rv2t_4 (v : rvec 4) : @T4 A := (v.1, v.2, v.3, v.4).

    (* Lemma rv2t_t2rv_id_2 : forall (t : A * A), rv2t_2 (t2rv_2 t) == t. *)
    (* Proof. intros. destruct t. simpl. unfold v2t_2. f_equal. Qed. *)

    Lemma t2rv_rv2t_id_2 : forall (v : rvec 2), t2rv_2 (rv2t_2 v) == v.
    Proof. lva. Qed.

    
    (** --------------------------------------------------- *)
    (** *** vector mapping *)
    Definition rvmap {n} (v : rvec n) (f : A -> A) : rvec n := mmap f v.
    Definition rvmap2 {n} (v1 v2 : rvec n) (f : A -> A -> A) : rvec n := mmap2 f v1 v2.

    (** --------------------------------------------------- *)
    (** *** vector folding *)
    (* Definition rvfold {B : Type} {n} (v : @rvec A n) (f : A -> B) (b0 : B) : B := b0. *)

  End basic.

  Arguments rvnth {A} A0 {n}.
  Arguments l2rv {A}.
  Arguments mk_rvec2 {A}.
  Arguments mk_rvec3 {A}.
  Arguments mk_rvec4 {A}.
  Arguments t2rv_2 {A}.
  Arguments t2rv_3 {A}.
  Arguments t2rv_4 {A}.

  Notation "v $ i " := (v $ 0 $ i) : rvec_scope.
  Notation "v .1" := (v $ 0) : rvec_scope.
  Notation "v .2" := (v $ 1) : rvec_scope.
  Notation "v .3" := (v $ 2) : rvec_scope.
  Notation "v .4" := (v $ 3) : rvec_scope.

  Section test.
    Notation "v ! i " := (rvnth 0 v i) : rvec_scope.
    Let v1 : rvec 3 := l2rv 0 3 [1;2].
    Let m1 : mat 2 3 := l2m 0 [[10;11];[15;16]].
    (* Compute v1!0. *)
    (* Compute v1!(v1!0). *)
    (* Compute m2l (mconsr v1 m1). *)
  End test.


  (* ======================================================================= *)
  (** ** Vector theory on element of ring type *)
  Section vec_ring.
    Context `{AG : AGroup}.

    Infix "==" := Aeq : A_scope.
    Infix "+" := Aadd : A_scope.
    Notation "- a" := (Aopp a) : A_scope.
    Infix "-" := (fun a b => a + (-b)) : A_scope.

    Infix "==" := (eqlistA Aeq) : list_scope.
    Notation meq := (meq (Aeq:=Aeq)).
    Infix "==" := (meq) : mat_scope.
    
    (* Infix "+" := (ladd (Aadd:=Aadd)) : list_scope. *)

    (** *** Zero vector *)

    (** Make a zero vector *)
    Definition rvec0 {n} : rvec n := mat0 A0.

    (** A vector is a zero vector. *)
    Definition rvzero {n} (v : rvec n) : Prop := v == rvec0.

    (** A vector is a non-zero vector. *)
    Definition rvnonzero {n} (v : rvec n) : Prop := ~(rvzero v).
    
    (** vec0 is equal to mat0 with column 1 *)
    Lemma rvec0_eq_mat0 : forall n, (@rvec0 n) == mat0 A0.
    Proof. intros. easy. Qed.

    (** *** Vector addition *)

    Definition rvadd {n} (v1 v2 : rvec n) : rvec n := madd (Aadd:=Aadd) v1 v2.
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
    
    Definition rvopp {n} (v : rvec n) : rvec n := mopp (Aopp:=Aopp) v.
    Notation "- v" := (rvopp v) : rvec_scope.

    (** (- v) + v = vec0 *)
    Lemma rvadd_opp_l : forall {n} (v : rvec n), (- v) + v == rvec0.
    Proof. intros. apply madd_opp_l. Qed.

    (** v + (- v) = vec0 *)
    Lemma rvadd_opp_r : forall {n} (v : rvec n), v + (- v) == rvec0.
    Proof. intros. apply madd_opp_r. Qed.
    

    (** *** Vector subtraction *)

    Definition rvsub {n} (v1 v2 : rvec n) : rvec n := v1 + (- v2).
    Infix "-" := rvsub : rvec_scope.

    
    (** Let's have a ring *)
    Context `{R : Ring A Aadd A0 Aopp Amul A1 Aeq}.
    Add Ring ring_inst : (make_ring_theory R).
    Infix "*" := Amul : A_scope.
    

    (** *** Vector scalar multiplication *)

    Definition rvcmul {n} a (v : rvec n) : rvec n := mcmul (Amul:=Amul) a v.
    Infix "c*" := rvcmul : rvec_scope.

    (* (** vcmul is a proper morphism *) *)
    (* Global Instance rvcmul_mor : forall n, Proper (Aeq ==> meq ==> meq) (rvcmul (n:=n)). *)
    (* Proof. intros. apply mcmul_mor. Qed. *)

    (** a c* (b c* v) = (a * b) c* v *)
    Lemma rvcmul_assoc : forall {n} a b (v : rvec n), a c* (b c* v) == (a * b) c* v.
    Proof. intros. apply mcmul_assoc. Qed.

    (** a c* (b c* v) = b c* (a c* v) *)
    Lemma rvcmul_perm : forall {n} a b (v : rvec n), a c* (b c* v) == b c* (a c* v).
    Proof. intros. apply mcmul_perm. Qed.

    (** (a + b) c* v = (a c* v) + (b c* v) *)
    Lemma rvcmul_add_distr_l : forall {n} a b (v : rvec n),
        (a + b)%A c* v == (a c* v) + (b c* v).
    Proof. intros. apply mcmul_add_distr_r. Qed.

    (** a c* (v1 + v2) = (a c* v1) + (a c* v2) *)
    Lemma rvcmul_add_distr_r : forall {n} a (v1 v2 : rvec n), 
        a c* (v1 + v2) == (a c* v1) + (a c* v2).
    Proof. intros. apply mcmul_add_distr_l. Qed.

    (** 1 c* v = v *)
    Lemma rvcmul_1_l : forall {n} (v : rvec n), A1 c* v == v.
    Proof. intros. apply mcmul_1_l. Qed.

    (** 0 c* v = rvec0 *)
    Lemma rvcmul_0_l : forall {n} (v : rvec n), A0 c* v == rvec0.
    Proof. intros. apply mcmul_0_l. Qed.

    Definition rvmulc {n} (v : rvec n) a : rvec n := mmulc (Amul:=Amul) v a.
    Infix "*c" := rvmulc : rvec_scope.

    (** v *c a = a c* v *)
    Lemma rvmulc_eq_cmul : forall {n} a (v : rvec n), (v *c a) == (a c* v).
    Proof. intros. apply mmulc_eq_cmul. Qed.

    
    (** *** Vector dot product *)

    (* (** version 1, by {fold_left,map,seq} *) *)
    (* Definition vdot_old {n : nat} (v1 v2 : rvec n) : A := *)
    (*   fold_left Aadd (map (fun i => v1$i * v2$i) (seq 0 n)) A0. *)

    (** dot production of two vectors. *)
    Definition rvdot {n : nat} (v1 v2 : rvec n) : A :=
      seqsum (fun i => v1$i * v2$i) n (Aadd:=Aadd) (A0:=A0).
    
    Notation "< a , b >" := (rvdot a b) : rvec_scope.

    (** <v1,v2> = <v2,v1> *)
    Lemma rvdot_comm : forall {n} (v1 v2 : rvec n), (<v1,v2> == <v2,v1>)%A.
    Proof. intros. apply seqsum_eq. intros. ring. Qed.

    (** <v1 + v2,v3> = <v1,v3> + <v2,v3> *)
    Lemma rvdot_add_distr_l : forall {n} (v1 v2 v3 : rvec n),
        (<(v1 + v2)%RV,v3> == <v1,v3> + <v2,v3>)%A.
    Proof.
      intros n [v1] [v2] [v3]. unfold rvdot; simpl.
      revert v1 v2 v3. induction n; intros; simpl; auto. ring. rewrite IHn. ring.
    Qed.

    (** <v1, v2 + v3> = <v1,v2> + <v1,v3> *)
    Lemma rvdot_add_distr_r : forall {n} (v1 v2 v3 : rvec n),
        (<v1,(v2 + v3)%RV> == <v1,v2> + <v1,v3>)%A.
    Proof.
      intros n [v1] [v2] [v3]. unfold rvdot; simpl.
      revert v1 v2 v3. induction n; intros; simpl; auto. ring. rewrite IHn. ring.
    Qed.

    (** <a c* v1, v2> = a * <v1,v2> *)
    Lemma rvdot_cmul_l : forall {n} (v1 v2 : rvec n) (a : A),
        (<a c* v1,v2> == a * <v1,v2>)%A.
    Proof.
      intros n [v1] [v2] a. unfold rvdot; simpl.
      rewrite seqsum_cmul_l. apply seqsum_eq; intros; ring.
    Qed.
    
    (** <v1, a c* v2> == a * <v1,v2> *)
    Lemma rvdot_cmul_r : forall {n} (v1 v2 : rvec n) (a : A),
        (<v1, a c* v2> == a * <v1,v2>)%A.
    Proof.
      intros n [v1] [v2] a. unfold rvdot; simpl.
      rewrite seqsum_cmul_l. apply seqsum_eq; intros; ring.
    Qed.

    (** <0,v> = 0 *)
    Lemma rvdot_0_l : forall {n} (v : rvec n), (<rvec0,v> == A0)%A.
    Proof. intros. apply seqsum_seq0. intros. cbv. ring. Qed.

    (** <v,0> = 0 *)
    Lemma rvdot_0_r : forall {n} (v : rvec n), (<v,rvec0> == A0)%A.
    Proof. intros. rewrite rvdot_comm, rvdot_0_l. easy. Qed.
    
  End vec_ring.

  Section test.
    Import ZArith.
    Open Scope Z_scope.
    Open Scope rvec_scope.
    
    Infix "+" := (rvadd (Aadd:=Z.add)) : rvec_scope.
    Notation "- v" := (rvopp (Aopp:=Z.opp) v) : rvec_scope.
    Infix "-" := (rvsub (Aadd:=Z.add)(Aopp:=Z.opp)) : rvec_scope.
    Infix "c*" := (rvcmul (Amul:=Z.mul)) : rvec_scope.
    Notation "< a , b >" :=  (rvdot a b (A0:=0) (Aadd:=Z.add) (Amul:=Z.mul)) : rvec_scope.

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

  Section vec_field.

    Context `{F : Field}.
    Infix "*" := (fun x y => Amul x y) : A_scope.
    Infix "/" := (fun x y => Amul x (Ainv y)) : A_scope.
    Infix "c*" := (rvcmul (Amul:=Amul)) : rvec_scope.

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

End RowVector.


Module Export ColVector.
  Open Scope cvec_scope.

  (* ======================================================================= *)
  (** ** Vector type *)

  (** A vector cvec(n) is a colum vector, equal to a matrix mat(n,1) *)
  Definition cvec {A : Type} (n : nat) := @mat A n 1.

  Definition mk_cvec {A : Type} {n : nat} (f : nat -> A) : @cvec A n :=
    @mk_mat A _ _ (fun i j => f i). (* Note, we won't limit "j" now. *)


  (* ======================================================================= *)
  (** ** Vector automation *)

  (** Convert vec to function *)
  Ltac cvec_to_fun :=
    repeat match goal with
      | v : cvec ?n |- _ => destruct v as [v]; simpl in *
      end.

  (** Linear vector arithmetic *)
  Ltac lva :=
    cvec_to_fun;
    lma.

  (* ======================================================================= *)
  (** ** Vector theory on general type *)
  Section basic.
    Context `{Equiv_Aeq : Equivalence A Aeq} {A0:A}.
    
    Infix "==" := Aeq : A_scope.
    Infix "==" := (eqlistA Aeq) : list_scope.
    Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.
    Notation "m ! i ! j " := (mnth A0 m i j) : mat_scope.

    (** --------------------------------------------------- *)
    (** *** Get element of vector *)

    (** get element from raw data, unsafe *)
    Notation "v $ i " := (v $ i $ 0) : cvec_scope.
    Notation "v .1" := (v $ 0) : cvec_scope.
    Notation "v .2" := (v $ 1) : cvec_scope.
    Notation "v .3" := (v $ 2) : cvec_scope.
    Notation "v .4" := (v $ 3) : cvec_scope.
    
    (** get element, safe *)
    Definition cvnth {n} (v : cvec n) i : A := v ! i ! 0.
    Notation "v ! i " := (cvnth v i) : cvec_scope.

    Lemma cvnth_spec : forall {n : nat} (v : cvec n) i ,
        i < n -> (v ! i == v $ i)%A.
    Proof. intros. unfold cvnth. apply mnth_eq_mnth_raw; auto. Qed.

    (** veq, iff vnth *)
    Lemma veq_iff_cvnth : forall {n : nat} (v1 v2 : cvec n),
        v1 == v2 <-> (forall i, i < n -> (v1 ! i == v2 ! i)%A).
    Proof.
      unfold cvec, cvnth. intros; split; intros.
      - rewrite (meq_iff_mnth (A0:=A0)) in H. apply H; auto.
      - rewrite (meq_iff_mnth (A0:=A0)). intros.
        assert (j = 0) by lia. subst; auto.
    Qed.

    (** veq, iff {top n-1 elements equal, and the n-th elements equal} *)
    

    
    (** --------------------------------------------------- *)
    (** *** Get column-vector of a matrix *)
    Definition mcol {r c : nat} (m : @mat A r c) (ci : nat) : cvec r :=
      mk_cvec (fun i => m $ i $ ci).

    
    (** --------------------------------------------------- *)
    (** *** List like operations for vector *)
    
    (** a :: v  *)
    Definition cvcons {n} (a : A) (v : cvec n) : cvec (S n) :=
      mk_cvec (fun i => match i with 0 => a | S i' => v $ i' end).

    Lemma cvcons_spec : forall n a (v : cvec n) i,
        let v' := cvcons a v in
        (v' $ 0 == a)%A /\ (i < n -> (v $ i == v' $ (S i))%A).
    Proof. intros. unfold cvcons. split; intros; solve_mnth. Qed.

    (** Get a vector from a given vector by remove k-th element *)
    Definition cvremove {n : nat} (v : @cvec A (S n)) (k : nat) : cvec n :=
      mk_cvec (fun i => if i <? k then v $ i else v $ (S i)).

    (** cons v.0 v.remove(0) = v *)
    Lemma cvcons_remove : forall {n} (v : @cvec A (S n)),
        cvcons (v$0) (cvremove v 0) == v.
    Proof. lva. Qed.
    
    (** --------------------------------------------------- *)
    (** *** Convert between list and vector *)
    Definition cv2l {n} (v : cvec n) : list A := map (fun i : nat => v $ i) (seq 0 n).
    Definition l2cv n (l : list A) : cvec n := mk_cvec (fun i => nth i l A0).

    (** list of vector to dlist *)
    Definition cvl2dl {n} (l : list (cvec n)) : dlist A := map cv2l l.

    Lemma cv2l_length : forall {n} (v : cvec n), length (cv2l v) = n.
    Proof. intros. unfold cv2l. rewrite map_length, seq_length; auto. Qed.

    Lemma cv2l_l2cv_id : forall {n} (l : list A),
        length l = n -> (cv2l (l2cv n l) == l)%list.
    Proof.
      intros. unfold l2cv,cv2l. simpl.
      apply nth_ext with (d1:=A0)(d2:=A0); intros; auto.
      - rewrite map_length, seq_length; auto.
      - rewrite map_length, seq_length in *. rewrite ?nth_map_seq; auto. f_equiv. lia.
    Qed.

    Lemma l2cv_cv2l_id : forall {n} (v : cvec n), l2cv n (cv2l v) == v.
    Proof. lva. unfold cv2l. rewrite nth_map_seq; auto. f_equiv. easy. Qed.

    
    (** --------------------------------------------------- *)
    (** *** Make concrete vector *)
    Definition mk_cvec2 (a0 a1 : A) : cvec 2 := l2cv 2 [a0;a1].
    Definition mk_cvec3 (a0 a1 a2 : A) : cvec 3 := l2cv 3 [a0;a1;a2].
    Definition mk_cvec4 (a0 a1 a2 a3 : A) : cvec 4 := l2cv 4 [a0;a1;a2;a3].

    
    (** --------------------------------------------------- *)
    (** *** Convert between tuples and vector *)
    Definition t2cv_2 (t : @T2 A) : cvec 2 := let '(a,b) := t in l2cv 2 [a;b].
    Definition t2cv_3 (t : @T3 A) : cvec 3 := let '(a,b,c) := t in l2cv 3 [a;b;c].
    Definition t2cv_4 (t : @T4 A) : cvec 4 := let '(a,b,c,d) := t in l2cv 4 [a;b;c;d].

    Definition cv2t_2 (v : cvec 2) : @T2 A := (v.1, v.2).
    Definition cv2t_3 (v : cvec 3) : @T3 A := (v.1, v.2, v.3).
    Definition cv2t_4 (v : cvec 4) : @T4 A := (v.1, v.2, v.3, v.4).

    (* Lemma cv2t_t2cv_id_2 : forall (t : A * A), cv2t_2 (t2cv_2 t) == t. *)
    (* Proof. intros. destruct t. simpl. unfold v2t_2. f_equal. Qed. *)

    Lemma t2cv_cv2t_id_2 : forall (v : cvec 2), t2cv_2 (cv2t_2 v) == v.
    Proof. lva. Qed.

    
    (** --------------------------------------------------- *)
    (** *** vector mapping *)
    Definition cvmap {n} (v : cvec n) (f : A -> A) : cvec n := mmap f v.
    Definition cvmap2 {n} (v1 v2 : cvec n) (f : A -> A -> A) : cvec n := mmap2 f v1 v2.


    (** --------------------------------------------------- *)
    (** *** vector folding *)
    Definition cvfold {n} {B:Type} (v : @cvec A n) (f : B -> A -> B) (b0 : B) : B :=
      seqfold (fun i => v$i) n f b0.

  End basic.

  Arguments cvnth {A} A0 {n}.
  Arguments l2cv {A}.
  Arguments mk_cvec2 {A}.
  Arguments mk_cvec3 {A}.
  Arguments mk_cvec4 {A}.
  Arguments t2cv_2 {A}.
  Arguments t2cv_3 {A}.
  Arguments t2cv_4 {A}.

  Notation "v $ i " := (v $ i $ 0) : cvec_scope.
  Notation "v .1" := (v $ 0) : cvec_scope.
  Notation "v .2" := (v $ 1) : cvec_scope.
  Notation "v .3" := (v $ 2) : cvec_scope.
  Notation "v .4" := (v $ 3) : cvec_scope.

  Section test.
    Notation "v ! i " := (cvnth 0 v i) : cvec_scope.
    Let v1 : cvec 3 := l2cv 0 3 [1;2].
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
    Infix "+" := Aadd : A_scope.
    Notation "- a" := (Aopp a) : A_scope.
    Infix "-" := (fun a b => a + (-b)) : A_scope.

    Infix "==" := (eqlistA Aeq) : list_scope.

    Notation meq := (meq (Aeq:=Aeq)).
    Infix "==" := (meq) : mat_scope.

    Notation seqsum := (seqsum (Aadd:=Aadd)(A0:=A0)).
    
    (* Infix "+" := (ladd (Aadd:=Aadd)) : list_scope. *)

    (** *** Zero vector *)

    (** Make a zero vector *)
    Definition cvec0 {n} : cvec n := mat0 A0.

    (** A vector is a zero vector. *)
    Definition cvzero {n} (v : cvec n) : Prop := v == cvec0.

    (** A vector is a non-zero vector. *)
    Definition cvnonzero {n} (v : cvec n) : Prop := ~(cvzero v).
    
    (** vec0 is equal to mat0 with column 1 *)
    Lemma cvec0_eq_mat0 : forall n, (@cvec0 n) == mat0 A0.
    Proof. intros. easy. Qed.

    (** *** Vector addition *)

    Definition cvadd {n} (v1 v2 : cvec n) : cvec n := madd (Aadd:=Aadd) v1 v2.
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
    
    Definition cvopp {n} (v : cvec n) : cvec n := mopp (Aopp:=Aopp) v.
    Notation "- v" := (cvopp v) : cvec_scope.

    (** (- v) + v = vec0 *)
    Lemma cvadd_opp_l : forall {n} (v : cvec n), (- v) + v == cvec0.
    Proof. intros. apply madd_opp_l. Qed.

    (** v + (- v) = vec0 *)
    Lemma cvadd_opp_r : forall {n} (v : cvec n), v + (- v) == cvec0.
    Proof. intros. apply madd_opp_r. Qed.

    (** - (v1 + v2) = (- v1) + (- v2) *)
    Lemma cvopp_add : forall {n} (v1 v2 : cvec n), - (v1 + v2) == (- v1) + (- v2).
    Proof. intros. apply mopp_add. Qed.


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
    (* intros. apply Group_MatAadd. Qed. *)

    
    (** Let's have a ring *)
    Context `{R : Ring A Aadd A0 Aopp Amul A1 Aeq}.
    Add Ring ring_inst : (make_ring_theory R).
    Infix "*" := Amul : A_scope.
    
    Infix "*" := (@mmul _ Aadd A0 Amul _ _ _) : mat_scope.
    Infix "c*" := (mcmul (Amul:=Amul)) : mat_scope.
    Infix "*c" := (mmulc (Amul:=Amul)) : mat_scope.

    (** *** Vector scalar multiplication *)

    Definition cvcmul {n} a (v : cvec n) : cvec n := mcmul (Amul:=Amul) a v.
    Infix "c*" := cvcmul : cvec_scope.

    (* (** vcmul is a proper morphism *) *)
    (* Global Instance cvcmul_mor : forall n, Proper (Aeq ==> meq ==> meq) (cvcmul (n:=n)). *)
    (* Proof. intros. apply mcmul_mor. Qed. *)

    (** a c* (b c* v) = (a * b) c* v *)
    Lemma cvcmul_assoc : forall {n} a b (v : cvec n), a c* (b c* v) == (a * b)%A c* v.
    Proof. intros. apply mcmul_assoc. Qed.

    (** a c* (b c* v) = b c* (a c* v) *)
    Lemma cvcmul_perm : forall {n} a b (v : cvec n), a c* (b c* v) == b c* (a c* v).
    Proof. intros. apply mcmul_perm. Qed.

    (** a c* (v1 + v2) = (a c* v1) + (a c* v2) *)
    Lemma cvcmul_add_distr_l : forall {n} a (v1 v2 : cvec n), 
        a c* (v1 + v2) == (a c* v1) + (a c* v2).
    Proof. intros. apply mcmul_add_distr_l. Qed.

    (** (a + b) c* v = (a c* v) + (b c* v) *)
    Lemma cvcmul_add_distr_r : forall {n} a b (v : cvec n),
        (a + b)%A c* v == (a c* v) + (b c* v).
    Proof. intros. apply mcmul_add_distr_r. Qed.

    (** 1 c* v = v *)
    Lemma cvcmul_1_l : forall {n} (v : cvec n), A1 c* v == v.
    Proof. intros. apply mcmul_1_l. Qed.

    (** 0 c* v = cvec0 *)
    Lemma cvcmul_0_l : forall {n} (v : cvec n), A0 c* v == cvec0.
    Proof. intros. apply mcmul_0_l. Qed.

    (** a c* 0 = cvec0 *)
    Lemma cvcmul_0_r : forall {n} a, a c* (@cvec0 n) == cvec0.
    Proof. intros. apply mcmul_0_r. Qed.

    (** - (a c* v) = (-a) c* v *)
    Lemma cvopp_cmul : forall {n} a (v : cvec n), - (a c* v) == (-a)%A c* v.
    Proof. lva. Qed.

    (** a c* (v1 - v2) = (a c* v1) - (a c* v2) *)
    Lemma cvcmul_sub : forall {n} a (v1 v2 : cvec n),
        a c* (v1 - v2) == (a c* v1) - (a c* v2).
    Proof. lva. Qed.

    Lemma cvcmul_mul_assoc_l : forall {r c} (a : A) (m : mat r c) (v : cvec c), 
        a c* (m * v) == (a c* m)%M * v.
    Proof. intros. apply mcmul_mul_assoc_l. Qed.

    Lemma cvcmul_mul_assoc_r : forall {r c} (a : A) (m : mat r c) (v : cvec c), 
        a c* (m * v) == m * (a c* v).
    Proof. intros. apply mcmul_mul_assoc_r. Qed.
    

    Definition cvmulc {n} (v : cvec n) a : cvec n := mmulc (Amul:=Amul) v a.
    Infix "*c" := cvmulc : cvec_scope.

    (** v *c a = a c* v *)
    Lemma cvmulc_eq_cmul : forall {n} a (v : cvec n), (v *c a) == (a c* v).
    Proof. intros. apply mmulc_eq_cmul. Qed.

    
    (** *** Vector dot product *)

    (* (** version 1, by {fold_left,map,seq} *) *)
    (* Definition vdot_old {n : nat} (v1 v2 : cvec n) : A := *)
    (*   fold_left Aadd (map (fun i => v1$i * v2$i) (seq 0 n)) A0. *)

    (** dot production of two vectors. *)
    Definition cvdot {n : nat} (v1 v2 : cvec n) : A :=
      seqsum (fun i => v1$i * v2$i)%A n.
    Notation "< a , b >" := (cvdot a b) : cvec_scope.

    Global Instance cvdot_mor {n} : Proper (meq ==> meq ==> Aeq) (@cvdot n).
    Proof.
      simp_proper. intros. unfold cvdot.
      apply seqsum_eq. intros. f_equiv; auto.
    Qed.

    (** [m1 * m2].ij = <row(m1,i)\T, col(m2,j)> *)
    Lemma mmul_eq_dot_row_col : forall {r c s} (m1 : mat r c) (m2 : mat c s) i j,
        i < r -> j < s -> ((m1 * m2)%M $ i $ j == <(mrow m1 i)\T, mcol m2 j>)%A.
    Proof. intros. mat_to_fun. unfold mrow,mcol,cvdot. simpl. easy. Qed.

    (** <v1,v2> = v1\T * v2 *)
    Lemma cvdot_eq_mul_trans : forall {n} (v1 v2 : cvec n),
        (<v1,v2> == scalar_of_mat (v1\T * v2)%M)%A.
    Proof. intros. simpl. apply seqsum_eq. intros. easy. Qed.

    (** <v1,v2> = <v2,v1> *)
    Lemma cvdot_comm : forall {n} (v1 v2 : cvec n), (<v1,v2> == <v2,v1>)%A.
    Proof. intros. apply seqsum_eq. intros. ring. Qed.

    (** <v1 + v2, v3> = <v1,v3> + <v2,v3> *)
    Lemma cvdot_add_distr_l : forall {n} (v1 v2 v3 : cvec n),
        (<(v1 + v2)%CV,v3> == <v1,v3> + <v2,v3>)%A.
    Proof.
      intros n [v1] [v2] [v3]. unfold cvdot; simpl.
      revert v1 v2 v3. induction n; intros; simpl; auto. ring. rewrite IHn. ring.
    Qed.

    (** <v1, v2 + v3> = <v1,v2> + <v1,v3> *)
    Lemma cvdot_add_distr_r : forall {n} (v1 v2 v3 : cvec n),
        (<v1, (v2 + v3)%CV> == <v1,v2> + <v1,v3>)%A.
    Proof.
      intros n [v1] [v2] [v3]. unfold cvdot; simpl.
      revert v1 v2 v3. induction n; intros; simpl; auto. ring. rewrite IHn. ring.
    Qed.

    (** <a c* v1, v2> = a * <v1,v2> *)
    Lemma cvdot_cmul_l : forall {n} (v1 v2 : cvec n) (a : A),
        (<a c* v1, v2> == a * <v1,v2>)%A.
    Proof.
      intros n [v1] [v2] a. unfold cvdot; simpl.
      rewrite seqsum_cmul_l. apply seqsum_eq; intros; ring.
    Qed.
    
    (** <v1, a c* v2> == a * <v1,v2> *)
    Lemma cvdot_cmul_r : forall {n} (v1 v2 : cvec n) (a : A),
        (<v1, a c* v2> == a * <v1,v2>)%A.
    Proof.
      intros n [v1] [v2] a. unfold cvdot; simpl.
      rewrite seqsum_cmul_l. apply seqsum_eq; intros; ring.
    Qed.

    (** <0,v> = 0 *)
    Lemma cvdot_0_l : forall {n} (v : cvec n), (<cvec0,v> == A0)%A.
    Proof. intros. apply seqsum_seq0. intros. cbv. ring. Qed.

    (** <v,0> = 0 *)
    Lemma cvdot_0_r : forall {n} (v : cvec n), (<v,cvec0> == A0)%A.
    Proof. intros. rewrite cvdot_comm, cvdot_0_l. easy. Qed.

    (** *** Connection and difference between "Matrix multiplication with row vector 
        or column vector" *)

    (** M * v = v * M\T *)
    Lemma mmv_eq_vmmt : forall {r c : nat} (M : mat r c) (v : cvec c),
        (* Treat the column vector v as a row vector *)
        let v' : rvec c := v\T in
        (* matrix left multiply a vector *)
        let u1 : cvec r := M * v in
        (* matrix right multiply a vector (the matrix need to be transposed) *)
        let u2 : rvec r := v' * M\T in
        (* Treat the row vector u2 as a column vector *)
        let u2' : cvec r := u2\T in
        (* The result must be same *)
        u1 == u2'.
      Proof. lva. apply seqsum_eq. intros. ring. Qed.
    
    (** v * M = M\T * v *)
    Lemma mvm_eq_mtmv : forall {r c : nat} (v : rvec r) (M : mat r c),
        (* Treat the row vector v as a column vector *)
        let v' : cvec r := v\T in
        (* matrix right multiply a vector *)
        let u1 : rvec c := v * M in
        (* matrix left multiply a vector (the matrix need to be transposed) *)
        let u2 : cvec c := M\T * v' in
        (* Treat the column vector u2 as a row vector *)
        let u2' : rvec c := u2\T in
        (* The result must be same *)
        u1 == u2'.
    Proof. lva. apply seqsum_eq. intros. ring. Qed.

    (** Thus, we proved that, row vector and column vector are different but have 
        a tight connection. *)
    
  End vec_ring.

  Section test.
    Import ZArith.
    Open Scope Z_scope.
    Open Scope cvec_scope.
    
    Infix "+" := (cvadd (Aadd:=Z.add)) : cvec_scope.
    Notation "- v" := (cvopp (Aopp:=Z.opp) v) : cvec_scope.
    Infix "-" := (cvsub (Aadd:=Z.add)(Aopp:=Z.opp)) : cvec_scope.
    Infix "c*" := (cvcmul (Amul:=Z.mul)) : cvec_scope.
    Notation "< a , b >" := (cvdot a b (A0:=0) (Aadd:=Z.add) (Amul:=Z.mul)) : cvec_scope.

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

  Section vec_field.

    Context `{F : Field}.
    Infix "*" := (fun x y => Amul x y) : A_scope.
    Infix "/" := (fun x y => Amul x (Ainv y)) : A_scope.
    Infix "c*" := (cvcmul (Amul:=Amul)) : cvec_scope.

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

End ColVector.


(** ** Convertion between cvec and rvec *)

Section cvt.
  Context `{Equiv_Aeq : Equivalence A Aeq} {A0:A}.
  
  Infix "==" := Aeq : A_scope.
  Infix "==" := (meq (Aeq:=Aeq)) : mat_scope.

  Definition cv2rv {n} (v : cvec n) : rvec n :=
    mk_rvec (fun i => cvnth A0 v i).

  Lemma cv2rv_spec : forall {n} (v : cvec n), cv2rv v == v\T.
  Proof. lva. rewrite cvnth_spec; easy. Qed.

  Definition rv2cv {n} (v : rvec n) : cvec n :=
    mk_cvec (fun i => rvnth A0 v i).

  Lemma rv2cv_spec : forall {n} (v : rvec n), rv2cv v == v\T.
  Proof. lva. rewrite rvnth_spec; easy. Qed.



End cvt.

Section test.
  Infix "==" := (meq (Aeq:=eq)) : mat_scope.

  Let cv1 : cvec 3 := l2cv 0 3 [1;2;3].
  Let rv1 : rvec 3 := l2rv 0 3 [1;2;3].
  (* Compute cv1. *)
  (* Compute cv1. *)

  Goal cv2rv (A0:=0) cv1 == rv1.
    lma. Qed.
  Goal rv2cv (A0:=0) rv1 == cv1.
    lma. Qed.

End test.
