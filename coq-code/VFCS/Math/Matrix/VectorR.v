(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector on R.
  author    : ZhengPu Shi
  date      : 2021.12

  reference :
  1. 《高等数学学习手册》徐小湛，p173
  2. 《高等数学》 第七版，同济大学数学系，第八章，向量代数与空间解析几何
  3. Vector Calculus - Michael Corral
  4. https://github.com/coq/coq/blob/master/test-suite/success/Nsatz.v
     Note that, there are concepts related to geometry including point, parallel, 
     colinear.

  remark    :
  一. 关于零向量的平行和垂直问题
  1. 来自《高等数学》的理论：
  (1) 零向量的起点和终点重合，它的方向可看做是任意的。
  (2) 如果∠a,b = 0 or π，则称它们平行，记做 a∥b。
      当两向量平行时，若将起点放在同一点，则终点和公共起点应在同一条直线，故
      两向量平行也称两向量共线。
  (3) 如果∠a,b = π/2，称它们垂直，记做 a⟂b。
  (4) 由于零向量与另一向量的夹角可以是[0,π]中的任意值，可认为零向量与任何向量
      都平行，也可认为零向量与任何向量都垂直。
  2. 网络上的观点
  (1) There are two choices to handling zero-vector
      a. The mainstream approach is that the zero vector is parallel and
         perpendicular to any vector.
      b. Only consider the non-zero vector, one reason of it is that the 
         transitivity is broken after including zero-vector.
         (因为包含了零向量以后，平行的传递性被破坏了）
  (2) https://www.zhihu.com/question/489006373
      a. “平行”或“不平行”是对两个可以被识别的方向的比较，对于零向量，“方向”是不可
         识别的，或说，是不确定的。从这个角度讲，“平行”这个概念不该被用到评价两个
         零向量的关系上的。
      b. 不过，两个零向量是“相等”的，对于向量而言，“相等”这件事包含了大小和方向
         的相等，这么说来，说两个零向量“方向”相等，也就是“平行”或也是说得通的。
  3. 本文的做法
  (1) 使用向量的运算来定义平行和垂直，这样无须三角函数就能判定。
      两向量点乘为零，则它们垂直；两向量叉乘为零向量，则它们平行。
  (2) 在严格证明中，都加上非零向量这一假设条件。

  二、一些观点
  1. 在三维向量空间中：空间点M <-> 原点O指向M的向量 r⃗=OM=xi+yj+zk <-> 有序数(x,y,z)

 *)

Require Export Vector.
Require Export MatrixR.

Open Scope R_scope.
Open Scope mat_scope.


Module Export RowVectorR.
  Open Scope rvec_scope.

  (* ======================================================================= *)
  (** ** Vector theory come from common implementations *)
  
  (** *** vector type and basic operation *)
  Definition rvec (n : nat) : Type := @rvec A n.

  Definition rvnth {n : nat} (v : rvec n) (i : nat) : A := rvnth A0 v i.
  Notation "v ! i" := (rvnth v i) : rvec_scope.

  Lemma veq_iff_rvnth : forall {n : nat} (v1 v2 : rvec n),
      (v1 == v2) <-> (forall i, i < n -> (v1!i == v2!i)%A)%nat.
  Proof. intros. apply veq_iff_rvnth. Qed.

  Definition mat2row {r c} (m : mat r c) (ci : nat) : rvec c := mat2row m ci.

  
  (** *** convert between list and vector *)
  Definition l2rv n (l : list A) : rvec n := l2rv A0 n l.
  Definition rv2l {n} (v : rvec n) : list A := rv2l v.

  Lemma rv2l_length : forall {n} (v : rvec n), length (rv2l v) = n.
  Proof. intros. apply rv2l_length. Qed.

  Lemma rv2l_l2rv_id : forall {n} (l : list A), length l = n -> (rv2l (l2rv n l) == l)%list.
  Proof. intros. apply rv2l_l2rv_id; auto. Qed.

  Lemma l2rv_rv2l_id : forall {n} (v : rvec n), l2rv n (rv2l v) == v.
  Proof. intros. apply l2rv_rv2l_id; auto. Qed.


  (** *** Convert between tuples and vector *)
  Definition t2rv_2 (t : T2) : rvec 2 := t2rv_2 A0 t.
  Definition t2rv_3 (t : T3) : rvec 3 := t2rv_3 A0 t.
  Definition t2rv_4 (t : T4) : rvec 4 := t2rv_4 A0 t.

  Definition rv2t_2 (v : rvec 2) : T2 := rv2t_2 v.
  Definition rv2t_3 (v : rvec 3) : T3 := rv2t_3 v.
  Definition rv2t_4 (v : rvec 4) : T4 := rv2t_4 v.

  (* Lemma t2v_v2t_id_2 : forall (v : vec 2), t2v_2 (v2t_2 v) == v. *)
  (* Lemma v2t_t2v_id_2 : forall (t : T2), v2t_2 (t2v_2 t) = t. *)


  (** *** make concrete vector *)
  Definition mk_rvec2 a0 a1 : rvec 2 := mk_rvec2 A0 a0 a1.
  Definition mk_rvec3 a0 a1 a2 : rvec 3 := mk_rvec3 A0 a0 a1 a2.
  Definition mk_rvec4 a0 a1 a2 a3 : rvec 4 := mk_rvec4 A0 a0 a1 a2 a3.


  (** *** vector mapping *)
  Definition rvmap {n} f (v : rvec n) : rvec n := rvmap v f.
  Definition rvmap2 {n} f (v1 v2 : rvec n) : rvec n := rvmap2 v1 v2 f.

  
  (** *** vector folding *)
  (* Definition vfold : forall {B : Type} {n} (v : vec n) (f : A -> B) (b : B), B. *)


  (** *** zero vector *)
  Definition rvec0 {n} : rvec n := rvec0 (A0:=A0).


  (** *** vector addition, opposition and subtraction *)
  Definition rvadd {n} (v1 v2 : rvec n) : rvec n := rvadd v1 v2 (Aadd:=Aadd).
  Infix "+" := rvadd : rvec_scope.

  Lemma rvadd_comm : forall {n} (v1 v2 : rvec n), (v1 + v2) == (v2 + v1).
  Proof. intros. apply rvadd_comm. Qed.

  Lemma rvadd_assoc : forall {n} (v1 v2 v3 : rvec n), (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof. intros. apply rvadd_assoc. Qed.

  Lemma rvadd_0_l : forall {n} (v : rvec n), rvec0 + v == v.
  Proof. intros. apply rvadd_0_l. Qed.

  Lemma rvadd_0_r : forall {n} (v : rvec n), v + rvec0 == v.
  Proof. intros. apply rvadd_0_r. Qed.

  Definition rvopp {n} (v : rvec n) : rvec n := rvopp v (Aopp:=Aopp).
  Notation "- v" := (rvopp v) : rvec_scope.

  Lemma rvadd_opp_l : forall {n} (v : rvec n), (- v) + v == rvec0.
  Proof. intros. apply rvadd_opp_l. Qed.

  Lemma rvadd_opp_r : forall {n} (v : rvec n), v + (- v) == rvec0.
  Proof. intros. apply rvadd_opp_r. Qed.

  Definition rvsub {n} (v1 v2 : rvec n) : rvec n := rvsub v1 v2 (Aadd:=Aadd) (Aopp:=Aopp).
  Infix "-" := rvsub : rvec_scope.


  (** *** vector scalar multiplication *)
  Definition rvcmul {n} a (v : rvec n) : rvec n := rvcmul a v (Amul:=Amul).
  Infix "c*" := rvcmul : rvec_scope.

  Lemma rvcmul_assoc : forall {n} a b (v : rvec n), a c* (b c* v) == (a * b) c* v.
  Proof. intros. apply rvcmul_assoc. Qed.

  Lemma rvcmul_perm : forall {n} a b (v : rvec n), a c* (b c* v) == b c* (a c* v).
  Proof. intros. apply rvcmul_perm. Qed.

  Lemma rvcmul_add_distr_l : forall {n} a b (v : rvec n),
      (a + b) c* v == (a c* v) + (b c* v).
  Proof. intros. apply rvcmul_add_distr_l. Qed.

  Lemma rvcmul_add_distr_r : forall {n} a (v1 v2 : rvec n),
      a c* (v1 + v2) == (a c* v1) + (a c* v2).
  Proof. intros. apply rvcmul_add_distr_r. Qed.

  Lemma rvcmul_0_l : forall {n} (v : rvec n), A0 c* v == rvec0.
  Proof. intros. apply rvcmul_0_l. Qed.

  Lemma rvcmul_1_l : forall {n} (v : rvec n), A1 c* v == v.
  Proof. intros. apply rvcmul_1_l. Qed.


  (** *** vector dot product *)
  Definition rvdot {n} (v1 v2 : rvec n) :=
    rvdot v1 v2 (Aadd:=Aadd)(A0:=A0)(Amul:=Amul).

  
  (* ======================================================================= *)
  (** ** Vector theory applied to this type *)


  (* ======================================================================= *)
  (** ** Usage demo *)
  Section test.

    Let l1 := [1;2;3].
    Let v1 := l2rv 2 l1.
    (* Compute rv2l (@l2rv 3 l1). *)

    Variable a1 a2 a3 : R.
    Let v2 := t2rv_3 (a1,a2,a3).
    (* Eval cbn in rv2l (rvmap Ropp v2). *)
  End test.

End RowVectorR.


Module Export ColVectorR.
  Open Scope cvec_scope.

  (* ======================================================================= *)
  (** ** Vector theory come from common implementations *)

  (** *** vector type and basic operation *)
  Definition cvec (n : nat) : Type := @cvec A n.

  
  (** *** vector automation *)

  (** Convert vec to function *)
  Ltac cvec_to_fun :=
    repeat match goal with
      | v : cvec ?n |- _ => destruct v as [v]; simpl in *
      end.

  (** Linear vector arithmetic *)
  Ltac lva :=
    cvec_to_fun;
    lma.

  
  (** *** geth nth element *)
  Definition cvnth {n : nat} (v : cvec n) (i : nat) : A := cvnth A0 v i.
  Notation "v ! i" := (cvnth v i) : cvec_scope.

  Lemma veq_iff_cvnth : forall {n : nat} (v1 v2 : cvec n),
      (v1 == v2) <-> (forall i, i < n -> (v1!i == v2!i)%A)%nat.
  Proof. intros. apply veq_iff_cvnth. Qed.

  Definition mat2vec {r c} (m : mat r c) (ri : nat) : cvec r := mat2col m ri.


  (** *** convert between list and vector *)
  Definition l2cv n (l : list A) : cvec n := l2cv A0 n l.
  Definition cv2l {n} (v : cvec n) : list A := cv2l v.

  Lemma cv2l_length : forall {n} (v : cvec n), length (cv2l v) = n.
  Proof. intros. apply cv2l_length. Qed.

  Lemma cv2l_l2cv_id : forall {n} (l : list A), length l = n -> (cv2l (l2cv n l) == l)%list.
  Proof. intros. apply cv2l_l2cv_id; auto. Qed.

  Lemma l2cv_cv2l_id : forall {n} (v : cvec n), l2cv n (cv2l v) == v.
  Proof. intros. apply l2cv_cv2l_id; auto. Qed.


  (** *** Convert between tuples and vector *)
  Definition t2cv_2 (t : T2) : cvec 2 := t2cv_2 A0 t.
  Definition t2cv_3 (t : T3) : cvec 3 := t2cv_3 A0 t.
  Definition t2cv_4 (t : T4) : cvec 4 := t2cv_4 A0 t.

  Definition cv2t_2 (v : cvec 2) : T2 := cv2t_2 v.
  Definition cv2t_3 (v : cvec 3) : T3 := cv2t_3 v.
  Definition cv2t_4 (v : cvec 4) : T4 := cv2t_4 v.

  (* Lemma t2v_v2t_id_2 : forall (v : vec 2), t2v_2 (v2t_2 v) == v. *)
  (* Lemma v2t_t2v_id_2 : forall (t : T2), v2t_2 (t2v_2 t) = t. *)


  (** *** make concrete vector *)
  Definition mk_cvec2 a0 a1 : cvec 2 := mk_cvec2 A0 a0 a1.
  Definition mk_cvec3 a0 a1 a2 : cvec 3 := mk_cvec3 A0 a0 a1 a2.
  Definition mk_cvec4 a0 a1 a2 a3 : cvec 4 := mk_cvec4 A0 a0 a1 a2 a3.


  (** *** vector mapping *)
  Definition cvmap {n} f (v : cvec n) : cvec n := cvmap v f.
  Definition cvmap2 {n} f (v1 v2 : cvec n) : cvec n := cvmap2 v1 v2 f.


  (** *** vector folding *)
  (* Definition vfold : forall {B : Type} {n} (v : vec n) (f : A -> B) (b : B), B. *)


  (** *** zero vector *)
  Definition cvec0 {n} : cvec n := cvec0 (A0:=A0).


  (** *** vector addition, opposition and subtraction *)
  Definition cvadd {n} (v1 v2 : cvec n) : cvec n := cvadd v1 v2 (Aadd:=Aadd).
  Infix "+" := cvadd : cvec_scope.

  Lemma cvadd_comm : forall {n} (v1 v2 : cvec n), (v1 + v2) == (v2 + v1).
  Proof. intros. apply cvadd_comm. Qed.

  Lemma cvadd_assoc : forall {n} (v1 v2 v3 : cvec n), (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof. intros. apply cvadd_assoc. Qed.

  Lemma cvadd_0_l : forall {n} (v : cvec n), cvec0 + v == v.
  Proof. intros. apply cvadd_0_l. Qed.

  Lemma cvadd_0_r : forall {n} (v : cvec n), v + cvec0 == v.
  Proof. intros. apply cvadd_0_r. Qed.

  Definition cvopp {n} (v : cvec n) : cvec n := cvopp v (Aopp:=Aopp).
  Notation "- v" := (cvopp v) : cvec_scope.

  Lemma cvadd_opp_l : forall {n} (v : cvec n), (- v) + v == cvec0.
  Proof. intros. apply cvadd_opp_l. Qed.

  Lemma cvadd_opp_r : forall {n} (v : cvec n), v + (- v) == cvec0.
  Proof. intros. apply cvadd_opp_r. Qed.

  Definition cvsub {n} (v1 v2 : cvec n) : cvec n := cvsub v1 v2 (Aadd:=Aadd) (Aopp:=Aopp).
  Infix "-" := cvsub : cvec_scope.


  (** *** vector scalar multiplication *)
  Definition cvcmul {n} a (v : cvec n) : cvec n := cvcmul a v (Amul:=Amul).
  Infix "c*" := cvcmul : cvec_scope.

  Lemma cvcmul_assoc : forall {n} a b (v : cvec n), a c* (b c* v) == (a * b) c* v.
  Proof. intros. apply cvcmul_assoc. Qed.

  Lemma cvcmul_perm : forall {n} a b (v : cvec n), a c* (b c* v) == b c* (a c* v).
  Proof. intros. apply cvcmul_perm. Qed.

  Lemma cvcmul_add_distr_l : forall {n} a b (v : cvec n),
      (a + b) c* v == (a c* v) + (b c* v).
  Proof. intros. apply cvcmul_add_distr_l. Qed.

  Lemma cvcmul_add_distr_r : forall {n} a (v1 v2 : cvec n),
      a c* (v1 + v2) == (a c* v1) + (a c* v2).
  Proof. intros. apply cvcmul_add_distr_r. Qed.

  Lemma cvcmul_0_l : forall {n} (v : cvec n), A0 c* v == cvec0.
  Proof. intros. apply cvcmul_0_l. Qed.

  Lemma cvcmul_1_l : forall {n} (v : cvec n), A1 c* v == v.
  Proof. intros. apply cvcmul_1_l. Qed.


  (** *** vector dot product *)
  Definition cvdot {n} (v1 v2 : cvec n) :=
    cvdot v1 v2 (Aadd:=Aadd)(A0:=A0)(Amul:=Amul).

  Infix "⋅" := cvdot : cvec_scope.

  
  (* ======================================================================= *)
  (** ** Vector theory applied to this type *)

  
  (** *** vector dot product *)
  Lemma cvdot_ge0 : forall {n} (v : cvec n), 0 <= v ⋅ v.
  Proof.
    intros. cvec_to_fun. unfold cvdot, ColVector.cvdot. simpl.
    revert v. induction n; intros; simpl; try lra. ra.
  Qed.

  
  (** *** zero or nonzero vector *)
  Section vzero_vnonzero.
    
    (** A vector is a zero vector. *)
    Definition cvzero {n} (v : cvec n) : Prop := cvzero v (A0:=A0)(Aeq:=Aeq).

    (** A vector is a non-zero vector. *)
    Definition cvnonzero {n} (v : cvec n) : Prop := cvnonzero v (A0:=A0)(Aeq:=Aeq).

    (** Any zero vector is vec0 *)
    Lemma cvzero_imply_vec0 : forall {n} (v : cvec n), cvzero v -> v == cvec0.
    Proof. intros. auto. Qed.

    (** If k times a non-zero vector equal to zero vector, then k must be not zero *)
    Lemma cvcmul_vnonzero_neq0_imply_neq0 : forall {n} (v : cvec n) k,
        cvnonzero v -> ~(k c* v == cvec0) -> k <> 0.
    Proof. intros. intro. subst. rewrite cvcmul_0_l in H0. destruct H0. easy. Qed.

    (** Two non-zero vectors has k-times relation, then k is not zero *)
    Lemma cvec_eq_vcmul_imply_coef_neq0 : forall {n} (v1 v2 : cvec n) k,
        cvnonzero v1 -> cvnonzero v2 -> v1 == k c* v2 -> k <> 0.
    Proof. intros. intro. subst. rewrite cvcmul_0_l in H1. easy. Qed.

    (** If k times a non-zero vector equal to zero, then k must be zero *)
    (*
    v <> 0 ==> ~(∀ i, v[i] = 0)
    k*v = 0 ==> ∀ i, k*v[i] = 0
    {k=0}+{k<>0} ==> k<>0  (if k=0, then qed)
    ---------------------------
    ∃ i, v[i] <> 0, then, k*v[i] <> 0, thus, contradict.
     *)
    Lemma cvcmul_nonzero_eq_zero_imply_k0 : forall {n} (v : cvec n) k,
        cvnonzero v -> k c* v == cvec0 -> k = 0.
    Proof.
      intros. destruct v as [v]. cbv in *.
      destruct (k ==? 0); auto.
      (* idea: from "~(∀ij(v i j = 0)" to "∃ij(v i j≠0)" *)
      (* Tips, a good practice of logic proposition *)
      assert (exists (ij:nat*nat), let (i,j) := ij in (i<n)%nat /\ (j<1)%nat /\ (v i j <> 0)).
      { clear k H0 n0.
        apply not_all_not_ex. intro.
        destruct H. intros. specialize (H0 (i,0)%nat). simpl in H0.
        apply not_and_or in H0. destruct H0; try easy.
        apply not_and_or in H0. destruct H0; try easy; try lia.
        apply NNPP in H0.
        assert (j = 0%nat) by lia. subst. auto. }
      destruct H1. destruct x as (i,j). destruct H1. destruct H2.
      specialize (H0 i j H1 H2).
      apply Rmult_integral in H0. destruct H0; easy.
    Qed.

    (** If use k1 and k2 to left multiplicate a non-zero vector get same result, 
      then k1 and k2 must be equal. *)
    Lemma cvcmul_vnonzero_eq_iff_unique_k : forall {n} (v : cvec n) k1 k2, 
        cvnonzero v -> k1 c* v == k2 c* v -> k1 = k2.
    Proof.
      intros. destruct v as [v]. cbv in H,H0.
      (* ∀i(f(i)=0 /\ k1*f(i) = k2*f(i)) -> k1 = k2 *)
      destruct (k1 ==? k2); auto.
      destruct H. intros. (* eliminated the universal quantifiers *)
      specialize (H0 i j H H1).
      (* k1 * x = k2 * x  /\  k1 <> k2  -> x = 0 *)
      ra.
    Qed.

    (** If k times a non-zero vector equal to itself, then k is equal to 1 *)
    Lemma cvcmul_vnonzero_eq_self_imply_k1 : forall {n} (v : cvec n) k,
        cvnonzero v -> k c* v == v -> k = 1.
    Proof.
      intros. destruct v as [g].
      cbv in H,H0.
      (* To prove k = 1， first get a conclusion of k <> 1, then eliminate the 
         universal quantifiers *)
      destruct (k ==? 1); auto.
      destruct H. intros. specialize (H0 i j H H1).
      (* k * x = x /\  k <> 1 /\ x <> 0 -> x = 0 *)
      apply Rmult_eq_self_imply_0_or_k1 in H0. destruct H0; try easy.
    Qed.

  End vzero_vnonzero.


  (** ** length of a vector *)
  Section vlen.

    (** Length (magnitude) of a vector *)
    Definition cvlen {n} (v : cvec n) : R := sqrt (v ⋅ v).

    Notation "`| v |" := (cvlen v) : cvec_scope.

    Lemma cvdot_same_eq : forall {n} (v : cvec n), v ⋅ v = (cvlen v)².
    Proof. intros. unfold cvlen. rewrite Rsqr_sqrt; auto. apply cvdot_ge0. Qed.
    
    (** Length of a vector u is 1, iff the dot product of u and u is 1 *)
    Lemma cvlen1_iff_vdot1 : forall n (u : cvec n), `|u| = 1 <-> u ⋅ u = 1.
    Proof. intros. unfold cvlen. split; intros; hnf in *. ra. rewrite H. ra. Qed.

  End vlen.

  Notation "`| v |" := (cvlen v) : cvec_scope.


  (** ** unit vector *)
  Section vunit.

    (** A unit vector u is a vector whose length equals one.
      Here, we use the square of length instead of length directly,
      but this is reasonable with the proof of vunit_ok.
     *)
    Definition cvunit {n} (u : cvec n) : Prop := u ⋅ u = 1.

    (** Verify the definition is reasonable *)
    Lemma cvunit_ok : forall {n} (u : cvec n), cvunit u <-> `|u| = 1.
    Proof. intros. split; intros; apply cvlen1_iff_vdot1; auto. Qed.

    (** If column of a and column of b all are unit, 
        then column of (a * b) is also unit *)
    (*   a : mat 2 2 *)
    (* a1 : cvunit (mat2col a 0) *)
    (* a2 : cvunit (mat2col a 1) *)
    (* a3 : cvorthogonal (mat2col a 0) (mat2col a 1) *)
    (* b1 : cvunit (mat2col b 0) *)
    (* b2 : cvunit (mat2col b 1) *)
    (* b3 : cvorthogonal (mat2col b 0) (mat2col b 1) *)
    (* ============================ *)
    (* cvunit (mat2col (a * b) 0) *)


    (** Normalization of a non-zero vector v.
      That is, get a unit vector in the same directin as v. *)
    Definition cvnormalize {n} (v : cvec n) : cvec n := `|v| c* v.

  End vunit.


  (** ** Angle between two vectors *)
  Section vangle.

    (** Cosine of the angle between two vectors, only valid when both are nonzero *)
    Definition cvangle_cos {n} (v1 v2 : cvec n) : R := (v1 ⋅ v2) / (`|v1| * `|v2|).

    (** Two vectors are perpendicular. Note that zero vector is perp to any vectors *)
    Definition cvperp {n} (v1 v2 : cvec n) : Prop := v1 ⋅ v2 = 0.
    Infix "⟂" := cvperp ( at level 50).
    
  End vangle.


  (** ** Operations on vectors of 3-dimensional *)
  Section v3.

    (** *** Frame and point *)
    (** A point can be described by a coordinate vector, and the vector represents 
      the displacement of the point with respect to some reference coordinate 
      frame. We call it a bound vector since it cannot be freely moved. *)
    Section frame.

      (** A frame contains three orthogonal axes and a point known as the origin. *)
      Record frame := {
          Forigin : cvec 3;
          Fx : cvec 3;
          Fy : cvec 3;
          Fz : cvec 3;
        }.
      
      
    End frame.

    (** 空间直角坐标系的三个轴所在的单位向量 *)
    Definition v3i : cvec 3 := mk_cvec3 1 0 0.
    Definition v3j : cvec 3 := mk_cvec3 0 1 0.
    Definition v3k : cvec 3 := mk_cvec3 0 0 1.

    (** *** Dot product of two 3-dim vectors *)
    Section v3dot.
      
      Definition cv3dot (a b : cvec 3) :=
        let '(a1,a2,a3) := cv2t_3 a in 
        let '(b1,b2,b3) := cv2t_3 b in
        (a1*b1 + a2*b2 + a3*b3)%R.

      Lemma cvdot3_spec : forall v1 v2 : cvec 3, cv3dot v1 v2 = v1 ⋅ v2.
      Proof. intros. cbv. ring. Qed.

      (** 习题8.2第12题, page 23, 高等数学，第七版 *)
      (** 利用向量来证明不等式，并指出等号成立的条件 *)
      Theorem Rineq3 : forall a1 a2 a3 b1 b2 b3 : R,
          sqrt (a1² + a2² + a3²) * sqrt (b1² + b2² + b3²) >= Rabs (a1*b1 + a2*b2 + a3*b3).
      Proof.
        intros.
        pose (a := t2cv_3 (a1,a2,a3)).
        pose (b := t2cv_3 (b1,b2,b3)).
        pose (alen := cvlen a).
        pose (blen := cvlen b).
        replace (sqrt _) with alen; [| unfold alen; cbv; f_equal; ring].
        replace (sqrt _) with blen; [| unfold blen; cbv; f_equal; ring].
        replace (Rabs _) with (Rabs (a ⋅ b)); [| cbv; autorewrite with R; auto].
      Abort.

    End v3dot.


    (** *** Cross product (vector product) of two 3-dim vectors *)
    Section v3cross.

      Definition cv3cross (v1 v2 : cvec 3) : cvec 3 :=
        let '(a0,a1,a2) := cv2t_3 v1 in
        let '(b0,b1,b2) := cv2t_3 v2 in
        t2cv_3 (a1 * b2 - a2 * b1, a2 * b0 - a0 * b2, a0 * b1 - a1 * b0)%R.

      Infix "×" := cv3cross : cvec_scope.

      (** Example 4, page 19, 高等数学，第七版 *)
      Goal let a := t2cv_3 (2,1,-1) in
           let b := t2cv_3 (1,-1,2) in
           a × b == t2cv_3 (1,-5,-3).
      Proof. lva. Qed.

      (** Example 5, page 19, 高等数学，第七版 *)
      (** 根据三点坐标求三角形面积 *)
      Definition cv3_area_of_triangle (A B C : cvec 3) :=
        let AB := B - A in
        let AC := C - A in
        ((1/2) * `|AB × AC|)%R.

      (** Example 6, page 20, 高等数学，第七版 *)
      (** 刚体绕轴以角速度 ω 旋转，某点M（OM为向量r⃗）处的线速度v⃗，三者之间的关系*)
      Definition cv3_rotation_model (ω r v : cvec 3) := v = ω × r.
      
      Lemma cv3cross_self : forall v : cvec 3, v × v == cvec0.
      Proof. lva. Qed.

      Lemma cv3cross_anticomm : forall v1 v2 : cvec 3, v1 × v2 == -(v2 × v1).
      Proof. lva. Qed.

      Lemma cv3cross_add_distr_l : forall v1 v2 v3 : cvec 3,
          (v1 + v2) × v3 == (v1 × v3) + (v2 × v3).
      Proof. lva. Qed.
      
      Lemma cv3cross_add_distr_r : forall v1 v2 v3 : cvec 3,
          v1 × (v2 + v3) == (v1 × v2) + (v1 × v3).
      Proof. lva. Qed.

      Lemma cv3cross_cmul_assoc_l : forall (a : R) (v1 v2 : cvec 3),
          (a c* v1) × v2 == a c* (v1 × v2).
      Proof. lva. Qed.
      
      Lemma cv3cross_cmul_assoc_r : forall (a : R) (v1 v2 : cvec 3),
          v1 × (a c* v2) == a c* (v1 × v2).
      Proof. lva. Qed.

    End v3cross.
    Infix "×" := cv3cross : cvec_scope.

    (** *** skew symmetry matrix *)
    Section v3ssm.
      
      Definition cv3_skew_sym_mat (v : cvec 3) : smat 3 :=
        let '(x,y,z) := cv2t_3 v in
        (mk_mat_3_3
           0    (-z)  y
           z     0    (-x)
           (-y)  x     0)%R.
      Notation "`| v |ₓ" := (cv3_skew_sym_mat v).

      Lemma cv3cross_eq_ssm : forall (v1 v2 : cvec 3), v1 × v2 == `|v1|ₓ * v2.
      Proof. lva. Qed.
      
    End v3ssm.
    Notation "`| v |ₓ" := (cv3_skew_sym_mat v).

    
    (** *** Two vectors are parallel (or called coliner) *)
    Section vparallel.
      
      (** Note that zero vector is perp to any vectors *)
      Definition cvparallel (v1 v2 : cvec 3) : Prop := cvzero (v1 × v2).
      Infix "∥" := cvparallel ( at level 50).

    End vparallel.
    Infix "∥" := cvparallel ( at level 50).


    (** *** The triple scalar product (or called Mixed products of vectors) *)
    Section v3mixed.

      (** 几何意义：绝对值表示以向量a,b,c为棱的平行六面体的体积，另外若a,b,c组成右手系，
        则混合积的符号为正；若组成左手系，则符号为负。*)
      Definition cv3mixed (a b c : cvec 3) :=
        let m :=
          l2m 3 3 [[a$0; a$1; a$2]; [b$0; b$1; b$2]; [c$0; c$1; c$2]] in
        det3 m.

      (** A equivalent form *)
      Lemma cv3mixed_eq : forall a b c : cvec 3, cv3mixed a b c = (a × b) ⋅ c.
      Proof. intros [a] [b] [c]. cbv. ring. Qed.
      

      (** 若混合积≠0，则三向量可构成平行六面体，即三向量不共面，反之也成立。
        所以有如下结论：三向量共面的充要条件是混合积为零。*)
      Definition cv3coplanar (a b c : cvec 3) := cv3mixed a b c = 0.

      (** Example 7, page 22, 高等数学，第七版 *)
      (** 根据四顶点的坐标，求四面体的体积：四面体ABCD的体积等于AB,AC,AD为棱的平行六面体
        的体积的六分之一 *)
      Definition cv3_volume_of_tetrahedron (A B C D : cvec 3) :=
        let AB := B - A in
        let AC := C - A in
        let AD := D - A in
        ((1/6) * (cv3mixed AB AC AD))%R.

    End v3mixed.


  (* 
  
  (** Angle between two vectors *)
  Definition vangle3 (v0 v1 : cvec 3) : R := acos (m2t_1_1 (v0\T * v1)).

  (** The angle between (1,0,0) and (1,1,0) is 45 degree, i.e., π/4 *)
  Example vangle3_ex1 : vangle3 (l2v 3 [1;0;0]) (l2v _ [1;1;0]) = PI/4.
  Proof.
    compute.
    (*     Search acos. *)
  Abort. (* 暂不知哪里错了，要去查叉乘的意义 *)
  
  (** 根据两个向量来计算旋转轴 *)
  Definition rot_axis_by_twovec (v0 v1 : cvec 3) : cvec 3 :=
    let s : R := (vlen v0 * vlen v1)%R in
    s c* (vcross3 v0 v1).

 (* 谓词：两向量不共线（不平行的） *)
 (* Definition v3_non_colinear (v0 v1 : V3) : Prop :=
    v0 <> v1 /\ v0 <> (-v1)%M.
   *)
   *)
    
  End v3.


  (** ** vector parallel (old implementation) *)
  Section vparallel_old.

    (* (* Definition 1: v1 is k times to v2，or v2 is k times to v1 *) *)
    (* Definition vparallel_ver1 {n} (v1 v2 : cvec n) : Prop := *)
    (*   exists k, (v1 == k c* v2 \/ v2 == k c* v1). *)

    (* (* Definition 2: v1 is zero-vector, or v2 is zero-vector, or v1 is k times to v2 *) *)
    (* Definition vparallel_ver2 {n} (v1 v2 : cvec n) : Prop := *)
    (*   (vzero v1) \/ (vzero v2) \/ (exists k, v1 == k c* v2). *)

    (* (* These two definitions are same *) *)
    (* Lemma vparallel_ver1_eq_ver2 : forall {n} (v1 v2 : cvec n), *)
    (*     vparallel_ver1 v1 v2 <-> vparallel_ver2 v1 v2. *)
    (* Proof. *)
    (*   intros. unfold vparallel_ver1, vparallel_ver2. *)
    (*   unfold vzero, vnonzero, Vector.vzero. split; intros. *)
    (*   - destruct H. destruct H. *)
    (*     + right. right. exists x. auto. *)
    (*     + destruct (v1 ==? cvec0); auto. *)
    (*       destruct (v2 ==? cvec0); auto. *)
    (*       right. right. exists (1/x). rewrite H. *)
    (*       lma. apply cvec_eq_vcmul_imply_coef_neq0 in H; auto. *)
    (*   - destruct H as [H1 | [H2 | H3]]. *)
    (*     + exists 0. left. rewrite H1. rewrite vcmul_0_l. easy. *)
    (*     + exists 0. right. rewrite H2. rewrite vcmul_0_l. easy. *)
    (*     + destruct H3. exists x. left; auto. *)
    (* Qed. *)

    (* (** Vector parallel relation. Here, we use definition 2 *) *)
    (* Definition vparallel {n} (v0 v1 : cvec n) : Prop := *)
    (*   vparallel_ver2 v0 v1. *)

    (* Notation "v0 // v1" := (vparallel (v0) (v1)) (at level 70) : cvec_scope. *)

    (* (** vparallel is an equivalence relation *) *)

    (* Lemma vparallel_refl : forall {n} (v : cvec n), v // v. *)
    (* Proof. *)
    (*   intros. unfold vparallel,vparallel_ver2. right. right. exists 1. *)
    (*   rewrite vcmul_1_l. easy. *)
    (* Qed. *)

    (* Lemma vparallel_sym : forall {n} (v0 v1 : cvec n), v0 // v1 -> v1 // v0. *)
    (* Proof. *)
    (*   intros. unfold vparallel,vparallel_ver2 in *. *)
    (*   destruct (v0 ==? cvec0); auto. *)
    (*   destruct (v1 ==? cvec0); auto. *)
    (*   destruct H; auto. destruct H; auto. destruct H. *)
    (*   right. right. exists (1/x). rewrite H. *)
    (*   lma. apply cvec_eq_vcmul_imply_coef_neq0 in H; auto. *)
    (* Qed. *)

  (* (* Additionally, v1 need to be a non-zero vector. Because if v1 is zero vector,  *)
   (*    then v0//v1, v1//v2, but v0 and v2 needn't to be parallel. *) *)
    (* Lemma vparallel_trans : forall {n} (v0 v1 v2 : cvec n),  *)
    (*     vnonzero v1 -> v0 // v1 -> v1 // v2 -> v0 // v2. *)
    (* Proof. *)
    (*   intros. unfold vparallel, vparallel_ver2 in *. *)
    (*   destruct (v0 ==? cvec0), (v1 ==? cvec0), (v2 ==? cvec0); *)
    (*     auto; try easy. *)
    (*   destruct H0,H1; auto; try easy. *)
    (*   destruct H0,H1; auto; try easy. *)
    (*   destruct H0,H1. right. right. *)
    (*   exists (x*x0)%R. rewrite H0,H1. apply mcmul_assoc. *)
    (* Qed. *)

  (* (** If two non-zero vectors are parallel, then there is a unique k such that *)
   (*     they are k times relation *) *)
    (* Lemma vparallel_vnonezero_imply_unique_k : forall {n} (v1 v2 : cvec n), *)
    (*     vnonzero v1 -> vnonzero v2 -> v1 // v2 -> (exists ! k, v1 == k c* v2). *)
    (* Proof. *)
    (*   intros. *)
    (*   destruct H1; try easy. destruct H1; try easy. destruct H1. *)
    (*   exists x. split; auto. *)
    (*   intros. apply vcmul_vnonzero_eq_iff_unique_k with (v:=v2); auto. *)
    (*   rewrite <- H1,H2. easy. *)
    (* Qed. *)

  (* (** Given a non-zero vector v1 and another vector v2, *)
   (*     v1 is parallel to v2, iff, there is a unique k such that v2 is k times v1. *) *)
    (* Lemma vparallel_iff1 : forall {n} (v1 v2 : cvec n) (H : vnonzero v1), *)
    (*     (v1 // v2) <-> (exists ! k, v2 == k c* v1). *)
    (* Proof. *)
    (*   intros. split; intros. *)
    (*   - destruct (v2 ==? cvec0). *)
    (*     + exists 0. split. *)
    (*       * rewrite vcmul_0_l. auto. *)
    (*       * intros. rewrite m in H1. *)
    (*         apply symmetry in H1. apply vcmul_nonzero_eq_zero_imply_k0 in H1; auto. *)
    (*     + apply vparallel_vnonezero_imply_unique_k; auto. apply vparallel_sym; auto. *)
    (*   - destruct H0. destruct H0. apply vparallel_sym. right. right. exists x. auto. *)
    (* Qed. *)
    
  End vparallel_old.

  (* ======================================================================= *)
  (** ** Usage demo *)
  Section test.

    Let l1 := [1;2;3].
    Let v1 := l2cv 2 l1.
    (* Compute cv2l (@l2cv 3 l1). *)
    (* Compute cvdot v1 v1. *)

    Variable a1 a2 a3 : R.
    Let v2 := t2cv_3 (a1,a2,a3).
    (* Eval cbn in cv2l (cvmap Ropp v2). *)

  End test.

End ColVectorR.
