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

  三、额外内容
  1. {R^n, standard-inner-product} is called Euclidean space
     |v| = √(v,v)

 *)

Require Export VectorModule.
Require MatrixR.


(* ======================================================================= *)
(** * Vector theory come from common implementations *)

Module VectorTheoryR := RingVectorTheory RingElementTypeR.

(* Note: The VectorTheoryR will contain basic matrix theory, but we need more 
   matrix theory which have been developped in module MatrixR.
   So, we should use this sequence to import the extended matrix theory.
   I think the manual controlling work is a disadvantage of Module style
 *)
Export VectorTheoryR.
Export MatrixR.

Open Scope R_scope.
Open Scope mat_scope.
Open Scope rvec_scope.
Open Scope cvec_scope.


(* ======================================================================= *)
(** * Vector theory applied to this type *)


(* ==================================== *)
(** ** Kronecker delta function *)
Section kronecker.
  
  Definition kronecker_fun {A} {Azero Aone : A} (i j : nat) :=
    if (i =? j)%nat then Aone else Azero.

End kronecker.


(* ==================================== *)
(** ** Properties about vcmul *)
Section vcmul.

  (** If k times a non-zero vector equal to zero, then k must be zero *)
  Lemma cvcmul_nonzero_eq_zero_imply_k0 : forall {n} (v : cvec n) k,
      cvnonzero v -> k c* v == cvec0 -> (k == Azero)%A.
  Proof.
    (* idea:
    v <> 0 ==> ~(∀ i, v[i] = 0)
    k*v = 0 ==> ∀ i, k*v[i] = 0
    {k=0}+{k<>0} ==> k<>0  (if k=0, then qed)
    ---------------------------
    ∃ i, v[i] <> 0, then, k*v[i] <> 0, thus, contradict.
     *)
    intros. destruct v as [v]. cbv in *.
    destruct (k ==? Azero); auto.
    (* idea: from "~(∀ij(v i j = 0)" to "∃ij(v i j≠0)" *)
    (* Tips, a good practice of logic proposition *)
    assert (exists (ij:nat*nat), let (i,j) := ij in (i<n)%nat /\ (j<1)%nat /\ (v i j != Azero)%A).
    { clear k H0 n0.
      apply not_all_not_ex. intro.
      destruct H. intros. specialize (H0 (i,0)%nat). simpl in H0.
      apply not_and_or in H0. destruct H0; try easy.
      apply not_and_or in H0. destruct H0; try easy; try lia.
      apply NNPP in H0.
      assert (j = 0%nat) by lia. subst. auto. }
    destruct H1. destruct x as (i,j). destruct H1. destruct H2.
    specialize (H0 i j H1 H2).
    (* 注意，这里要求一个无零因子环，因此暂时只能在 Real 上证明 *)
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
    cbv in n0. ra.
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
End vcmul.


(* ==================================== *)
(** ** Two vectors are parallel (or called collinear) *)
Section cvparallel.

  (* 注意：这个定义可能还需改进，因为有平行、反向平行两种情况，以及v1和v2的区分等问题 *)
  (** Two vectors are parallel, iff their components have k-times relation *)
  Definition cvparallel {n} (v1 v2 : cvec n) : Prop :=
    exists k : R, k <> 0 /\ k c* v1 == v2.

  Infix "∥" := cvparallel (at level 50) : cvec_scope.

  (** vparallel is an equivalence relation *)

  Lemma cvparallel_refl : forall {n} (v : cvec n), v ∥ v.
  Proof. intros. exists 1. split; auto. apply cvcmul_1_l. Qed.

  Lemma cvparallel_sym : forall {n} (v0 v1 : cvec n), v0 ∥ v1 -> v1 ∥ v0.
  Proof.
    intros. destruct H as [k [H1 H2]]. exists (1/k). split.
    (* ToDo: 提高R的自动化程度 *)
    - apply Rinv_neq_0_compat in H1. ra.
    - rewrite <- H2. rewrite cvcmul_assoc.
      unfold Rdiv. autorewrite with R. rewrite Rinv_l; auto. apply cvcmul_1_l.
  Qed.

  Lemma cvparallel_trans : forall {n} (v0 v1 v2 : cvec n), v0 ∥ v1 -> v1 ∥ v2 -> v0 ∥ v2.
  Proof.
    intros. destruct H as [k1 [H1 H2]], H0 as [k2 [H3 H4]].
    exists (k2 * k1)%R. split; auto.
    rewrite <- cvcmul_assoc. rewrite H2. auto.
  Qed.

  (** Zero vector is parallel to any other vectors *)
  (* Lemma cvparallel_zero_l : forall {n} (v1 v2 : cvec n), cvzero v1 -> v1 ∥ v2. *)
  (* Proof. intros. exists 0. *)

(* (** If two non-zero vectors are parallel, then there is a unique k such that *)
 (*     they are k times relation *) *)
  (* Lemma cvparallel_vnonezero_imply_unique_k : *)
  (*   forall {n} (v1 v2 : cvec n) (H1 : cvnonzero v1) (H2 : cvnonzero v2), *)
  (*     v1 ∥ v2 -> (exists ! k, k c* v1 == v2). *)
  (* Proof. *)
  (*   intros. destruct H1 as [x [H1 H2]]. *)
  (*   exists x. split; auto. *)
  (*   intros. apply cvcmul_vnonzero_eq_iff_unique_k with (v:=v1); auto. *)
  (*   rewrite H2,H3. easy. *)
  (* Qed. *)

(** A non-zero vector v1 is parallel to any other vector v2,
        iff there is a unique k such that v2 is k times v1. *)
  (* Lemma cvparallel_iff1 : forall {n} (v1 v2 : cvec n), *)
  (*     (cvnonzero v1 /\ (v1 ∥ v2)) <-> (exists ! k, v2 == k c* v1). *)
  (* Proof. *)
  (*   intros. split; intros. *)
  (*   - destruct (v2 ==? cvec0). *)
  (*     + exists 0. split. *)
  (*       * rewrite vcmul_0_l. auto. *)
  (*       * intros. rewrite m in H1. *)
  (*         apply symmetry in H1. apply cvcmul_nonzero_eq_zero_imply_k0 in H1; auto. *)
  (*     + apply cvparallel_vnonezero_imply_unique_k; auto. apply vparallel_sym; auto. *)
  (*   - destruct H0. destruct H0. apply vparallel_sym. right. right. exists x. auto. *)
  (* Qed. *)


End cvparallel.
Infix "∥" := cvparallel (at level 50) : cvec_scope.


(* ==================================== *)
(** ** Propertities for vector dot product *)
Section vdot.

  (** 0 <= <v,v> *)
  Lemma cvdot_ge0 : forall {n} (v : cvec n), 0 <= <v,v>.
  Proof.
    intros. cvec2fun. unfold cvdot,Vector.cvdot. simpl.
    revert v. induction n; intros; simpl; autounfold with A; ra.
  Qed.

  (** <v,v> = 0 <-> v = 0 *)
  Lemma cvdot0_iff_0 : forall {n} (v : cvec n), <v,v> = 0 <-> v == cvec0.
  Proof.
    intros. unfold cvdot, Vector.cvdot. cvec2fun.
    split; intros.
    - revert v H. induction n; intros; simpl in *. lma.
      apply Rplus_eq_R0 in H; ra.
      + destruct H. apply IHn in H. apply Rsqr_eq_0 in H0.
        apply seq2eq_Sr. split; auto.
        hnf; simpl. intros. assert (i = 0%nat) by lia. subst; auto.
      + apply seqsum_ge0. intros. ra.
    - hnf in H; simpl in *.
      apply seqsum_seq0. intros. apply Rsqr_eq0_if0. apply H; auto.
  Qed.

  (** <row(m1,i), col(m2,j)> = (m1 * m2)[i,j] *)
  Lemma cvdot_row_col_eq : forall {r c s} (m : mat r c) (n : mat c s) i j,
      (i < r)%nat -> (j < c)%nat ->
      cvdot ((mrow m i)\T) (mcol n j) = (m * n) $ i $ j.
  Admitted.

  (** <col(m1,i), col(m2,j)> = (m1\T * m2)[i,j] *)
  Lemma cvdot_col_col : forall {n} (m : smat n) i j,
      (i < n)%nat -> (j < n)%nat ->
      cvdot (mcol m i) (mcol m j) = (m\T * m) $ i $ j.
  Admitted.

  (** <row(m1,i), row(m2,j)> = (m1 * m2\T)[i,j] *)
  Lemma cvdot_row_row : forall {n} (m : smat n) i j,
      (i < n)%nat -> (j < n)%nat ->
      rvdot (mrow m i) (mrow m j) = (m * m\T) $ i $ j.
  Admitted.

  
End vdot.


(* ==================================== *)
(** ** Length of a vector *)
Section vlen.

  (** Length (magnitude) of a vector, is derived by inner-product *)
  Definition cvlen {n} (v : cvec n) : R := sqrt (<v,v>).

  Notation "|| v ||" := (cvlen v) : cvec_scope.

  #[export] Instance cvlen_mor {n} : Proper (meq ==> eq) (@cvlen n).
  Proof.
    simp_proper. intros. unfold cvlen. f_equiv. rewrite H. auto.
  Qed.

  (** Square of length equal to dot-product *)
  Lemma cvlen_sqr : forall {n} (v : cvec n), ||v||² = <v,v>.
  Proof. intros. unfold cvlen. rewrite Rsqr_sqrt; auto. apply cvdot_ge0. Qed.

  (** 0 <= ||v|| *)
  Lemma cvlen_ge0 : forall {n} (v : cvec n), 0 <= ||v||.
  Proof. intros. unfold cvlen. ra. Qed.

  (** Length equal iff dot-product equal *)
  Lemma cvlen_eq_iff_dot_eq : forall {n} (u v : cvec n), ||u|| = ||v|| <-> <u,u> = <v,v>.
  Proof.
    intros. rewrite <- !cvlen_sqr. split; intros.
    - apply Rsqr_eq_asb_1. rewrite H. auto.
    - apply Rsqr_eq_abs_0 in H. rewrite !Rabs_right in H; auto.
      all: apply Rle_ge; apply cvlen_ge0.
  Qed.

  (** ||v|| = 0 <-> v = 0 *)
  Lemma cvlen_eq0_iff_eq0 : forall {n} (v : cvec n), ||v|| = 0 <-> v == cvec0.
  Proof.
    intros. unfold cvlen. split; intros.
    - apply cvdot0_iff_0. apply sqrt_eq_0 in H. auto. apply cvdot_ge0.
    - apply cvdot0_iff_0 in H. rewrite H. ra.
  Qed.

  (** ||v|| <> 0 <-> v <> 0 *)
  Lemma cvlen_neq0_iff_neq0 : forall {n} (v : cvec n), ||v|| <> 0 <-> v != cvec0.
  Proof.
    intros. split; intros; intro.
    - apply cvlen_eq0_iff_eq0 in H0. easy.
    - apply cvlen_eq0_iff_eq0 in H0. easy.
  Qed.

  (** Length of a vector u is 1, iff the dot product of u and u is 1 *)
  Lemma cvlen_eq1_iff_vdot1 : forall {n} (u : cvec n), ||u|| = 1 <-> <u,u> = 1.
  Proof. intros. unfold cvlen. split; intros; hnf in *. ra. rewrite H. ra. Qed.

  (** ||k c* v|| = |k| * ||v|| *)
  Lemma cvlen_cmul : forall n (v : cvec n) k, ||k c* v|| = (|k| * ||v||)%R.
  Proof.
  Admitted.

  (** ||u + v|| <= ||u|| + ||v|| *)
  Lemma cvlen_add_ineq : forall {n} (u v : cvec n), ||(u + v)|| <= ||u|| + ||v||.
  Admitted.

  (** |<u,v>| <= ||u|| * ||v|| *)
  Lemma cvlen_mul_ineq : forall {n} (u v : cvec n), |<u,v>| <= ||u|| * ||v||.
  Admitted.

End vlen.
Notation "|| v ||" := (cvlen v) : cvec_scope.


(* ==================================== *)
(** ** Unit vector *)
Section vunit.

  (** A unit vector u is a vector whose length equals one.
      Here, we use the square of length instead of length directly,
      but this is reasonable with the proof of vunit_ok.
   *)
  Definition cvunit {n} (u : cvec n) : Prop := <u,u> = 1.

  (** (bool version) *)
  Definition cvunitb {n} (u : cvec n) : bool := (<u,u> =? 1)%R.

  (** Convenient property *)
  Lemma cvlen_cvunit : forall {n} (u : cvec n), cvunit u -> ||u|| = 1.
  Proof. intros. apply cvlen_eq1_iff_vdot1. auto. Qed.

  (** Verify the definition is reasonable *)
  Lemma cvunit_spec : forall {n} (u : cvec n), cvunit u <-> ||u|| = 1.
  Proof. intros. split; intros; apply cvlen_eq1_iff_vdot1; auto. Qed.

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
End vunit.


(* ==================================== *)
(** ** vector normalization *)
Section vnormalize.

  (** Normalization of a non-zero vector v.
    That is, get a unit vector in the same directin as v. *)
  Definition cvnormalize {n} (v : cvec n) : cvec n := (1/||v||) c* v.

  #[export] Instance cvnormalize_mor {n} : Proper (meq ==> meq) (@cvnormalize n).
  Proof. simp_proper. intros. unfold cvnormalize. rewrite H. easy. Qed.

  Lemma cvnormalize_len1 : forall {n} (v : cvec n),
      cvnonzero v -> ||cvnormalize v|| = 1.
  Proof.
    (* v̂ = v/|v|, |v̂| = sqrt (v/|v| ⋅ v/|v|) = sqrt ((v⋅v) / (|v|*|v|))
     = sqrt(v⋅v) / |v| = |v| / |v| = 1 *)
    intros. unfold cvnormalize. unfold cvlen.
    rewrite !cvdot_vcmul_l, !cvdot_vcmul_r. rewrite <- cvlen_sqr.
    remember (||v||). autounfold with A. autorewrite with R.
    apply sqrt_eq1_imply_eq1_rev.
    assert (|r| = r). { pose proof (cvlen_ge0 v). subst. ra. }
    rewrite H0. cbv. field. subst. apply cvlen_neq0_iff_neq0; auto.
  Qed.

  (** Keep the same direction as the original vector *)
  Lemma cvnormalize_direction : forall {n} (v : cvec n),
      (cvnormalize v) ∥ v.
  Proof.
  Admitted.

  (* Variable n : nat. *)
  (* Variable v : cvec n. *)
  (* Hypotheses H : cvnonzero v. *)
  (* Check cvnormalize_direction v. *)
  (* Check (cvnormalize_len1 v H) /\ True. : Prop. *)
  Lemma cvnormalize_spec : forall {n} (v : cvec n),
      (cvnonzero v -> ||cvnormalize v|| = 1) /\ ((cvnormalize v) ∥ v).
  Proof. intros. split. apply cvnormalize_len1. apply cvnormalize_direction. Qed.

  (** 单位化后的非零向量都是单位向量 *)
  Lemma cvnormalize_unit : forall {n} (v : cvec n),
      cvnonzero v -> cvunit (cvnormalize v).
  Proof. intros. apply cvunit_spec. apply cvnormalize_len1; auto. Qed.

End vnormalize.


(* ==================================== *)
(** ** Angle between two vectors *)
Section vangle.

  (** The angle from vector v1 to vector v2, is derived from the inner-product *)
  Definition cvangle {n} (v1 v2 : cvec n) : R :=
    let v1' := cvnormalize v1 in
    let v2' := cvnormalize v2 in
    acos (<v1', v2'>).
  
  Infix "∠" := cvangle (at level 60) : cvec_scope.

  (** Angle is commutative *)
  Lemma cvangle_comm : forall {n} (v1 v2 : cvec n), v1 ∠ v2 = v2 ∠ v1.
  Proof. intros. unfold cvangle. rewrite cvdot_comm. auto. Qed.
  
  (* (** Angle equal iff dot-product equal *) *)
  (* Lemma cvangle_eq_if_dot_eq : forall {n} (u1 u2 v1 v2 : cvec n), *)
  (*     <u1,v1> = <u2,v2> -> u1 ∠ v1 = u2 ∠ v2. *)
  (* Proof. *)
  (*   intros. unfold cvangle. f_equal. *)
  (* Qed. *)

  (** The angle between (1,0,0) and (1,1,0) is 45 degree, i.e., π/4 *)
  Example cvangle_ex1 : (@l2cv 3 [1;0;0]) ∠ (l2cv [1;1;0]) = PI/4.
  Proof.
    compute.
    (* Todo: 含有 sqrt, acos, PI 等，如何证明此类等式？ *)
  Abort.

  (** The law of cosine *)
  Axiom cosine_law : forall {n} (a b : cvec n),
      ((||(a - b)%CV||)² = ||a||² + ||b||² - 2 * ||a|| * ||b|| * cos (cvangle a b))%R.

  (** The relation between dot product and the cosine of angle in 2D *)
  Theorem cvdot_eq_cos_angle : forall {n} (a b : cvec n),
      <a,b> = (||a|| * ||b|| * cos (cvangle a b))%R.
  Proof.
    intros.
    (* construct another form of "cosine_law" *)
    assert (||(a-b)%CV||² = ||a||² + ||b||² - 2 * <a,b>)%R.
    { rewrite !cvlen_sqr.  unfold cvsub.
      rewrite !cvdot_vadd_distr_l, !cvdot_vadd_distr_r.
      rewrite !cvdot_vopp_l, !cvdot_vopp_r. rewrite (cvdot_comm b a).
      autounfold with A; ring. }
    pose proof (cosine_law a b). ra.
  Qed.

End vangle.
Infix "∠" := cvangle (at level 60) : cvec_scope.


(* ==================================== *)
(** ** About {cvdot, cvunit, cvangle, cvnormalize} *)
Section cvdot_cvunit_cvangle_cvnormalize.
  
  (** 单位向量的点积介于[-1,1] *)
  Lemma cvdot_unit_bound : forall {n} (u v : cvec n),
      cvunit u -> cvunit v -> -1 <= <u,v> <= 1.
  Proof.
    intros. rewrite cvdot_eq_cos_angle.
    rewrite ?cvlen_cvunit; auto.
    match goal with |- context [cos ?r] => remember r as a end.
    pose proof (COS_bound a). lra.
  Qed.

  (** 单位化后的非零向量的点积介于 [-1,1] *)
  Lemma cvdot_vnormalize_bound : forall {n} (u v : cvec n),
      cvnonzero u -> cvnonzero v ->
      -1 <= <cvnormalize u, cvnormalize v> <= 1.
  Proof. intros. apply cvdot_unit_bound; apply cvnormalize_unit; auto. Qed.

End cvdot_cvunit_cvangle_cvnormalize.



(* ==================================== *)
(** ** Projection component of a vector onto another *)
Section cvproj.

  (** The projection component of a onto b *)
  Definition cvproj {n} (a b : cvec n) : cvec n := (<a,b> / <b,b>) c* b.

  (* (** The scalar projection of a on b is a simple triangle relation *) *)
  (* Lemma cvsproj_spec : forall {n} (a b : cvec n), cvsproj a b == `|a| * cvangle. *)
End cvproj.


(* ==================================== *)
(** ** Perpendicular component of a vector respect to another *)
Section cvperp.

  (** The perpendicular component of a respect to b *)
  Definition cvperp {n} (a b : cvec n) : cvec n := a - cvproj a b.

End cvperp.


(* ==================================== *)
(** ** Orthogonal vectors 正交的两个向量 *)
Section cvorthogonal.

  (** Two vectors, x and y, in an inner product space V, are orthogonal if their 
    inner-product <x,y> is zero, and the relationship is denoted x ⟂ y. *)

  (** Two real column-vectors are orthogonal (also called perpendicular) *)
  Definition cvorthogonal {n} (v1 v2 : cvec n) : Prop := <v1,v2> = 0.

  (** Bool version to determine if two vectors are orthogonal *)
  Definition cvorthogonalb {n} (v1 v2 : cvec n) : bool := (<v1,v2> =? 0)%R.
  Infix "⟂" := cvorthogonal ( at level 50).

  (** cvproj ⟂ cvperp *)
  Lemma cvorthogonal_proj_perp : forall {n} (u v : cvec n), cvproj u v ⟂ cvperp u v.
  Proof.
    intros. hnf. unfold cvproj,cvperp.
    (* 以下证明思路明显是错误的，不可能所有元素都是0 *)
    apply seqsum_seq0.
    intros.
    cvec2fun. simpl.
    unfold cvdot, Vector.cvdot. simpl.
    autorewrite with R.
    remember (seqsum (fun i0 : nat => v i0 0%nat * v i0 0%nat) n)%A as r1.
    remember (seqsum (fun i0 : nat => u i0 0%nat * v i0 0%nat) n)%A as r2.
  Abort.
End cvorthogonal.
Infix "⟂" := cvorthogonal ( at level 50).


(* ==================================== *)
(** ** Orthogonal set 正交向量组（集） *)
Section cvorthogonalset.

  (** A set of vectors in an inner product space is called pairwise orthogonal if 
    each pairing of them is orthogonal. Such a set is called an orthogonal set.
    Note: each pair means {(vi,vj)|i≠j}  *)
  Definition cvorthogonalset {r c} (m : mat r c) : Prop :=
    forall j1 j2, (j1 < c)%nat -> (j2 < c)%nat -> (j1 <> j2) -> <mcol m j1, mcol m j2> = Azero.

  (** (bool version) *)
  Definition cvorthogonalsetb {r c} (m : mat r c) : bool :=
    (* two column vectors is orthogonal *)
    let orth (i j : nat) : bool := (<mcol m i, mcol m j> =? Azero)%R in
    (* remain column indexes after this column *)
    let cids (i : nat) : list nat := seq (S i) (c - S i) in
    (* the column is orthogonal to right-side remain columns *)
    let allcols (j : nat) : bool := and_blist (map (fun k => orth j k) (cids j)) in
    (* all columns is mutually orthogonal (Note orthogonal is commutative) *)
    and_blist (map (fun j => allcols j) (seq 0 c)).

  Lemma cvorthogonalsetb_true_iff : forall {r c} (m : mat r c),
      cvorthogonalsetb m <-> cvorthogonalset m.
  Admitted.

  Example cvorthogonalset_ex1 :
    cvorthogonalset (@l2m 3 3 [[1;1;1];[0;sqrt 2; -(sqrt 2)];[-1;1;1]])%A.
  Proof.
    apply cvorthogonalsetb_true_iff. cbv.
    (** Auto solve equality contatin "Req_EM_T" *)
    repeat
      match goal with
      | |- context[ Req_EM_T ?a ?b] => destruct Req_EM_T; try lra
      end.
    autorewrite with R sqrt in *; ra.
  Qed.
End cvorthogonalset.


(* ==================================== *)
(** ** Orthonormal vectors 标准正交的向量组 *)
Section mcolsOrthonormal.

  (** All (different) column-vectors of a matrix are orthogonal each other.
    For example: [v1;v2;v3] => v1⟂v2 && v1⟂v3 && v2⟂v3. *)
  Definition mcolsOrthogonal {r c} (m : mat r c) : Prop :=
    forall j1 j2, (j1 < c)%nat -> (j2 < c)%nat -> j1 <> j2 -> mcol m j1 ⟂ mcol m j2.

  (** bool version *)
  Definition mcolsOrthogonalb {r c} (m : mat r c) : bool :=
    let is_orth (i j : nat) : bool := (<mcol m i, mcol m j> =? Azero)%R in
    let cids (i : nat) : list nat := seq (S i) (c - S i) in
    let chk_col (j : nat) : bool := and_blist (map (fun k => is_orth j k) (cids j)) in
    and_blist (map (fun j => chk_col j) (seq 0 c)).

  Lemma mcolsOrthogonalb_spec : forall {r c} (m : mat r c),
      mcolsOrthogonalb m <-> mcolsOrthogonal m.
  Proof.
  Admitted.

  Section test.
    Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : R.
    Let m1 : mat 1 3 := l2m [[a11;a12;a13];[a21;a22;a23]].
    Let m2 : mat 3 1 := l2m [[a11;a12];[a21;a22];[a31;a32]].

    (* Compute mcolsOrthogonalb m1. *)
    (* Compute mcolsOrthogonalb m2. (* because only one column, needn't be check *) *)
  End test.

  (** All column-vectors of a matrix are unit vector.
    For example: [v1;v2;v3] => unit v1 && unit v2 && unit v3 *)
  Definition mcolsUnit {r c} (m : mat r c) : Prop :=
    forall j, (j < c)%nat -> cvunit (mcol m j).

  (** bool version *)
  Definition mcolsUnitb {r c} (m : mat r c) : bool :=
    and_blist (map (fun i => cvunitb (mcol m i)) (seq 0 c)).

  Lemma mcolsUnitb_spec : forall {r c} (m : mat r c),
      mcolsUnitb m <-> mcolsUnit m.
  Proof.
  Admitted.

  (** The columns of a matrix is orthogomal *)
  Definition mcolsOrthonormal {r c} (m : mat r c) : Prop :=
    mcolsOrthogonal m /\ mcolsUnit m.

End mcolsOrthonormal.


(* ==================================== *)
(** ** Orthogonal matrix *)
Section morthogonal.

  (** matrix m is orthogonal <-> columns of m are orthogomal *)
  Lemma morthogonal_iff_mcolsOrthonormal : forall {n} (m : smat n),
      morthogonal m <-> mcolsOrthonormal m.
  Proof.
    intros.
    unfold morthogonal,mcolsOrthonormal.
    unfold mcolsOrthogonal, mcolsUnit.
    unfold cvorthogonal, cvunit.
    split; intros.
    - split; intros.
      + rewrite cvdot_col_col; auto. rewrite H; auto. rewrite mnth_mat1_diff; auto.
      + rewrite cvdot_col_col; auto. rewrite H; auto. rewrite mnth_mat1_same; auto.
    - destruct H as [H1 H2]. hnf. intros. rewrite <- cvdot_col_col; auto.
      bdestruct (i =? j)%nat.
      + subst. rewrite mnth_mat1_same; auto. apply H2; auto.
      + rewrite mnth_mat1_diff; auto. apply H1; auto.
  Qed.

  (** Transformation by orthogonal matrix will keep inner-product *)
  Theorem morthogonal_keep_dot : forall {n} (m : smat n) (v1 v2 : cvec n),
      morthogonal m -> <m * v1, m * v2> = <v1, v2>.
  Proof.
    intros.
    rewrite cvdot_eq_mul_trans.
    unfold scalar_of_mat, Matrix.scalar_of_mat.
    rewrite (m2f_mor _ (v1\T * v2)); auto.
    rewrite mtrans_mmul. rewrite mmul_assoc. rewrite <- (mmul_assoc _ m).
    rewrite morthogonal_iff_mul_trans_l in H. rewrite H.
    rewrite mmul_1_l. easy.
  Qed.

  (** Transformation by orthogonal matrix will keep length. *)
  Corollary morthogonal_keep_length : forall {n} (m : smat n) (v : cvec n),
      morthogonal m -> ||m * v|| = ||v||.
  Proof.
    intros. rewrite cvlen_eq_iff_dot_eq. apply morthogonal_keep_dot. auto.
  Qed.

  (** Transformation by orthogonal matrix will keep normalization. *)
  Corollary morthogonal_keep_normalize : forall {n} (m : smat n) (v : cvec n),
      morthogonal m -> cvnormalize (m * v) == m * (cvnormalize v).
  Proof.
    intros. unfold cvnormalize.
    rewrite morthogonal_keep_length; auto. apply mcmul_mmul_assoc_r.
  Qed.

  (** Transformation by orthogonal matrix will keep angle. *)
  Corollary morthogonal_keep_angle : forall {n} (m : smat n) (v1 v2 : cvec n),
      morthogonal m -> m * v1 ∠ m * v2 = v1 ∠ v2.
  Proof.
    intros. unfold cvangle. f_equal. rewrite !morthogonal_keep_normalize; auto.
    rewrite morthogonal_keep_dot; auto.
  Qed.

  (** 由于正交矩阵可保持变换向量的长度和角度，它可保持坐标系的整体结构不变。
    因此，正交矩阵仅可用于旋转变换和反射变换或二者的组合变换。
    当正交矩阵的行列式为1，表示一个旋转，行列式为-1，表示一个反射。*)
End morthogonal.


(* ==================================== *)
(** ** Exercise in textbook *)
Section exercise.
  (** 习题8.2第12题, page 23, 高等数学，第七版 *)
  (** 利用向量来证明不等式，并指出等号成立的条件 *)
  Theorem Rineq3 : forall a1 a2 a3 b1 b2 b3 : R,
      sqrt (a1² + a2² + a3²) * sqrt (b1² + b2² + b3²) >= |a1*b1 + a2*b2 + a3*b3|.
  Proof.
    intros.
    pose (a := t2cv_3 (a1,a2,a3)).
    pose (b := t2cv_3 (b1,b2,b3)).
    pose (alen := cvlen a).
    pose (blen := cvlen b).
    replace (sqrt _) with alen; [| unfold alen; cbv; f_equal; ring].
    replace (sqrt _) with blen; [| unfold blen; cbv; f_equal; ring].
    replace (Rabs _) with (|<a,b>|); [| cbv; autorewrite with R; auto].
  Abort.

End exercise.


(* ======================================================================= *)
(** * Usage demo *)
Section test.
  Let l1 := [1;2;3].
  Let v1 := @l2rv 2 l1.
  Let v2 := @l2cv 2 l1.
  (* Compute rv2l v1. *)
  (* Compute cv2l v2. *)


  Variable a1 a2 a3 : A.
  Variable f : A -> A.
  Let v3 := t2rv_3 (a1,a2,a3).
  Let v4 := t2cv_3 (a1,a2,a3).
  (* Compute rv2l (rvmap v3 f). *)
  (* Compute cv2l (cvmap v4 f). *)
  
End test.
