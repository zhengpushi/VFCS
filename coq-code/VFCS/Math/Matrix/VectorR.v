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
  (2) 如果∠a,b = 0 or π，则称它们平行，记做 a//b。
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
  
  Definition kronecker_fun {T} {T0 T1 : T} (i j : nat) :=
    if (i =? j)%nat then T1 else T0.

End kronecker.


(* ==================================== *)
(** ** Properties about vcmul *)
Section vcmul.

  (** cvnonzero v -> k <> 0 -> cvnonzero (k c* v). *)
  Lemma cvcmul_cvnonzero : forall {n} (v : cvec n) (k : R),
      cvnonzero v -> k <> 0 -> cvnonzero (k c* v).
  Proof.
    Admitted.

  (** If k times a non-zero vector equal to zero, then k must be zero *)
  Lemma cvcmul_nonzero_eq_zero_imply_k0 : forall {n} (v : cvec n) k,
      cvnonzero v -> k c* v == cvec0 -> (k == T0)%T.
  Proof.
    (* idea:
    v <> 0 ==> ~(∀ i, v[i] = 0)
    k*v = 0 ==> ∀ i, k*v[i] = 0
    {k=0}+{k<>0} ==> k<>0  (if k=0, then qed)
    ---------------------------
    ∃ i, v[i] <> 0, then, k*v[i] <> 0, thus, contradict.
     *)
    intros. destruct v as [v]. cbv in *.
    destruct (k ==? T0); auto.
    (* idea: from "~(∀ij(v i j = 0)" to "∃ij(v i j≠0)" *)
    (* Tips, a good practice of logic proposition *)
    assert (exists (ij:nat*nat), let (i,j) := ij in (i<n)%nat /\ (j<1)%nat /\ (v i j != T0)%T).
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
Section cvpara.

  (* 注意：这个定义可能还需改进，因为有平行、反向平行两种情况，以及v1和v2的区分等问题 *)
  (** Two vectors are parallel, iff their components have k-times relation *)
  Definition cvpara {n} (v1 v2 : cvec n) : Prop :=
    exists k : R, k <> 0 /\ k c* v1 == v2.

  Infix "//" := cvpara (at level 50) : cvec_scope.

  (** vparallel is an equivalence relation *)

  Lemma cvpara_refl : forall {n} (v : cvec n), v // v.
  Proof. intros. exists 1. split; auto. apply cvcmul_1_l. Qed.

  Lemma cvpara_sym : forall {n} (v0 v1 : cvec n), v0 // v1 -> v1 // v0.
  Proof.
    intros. destruct H as [k [H1 H2]]. exists (1/k). split.
    (* ToDo: 提高R的自动化程度 *)
    - apply Rinv_neq_0_compat in H1. ra.
    - rewrite <- H2. rewrite cvcmul_assoc.
      unfold Rdiv. autorewrite with R. rewrite Rinv_l; auto. apply cvcmul_1_l.
  Qed.

  Lemma cvpara_trans : forall {n} (v0 v1 v2 : cvec n), v0 // v1 -> v1 // v2 -> v0 // v2.
  Proof.
    intros. destruct H as [k1 [H1 H2]], H0 as [k2 [H3 H4]].
    exists (k2 * k1)%R. split; auto.
    rewrite <- cvcmul_assoc. rewrite H2. auto.
  Qed.

  (** v1 // v2 -> (a c* v1) // v2 *)
  Lemma cvcmul_cvpara_l : forall {n} (v1 v2 : cvec n) (a : R),
      v1 // v2 -> a <> 0 -> (a c* v1) // v2.
  Proof.
    intros. unfold cvpara in *. destruct H as [k [H1 H2]].
    exists (k/a). split.
    - unfold Rdiv.
      apply Rmult_integral_contrapositive_currified; auto.
      apply Rinv_neq_0_compat; auto.
    - rewrite cvcmul_assoc.
      replace (k / a * a)%T with k; auto. cbv. field; auto.
  Qed.

  (** v1 // v2 -> v1 // (a c* v2) *)
  Lemma cvcmul_cvpara_r : forall {n} (v1 v2 : cvec n) (a : R),
      v1 // v2 -> a <> 0 -> v1 // (a c* v2).
  Proof.
    intros. apply cvpara_sym. apply cvcmul_cvpara_l; auto.
    apply cvpara_sym; auto.
  Qed.

  (** Zero vector is parallel to any other vectors. *)
  Lemma cvpara_0_l : forall {n} (v1 v2 : cvec n), cvzero v1 -> v1 // v2.
  Proof.
    intros. exists 0.
    (* Note, it is not true, because the definition of cvpara.  *)
  Abort.


(* (** If two non-zero vectors are parallel, then there is a unique k such that *)
 (*     they are k times relation *) *)
  (* Lemma cvpara_vnonezero_imply_unique_k : *)
  (*   forall {n} (v1 v2 : cvec n) (H1 : cvnonzero v1) (H2 : cvnonzero v2), *)
  (*     v1 // v2 -> (exists ! k, k c* v1 == v2). *)
  (* Proof. *)
  (*   intros. destruct H1 as [x [H1 H2]]. *)
  (*   exists x. split; auto. *)
  (*   intros. apply cvcmul_vnonzero_eq_iff_unique_k with (v:=v1); auto. *)
  (*   rewrite H2,H3. easy. *)
  (* Qed. *)

(** A non-zero vector v1 is parallel to any other vector v2,
        iff there is a unique k such that v2 is k times v1. *)
  (* Lemma cvpara_iff1 : forall {n} (v1 v2 : cvec n), *)
  (*     (cvnonzero v1 /\ (v1 // v2)) <-> (exists ! k, v2 == k c* v1). *)
  (* Proof. *)
  (*   intros. split; intros. *)
  (*   - destruct (v2 ==? cvec0). *)
  (*     + exists 0. split. *)
  (*       * rewrite vcmul_0_l. auto. *)
  (*       * intros. rewrite m in H1. *)
  (*         apply symmetry in H1. apply cvcmul_nonzero_eq_zero_imply_k0 in H1; auto. *)
  (*     + apply cvpara_vnonezero_imply_unique_k; auto. apply vparallel_sym; auto. *)
  (*   - destruct H0. destruct H0. apply vparallel_sym. right. right. exists x. auto. *)
  (* Qed. *)


End cvpara.
Infix "//" := cvpara (at level 50) : cvec_scope.


(* ==================================== *)
(** ** Propertities for vector dot product *)
Section vdot.

  (** 0 <= <v,v> *)
  Lemma cvdot_ge0 : forall {n} (v : cvec n), 0 <= <v,v>.
  Proof.
    intros. cvec2fun. unfold cvdot,Vector.cvdot. simpl.
    revert v. induction n; intros; simpl; autounfold with T; ra.
  Qed.

  (** <v,v> = 0 <-> v = 0 *)
  Lemma cvdot_same_eq0 : forall {n} (v : cvec n), <v,v> = 0 <-> v == cvec0.
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
      apply seqsum_eq0. intros. apply Rsqr_eq0_if0. apply H; auto.
  Qed.

  (** Another proof. *)
  Lemma cvdot_same_eq0' : forall {n} (v : cvec n), <v,v> = 0 <-> v == cvec0.
  Proof.
    intros. unfold cvdot. split; intros.
    - hnf; intros. apply (seqsum_eq0_imply_seq0) with (i:=i) in H; auto; ra.
      cvec2fun; cbv in H.
      assert (j = 0)%nat by nia.
      assert (v i 0%nat = 0); ra. subst. easy.
    - rewrite H. rewrite cvdot_0_l. auto.
  Qed.
      
  (** <v, v> != T0 <-> cvnonzero v *)
  Lemma cvdot_same_neq0 : forall {n} (v : cvec n),
      <v, v> <> 0 <-> cvnonzero v.
  Proof.
    intros. split; intros; intro; apply cvdot_same_eq0 in H0; easy.
  Qed.

  (** <row(m1,i), col(m2,j)> = (m1 * m2)[i,j] *)
  Lemma cvdot_row_col_eq : forall {r c s} (m : mat r c) (n : mat c s) i j,
      (i < r)%nat -> (j < c)%nat ->
      cvdot ((mrow m i)\T) (mcol n j) = (m * n) $ i $ j.
  Proof. intros. apply seqsum_eq. intros. simpl. auto. Qed.

  (** <col(m1,i), col(m2,j)> = (m1\T * m2)[i,j] *)
  Lemma cvdot_col_col : forall {n} (m : smat n) i j,
      (i < n)%nat -> (j < n)%nat ->
      cvdot (mcol m i) (mcol m j) = (m\T * m) $ i $ j.
  Proof. intros. apply seqsum_eq. intros. simpl. auto. Qed.

  (** <row(m1,i), row(m2,j)> = (m1 * m2\T)[i,j] *)
  Lemma cvdot_row_row : forall {n} (m : smat n) i j,
      (i < n)%nat -> (j < n)%nat ->
      rvdot (mrow m i) (mrow m j) = (m * m\T) $ i $ j.
  Proof. intros. apply seqsum_eq. intros. simpl. auto. Qed.

  (** <-v1, v2> = - <v1,v2> *)
  Lemma cvdot_cvopp_l : forall {n} (v1 v2 : cvec n), < -v1, v2> = (- <v1,v2>)%R.
  Proof.
    intros. unfold cvdot, Vector.cvdot. cvec2fun.
    rewrite seqsum_opp. apply seqsum_eq. intros. cbv. ring.
  Qed.

  (** <v1, -v2> = - <v1,v2> *)
  Lemma cvdot_cvopp_r : forall {n} (v1 v2 : cvec n), < v1, -v2> = (- <v1,v2>)%R.
  Proof. intros. rewrite cvdot_comm, cvdot_cvopp_l, cvdot_comm. auto. Qed.

  (** <k * v1, v2> = k * <v1,v2> *)
  Lemma cvdot_cvcmul_l : forall {n} (k : R) (v1 v2 : cvec n),
      < k c* v1, v2> = (k * <v1,v2>)%R.
  Proof.
    intros. unfold cvdot, Vector.cvdot. cvec2fun.
    rewrite seqsum_cmul_l. apply seqsum_eq. intros. cbv. ring.
  Qed.

  (** <v1, k * v2> = k * <v1,v2> *)
  Lemma cvdot_cvcmul_r : forall {n} (k : R) (v1 v2 : cvec n),
      < v1, k c* v2> = (k * <v1,v2>)%R.
  Proof. intros. rewrite cvdot_comm, cvdot_cvcmul_l, cvdot_comm. auto. Qed.
  
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
  
  (** Dot product a same vector equal to the square of its length *)
  Lemma cvdot_same : forall {n} (v : cvec n), <v,v> = ||v||².
  Proof. intros. unfold cvlen. rewrite Rsqr_sqrt; auto. apply cvdot_ge0. Qed.

  (** 0 <= ||v|| *)
  Lemma cvlen_ge0 : forall {n} (v : cvec n), 0 <= ||v||.
  Proof. intros. unfold cvlen. ra. Qed.

  (** Length equal iff dot-product equal *)
  Lemma cvlen_eq_iff_dot_eq : forall {n} (u v : cvec n), ||u|| = ||v|| <-> <u,u> = <v,v>.
  Proof.
    intros. unfold cvlen. split; intros H; try rewrite H; auto.
    apply sqrt_inj in H; auto; apply cvdot_ge0.
  Qed.

  (** || cvec0 || = 0 *)
  Lemma cvlen_cvec0 : forall {n}, || @cvec0 n || = 0.
  Proof. intros. unfold cvlen. rewrite cvdot_0_l. ra. Qed.

  (** ||v|| = 0 <-> v = 0 *)
  Lemma cvlen_eq0_iff_eq0 : forall {n} (v : cvec n), ||v|| = 0 <-> cvzero v.
  Proof.
    intros. unfold cvlen. split; intros.
    - apply cvdot_same_eq0. apply sqrt_eq_0 in H. auto. apply cvdot_ge0.
    - apply cvdot_same_eq0 in H. rewrite H. ra.
  Qed.

  (** ||v|| <> 0 <-> v <> 0 *)
  Lemma cvlen_neq0_iff_neq0 : forall {n} (v : cvec n), ||v|| <> 0 <-> cvnonzero v.
  Proof.
    intros. split; intros; intro.
    - apply cvlen_eq0_iff_eq0 in H0. easy.
    - apply cvlen_eq0_iff_eq0 in H0. easy.
  Qed.

  (** v <> vec0 -> 0 < ||v|| *)
  Lemma cvlen_gt0 : forall {n} (v : cvec n), cvnonzero v -> 0 < ||v||.
  Proof. intros. pose proof (cvlen_ge0 v). apply cvlen_neq0_iff_neq0 in H. lra. Qed.

  (** Length of a vector u is 1, iff the dot product of u and u is 1 *)
  Lemma cvlen_eq1_iff_vdot1 : forall {n} (u : cvec n), ||u|| = 1 <-> <u,u> = 1.
  Proof. intros. unfold cvlen. split; intros; hnf in *. ra. rewrite H. ra. Qed.

  (** || - v|| = || v || *)
  Lemma cvlen_copp : forall n (v : cvec n), || - v|| = || v ||.
  Proof.
    intros. unfold cvlen. f_equal. rewrite cvdot_cvopp_l,cvdot_cvopp_r.
    autorewrite with R. auto.
  Qed.
  
  (** ||k c* v|| = |k| * ||v|| *)
  Lemma cvlen_cmul : forall n (v : cvec n) k, ||k c* v|| = (|k| * ||v||)%R.
  Proof.
    intros. unfold cvlen. rewrite cvdot_cvcmul_l, cvdot_cvcmul_r.
    rewrite <- Rmult_assoc.
    rewrite sqrt_mult_alt; ra. f_equal. autorewrite with R. ra.
  Qed.

  (** ||u + v|| <= ||u|| + ||v|| *)
  Lemma cvlen_add_ineq : forall {n} (u v : cvec n), ||(u + v)|| <= ||u|| + ||v||.
  Abort.

  (** |<u,v>| <= ||u|| * ||v|| *)
  Lemma cvlen_mul_ineq : forall {n} (u v : cvec n), |<u,v>| <= ||u|| * ||v||.
  Abort.
  
  (** 这个性质不成立，有一个例子：相反向量长度相等且平行，但不相等。*)
  Lemma cv_eq_iff_len_parallel : forall {n} (v1 v2 : cvec n),
      (||v1|| = ||v2|| /\ v1 // v2) <-> v1 == v2.
  Abort.

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

  #[export] Instance cvunit_mor {n} : Proper (meq ==> impl) (@cvunit n).
  Proof. simp_proper. intros. unfold cvunit. rewrite H. easy. Qed.
  
  (** (bool version) *)
  Definition cvunitb {n} (u : cvec n) : bool := (<u,u> =? 1)%R.

  (** Convenient property *)
  Lemma cvlen_cvunit : forall {n} (u : cvec n), cvunit u -> ||u|| = 1.
  Proof. intros. apply cvlen_eq1_iff_vdot1. auto. Qed.

  (** Verify the definition is reasonable *)
  Lemma cvunit_spec : forall {n} (u : cvec n), cvunit u <-> ||u|| = 1.
  Proof. intros. split; intros; apply cvlen_eq1_iff_vdot1; auto. Qed.

  (** cvunit v -> v != cvec0. *)
  Lemma cvunit_neq0 : forall {n} (v : cvec n), cvunit v -> v != cvec0.
  Proof.
    intros. intro. rewrite H0 in H. unfold cvunit in H.
    rewrite cvdot_0_l in H. ra.
  Qed.

  (** cvunit u <-> cvunit (cvopp u). *)
  Lemma cvopp_cvunit : forall {n} (u : cvec n), cvunit (cvopp u) <-> cvunit u.
  Proof.
    intros. unfold cvunit. rewrite <- !cvlen_eq1_iff_vdot1.
    rewrite cvlen_copp. easy.
  Qed.

  (** If column of a and column of b all are unit, 
    then column of (a * b) is also unit *)
  (*   a : mat 2 2 *)
  (* a1 : cvunit (mat2col a 0) *)
  (* a2 : cvunit (mat2col a 1) *)
  (* a3 : cvorth (mat2col a 0) (mat2col a 1) *)
  (* b1 : cvunit (mat2col b 0) *)
  (* b2 : cvunit (mat2col b 1) *)
  (* b3 : cvorth (mat2col b 0) (mat2col b 1) *)
  (* ============================ *)
  (* cvunit (mat2col (a * b) 0) *)
End vunit.


(* ==================================== *)
(** ** vector normalization *)
Section vnormalize.

  (** Normalization of a non-zero vector v.
    That is, get a unit vector in the same directin as v. *)
  Definition cvnorm {n} (v : cvec n) : cvec n := (1/||v||) c* v.

  #[export] Instance cvnorm_mor {n} : Proper (meq ==> meq) (@cvnorm n).
  Proof. simp_proper. intros. unfold cvnorm. rewrite H. easy. Qed.

  Lemma cvnorm_len1 : forall {n} (v : cvec n),
      cvnonzero v -> ||cvnorm v|| = 1.
  Proof.
    (* v̂ = v/|v|, |v̂| = sqrt (v/|v| ⋅ v/|v|) = sqrt ((v⋅v) / (|v|*|v|))
     = sqrt(v⋅v) / |v| = |v| / |v| = 1 *)
    intros. unfold cvnorm. unfold cvlen.
    rewrite !cvdot_vcmul_l, !cvdot_vcmul_r. rewrite cvdot_same.
    remember (||v||). autounfold with T. autorewrite with R.
    apply sqrt_eq1_imply_eq1_rev.
    assert (|r| = r). { pose proof (cvlen_ge0 v). subst. ra. }
    rewrite H0. cbv. field. subst. apply cvlen_neq0_iff_neq0; auto.
  Qed.

  (** Unit vector is fixpoint of cvnorm operation *)
  Lemma cvnorm_cvunit_fixpoint : forall {n} (v : cvec n),
      cvunit v -> cvnorm v == v.
  Proof.
    intros. lma. rewrite (cvunit_spec v) in H. rewrite H. autorewrite with R. easy.
  Qed.

  (** The component of a normalized vector is equivalent to its original component 
      divide the vector's length *)
  Lemma cvnorm_nth : forall {n} (v : cvec n) i,
      cvnonzero v -> (i < n)%nat -> ((cvnorm v) $ i == v $ i / (||v||))%T.
  Proof.
    intros. unfold cvnorm. rewrite cvcmul_nth; auto.
    autounfold with T. field. apply cvlen_neq0_iff_neq0; auto.
  Qed.

  (** Normalization is idempotent *)
  Lemma cvnorm_idem : forall {n} (v : cvec n),
      cvnonzero v -> cvnorm (cvnorm v) == cvnorm v.
  Proof.
    intros. unfold cvnorm. rewrite cvcmul_assoc.
    assert (1 / (||1 / (||v||) c* v||) == T1)%T.
    { rewrite cvlen_cmul. remember (||v||) as r. autounfold with T.
      replace (|(1/r)|) with (1/r); try field.
      + rewrite Heqr. apply cvlen_neq0_iff_neq0; auto.
      + rewrite Rabs_right; auto.
        pose proof (cvlen_gt0 v H). rewrite <- Heqr in H0.
        assert (forall r, 0 < r -> 0 <= r). intros. ra.
        apply Rle_ge. apply H1. apply Rdiv_lt_0_compat; lra. }
    rewrite H0. monoid_simp.
  Qed.

  (** Keep the same direction as the original vector *)
  Lemma cvnorm_direction : forall {n} (v : cvec n),
      cvnonzero v -> (cvnorm v) // v.
  Proof.
    intros. unfold cvpara. unfold cvnorm. exists (||v||). split.
    - apply cvlen_neq0_iff_neq0; auto.
    - rewrite cvcmul_assoc. autounfold with T.
      match goal with | |- context[?a c* _] => replace a with 1 end.
      apply cvcmul_1_l. field. apply cvlen_neq0_iff_neq0; auto.
  Qed.

  Lemma cvnorm_spec : forall {n} (v : cvec n),
      cvnonzero v -> (||cvnorm v|| = 1 /\ (cvnorm v) // v).
  Proof.
    intros. split. apply cvnorm_len1; auto.
    apply cvnorm_direction; auto.
  Qed.

  (** 单位化后的非零向量都是单位向量 *)
  Lemma cvnorm_unit : forall {n} (v : cvec n),
      cvnonzero v -> cvunit (cvnorm v).
  Proof. intros. apply cvunit_spec. apply cvnorm_len1; auto. Qed.

End vnormalize.


(* ==================================== *)
(* (** ** About {cvdot, cvunit,  cvnorm} *) *)
(* Section cvdot_cvunit_cvnorm. *)
  

(* End cvdot_cvunit_cvangle_cvnorm. *)


(* ==================================== *)
(** ** Angle between two vectors *)
Section vangle.

  (** The angle from vector v1 to vector v2, Here, θ ∈ [0,π] *)
  Definition cvangle {n} (v1 v2 : cvec n) : R :=
    let v1' := cvnorm v1 in
    let v2' := cvnorm v2 in
    acos (<v1', v2'>).
  
  Infix "∠" := cvangle (at level 60) : cvec_scope.

  #[export] Instance cvangle_mor {n} : Proper (meq ==> meq ==> eq) (@cvangle n).
  Proof.
    simp_proper. intros. unfold cvangle. rewrite H,H0. auto.
  Qed.

  (** Angle is commutative *)
  Lemma cvangle_comm : forall {n} (v1 v2 : cvec n), v1 ∠ v2 = v2 ∠ v1.
  Proof. intros. unfold cvangle. rewrite cvdot_comm. auto. Qed.
  
  (** The angle between (1,0,0) and (1,1,0) is 45 degree, i.e., π/4 *)
  (* Remark: Here, we can finish a demo proof with a special value π/4,
     but real cases maybe have any value, it is hard to finished in Coq.
     Because the construction of {sqrt, acos, PI, etc} is complex. *)
  Example cvangle_ex1 : (@l2cv 3 [1;0;0]) ∠ (l2cv [1;1;0]) = PI/4.
  Proof.
    rewrite <- acos_inv_sqrt2.
    compute. f_equiv. autorewrite with R. auto.
  Qed.

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
    { rewrite <- !cvdot_same. unfold cvsub.
      rewrite !cvdot_vadd_distr_l, !cvdot_vadd_distr_r.
      rewrite !cvdot_vopp_l, !cvdot_vopp_r. rewrite (cvdot_comm b a).
      autounfold with T; ring. }
    pose proof (cosine_law a b). ra.
  Qed.

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
      -1 <= <cvnorm u, cvnorm v> <= 1.
  Proof. intros. apply cvdot_unit_bound; apply cvnorm_unit; auto. Qed.

  (** 0 <= cvangle u v <= PI *)
  Lemma cvangle_bound : forall {n} (u v : cvec n), 0 <= cvangle u v <= PI.
  Proof. intros. unfold cvangle. apply acos_bound. Qed.

  (** 0 <= sin (cvangle u v) *)
  Lemma sin_cvangle_ge0 : forall {n} (u v : cvec n), 0 <= sin (cvangle u v).
  Proof. intros. apply sin_ge_0; apply cvangle_bound. Qed.
  
  (** θ ≠ 0 -> θ ≠ π -> 0 < sin (cvangle u v) *)
  Lemma sin_cvangle_gt0 : forall {n} (u v : cvec n),
      u ∠ v <> 0 -> u ∠ v <> PI -> 0 < sin (u ∠ v).
  Proof. intros. pose proof (cvangle_bound u v). apply sin_gt_0; ra. Qed.

  (* (** v1 ∠ v2 = 0 <-> v1,v2同向平行 *) *)
  (* Lemma cvangle_eq0_cvpara : forall {n} (v1 v2 : cvec n), *)
  (*     cvnonzero v1 -> cvnonzero v2 -> *)
  (*     (cvangle v1 v2 = 0 <-> (exists k : R, k > 0 /\ k c* v1 == v2)). *)
  (* Proof. *)
  (*   intros. unfold cvangle. split; intros. *)
  (*   2:{ *)
  (*     destruct H1 as [k [H11 H12]]. *)
  (*     rewrite <- H12. rewrite <- acos_1. f_equal. *)
  (*     unfold cvnorm. *)
  (*     rewrite cvcmul_assoc, !cvdot_cvcmul_l, !cvdot_cvcmul_r. *)
  (*     rewrite cvlen_cmul. rewrite cvdot_same. rewrite Rabs_right; ra. *)
  (*     autounfold with T. field. *)
  (*     apply cvlen_neq0_iff_neq0 in H,H0. lra. } *)
  (*   1:{ *)
  (*     rewrite <- acos_1 in H1. apply acos_inj in H1; ra. *)
  (*     2:{ apply cvdot_vnormalize_bound; auto. } *)
  (*     1:{ *)
  (*       (** *)
  (*          v1 ∠ v2 = 0 -> acos(<v1',v2'>) = 0, where v1',v2' is normalized v1,v2. *)
  (*          then <v1',v2'> = 1. that is <cvnormlize v1, cvnorm v2> = , *)
  (*          then (1/(|v1|*|v2|)) * <v1,v2> = 1 *)
  (*          可以借助投影来表明 v1和v2是k倍的关系 *)
  (*        *) *)
  (*       exists (||v1|| * ||v2||)%R. *)
  (*       rewrite cvdot_eq_cos_angle in H1. *)
  (*       Admitted. *)

  (** 相同的向量之间的角度是 0。可能还有一个特例，两个0向量之间的夹角可能是任意值 *)
  Lemma cvangle_same_eq0 : forall {n} (v : cvec n),
      cvnonzero v -> v ∠ v = 0.
  Proof.
    intros. unfold cvangle. rewrite cvdot_same.
    rewrite cvnorm_len1; auto. autorewrite with R. apply acos_1.
  Qed.

  (** v1 ∠ v3 = (v1 ∠ v2) + (v2 ∠ v3) *)
  Lemma cvangle_add : forall (v1 v2 v3 : cvec 3),
      v1 ∠ v2 < PI ->
      v2 ∠ v3 < PI ->
      v1 ∠ v3 = ((v1 ∠ v2) + (v2 ∠ v3))%R.
  Proof.
  (** 由于目前 cvangle 的值域是 [0,π]，暂不能表示 [0,2π)，所以该性质有点困难。
      有扩展了值域为 [0,2π) 的 cv2angle 可做参考，但3D中尚未实现。*)
  Admitted.

  Lemma Rdiv_1_neq_0_compat : forall r : R, r <> 0 -> 1 / r <> 0.
  Proof. intros. pose proof (Rinv_neq_0_compat r H). ra. Qed.

  
  (* (** 给定两个向量，若将这两个向量同时旋转θ角，则向量之和在旋转前后的夹角也是θ。*) *)
  (* Lemma cvangle_cvadd : forall (v1 v2 v1' v2' : cvec 2), *)
  (*     cvnonzero v1 -> cvnonzero v2 -> *)
  (*     ||v1|| = ||v1'|| -> ||v2|| = ||v2'|| -> *)
  (*     v1 ∠ v2 = v1' ∠ v2' -> *)
  (*     v1 + v2 ∠ v1' + v2' = v1 ∠ v1'. *)
  (* Proof. *)
  (*   intros v1 v2 v1' v2' Hneq0_v1 Hneq0_v2 Hlen_eq_11' Hlen_eq_22' Hangle_eq. *)
  (*   assert (||v1|| <> 0) as Hlen_neq0_v1. *)
  (*   { apply cvlen_neq0_iff_neq0; auto. } *)
  (*   assert (||v2|| <> 0) as Hlen_neq0_v2. *)
  (*   { apply cvlen_neq0_iff_neq0; auto. } *)
  (*   assert (cvnonzero v1') as Hneq0_v1'. *)
  (*   { apply cvlen_neq0_iff_neq0 in Hneq0_v1. apply cvlen_neq0_iff_neq0. ra. } *)
  (*   assert (cvnonzero v2') as Hneq0_v2'. *)
  (*   { apply cvlen_neq0_iff_neq0 in Hneq0_v2. apply cvlen_neq0_iff_neq0. ra. } *)
  (*   unfold cvangle in *. f_equiv. *)
  (*   apply acos_inj in Hangle_eq; try apply cvdot_vnormalize_bound; auto. *)
  (*   unfold cvnorm in *. *)
  (*   rewrite !cvdot_cvcmul_l, !cvdot_cvcmul_r in *. *)
  (*   (* remember (||(v1 + v2)%CV||) as r1. *) *)
  (*   (* remember (||(v1' + v2')%CV||) as r1'. *) *)
  (*   rewrite !cvdot_vadd_distr_l, !cvdot_vadd_distr_r. *)
  (*   rewrite <- Hlen_eq_11', <- Hlen_eq_22' in *. *)
  (*   assert (<v1,v2> = <v1',v2'>). *)
  (*   { apply Rmult_eq_reg_l with (r:=(1/(||v2||))). *)
  (*     apply Rmult_eq_reg_l with (r:=(1/(||v1||))). auto. *)
  (*     all: apply Rdiv_1_neq_0_compat; auto. } *)
  (*   (* 以下，尝试自动证明，因为我暂时无法手动证明 *) *)
  (*   Open Scope fun_scope. *)
  (*   cvec2fun. cbv in *. autorewrite with R in *. *)
  (*   remember (v1.11) as a1; remember (v1.21) as a2; remember (v1.31) as a3. *)
  (*   remember (v2.11) as b1; remember (v2.21) as b2; remember (v2.31) as b3. *)
  (*   rename v1' into v3. rename v2' into v4. *)
  (*   remember (v3.11) as c1; remember (v3.21) as c2; remember (v3.31) as c3. *)
  (*   remember (v4.11) as d1; remember (v4.21) as d2; remember (v4.31) as d3. *)
  (*   autorewrite with R. autorewrite with R in H. *)
  (*   generalize Hlen_eq_11' Hlen_eq_22' H. clear. *)
  (*   intros. *)
  (*   field_simplify. *)
  (*   autorewrite with R sqrt. *)
  (*   rewrite <- sqrt_mult_alt. *)
  (*   cbv. *)
  (*   field_simplify. *)
  (*   autorewrite with R. *)
  (*   apply sqrt_inj in Hlen_eq_11', Hlen_eq_22'. *)
  (*   match goal with *)
  (*   | |- context [?a / sqrt ?b = ?c] => *)
  (*       assert (b * c * c = a * a)%R end. *)
  (*   (* 核心部分 *) *)
  (*   field_simplify. *)
  (*   Admitted. *)

  (** 给定两个向量，若将这两个向量同时旋转θ角，则向量之和在旋转前后的夹角也是θ。*)
  Lemma cvangle_cvadd : forall (v1 v2 v1' v2' : cvec 3),
      cvnonzero v1 -> cvnonzero v2 ->
      ||v1|| = ||v1'|| -> ||v2|| = ||v2'|| ->
      v1 ∠ v2 = v1' ∠ v2' ->
      v1 + v2 ∠ v1' + v2' = v1 ∠ v1'.
  Proof.
    Admitted.
    (* intros v1 v2 v1' v2' Hneq0_v1 Hneq0_v2 Hlen_eq_11' Hlen_eq_22' Hangle_eq. *)
    (* assert (||v1|| <> 0) as Hlen_neq0_v1. *)
    (* { apply cvlen_neq0_iff_neq0; auto. } *)
    (* assert (||v2|| <> 0) as Hlen_neq0_v2. *)
    (* { apply cvlen_neq0_iff_neq0; auto. } *)
    (* assert (cvnonzero v1') as Hneq0_v1'. *)
    (* { apply cvlen_neq0_iff_neq0 in Hneq0_v1. apply cvlen_neq0_iff_neq0. ra. } *)
    (* assert (cvnonzero v2') as Hneq0_v2'. *)
    (* { apply cvlen_neq0_iff_neq0 in Hneq0_v2. apply cvlen_neq0_iff_neq0. ra. } *)
    (* unfold cvangle in *. f_equiv. *)
    (* apply acos_inj in Hangle_eq; try apply cvdot_vnormalize_bound; auto. *)
    (* unfold cvnorm in *. *)
    (* rewrite !cvdot_cvcmul_l, !cvdot_cvcmul_r in *. *)
    (* (* remember (||(v1 + v2)%CV||) as r1. *) *)
    (* (* remember (||(v1' + v2')%CV||) as r1'. *) *)
    (* rewrite !cvdot_vadd_distr_l, !cvdot_vadd_distr_r. *)
    (* rewrite <- Hlen_eq_11', <- Hlen_eq_22' in *. *)
    (* assert (<v1,v2> = <v1',v2'>). *)
    (* { apply Rmult_eq_reg_l with (r:=(1/(||v2||))). *)
    (*   apply Rmult_eq_reg_l with (r:=(1/(||v1||))). auto. *)
    (*   all: apply Rdiv_1_neq_0_compat; auto. } *)
    (* (* 以下，尝试自动证明，因为我暂时无法手动证明 *) *)
    (* Open Scope fun_scope. *)
    (* cvec2fun. cbv in *. autorewrite with R in *. *)
    (* remember (v1.11) as a1; remember (v1.21) as a2; remember (v1.31) as a3. *)
    (* remember (v2.11) as b1; remember (v2.21) as b2; remember (v2.31) as b3. *)
    (* rename v1' into v3. rename v2' into v4. *)
    (* remember (v3.11) as c1; remember (v3.21) as c2; remember (v3.31) as c3. *)
    (* remember (v4.11) as d1; remember (v4.21) as d2; remember (v4.31) as d3. *)
    (* autorewrite with R. autorewrite with R in H. *)
    (* generalize Hlen_eq_11' Hlen_eq_22' H. clear. *)
    (* intros. *)
    (* clear. *)
    

  (** a <> 0 -> (a c* v1) ∠ v2 = v1 ∠ v2 *)
  Lemma cvangle_cvcmul_l : forall {n} (v1 v2 : cvec n) (a : R),
      a <> 0 -> (a c* v1) ∠ v2 = v1 ∠ v2.
  Proof.
  Admitted.

  (** a <> 0 -> v1 ∠ (a c* v2) = v1 ∠ v2 *)
  Lemma cvangle_cvcmul_r : forall {n} (v1 v2 : cvec n) (a : R),
      a <> 0 -> v1 ∠ (a c* v2) = v1 ∠ v2.
  Proof.
  Admitted.

  Lemma cvangle_cvnorm_l : forall {n} (v1 v2 : cvec n),
      cvnorm v1 ∠ v2 = v1 ∠ v2.
  Admitted.
  Lemma cvangle_cvnorm_r : forall {n} (v1 v2 : cvec n),
      v1 ∠ cvnorm v2 = v1 ∠ v2.
  Admitted.

End vangle.
Infix "∠" := cvangle (at level 60) : cvec_scope.


(* ==================================== *)
(** ** Projection component of a vector onto another *)
Section cvproj.

  (** The projection component of a onto b *)
  Definition cvproj {n} (a b : cvec n) : cvec n := (<a,b> / <b,b>) c* b.

  (* (** The scalar projection of a on b is a simple triangle relation *) *)
  (* Lemma cvsproj_spec : forall {n} (a b : cvec n), cvsproj a b == `|a| * cvangle. *)

  #[export] Instance cvproj_mor {n} : Proper (meq ==> meq ==> meq) (@cvproj n).
  Proof. simp_proper. intros. unfold cvproj. rewrite H,H0. easy. Qed.

  (** cvproj (a1 + a2) b == cvproj a1 b + cvproj a2 b *)
  Lemma cvproj_linear_cvadd : forall {n} (a1 a2 b : cvec n),
      cvnonzero b -> (cvproj (a1 + a2) b == cvproj a1 b + cvproj a2 b)%CV.
  Proof.
    intros. unfold cvproj. rewrite cvdot_vadd_distr_l.
    rewrite <- cvcmul_add_distr. f_equiv. autounfold with T. field.
    rewrite cvdot_same. apply cvlen_gt0 in H. ra.
  Qed.

  (** cvproj (k * a) b == k * (cvproj a b) *)
  Lemma cvproj_linear_cvcmul : forall {n} (a b : cvec n) (k : R),
      cvnonzero b -> (cvproj (k c* a) b == k c* (cvproj a b))%CV.
  Proof.
    intros. unfold cvproj. rewrite cvdot_vcmul_l. rewrite cvcmul_assoc. f_equiv.
    autounfold with T. field.
    rewrite cvdot_same. apply cvlen_gt0 in H. ra.
  Qed.
  
  (** cvproj a a = a *)
  Lemma cvproj_same : forall {n} (a : cvec n), cvnonzero a -> cvproj a a == a.
  Proof.
    intros. unfold cvproj. replace (<a,a> / <a,a>) with 1; try field.
    apply cvcmul_1_l. rewrite cvdot_same. apply cvlen_gt0 in H. ra.
  Qed.
  
End cvproj.


(* ==================================== *)
(** ** Perpendicular component of a vector respect to another *)
Section cvperp.

  (** The perpendicular component of a respect to b *)
  Definition cvperp {n} (a b : cvec n) : cvec n := a - cvproj a b.
  
  #[export] Instance cvperp_mor {n} : Proper (meq ==> meq ==> meq) (@cvperp n).
  Proof. simp_proper. intros. unfold cvperp. rewrite H,H0. easy. Qed.

  (** cvperp (a1 + a2) b == cvperp a1 b + cvperp a2 b *)
  Lemma cvperp_linear_cvadd : forall {n} (a1 a2 b : cvec n),
      cvnonzero b -> (cvperp (a1 + a2) b == cvperp a1 b + cvperp a2 b)%CV.
  Proof.
    intros. unfold cvperp. rewrite cvproj_linear_cvadd; auto.
    unfold cvsub. elimh. rewrite cvopp_vadd. easy.
  Qed.

  (** cvperp (k * a) b == k * (cvperp a b) *)
  Lemma cvperp_linear_cvcmul : forall {n} (a b : cvec n) (k : R),
      cvnonzero b -> (cvperp (k c* a) b == k c* (cvperp a b))%CV.
  Proof.
    intros. unfold cvperp. rewrite cvproj_linear_cvcmul; auto.
    rewrite cvcmul_vsub. easy.
  Qed.

  (** cvperp a a = 0 *)
  Lemma cvperp_same : forall {n} (a : cvec n), cvnonzero a -> cvperp a a == cvec0.
  Proof.
    intros. unfold cvperp. rewrite cvproj_same; auto; auto. apply cvsub_self.
  Qed.
  
End cvperp.


(* ==================================== *)
(** ** Orthogonal vectors 正交的两个向量 *)
Section cvorth.

  (** Two vectors, x and y, in an inner product space V, are orthogonal if their 
    inner-product <x,y> is zero, and the relationship is denoted x ⟂ y. *)

  (** Two real column-vectors are orthogonal (also called perpendicular) *)
  Definition cvorth {n} (v1 v2 : cvec n) : Prop := <v1,v2> = 0.

  (** Bool version to determine if two vectors are orthogonal *)
  Definition cvorthb {n} (v1 v2 : cvec n) : bool := (<v1,v2> =? 0)%R.
  Infix "⟂" := cvorth ( at level 50).

  #[export] Instance cvorth_mor {n} :
    Proper (meq ==> meq ==> impl) (@cvorth n).
  Proof.
    simp_proper. intros. unfold cvorth. rewrite H,H0. easy.
  Qed.

  (** u ⟂ v -> v ⟂ u *)
  Lemma cvorth_comm : forall (u v : cvec 3), u ⟂ v -> v ⟂ u.
  Proof. intros. unfold cvorth in *. rewrite cvdot_comm; auto. Qed.

  (** u ⟂ v -> cvproj u v == cvec0 *)
  Lemma cvorth_cvproj : forall (u v : cvec 3),
      cvnonzero v -> u ⟂ v -> cvproj u v == cvec0.
  Proof.
    intros. unfold cvorth in H0.
    unfold cvproj. rewrite H0. autorewrite with R. rewrite cvcmul_0_l; easy.
    apply cvdot_same_neq0; auto.
  Qed.
  
  (** u ⟂ v -> cvperp u v == u *)
  Lemma cvorth_cvperp : forall (u v : cvec 3),
      cvnonzero v -> u ⟂ v -> cvperp u v == u.
  Proof.
    intros. unfold cvperp. rewrite cvorth_cvproj; auto. apply cvsub_0_r.
  Qed.

  (** u ⟂ v -> cvnorm u ⟂ v *)
  Lemma cvorth_cvnorm_l : forall (u v : cvec 3), u ⟂ v -> cvnorm u ⟂ v.
  Proof.
    intros. unfold cvorth, cvnorm in *. rewrite cvdot_cvcmul_l; ra.
  Qed.

  (** cvnorm u ⟂ v -> u ⟂ v *)
  Lemma cvorth_cvnorm_l_rev : forall (u v : cvec 3),
      u != cvec0 -> cvnorm u ⟂ v -> u ⟂ v.
  Proof.
    intros. unfold cvorth, cvnorm in *.
    rewrite cvdot_cvcmul_l in H0; ra.
    assert (1 * / (||u||) <> 0)%R; ra.
    apply cvlen_neq0_iff_neq0 in H.
    apply Rmult_integral_contrapositive_currified; ra.
    apply Rinv_neq_0_compat; auto.
  Qed.

  (** u ⟂ v -> cvnorm u ⟂ v *)
  Lemma cvorth_cvnorm_r : forall (u v : cvec 3), u ⟂ v -> u ⟂ cvnorm v.
  Proof.
    intros. unfold cvorth, cvnorm in *. rewrite cvdot_cvcmul_r; ra.
  Qed.

  (** u ⟂ cvnorm v -> u ⟂ v *)
  Lemma cvorth_cvnorm_r_rev : forall (u v : cvec 3),
      v != cvec0 -> u ⟂ cvnorm v -> u ⟂ v.
  Proof.
    intros. unfold cvorth, cvnorm in *.
    rewrite cvdot_cvcmul_r in H0; ra. assert (1 * / (||v||) <> 0)%R; ra.
    apply cvlen_neq0_iff_neq0 in H.
    apply Rmult_integral_contrapositive_currified; ra.
    apply Rinv_neq_0_compat; auto.
  Qed.
  
  (** u ⟂ v -> (k c* u) ⟂ v *)
  Lemma cvorth_cvcmul_l : forall (u v : cvec 3) (k : R), u ⟂ v -> (k c* u) ⟂ v.
  Proof.
    intros. unfold cvorth, cvnorm in *. rewrite cvdot_cvcmul_l; ra.
  Qed.

  (** (k c* u) ⟂ v -> u ⟂ v *)
  Lemma cvorth_cvcmul_l_rev : forall (u v : cvec 3) (k : R),
      k <> 0 -> (k c* u) ⟂ v -> u ⟂ v.
  Proof.
    intros. unfold cvorth, cvnorm in *. rewrite cvdot_cvcmul_l in H0; ra.
  Qed.

  (** u ⟂ v -> u ⟂ (k c* v) *)
  Lemma cvorth_cvcmul_r : forall (u v : cvec 3) (k : R), u ⟂ v -> u ⟂ (k c* v).
  Proof.
    intros. unfold cvorth, cvnorm in *. rewrite cvdot_cvcmul_r; ra.
  Qed.

  (** u ⟂ (k c* v) -> u ⟂ v *)
  Lemma cvorth_cvcmul_r_rev : forall (u v : cvec 3) (k : R),
      k <> 0 -> u ⟂ (k c* v) -> u ⟂ v.
  Proof.
    intros. unfold cvorth, cvnorm in *. rewrite cvdot_cvcmul_r in H0; ra.
  Qed.

  (** cvproj ⟂ cvperp *)
  Lemma cvorth_proj_perp : forall {n} (u v : cvec n), cvproj u v ⟂ cvperp u v.
  Proof.
    intros. hnf. unfold cvperp, cvproj.
    (* unfold cvperp. unfold cvsub. rewrite cvdot_vadd_distr_r. *)
    (* 以下证明思路明显是错误的，不可能所有元素都是0 *)
    apply seqsum_eq0.
    intros.
    cvec2fun. simpl.
    unfold cvdot, Vector.cvdot. simpl.
    autorewrite with R.
    remember (seqsum (fun i0 : nat => v i0 0%nat * v i0 0%nat) n)%T as r1.
    remember (seqsum (fun i0 : nat => u i0 0%nat * v i0 0%nat) n)%T as r2.
  Abort.
  
End cvorth.
Infix "⟂" := cvorth ( at level 50).


(* ==================================== *)
(** ** Orthogonal set 正交向量组（集） *)
Section cvorthset.

  (** A set of vectors in an inner product space is called pairwise orthogonal if 
      each pairing of them is orthogonal. Such a set is called an orthogonal set.
      Note: each pair means {(vi,vj)|i≠j}  *)
  Definition cvorthset {r c} (m : mat r c) : Prop :=
    forall j1 j2, (j1 < c)%nat -> (j2 < c)%nat -> (j1 <> j2) -> <mcol m j1, mcol m j2> = T0.

  (** (bool version) *)
  Definition cvorthsetb {r c} (m : mat r c) : bool :=
    (* two column vectors is orthogonal *)
    let orth (i j : nat) : bool := (<mcol m i, mcol m j> =? T0)%R in
    (* remain column indexes after this column *)
    let cids (i : nat) : list nat := seq (S i) (c - S i) in
    (* the column is orthogonal to right-side remain columns *)
    let allcols (j : nat) : bool := and_blist (map (fun k => orth j k) (cids j)) in
    (* all columns is mutually orthogonal (Note orthogonal is commutative) *)
    and_blist (map (fun j => allcols j) (seq 0 c)).

  Lemma cvorthsetb_true_iff : forall {r c} (m : mat r c),
      cvorthsetb m <-> cvorthset m.
  Admitted.

  Example cvorthset_ex1 :
    cvorthset (@l2m 3 3 [[1;1;1];[0;sqrt 2; -(sqrt 2)];[-1;1;1]])%T.
  Proof.
    apply cvorthsetb_true_iff. cbv.
    (** Auto solve equality contatin "Req_EM_T" *)
    repeat
      match goal with
      | |- context[ Req_EM_T ?a ?b] => destruct Req_EM_T; try lra
      end.
    autorewrite with R sqrt in *; ra.
  Qed.
End cvorthset.


(* ==================================== *)
(** ** Orthonormal vectors 标准正交的向量组 *)
Section mcolsOrthonormal.

  (** All (different) column-vectors of a matrix are orthogonal each other.
      For example: [v1;v2;v3] => v1⟂v2 && v1⟂v3 && v2⟂v3. *)
  Definition mcolsorth {r c} (m : mat r c) : Prop :=
    forall j1 j2, (j1 < c)%nat -> (j2 < c)%nat -> j1 <> j2 -> mcol m j1 ⟂ mcol m j2.

  (** bool version *)
  Definition mcolsorthb {r c} (m : mat r c) : bool :=
    let is_orth (i j : nat) : bool := (<mcol m i, mcol m j> =? T0)%R in
    let cids (i : nat) : list nat := seq (S i) (c - S i) in
    let chk_col (j : nat) : bool := and_blist (map (fun k => is_orth j k) (cids j)) in
    and_blist (map (fun j => chk_col j) (seq 0 c)).

  Lemma mcolsorthb_spec : forall {r c} (m : mat r c),
      mcolsorthb m <-> mcolsorth m.
  Proof.
  Admitted.

  Section test.
    Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : R.
    Let m1 : mat 1 3 := l2m [[a11;a12;a13];[a21;a22;a23]].
    Let m2 : mat 3 1 := l2m [[a11;a12];[a21;a22];[a31;a32]].

    (* Compute mcolsorthb m1. *)
    (* Compute mcolsorthb m2. (* because only one column, needn't be check *) *)
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
    mcolsorth m /\ mcolsUnit m.

End mcolsOrthonormal.


(* ==================================== *)
(** ** Orthogonal matrix *)
Section morth.

  (** matrix m is orthogonal <-> columns of m are orthogomal *)
  Lemma morth_iff_mcolsOrthonormal : forall {n} (m : smat n),
      morth m <-> mcolsOrthonormal m.
  Proof.
    intros.
    unfold morth,mcolsOrthonormal.
    unfold mcolsorth, mcolsUnit.
    unfold cvorth, cvunit.
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
  Theorem morth_keep_dot : forall {n} (m : smat n) (v1 v2 : cvec n),
      morth m -> <m * v1, m * v2> = <v1, v2>.
  Proof.
    intros.
    rewrite cvdot_eq_mul_trans.
    unfold scalar_of_mat, Matrix.scalar_of_mat.
    rewrite (m2f_mor _ (v1\T * v2)); auto.
    rewrite mtrans_mmul. rewrite mmul_assoc. rewrite <- (mmul_assoc _ m).
    rewrite morth_iff_mul_trans_l in H. rewrite H.
    rewrite mmul_1_l. easy.
  Qed.

  (** Transformation by orthogonal matrix will keep length. *)
  Corollary morth_keep_length : forall {n} (m : smat n) (v : cvec n),
      morth m -> ||m * v|| = ||v||.
  Proof.
    intros. rewrite cvlen_eq_iff_dot_eq. apply morth_keep_dot. auto.
  Qed.

  (** Transformation by orthogonal matrix will keep normalization. *)
  Corollary morth_keep_normalize : forall {n} (m : smat n) (v : cvec n),
      morth m -> cvnorm (m * v) == m * (cvnorm v).
  Proof.
    intros. unfold cvnorm.
    rewrite morth_keep_length; auto. apply mcmul_mmul_assoc_r.
  Qed.

  (** Transformation by orthogonal matrix will keep angle. *)
  Corollary morth_keep_angle : forall {n} (m : smat n) (v1 v2 : cvec n),
      morth m -> m * v1 ∠ m * v2 = v1 ∠ v2.
  Proof.
    intros. unfold cvangle. f_equal. rewrite !morth_keep_normalize; auto.
    rewrite morth_keep_dot; auto.
  Qed.

  (** 由于正交矩阵可保持变换向量的长度和角度，它可保持坐标系的整体结构不变。
      因此，正交矩阵仅可用于旋转变换和反射变换或二者的组合变换。
      当正交矩阵的行列式为1，表示一个旋转，行列式为-1，表示一个反射。*)
End morth.


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


  Variable a1 a2 a3 : T.
  Variable f : T -> T.
  Let v3 := t2rv_3 (a1,a2,a3).
  Let v4 := t2cv_3 (a1,a2,a3).
  (* Compute rv2l (rvmap v3 f). *)
  (* Compute cv2l (cvmap v4 f). *)
  
End test.
