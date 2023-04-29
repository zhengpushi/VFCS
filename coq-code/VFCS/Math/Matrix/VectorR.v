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
Require Export MatrixR.


(* ======================================================================= *)
(** * Vector theory come from common implementations *)

Module Export VectorTheoryR := RingVectorTheory RingElementTypeR.

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
  
End vnormalize.


(* ==================================== *)
(** ** Angle between two vectors *)
Section vangle.

  (** The angle between two vectors, is derived from the inner-product *)
  Definition cvangle {n} (v1 v2 : cvec n) : R :=
    let v1' := cvnormalize v1 in
    let v2' := cvnormalize v2 in
    acos (<v1', v2'>).
  
  Infix "∠" := cvangle (at level 60) : cvec_scope.
  
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

End vangle.
Infix "∠" := cvangle (at level 60) : cvec_scope.


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
    Variable a00 a01 a02 a10 a11 a12 a20 a21 a22 : R.
    Let m1 : mat 1 3 := l2m [[a00;a01;a02];[a10;a11;a12]].
    Let m2 : mat 3 1 := l2m [[a00;a01];[a10;a11];[a20;a21]].

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
    intros. rewrite cvdot_eq_mul_trans.
    unfold scalar_of_mat, Matrix.scalar_of_mat.
    rewrite (matf_mor _ (v1\T * v2)); auto.
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
(** ** 2D vector theory *)
Section v2.
  
  (** A theorem about the angle between two vectors and its dot product in 2D *)
  Section cosine_dot.
    Variable a b : cvec 2.
    Variable θ : R. (* this is angle between a and b *)
    (* The law of cosine *)
    Hypotheses cosine_law : ((||(a - b)%CV||)² = ||a||² + ||b||² - 2 * ||a|| * ||b|| * cos θ)%R.
    
    Theorem cosine_dot : <a,b> = (||a|| * ||b|| * cos θ)%R.
    Proof.
      assert (||(a-b)%CV||² = ||a||² + ||b||² - 2 * <a,b>)%R.
      { rewrite !cvlen_sqr.
        unfold cvsub.
        rewrite !cvdot_vadd_distr_l, !cvdot_vadd_distr_r.
        rewrite !cvdot_vopp_l, !cvdot_vopp_r. rewrite (cvdot_comm b a).
        autounfold with A; ring. } ra.
    Qed.
  End cosine_dot.

  (** 主动旋转，逆时针正向(或顺时针负向)时，旋转矩阵 *)

  (** 注意列向量和行向量的不同用法：
     1. 给一个在该坐标系下的列向量 v1，正向旋转该向量 θ 角得到新的向量 v1'，按如下公式
          v1' = R2d(θ) * v1
     2. 给一个在该坐标系下的行向量 v2，正向旋转该向量 θ 角得到新的向量 v2'，按如下公式
          v2' = v2 * (R2d(θ))\T
     3. 如果进行了连续两次旋转，即，先旋转θ1，然后在此基础上再旋转θ2，则
        按照列向量：v' = R(θ2) * R(θ1) * v，其中 R 是 R2d
        按照行向量：v' = v * R(θ1) * R(θ2)，其中 R 是 R2d\T
   *)
  Definition R2d (θ : R) : smat 2 :=
    let c := cos θ in
    let s := sin θ in
    l2m [[c;-s];[s;c]]%R.

  (** 一个实际的例子来说明该旋转矩阵的用法 *)
  Section test.
    Variable θ : R.
    Variable v1 : cvec 2.
    Let v2 : rvec 2 := v1\T. (* v1和v2在数学上相等，只是分别写作列向量和行向量的形式 *)
    Let v1' : cvec 2 := (R2d θ) * v1.     (* 用列向量形式计算 *)
    Let v2' : rvec 2 := v2 * ((R2d θ)\T). (* 用行向量形式计算 *)
    Let v2'' : cvec 2 := v2'\T.  (* 再次写出 v2' 的列向量形式 *)
    Goal v1' == v2''. (* 结果应该相同 *)
    Proof. lma. Qed.

  End test.

  (** 为了避免旋转矩阵使用错误，命名一些操作 *)

  (** 2D中旋转一个列向量 *)
  Definition Rot2dC (θ : R) (v : cvec 2) : cvec 2 := (R2d θ) * v.

  (** 2D中旋转一个行向量 *)
  Definition Rot2dR (θ : R) (v : rvec 2) : rvec 2 := v * ((R2d θ)\T).

  (** 旋转列向量，等效于旋转行向量，但需要转换输入和输出的向量形式 *)
  Lemma Rot2dC_eq_Rot2dR : forall θ (v : cvec 2), Rot2dC θ v == (Rot2dR θ (v\T))\T.
  Proof. lma. Qed.

  (** 旋转列向量，等效于旋转行向量，但需要转换输入和输出的向量形式 *)
  Lemma Rot2dR_eq_Rot2dC : forall θ (v : rvec 2), Rot2dR θ v == (Rot2dC θ (v\T))\T.
  Proof. lma. Qed.
End v2.


(* ==================================== *)
(** ** 3D vector theory *)
Section v3.

  (** Standard basis vector in Euclidean space of 3-dimensions *)
  Section basis_vector.
    Definition rv3i : rvec 3 := mk_rvec3 1 0 0.
    Definition rv3j : rvec 3 := mk_rvec3 0 1 0.
    Definition rv3k : rvec 3 := mk_rvec3 0 0 1.

    Definition cv3i : cvec 3 := mk_cvec3 1 0 0.
    Definition cv3j : cvec 3 := mk_cvec3 0 1 0.
    Definition cv3k : cvec 3 := mk_cvec3 0 0 1.

    (** <v,i> = v.0, <v,j> = v.1, <v,k> = v.2 *)
    Lemma cvdot_v3i_l : forall v : cvec 3, <cv3i, v> = v.0. Proof. intros. cbv; ring. Qed.
    Lemma cvdot_v3j_l : forall v : cvec 3, <cv3j, v> = v.1. Proof. intros. cbv; ring. Qed.
    Lemma cvdot_v3k_l : forall v : cvec 3, <cv3k, v> = v.2. Proof. intros. cbv; ring. Qed.
    Lemma cvdot_v3i_r : forall v : cvec 3, <v, cv3i> = v.0. Proof. intros. cbv; ring. Qed.
    Lemma cvdot_v3j_r : forall v : cvec 3, <v, cv3j> = v.1. Proof. intros. cbv; ring. Qed.
    Lemma cvdot_v3k_r : forall v : cvec 3, <v, cv3k> = v.2. Proof. intros. cbv; ring. Qed.

  End basis_vector.

  (** Dot product (inner-product) in 3D *)
  Section cv3dot.
    Definition cv3dot (a b : cvec 3) := (a.0*b.0 + a.1*b.1 + a.2*b.2)%R.

    Lemma cv3dot_spec : forall v1 v2 : cvec 3, cv3dot v1 v2 = <v1,v2>.
    Proof. intros. cbv. ring. Qed.
  End cv3dot.

  (** Normalization in 3D *)
  Section cv3normalize.
    
    (** normalize v = (v.0/|v|, v.1/|v|, v.2/|v|) *)
    Lemma cv3normalize_eq : forall {n} (v : cvec n),
        let v' := cvnormalize v in
        cvnonzero v ->
        (v'.0 = v.0 / ||v||) /\ (v'.1 = v.1 / ||v||) /\ (v'.2 = v.2 / ||v||).
    Proof.
      intros. unfold v', cvnormalize. cvec2fun.
      autounfold with A. repeat split; try field.
      all: apply cvlen_neq0_iff_neq0; auto.
    Qed.

    Lemma cv3normalize_sqr_eq1 : forall (v : cvec 3),
        let r := ||v|| in
        ((v.0 / r)² + (v.1 / r)² + (v.2 / r)² = 1)%R.
    Proof.
      intros. pose proof (cvnormalize_len1 v).
      unfold cvnormalize in H.
      rewrite <- H.
      unfold cvlen.
      unfold cvdot. cbn. autorewrite with R.
      Admitted. (* 可能太复杂了，下次重新证 *)
  
  End cv3normalize.

  (** Cross product (vector product) of two 3-dim vectors *)
  Section cv3cross.
    (**
   1. 外积的几何学(三角学)意义  ||P×Q|| = ||P|| * ||Q|| * sin α
   2. 外积若不为零，则其与这两个向量都垂直。有两个向量，方向相反。
      根据所选左/右手系来确定方向。
   3. 3D坐标系中的x,y,z轴正方向用 i,j,k 表示，并按 i,j,k 顺序组成一个循环，则：
   (1) 相邻两个向量按相同次序的外积为第三个向量，即 i×j=k, j×k=i, k×i=j。
   (2) 相邻两个向量按相反次序的外积为第三个向量的取反，即 j×i=-k, etc.
     *)
    Definition cv3cross (a b : cvec 3) : cvec 3 :=
      l2cv [a.1 * b.2 - a.2 * b.1;
            a.2 * b.0 - a.0 * b.2;
            a.0 * b.1 - a.1 * b.0]%R.

    Infix "×" := cv3cross : cvec_scope.

    #[export] Instance cv3corss_mor : Proper (meq ==> meq ==> meq) cv3cross.
    Proof.
      simp_proper. intros. hnf in *. mat2fun. intros. rewrite !H,!H0; auto. easy.
    Qed.

    (** v × v = 0 *)
    Lemma cv3cross_self : forall v : cvec 3, v × v == cvec0.
    Proof. lma. Qed.

    (** v1 × v2 = - (v2 × v1) *)
    Lemma cv3cross_anticomm : forall v1 v2 : cvec 3, v1 × v2 == -(v2 × v1).
    Proof. lma. Qed.

    (** (v1 + v2) × v3 = (v1 × v3) + (v2 × v3) *)
    Lemma cv3cross_add_distr_l : forall v1 v2 v3 : cvec 3,
        (v1 + v2) × v3 == (v1 × v3) + (v2 × v3).
    Proof. lma. Qed.

    (** v1 × (v2 + v3) = (v1 × v2) + (v1 × v3) *)
    Lemma cv3cross_add_distr_r : forall v1 v2 v3 : cvec 3,
        v1 × (v2 + v3) == (v1 × v2) + (v1 × v3).
    Proof. lma. Qed.

    (** (- v1) × v2 = - (v1 × v2) *)
    Lemma cv3cross_vopp_l : forall v1 v2 : cvec 3, (-v1) × v2 == - (v1 × v2).
    Proof. lma. Qed.

    (** v1 × (- v2) = - (v1 × v2) *)
    Lemma cv3cross_vopp_r : forall v1 v2 : cvec 3, v1 × (-v2) == - (v1 × v2).
    Proof. lma. Qed.

    (** (a c* v1) × v2 = a c* (v1 × v2) *)
    Lemma cv3cross_cmul_assoc_l : forall (a : R) (v1 v2 : cvec 3),
        (a c* v1) × v2 == a c* (v1 × v2).
    Proof. lma. Qed.

    (** v1 × (a c* v2) = a c* (v1 × v2) *)
    Lemma cv3cross_cmul_assoc_r : forall (a : R) (v1 v2 : cvec 3),
        v1 × (a c* v2) == a c* (v1 × v2).
    Proof. lma. Qed.

    (** <v1 × v2, v3> = <v3 × v1, v2> *)
    Lemma cv3cross_dot_l : forall v1 v2 v3 : cvec 3, <v1 × v2, v3> = <v3 × v1, v2>.
    Proof. intros. cbv. field. Qed.

    (** <v1 × v2, v3> = <v2 × v3, v1> *)
    Lemma cv3cross_dot_r : forall v1 v2 v3 : cvec 3, <v1 × v2, v3> = <v2 × v3, v1>.
    Proof. intros. cbv. field. Qed.

    (** <v1 × v2, v1> = 0 *)
    Lemma cv3cross_dot_same_l : forall v1 v2 : cvec 3, <v1 × v2, v1> = 0.
    Proof. intros. cbv. field. Qed.

    (** <v1 × v2, v2> = 0 *)
    Lemma cv3cross_dot_same_r : forall v1 v2 : cvec 3, <v1 × v2, v2> = 0.
    Proof. intros. cbv. field. Qed.

    (** (v1 × v2) × v1 = v1 × (v2 × v1) *)
    Lemma cv3cross_cross_form1 : forall v1 v2 : cvec 3,
        (v1 × v2) × v1 == v1 × (v2 × v1).
    Proof. lma. Qed.

    (** (v1 × v2) × v1 = <v1,v1> c* v2 - <v1,v2> c* v1 *)
    Lemma cv3cross_cross_form2 : forall v1 v2 : cvec 3,
        (v1 × v2) × v1 == <v1,v1> c* v2 - <v1,v2> c* v1.
    Proof. lma. Qed.

    (** i×j=k, j×k=i, k×i=j *)
    Lemma cv3cross_ij : cv3i × cv3j == cv3k. Proof. lma. Qed.
    Lemma cv3cross_jk : cv3j × cv3k == cv3i. Proof. lma. Qed.
    Lemma cv3cross_ki : cv3k × cv3i == cv3j. Proof. lma. Qed.

    (** j×i=-k, k×j=-i, i×k=-j *)
    Lemma cv3cross_ji : cv3j × cv3i == -cv3k. Proof. lma. Qed.
    Lemma cv3cross_kj : cv3k × cv3j == -cv3i. Proof. lma. Qed.
    Lemma cv3cross_ik : cv3i × cv3k == -cv3j. Proof. lma. Qed.

  End cv3cross.
  Infix "×" := cv3cross : cvec_scope.

  (** Projection component of vector in 3D : 投影分量 *)
  Section cv3proj.

    (** The matrix form of cvproj in 3-dim *)
    Definition cv3proj (a b : cvec 3) : cvec 3 :=
      let x := b.0 in
      let y := b.1 in
      let z := b.2 in
      let M : mat 3 3 :=
        l2m [[x * x; x * y; x * z];
             [x * y; y * y; y * z];
             [x * z; y * z; z * z]]%R in
      (1/<b,b>) c* (M * a).

    Lemma cv3proj_spec : forall a b : cvec 3, cv3proj a b == cvproj a b.
    Proof. lma. Qed.

  End cv3proj.

  (** Perpendicular component of vector in 3D : 垂直分量 *)
  Section cv3perp.
    Open Scope fun_scope.

    (** The perpendicular vector can be get from cross product.
    ref: https://en.wikipedia.org/wiki/Rodrigues%27_rotation_formula.
    利用两次叉乘得到垂直分量的表示。此式在几何上容易理解，但代数上不是很显然。*)
    Definition cv3perp (a b : cvec 3) : cvec 3 := - ((a × b) × b).
    
    Lemma cv3perp_spec : forall (a b : cvec 3), cvunit b -> cvperp a b == cv3perp a b.
    Proof.
      intros. unfold cvperp,cvproj,cv3perp. rewrite H. autorewrite with R.
      (* Why it is a correct algebra equation? 
       I'm confused, and it's just a brute proof. *)
      cvec2fun.
      assert (b.00 ^ 2 = R1 - b.10 ^ 2 - b.20 ^ 2)%R as H1.
      { cbv in H. rewrite <- H. field. }
      lma; cbv; ring_simplify; ring_simplify in H1; rewrite H1; field.
    Qed.
    
  End cv3perp.


  (** Parallel vectors in 3D *)
  Section cv3parallel.
    Local Open Scope fun_scope.

    (** Two vectors in 3D are parallel, can be determined by cross-product.
      That is: v1 ∥ v2 <-> v1 × v2 = 0 *)
    Definition cv3parallel (v1 v2 : cvec 3) : Prop := cvzero (v1 × v2).
    
    Lemma cv3parallel_spec : forall (v1 v2 : cvec 3), v1 ∥ v2 <-> cv3parallel v1 v2.
    Proof.
      intros. cvec2fun. unfold cvparallel,cv3parallel. split; intros.
      - destruct H as [k [H1]].
        cbv. intros. rewrite <- !H; auto; simpl.
        repeat (destruct i; cbv; try ring).
      - cbv in *.
    Abort. (* 叉乘为零，则{1:两行线性相关，对应系数成比例; 2.存在零向量}。*)
  End cv3parallel.


  (** Direction cosine *)
  Section direction_cosine.

    (** Direction cosine of a vector relative to standard basis.
      That is : (cos α, cos β, cos γ) *)
    Definition cv3dc (v : cvec 3) : cvec 3 :=
      let r := ||v|| in l2cv [v.0/r; v.1/r; v.2/r].

    (** The original (lower level) definition as its spec. *)
    Lemma cv3dc_spec : forall (v : cvec 3),
        let v' := cv3dc v in
        let r := ||v|| in 
        (v'.0 = <v,cv3i> / r) /\ v'.1 = (<v,cv3j> / r) /\ v'.2 = (<v,cv3k> / r).
    Proof. intros. rewrite cvdot_v3i_r, cvdot_v3j_r, cvdot_v3k_r; auto. Qed.

    (** dc of a nonzero vector is a unit vector *)
    Lemma cv3dc_unit : forall (v : cvec 3), cvnonzero v -> cvunit (cv3dc v).
    Proof.
      intros. unfold cvunit. cbn. autorewrite with R.
      apply cv3normalize_sqr_eq1.
    Qed.
  End direction_cosine.


  (** Skew-symmetric matrix of 3-dimensions *)
  Section skew.
    
    (** Given matrix is skew-symmetric matrices *)
    Definition cv3skewP (m : mat 3 3) : Prop := (- m)%M == m\T.

    Lemma cv3skewP_spec : forall m : mat 3 3,
        cv3skewP m ->
        let '((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) := m2t_3_3 m in
        (a11 = 0) /\ (a22 = 0) /\ (a33 = 0) /\
          (a12 = -a21 /\ a13 = -a31 /\ a23 = -a32)%R.
    Proof.
      intros. destruct m as [m]; simpl in *. cbv in H. split_intro.
      - epose proof (H 0 0 _ _)%nat. ra.
      - epose proof (H 1 1 _ _)%nat. ra.
      - epose proof (H 2 2 _ _)%nat. ra.
      - epose proof (H 0 1 _ _)%nat. ra.
      - epose proof (H 0 2 _ _)%nat. ra.
      - epose proof (H 1 2 _ _)%nat. ra.
        Unshelve. all: ra.
    Qed.

    (** Convert a vector to its corresponding skew-symmetric matrix *)
    Definition cv3skew (v : cvec 3) : mat 3 3 :=
      l2m [[0; -v.2; v.1];
           [v.2; 0; -v.0];
           [-v.1; v.0; 0]]%R.
    
    Notation "`| v |ₓ" := (cv3skew v).

    (** Convert a skew-symmetric matrix to its corresponding vector *)
    Definition cv3skew2v (m : mat 3 3) : option (cvec 3) :=
      Some (l2cv [m.21; m.02; m.10]).

    Lemma cv3skew_skew2v_id : forall (m : mat 3 3),
        cv3skewP m -> 
        match cv3skew2v m with
        | Some v => cv3skew v == m
        | _ => False
        end.
    Proof.
      intros [m]. simpl. intros. apply cv3skewP_spec in H.
      do 5 destruct H as [? H]. lma. simpl in *.
      autounfold with A. ra.
    Qed.

    Lemma cv3skew2v_skew_id : forall (v : cvec 3),
        match cv3skew2v (cv3skew v) with
        | Some v' => v == v'
        | _ => False
        end.
    Proof.
      intros. cvec2fun. cbv. intros.
      assert (j = 0%nat) by lia. rewrite H1.
      destruct i; try easy.
      destruct i; try easy.
      destruct i; try easy. lia.
    Qed.
    
    Lemma cv3cross_eq_skew_mul : forall (v1 v2 : cvec 3), v1 × v2 == `|v1|ₓ * v2.
    Proof. lma. Qed.

  End skew.
  Notation "`| v |ₓ" := (cv3skew v).


  (** The triple scalar product (or called Mixed products of vectors) *)
  Section cv3mixed.
    
    (** 几何意义：绝对值表示以向量a,b,c为棱的平行六面体的体积，另外若a,b,c组成右手系，
      则混合积的符号为正；若组成左手系，则符号为负。*)
    Definition cv3mixed (a b c : cvec 3) := <a × b, c>.

    (** The mixed product is equal to the determinant *)
    Lemma cv3mixed_eq_det : forall a b c : cvec 3,
        cv3mixed a b c = mdet3 (mconsc a (mconsc b c)).
    Proof. intros [a] [b] [c]. cbv. ring. Qed.

    (** 若混合积≠0，则三向量可构成平行六面体，即三向量不共面，反之也成立。
    所以：三向量共面的充要条件是混合积为零。*)
    Definition cv3coplanar (a b c : cvec 3) := cv3mixed a b c = 0.

    (** Example 7, page 22, 高等数学，第七版 *)
    (** 根据四顶点的坐标，求四面体的体积：四面体ABCD的体积等于AB,AC,AD为棱的平行六面体
    的体积的六分之一 *)
    Definition cv3_volume_of_tetrahedron (A B C D : cvec 3) :=
      let AB := B - A in
      let AC := C - A in
      let AD := D - A in
      ((1/6) * (cv3mixed AB AC AD))%R.
    
  End cv3mixed.


  (** Axis-angle representation *)
  Section rotAxisAngle.

    (** 推导绕任意轴 k̂ 旋转 θ 角度的矩阵 R(k̂,θ)，使得 v' = R(k̂,θ) * v *)

    (** Rotate a vector v in R^3 by an axis described with a unit vector k and 
    an angle θ according to right handle rule, we got the rotated vector as
    follows. This formula is known as Rodrigues formula. *)
    Definition rotAxisAngle (θ : R) (k : cvec 3) (v : cvec 3) : cvec 3 :=
      (cos θ) c* (v - <v,k> c* k) + (sin θ) c* (k×v) + <v,k> c* k.

    (** Proof its correctness *)
    Theorem rotAxisAngle_spec : forall (θ : R) (k : cvec 3) (v : cvec 3),
        let v_para : cvec 3 := cvproj v k in
        let v_perp : cvec 3 := v - v_para in
        let w : cvec 3 := k × v_perp in
        let v_perp' : cvec 3 := (cos θ) c* v_perp + (sin θ) c* w in
        let v' : cvec 3 := v_perp' + v_para in
        cvunit k ->
        v' == rotAxisAngle θ k v.
    Proof.
      intros.
      unfold rotAxisAngle.
      assert (v_para == <v,k> c* k) as H1.
      { unfold v_para, cvproj. rewrite H. f_equiv. autounfold with A. field. }
      assert (v_perp == v - <v,k> c* k) as H2.
      { unfold v_perp. rewrite H1. easy. }
      assert (w == k × v) as H3.
      { unfold w. rewrite H2.
        (* lma. (* auto solvable. But the detail also be shown below. *) *)
        unfold cvsub, Vector.cvsub. rewrite cv3cross_add_distr_r.
        unfold cvcmul. rewrite cvopp_vcmul. rewrite cv3cross_cmul_assoc_r.
        rewrite cv3cross_self. rewrite cvcmul_0_r. rewrite cvadd_0_r. easy. }
      unfold v'. unfold v_perp'. rewrite H1. rewrite H2. rewrite H3. easy.
    Qed.

    (** Another form of the formula *)
    Lemma rotAxisAngle_form1 : forall (θ : R) (k : cvec 3) (v : cvec 3),
        rotAxisAngle θ k v ==
          v *c (cos θ) + (k × v) *c (sin θ) + k *c (<v,k> * (1 - cos θ))%R.
    Proof.
      intros. unfold rotAxisAngle.
      rewrite !cvmulc_eq_vcmul. rewrite cvcmul_vsub. rewrite cvsub_rw.
      rewrite !cvadd_assoc. f_equiv.
      rewrite <- cvadd_assoc. rewrite cvadd_perm. rewrite cvadd_comm. f_equiv.
      unfold Rminus. rewrite Rmult_plus_distr_l. autorewrite with R.
      rewrite cvcmul_add_distr. rewrite cvadd_comm. f_equiv.
      rewrite cvopp_vcmul. rewrite cvcmul_assoc. f_equiv. autounfold with A. ring.
    Qed.

    (** Matrix formula of roation with axis-angle *)
    (* https://en.wikipedia.org/wiki/Rodrigues%27_rotation_formula *)
    Definition rotAxisAngleMat (θ : R) (k : cvec 3) : smat 3 :=
      let K := cv3skew k in
      (mat1 + (sin θ) c* K + (1 - cos θ)%R c* K * K)%M.

    Lemma rotAxisAngleMat_spec : forall (θ : R) (k : cvec 3) (v : cvec 3),
        cvunit k -> (rotAxisAngleMat θ k) * v == rotAxisAngle θ k v.
    Proof.
      intros.
      (* unfold rotAxisAngleMat. *)
      rewrite rotAxisAngle_form1.
      (* v * cosθ + (k × v) * sinθ + k *c (<k,v> * (1-cosθ)) *)
      rewrite <- cvmulc_assoc.
      (* v * cosθ + (k × v) * sinθ + (k *c <k,v>) *c (1-cosθ) *)
      remember (cv3skew k) as K.
      assert ((k *c <k,v>) == v + K * (K * v)).
      {
        assert ((k *c <k,v>) == v - cvperp v k).
        { unfold cvperp. unfold cvproj. rewrite H. rewrite cvdot_comm. lma. }
        rewrite H0. rewrite cv3perp_spec; auto. unfold cv3perp.
        rewrite cv3cross_anticomm. rewrite (cv3cross_anticomm v).
        rewrite cv3cross_vopp_r.
        rewrite !cv3cross_eq_skew_mul. rewrite <- HeqK.
        unfold cvsub. rewrite ?cvopp_vopp. easy. }
      rewrite (cvdot_comm v k). rewrite H0.
      (* v * cosθ + (k × v) * sinθ + (v + K * (K * v)) * (1 - cosθ) *)
      rewrite !cvmulc_eq_vcmul.
      rewrite !cvcmul_vadd_distr.
      rewrite cv3cross_eq_skew_mul.
      rewrite !cvcmul_mmul_assoc_l. rewrite <- !mmul_assoc.
      move2h ((1 - cos θ)%R c* v). rewrite <- !associative.
      assert ((1 - cos θ)%R c* v + cos θ c* v == v) by lma. rewrite H1.
      (* right side is ready *)
      unfold rotAxisAngleMat.
      rewrite !mmul_madd_distr_r. rewrite <- HeqK. f_equiv. f_equiv. apply mmul_1_l.
    Qed.

    (* (** Direct formula of rotation with axis-angle *) *)
    (* Definition rotAxisAngle_direct (θ : R) (k : cvec 3) (v : cvec 3) : cvec 3 := *)
    (*   l2cv 3 *)
    (*     [? *)

  End rotAxisAngle.
  
End v3.
Infix "×" := cv3cross : cvec_scope.
Notation "`| v |ₓ" := (cv3skew v).

  
(* ==================================== *)
(** ** 4D vector theory *)
Section v4.

  (** Standard unit vector in space of 4-dimensions *)
  Section basis_vector.
    Definition cv4i : cvec 4 := mk_cvec4 1 0 0 0.
    Definition cv4j : cvec 4 := mk_cvec4 0 1 0 0.
    Definition cv4k : cvec 4 := mk_cvec4 0 0 1 0.
    Definition cv4l : cvec 4 := mk_cvec4 0 0 0 1.

    Definition rv4i : rvec 4 := mk_rvec4 1 0 0 0.
    Definition rv4j : rvec 4 := mk_rvec4 0 1 0 0.
    Definition rv4k : rvec 4 := mk_rvec4 0 0 1 0.
    Definition rv4l : rvec 4 := mk_rvec4 0 0 0 1.
  End basis_vector.
End v4.


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

  (** Example 4, page 19, 高等数学，第七版 *)
  Goal let a := t2cv_3 (2,1,-1) in
       let b := t2cv_3 (1,-1,2) in
       a × b == t2cv_3 (1,-5,-3).
  Proof. lma. Qed.

  (** Example 5, page 19, 高等数学，第七版 *)
  (** 根据三点坐标求三角形面积 *)
  Definition cv3_area_of_triangle (A B C : cvec 3) :=
    let AB := B - A in
    let AC := C - A in
    ((1/2) * ||AB × AC||)%R.

  (** Example 6, page 20, 高等数学，第七版 *)
  (** 刚体绕轴以角速度 ω 旋转，某点M（OM为向量r⃗）处的线速度v⃗，三者之间的关系*)
  Definition cv3_rotation_model (ω r v : cvec 3) := v = ω × r.

End exercise.


(* ======================================================================= *)
(** * Usage demo *)
Section test.
  Let l1 := [1;2;3].
  Let v1 := @l2rv 2 l1.
  Let v2 := @l2cv 2 l1.
  (* Compute rv2l v1. *)
  (* Compute cv2l v2. *)

  Variable a0 a1 a2 : A.
  Let v3 := t2rv_3 (a0,a1,a2).
  (* Compute rv2l (rvmap v3 fopp). *)
  (* Eval cbn in rv2l (rvmap v3 fopp). *)

  Let v4 := t2cv_3 (a0,a1,a2).
  (* Compute cv2l (cvmap v4 fopp). *)
  (* Eval cbn in cv2l (cvmap v4 fopp). *)
End test.
