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
  3. 使用向量运算的做法
  (1) 使用向量的运算来定义平行和垂直，这样无须三角函数就能判定。
      两向量点乘为零，则它们垂直；两向量叉乘为零向量，则它们平行。
  (2) 在严格证明中，都加上非零向量这一假设条件。
  4. 本文的做法
  (1) vnonzero 类型：表示非零向量。
      在这个类型上定义平行、垂直、角度等。
      换言之，零向量上未定义几何关系。

  二、一些观点
  1. 在三维向量空间中：空间点M <-> 原点O指向M的向量 r⃗=OM=xi+yj+zk <-> 有序数(x,y,z)

  三、额外内容
  1. {R^n, standard-inner-product} is called Euclidean space
     |v| = √<v, v>

 *)

Require Export RealFunction.
Require Export RExt VectorModule.
(* Require Export RowColVectorModule. *)


(* ######################################################################### *)
(** * Vector theory come from common implementations *)

Module Export VectorTheoryR := OrderedFieldVectorTheory OrderedFieldElementTypeR.

Open Scope R_scope.
Open Scope vec_scope.


(* ######################################################################### *)
(** * Vector theory applied to this type *)


(* ======================================================================= *)
(** ** Two vectors are parallel (on vnonzero version) *)

(* 这是使用了子类型 `vnonzero` 来实现 `vpara` 的版本。
   这种做法的特点是：
   1. `vpara`成了等价关系（因为排除了非零向量，而且将非零的条件封装到了类型中）
   2. 同时也带来了一些构造上的繁琐性。因为返回该类型的函数必须要证明其满足非零的条件。
   3. 同时也使得其他相关的函数都要使用 vnonzero 版本，可能过于复杂。
   所以，当一个概念特别有应用需求时，才考虑用这种子类型的方式。
 *)
Module vpara_on_vnonzero.
  
  (** *** Non-zero vector *)
  Record vnonzero n :=
    mkvnonzero {
        vnonzeroV :> vec n ;
        vnonzero_cond : vnonzeroV <> vzero
      }.

  Arguments mkvnonzero {n}.
  Arguments vnonzeroV {n}.
  Arguments vnonzero_cond {n}.

  (** Vector scalar multiplication on `vnonzero` *)
  Definition vnonzero_cmul {n} (k : nonzeroreal) (v : vnonzero n) : vnonzero n.
    refine (mkvnonzero (vcmul k v) _).
    intro. apply vcmul_eq0_imply_k0_or_v0 in H. destruct k, v, H; auto.
  Defined.

  Section vpara.

    (** Two non-zero vectors are parallel, when their components are proportional *)
    Definition vpara {n} (u v : vnonzero n) : Prop :=
      exists k : R, k \.* u = v.

    (* Note: if the coefficient `k` is limited to positive, then two vectors have
     same direction *)

    Infix "//" := vpara (at level 50) : vec_scope.

    (** vparallel is an equivalence relation *)

    Lemma vpara_refl : forall {n} (v : vnonzero n), v // v.
    Proof. intros. exists 1. apply vcmul_1_l. Qed.

    Lemma vpara_sym : forall {n} (u v : vnonzero n), u // v -> v // u.
    Proof.
      intros. destruct H as [k H]. exists (1/k). rewrite <- H.
      rewrite vcmul_assoc. symmetry. rewrite <- vcmul_1_l at 1. f_equal.
      cbv. field. apply vcmul_eq_imply_k_neq0 in H; auto. apply u. apply v.
    Qed.

    Lemma vpara_trans : forall {n} (u v w : vnonzero n), u // v -> v // w -> u // w.
    Proof.
      intros. destruct H as [k1 H1], H0 as [k2 H2].
      exists (k2 * k1)%R. rewrite <- H2,<- H1. rewrite vcmul_assoc. auto.
    Qed.

    (** u // v -> (k \.* u) // v *)
    Lemma vcmul_cvpara_l : forall {n} (k : nonzeroreal) (u v : vnonzero n),
        u // v -> (vnonzero_cmul k u) // v.
    Proof.
      intros. destruct H as [x H]. exists (x/k); simpl. rewrite <- H.
      rewrite vcmul_assoc. f_equal. destruct k. cbv in *. field. auto.
    Qed.

    (** u // v -> u // (k \.* v) *)
    Lemma vcmul_cvpara_r : forall {n} (k : nonzeroreal) (u v : vnonzero n),
        u // v -> u // (vnonzero_cmul k v).
    Proof.
      intros. apply vpara_sym. apply vcmul_cvpara_l; auto.
      apply vpara_sym; auto.
    Qed.

    (** u // v => ∃! k, k * u = v *)
    Lemma vpara_imply_uniqueK : forall {n} (u v : vnonzero n),
        u // v -> (exists ! k, k \.* u = v).
    Proof.
      intros. destruct H as [k H]. exists k. split; auto.
      intros. rewrite <- H in H0. apply vcmul_sameV_imply_eqK in H0; auto.
      apply u.
    Qed.

  End vpara.

  Infix "//" := vpara (at level 50) : vec_scope.

End vpara_on_vnonzero.


(* ======================================================================= *)
(** ** Two vectors are parallel (or called collinear) *)
Section vpara.

  (** Two non-zero vectors are parallel, when their components are proportional *)
  Definition vpara {n} (u v : vec n) : Prop :=
    u <> vzero /\ v <> vzero /\ exists k : R, k \.* u = v.

  (* Note: if the coefficient `k` is limited to positive, then two vectors have
     same direction *)

  Infix "//" := vpara (at level 50) : vec_scope.

  (** vpara is almost an equivalence relation (but the reflexivity law not hold) *)

  Lemma vpara_refl : forall {n} (v : vec n), v <> vzero -> v // v.
  Proof. intros. unfold vpara. repeat split; auto. exists 1. apply vcmul_1_l. Qed.

  Lemma vpara_sym : forall {n} (u v : vec n), u // v -> v // u.
  Proof.
    intros. destruct H as [H1 [H2 [k H3]]]. repeat split; auto.
    exists (1/k). rewrite <- H3.
    rewrite vcmul_assoc. symmetry. rewrite <- vcmul_1_l at 1. f_equal.
    cbv. field. apply vcmul_eq_imply_k_neq0 in H3; auto.
  Qed.

  Lemma vpara_trans : forall {n} (u v w: vec n), u // v -> v // w -> u // w.
  Proof.
    intros. destruct H as [H1 [H2 [k1 H3]]], H0 as [H4 [H5 [k2 H6]]].
    repeat split; auto.
    exists (k2 * k1). rewrite <- H6,<- H3. rewrite vcmul_assoc. auto.
  Qed.

  (** u // v => ∃! k, k * u = v *)
  Lemma vpara_imply_uniqueK : forall {n} (u v : vec n),
      u // v -> (exists ! k, k \.* u = v).
  Proof.
    intros. destruct H as [H1 [H2 [k H3]]]. exists k. split; auto.
    intros. rewrite <- H3 in H. apply vcmul_sameV_imply_eqK in H; auto.
  Qed.

  (** u // v -> (k \.* u) // v *)
  Lemma vcmul_cvpara_l : forall {n} k (u v : vec n),
      k <> 0 -> u // v -> k \.* u // v.
  Proof.
    intros. destruct H0 as [H1 [H2 [k1 H3]]]. repeat split; auto.
    - intro. apply vcmul_eq0_imply_k0_or_v0 in H0. destruct H0; auto.
    - exists (k1/k); simpl. rewrite <- H3. rewrite vcmul_assoc. f_equal.
      cbv. field. auto.
  Qed.

  (** u // v -> u // (k \.* v) *)
  Lemma vcmul_cvpara_r : forall {n} k (u v : vec n),
      k <> 0 -> u // v -> u // (k \.* v).
  Proof.
    intros. apply vpara_sym. apply vcmul_cvpara_l; auto.
    apply vpara_sym; auto.
  Qed.

End vpara.

Infix "//" := vpara (at level 50) : vec_scope.


(* ======================================================================= *)
(** ** Length of a vector *)

(** Length (magnitude) of a vector, is derived by inner-product *)
Definition vlen {n} (v : vec n) : R := sqrt (<v, v>).

Notation "|| v ||" := (vlen v) : vec_scope.

Section vlen_props.
  Notation seqsum := (@seqsum _ Rplus 0).

  (** 0 <= ||v|| *)
  Lemma vlen_ge0 : forall {n} (v : vec n), 0 <= || v ||.
  Proof. intros. unfold vlen. ra. Qed.
  
  (** Length equal iff dot-product equal *)
  Lemma vlen_eq_iff_dot_eq : forall {n} (u v : vec n), ||u|| = ||v|| <-> <u, u> = <v, v>.
  Proof.
    intros. unfold vlen. split; intros H; try rewrite H; auto.
    apply sqrt_inj in H; auto; apply vdot_ge0.
  Qed.

  (** ||vzero|| = 0 *)
  Lemma vlen_vzero : forall {n}, || @vzero n || = 0.
  Proof. intros. unfold vlen. rewrite vdot_0_l. ra. Qed.

  (** ||v|| = 0 <-> v = 0 *)
  Lemma vlen_eq0_iff_eq0 : forall {n} (v : vec n), ||v|| = 0 <-> v = vzero.
  Proof.
    intros. unfold vlen. split; intros.
    - apply vdot_eq0_iff_vzero. apply sqrt_eq_0 in H; auto. apply vdot_ge0.
    - rewrite H. rewrite vdot_0_l. cbv. apply sqrt_0.
  Qed.

  (** ||v|| <> 0 <-> v <> 0 *)
  Lemma vlen_neq0_iff_neq0 : forall {n} (v : vec n), ||v|| <> 0 <-> v <> vzero.
  Proof. intros. rewrite vlen_eq0_iff_eq0. easy. Qed.

  (** v <> vzero -> 0 < ||v|| *)
  Lemma vlen_gt0 : forall {n} (v : vec n), v <> vzero -> 0 < ||v||.
  Proof. intros. pose proof (vlen_ge0 v). apply vlen_neq0_iff_neq0 in H; ra. Qed.

  (** <v, v> = ||v||² *)
  Lemma vdot_same : forall {n} (v : vec n), <v, v> = ||v||².
  Proof. intros. unfold vlen. rewrite Rsqr_sqrt; auto. apply vdot_ge0. Qed.
  
  (** 0 <= <v, v> *)
  Lemma vdot_same_ge0 : forall {n} (v : vec n), 0 <= <v, v>.
  Proof. intros. rewrite vdot_same. ra. Qed.

  (** v <> vzero -> <v, v> <> 0*)
  Lemma vdot_same_neq0 : forall {n} (v : vec n), v <> vzero -> <v, v> <> 0.
  Proof. intros. rewrite vdot_same. apply vlen_neq0_iff_neq0 in H. ra. Qed.

  (** v <> vzero -> 0 < <v, v> *)
  Lemma vdot_same_gt0 : forall {n} (v : vec n), v <> vzero -> 0 < <v, v>.
  Proof.
    intros. pose proof (vdot_same_ge0 v). pose proof (vdot_same_neq0 v H). ra.
  Qed.
  
  (** || v || = 1 <-> <v, v> = 1 *)
  Lemma vlen_eq1_iff_vdot1 : forall {n} (v : vec n), ||v|| = 1 <-> <v, v> = 1.
  Proof. intros. unfold vlen. split; intros; hnf in *. ra. rewrite H. ra. Qed.

  (** || - v|| = || v || *)
  Lemma vlen_vopp : forall n (v : vec n), || - v|| = || v ||.
  Proof.
    intros. unfold vlen. f_equal. rewrite vdot_vopp_l,vdot_vopp_r.
    autorewrite with R. auto.
  Qed.
  
  (** ||k \.* v|| = |k| * ||v|| *)
  Lemma vlen_vcmul : forall n k (v : vec n), ||k \.* v|| = |k| * ||v||.
  Proof.
    intros. unfold vlen. rewrite vdot_vcmul_l, vdot_vcmul_r.
    rewrite <- Rmult_assoc.
    rewrite sqrt_mult_alt; ra. f_equal. autorewrite with R. ra.
  Qed.
  
  (** ||u + v||² = ||u||² + ||v||² + 2 * <u, v> *)
  Lemma vlen2_vadd : forall {n} (u v : vec n),
      ||(u + v)||² = (||u||² + ||v||² + 2 * <u, v>)%R.
  Proof.
    intros. rewrite <- !vdot_same.
    rewrite !vdot_vadd_l, !vdot_vadd_r.
    rewrite (vdot_comm v u).
    autounfold with A. ring.
  Qed.
  
  (** ||u - v||² = ||u||² + ||v||² - 2 * <u, v> *)
  Lemma vlen2_vsub : forall {n} (u v : vec n),
      ||(u - v)||² = (||u||² + ||v||² - 2 * <u, v>)%R.
  Proof.
    intros. rewrite <- !vdot_same. unfold vsub.
    rewrite !vdot_vadd_l, !vdot_vadd_r.
    rewrite !vdot_vopp_l, !vdot_vopp_r. rewrite (vdot_comm v u).
    autounfold with A. ring.
  Qed.

  (** <u, v>² <= <u, u> * <v, v> *)
  Lemma vdot_sqr_le : forall {n} (u v : vec n), <u, v>² <= <u, u> * <v, v>.
  Proof.
    intros. unfold vdot,Vector.vdot,Vector.vsum,Vector.vmap2.
    autounfold with A. destruct n.
    - cbv; ra.
    - (* Convert dependent "vec" to non-dependent "nat -> A", by "Abstraction"  *)
      remember (fun i => u (nat2finS i)) as f.
      remember (fun i => v (nat2finS i)) as g.
      replace (fseqsum (fun i => (u i * v i)))
        with (seqsum (fun i => f i * g i) (S n)); auto.
      2:{ rewrite ?Heqf,?Heqg. rewrite !fseqsum_to_seqsum_form3. auto. }
      replace (fseqsum (fun i => u i * u i))
        with (seqsum (fun i => f i * f i) (S n)).
      2:{ rewrite ?Heqf,?Heqg. rewrite !fseqsum_to_seqsum_form3. auto. }
      replace (fseqsum (fun i => v i * v i))
        with (seqsum (fun i => g i * g i) (S n)).
      2:{ rewrite ?Heqf,?Heqg. rewrite !fseqsum_to_seqsum_form3. auto. }
      clear.
      apply seqsum_SqrMul_le_MulSqr.
  Qed.

  (** <u, v>² / (<u, u> * <v, v>) <= 1. *)
  Lemma vdot_sqr_le_form2 : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero -> <u, v>² / (<u, u> * <v, v>) <= 1.
  Proof.
    intros.
    pose proof (vdot_gt0 u H). pose proof (vdot_gt0 v H0).
    apply Rdiv_le_1; ra. apply vdot_sqr_le.
  Qed.

  (* 柯西.许西尔兹不等式，Cauchy-Schwarz Inequality *)
  (** |<u, v>| <= ||u|| * ||v|| *)
  Lemma vdot_abs_le : forall {n} (u v : vec n), |<u, v>| <= ||u|| * ||v||.
  Proof.
    intros. pose proof (vdot_sqr_le u v).
    rewrite !vdot_same in H.
    replace ((||u||)² * (||v||)²) with ((||u|| * ||v||)²) in H; [| cbv;ring].
    apply Rsqr_le_abs_0 in H.
    replace (|((||u||) * (||v||))|) with (||u|| * ||v||) in H; auto.
    rewrite !Rabs_right; auto.
    pose proof (vlen_ge0 u). pose proof (vlen_ge0 v). ra.
  Qed.

  (** <u, v> <= ||u|| * ||v|| *)
  Lemma vdot_le_mul_vlen : forall {n} (u v : vec n), <u, v> <= ||u|| * ||v||.
  Proof. intros. pose proof (vdot_abs_le u v). apply Rabs_le_rev in H. ra. Qed.

  (** - ||u|| * ||v|| <= <u, v> *)
  Lemma vdot_ge_neg_mul_vlen : forall {n} (u v : vec n), (- ||u|| * ||v||)%R <= <u, v>.
  Proof. intros. pose proof (vdot_abs_le u v). apply Rabs_le_rev in H. ra. Qed.
    
  
  (** ||u + v|| <= ||u|| + ||v|| *)
  (* 任意维度“三角形”两边长度之和大于第三边长度 *)
  Lemma vlen_vadd_le : forall {n} (u v : vec n), ||(u + v)|| <= ||u|| + ||v||.
  Proof.
    intros. apply Rsqr_incr_0_var.
    2:{ unfold vlen; ra. }
    rewrite Rsqr_plus. rewrite <- !vdot_same.
    replace (<u + v, u + v>)
      with ((<u, u>) + (<v, v>) + (2 * (<u, v>)))%A.
    2:{ rewrite vdot_vadd_l,!vdot_vadd_r.
        rewrite (vdot_comm v u). autounfold with A; ra. }
    apply Rplus_le_compat_l.
    rewrite !associative. apply Rmult_le_compat_l; ra.
    pose proof (vdot_abs_le u v). unfold Rabs in H.
    destruct Rcase_abs; ra.
  Qed.
  
  (** 这个性质不成立，有一个例子：相反向量长度相等且平行，但不相等。*)
  Lemma v_eq_iff_len_parallel : forall {n} (u v : vec n),
      (||u|| = ||v|| /\ u // v) <-> u = v.
  Abort.

End vlen_props.


(* ======================================================================= *)
(** ** Unit vector *)
Section vunit.

  (** A unit vector u is a vector whose length equals one.
      Here, we use the square of length instead of length directly,
      but this is reasonable with the proof of vunit_spec.
   *)
  Definition vunit {n} (v : vec n) : Prop := <v, v> = 1.

  (** Verify the definition is reasonable *)
  Lemma vunit_spec : forall {n} (v : vec n), vunit v <-> ||v|| = 1.
  Proof. intros. split; intros; apply vlen_eq1_iff_vdot1; auto. Qed.
  
  (** (bool version) *)
  Definition vunitb {n} (v : vec n) : bool := (<v, v> =? 1)%R.

  (** The length of a unit vector is one *)
  Lemma vlen_vunit : forall {n} (v : vec n), vunit v -> ||v|| = 1.
  Proof. intros. apply vlen_eq1_iff_vdot1. auto. Qed.

  (** The unit vector cannot be zero vector *)
  Lemma vunit_neq0 : forall {n} (v : vec n), vunit v -> v <> vzero.
  Proof.
    intros. intro. rewrite H0 in H. unfold vunit in H.
    rewrite vdot_0_l in H. ra.
  Qed.

  (** vunit v <-> vunit (vopp u). *)
  Lemma vopp_vunit : forall {n} (v : vec n), vunit (vopp v) <-> vunit v.
  Proof.
    intros. unfold vunit. rewrite <- !vlen_eq1_iff_vdot1.
    rewrite vlen_vopp. easy.
  Qed.

  (** If column of a and column of b all are unit, 
    then column of (a * b) is also unit *)
  (*   a : mat 2 2 *)
  (* a1 : vunit (mat2col a 0) *)
  (* a2 : vunit (mat2col a 1) *)
  (* a3 : vorth (mat2col a 0) (mat2col a 1) *)
  (* b1 : vunit (mat2col b 0) *)
  (* b2 : vunit (mat2col b 1) *)
  (* b3 : vorth (mat2col b 0) (mat2col b 1) *)
  (* ============================ *)
  (* vunit (mat2col (a * b) 0) *)
End vunit.


(* ======================================================================= *)
(** ** Vector normalization *)
Section vnorm.

  (** Normalization of a non-zero vector v.
      That is, make a unit vector that in the same directin as v. *)
  Definition vnorm {n} (v : vec n) : vec n := (1/ ||v||) \.* v.

  (** The component of a normalized vector is equivalent to its original component 
      divide the vector's length *)
  Lemma vnth_vnorm : forall {n} (v : vec n) i,
      v <> vzero -> (vnorm v) $ i = (v $ i) / ||v||.
  Proof.
    intros. unfold vnorm. rewrite vnth_vcmul; auto.
    autounfold with A. field. apply vlen_neq0_iff_neq0; auto.
  Qed.

  (** Unit vector is fixpoint of vnorm operation *)
  Lemma vnorm_vunit_fixpoint : forall {n} (v : vec n),
      vunit v -> vnorm v = v.
  Proof.
    intros. unfold vnorm. rewrite (vunit_spec v) in H. rewrite H.
    autorewrite with R. apply vcmul_1_l.
  Qed.

  (** Normalized vector is non-zero  *)
  Lemma vnorm_vnonzero : forall {n} (v : vec n), v <> vzero -> vnorm v <> vzero.
  Proof.
    intros. unfold vnorm. intro.
    apply vcmul_eq0_imply_k0_or_v0 in H0. destruct H0; auto.
    apply vlen_neq0_iff_neq0 in H. unfold Rdiv in H0.
    rewrite Rmult_1_l in H0. apply Rinv_neq_0_compat in H. easy.
  Qed.

  (* The length of a normalized vector is one *)
  Lemma vnorm_len1 : forall {n} (v : vec n), v <> vzero -> ||vnorm v|| = 1.
  Proof.
    (* v̂ = v/|v|, |v̂| = sqrt (v/|v| ⋅ v/|v|) = sqrt ((v⋅v) / (|v|*|v|))
     = sqrt(v⋅v) / |v| = |v| / |v| = 1 *)
    intros. unfold vnorm. unfold vlen.
    rewrite !vdot_vcmul_l, !vdot_vcmul_r. rewrite vdot_same.
    remember (||v||). autounfold with A. autorewrite with R.
    apply sqrt_eq1_imply_eq1_rev.
    assert (|r| = r). { pose proof (vlen_ge0 v). subst. ra. }
    rewrite H0. cbv. field. subst. apply vlen_neq0_iff_neq0; auto.
  Qed.

  (** Normalized vector are unit vector *)
  Lemma vnorm_unit : forall {n} (v : vec n), v <> vzero -> vunit (vnorm v).
  Proof. intros. apply vunit_spec. apply vnorm_len1; auto. Qed.

  (** Normalized vector is parallel to original vector *)
  Lemma vnorm_vpara : forall {n} (v : vec n), v <> vzero -> (vnorm v) // v.
  Proof.
    intros. repeat split; auto.
    - apply vnorm_vnonzero; auto.
    - exists (||v||). unfold vnorm. rewrite vcmul_assoc.
      apply vcmul_same_if_k1_or_v0. left.
      autounfold with A. field. apply vlen_neq0_iff_neq0; auto.
  Qed.

  Lemma vnorm_spec : forall {n} (v : vec n),
      v <> vzero -> (||vnorm v|| = 1 /\ (vnorm v) // v).
  Proof. intros. split. apply vnorm_len1; auto. apply vnorm_vpara; auto. Qed.

  (** Normalization is idempotent *)
  Lemma vnorm_idem : forall {n} (v : vec n),
      v <> vzero -> vnorm (vnorm v) = vnorm v.
  Proof. intros. apply vnorm_vunit_fixpoint. apply vnorm_unit; auto. Qed.

  (** k <> 0 -> vnorm (k \.* v) = (sign k) \.* (vnorm v) *)
  Lemma vnorm_vcmul : forall {n} k (v : vec n),
      k <> 0 -> v <> vzero -> vnorm (k \.* v) = sign k \.* (vnorm v).
  Proof.
    intros. unfold vnorm. rewrite vlen_vcmul. rewrite !vcmul_assoc.
    f_equal. unfold sign. autounfold with A. apply vlen_neq0_iff_neq0 in H0.
    bdestruct (0 <? k).
    - rewrite Rabs_right; ra. field. split; auto.
    - bdestruct (k =? 0). easy. rewrite Rabs_left; ra. field. auto.
  Qed.

  (** k > 0 -> vnorm (k \.* v) = vnorm v *)
  Lemma vnorm_vcmul_k_gt0 : forall {n} k (v : vec n),
      k > 0 -> v <> vzero -> vnorm (k \.* v) = vnorm v.
  Proof.
    intros. rewrite vnorm_vcmul; auto; ra. rewrite sign_gt0; auto.
    apply vcmul_1_l.
  Qed.

  (** k < 0 -> vnorm (k \.* v) = vnorm v *)
  Lemma vnorm_vcmul_k_lt0 : forall {n} k (v : vec n),
      k < 0 -> v <> vzero -> vnorm (k \.* v) = - vnorm v.
  Proof.
    intros. rewrite vnorm_vcmul; auto; ra. rewrite sign_lt0; auto.
    rewrite (vcmul_opp 1). f_equal. apply vcmul_1_l.
  Qed.
  
End vnorm.


(* ======================================================================= *)
(** ** Angle between two vectors *)
Section vangle.

  (** The angle from vector u to vector v, Here, θ ∈ [0,π] *)
  Definition vangle {n} (u v : vec n) : R := acos (<vnorm u, vnorm v>).
  
  Infix "/_" := vangle (at level 60) : vec_scope.

  (** The angle of between any vector and itself is 0 *)
  Lemma vangle_self_eq0 : forall {n} (v : vec n), v <> vzero -> v /_ v = 0.
  Proof.
    intros. unfold vangle. rewrite vdot_same.
    rewrite vnorm_len1; auto. autorewrite with R. apply acos_1.
  Qed.

  (** Angle is commutative *)
  Lemma vangle_comm : forall {n} (u v : vec n), u /_ v = v /_ u.
  Proof. intros. unfold vangle. rewrite vdot_comm. auto. Qed.
  
  (** The angle between (1,0,0) and (1,1,0) is 45 degree, i.e., π/4 *)
  (* Remark: Here, we can finish a demo proof with a special value π/4,
     but actual cases maybe have any value, it is hard to finished in Coq.
     Because the construction of {sqrt, acos, PI, etc} is complex. *)
  Fact vangle_pi4 : (@l2v 3 [1;0;0]) /_ (l2v [1;1;0]) = PI/4.
  Proof.
    rewrite <- acos_inv_sqrt2.
    compute. f_equiv. autorewrite with R. auto.
  Qed.

  (** 单位向量的点积介于[-1,1] *)
  Lemma vdot_unit_bound : forall {n} (u v : vec n),
      vunit u -> vunit v -> -1 <= <u, v> <= 1.
  Proof.
    intros.
    pose proof (vdot_abs_le u v).
    pose proof (vdot_ge_neg_mul_vlen u v).
    apply vlen_vunit in H,H0. rewrite H,H0 in H1,H2.
    unfold Rabs in H1. destruct Rcase_abs; ra.
  Qed.

  (** 单位化后的非零向量的点积介于 [-1,1] *)
  Lemma vdot_vnorm_bound : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero -> -1 <= <vnorm u, vnorm v> <= 1.
  Proof. intros. apply vdot_unit_bound; apply vnorm_unit; auto. Qed.
  
  (** The relation between dot product and the cosine of angle *)
  (* Note that we needn't the vectors are non-zero *)
  Lemma vdot_eq_cos_angle : forall {n} (u v : vec n),
      <u, v> = (||u|| * ||v|| * cos (u /_ v))%R.
  Proof.
    intros. destruct (Aeqdec u vzero).
    - subst. rewrite vdot_0_l, vlen_vzero. rewrite Rmult_0_l. auto.
    - destruct (Aeqdec v vzero).
      + subst. rewrite vdot_0_r, vlen_vzero. rewrite Rmult_0_l,Rmult_0_r. auto.
      + unfold vangle. rewrite cos_acos.
        * unfold vnorm. rewrite <- vdot_vcmul_r. rewrite <- vdot_vcmul_l.
          rewrite !vcmul_assoc. autounfold with A.
          replace ((||u||) * (1 / (||u||))) with 1;
            [|field; apply vlen_neq0_iff_neq0; auto].
          replace ((||v||) * (1 / (||v||))) with 1;
            [|field; apply vlen_neq0_iff_neq0; auto].
          rewrite !vcmul_1_l. auto.
        * apply vdot_vnorm_bound; auto.
  Qed.
  
  (** The cosine law *)
  Theorem CosineLaw : forall {n} (u v : vec n),
      ||(u - v)||² = (||u||² + ||v||² - 2 * ||u|| * ||v|| * cos (u /_ v))%R.
  Proof.
    intros. rewrite vlen2_vsub. f_equal. f_equal.
    rewrite vdot_eq_cos_angle. auto.
  Qed.

  (* A variant form *)
  Theorem CosineLaw_var : forall {n} (u v : vec n),
      ||(u + v)||² = (||u||² + ||v||² + 2 * ||u|| * ||v|| * cos (u /_ v))%R.
  Proof.
    intros. rewrite vlen2_vadd. f_equal. f_equal.
    rewrite vdot_eq_cos_angle. auto.
  Qed.
  
  (** The relation between dot product and the cosine of angle *)
  Theorem vdot_eq_cos_angle_by_CosineLaw : forall {n} (u v : vec n),
      <u, v> = (||u|| * ||v|| * cos (u /_ v))%R.
  Proof.
    intros.
    pose proof (vlen2_vsub u v).
    pose proof (CosineLaw u v). ra.
  Qed.

  (** 0 <= u /_ v <= PI *)
  Lemma vangle_bound : forall {n} (u v : vec n), 0 <= u /_ v <= PI.
  Proof. intros. unfold vangle. apply acos_bound. Qed.

  (** <u, v> = ||u|| * ||v|| -> u /_ v = 0 *)
  Lemma vdot_eq_mul_vlen_imply_angle_0 : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero -> (<u, v> = ||u|| * ||v||) -> u /_ v = 0.
  Proof.
    intros. unfold vangle.
    match goal with | |- acos ?a = _ => replace a with 1 end.
    apply acos_1. unfold vnorm. rewrite vdot_vcmul_l,vdot_vcmul_r.
    rewrite H1. autounfold with A. field.
    apply vlen_neq0_iff_neq0 in H,H0. auto.
  Qed.
  
  (** <u, v> = - ||u|| * ||v|| -> u /_ v = π *)
  Lemma vdot_eq_neg_mul_vlen_imply_angle_pi : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero -> (<u, v> = - ||u|| * ||v||)%R -> u /_ v = PI.
  Proof.
    intros. unfold vangle.
    match goal with | |- acos ?a = _ => replace a with (-1)%R end.
    apply acos_neg1. unfold vnorm. rewrite vdot_vcmul_l,vdot_vcmul_r.
    rewrite H1. autounfold with A. field.
    apply vlen_neq0_iff_neq0 in H,H0. auto.
  Qed.

  (** <u, v> = 0 -> u /_ v = π/2 *)
  Lemma vdot_eq_0_imply_angle_pi2 : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero -> (<u, v> = 0) -> u /_ v = PI/2.
  Proof.
    intros. unfold vangle.
    match goal with | |- acos ?a = _ => replace a with 0 end.
    apply acos_0. unfold vnorm. rewrite vdot_vcmul_l,vdot_vcmul_r.
    rewrite H1. autounfold with A. field.
    apply vlen_neq0_iff_neq0 in H,H0. auto.
  Qed.

  (** v /_ v = 0 *)
  Lemma vdot_same_imply_angle_0 : forall {n} (v : vec n), v <> vzero -> v /_ v = 0.
  Proof.
    intros. apply vdot_eq_mul_vlen_imply_angle_0; auto.
    rewrite vdot_same. ra.
  Qed.

  (** 0 <= sin (u /_ v) *)
  Lemma sin_vangle_ge0 : forall {n} (u v : vec n), 0 <= sin (u /_ v).
  Proof. intros. apply sin_ge_0; apply vangle_bound. Qed.
  
  (** θ ≠ 0 -> θ ≠ π -> 0 < sin (u /_ v) *)
  Lemma sin_vangle_gt0 : forall {n} (u v : vec n),
      u /_ v <> 0 -> u /_ v <> PI -> 0 < sin (u /_ v).
  Proof. intros. pose proof (vangle_bound u v). apply sin_gt_0; ra. Qed.

  (** u /_ v = 0 <-> u and v 同向平行 *)
  Lemma vangle_eq0_sameDir : forall {n} (u v : vec n),
      u <> vzero -> v <> vzero ->
      (u /_ v = 0 <-> (exists k : R, k > 0 /\ k \.* u = v)).
  Proof.
    intros. unfold vangle. split; intros.
    2:{
      destruct H1 as [k [H11 H12]]. rewrite <- H12.
      rewrite <- acos_1. f_equal. unfold vnorm.
      rewrite vcmul_assoc, !vdot_vcmul_l, !vdot_vcmul_r.
      rewrite vlen_vcmul. rewrite vdot_same. rewrite Rabs_right; ra.
      autounfold with A. field. apply vlen_neq0_iff_neq0 in H,H0. ra. }
    1:{
      rewrite <- acos_1 in H1.
      apply acos_inj in H1; ra.
      2:{ apply vdot_vnorm_bound; auto. }
      1:{
        (*        
           u /_ v = 0 -> acos(<u', v'>) = 0, where u',v' is normalized u,v.
           then <u', v'> = 1. that is <vnorm u, vnorm v> = 1,
           then (1/(|u|*|v|)) * <u, v> = 1
           可以借助投影来表明 u和v是k倍的关系
         *)
        
        (* Search vpara.  *)
        (* exists (||u|| * ||v||)%R. split. *)
        (* * pose proof (vlen_gt0 u H). pose proof (vlen_gt0 v H0). ra. *)
        (* * rewrite vdot_eq_cos_angle in H1. *)
        (*   Search vlen. *)
  Abort.

  (** u /_ w = (u /_ v) + (v /_ w) *)
  Lemma vangle_add : forall {n} (u v w : vec n),
      u /_ v < PI ->
      v /_ w < PI ->
      u /_ w = ((u /_ v) + (v /_ w))%R.
  Proof.
  (** 由于目前 vangle 的值域是 [0,π]，暂不能表示 [0,2π)，所以该性质有点困难。
      有扩展了值域为 [0,2π) 的 vangle 可做参考。
      在3D中，需要增加共面的条件。*)
    intros. unfold vangle in *.
  Abort.

  
  Lemma Rdiv_1_neq_0_compat : forall r : R, r <> 0 -> 1 / r <> 0.
  Proof. intros. pose proof (Rinv_neq_0_compat r H). ra. Qed.

  
  (* (** 给定两个向量，若将这两个向量同时旋转θ角，则向量之和在旋转前后的夹角也是θ。*) *)
  (* Lemma vangle_vadd : forall (u v u' v' : vec 2), *)
  (*     vnonzero u -> vnonzero v -> *)
  (*     ||v1|| = ||v1'|| -> ||v2|| = ||v2'|| -> *)
  (*     u /_ v = u' /_ v' -> *)
  (*     u + v /_ u' + v' = u /_ u'. *)
  (* Proof. *)
  (*   intros u v u' v' Hneq0_u Hneq0_v2 Hlen_eq_11' Hlen_eq_22' Hangle_eq. *)
  (*   assert (||v1|| <> 0) as Hlen_neq0_v1. *)
  (*   { apply vlen_neq0_iff_neq0; auto. } *)
  (*   assert (||v2|| <> 0) as Hlen_neq0_v2. *)
  (*   { apply vlen_neq0_iff_neq0; auto. } *)
  (*   assert (vnonzero u') as Hneq0_v1'. *)
  (*   { apply vlen_neq0_iff_neq0 in Hneq0_v1. apply vlen_neq0_iff_neq0. ra. } *)
  (*   assert (vnonzero v') as Hneq0_v2'. *)
  (*   { apply vlen_neq0_iff_neq0 in Hneq0_v2. apply vlen_neq0_iff_neq0. ra. } *)
  (*   unfold vangle in *. f_equiv. *)
  (*   apply acos_inj in Hangle_eq; try apply vdot_vnorm_bound; auto. *)
  (*   unfold vnorm in *. *)
  (*   rewrite !vdot_vcmul_l, !vdot_vcmul_r in *. *)
  (*   (* remember (||(u + v)%V||) as r1. *) *)
  (*   (* remember (||(v1' + v')%V||) as r1'. *) *)
  (*   rewrite !vdot_vadd_distr_l, !vdot_vadd_distr_r. *)
  (*   rewrite <- Hlen_eq_11', <- Hlen_eq_22' in *. *)
  (*   assert (<v1, v2> = <v1', v2'>). *)
  (*   { apply Rmult_eq_reg_l with (r:=(1/(||v2||))). *)
  (*     apply Rmult_eq_reg_l with (r:=(1/(||v1||))). auto. *)
  (*     all: apply Rdiv_1_neq_0_compat; auto. } *)
  (*   (* 以下，尝试自动证明，因为我暂时无法手动证明 *) *)
  (*   Open Scope fun_scope. *)
  (*   vec2fun. cbv in *. autorewrite with R in *. *)
  (*   remember (v1.11) as a1; remember (v1.21) as a2; remember (v1.31) as a3. *)
  (*   remember (v2.11) as b1; remember (v2.21) as b2; remember (v2.31) as b3. *)
  (*   rename u' into v3. rename v' into v4. *)
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

  (** 给定两个向量，若将这两个向量同时旋转θ角，则向量之和在旋转前后的夹角也是θ。*)
  Lemma vangle_vadd : forall {n} (u v u' v' : vec n),
      u <> vzero -> v <> vzero ->
      ||u|| = ||u'|| -> ||v|| = ||v'|| ->
      u /_ v = u' /_ v' ->
      (u + v) /_ (u' + v') = u /_ u'.
  Proof.
    intros.
    unfold vangle in *.
    apply acos_inj in H3.
    f_equal. unfold vnorm in *.
    rewrite !vdot_vcmul_l, !vdot_vcmul_r in *.
    rewrite !vdot_vadd_l, !vdot_vadd_r in *.
    autounfold with A in *. rewrite <- H1, <- H2 in *.
    remember (||u||) as r1.
    remember (||v||) as r2.
    rewrite <- !associative in H3.
    rewrite <- !associative.
    
  Abort.
    (* intros u v u' v' Hneq0_u Hneq0_v2 Hlen_eq_11' Hlen_eq_22' Hangle_eq. *)
    (* assert (||v1|| <> 0) as Hlen_neq0_v1. *)
    (* { apply vlen_neq0_iff_neq0; auto. } *)
    (* assert (||v2|| <> 0) as Hlen_neq0_v2. *)
    (* { apply vlen_neq0_iff_neq0; auto. } *)
    (* assert (vnonzero u') as Hneq0_v1'. *)
    (* { apply vlen_neq0_iff_neq0 in Hneq0_v1. apply vlen_neq0_iff_neq0. ra. } *)
    (* assert (vnonzero v') as Hneq0_v2'. *)
    (* { apply vlen_neq0_iff_neq0 in Hneq0_v2. apply vlen_neq0_iff_neq0. ra. } *)
    (* unfold vangle in *. f_equiv. *)
    (* apply acos_inj in Hangle_eq; try apply vdot_vnorm_bound; auto. *)
    (* unfold vnorm in *. *)
    (* rewrite !vdot_vcmul_l, !vdot_vcmul_r in *. *)
    (* (* remember (||(u + v)%V||) as r1. *) *)
    (* (* remember (||(v1' + v')%V||) as r1'. *) *)
    (* rewrite !vdot_vadd_distr_l, !vdot_vadd_distr_r. *)
    (* rewrite <- Hlen_eq_11', <- Hlen_eq_22' in *. *)
    (* assert (<v1, v2> = <v1', v2'>). *)
    (* { apply Rmult_eq_reg_l with (r:=(1/(||v2||))). *)
    (*   apply Rmult_eq_reg_l with (r:=(1/(||v1||))). auto. *)
    (*   all: apply Rdiv_1_neq_0_compat; auto. } *)
    (* (* 以下，尝试自动证明，因为我暂时无法手动证明 *) *)
    (* Open Scope fun_scope. *)
    (* vec2fun. cbv in *. autorewrite with R in *. *)
    (* remember (v1.11) as a1; remember (v1.21) as a2; remember (v1.31) as a3. *)
    (* remember (v2.11) as b1; remember (v2.21) as b2; remember (v2.31) as b3. *)
    (* rename u' into v3. rename v' into v4. *)
    (* remember (v3.11) as c1; remember (v3.21) as c2; remember (v3.31) as c3. *)
    (* remember (v4.11) as d1; remember (v4.21) as d2; remember (v4.31) as d3. *)
    (* autorewrite with R. autorewrite with R in H. *)
    (* generalize Hlen_eq_11' Hlen_eq_22' H. clear. *)
    (* intros. *)
    (* clear. *)
    

  (** a > 0 -> (a \.* u) /_ v = u /_ v *)
  Lemma vangle_vcmul_l_gt0 : forall {n} (u v : vec n) (a : R),
      a > 0 -> u <> vzero -> v <> vzero -> (a \.* u) /_ v = u /_ v.
  Proof.
    intros. unfold vangle. rewrite vnorm_vcmul; auto.
    rewrite vdot_vcmul_l. unfold sign. bdestruct (0 <? a); ra.
    - rewrite !Rmult_1_l. auto.
    - bdestruct (a =? 0); ra.
  Qed.

  (** a < 0 -> (a \.* u) /_ v = PI - u /_ v *)
  Lemma vangle_vcmul_l_lt0 : forall {n} (u v : vec n) (a : R),
      a < 0 -> u <> vzero -> v <> vzero -> (a \.* u) /_ v = (PI - (u /_ v))%R.
  Proof.
    intros. unfold vangle. rewrite vnorm_vcmul; auto.
    rewrite vdot_vcmul_l. unfold sign. bdestruct (0 <? a); ra.
    - bdestruct (a =? 0); ra. rewrite Rmult_neg1_l. rewrite acos_opp. auto.
    - bdestruct (a =? 0); ra.
  Qed.

  (** a > 0 -> u /_ (a \.* v) = u /_ v *)
  Lemma vangle_vcmul_r_gt0 : forall {n} (u v : vec n) (a : R),
      a > 0 -> u <> vzero -> v <> vzero -> u /_ (a \.* v) = u /_ v.
  Proof.
    intros. unfold vangle. rewrite vnorm_vcmul; auto.
    rewrite vdot_vcmul_r. unfold sign. bdestruct (0 <? a); ra.
    - rewrite !Rmult_1_l. auto.
    - bdestruct (a =? 0); ra.
  Qed.

  (** a < 0 -> u /_ (a \.* v) = PI - u /_ v *)
  Lemma vangle_vcmul_r_lt0 : forall {n} (u v : vec n) (a : R),
      a < 0 -> u <> vzero -> v <> vzero -> u /_ (a \.* v) = (PI - (u /_ v))%R.
  Proof.
    intros. unfold vangle. rewrite vnorm_vcmul; auto.
    rewrite vdot_vcmul_r. unfold sign. bdestruct (0 <? a); ra.
    - bdestruct (a =? 0); ra. rewrite Rmult_neg1_l. rewrite acos_opp. auto.
    - bdestruct (a =? 0); ra.
  Qed.

  (** (vnorm u) /_ v = u /_ v *)
  Lemma vangle_vnorm_l : forall {n} (u v : vec n),
      u <> vzero -> vnorm u /_ v = u /_ v.
  Proof. intros. unfold vangle. rewrite vnorm_idem; auto. Qed.

  (** u /_ (vnorm v) = u /_ v *)
  Lemma vangle_vnorm_r : forall {n} (u v : vec n),
      v <> vzero -> u /_ vnorm v = u /_ v.
  Proof. intros. unfold vangle. rewrite vnorm_idem; auto. Qed.

End vangle.

Infix "/_" := vangle (at level 60) : vec_scope.


(* ======================================================================= *)
(** ** Projection component of a vector onto another *)
Section vproj.

  (** The projection component of a onto b *)
  Definition vproj {n} (u v : vec n) : vec n := (<u, v> / <v, v>) \.* v.

  (* (** The scalar projection of u on v is a simple triangle relation *) *)
  (* Lemma vsproj_spec : forall {n} (u v : vec n), 
     vsproj u v = `|u| * vangle. *)

  (** vproj (u + v) w = vproj u w + vproj v w *)
  Lemma vproj_vadd : forall {n} (u v w : vec n),
      w <> vzero -> (vproj (u + v) w = vproj u w + vproj v w)%V.
  Proof.
    intros. unfold vproj. rewrite vdot_vadd_l.
    rewrite <- vcmul_add. f_equal. autounfold with A. field.
    apply vdot_same_neq0; auto.
  Qed.

  (** vproj (k \.* u) v = k * (vproj u v) *)
  Lemma vproj_vcmul : forall {n} (u v : vec n) (k : R),
      v <> vzero -> (vproj (k \.* u) v = k \.* (vproj u v))%V.
  Proof.
    intros. unfold vproj. rewrite vdot_vcmul_l. rewrite vcmul_assoc. f_equal.
    autounfold with A. field. apply vdot_same_neq0; auto.
  Qed.
  
  (** vproj v v = v *)
  Lemma vproj_same : forall {n} (v : vec n), v <> vzero -> vproj v v = v.
  Proof.
    intros. unfold vproj. replace (<v, v> / <v, v>) with 1; try field.
    apply vcmul_1_l. apply vdot_same_neq0; auto.
  Qed.
  
End vproj.


(* ======================================================================= *)
(** ** Perpendicular component of a vector respect to another *)
Section vperp.

  (** The perpendicular component of u respect to u *)
  Definition vperp {n} (u v : vec n) : vec n := u - vproj u v.

  (** vperp (u + v) w = vperp u w + vperp v w *)
  Lemma vperp_vadd : forall {n} (u v w : vec n),
      w <> vzero -> (vperp (u + v) w = vperp u w + vperp v w)%V.
  Proof.
    intros. unfold vperp. rewrite vproj_vadd; auto.
    unfold vsub. asemigroup. rewrite vopp_vadd. auto.
  Qed.

  (** vperp (k * u) v = k * (vperp u v) *)
  Lemma vperp_vcmul : forall {n} (k : R) (u v : vec n),
      v <> vzero -> (vperp (k \.* u) v = k \.* (vperp u v))%V.
  Proof.
    intros. unfold vperp. rewrite vproj_vcmul; auto. rewrite vcmul_vsub. easy.
  Qed.

  (** vperp v v = 0 *)
  Lemma vperp_same : forall {n} (v : vec n), v <> vzero -> vperp v v = vzero.
  Proof.
    intros. unfold vperp. rewrite vproj_same; auto; auto. apply vsub_self.
  Qed.
  
End vperp.


(* ======================================================================= *)
(** ** Orthogonal vectors 正交的两个向量 *)
Section vorth.

  (** Two vectors, u and v, in an inner product space v, are orthogonal if their 
    inner-product <u, v> is zero, and the relationship is denoted u ⟂ v. *)

  (** Two real column-vectors are orthogonal (also called perpendicular) *)
  Definition vorth {n} (u v : vec n) : Prop := <u, v> = 0.
  Infix "⟂" := vorth ( at level 50).

  (** Bool version to determine if two vectors are orthogonal *)
  Definition vorthb {n} (u v : vec n) : bool := (<u, v> =? 0)%R.

  (** u ⟂ v -> v ⟂ u *)
  Lemma vorth_comm : forall {n} (u v : vec n), u ⟂ v -> v ⟂ u.
  Proof. intros. unfold vorth in *. rewrite vdot_comm; auto. Qed.

  (** u ⟂ v -> vproj u v = vzero *)
  Lemma vorth_vproj : forall {n} (u v : vec n),
      v <> vzero -> u ⟂ v -> vproj u v = vzero.
  Proof.
    intros. unfold vorth in H0. unfold vproj. rewrite H0.
    autorewrite with R. rewrite vcmul_0_l; easy. apply vdot_same_neq0; auto.
  Qed.
  
  (** u ⟂ v -> vperp u v = u *)
  Lemma vorth_vperp : forall {n} (u v : vec n),
      v <> vzero -> u ⟂ v -> vperp u v = u.
  Proof. intros. unfold vperp. rewrite vorth_vproj; auto. apply vsub_0_r. Qed.

  (** u ⟂ v -> vnorm u ⟂ v *)
  Lemma vorth_vnorm_l : forall {n} (u v : vec n), u ⟂ v -> vnorm u ⟂ v.
  Proof.
    intros. unfold vorth, vnorm in *. rewrite vdot_vcmul_l.
    rewrite H. autounfold with A. ra.
  Qed.

  (** vnorm u ⟂ v -> u ⟂ v *)
  Lemma vorth_vnorm_l_rev : forall {n} (u v : vec n),
      u <> vzero -> vnorm u ⟂ v -> u ⟂ v.
  Proof.
    intros. unfold vorth, vnorm in *. rewrite vdot_vcmul_l in H0; ra.
    apply Rmult_integral  in H0. destruct H0; auto.
    assert (1 * / (||u||) <> 0)%R; ra.
    apply vlen_neq0_iff_neq0 in H.
    apply Rmult_integral_contrapositive_currified; ra.
    apply Rinv_neq_0_compat; auto.
  Qed.

  (** u ⟂ v -> u ⟂ vnorm v *)
  Lemma vorth_vnorm_r : forall {n} (u v : vec n), u ⟂ v -> u ⟂ vnorm v.
  Proof.
    intros. apply vorth_comm. apply vorth_comm in H. apply vorth_vnorm_l; auto.
  Qed.

  (** u ⟂ vnorm v -> u ⟂ v *)
  Lemma vorth_vnorm_r_rev : forall {n} (u v : vec n),
      v <> vzero -> u ⟂ vnorm v -> u ⟂ v.
  Proof.
    intros. apply vorth_comm. apply vorth_comm in H0. apply vorth_vnorm_l_rev; auto.
  Qed.
  
  (** u ⟂ v -> (k \.* u) ⟂ v *)
  Lemma vorth_vcmul_l : forall {n} k (u v : vec n), u ⟂ v -> (k \.* u) ⟂ v.
  Proof.
    intros. unfold vorth, vnorm in *. rewrite vdot_vcmul_l.
    autounfold with A; ra.
  Qed.

  (** (k \.* u) ⟂ v -> u ⟂ v *)
  Lemma vorth_vcmul_l_rev : forall {n} k (u v : vec n),
      k <> 0 -> (k \.* u) ⟂ v -> u ⟂ v.
  Proof.
    intros. unfold vorth, vnorm in *. rewrite vdot_vcmul_l in H0.
    autounfold with A in *; ra.
  Qed.

  (** u ⟂ v -> u ⟂ (k \.* v) *)
  Lemma vorth_vcmul_r : forall {n} k (u v : vec n), u ⟂ v -> u ⟂ (k \.* v).
  Proof.
    intros. apply vorth_comm. apply vorth_vcmul_l. apply vorth_comm; auto.
  Qed.

  (** u ⟂ (k \.* v) -> u ⟂ v *)
  Lemma vorth_vcmul_r_rev : forall {n} k (u v : vec n),
      k <> 0 -> u ⟂ (k \.* v) -> u ⟂ v.
  Proof.
    intros. apply vorth_comm, vorth_vcmul_l_rev in H0; auto. apply vorth_comm; auto.
  Qed.

  (** vproj ⟂ vperp *)
  Lemma vorth_proj_perp : forall {n} (u v : vec n),
      v <> vzero -> vproj u v ⟂ vperp u v.
  Proof.
    intros. hnf. unfold vperp, vproj.
    rewrite !vdot_vcmul_l. rewrite vdot_vsub_r. rewrite !vdot_vcmul_r.
    autounfold with A. rewrite (vdot_comm v u). field_simplify; ra.
    apply vdot_same_neq0; auto.
  Qed.

End vorth.

Infix "⟂" := vorth ( at level 50).


(* ======================================================================= *)
(** ** Orthogonal set 正交向量组（集） *)
Section vorthset.

  (*
  (** A set of vectors in an inner product space is called pairwise orthogonal if 
      each pairing of them is orthogonal. Such a set is called an orthogonal set.
      Note: each pair means {(vi, vj)|i≠j}  *)
  Definition vorthset {r c} (M : mat r c) : Prop :=
    forall j1 j2, (j1 < c)%nat -> (j2 < c)%nat -> (j1 <> j2) -> <mcol m j1, mcol m j2> = Azero.

  (** (bool version) *)
  Definition vorthsetb {r c} (m : mat r c) : bool :=
    (* two column vectors is orthogonal *)
    let orth (i j : nat) : bool := (<mcol m i, mcol m j> =? Azero)%R in
    (* remain column indexes after this column *)
    let cids (i : nat) : list nat := seq (S i) (c - S i) in
    (* the column is orthogonal to right-side remain columns *)
    let allcols (j : nat) : bool := and_blist (map (fun k => orth j k) (cids j)) in
    (* all columns is mutually orthogonal (Note orthogonal is commutative) *)
    and_blist (map (fun j => allcols j) (seq 0 c)).

  Lemma vorthsetb_true_iff : forall {r c} (m : mat r c),
      vorthsetb m <-> vorthset m.
  Abort.

  Example vorthset_ex1 :
    vorthset (@l2m 3 3 [[1;1;1];[0;sqrt 2; -(sqrt 2)];[-1;1;1]])%A.
  Proof.
    apply vorthsetb_true_iff. cbv.
    (** Auto solve equality contatin "Req_EM_T" *)
    repeat
      match goal with
      | |- context[ Req_EM_T ?a ?b] => destruct Req_EM_T; ra
      end.
    autorewrite with R sqrt in *; ra.
  Qed.
*)
End vorthset.


(* ======================================================================= *)
(** ** Orthonormal vectors 标准正交的向量组 *)
Section mcolsOrthonormal.

  (*
  (** All (different) column-vectors of a matrix are orthogonal each other.
      For example: [v1;v2;v3] => u⟂v2 && u⟂v3 && v⟂v3. *)
  Definition mcolsorth {r c} (m : mat r c) : Prop :=
    forall j1 j2, (j1 < c)%nat -> (j2 < c)%nat -> j1 <> j2 -> mcol m j1 ⟂ mcol m j2.

  (** bool version *)
  Definition mcolsorthb {r c} (m : mat r c) : bool :=
    let is_orth (i j : nat) : bool := (<mcol m i, mcol m j> =? Azero)%R in
    let cids (i : nat) : list nat := seq (S i) (c - S i) in
    let chk_col (j : nat) : bool := and_blist (map (fun k => is_orth j k) (cids j)) in
    and_blist (map (fun j => chk_col j) (seq 0 c)).

  Lemma mcolsorthb_spec : forall {r c} (m : mat r c),
      mcolsorthb m <-> mcolsorth m.
  Proof.
  Abort.

  Section test.
    Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : R.
    Let m1 : mat 1 3 := l2m [[a11;a12;a13];[a21;a22;a23]].
    Let m2 : mat 3 1 := l2m [[a11;a12];[a21;a22];[a31;a32]].

    (* Compute mcolsorthb m1. *)
    (* Compute mcolsorthb m2. (* because only one column, needn't be check *) *)
  End test.

  (** All column-vectors of a matrix are unit vector.
      For example: [v1;v2;v3] => unit u && unit v && unit v3 *)
  Definition mcolsUnit {r c} (m : mat r c) : Prop :=
    forall j, (j < c)%nat -> vunit (mcol m j).

  (** bool version *)
  Definition mcolsUnitb {r c} (m : mat r c) : bool :=
    and_blist (map (fun i => vunitb (mcol m i)) (seq 0 c)).

  Lemma mcolsUnitb_spec : forall {r c} (m : mat r c),
      mcolsUnitb m <-> mcolsUnit m.
  Proof.
  Abort.

  (** The columns of a matrix is orthogomal *)
  Definition mcolsOrthonormal {r c} (m : mat r c) : Prop :=
    mcolsorth m /\ mcolsUnit m.

*)
End mcolsOrthonormal.


(* ======================================================================= *)
(** ** Orthogonal matrix *)
Section morth.

  (* (** matrix m is orthogonal <-> columns of m are orthogomal *) *)
  (* Lemma morth_iff_mcolsOrthonormal : forall {n} (m : smat n), *)
  (*     morth m <-> mcolsOrthonormal m. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold morth,mcolsOrthonormal. *)
  (*   unfold mcolsorth, mcolsUnit. *)
  (*   unfold vorth, vunit. *)
  (*   split; intros. *)
  (*   - split; intros. *)
  (*     + rewrite vdot_col_col; auto. rewrite H; auto. rewrite mnth_mat1_diff; auto. *)
  (*     + rewrite vdot_col_col; auto. rewrite H; auto. rewrite mnth_mat1_same; auto. *)
  (*   - destruct H as [H1 H2]. hnf. intros. rewrite <- vdot_col_col; auto. *)
  (*     bdestruct (i =? j)%nat. *)
  (*     + subst. rewrite mnth_mat1_same; auto. apply H2; auto. *)
  (*     + rewrite mnth_mat1_diff; auto. apply H1; auto. *)
  (* Qed. *)

  (* (** Transformation by orthogonal matrix will keep inner-product *) *)
  (* Theorem morth_keep_dot : forall {n} (m : smat n) (u v : vec n), *)
  (*     morth m -> <m * u, m * v> = <v1, v>. *)
  (* Proof. *)
  (*   intros. *)
  (*   rewrite vdot_eq_mul_trans. *)
  (*   unfold scalar_of_mat, Matrix.scalar_of_mat. *)
  (*   rewrite (m2f_mor _ (v1\T * v)); auto. *)
  (*   rewrite mtrans_mmul. rewrite mmul_assoc. rewrite <- (mmul_assoc _ m). *)
  (*   rewrite morth_iff_mul_trans_l in H. rewrite H. *)
  (*   rewrite mmul_1_l. easy. *)
  (* Qed. *)

  (* (** Transformation by orthogonal matrix will keep length. *) *)
  (* Corollary morth_keep_length : forall {n} (m : smat n) (v : vec n), *)
  (*     morth m -> ||m * v|| = ||v||. *)
  (* Proof. *)
  (*   intros. rewrite vlen_eq_iff_dot_eq. apply morth_keep_dot. auto. *)
  (* Qed. *)

  (* (** Transformation by orthogonal matrix will keep normalization. *) *)
  (* keep unit?? or keep norm?? or both *)
  (* Corollary morth_keep_normalize : forall {n} (m : smat n) (v : vec n), *)
  (*     morth m -> vnorm (m * v) = m * (vnorm v). *)
  (* Proof. *)
  (*   intros. unfold vnorm. *)
  (*   rewrite morth_keep_length; auto. apply mcmul_mmul_assoc_r. *)
  (* Qed. *)

  (* (** Transformation by orthogonal matrix will keep angle. *) *)
  (* Corollary morth_keep_angle : forall {n} (m : smat n) (u v : vec n), *)
  (*     morth m -> m * u /_ m * v = u /_ v. *)
  (* Proof. *)
  (*   intros. unfold vangle. f_equal. rewrite !morth_keep_normalize; auto. *)
  (*   rewrite morth_keep_dot; auto. *)
  (* Qed. *)

  (** 由于正交矩阵可保持变换向量的长度和角度，它可保持坐标系的整体结构不变。
      因此，正交矩阵仅可用于旋转变换和反射变换或二者的组合变换。
      当正交矩阵的行列式为1，表示一个旋转，行列式为-1，表示一个反射。*)
End morth.


(* ======================================================================= *)
(** ** Exercise in textbook *)
Section exercise.
  (** 习题8.2第12题, page 23, 高等数学，第七版 *)
  (** 利用向量来证明不等式，并指出等号成立的条件 *)
  Theorem Rineq3 : forall a1 a2 a3 b1 b2 b3 : R,
      sqrt (a1² + a2² + a3²) * sqrt (b1² + b2² + b3²) >= |a1*b1 + a2*b2 + a3*b3|.
  Proof.
    intros.
    pose (u := mkvec3 a1 a2 a3).
    pose (v := mkvec3 b1 b2 b3).
    replace (sqrt (a1² + a2² + a3²)) with (vlen u); [|cbv; f_equal; ring].
    replace (sqrt (b1² + b2² + b3²)) with (vlen v); [|cbv; f_equal; ring].
    replace (a1 * b1 + a2 * b2 + a3 * b3)%R with (<u, v>); [|cbv; f_equal; ring].
    pose proof (vdot_abs_le u v). ra.
  Qed.

End exercise.


(* ######################################################################### *)
(** * Usage demo *)
Section test.
  Let u := @l2v 3 [1;2;3].
  Let v := @f2v 3 (fun i => 2 + nat2R i)%R.
  
  (* Compute v2l u. *)
  (* Compute v2l v. *)
  (* Compute u$fin0. *)
  (* Compute v2l (vmap u Ropp). *)
  (* Compute v2l (vmap2 u v Rplus). *)
  (* Compute @Vector.v2l _ _ (@Vector.vmap2 _ _ _ pair _ u v). *)
  (* Compute vsum u Rplus 0. *)
  (* Compute v2l (u + v). *)

  (* Compute v2l (u - v). *)
  (* Compute v2l (3 \.* u). *)
  (* Compute <u, v>. *)
  (* Compute vunitb u. *)
  (* Compute vnorm u. *)
  (* Compute vorthb u v. *)
End test.
