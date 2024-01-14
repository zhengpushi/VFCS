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
     |v| = √(v,v)

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
  Definition vnonzero_cmul {n} (k : nonzeroreal) (V : vnonzero n) : vnonzero n.
    refine (mkvnonzero (vcmul k V) _).
    intro. apply vcmul_eq0_imply_k0_or_V0 in H. destruct k,V,H; auto.
  Defined.

  Section vpara.

    (** Two non-zero vectors are parallel, when their components are proportional *)
    Definition vpara {n} (V1 V2 : vnonzero n) : Prop :=
      exists k : R, k c* V1 = V2.

    (* Note: if the coefficient `k` is limited to positive, then two vectors have
     same direction *)

    Infix "//" := vpara (at level 50) : vec_scope.

    (** vparallel is an equivalence relation *)

    Lemma vpara_refl : forall {n} (V : vnonzero n), V // V.
    Proof. intros. exists 1. apply vcmul_1_l. Qed.

    Lemma vpara_sym : forall {n} (V1 V2 : vnonzero n), V1 // V2 -> V2 // V1.
    Proof.
      intros. destruct H as [k H]. exists (1/k). rewrite <- H.
      rewrite vcmul_assoc. symmetry. rewrite <- vcmul_1_l at 1. f_equal.
      cbv. field. apply vcmul_eq_imply_k_neq0 in H; auto. apply V1. apply V2.
    Qed.

    Lemma vpara_trans : forall {n} (V1 V2 V3: vnonzero n), V1//V2 -> V2//V3 -> V1//V3.
    Proof.
      intros. destruct H as [k1 H1], H0 as [k2 H2].
      exists (k2 * k1)%R. rewrite <- H2,<- H1. rewrite vcmul_assoc. auto.
    Qed.

    (** V1 // V2 -> (k c* V1) // V2 *)
    Lemma vcmul_cvpara_l : forall {n} (k : nonzeroreal) (V1 V2 : vnonzero n),
        V1 // V2 -> (vnonzero_cmul k V1) // V2.
    Proof.
      intros. destruct H as [x H]. exists (x/k); simpl. rewrite <- H.
      rewrite vcmul_assoc. f_equal. destruct k. cbv in *. field. auto.
    Qed.

    (** V1 // V2 -> V1 // (k c* V2) *)
    Lemma vcmul_cvpara_r : forall {n} (k : nonzeroreal) (V1 V2 : vnonzero n),
        V1 // V2 -> V1 // (vnonzero_cmul k V2).
    Proof.
      intros. apply vpara_sym. apply vcmul_cvpara_l; auto.
      apply vpara_sym; auto.
    Qed.

    (** V1 // V2 => ∃! k, k * V1 = V2 *)
    Lemma vpara_imply_uniqueK : forall {n} (V1 V2 : vnonzero n),
        V1 // V2 -> (exists ! k, k c* V1 = V2).
    Proof.
      intros. destruct H as [k H]. exists k. split; auto.
      intros. rewrite <- H in H0. apply vcmul_sameV_imply_eqK in H0; auto.
      apply V1.
    Qed.

  End vpara.

  Infix "//" := vpara (at level 50) : vec_scope.

End vpara_on_vnonzero.


(* ======================================================================= *)
(** ** Two vectors are parallel (or called collinear) *)
Section vpara.

  (** Two non-zero vectors are parallel, when their components are proportional *)
  Definition vpara {n} (V1 V2 : vec n) : Prop :=
    V1 <> vzero /\ V2 <> vzero /\ exists k : R, k c* V1 = V2.

  (* Note: if the coefficient `k` is limited to positive, then two vectors have
     same direction *)

  Infix "//" := vpara (at level 50) : vec_scope.

  (** vpara is almost an equivalence relation (but the reflexivity law not hold) *)

  Lemma vpara_refl : forall {n} (V : vec n), V <> vzero -> V // V.
  Proof. intros. unfold vpara. repeat split; auto. exists 1. apply vcmul_1_l. Qed.

  Lemma vpara_sym : forall {n} (V1 V2 : vec n), V1 // V2 -> V2 // V1.
  Proof.
    intros. destruct H as [H1 [H2 [k H3]]]. repeat split; auto.
    exists (1/k). rewrite <- H3.
    rewrite vcmul_assoc. symmetry. rewrite <- vcmul_1_l at 1. f_equal.
    cbv. field. apply vcmul_eq_imply_k_neq0 in H3; auto.
  Qed.

  Lemma vpara_trans : forall {n} (V1 V2 V3: vec n), V1//V2 -> V2//V3 -> V1//V3.
  Proof.
    intros. destruct H as [H1 [H2 [k1 H3]]], H0 as [H4 [H5 [k2 H6]]].
    repeat split; auto.
    exists (k2 * k1). rewrite <- H6,<- H3. rewrite vcmul_assoc. auto.
  Qed.

  (** V1 // V2 => ∃! k, k * V1 = V2 *)
  Lemma vpara_imply_uniqueK : forall {n} (V1 V2 : vec n),
      V1 // V2 -> (exists ! k, k c* V1 = V2).
  Proof.
    intros. destruct H as [H1 [H2 [k H3]]]. exists k. split; auto.
    intros. rewrite <- H3 in H. apply vcmul_sameV_imply_eqK in H; auto.
  Qed.

  (** V1 // V2 -> (k c* V1) // V2 *)
  Lemma vcmul_cvpara_l : forall {n} k (V1 V2 : vec n),
      k <> 0 -> V1 // V2 -> k c* V1 // V2.
  Proof.
    intros. destruct H0 as [H1 [H2 [k1 H3]]]. repeat split; auto.
    - intro. apply vcmul_eq0_imply_k0_or_V0 in H0. destruct H0; auto.
    - exists (k1/k); simpl. rewrite <- H3. rewrite vcmul_assoc. f_equal.
      cbv. field. auto.
  Qed.

  (** V1 // V2 -> V1 // (k c* V2) *)
  Lemma vcmul_cvpara_r : forall {n} k (V1 V2 : vec n),
      k <> 0 -> V1 // V2 -> V1 // (k c* V2).
  Proof.
    intros. apply vpara_sym. apply vcmul_cvpara_l; auto.
    apply vpara_sym; auto.
  Qed.

End vpara.

Infix "//" := vpara (at level 50) : vec_scope.


(* ======================================================================= *)
(** ** Length of a vector *)

(** Length (magnitude) of a vector, is derived by inner-product *)
Definition vlen {n} (V : vec n) : R := sqrt (<V,V>).

Notation "|| V ||" := (vlen V) : vec_scope.

Section vlen_props.
  Notation seqsum := (@seqsum _ Rplus 0).

  (** 0 <= ||v|| *)
  Lemma vlen_ge0 : forall {n} (V : vec n), 0 <= ||V||.
  Proof. intros. unfold vlen. ra. Qed.
  
  (** Length equal iff dot-product equal *)
  Lemma vlen_eq_iff_dot_eq : forall {n} (V1 V2 : vec n), ||V1|| = ||V2|| <-> <V1,V1> = <V2,V2>.
  Proof.
    intros. unfold vlen. split; intros H; try rewrite H; auto.
    apply sqrt_inj in H; auto; apply vdot_ge0.
  Qed.

  (** || vzero || = 0 *)
  Lemma vlen_vzero : forall {n}, || @vzero n || = 0.
  Proof. intros. unfold vlen. rewrite vdot_0_l. ra. Qed.

  (** ||V|| = 0 <-> V = 0 *)
  Lemma vlen_eq0_iff_eq0 : forall {n} (V : vec n), ||V|| = 0 <-> V = vzero.
  Proof.
    intros. unfold vlen. split; intros.
    - apply vdot_eq0_iff_vzero. apply sqrt_eq_0 in H; auto. apply vdot_ge0.
    - rewrite H. rewrite vdot_0_l. cbv. apply sqrt_0.
  Qed.

  (** ||V|| <> 0 <-> V <> 0 *)
  Lemma vlen_neq0_iff_neq0 : forall {n} (V : vec n), ||V|| <> 0 <-> V <> vzero.
  Proof. intros. rewrite vlen_eq0_iff_eq0. easy. Qed.

  (** V <> vzero -> 0 < ||V|| *)
  Lemma vlen_gt0 : forall {n} (V : vec n), V <> vzero -> 0 < ||V||.
  Proof. intros. pose proof (vlen_ge0 V). apply vlen_neq0_iff_neq0 in H; ra. Qed.

  (** <V,V> = ||V||² *)
  Lemma vdot_same : forall {n} (V : vec n), <V,V> = ||V||².
  Proof. intros. unfold vlen. rewrite Rsqr_sqrt; auto. apply vdot_ge0. Qed.
  
  (** 0 <= <V,V> *)
  Lemma vdot_same_ge0 : forall {n} (V : vec n), 0 <= <V,V>.
  Proof. intros. rewrite vdot_same. ra. Qed.

  (** V <> vzero -> <V,V> <> 0*)
  Lemma vdot_same_neq0 : forall {n} (V : vec n), V <> vzero -> <V,V> <> 0.
  Proof. intros. rewrite vdot_same. apply vlen_neq0_iff_neq0 in H. ra. Qed.

  (** V <> vzero -> 0 < <V,V> *)
  Lemma vdot_same_gt0 : forall {n} (V : vec n), V <> vzero -> 0 < <V,V>.
  Proof.
    intros. pose proof (vdot_same_ge0 V). pose proof (vdot_same_neq0 V H). ra.
  Qed.
  
  (** || V || = 1 <-> <V,V> = 1 *)
  Lemma vlen_eq1_iff_vdot1 : forall {n} (V : vec n), ||V|| = 1 <-> <V,V> = 1.
  Proof. intros. unfold vlen. split; intros; hnf in *. ra. rewrite H. ra. Qed.

  (** || - V|| = || V || *)
  Lemma vlen_vopp : forall n (V : vec n), || - V|| = || V ||.
  Proof.
    intros. unfold vlen. f_equal. rewrite vdot_vopp_l,vdot_vopp_r.
    autorewrite with R. auto.
  Qed.
  
  (** ||k c* V|| = |k| * ||V|| *)
  Lemma vlen_vcmul : forall n k (V : vec n), ||k c* V|| = |k| * ||V||.
  Proof.
    intros. unfold vlen. rewrite vdot_vcmul_l, vdot_vcmul_r.
    rewrite <- Rmult_assoc.
    rewrite sqrt_mult_alt; ra. f_equal. autorewrite with R. ra.
  Qed.
  
  (** ||V1 + V2||² = ||V1||² + ||V2||² + 2 * <V1,V2> *)
  Lemma vlen2_vadd : forall {n} (V1 V2 : vec n),
      ||(V1 + V2)||² = (||V1||² + ||V2||² + 2 * <V1,V2>)%R.
  Proof.
    intros. rewrite <- !vdot_same.
    rewrite !vdot_vadd_l, !vdot_vadd_r.
    rewrite (vdot_comm V2 V1).
    autounfold with A. ring.
  Qed.
  
  (** ||V1 - V2||² = ||V1||² + ||V2||² - 2 * <V1,V2> *)
  Lemma vlen2_vsub : forall {n} (V1 V2 : vec n),
      ||(V1 - V2)||² = (||V1||² + ||V2||² - 2 * <V1,V2>)%R.
  Proof.
    intros. rewrite <- !vdot_same. unfold vsub.
    rewrite !vdot_vadd_l, !vdot_vadd_r.
    rewrite !vdot_vopp_l, !vdot_vopp_r. rewrite (vdot_comm V2 V1).
    autounfold with A. ring.
  Qed.

  (** <V1,V2>² <= <V1,V1> * <V2,V2> *)
  Lemma vdot_sqr_le : forall {n} (V1 V2 : vec n), <V1,V2>² <= <V1,V1> * <V2,V2>.
  Proof.
    intros. unfold vdot,Vector.vdot,Vector.vsum,Vector.vmap2.
    autounfold with A. destruct n.
    - cbv; ra.
    - (* Convert dependent "vec" to non-dependent "nat -> A", by "Abstraction"  *)
      remember (fun i => V1 (nat2finS i)) as f.
      remember (fun i => V2 (nat2finS i)) as g.
      replace (fseqsum (fun i => (V1 i * V2 i)))
        with (seqsum (fun i => f i * g i) (S n)); auto.
      2:{ rewrite ?Heqf,?Heqg. rewrite !fseqsum_to_seqsum_form3. auto. }
      replace (fseqsum (fun i => V1 i * V1 i))
        with (seqsum (fun i => f i * f i) (S n)).
      2:{ rewrite ?Heqf,?Heqg. rewrite !fseqsum_to_seqsum_form3. auto. }
      replace (fseqsum (fun i => V2 i * V2 i))
        with (seqsum (fun i => g i * g i) (S n)).
      2:{ rewrite ?Heqf,?Heqg. rewrite !fseqsum_to_seqsum_form3. auto. }
      clear.
      apply seqsum_SqrMul_le_MulSqr.
  Qed.

  (* 柯西.许西尔兹不等式，Cauchy-Schwarz Inequality *)
  (** |<V1,V2>| <= ||V1|| * ||V2|| *)
  Lemma vdot_abs_le : forall {n} (V1 V2 : vec n), |<V1,V2>| <= ||V1|| * ||V2||.
  Proof.
    intros. pose proof (vdot_sqr_le V1 V2).
    rewrite !vdot_same in H.
    replace ((||V1||)² * (||V2||)²) with ((||V1|| * ||V2||)²) in H; [| cbv;ring].
    apply Rsqr_le_abs_0 in H.
    replace (|((||V1||) * (||V2||))|) with (||V1|| * ||V2||) in H; auto.
    rewrite !Rabs_right; auto.
    pose proof (vlen_ge0 V1). pose proof (vlen_ge0 V2). ra.
  Qed.

  (** <V1,V2> <= ||V1|| * ||V2|| *)
  Lemma vdot_le_mul_vlen : forall {n} (V1 V2 : vec n), <V1,V2> <= ||V1|| * ||V2||.
  Proof. intros. pose proof (vdot_abs_le V1 V2). apply Rabs_le_rev in H. ra. Qed.

  (** - ||V1|| * ||V2|| <= <V1,V2> *)
  Lemma vdot_ge_neg_mul_vlen : forall {n} (V1 V2 : vec n), (- ||V1|| * ||V2||)%R <= <V1,V2>.
  Proof. intros. pose proof (vdot_abs_le V1 V2). apply Rabs_le_rev in H. ra. Qed.
    
  
  (** ||V1 + V2|| <= ||V1|| + ||V2|| *)
  (* 任意维度“三角形”两边长度之和大于第三边长度 *)
  Lemma vlen_vadd_le : forall {n} (V1 V2 : vec n), ||(V1 + V2)|| <= ||V1|| + ||V2||.
  Proof.
    intros. apply Rsqr_incr_0_var.
    2:{ unfold vlen; ra. }
    rewrite Rsqr_plus. rewrite <- !vdot_same.
    replace (<V1 + V2,V1 + V2>)
      with ((<V1,V1>) + (<V2,V2>) + (2 * (<V1,V2>)))%A.
    2:{ rewrite vdot_vadd_l,!vdot_vadd_r.
        rewrite (vdot_comm V2 V1). autounfold with A; ra. }
    apply Rplus_le_compat_l.
    rewrite !associative. apply Rmult_le_compat_l; ra.
    pose proof (vdot_abs_le V1 V2). unfold Rabs in H.
    destruct Rcase_abs; ra.
  Qed.
  
  (** 这个性质不成立，有一个例子：相反向量长度相等且平行，但不相等。*)
  Lemma v_eq_iff_len_parallel : forall {n} (V1 V2 : vec n),
      (||V1|| = ||V2|| /\ V1 // V2) <-> V1 = V2.
  Abort.

End vlen_props.


(* ======================================================================= *)
(** ** Unit vector *)
Section vunit.

  (** A unit vector u is a vector whose length equals one.
      Here, we use the square of length instead of length directly,
      but this is reasonable with the proof of vunit_spec.
   *)
  Definition vunit {n} (V : vec n) : Prop := <V,V> = 1.

  (** Verify the definition is reasonable *)
  Lemma vunit_spec : forall {n} (V : vec n), vunit V <-> ||V|| = 1.
  Proof. intros. split; intros; apply vlen_eq1_iff_vdot1; auto. Qed.
  
  (** (bool version) *)
  Definition vunitb {n} (V : vec n) : bool := (<V,V> =? 1)%R.

  (** The length of a unit vector is one *)
  Lemma vlen_vunit : forall {n} (V : vec n), vunit V -> ||V|| = 1.
  Proof. intros. apply vlen_eq1_iff_vdot1. auto. Qed.

  (** The unit vector cannot be zero vector *)
  Lemma vunit_neq0 : forall {n} (V : vec n), vunit V -> V <> vzero.
  Proof.
    intros. intro. rewrite H0 in H. unfold vunit in H.
    rewrite vdot_0_l in H. ra.
  Qed.

  (** vunit V <-> vunit (vopp u). *)
  Lemma vopp_vunit : forall {n} (V : vec n), vunit (vopp V) <-> vunit V.
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

  (** Normalization of a non-zero vector V.
      That is, make a unit vector that in the same directin as V. *)
  Definition vnorm {n} (V : vec n) : vec n := (1/ ||V||) c* V.

  (** The component of a normalized vector is equivalent to its original component 
      divide the vector's length *)
  Lemma vnth_vnorm : forall {n} (V : vec n) i,
      V <> vzero -> (vnorm V) $ i = (V $ i) / ||V||.
  Proof.
    intros. unfold vnorm. rewrite vnth_vcmul; auto.
    autounfold with A. field. apply vlen_neq0_iff_neq0; auto.
  Qed.

  (** Unit vector is fixpoint of vnorm operation *)
  Lemma vnorm_vunit_fixpoint : forall {n} (V : vec n),
      vunit V -> vnorm V = V.
  Proof.
    intros. unfold vnorm. rewrite (vunit_spec V) in H. rewrite H.
    autorewrite with R. apply vcmul_1_l.
  Qed.

  (** Normalized vector is non-zero  *)
  Lemma vnorm_vnonzero : forall {n} (V : vec n), V <> vzero -> vnorm V <> vzero.
  Proof.
    intros. unfold vnorm. intro.
    apply vcmul_eq0_imply_k0_or_V0 in H0. destruct H0; auto.
    apply vlen_neq0_iff_neq0 in H. unfold Rdiv in H0.
    rewrite Rmult_1_l in H0. apply Rinv_neq_0_compat in H. easy.
  Qed.

  (* The length of a normalized vector is one *)
  Lemma vnorm_len1 : forall {n} (V : vec n), V <> vzero -> ||vnorm V|| = 1.
  Proof.
    (* V̂ = V/|V|, |V̂| = sqrt (V/|V| ⋅ V/|V|) = sqrt ((V⋅V) / (|V|*|V|))
     = sqrt(V⋅V) / |V| = |V| / |V| = 1 *)
    intros. unfold vnorm. unfold vlen.
    rewrite !vdot_vcmul_l, !vdot_vcmul_r. rewrite vdot_same.
    remember (||V||). autounfold with A. autorewrite with R.
    apply sqrt_eq1_imply_eq1_rev.
    assert (|r| = r). { pose proof (vlen_ge0 V). subst. ra. }
    rewrite H0. cbv. field. subst. apply vlen_neq0_iff_neq0; auto.
  Qed.

  (** Normalized vector are unit vector *)
  Lemma vnorm_unit : forall {n} (V : vec n), V <> vzero -> vunit (vnorm V).
  Proof. intros. apply vunit_spec. apply vnorm_len1; auto. Qed.

  (** Normalized vector is parallel to original vector *)
  Lemma vnorm_vpara : forall {n} (V : vec n), V <> vzero -> (vnorm V) // V.
  Proof.
    intros. repeat split; auto.
    - apply vnorm_vnonzero; auto.
    - exists (||V||). unfold vnorm. rewrite vcmul_assoc.
      apply vcmul_same_if_k1_or_V0. left.
      autounfold with A. field. apply vlen_neq0_iff_neq0; auto.
  Qed.

  Lemma vnorm_spec : forall {n} (V : vec n),
      V <> vzero -> (||vnorm V|| = 1 /\ (vnorm V) // V).
  Proof. intros. split. apply vnorm_len1; auto. apply vnorm_vpara; auto. Qed.

  (** Normalization is idempotent *)
  Lemma vnorm_idem : forall {n} (V : vec n),
      V <> vzero -> vnorm (vnorm V) = vnorm V.
  Proof. intros. apply vnorm_vunit_fixpoint. apply vnorm_unit; auto. Qed.

  (** k <> 0 -> vnorm (k c* V) = (sign k) c* (vnorm V) *)
  Lemma vnorm_vcmul : forall {n} k (V : vec n),
      k <> 0 -> V <> vzero -> vnorm (k c* V) = sign k c* (vnorm V).
  Proof.
    intros. unfold vnorm. rewrite vlen_vcmul. rewrite !vcmul_assoc.
    f_equal. unfold sign. autounfold with A. apply vlen_neq0_iff_neq0 in H0.
    bdestruct (0 <? k).
    - rewrite Rabs_right; ra. field. split; auto.
    - bdestruct (k =? 0). easy. rewrite Rabs_left; ra. field. auto.
  Qed.

  (** k > 0 -> vnorm (k c* V) = vnorm V *)
  Lemma vnorm_vcmul_k_gt0 : forall {n} k (V : vec n),
      k > 0 -> V <> vzero -> vnorm (k c* V) = vnorm V.
  Proof.
    intros. rewrite vnorm_vcmul; auto; ra. rewrite sign_gt0; auto.
    apply vcmul_1_l.
  Qed.

  (** k < 0 -> vnorm (k c* V) = vnorm V *)
  Lemma vnorm_vcmul_k_lt0 : forall {n} k (V : vec n),
      k < 0 -> V <> vzero -> vnorm (k c* V) = - vnorm V.
  Proof.
    intros. rewrite vnorm_vcmul; auto; ra. rewrite sign_lt0; auto.
    rewrite (vcmul_opp 1). f_equal. apply vcmul_1_l.
  Qed.
  
End vnorm.


(* ======================================================================= *)
(** ** Angle between two vectors *)
Section vangle.

  (** The angle from vector V1 to vector V2, Here, θ ∈ [0,π] *)
  Definition vangle {n} (V1 V2 : vec n) : R := acos (<vnorm V1, vnorm V2>).
  
  Infix "/_" := vangle (at level 60) : vec_scope.

  (** The angle of between any vector and itself is 0 *)
  Lemma vangle_self_eq0 : forall {n} (V : vec n), V <> vzero -> V /_ V = 0.
  Proof.
    intros. unfold vangle. rewrite vdot_same.
    rewrite vnorm_len1; auto. autorewrite with R. apply acos_1.
  Qed.

  (** Angle is commutative *)
  Lemma vangle_comm : forall {n} (V1 V2 : vec n), V1 /_ V2 = V2 /_ V1.
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
  Lemma vdot_unit_bound : forall {n} (V1 V2 : vec n),
      vunit V1 -> vunit V2 -> -1 <= <V1,V2> <= 1.
  Proof.
    intros.
    pose proof (vdot_abs_le V1 V2).
    pose proof (vdot_ge_neg_mul_vlen V1 V2).
    apply vlen_vunit in H,H0. rewrite H,H0 in H1,H2.
    unfold Rabs in H1. destruct Rcase_abs; ra.
  Qed.

  (** 单位化后的非零向量的点积介于 [-1,1] *)
  Lemma vdot_vnorm_bound : forall {n} (V1 V2 : vec n),
      V1 <> vzero -> V2 <> vzero -> -1 <= <vnorm V1, vnorm V2> <= 1.
  Proof. intros. apply vdot_unit_bound; apply vnorm_unit; auto. Qed.
  
  (** The relation between dot product and the cosine of angle *)
  (* Note that we needn't the vectors are non-zero *)
  Lemma vdot_eq_cos_angle : forall {n} (V1 V2 : vec n),
      <V1,V2> = (||V1|| * ||V2|| * cos (V1 /_ V2))%R.
  Proof.
    intros. destruct (Aeqdec V1 vzero).
    - subst. rewrite vdot_0_l, vlen_vzero. rewrite Rmult_0_l. auto.
    - destruct (Aeqdec V2 vzero).
      + subst. rewrite vdot_0_r, vlen_vzero. rewrite Rmult_0_l,Rmult_0_r. auto.
      + unfold vangle. rewrite cos_acos.
        * unfold vnorm. rewrite <- vdot_vcmul_r. rewrite <- vdot_vcmul_l.
          rewrite !vcmul_assoc. autounfold with A.
          replace ((||V1||) * (1 / (||V1||))) with 1;
            [|field; apply vlen_neq0_iff_neq0; auto].
          replace ((||V2||) * (1 / (||V2||))) with 1;
            [|field; apply vlen_neq0_iff_neq0; auto].
          rewrite !vcmul_1_l. auto.
        * apply vdot_vnorm_bound; auto.
  Qed.
  
  (** The cosine law *)
  Theorem CosineLaw : forall {n} (V1 V2 : vec n),
      ||(V1 - V2)||² = (||V1||² + ||V2||² - 2 * ||V1|| * ||V2|| * cos (V1 /_ V2))%R.
  Proof.
    intros. rewrite vlen2_vsub. f_equal. f_equal.
    rewrite vdot_eq_cos_angle. auto.
  Qed.

  (* A variant form *)
  Theorem CosineLaw_var : forall {n} (V1 V2 : vec n),
      ||(V1 + V2)||² = (||V1||² + ||V2||² + 2 * ||V1|| * ||V2|| * cos (V1 /_ V2))%R.
  Proof.
    intros. rewrite vlen2_vadd. f_equal. f_equal.
    rewrite vdot_eq_cos_angle. auto.
  Qed.
  
  (** The relation between dot product and the cosine of angle *)
  Theorem vdot_eq_cos_angle_by_CosineLaw : forall {n} (V1 V2 : vec n),
      <V1,V2> = (||V1|| * ||V2|| * cos (V1 /_ V2))%R.
  Proof.
    intros.
    pose proof (vlen2_vsub V1 V2).
    pose proof (CosineLaw V1 V2). ra.
  Qed.

  (** 0 <= V1 /_ V2 <= PI *)
  Lemma vangle_bound : forall {n} (V1 V2 : vec n), 0 <= V1 /_ V2 <= PI.
  Proof. intros. unfold vangle. apply acos_bound. Qed.

  (** <V1,V2> = ||V1|| * ||V2|| -> V1 /_ V2 = 0 *)
  Lemma vdot_eq_mul_vlen_imply_angle_0 : forall {n} (V1 V2 : vec n),
      V1 <> vzero -> V2 <> vzero -> (<V1,V2> = ||V1|| * ||V2||) -> V1 /_ V2 = 0.
  Proof.
    intros. unfold vangle.
    match goal with | |- acos ?a = _ => replace a with 1 end.
    apply acos_1. unfold vnorm. rewrite vdot_vcmul_l,vdot_vcmul_r.
    rewrite H1. autounfold with A. field.
    apply vlen_neq0_iff_neq0 in H,H0. auto.
  Qed.
  
  (** <V1,V2> = - ||V1|| * ||V2|| -> V1 /_ V2 = π *)
  Lemma vdot_eq_neg_mul_vlen_imply_angle_pi : forall {n} (V1 V2 : vec n),
      V1 <> vzero -> V2 <> vzero -> (<V1,V2> = - ||V1|| * ||V2||)%R -> V1 /_ V2 = PI.
  Proof.
    intros. unfold vangle.
    match goal with | |- acos ?a = _ => replace a with (-1)%R end.
    apply acos_neg1. unfold vnorm. rewrite vdot_vcmul_l,vdot_vcmul_r.
    rewrite H1. autounfold with A. field.
    apply vlen_neq0_iff_neq0 in H,H0. auto.
  Qed.

  (** <V1,V2> = 0 -> V1 /_ V2 = π/2 *)
  Lemma vdot_eq_0_imply_angle_pi2 : forall {n} (V1 V2 : vec n),
      V1 <> vzero -> V2 <> vzero -> (<V1,V2> = 0) -> V1 /_ V2 = PI/2.
  Proof.
    intros. unfold vangle.
    match goal with | |- acos ?a = _ => replace a with 0 end.
    apply acos_0. unfold vnorm. rewrite vdot_vcmul_l,vdot_vcmul_r.
    rewrite H1. autounfold with A. field.
    apply vlen_neq0_iff_neq0 in H,H0. auto.
  Qed.

  (** V /_ V = 0 *)
  Lemma vdot_same_imply_angle_0 : forall {n} (V : vec n), V <> vzero -> V /_ V = 0.
  Proof.
    intros. apply vdot_eq_mul_vlen_imply_angle_0; auto.
    rewrite vdot_same. ra.
  Qed.

  (** 0 <= sin (V1 /_ V2) *)
  Lemma sin_vangle_ge0 : forall {n} (V1 V2 : vec n), 0 <= sin (V1 /_ V2).
  Proof. intros. apply sin_ge_0; apply vangle_bound. Qed.
  
  (** θ ≠ 0 -> θ ≠ π -> 0 < sin (V1 /_ V2) *)
  Lemma sin_vangle_gt0 : forall {n} (V1 V2 : vec n),
      V1 /_ V2 <> 0 -> V1 /_ V2 <> PI -> 0 < sin (V1 /_ V2).
  Proof. intros. pose proof (vangle_bound V1 V2). apply sin_gt_0; ra. Qed.

  (** V1 /_ V2 = 0 <-> V1,V2 同向平行 *)
  Lemma vangle_eq0_sameDir : forall {n} (V1 V2 : vec n),
      V1 <> vzero -> V2 <> vzero ->
      (V1 /_ V2 = 0 <-> (exists k : R, k > 0 /\ k c* V1 = V2)).
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
           V1 /_ V2 = 0 -> acos(<V1',V2'>) = 0, where V1',V2' is normalized V1,V2.
           then <V1',V2'> = 1. that is <vnorm V1, vnorm V2> = 1,
           then (1/(|V1|*|V2|)) * <V1,V2> = 1
           可以借助投影来表明 V1和V2是k倍的关系
         *)
        
        (* Search vpara.  *)
        (* exists (||V1|| * ||V2||)%R. split. *)
        (* * pose proof (vlen_gt0 V1 H). pose proof (vlen_gt0 V2 H0). ra. *)
        (* * rewrite vdot_eq_cos_angle in H1. *)
        (*   Search vlen. *)
  Abort.

  (** V1 /_ V3 = (V1 /_ V2) + (V2 /_ V3) *)
  Lemma vangle_add : forall {n} (V1 V2 V3 : vec n),
      V1 /_ V2 < PI ->
      V2 /_ V3 < PI ->
      V1 /_ V3 = ((V1 /_ V2) + (V2 /_ V3))%R.
  Proof.
  (** 由于目前 vangle 的值域是 [0,π]，暂不能表示 [0,2π)，所以该性质有点困难。
      有扩展了值域为 [0,2π) 的 V2angle 可做参考。
      在3D中，需要增加共面的条件。*)
    intros. unfold vangle in *.
  Abort.

  
  Lemma Rdiv_1_neq_0_compat : forall r : R, r <> 0 -> 1 / r <> 0.
  Proof. intros. pose proof (Rinv_neq_0_compat r H). ra. Qed.

  
  (* (** 给定两个向量，若将这两个向量同时旋转θ角，则向量之和在旋转前后的夹角也是θ。*) *)
  (* Lemma vangle_vadd : forall (V1 V2 V1' V2' : vec 2), *)
  (*     vnonzero V1 -> vnonzero V2 -> *)
  (*     ||v1|| = ||v1'|| -> ||v2|| = ||v2'|| -> *)
  (*     V1 /_ V2 = V1' /_ V2' -> *)
  (*     V1 + V2 /_ V1' + V2' = V1 /_ V1'. *)
  (* Proof. *)
  (*   intros V1 V2 V1' V2' Hneq0_V1 Hneq0_v2 Hlen_eq_11' Hlen_eq_22' Hangle_eq. *)
  (*   assert (||v1|| <> 0) as Hlen_neq0_v1. *)
  (*   { apply vlen_neq0_iff_neq0; auto. } *)
  (*   assert (||v2|| <> 0) as Hlen_neq0_v2. *)
  (*   { apply vlen_neq0_iff_neq0; auto. } *)
  (*   assert (vnonzero V1') as Hneq0_v1'. *)
  (*   { apply vlen_neq0_iff_neq0 in Hneq0_v1. apply vlen_neq0_iff_neq0. ra. } *)
  (*   assert (vnonzero V2') as Hneq0_v2'. *)
  (*   { apply vlen_neq0_iff_neq0 in Hneq0_v2. apply vlen_neq0_iff_neq0. ra. } *)
  (*   unfold vangle in *. f_equiv. *)
  (*   apply acos_inj in Hangle_eq; try apply vdot_vnorm_bound; auto. *)
  (*   unfold vnorm in *. *)
  (*   rewrite !vdot_vcmul_l, !vdot_vcmul_r in *. *)
  (*   (* remember (||(V1 + V2)%V||) as r1. *) *)
  (*   (* remember (||(v1' + V2')%V||) as r1'. *) *)
  (*   rewrite !vdot_vadd_distr_l, !vdot_vadd_distr_r. *)
  (*   rewrite <- Hlen_eq_11', <- Hlen_eq_22' in *. *)
  (*   assert (<v1,v2> = <v1',v2'>). *)
  (*   { apply Rmult_eq_reg_l with (r:=(1/(||v2||))). *)
  (*     apply Rmult_eq_reg_l with (r:=(1/(||v1||))). auto. *)
  (*     all: apply Rdiv_1_neq_0_compat; auto. } *)
  (*   (* 以下，尝试自动证明，因为我暂时无法手动证明 *) *)
  (*   Open Scope fun_scope. *)
  (*   vec2fun. cbv in *. autorewrite with R in *. *)
  (*   remember (v1.11) as a1; remember (v1.21) as a2; remember (v1.31) as a3. *)
  (*   remember (v2.11) as b1; remember (v2.21) as b2; remember (v2.31) as b3. *)
  (*   rename V1' into v3. rename V2' into v4. *)
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
  Lemma vangle_vadd : forall {n} (V1 V2 V1' V2' : vec n),
      V1 <> vzero -> V2 <> vzero ->
      ||V1|| = ||V1'|| -> ||V2|| = ||V2'|| ->
      V1 /_ V2 = V1' /_ V2' ->
      (V1 + V2) /_ (V1' + V2') = V1 /_ V1'.
  Proof.
    intros.
    unfold vangle in *.
    apply acos_inj in H3.
    f_equal. unfold vnorm in *.
    rewrite !vdot_vcmul_l, !vdot_vcmul_r in *.
    rewrite !vdot_vadd_l, !vdot_vadd_r in *.
    autounfold with A in *. rewrite <- H1, <- H2 in *.
    remember (||V1||) as r1.
    remember (||V2||) as r2.
    rewrite <- !associative in H3.
    rewrite <- !associative.
    
  Abort.
    (* intros V1 V2 V1' V2' Hneq0_V1 Hneq0_v2 Hlen_eq_11' Hlen_eq_22' Hangle_eq. *)
    (* assert (||v1|| <> 0) as Hlen_neq0_v1. *)
    (* { apply vlen_neq0_iff_neq0; auto. } *)
    (* assert (||v2|| <> 0) as Hlen_neq0_v2. *)
    (* { apply vlen_neq0_iff_neq0; auto. } *)
    (* assert (vnonzero V1') as Hneq0_v1'. *)
    (* { apply vlen_neq0_iff_neq0 in Hneq0_v1. apply vlen_neq0_iff_neq0. ra. } *)
    (* assert (vnonzero V2') as Hneq0_v2'. *)
    (* { apply vlen_neq0_iff_neq0 in Hneq0_v2. apply vlen_neq0_iff_neq0. ra. } *)
    (* unfold vangle in *. f_equiv. *)
    (* apply acos_inj in Hangle_eq; try apply vdot_vnorm_bound; auto. *)
    (* unfold vnorm in *. *)
    (* rewrite !vdot_vcmul_l, !vdot_vcmul_r in *. *)
    (* (* remember (||(V1 + V2)%V||) as r1. *) *)
    (* (* remember (||(v1' + V2')%V||) as r1'. *) *)
    (* rewrite !vdot_vadd_distr_l, !vdot_vadd_distr_r. *)
    (* rewrite <- Hlen_eq_11', <- Hlen_eq_22' in *. *)
    (* assert (<v1,v2> = <v1',v2'>). *)
    (* { apply Rmult_eq_reg_l with (r:=(1/(||v2||))). *)
    (*   apply Rmult_eq_reg_l with (r:=(1/(||v1||))). auto. *)
    (*   all: apply Rdiv_1_neq_0_compat; auto. } *)
    (* (* 以下，尝试自动证明，因为我暂时无法手动证明 *) *)
    (* Open Scope fun_scope. *)
    (* vec2fun. cbv in *. autorewrite with R in *. *)
    (* remember (v1.11) as a1; remember (v1.21) as a2; remember (v1.31) as a3. *)
    (* remember (v2.11) as b1; remember (v2.21) as b2; remember (v2.31) as b3. *)
    (* rename V1' into v3. rename V2' into v4. *)
    (* remember (v3.11) as c1; remember (v3.21) as c2; remember (v3.31) as c3. *)
    (* remember (v4.11) as d1; remember (v4.21) as d2; remember (v4.31) as d3. *)
    (* autorewrite with R. autorewrite with R in H. *)
    (* generalize Hlen_eq_11' Hlen_eq_22' H. clear. *)
    (* intros. *)
    (* clear. *)
    

  (** a > 0 -> (a c* V1) /_ V2 = V1 /_ V2 *)
  Lemma vangle_vcmul_l_gt0 : forall {n} (V1 V2 : vec n) (a : R),
      a > 0 -> V1 <> vzero -> V2 <> vzero -> (a c* V1) /_ V2 = V1 /_ V2.
  Proof.
    intros. unfold vangle. rewrite vnorm_vcmul; auto.
    rewrite vdot_vcmul_l. unfold sign. bdestruct (0 <? a); ra.
    - rewrite !Rmult_1_l. auto.
    - bdestruct (a =? 0); ra.
  Qed.

  (** a < 0 -> (a c* V1) /_ V2 = PI - V1 /_ V2 *)
  Lemma vangle_vcmul_l_lt0 : forall {n} (V1 V2 : vec n) (a : R),
      a < 0 -> V1 <> vzero -> V2 <> vzero -> (a c* V1) /_ V2 = (PI - (V1 /_ V2))%R.
  Proof.
    intros. unfold vangle. rewrite vnorm_vcmul; auto.
    rewrite vdot_vcmul_l. unfold sign. bdestruct (0 <? a); ra.
    - bdestruct (a =? 0); ra. rewrite Rmult_neg1_l. rewrite acos_opp. auto.
    - bdestruct (a =? 0); ra.
  Qed.

  (** a > 0 -> V1 /_ (a c* V2) = V1 /_ V2 *)
  Lemma vangle_vcmul_r_gt0 : forall {n} (V1 V2 : vec n) (a : R),
      a > 0 -> V1 <> vzero -> V2 <> vzero -> V1 /_ (a c* V2) = V1 /_ V2.
  Proof.
    intros. unfold vangle. rewrite vnorm_vcmul; auto.
    rewrite vdot_vcmul_r. unfold sign. bdestruct (0 <? a); ra.
    - rewrite !Rmult_1_l. auto.
    - bdestruct (a =? 0); ra.
  Qed.

  (** a < 0 -> V1 /_ (a c* V2) = PI - V1 /_ V2 *)
  Lemma vangle_vcmul_r_lt0 : forall {n} (V1 V2 : vec n) (a : R),
      a < 0 -> V1 <> vzero -> V2 <> vzero -> V1 /_ (a c* V2) = (PI - (V1 /_ V2))%R.
  Proof.
    intros. unfold vangle. rewrite vnorm_vcmul; auto.
    rewrite vdot_vcmul_r. unfold sign. bdestruct (0 <? a); ra.
    - bdestruct (a =? 0); ra. rewrite Rmult_neg1_l. rewrite acos_opp. auto.
    - bdestruct (a =? 0); ra.
  Qed.

  (** (vnorm V1) /_ V2 = V1 /_ V2 *)
  Lemma vangle_vnorm_l : forall {n} (V1 V2 : vec n),
      V1 <> vzero -> vnorm V1 /_ V2 = V1 /_ V2.
  Proof. intros. unfold vangle. rewrite vnorm_idem; auto. Qed.

  (** V1 /_ (vnorm V2) = V1 /_ V2 *)
  Lemma vangle_vnorm_r : forall {n} (V1 V2 : vec n),
      V2 <> vzero -> V1 /_ vnorm V2 = V1 /_ V2.
  Proof. intros. unfold vangle. rewrite vnorm_idem; auto. Qed.

End vangle.

Infix "/_" := vangle (at level 60) : vec_scope.


(* ======================================================================= *)
(** ** Projection component of a vector onto another *)
Section vproj.

  (** The projection component of a onto b *)
  Definition vproj {n} (V1 V2 : vec n) : vec n := (<V1,V2> / <V2,V2>) c* V2.

  (* (** The scalar projection of V1 on V2 is a simple triangle relation *) *)
  (* Lemma vsproj_spec : forall {n} (V1 V2 : vec n), 
     vsproj V1 V2 = `|V1| * vangle. *)

  (** vproj (V1 + V2) V3 = vproj V1 V3 + vproj V2 V3 *)
  Lemma vproj_vadd : forall {n} (V1 V2 V3 : vec n),
      V3 <> vzero -> (vproj (V1 + V2) V3 = vproj V1 V3 + vproj V2 V3)%V.
  Proof.
    intros. unfold vproj. rewrite vdot_vadd_l.
    rewrite <- vcmul_add. f_equal. autounfold with A. field.
    apply vdot_same_neq0; auto.
  Qed.

  (** vproj (k c* V1) V2 = k * (vproj V1 V2) *)
  Lemma vproj_vcmul : forall {n} (V1 V2 : vec n) (k : R),
      V2 <> vzero -> (vproj (k c* V1) V2 = k c* (vproj V1 V2))%V.
  Proof.
    intros. unfold vproj. rewrite vdot_vcmul_l. rewrite vcmul_assoc. f_equal.
    autounfold with A. field. apply vdot_same_neq0; auto.
  Qed.
  
  (** vproj V V = V *)
  Lemma vproj_same : forall {n} (V : vec n), V <> vzero -> vproj V V = V.
  Proof.
    intros. unfold vproj. replace (<V,V> / <V,V>) with 1; try field.
    apply vcmul_1_l. apply vdot_same_neq0; auto.
  Qed.
  
End vproj.


(* ======================================================================= *)
(** ** Perpendicular component of a vector respect to another *)
Section vperp.

  (** The perpendicular component of V1 respect to V1 *)
  Definition vperp {n} (V1 V2 : vec n) : vec n := V1 - vproj V1 V2.

  (** vperp (V1 + V2) V3 = vperp V1 V3 + vperp V2 V3 *)
  Lemma vperp_vadd : forall {n} (V1 V2 V3 : vec n),
      V3 <> vzero -> (vperp (V1 + V2) V3 = vperp V1 V3 + vperp V2 V3)%V.
  Proof.
    intros. unfold vperp. rewrite vproj_vadd; auto.
    unfold vsub. asemigroup. rewrite vopp_vadd. auto.
  Qed.

  (** vperp (k * V1) V2 = k * (vperp V1 V2) *)
  Lemma vperp_vcmul : forall {n} (k : R) (V1 V2 : vec n),
      V2 <> vzero -> (vperp (k c* V1) V2 = k c* (vperp V1 V2))%V.
  Proof.
    intros. unfold vperp. rewrite vproj_vcmul; auto. rewrite vcmul_vsub. easy.
  Qed.

  (** vperp V V = 0 *)
  Lemma vperp_same : forall {n} (V : vec n), V <> vzero -> vperp V V = vzero.
  Proof.
    intros. unfold vperp. rewrite vproj_same; auto; auto. apply vsub_self.
  Qed.
  
End vperp.


(* ======================================================================= *)
(** ** Orthogonal vectors 正交的两个向量 *)
Section vorth.

  (** Two vectors, V1 and V2, in an inner product space V, are orthogonal if their 
    inner-product <V1,V2> is zero, and the relationship is denoted V1 ⟂ V2. *)

  (** Two real column-vectors are orthogonal (also called perpendicular) *)
  Definition vorth {n} (V1 V2 : vec n) : Prop := <V1,V2> = 0.
  Infix "⟂" := vorth ( at level 50).

  (** Bool version to determine if two vectors are orthogonal *)
  Definition vorthb {n} (V1 V2 : vec n) : bool := (<V1,V2> =? 0)%R.

  (** V1 ⟂ V2 -> V2 ⟂ V1 *)
  Lemma vorth_comm : forall {n} (V1 V2 : vec n), V1 ⟂ V2 -> V2 ⟂ V1.
  Proof. intros. unfold vorth in *. rewrite vdot_comm; auto. Qed.

  (** V1 ⟂ V2 -> vproj V1 V2 = vzero *)
  Lemma vorth_vproj : forall {n} (V1 V2 : vec n),
      V2 <> vzero -> V1 ⟂ V2 -> vproj V1 V2 = vzero.
  Proof.
    intros. unfold vorth in H0. unfold vproj. rewrite H0.
    autorewrite with R. rewrite vcmul_0_l; easy. apply vdot_same_neq0; auto.
  Qed.
  
  (** V1 ⟂ V2 -> vperp V1 V2 = V1 *)
  Lemma vorth_vperp : forall {n} (V1 V2 : vec n),
      V2 <> vzero -> V1 ⟂ V2 -> vperp V1 V2 = V1.
  Proof. intros. unfold vperp. rewrite vorth_vproj; auto. apply vsub_0_r. Qed.

  (** V1 ⟂ V2 -> vnorm V1 ⟂ V2 *)
  Lemma vorth_vnorm_l : forall {n} (V1 V2 : vec n), V1 ⟂ V2 -> vnorm V1 ⟂ V2.
  Proof.
    intros. unfold vorth, vnorm in *. rewrite vdot_vcmul_l.
    rewrite H. autounfold with A. ra.
  Qed.

  (** vnorm V1 ⟂ V2 -> V1 ⟂ V2 *)
  Lemma vorth_vnorm_l_rev : forall {n} (V1 V2 : vec n),
      V1 <> vzero -> vnorm V1 ⟂ V2 -> V1 ⟂ V2.
  Proof.
    intros. unfold vorth, vnorm in *. rewrite vdot_vcmul_l in H0; ra.
    apply Rmult_integral  in H0. destruct H0; auto.
    assert (1 * / (||V1||) <> 0)%R; ra.
    apply vlen_neq0_iff_neq0 in H.
    apply Rmult_integral_contrapositive_currified; ra.
    apply Rinv_neq_0_compat; auto.
  Qed.

  (** V1 ⟂ V2 -> V1 ⟂ vnorm V2 *)
  Lemma vorth_vnorm_r : forall {n} (V1 V2 : vec n), V1 ⟂ V2 -> V1 ⟂ vnorm V2.
  Proof.
    intros. apply vorth_comm. apply vorth_comm in H. apply vorth_vnorm_l; auto.
  Qed.

  (** V1 ⟂ vnorm V2 -> V1 ⟂ V2 *)
  Lemma vorth_vnorm_r_rev : forall {n} (V1 V2 : vec n),
      V2 <> vzero -> V1 ⟂ vnorm V2 -> V1 ⟂ V2.
  Proof.
    intros. apply vorth_comm. apply vorth_comm in H0. apply vorth_vnorm_l_rev; auto.
  Qed.
  
  (** V1 ⟂ V2 -> (k c* V1) ⟂ V2 *)
  Lemma vorth_vcmul_l : forall {n} k (V1 V2 : vec n), V1 ⟂ V2 -> (k c* V1) ⟂ V2.
  Proof.
    intros. unfold vorth, vnorm in *. rewrite vdot_vcmul_l.
    autounfold with A; ra.
  Qed.

  (** (k c* V1) ⟂ V2 -> V1 ⟂ V2 *)
  Lemma vorth_vcmul_l_rev : forall {n} k (V1 V2 : vec n),
      k <> 0 -> (k c* V1) ⟂ V2 -> V1 ⟂ V2.
  Proof.
    intros. unfold vorth, vnorm in *. rewrite vdot_vcmul_l in H0.
    autounfold with A in *; ra.
  Qed.

  (** V1 ⟂ V2 -> V1 ⟂ (k c* V2) *)
  Lemma vorth_vcmul_r : forall {n} k (V1 V2 : vec n), V1 ⟂ V2 -> V1 ⟂ (k c* V2).
  Proof.
    intros. apply vorth_comm. apply vorth_vcmul_l. apply vorth_comm; auto.
  Qed.

  (** V1 ⟂ (k c* V2) -> V1 ⟂ V2 *)
  Lemma vorth_vcmul_r_rev : forall {n} k (V1 V2 : vec n),
      k <> 0 -> V1 ⟂ (k c* V2) -> V1 ⟂ V2.
  Proof.
    intros. apply vorth_comm, vorth_vcmul_l_rev in H0; auto. apply vorth_comm; auto.
  Qed.

  (** vproj ⟂ vperp *)
  Lemma vorth_proj_perp : forall {n} (V1 V2 : vec n),
      V2 <> vzero -> vproj V1 V2 ⟂ vperp V1 V2.
  Proof.
    intros. hnf. unfold vperp, vproj.
    rewrite !vdot_vcmul_l. rewrite vdot_vsub_r. rewrite !vdot_vcmul_r.
    autounfold with A. rewrite (vdot_comm V2 V1). field_simplify; ra.
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
      Note: each pair means {(vi,vj)|i≠j}  *)
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
      For example: [v1;v2;v3] => V1⟂v2 && V1⟂v3 && V2⟂v3. *)
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
      For example: [v1;v2;v3] => unit V1 && unit V2 && unit v3 *)
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
  (* Theorem morth_keep_dot : forall {n} (m : smat n) (V1 V2 : vec n), *)
  (*     morth m -> <m * V1, m * V2> = <v1, V2>. *)
  (* Proof. *)
  (*   intros. *)
  (*   rewrite vdot_eq_mul_trans. *)
  (*   unfold scalar_of_mat, Matrix.scalar_of_mat. *)
  (*   rewrite (m2f_mor _ (v1\T * V2)); auto. *)
  (*   rewrite mtrans_mmul. rewrite mmul_assoc. rewrite <- (mmul_assoc _ m). *)
  (*   rewrite morth_iff_mul_trans_l in H. rewrite H. *)
  (*   rewrite mmul_1_l. easy. *)
  (* Qed. *)

  (* (** Transformation by orthogonal matrix will keep length. *) *)
  (* Corollary morth_keep_length : forall {n} (m : smat n) (V : vec n), *)
  (*     morth m -> ||m * v|| = ||v||. *)
  (* Proof. *)
  (*   intros. rewrite vlen_eq_iff_dot_eq. apply morth_keep_dot. auto. *)
  (* Qed. *)

  (* (** Transformation by orthogonal matrix will keep normalization. *) *)
  (* keep unit?? or keep norm?? or both *)
  (* Corollary morth_keep_normalize : forall {n} (m : smat n) (V : vec n), *)
  (*     morth m -> vnorm (m * v) = m * (vnorm v). *)
  (* Proof. *)
  (*   intros. unfold vnorm. *)
  (*   rewrite morth_keep_length; auto. apply mcmul_mmul_assoc_r. *)
  (* Qed. *)

  (* (** Transformation by orthogonal matrix will keep angle. *) *)
  (* Corollary morth_keep_angle : forall {n} (m : smat n) (V1 V2 : vec n), *)
  (*     morth m -> m * V1 /_ m * V2 = V1 /_ V2. *)
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
    pose (V1 := mkvec3 a1 a2 a3).
    pose (V2 := mkvec3 b1 b2 b3).
    replace (sqrt (a1² + a2² + a3²)) with (vlen V1); [|cbv; f_equal; ring].
    replace (sqrt (b1² + b2² + b3²)) with (vlen V2); [|cbv; f_equal; ring].
    replace (a1 * b1 + a2 * b2 + a3 * b3)%R with (<V1,V2>); [|cbv; f_equal; ring].
    pose proof (vdot_abs_le V1 V2). ra.
  Qed.

End exercise.


(* ######################################################################### *)
(** * Usage demo *)
Section test.
  Let V1 := @l2v 3 [1;2;3].
  Let V2 := @f2v 3 (fun i => 2 + nat2R i)%R.
  
  (* Compute v2l V1. *)
  (* Compute v2l V2. *)
  (* Compute V1$fin0. *)
  (* Compute v2l (vmap V1 Ropp). *)
  (* Compute v2l (vmap2 V1 V2 Rplus). *)
  (* Compute @Vector.v2l _ _ (@Vector.vmap2 _ _ _ pair _ V1 V2). *)
  (* Compute vsum V1 Rplus 0. *)
  (* Compute v2l (V1 + V2). *)

  (* Compute v2l (V1 - V2). *)
  (* Compute v2l (3 c* V1). *)
  (* Compute <V1,V2>. *)
  (* Compute vunitb V1. *)
  (* Compute vnorm V1. *)
  (* Compute vorthb V1 V2. *)
End test.
