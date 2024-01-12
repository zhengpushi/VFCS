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
(** ** Non-zero vector *)

Record vnonzero n :=
  mkvnonzero {
      vnonzeroV :> vec n ;
      vnonzero_cond : vnonzeroV <> vzero
    }.

Arguments mkvnonzero {n}.
Arguments vnonzeroV {n}.
Arguments vnonzero_cond {n}.

(* k c* V1 = V2 -> k <> 0 *)
Lemma vnonzero_vcmul_eq_imply_k_neq0 : forall {n} k (V1 V2 : vnonzero n),
    k c* V1 = V2 -> k <> Azero.
Proof. intros. apply (vcmul_eq_imply_k_neq0 V1 V2); auto. apply V1. apply V2. Qed.

(** Vector scalar multiplication on `vnonzero` *)
Definition vnonzero_cmul {n} (k : nonzeroreal) (V : vnonzero n) : vnonzero n.
  refine (mkvnonzero (vcmul k V) _).
  intro. apply vcmul_eq0_imply_k0_or_V0 in H. destruct k,V,H; auto.
Defined.


(* ======================================================================= *)
(** ** Two vectors are parallel (or called collinear) *)
Section vpara.

  (** Two non-zero vectors are parallel, when their components are proportional *)
  Definition vpara {n} (V1 V2 : vnonzero n) : Prop :=
    exists k : R, k c* V1 = V2.

  Infix "//" := vpara (at level 50) : vec_scope.

  (** vparallel is an equivalence relation *)

  Lemma vpara_refl : forall {n} (V : vnonzero n), V // V.
  Proof. intros. exists 1. apply vcmul_1_l. Qed.

  Lemma vpara_sym : forall {n} (V1 V2 : vnonzero n), V1 // V2 -> V2 // V1.
  Proof.
    intros. destruct H as [k H]. exists (1/k). rewrite <- H.
    rewrite vcmul_assoc. symmetry. rewrite <- vcmul_1_l at 1. f_equal.
    cbv. field. apply vnonzero_vcmul_eq_imply_k_neq0 in H; auto.
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


(* ======================================================================= *)
(** ** Length of a vector *)
Section vlen.

  (** Length (magnitude) of a vector, is derived by inner-product *)
  Definition vlen {n} (V : vec n) : R := sqrt (<V,V>).

  Notation "|| V ||" := (vlen V) : vec_scope.
  
  Lemma vlen2_eq_vdot : forall {n} (V : vec n), ||V||² = <V,V>.
  Proof. intros. unfold vlen. rewrite Rsqr_sqrt; auto. apply vdot_ge0. Qed.

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

  (** ||v|| = 0 <-> V = 0 *)
  Lemma vlen_eq0_iff_eq0 : forall {n} (V : vec n), ||V|| = 0 <-> V = vzero.
  Proof.
    intros. unfold vlen. split; intros.
    - apply vdot_eq0_iff_vzero. apply sqrt_eq_0 in H; auto. apply vdot_ge0.
    - rewrite H. rewrite vdot_0_l. cbv. apply sqrt_0.
  Qed.

  (** ||v|| <> 0 <-> V <> 0 *)
  Lemma vlen_neq0_iff_neq0 : forall {n} (V : vec n), ||V|| <> 0 <-> V <> vzero.
  Proof. intros. rewrite vlen_eq0_iff_eq0. easy. Qed.

  (** V <> vzero -> 0 < ||V|| *)
  Lemma vlen_gt0 : forall {n} (V : vec n), V <> vzero -> 0 < ||V||.
  Proof. intros. pose proof (vlen_ge0 V). apply vlen_neq0_iff_neq0 in H. lra. Qed.

  ?
  (** || V || = 1 <-> <V,V> = 1 *)
  Lemma vlen_eq1_iff_vdot1 : forall {n} (V : vec n), ||V|| = 1 <-> <u,u> = 1.
  Proof. intros. unfold vlen. split; intros; hnf in *. ra. rewrite H. ra. Qed.

  (** || - v|| = || V || *)
  Lemma vlen_copp : forall n (V : vec n), || - v|| = || V ||.
  Proof.
    intros. unfold vlen. f_equal. rewrite vdot_vopp_l,vdot_vopp_r.
    autorewrite with R. auto.
  Qed.
  
  (** ||k c* v|| = |k| * ||v|| *)
  Lemma vlen_cmul : forall n (V : vec n) k, ||k c* v|| = (|k| * ||v||)%R.
  Proof.
    intros. unfold vlen. rewrite vdot_vcmul_l, vdot_vcmul_r.
    rewrite <- Rmult_assoc.
    rewrite sqrt_mult_alt; ra. f_equal. autorewrite with R. ra.
  Qed.

  (** ||u + v|| <= ||u|| + ||v|| *)
  Lemma vlen_add_ineq : forall {n} (u V : vec n), ||(u + v)|| <= ||u|| + ||v||.
  Abort.

  (** |<u,v>| <= ||u|| * ||v|| *)
  Lemma vlen_mul_ineq : forall {n} (u V : vec n), |<u,v>| <= ||u|| * ||v||.
  Abort.
  
  (** 这个性质不成立，有一个例子：相反向量长度相等且平行，但不相等。*)
  Lemma v_eq_iff_len_parallel : forall {n} (V1 V2 : vec n),
      (||v1|| = ||v2|| /\ V1 // V2) <-> V1 = V2.
  Abort.

End vlen.
Notation "|| V ||" := (vlen v) : vec_scope.


(* ======================================================================= *)
(** ** Unit vector *)
Section vunit.

  (** A unit vector u is a vector whose length equals one.
      Here, we use the square of length instead of length directly,
      but this is reasonable with the proof of vunit_ok.
   *)
  Definition vunit {n} (u : vec n) : Prop := <u,u> = 1.

  #[export] Instance vunit_mor {n} : Proper (meq ==> impl) (@vunit n).
  Proof. simp_proper. intros. unfold vunit. rewrite H. easy. Qed.
  
  (** (bool version) *)
  Definition vunitb {n} (u : vec n) : bool := (<u,u> =? 1)%R.

  (** Convenient property *)
  Lemma vlen_vunit : forall {n} (u : vec n), vunit u -> ||u|| = 1.
  Proof. intros. apply vlen_eq1_iff_vdot1. auto. Qed.

  (** Verify the definition is reasonable *)
  Lemma vunit_spec : forall {n} (u : vec n), vunit u <-> ||u|| = 1.
  Proof. intros. split; intros; apply vlen_eq1_iff_vdot1; auto. Qed.

  (** vunit V -> V != vzero. *)
  Lemma vunit_neq0 : forall {n} (V : vec n), vunit V -> V != vzero.
  Proof.
    intros. intro. rewrite H0 in H. unfold vunit in H.
    rewrite vdot_0_l in H. ra.
  Qed.

  (** vunit u <-> vunit (vopp u). *)
  Lemma vopp_vunit : forall {n} (u : vec n), vunit (vopp u) <-> vunit u.
  Proof.
    intros. unfold vunit. rewrite <- !vlen_eq1_iff_vdot1.
    rewrite vlen_copp. easy.
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
(** ** vector normalization *)
Section vnormalize.

  (** Normalization of a non-zero vector V.
    That is, get a unit vector in the same directin as V. *)
  Definition vnorm {n} (V : vec n) : vec n := (1/||v||) c* V.

  #[export] Instance vnorm_mor {n} : Proper (meq ==> meq) (@vnorm n).
  Proof. simp_proper. intros. unfold vnorm. rewrite H. easy. Qed.

  Lemma vnorm_len1 : forall {n} (V : vec n),
      vnonzero V -> ||vnorm v|| = 1.
  Proof.
    (* v̂ = v/|v|, |v̂| = sqrt (v/|v| ⋅ v/|v|) = sqrt ((v⋅v) / (|v|*|v|))
     = sqrt(v⋅v) / |v| = |v| / |v| = 1 *)
    intros. unfold vnorm. unfold vlen.
    rewrite !vdot_vcmul_l, !vdot_vcmul_r. rewrite vdot_same.
    remember (||v||). autounfold with T. autorewrite with R.
    apply sqrt_eq1_imply_eq1_rev.
    assert (|r| = r). { pose proof (vlen_ge0 v). subst. ra. }
    rewrite H0. cbv. field. subst. apply vlen_neq0_iff_neq0; auto.
  Qed.

  (** Unit vector is fixpoint of vnorm operation *)
  Lemma vnorm_vunit_fixpoint : forall {n} (V : vec n),
      vunit V -> vnorm V = V.
  Proof.
    intros. lma. rewrite (vunit_spec v) in H. rewrite H. autorewrite with R. easy.
  Qed.

  (** The component of a normalized vector is equivalent to its original component 
      divide the vector's length *)
  Lemma vnorm_nth : forall {n} (V : vec n) i,
      vnonzero V -> (i < n)%nat -> ((vnorm v) $ i = V $ i / (||v||))%A.
  Proof.
    intros. unfold vnorm. rewrite vcmul_nth; auto.
    autounfold with T. field. apply vlen_neq0_iff_neq0; auto.
  Qed.

  (** Normalization is idempotent *)
  Lemma vnorm_idem : forall {n} (V : vec n),
      vnonzero V -> vnorm (vnorm v) = vnorm V.
  Proof.
    intros. unfold vnorm. rewrite vcmul_assoc.
    assert (1 / (||1 / (||v||) c* v||) = Aone)%A.
    { rewrite vlen_cmul. remember (||v||) as r. autounfold with T.
      replace (|(1/r)|) with (1/r); try field.
      + rewrite Heqr. apply vlen_neq0_iff_neq0; auto.
      + rewrite Rabs_right; auto.
        pose proof (vlen_gt0 V H). rewrite <- Heqr in H0.
        assert (forall r, 0 < r -> 0 <= r). intros. ra.
        apply Rle_ge. apply H1. apply Rdiv_lt_0_compat; lra. }
    rewrite H0. monoid_simp.
  Qed.

  (** Keep the same direction as the original vector *)
  Lemma vnorm_direction : forall {n} (V : vec n),
      vnonzero V -> (vnorm v) // V.
  Proof.
    intros. unfold vpara. unfold vnorm. exists (||v||). split.
    - apply vlen_neq0_iff_neq0; auto.
    - rewrite vcmul_assoc. autounfold with T.
      match goal with | |- context[?a c* _] => replace a with 1 end.
      apply vcmul_1_l. field. apply vlen_neq0_iff_neq0; auto.
  Qed.

  Lemma vnorm_spec : forall {n} (V : vec n),
      vnonzero V -> (||vnorm v|| = 1 /\ (vnorm v) // v).
  Proof.
    intros. split. apply vnorm_len1; auto.
    apply vnorm_direction; auto.
  Qed.

  (** 单位化后的非零向量都是单位向量 *)
  Lemma vnorm_unit : forall {n} (V : vec n),
      vnonzero V -> vunit (vnorm v).
  Proof. intros. apply vunit_spec. apply vnorm_len1; auto. Qed.

End vnormalize.


(* ======================================================================= *)
(* (** ** About {vdot, vunit,  vnorm} *) *)
(* Section vdot_vunit_vnorm. *)
  

(* End vdot_vunit_vangle_vnorm. *)


(* ======================================================================= *)
(** ** Angle between two vectors *)
Section vangle.

  (** The angle from vector V1 to vector V2, Here, θ ∈ [0,π] *)
  Definition vangle {n} (V1 V2 : vec n) : R :=
    let V1' := vnorm V1 in
    let V2' := vnorm V2 in
    acos (<v1', V2'>).
  
  Infix "∠" := vangle (at level 60) : vec_scope.

  #[export] Instance vangle_mor {n} : Proper (meq ==> meq ==> eq) (@vangle n).
  Proof.
    simp_proper. intros. unfold vangle. rewrite H,H0. auto.
  Qed.

  (** Angle is commutative *)
  Lemma vangle_comm : forall {n} (V1 V2 : vec n), V1 ∠ V2 = V2 ∠ V1.
  Proof. intros. unfold vangle. rewrite vdot_comm. auto. Qed.
  
  (** The angle between (1,0,0) and (1,1,0) is 45 degree, i.e., π/4 *)
  (* Remark: Here, we can finish a demo proof with a special value π/4,
     but real cases maybe have any value, it is hard to finished in Coq.
     Because the construction of {sqrt, acos, PI, etc} is complex. *)
  Example vangle_ex1 : (@l2v 3 [1;0;0]) ∠ (l2v [1;1;0]) = PI/4.
  Proof.
    rewrite <- acos_inv_sqrt2.
    compute. f_equiv. autorewrite with R. auto.
  Qed.

  (** The law of cosine *)
  Axiom cosine_law : forall {n} (a b : vec n),
      ((||(a - b)%V||)² = ||a||² + ||b||² - 2 * ||a|| * ||b|| * cos (vangle a b))%R.

  (** The relation between dot product and the cosine of angle in 2D *)
  Theorem vdot_eq_cos_angle : forall {n} (a b : vec n),
      <a,b> = (||a|| * ||b|| * cos (vangle a b))%R.
  Proof.
    intros.
    (* construct another form of "cosine_law" *)
    assert (||(a-b)%V||² = ||a||² + ||b||² - 2 * <a,b>)%R.
    { rewrite <- !vdot_same. unfold vsub.
      rewrite !vdot_vadd_distr_l, !vdot_vadd_distr_r.
      rewrite !vdot_vopp_l, !vdot_vopp_r. rewrite (vdot_comm b a).
      autounfold with T; ring. }
    pose proof (cosine_law a b). ra.
  Qed.

  (** 单位向量的点积介于[-1,1] *)
  Lemma vdot_unit_bound : forall {n} (u V : vec n),
      vunit u -> vunit V -> -1 <= <u,v> <= 1.
  Proof.
    intros. rewrite vdot_eq_cos_angle.
    rewrite ?vlen_vunit; auto.
    match goal with |- context [cos ?r] => remember r as a end.
    pose proof (COS_bound a). lra.
  Qed.

  (** 单位化后的非零向量的点积介于 [-1,1] *)
  Lemma vdot_vnormalize_bound : forall {n} (u V : vec n),
      vnonzero u -> vnonzero V ->
      -1 <= <vnorm u, vnorm v> <= 1.
  Proof. intros. apply vdot_unit_bound; apply vnorm_unit; auto. Qed.

  (** 0 <= vangle u V <= PI *)
  Lemma vangle_bound : forall {n} (u V : vec n), 0 <= vangle u V <= PI.
  Proof. intros. unfold vangle. apply acos_bound. Qed.

  (** 0 <= sin (vangle u v) *)
  Lemma sin_vangle_ge0 : forall {n} (u V : vec n), 0 <= sin (vangle u v).
  Proof. intros. apply sin_ge_0; apply vangle_bound. Qed.
  
  (** θ ≠ 0 -> θ ≠ π -> 0 < sin (vangle u v) *)
  Lemma sin_vangle_gt0 : forall {n} (u V : vec n),
      u ∠ V <> 0 -> u ∠ V <> PI -> 0 < sin (u ∠ v).
  Proof. intros. pose proof (vangle_bound u v). apply sin_gt_0; ra. Qed.

  (* (** V1 ∠ V2 = 0 <-> V1,v2同向平行 *) *)
  (* Lemma vangle_eq0_vpara : forall {n} (V1 V2 : vec n), *)
  (*     vnonzero V1 -> vnonzero V2 -> *)
  (*     (vangle V1 V2 = 0 <-> (exists k : R, k > 0 /\ k c* V1 = V2)). *)
  (* Proof. *)
  (*   intros. unfold vangle. split; intros. *)
  (*   2:{ *)
  (*     destruct H1 as [k [H11 H12]]. *)
  (*     rewrite <- H12. rewrite <- acos_1. f_equal. *)
  (*     unfold vnorm. *)
  (*     rewrite vcmul_assoc, !vdot_vcmul_l, !vdot_vcmul_r. *)
  (*     rewrite vlen_cmul. rewrite vdot_same. rewrite Rabs_right; ra. *)
  (*     autounfold with T. field. *)
  (*     apply vlen_neq0_iff_neq0 in H,H0. lra. } *)
  (*   1:{ *)
  (*     rewrite <- acos_1 in H1. apply acos_inj in H1; ra. *)
  (*     2:{ apply vdot_vnormalize_bound; auto. } *)
  (*     1:{ *)
  (*       (** *)
  (*          V1 ∠ V2 = 0 -> acos(<v1',v2'>) = 0, where V1',v2' is normalized V1,v2. *)
  (*          then <v1',v2'> = 1. that is <vnormlize V1, vnorm V2> = , *)
  (*          then (1/(|v1|*|v2|)) * <v1,v2> = 1 *)
  (*          可以借助投影来表明 V1和v2是k倍的关系 *)
  (*        *) *)
  (*       exists (||v1|| * ||v2||)%R. *)
  (*       rewrite vdot_eq_cos_angle in H1. *)
  (*       Admitted. *)

  (** 相同的向量之间的角度是 0。可能还有一个特例，两个0向量之间的夹角可能是任意值 *)
  Lemma vangle_same_eq0 : forall {n} (V : vec n),
      vnonzero V -> V ∠ V = 0.
  Proof.
    intros. unfold vangle. rewrite vdot_same.
    rewrite vnorm_len1; auto. autorewrite with R. apply acos_1.
  Qed.

  (** V1 ∠ v3 = (V1 ∠ V2) + (v2 ∠ v3) *)
  Lemma vangle_add : forall (V1 V2 v3 : vec 3),
      V1 ∠ V2 < PI ->
      V2 ∠ v3 < PI ->
      V1 ∠ v3 = ((V1 ∠ V2) + (v2 ∠ v3))%R.
  Proof.
  (** 由于目前 vangle 的值域是 [0,π]，暂不能表示 [0,2π)，所以该性质有点困难。
      有扩展了值域为 [0,2π) 的 V2angle 可做参考。
      在3D中，需要增加共面的条件。*)
  Admitted.

  Lemma Rdiv_1_neq_0_compat : forall r : R, r <> 0 -> 1 / r <> 0.
  Proof. intros. pose proof (Rinv_neq_0_compat r H). ra. Qed.

  
  (* (** 给定两个向量，若将这两个向量同时旋转θ角，则向量之和在旋转前后的夹角也是θ。*) *)
  (* Lemma vangle_vadd : forall (V1 V2 V1' V2' : vec 2), *)
  (*     vnonzero V1 -> vnonzero V2 -> *)
  (*     ||v1|| = ||v1'|| -> ||v2|| = ||v2'|| -> *)
  (*     V1 ∠ V2 = V1' ∠ V2' -> *)
  (*     V1 + V2 ∠ V1' + V2' = V1 ∠ V1'. *)
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
  (*   apply acos_inj in Hangle_eq; try apply vdot_vnormalize_bound; auto. *)
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
  (*   Admitted. *)

  (** 给定两个向量，若将这两个向量同时旋转θ角，则向量之和在旋转前后的夹角也是θ。*)
  Lemma vangle_vadd : forall (V1 V2 V1' V2' : vec 3),
      vnonzero V1 -> vnonzero V2 ->
      ||v1|| = ||v1'|| -> ||v2|| = ||v2'|| ->
      V1 ∠ V2 = V1' ∠ V2' ->
      V1 + V2 ∠ V1' + V2' = V1 ∠ V1'.
  Proof.
    Admitted.
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
    (* apply acos_inj in Hangle_eq; try apply vdot_vnormalize_bound; auto. *)
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
    

  (** a <> 0 -> (a c* V1) ∠ V2 = V1 ∠ V2 *)
  Lemma vangle_vcmul_l : forall {n} (V1 V2 : vec n) (a : R),
      a <> 0 -> (a c* V1) ∠ V2 = V1 ∠ V2.
  Proof.
  Admitted.

  (** a <> 0 -> V1 ∠ (a c* V2) = V1 ∠ V2 *)
  Lemma vangle_vcmul_r : forall {n} (V1 V2 : vec n) (a : R),
      a <> 0 -> V1 ∠ (a c* V2) = V1 ∠ V2.
  Proof.
  Admitted.

  Lemma vangle_vnorm_l : forall {n} (V1 V2 : vec n),
      vnorm V1 ∠ V2 = V1 ∠ V2.
  Admitted.
  Lemma vangle_vnorm_r : forall {n} (V1 V2 : vec n),
      V1 ∠ vnorm V2 = V1 ∠ V2.
  Admitted.

End vangle.
Infix "∠" := vangle (at level 60) : vec_scope.


(* ======================================================================= *)
(** ** Projection component of a vector onto another *)
Section vproj.

  (** The projection component of a onto b *)
  Definition vproj {n} (a b : vec n) : vec n := (<a,b> / <b,b>) c* b.

  (* (** The scalar projection of a on b is a simple triangle relation *) *)
  (* Lemma vsproj_spec : forall {n} (a b : vec n), vsproj a b = `|a| * vangle. *)

  #[export] Instance vproj_mor {n} : Proper (meq ==> meq ==> meq) (@vproj n).
  Proof. simp_proper. intros. unfold vproj. rewrite H,H0. easy. Qed.

  (** vproj (a1 + a2) b = vproj a1 b + vproj a2 b *)
  Lemma vproj_linear_vadd : forall {n} (a1 a2 b : vec n),
      vnonzero b -> (vproj (a1 + a2) b = vproj a1 b + vproj a2 b)%V.
  Proof.
    intros. unfold vproj. rewrite vdot_vadd_distr_l.
    rewrite <- vcmul_add_distr. f_equiv. autounfold with T. field.
    rewrite vdot_same. apply vlen_gt0 in H. ra.
  Qed.

  (** vproj (k * a) b = k * (vproj a b) *)
  Lemma vproj_linear_vcmul : forall {n} (a b : vec n) (k : R),
      vnonzero b -> (vproj (k c* a) b = k c* (vproj a b))%V.
  Proof.
    intros. unfold vproj. rewrite vdot_vcmul_l. rewrite vcmul_assoc. f_equiv.
    autounfold with T. field.
    rewrite vdot_same. apply vlen_gt0 in H. ra.
  Qed.
  
  (** vproj a a = a *)
  Lemma vproj_same : forall {n} (a : vec n), vnonzero a -> vproj a a = a.
  Proof.
    intros. unfold vproj. replace (<a,a> / <a,a>) with 1; try field.
    apply vcmul_1_l. rewrite vdot_same. apply vlen_gt0 in H. ra.
  Qed.
  
End vproj.


(* ======================================================================= *)
(** ** Perpendicular component of a vector respect to another *)
Section vperp.

  (** The perpendicular component of a respect to b *)
  Definition vperp {n} (a b : vec n) : vec n := a - vproj a b.
  
  #[export] Instance vperp_mor {n} : Proper (meq ==> meq ==> meq) (@vperp n).
  Proof. simp_proper. intros. unfold vperp. rewrite H,H0. easy. Qed.

  (** vperp (a1 + a2) b = vperp a1 b + vperp a2 b *)
  Lemma vperp_linear_vadd : forall {n} (a1 a2 b : vec n),
      vnonzero b -> (vperp (a1 + a2) b = vperp a1 b + vperp a2 b)%V.
  Proof.
    intros. unfold vperp. rewrite vproj_linear_vadd; auto.
    unfold vsub. elimh. rewrite vopp_vadd. easy.
  Qed.

  (** vperp (k * a) b = k * (vperp a b) *)
  Lemma vperp_linear_vcmul : forall {n} (a b : vec n) (k : R),
      vnonzero b -> (vperp (k c* a) b = k c* (vperp a b))%V.
  Proof.
    intros. unfold vperp. rewrite vproj_linear_vcmul; auto.
    rewrite vcmul_vsub. easy.
  Qed.

  (** vperp a a = 0 *)
  Lemma vperp_same : forall {n} (a : vec n), vnonzero a -> vperp a a = vzero.
  Proof.
    intros. unfold vperp. rewrite vproj_same; auto; auto. apply vsub_self.
  Qed.
  
End vperp.


(* ======================================================================= *)
(** ** Orthogonal vectors 正交的两个向量 *)
Section vorth.

  (** Two vectors, x and y, in an inner product space V, are orthogonal if their 
    inner-product <x,y> is zero, and the relationship is denoted x ⟂ y. *)

  (** Two real column-vectors are orthogonal (also called perpendicular) *)
  Definition vorth {n} (V1 V2 : vec n) : Prop := <v1,v2> = 0.

  (** Bool version to determine if two vectors are orthogonal *)
  Definition vorthb {n} (V1 V2 : vec n) : bool := (<v1,v2> =? 0)%R.
  Infix "⟂" := vorth ( at level 50).

  #[export] Instance vorth_mor {n} :
    Proper (meq ==> meq ==> impl) (@vorth n).
  Proof.
    simp_proper. intros. unfold vorth. rewrite H,H0. easy.
  Qed.

  (** u ⟂ V -> V ⟂ u *)
  Lemma vorth_comm : forall (u V : vec 3), u ⟂ V -> V ⟂ u.
  Proof. intros. unfold vorth in *. rewrite vdot_comm; auto. Qed.

  (** u ⟂ V -> vproj u V = vzero *)
  Lemma vorth_vproj : forall (u V : vec 3),
      vnonzero V -> u ⟂ V -> vproj u V = vzero.
  Proof.
    intros. unfold vorth in H0.
    unfold vproj. rewrite H0. autorewrite with R. rewrite vcmul_0_l; easy.
    apply vdot_same_neq0; auto.
  Qed.
  
  (** u ⟂ V -> vperp u V = u *)
  Lemma vorth_vperp : forall (u V : vec 3),
      vnonzero V -> u ⟂ V -> vperp u V = u.
  Proof.
    intros. unfold vperp. rewrite vorth_vproj; auto. apply vsub_0_r.
  Qed.

  (** u ⟂ V -> vnorm u ⟂ V *)
  Lemma vorth_vnorm_l : forall (u V : vec 3), u ⟂ V -> vnorm u ⟂ V.
  Proof.
    intros. unfold vorth, vnorm in *. rewrite vdot_vcmul_l; ra.
  Qed.

  (** vnorm u ⟂ V -> u ⟂ V *)
  Lemma vorth_vnorm_l_reV : forall (u V : vec 3),
      u != vzero -> vnorm u ⟂ V -> u ⟂ V.
  Proof.
    intros. unfold vorth, vnorm in *.
    rewrite vdot_vcmul_l in H0; ra.
    assert (1 * / (||u||) <> 0)%R; ra.
    apply vlen_neq0_iff_neq0 in H.
    apply Rmult_integral_contrapositive_currified; ra.
    apply Rinv_neq_0_compat; auto.
  Qed.

  (** u ⟂ V -> vnorm u ⟂ V *)
  Lemma vorth_vnorm_r : forall (u V : vec 3), u ⟂ V -> u ⟂ vnorm V.
  Proof.
    intros. unfold vorth, vnorm in *. rewrite vdot_vcmul_r; ra.
  Qed.

  (** u ⟂ vnorm V -> u ⟂ V *)
  Lemma vorth_vnorm_r_reV : forall (u V : vec 3),
      V != vzero -> u ⟂ vnorm V -> u ⟂ V.
  Proof.
    intros. unfold vorth, vnorm in *.
    rewrite vdot_vcmul_r in H0; ra. assert (1 * / (||v||) <> 0)%R; ra.
    apply vlen_neq0_iff_neq0 in H.
    apply Rmult_integral_contrapositive_currified; ra.
    apply Rinv_neq_0_compat; auto.
  Qed.
  
  (** u ⟂ V -> (k c* u) ⟂ V *)
  Lemma vorth_vcmul_l : forall (u V : vec 3) (k : R), u ⟂ V -> (k c* u) ⟂ V.
  Proof.
    intros. unfold vorth, vnorm in *. rewrite vdot_vcmul_l; ra.
  Qed.

  (** (k c* u) ⟂ V -> u ⟂ V *)
  Lemma vorth_vcmul_l_reV : forall (u V : vec 3) (k : R),
      k <> 0 -> (k c* u) ⟂ V -> u ⟂ V.
  Proof.
    intros. unfold vorth, vnorm in *. rewrite vdot_vcmul_l in H0; ra.
  Qed.

  (** u ⟂ V -> u ⟂ (k c* v) *)
  Lemma vorth_vcmul_r : forall (u V : vec 3) (k : R), u ⟂ V -> u ⟂ (k c* v).
  Proof.
    intros. unfold vorth, vnorm in *. rewrite vdot_vcmul_r; ra.
  Qed.

  (** u ⟂ (k c* v) -> u ⟂ V *)
  Lemma vorth_vcmul_r_reV : forall (u V : vec 3) (k : R),
      k <> 0 -> u ⟂ (k c* v) -> u ⟂ V.
  Proof.
    intros. unfold vorth, vnorm in *. rewrite vdot_vcmul_r in H0; ra.
  Qed.

  (** vproj ⟂ vperp *)
  Lemma vorth_proj_perp : forall {n} (u V : vec n), vproj u V ⟂ vperp u V.
  Proof.
    intros. hnf. unfold vperp, vproj.
    (* unfold vperp. unfold vsub. rewrite vdot_vadd_distr_r. *)
    (* 以下证明思路明显是错误的，不可能所有元素都是0 *)
    apply seqsum_eq0.
    intros.
    vec2fun. simpl.
    unfold vdot, Vector.vdot. simpl.
    autorewrite with R.
    remember (seqsum (fun i0 : nat => V i0 0%nat * V i0 0%nat) n)%A as r1.
    remember (seqsum (fun i0 : nat => u i0 0%nat * V i0 0%nat) n)%A as r2.
  Abort.
  
End vorth.
Infix "⟂" := vorth ( at level 50).


(* ======================================================================= *)
(** ** Orthogonal set 正交向量组（集） *)
Section vorthset.

  (** A set of vectors in an inner product space is called pairwise orthogonal if 
      each pairing of them is orthogonal. Such a set is called an orthogonal set.
      Note: each pair means {(vi,vj)|i≠j}  *)
  Definition vorthset {r c} (m : mat r c) : Prop :=
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
  Admitted.

  Example vorthset_ex1 :
    vorthset (@l2m 3 3 [[1;1;1];[0;sqrt 2; -(sqrt 2)];[-1;1;1]])%A.
  Proof.
    apply vorthsetb_true_iff. cbv.
    (** Auto solve equality contatin "Req_EM_T" *)
    repeat
      match goal with
      | |- context[ Req_EM_T ?a ?b] => destruct Req_EM_T; try lra
      end.
    autorewrite with R sqrt in *; ra.
  Qed.
End vorthset.


(* ======================================================================= *)
(** ** Orthonormal vectors 标准正交的向量组 *)
Section mcolsOrthonormal.

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
  Admitted.

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
  Admitted.

  (** The columns of a matrix is orthogomal *)
  Definition mcolsOrthonormal {r c} (m : mat r c) : Prop :=
    mcolsorth m /\ mcolsUnit m.

End mcolsOrthonormal.


(* ======================================================================= *)
(** ** Orthogonal matrix *)
Section morth.

  (** matrix m is orthogonal <-> columns of m are orthogomal *)
  Lemma morth_iff_mcolsOrthonormal : forall {n} (m : smat n),
      morth m <-> mcolsOrthonormal m.
  Proof.
    intros.
    unfold morth,mcolsOrthonormal.
    unfold mcolsorth, mcolsUnit.
    unfold vorth, vunit.
    split; intros.
    - split; intros.
      + rewrite vdot_col_col; auto. rewrite H; auto. rewrite mnth_mat1_diff; auto.
      + rewrite vdot_col_col; auto. rewrite H; auto. rewrite mnth_mat1_same; auto.
    - destruct H as [H1 H2]. hnf. intros. rewrite <- vdot_col_col; auto.
      bdestruct (i =? j)%nat.
      + subst. rewrite mnth_mat1_same; auto. apply H2; auto.
      + rewrite mnth_mat1_diff; auto. apply H1; auto.
  Qed.

  (** Transformation by orthogonal matrix will keep inner-product *)
  Theorem morth_keep_dot : forall {n} (m : smat n) (V1 V2 : vec n),
      morth m -> <m * V1, m * V2> = <v1, V2>.
  Proof.
    intros.
    rewrite vdot_eq_mul_trans.
    unfold scalar_of_mat, Matrix.scalar_of_mat.
    rewrite (m2f_mor _ (v1\T * V2)); auto.
    rewrite mtrans_mmul. rewrite mmul_assoc. rewrite <- (mmul_assoc _ m).
    rewrite morth_iff_mul_trans_l in H. rewrite H.
    rewrite mmul_1_l. easy.
  Qed.

  (** Transformation by orthogonal matrix will keep length. *)
  Corollary morth_keep_length : forall {n} (m : smat n) (V : vec n),
      morth m -> ||m * v|| = ||v||.
  Proof.
    intros. rewrite vlen_eq_iff_dot_eq. apply morth_keep_dot. auto.
  Qed.

  (** Transformation by orthogonal matrix will keep normalization. *)
  Corollary morth_keep_normalize : forall {n} (m : smat n) (V : vec n),
      morth m -> vnorm (m * v) = m * (vnorm v).
  Proof.
    intros. unfold vnorm.
    rewrite morth_keep_length; auto. apply mcmul_mmul_assoc_r.
  Qed.

  (** Transformation by orthogonal matrix will keep angle. *)
  Corollary morth_keep_angle : forall {n} (m : smat n) (V1 V2 : vec n),
      morth m -> m * V1 ∠ m * V2 = V1 ∠ V2.
  Proof.
    intros. unfold vangle. f_equal. rewrite !morth_keep_normalize; auto.
    rewrite morth_keep_dot; auto.
  Qed.

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
    pose (a := t2v_3 (a1,a2,a3)).
    pose (b := t2v_3 (b1,b2,b3)).
    pose (alen := vlen a).
    pose (blen := vlen b).
    replace (sqrt _) with alen; [| unfold alen; cbv; f_equal; ring].
    replace (sqrt _) with blen; [| unfold blen; cbv; f_equal; ring].
    replace (Rabs _) with (|<a,b>|); [| cbv; autorewrite with R; auto].
  Abort.

End exercise.


(* ######################################################################### *)
(** * Usage demo *)
Section test.
  Let l1 := [1;2;3].
  Let V1 := @l2rv 2 l1.
  Let V2 := @l2v 2 l1.
  (* Compute rv2l V1. *)
  (* Compute V2l V2. *)


  Variable a1 a2 a3 : A.
  Variable f : A -> T.
  Let v3 := t2rv_3 (a1,a2,a3).
  Let v4 := t2v_3 (a1,a2,a3).
  (* Compute rv2l (rvmap v3 f). *)
  (* Compute V2l (vmap v4 f). *)
  
End test.
