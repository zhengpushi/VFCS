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


(* ======================================================================= *)
(** * Vector theory come from common implementations *)

Open Scope R_scope.
Open Scope mat_scope.
Open Scope vec_scope.

(** general notations *)
Notation A := R.
Notation A0 := R0.
Notation A1 := R1.
Notation Aadd := Rplus.
Notation Aopp := Ropp.
Notation Amul := Rmult.
Notation Ainv := Rinv.

(** ** vector type and basic operation *)
Section basic.

  (** *** vector type *)
  Definition vec (n : nat) : Type := @vec A n.

  Notation "v ! i" := (vnth A0 v i) : vec_scope.

  Lemma veq_iff_vnth : forall {n : nat} (v1 v2 : vec n),
      (v1 == v2) <-> (forall i, i < n -> v1!i = v2!i)%nat.
  Proof. apply veq_iff_vnth. Qed.

  (** *** convert between list and vector *)
  Definition l2v n (l : list A) : vec n := l2v A0 n l.
  Definition v2l {n} (v : vec n) : list A := v2l v.

  Lemma v2l_length : forall {n} (v : vec n), length (v2l v) = n.
  Proof. intros. apply v2l_length. Qed.

  Lemma v2l_l2v_id : forall {n} (l : list A), length l = n -> v2l (l2v n l) = l.
  Proof. intros. apply v2l_l2v_id; auto. Qed.

  Lemma l2v_v2l_id : forall {n} (v : vec n), l2v n (v2l v) == v.
  Proof. intros. apply l2v_v2l_id; auto. Qed.

  (** *** convert between tuples and vector *)
  Definition t2v_2 (t : T2) : vec 2 := t2v_2 A0 t.
  Definition t2v_3 (t : T3) : vec 3 := t2v_3 A0 t.
  Definition t2v_4 (t : T4) : vec 4 := t2v_4 A0 t.

  Definition v2t_2 (v : vec 2) : T2 := v2t_2 v.
  Definition v2t_3 (v : vec 3) : T3 := v2t_3 v.
  Definition v2t_4 (v : vec 4) : T4 := v2t_4 v.

  (* Lemma t2v_v2t_id_2 : forall (v : vec 2), t2v_2 (v2t_2 v) == v. *)
  (* Lemma v2t_t2v_id_2 : forall (t : T2), v2t_2 (t2v_2 t) = t. *)

  (** *** make concrete vector *)
  Definition mk_vec2 a0 a1 : vec 2 := mk_vec2 A0 a0 a1.
  Definition mk_vec3 a0 a1 a2 : vec 3 := mk_vec3 A0 a0 a1 a2.
  Definition mk_vec4 a0 a1 a2 a3 : vec 4 := mk_vec4 A0 a0 a1 a2 a3.

  (** *** vector mapping *)
  Definition vmap {n} f (v : vec n) : vec n := vmap v f.
  Definition vmap2 {n} f (v1 v2 : vec n) : vec n := vmap2 v1 v2 f.

  (** *** vector folding *)
  (* Definition vfold : forall {B : Type} {n} (v : vec n) (f : A -> B) (b : B), B. *)
  
End basic.

Notation "v ! i" := (vnth A0 v i) : vec_scope.

(** Convert vec to function *)
Ltac vec_to_fun :=
  repeat match goal with
    | v:vec ?n |- _ => destruct v as [v]; simpl in *
    end.


(** ** Linear operations of vector *)
Section algebra.

  (** *** make a zero vector *)
  Definition vec0 {n} : vec n := vec0 (A0:=A0).
  
  (** Every 0-dim vector is a zero-vector, i.e., it is unique *)
  Lemma vec_len0_is_vec0 : forall v : vec 0, v == vec0.
  Proof. lva. Qed.

  (** *** vector addition *)
  Definition vadd {n} (v1 v2 : vec n) : vec n := vadd v1 v2 (Aadd:=Aadd).
  Infix "+" := vadd : vec_scope.

  Lemma vadd_comm : forall {n} (v1 v2 : vec n), (v1 + v2) == (v2 + v1).
  Proof. intros. apply vadd_comm. Qed.

  Lemma vadd_assoc : forall {n} (v1 v2 v3 : vec n), (v1 + v2) + v3 == v1 + (v2 + v3).
  Proof. intros. apply vadd_assoc. Qed.

  Lemma vadd_0_l : forall {n} (v : vec n), vec0 + v == v.
  Proof. intros. apply vadd_0_l. Qed.

  Lemma vadd_0_r : forall {n} (v : vec n), v + vec0 == v.
  Proof. intros. apply vadd_0_r. Qed.

  (** *** vector opposition *)
  Definition vopp {n} (v : vec n) : vec n := vopp v (Aopp:=Aopp).
  Notation "- v" := (vopp v) : vec_scope.

  Lemma vadd_opp_l : forall {n} (v : vec n), (- v) + v == vec0.
  Proof. intros. apply vadd_opp_l. Qed.

  Lemma vadd_opp_r : forall {n} (v : vec n), v + (- v) == vec0.
  Proof. intros. apply vadd_opp_r. Qed.

  (** *** vector subtraction *)
  Definition vsub {n} (v1 v2 : vec n) : vec n := vsub v1 v2 (Aadd:=Aadd) (Aopp:=Aopp).
  Infix "-" := vsub : vec_scope.

  (** *** vector scalar multiplication *)
  Definition vcmul {n} a (v : vec n) : vec n := vcmul a v (Amul:=Amul).
  Infix "c*" := vcmul : vec_scope.

  (** vcmul is a proper morphism *)
  Global Instance vcmul_mor : forall n, Proper (eq ==> meq ==> meq) (vcmul (n:=n)).
  Proof. apply vcmul_mor. Qed.

  Lemma vcmul_assoc : forall {n} a b (v : vec n), a c* (b c* v) == (a * b) c* v.
  Proof. intros. apply vcmul_assoc. Qed.

  Lemma vcmul_perm : forall {n} a b (v : vec n), a c* (b c* v) == b c* (a c* v).
  Proof. intros. apply vcmul_perm. Qed.

  Lemma vcmul_add_distr_l : forall {n} a b (v : vec n), (a + b) c* v == (a c* v) + (b c* v).
  Proof. intros. apply vcmul_add_distr_l. Qed.

  Lemma vcmul_add_distr_r : forall {n} a (v1 v2 : vec n),
      a c* (v1 + v2) == (a c* v1) + (a c* v2).
  Proof. intros. apply vcmul_add_distr_r. Qed.

  Lemma vcmul_0_l : forall {n} (v : vec n), A0 c* v == vec0.
  Proof. intros. apply vcmul_0_l. Qed.

  Lemma vcmul_1_l : forall {n} (v : vec n), A1 c* v == v.
  Proof. intros. apply vcmul_1_l. Qed.

  Definition vmulc {n} (v : vec n) a : vec n := vmulc v a (Amul:=Amul).
  Infix "*c" := vmulc : vec_scope.

  Lemma vmulc_eq_vcmul : forall {n} a (v : vec n), (v *c a) == (a c* v).
  Proof. intros. apply vmulc_eq_vcmul. Qed.

End algebra.

Infix "+" := vadd : vec_scope.
Notation "- v" := (vopp v) : vec_scope.
Infix "-" := vsub : vec_scope.
Infix "c*" := vcmul : vec_scope.
Infix "*c" := vmulc : vec_scope.


(** ** vector dot product *)
Section vdot.
  
  Definition vdot {n} (v1 v2 : vec n) := vdot v1 v2 (Aadd:=Aadd)(A0:=A0)(Amul:=Amul).
  Infix "⋅" := vdot : vec_scope.

  Lemma vdot_comm : forall {n} (v1 v2 : vec n), v1 ⋅ v2 = v2 ⋅ v1.
  Proof. intros. apply vdot_comm. Qed.

  Lemma vdot_add_distr_l : forall {n} (v1 v2 v3 : vec n),
      (v1 + v2) ⋅ v3 = (v1 ⋅ v3 + v2 ⋅ v3)%R.
  Proof. intros. apply vdot_add_distr_l. Qed.

  Lemma vdot_add_distr_r : forall {n} (v1 v2 v3 : vec n),
      v1 ⋅ (v2 + v3) = (v1 ⋅ v2 + v1 ⋅ v3)%R.
  Proof. intros. apply vdot_add_distr_r. Qed.

  Lemma vdot_cmul_l : forall {n} (v1 v2 : vec n) (a : A),
      (a c* v1) ⋅ v2 = (a * (v1 ⋅ v2))%R.
  Proof. intros. apply vdot_cmul_l. Qed.

  Lemma vdot_cmul_r : forall {n} (v1 v2 : vec n) (a : A),
      v1 ⋅ (a c* v2) = (a * (v1 ⋅ v2))%R.
  Proof. intros. apply vdot_cmul_r. Qed.

  Lemma vdot_0_l : forall {n} (v : vec n), vec0 ⋅ v = A0.
  Proof. intros. apply vdot_0_l. Qed.

  Lemma vdot_0_r : forall {n} (v : vec n), v ⋅ vec0 = A0.
  Proof. intros. apply vdot_0_r. Qed.

  Lemma vdot_ge0 : forall {n} (v : vec n), 0 <= v ⋅ v.
  Proof.
    intros. vec_to_fun. unfold vdot,Vector.vdot. simpl.
    revert v. induction n; intros; simpl; try lra. ra.
  Qed.

End vdot.

Infix "⋅" := vdot : vec_scope.


(* ======================================================================= *)
(** * Vector theory applied to this type *)


(** ** zero or nonzero vector *)
Section vzero_vnonzero.
  
  (** A vector is a zero vector. *)
  Definition vzero {n} (v : vec n) : Prop := vzero v (A0:=0).

  (** A vector is a non-zero vector. *)
  Definition vnonzero {n} (v : vec n) : Prop := vnonzero v (A0:=0).

  (** Any zero vector is vec0 *)
  Lemma vzero_imply_vec0 : forall {n} (v : vec n), vzero v -> v == vec0.
  Proof. intros. auto. Qed.

  (** If k times a non-zero vector equal to zero vector, then k must be not zero *)
  Lemma vcmul_vnonzero_neq0_imply_neq0 : forall {n} (v : vec n) k,
      vnonzero v -> ~(k c* v == vec0) -> k <> 0.
  Proof. intros. intro. subst. rewrite vcmul_0_l in H0. destruct H0. easy. Qed.

  (** Two non-zero vectors has k-times relation, then k is not zero *)
  Lemma vec_eq_vcmul_imply_coef_neq0 : forall {n} (v1 v2 : vec n) k,
      vnonzero v1 -> vnonzero v2 -> v1 == k c* v2 -> k <> 0.
  Proof. intros. intro. subst. rewrite vcmul_0_l in H1. easy. Qed.

  (** If k times a non-zero vector equal to zero, then k must be zero *)
  (*
    v <> 0 ==> ~(∀ i, v[i] = 0)
    k*v = 0 ==> ∀ i, k*v[i] = 0
    {k=0}+{k<>0} ==> k<>0  (if k=0, then qed)
    ---------------------------
    ∃ i, v[i] <> 0, then, k*v[i] <> 0, thus, contradict.
   *)
  Lemma vcmul_nonzero_eq_zero_imply_k0 : forall {n} (v : vec n) k,
      vnonzero v -> k c* v == vec0 -> k = 0.
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
  Lemma vcmul_vnonzero_eq_iff_unique_k : forall {n} (v : vec n) k1 k2, 
      vnonzero v -> k1 c* v == k2 c* v -> k1 = k2.
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
  Lemma vcmul_vnonzero_eq_self_imply_k1 : forall {n} (v : vec n) k,
      vnonzero v -> k c* v == v -> k = 1.
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
  Definition vlen {n} (v : vec n) : R := sqrt (v ⋅ v).

  Notation "`| v |" := (vlen v) : vec_scope.

  Lemma vdot_same_eq : forall {n} (v : vec n), v ⋅ v = (vlen v)².
  Proof. intros. unfold vlen. rewrite Rsqr_sqrt; auto. apply vdot_ge0. Qed.
    
  (** Length of a vector u is 1, iff the dot product of u and u is 1 *)
  Lemma vlen1_iff_vdot1 : forall n (u : vec n), `|u| = 1 <-> u ⋅ u = 1.
  Proof. intros. unfold vlen. split; intros; hnf in *. ra. rewrite H. ra. Qed.

End vlen.

Notation "`| v |" := (vlen v) : vec_scope.


(** ** unit vector *)
Section vunit.

  (** A unit vector u is a vector whose length equals one.
      Here, we use the square of length instead of length directly,
      but this is reasonable with the proof of vunit_ok.
   *)
  Definition vunit {n} (u : vec n) : Prop := u ⋅ u = 1.

  (** Verify the definition is reasonable *)
  Lemma vunit_ok : forall {n} (u : vec n), vunit u <-> `|u| = 1.
  Proof. intros. split; intros; apply vlen1_iff_vdot1; auto. Qed.

  (** Normalization of a non-zero vector v.
      That is, get a unit vector in the same directin as v. *)
  Definition vnormalize {n} (v : vec n) : vec n := `|v| c* v.

End vunit.


(** ** Angle between two vectors *)
Section vangle.

  (** Cosine of the angle between two vectors, only valid when both are nonzero *)
  Definition vangle_cos {n} (v1 v2 : vec n) : R := (v1 ⋅ v2) / (`|v1| * `|v2|).

  (** Two vectors are perpendicular. Note that zero vector is perp to any vectors *)
  Definition vperp {n} (v1 v2 : vec n) : Prop := v1 ⋅ v2 = 0.
  Infix "⟂" := vperp ( at level 50).
  
End vangle.


(** ** Operations on vectors of 3-dimensional *)
Section v3.

  (** 空间直角坐标系的三个轴所在的单位向量 *)
  Definition v3i : vec 3 := mk_vec3 1 0 0.
  Definition v3j : vec 3 := mk_vec3 0 1 0.
  Definition v3k : vec 3 := mk_vec3 0 0 1.

  (** *** Dot product of two 3-dim vectors *)
  Section v3dot.
    
    Definition v3dot (a b : vec 3) :=
      let '(a1,a2,a3) := v2t_3 a in 
      let '(b1,b2,b3) := v2t_3 b in
      (a1*b1 + a2*b2 + a3*b3)%R.

    Lemma vdot3_spec : forall v1 v2 : vec 3, v3dot v1 v2 = v1 ⋅ v2.
    Proof. intros. cbv. ring. Qed.

    (** 习题8.2第12题, page 23, 高等数学，第七版 *)
    (** 利用向量来证明不等式，并指出等号成立的条件 *)
    Theorem Rineq3 : forall a1 a2 a3 b1 b2 b3 : R,
        sqrt (a1² + a2² + a3²) * sqrt (b1² + b2² + b3²) >= Rabs (a1*b1 + a2*b2 + a3*b3).
    Proof.
      intros.
      pose (a := t2v_3 (a1,a2,a3)).
      pose (b := t2v_3 (b1,b2,b3)).
      pose (alen := vlen a).
      pose (blen := vlen b).
      replace (sqrt _) with alen; [| unfold alen; cbv; f_equal; ring].
      replace (sqrt _) with blen; [| unfold blen; cbv; f_equal; ring].
      replace (Rabs _) with (Rabs (a ⋅ b)); [| cbv; autorewrite with R; auto].
    Abort.

  End v3dot.


  (** *** Cross product (vector product) of two 3-dim vectors *)
  Section v3cross.

    Definition v3cross (v1 v2 : vec 3) : vec 3 :=
      let '(a0,a1,a2) := v2t_3 v1 in
      let '(b0,b1,b2) := v2t_3 v2 in
      t2v_3 (a1 * b2 - a2 * b1, a2 * b0 - a0 * b2, a0 * b1 - a1 * b0)%R.

    Infix "×" := v3cross : vec_scope.

    (** Example 4, page 19, 高等数学，第七版 *)
    Goal let a := t2v_3 (2,1,-1) in
         let b := t2v_3 (1,-1,2) in
         a × b == t2v_3 (1,-5,-3).
    Proof. lva. Qed.

    (** Example 5, page 19, 高等数学，第七版 *)
    (** 根据三点坐标求三角形面积 *)
    Definition v3_area_of_triangle (A B C : vec 3) :=
      let AB := B - A in
      let AC := C - A in
      ((1/2) * `|AB × AC|)%R.

    (** Example 6, page 20, 高等数学，第七版 *)
    (** 刚体绕轴以角速度 ω 旋转，某点M（OM为向量r⃗）处的线速度v⃗，三者之间的关系*)
    Definition v3_rotation_model (ω r v : vec 3) := v = ω × r.
    
    Lemma v3cross_same : forall v : vec 3, v × v == vec0.
    Proof. lva. Qed.

    Lemma v3cross_anticomm : forall v1 v2 : vec 3, v1 × v2 == -(v2 × v1).
    Proof. lva. Qed.

    Lemma v3cross_add_distr_l : forall v1 v2 v3 : vec 3,
        (v1 + v2) × v3 == (v1 × v3) + (v2 × v3).
    Proof. lva. Qed.
    
    Lemma v3cross_add_distr_r : forall v1 v2 v3 : vec 3,
        v1 × (v2 + v3) == (v1 × v2) + (v1 × v3).
    Proof. lva. Qed.

    Lemma v3cross_cmul_assoc_l : forall (a : R) (v1 v2 : vec 3),
        (a c* v1) × v2 == a c* (v1 × v2).
    Proof. lva. Qed.
    
    Lemma v3cross_cmul_assoc_r : forall (a : R) (v1 v2 : vec 3),
        v1 × (a c* v2) == a c* (v1 × v2).
    Proof. lva. Qed.

  End v3cross.
  Infix "×" := v3cross : vec_scope.

  (** *** skew symmetry matrix *)
  Section v3ssm.
    
    Definition v3_skew_sym_mat (v : vec 3) : smat 3 :=
      let '(x,y,z) := v2t_3 v in
      (mk_mat_3_3
         0    (-z)  y
         z     0    (-x)
         (-y)  x     0)%R.
    Notation "`| v |ₓ" := (v3_skew_sym_mat v).

    Lemma v3cross_eq_ssm : forall (v1 v2 : vec 3), v1 × v2 == `|v1|ₓ * v2.
    Proof. lva. Qed.
    
  End v3ssm.
  Notation "`| v |ₓ" := (v3_skew_sym_mat v).

  
  (** *** Two vectors are parallel (or called coliner) *)
  Section vparallel.
    
    (** Note that zero vector is perp to any vectors *)
    Definition vparallel (v1 v2 : vec 3) : Prop := vzero (v1 × v2).
    Infix "∥" := vparallel ( at level 50).

  End vparallel.
  Infix "∥" := vparallel ( at level 50).


  (** *** The triple scalar product (or called Mixed products of vectors) *)
  Section v3mixed.

    (** 几何意义：绝对值表示以向量a,b,c为棱的平行六面体的体积，另外若a,b,c组成右手系，
        则混合积的符号为正；若组成左手系，则符号为负。*)
    Definition v3mixed (a b c : vec 3) :=
      let m :=
        l2m 3 3 [[a$0; a$1; a$2]; [b$0; b$1; b$2]; [c$0; c$1; c$2]] in
      det3 m.

    (** A equivalent form *)
    Lemma v3mixed_eq : forall a b c : vec 3, v3mixed a b c = (a × b) ⋅ c.
    Proof. intros [a] [b] [c]. cbv. ring. Qed.
    

    (** 若混合积≠0，则三向量可构成平行六面体，即三向量不共面，反之也成立。
        所以有如下结论：三向量共面的充要条件是混合积为零。*)
    Definition v3coplanar (a b c : vec 3) := v3mixed a b c = 0.

    (** Example 7, page 22, 高等数学，第七版 *)
    (** 根据四顶点的坐标，求四面体的体积：四面体ABCD的体积等于AB,AC,AD为棱的平行六面体
        的体积的六分之一 *)
    Definition v3_volume_of_tetrahedron (A B C D : vec 3) :=
      let AB := B - A in
      let AC := C - A in
      let AD := D - A in
      ((1/6) * (v3mixed AB AC AD))%R.

  End v3mixed.


  (** *** SO(n): special orthogonal group *)
  Section SO3.

    (** If a matrix is SO3? *)
    Definition so3 (m : smat 3) : Prop := 
      let so3_mul_unit : Prop := m\T * m == mat1 in
      let so3_det : Prop := (det3 m) = 1 in
      so3_mul_unit /\ so3_det.

  End SO3.

?  


  (* 
  
  (** Angle between two vectors *)
  Definition vangle3 (v0 v1 : vec 3) : R := acos (m2t_1_1 (v0\T * v1)).

  (** The angle between (1,0,0) and (1,1,0) is 45 degree, i.e., π/4 *)
  Example vangle3_ex1 : vangle3 (l2v 3 [1;0;0]) (l2v _ [1;1;0]) = PI/4.
  Proof.
    compute.
    (*     Search acos. *)
  Abort. (* 暂不知哪里错了，要去查叉乘的意义 *)
  
  (** 根据两个向量来计算旋转轴 *)
  Definition rot_axis_by_twovec (v0 v1 : vec 3) : vec 3 :=
    let s : R := (vlen v0 * vlen v1)%R in
    s c* (vcross3 v0 v1).

  (* 谓词：两向量不共线（不平行的） *)
(* Definition v3_non_colinear (v0 v1 : V3) : Prop :=
    v0 <> v1 /\ v0 <> (-v1)%M.
 *)
  
End vec_3d.




  End v3cross3.


(** ** vector of any dimension *)
Section vec_any_dim.

  (* Definition 1: v1 is k times to v2，or v2 is k times to v1 *)
  Definition vparallel_ver1 {n} (v1 v2 : vec n) : Prop :=
    exists k, (v1 == k c* v2 \/ v2 == k c* v1).

  (* Definition 2: v1 is zero-vector, or v2 is zero-vector, or v1 is k times to v2 *)
  Definition vparallel_ver2 {n} (v1 v2 : vec n) : Prop :=
    (vzero v1) \/ (vzero v2) \/ (exists k, v1 == k c* v2).

  (* These two definitions are same *)
  Lemma vparallel_ver1_eq_ver2 : forall {n} (v1 v2 : vec n),
      vparallel_ver1 v1 v2 <-> vparallel_ver2 v1 v2.
  Proof.
    intros. unfold vparallel_ver1, vparallel_ver2.
    unfold vzero, vnonzero, Vector.vzero. split; intros.
    - destruct H. destruct H.
      + right. right. exists x. auto.
      + destruct (v1 ==? vec0); auto.
        destruct (v2 ==? vec0); auto.
        right. right. exists (1/x). rewrite H.
        lma. apply vec_eq_vcmul_imply_coef_neq0 in H; auto.
    - destruct H as [H1 | [H2 | H3]].
      + exists 0. left. rewrite H1. rewrite vcmul_0_l. easy.
      + exists 0. right. rewrite H2. rewrite vcmul_0_l. easy.
      + destruct H3. exists x. left; auto.
  Qed.

  (** Vector parallel relation. Here, we use definition 2 *)
  Definition vparallel {n} (v0 v1 : vec n) : Prop :=
    vparallel_ver2 v0 v1.

  Notation "v0 // v1" := (vparallel (v0) (v1)) (at level 70) : vec_scope.

  (** vparallel is an equivalence relation *)

  Lemma vparallel_refl : forall {n} (v : vec n), v // v.
  Proof.
    intros. unfold vparallel,vparallel_ver2. right. right. exists 1.
    rewrite vcmul_1_l. easy.
  Qed.

  Lemma vparallel_sym : forall {n} (v0 v1 : vec n), v0 // v1 -> v1 // v0.
  Proof.
    intros. unfold vparallel,vparallel_ver2 in *.
    destruct (v0 ==? vec0); auto.
    destruct (v1 ==? vec0); auto.
    destruct H; auto. destruct H; auto. destruct H.
    right. right. exists (1/x). rewrite H.
    lma. apply vec_eq_vcmul_imply_coef_neq0 in H; auto.
  Qed.

  (* Additionally, v1 need to be a non-zero vector. Because if v1 is zero vector, 
     then v0//v1, v1//v2, but v0 and v2 needn't to be parallel. *)
  Lemma vparallel_trans : forall {n} (v0 v1 v2 : vec n), 
      vnonzero v1 -> v0 // v1 -> v1 // v2 -> v0 // v2.
  Proof.
    intros. unfold vparallel, vparallel_ver2 in *.
    destruct (v0 ==? vec0), (v1 ==? vec0), (v2 ==? vec0);
      auto; try easy.
    destruct H0,H1; auto; try easy.
    destruct H0,H1; auto; try easy.
    destruct H0,H1. right. right.
    exists (x*x0)%R. rewrite H0,H1. apply mcmul_assoc.
  Qed.

  (** If two non-zero vectors are parallel, then there is a unique k such that
      they are k times relation *)
  Lemma vparallel_vnonezero_imply_unique_k : forall {n} (v1 v2 : vec n),
      vnonzero v1 -> vnonzero v2 -> v1 // v2 -> (exists ! k, v1 == k c* v2).
  Proof.
    intros.
    destruct H1; try easy. destruct H1; try easy. destruct H1.
    exists x. split; auto.
    intros. apply vcmul_vnonzero_eq_iff_unique_k with (v:=v2); auto.
    rewrite <- H1,H2. easy.
  Qed.

  (** Given a non-zero vector v1 and another vector v2,
      v1 is parallel to v2, iff, there is a unique k such that v2 is k times v1. *)
  Lemma vparallel_iff1 : forall {n} (v1 v2 : vec n) (H : vnonzero v1),
      (v1 // v2) <-> (exists ! k, v2 == k c* v1).
  Proof.
    intros. split; intros.
    - destruct (v2 ==? vec0).
      + exists 0. split.
        * rewrite vcmul_0_l. auto.
        * intros. rewrite m in H1.
          apply symmetry in H1. apply vcmul_nonzero_eq_zero_imply_k0 in H1; auto.
      + apply vparallel_vnonezero_imply_unique_k; auto. apply vparallel_sym; auto.
    - destruct H0. destruct H0. apply vparallel_sym. right. right. exists x. auto.
  Qed.
  
End vec_any_dim.


(* ======================================================================= *)
(** ** Usage demo *)
Section test.

  Let l1 := [1;2;3].
  Let v1 := l2v 2 l1.
  (* Compute v2l v1. *)
  (* Compute v2l (@l2v 3 l1). *)

  Variable a1 a2 a3 : R.
  Let v2 := t2v_3 (a1,a2,a3).
  (* Compute v2l v2. *)
  (* Compute v2l (vmap Ropp v2). *)

  Let v3 := @l2v 3 (map nat2R (seq 0 5)).
  (* Compute v2l v3. *)
  (* Compute vdot v1 v1. *)

End test.
