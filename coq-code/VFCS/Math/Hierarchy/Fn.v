(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : vector space
  author    : ZhengPu Shi
  date      : 2024.01

  remark    :
  1. 向量空间是线性空间的具体情形。其元素形如 @vec A c。
  (1) 若A为实数，称为 real vector space
  (2) 若A为复数，称为 complex vector space
 *)


Require Export VectorSpace.

Set Implicit Arguments.
Unset Strict Implicit.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv Ale Alt Altb Aleb a2r.

Open Scope A_scope.
Open Scope vec_scope.
Open Scope VectorSpace_scope.


(* ===================================================================== *)
(** ** Vector Space *)

(** Vector forms a linear space (called `Vector Space`) *)
Section vectorSpace.
  Context `{HField : Field A Aadd Azero Aopp Amul Aone Ainv}.
  
  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vcmul := (@vcmul _ Amul).
  
  #[export] Instance vectorSpace {n : nat} :
    VectorSpace (V:=vec n) vadd vzero vopp vcmul.
  Proof.
    constructor; try apply vadd_AGroup; intros.
    apply vcmul_1_l. rewrite vcmul_assoc; auto.
    apply vcmul_add. apply vcmul_vadd.
  Qed.

End vectorSpace.
Arguments vectorSpace {A Aadd Azero Aopp Amul Aone Ainv} HField {n}.

Section props.
  Context `{HField : Field A Aadd Azero Aopp Amul Aone Ainv}.
  Notation vectorSpace := (vectorSpace HField).

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vsub := (@vsub _ Aadd Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Notation vsum := (@vsum _ Aadd Azero).
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.
  Notation lcomb := (@lcomb _ _ vadd vzero vcmul).
  Notation lrepr := (@lrepr _ _ vadd vzero vcmul).
  Notation ldep := (@ldep _ Azero _ vadd vzero vcmul).
  Notation lindep := (@lindep _ Azero _ vadd vzero vcmul).

  (** (lcomb cs vs).i = ∑(vmap2 Amul cs (vcol vs i)) *)
  Lemma vnth_lcomb : forall {n r} (cs : @vec A r) (vs : @vec (@vec A n) r) (i : fin n),
      (lcomb cs vs) $ i = vsum (vmap2 Amul cs (vcol vs i)).
  Proof. intros. unfold lcomb. rewrite vnth_vsum. auto. Qed.

  (** lcomb over vectors from `vmap2 vapp us vs` *)
  Lemma lcomb_vec_vmap2_vapp :
    forall (m n r : nat) (cs : @vec A r)
      (us : @vec (@vec A m) r) (vs : @vec (@vec A n) r) (i : fin (m + n)),
      lcomb cs (vmap2 vapp us vs) i = vapp (lcomb cs us) (lcomb cs vs) i.
  Proof.
    intros. rewrite vnth_lcomb. destruct (fin2nat i ??< m).
    - rewrite vnth_vapp_L with (H:=l). unfold lcomb.
      rewrite vnth_vsum. apply vsum_eq; intros j.
      rewrite !vnth_vmap2. rewrite !vnth_vcmul. f_equal. rewrite !vnth_vcol.
      rewrite vnth_vmap2. rewrite vnth_vapp_L with (H:=l); auto.
    - assert (m <= fin2nat i). lia. rewrite vnth_vapp_R with (H:=H). unfold lcomb.
      rewrite vnth_vsum. apply vsum_eq; intros j.
      rewrite !vnth_vmap2. rewrite !vnth_vcmul. f_equal. rewrite !vnth_vcol.
      rewrite vnth_vmap2. rewrite vnth_vapp_R with (H:=H). auto.
  Qed.

  (** F^n的下述子集U是一个子空间 U = {(a1,...,ak,0,...,0) | ai ∈ F, 1 <= k < n } *)
  Section topKWithZero_SubSpace.
    Context {n k : nat}.
    Context {Hk : 1 <= k < n}.

    Instance topKWithZero_SubSpaceStruct
      : SubSpaceStruct
          (fun v => forall (i:fin n),
               if (fin2nat i ??> k)%nat then v$i = Azero else True).
    Proof.
      constructor; intros.
      - destruct (_??<_); auto.
      - destruct (_??<_); auto. rewrite vnth_vadd.
        pose proof (u.prf). pose proof (v.prf). simpl in *.
        specialize (H i). specialize (H0 i).
        destruct (_??<_) in H,H0; try lia. rewrite H,H0. monoid.
      - destruct (_??<_); auto. rewrite vnth_vcmul.
        pose proof (v.prf). simpl in *. specialize (H i).
        destruct (_??<_) in H; try lia. rewrite H. apply ring_mul_0_r.
    Qed.

    #[export] Instance topKWithZero_SubSpace : VectorSpace Hadd Hzero Hopp Hcmul :=
      makeSubSpace topKWithZero_SubSpaceStruct.
  End topKWithZero_SubSpace.

  (** F^n的下述子集U是一个子空间 U = {(a1,0,a3,0,...0,an) | ai ∈ F, i=1,3,...,n} *)
  Section oddWithZero_SubSpace.
    Context {n : nat}.
    
    Instance oddWithZero_SubSpaceStruct
      : SubSpaceStruct
          (fun v => forall (i : fin n),
               if ((fin2nat i mod 2) ??= 0)%nat then v$i = Azero else True).
    Proof.
      constructor; intros.
      - destruct (_??=_)%nat; auto.
      - destruct (_??=_)%nat; auto. rewrite vnth_vadd.
        pose proof (u.prf). pose proof (v.prf). hnf in H,H0.
        specialize (H i). specialize (H0 i).
        destruct (_??=_)%nat in H,H0; try lia. rewrite H,H0. monoid.
      - destruct (_??=_)%nat; auto. rewrite vnth_vcmul.
        pose proof (v.prf). hnf in H. specialize (H i).
        destruct (_??=_)%nat in H; try lia. rewrite H. apply ring_mul_0_r.
    Qed.

    #[export] Instance oddWithZero_SubSpace : VectorSpace Hadd Hzero Hopp Hcmul :=
      makeSubSpace oddWithZero_SubSpaceStruct.
  End oddWithZero_SubSpace.

  (** 添加或去掉向量的一些分量构成的延伸组与缩短组的一对性质：
      1. 如果向量组线性无关，那么把每个向量在相同位置添上m个分量得到的延伸组也线性无关
      2. 如果向量组线性相关，那么把每个向量在相同位置去掉m个分量得到的缩短组也线性相关 

      如何表示“延伸组和缩短组”？
      1. 如何表示“延伸的向量”，“缩短的向量”？
      (1) 在头部加入/去掉数个元素，在尾部加入/去掉数个元素，在任意位置加入/去掉数个元素
      (2) 在任意位置的操作包含了头部或尾部。
      3. 如何表示“延伸组”，“缩短组”？
      (1) 关键是要对向量组在相同的位置进行操作。
      (2) 还可以换一种思路，不进行具体的操作，但是可以判断两个向量是否具有“延伸组”或
      “缩短组”的关系？

      给定v1,...,vs，记其延伸组为 v1',...,vs'，
      则从 k1v1'+...ksvs'=0 可得到 k1v1+...+ksvs=0。
      若v1,...,vs线性无关，则可知k1=...=ks=0，从而v1',...,vs'也线性无关。
   *)

  (** 若向量组线性无关，每个向量的相同位置添上m个分量后的延伸组线性无关。*)
  Section lindep_extend.
    
    (** 在每个向量头部都加入数个元素后保持线性无关 *)
    Lemma lindep_extend_head :
      forall {m n r} (us : @vec (@vec A m) r) (vs : @vec (@vec A n) r),
        lindep vs -> lindep (vmap2 vapp us vs).
    Proof.
      intros. unfold lindep, ldep in *. intro. destruct H.
      destruct H0 as [cs [H H0]]. exists cs. split; auto.
      rewrite veq_iff_vnth. rewrite veq_iff_vnth in H0. intros.
      specialize (H0 (fin2AddRangeAddL i)).
      rewrite vnth_vzero in *. rewrite <- H0 at 2.
      rewrite lcomb_vec_vmap2_vapp. erewrite vnth_vapp_R.
      rewrite fin2AddRangeAddL'_fin2AddRangeAddL. auto.
      Unshelve. rewrite fin2nat_fin2AddRangeAddL. lia.
    Qed.

    (** 在每个向量尾部都加入数个元素后保持线性无关 *)
    Lemma lindep_extend_tail :
      forall {m n r} (us : @vec (@vec A m) r) (vs : @vec (@vec A n) r),
        lindep us -> lindep (vmap2 vapp us vs).
    Proof.
      intros. unfold lindep, ldep in *. intro. destruct H.
      destruct H0 as [cs [H H0]]. exists cs. split; auto.
      rewrite veq_iff_vnth. rewrite veq_iff_vnth in H0. intros.
      specialize (H0 (fin2AddRangeR i)).
      rewrite vnth_vzero in *. rewrite <- H0 at 2.
      rewrite lcomb_vec_vmap2_vapp. erewrite vnth_vapp_L.
      rewrite fin2AddRangeR'_fin2AddRangeR. auto.
      Unshelve. rewrite fin2nat_fin2AddRangeR. apply fin2nat_lt.
    Qed.

    (** 对每个向量都插入1个元素后保持线性无关 *)
    Lemma lindep_extend_insert :
      forall {n r} (vs : @vec (@vec A n) r) (i : fin (S n)) (a : A),
        lindep vs -> lindep (vmap (fun v => vinsert v i a) vs).
    Proof.
      intros. unfold lindep, ldep in *. intro. destruct H.
      destruct H0 as [cs [H H0]]. exists cs. split; intros; auto.
      rewrite veq_iff_vnth. intros j. rewrite veq_iff_vnth in H0.
      destruct (fin2nat j ??< fin2nat i).
      - specialize (H0 (fin2SuccRange j)).
        rewrite vnth_vzero in *. rewrite <- H0 at 2. rewrite !vnth_lcomb.
        apply vsum_eq; intros k. rewrite !vnth_vmap2. f_equal. unfold vcol.
        rewrite !vnth_vmap. rewrite (@vnth_vinsert_lt _ Azero) with (j:=j); auto.
      - specialize (H0 (fin2SuccRangeSucc j)).
        rewrite vnth_vzero in *. rewrite <- H0 at 2. rewrite !vnth_lcomb.
        apply vsum_eq; intros k. rewrite !vnth_vmap2. f_equal. unfold vcol.
        rewrite !vnth_vmap. rewrite (@vnth_vinsert_gt _ Azero) with (j:=j); auto.
        lia. apply fin2nat_lt.
    Qed.

  End lindep_extend.

  (** 若向量组线性相关，每个向量的相同位置去掉m个分量后的延伸组线性相关。*)
  Section ldep_shorten.
    
    (** 在每个向量头部都去掉数个元素后保持线性相关 *)
    Lemma ldep_shorten_head : forall {m n r} (vs : @vec (@vec A (m + n)) r),
        ldep vs -> ldep (vmap vtailN vs).
    Proof.
      intros. unfold ldep in *. destruct H as [cs [H H0]]. exists cs. split; auto.
      rewrite veq_iff_vnth. rewrite veq_iff_vnth in H0. intros.
      specialize (H0 (fin2AddRangeAddL i)). rewrite vnth_vzero in *.
      rewrite <- H0 at 2. rewrite !vnth_lcomb. apply vsum_eq; intros j.
      rewrite !vnth_vmap2. f_equal.
    Qed.
    
    (** 在每个向量尾部都去掉数个元素后保持线性相关 *)
    Lemma ldep_shorten_tail : forall {m n r} (vs : @vec (@vec A (m + n)) r),
        ldep vs -> ldep (vmap vheadN vs).
    Proof.
      intros. unfold ldep in *. destruct H as [cs [H H0]]. exists cs. split; auto.
      rewrite veq_iff_vnth. rewrite veq_iff_vnth in H0. intros.
      specialize (H0 (fin2AddRangeR i)). rewrite vnth_vzero in *.
      rewrite <- H0 at 2. rewrite !vnth_lcomb. apply vsum_eq; intros j.
      rewrite !vnth_vmap2. f_equal.
    Qed.

    (** 对每个向量都删除1个元素后保持线性相关 *)
    Lemma ldep_shorten_delete :
      forall {n r} (vs : @vec (@vec A (S n)) r) (i : fin (S n)) (a : A),
        ldep vs -> ldep (vmap (fun v => vremove v i) vs).
    Proof.
      intros. unfold ldep in *. destruct H as [cs [H H0]]. exists cs. split; intros; auto.
      rewrite veq_iff_vnth. intros j. rewrite veq_iff_vnth in H0.
      destruct (fin2nat j ??< fin2nat i).
      - specialize (H0 (fin2SuccRange j)).
        rewrite vnth_vzero in *. rewrite <- H0 at 2. rewrite !vnth_lcomb.
        apply vsum_eq; intros k. f_equal. apply veq_iff_vnth; intros s.
        rewrite !vnth_vcol. rewrite !vnth_vmap.
        rewrite (@vnth_vremove_lt _ Azero); auto. erewrite nth_v2f. f_equal.
        apply fin2nat_imply_nat2fin. rewrite fin2nat_fin2SuccRange. auto.
      - specialize (H0 (fin2SuccRangeSucc j)).
        rewrite vnth_vzero in *. rewrite <- H0 at 2. rewrite !vnth_lcomb.
        apply vsum_eq; intros k. f_equal. apply veq_iff_vnth; intros s.
        rewrite !vnth_vcol. rewrite !vnth_vmap.
        rewrite (@vnth_vremove_ge _ Azero); auto; try lia.
        + erewrite nth_v2f. f_equal. apply fin2nat_imply_nat2fin.
          rewrite fin2nat_fin2SuccRangeSucc. auto.
        + apply fin2nat_lt.
          Unshelve. pose proof (fin2nat_lt j). lia.
          pose proof (fin2nat_lt j). lia.
    Qed.
    
  End ldep_shorten.

  
  (** F^n中的s个向量中的每一个都在这个向量组张成的线性空间中。
      即，vi ∈ <v1,v2,...,vs>, 1<=i<=s, vi∈F^n *)
  Lemma in_lspan : forall {n s} (vs : @vec (@vec A n) s) i,
      Hbelong (ss := lspan_Struct vs) (vs $ i).
  Proof. intros. hnf. apply lrepr_in. Qed.
  
  (** 在F^n中，任意向量都能由n个线性无关的向量来线性表示 *)
  Lemma lindep_imply_lrepr_any : forall {n} (vs : @vec (@vec A n) n) (u : @vec A n),
      lindep vs -> lrepr vs u.
  Proof.
    intros.
    pose proof (in_lspan vs). unfold Hbelong in H0.
    rewrite lindep_iff_coef0 in H.
    unfold lindep,ldep in H. unfold lrepr.
  Admitted.
  
  (** 在F^n中，任意n+1个向量都线性相关 *)
  Lemma ldep_Sn : forall {n} (vs : @vec (@vec A n) (S n)), ldep vs.
  Proof.
    (* 丘老师的证明：
       考虑齐次线性方程组 x1v1+x2v2+...+x(n-1)v(n-1)=0，
       它的方程个数n小于未知量个数n+1，因此它有非零解。所以vs线性相关。*)

    (* 我的证明（只有思路，尚未完成）：
       1. 前n个向量要么线性相关，要么线性无关。
       (1). 若线性相关，则这n+1个向量是线性相关的；
       (2). 若线性无关，则第n+1个向量可由前n个向量线性表示，于是这n+1个向量线性相关。*)
    intros.
    rewrite (vconsT_vremoveT_vtail vs (Azero:=vzero)).
    assert ({ldep (vremoveT vs)} + {~ (ldep (vremoveT vs))}).
    (* 此可判定性也许无法证明，因为涉及到存在量词 *) admit.
    destruct H.
    - apply ldep_imply_vconsT_ldep. auto.
    -
      Admitted.
    


  (* 几何空间：
     1. 几何空间可以看成是以原点O为起点的所有向量组成的集合V，它有加法和数量乘法两种运算。
     2. 几何空间V的一个非空子集U如果对于向量的加法和数乘都封闭，则称U是V的一个子空间。
     3. 一条直线l可看成是以O为起点，以l上的点为终点的所有向量组成的集合。
     4. 一个平面π可看成是以O为起点，以π上的点为终点的所有向量组成的集合。
   *)
  
  
  (* 自然基的性质 *)
  Section veyes.
    Context {n : nat}.
    Notation veyes := (veyes 0 1).

    (** 任意向量都能写成自然基的线性组合: v * eyes = v *)
    Lemma lcomb_veyes : forall v : vec n, lcomb v (veyes n) = v.
    Proof.
      intros. unfold lcomb. apply veq_iff_vnth. intros.
      (* (v1(1,0,0) + v2(0,1,0) + v3(0,0,1)).i = v.i *)
      rewrite vnth_vsum.
      (* v1(1,0,0).i + v2(0,1,0).i + v3(0,0,1).i = v.i *)
      apply vsum_unique with (i:=i).
      - rewrite vnth_vmap2. rewrite vnth_vcmul. rewrite vnth_veyes_eq. amonoid.
      - intros. rewrite vnth_vmap2. rewrite vnth_vcmul.
        rewrite vnth_veyes_neq; auto. apply ring_mul_0_r.
    Qed.
    
    (** 自然基是线性无关的 *)
    Lemma lindep_veyes : lindep (veyes n).
    Proof.
      intros. unfold lindep, ldep. intro. destruct H as [v [H H0]]. destruct H.
      rewrite lcomb_veyes in H0. auto.
    Qed.

    (** 任意向量 v 都可由自然基线性表示 *)
    Lemma lrepr_veyes : forall (v : vec n), lrepr (veyes n) v.
    Proof. intros. unfold lrepr. exists v. apply lcomb_veyes. Qed.

    (** 任意向量 v，用自然基线性表示的方式唯一 *)
    Lemma lrepr_veyes_unique : forall (v : vec n), exists! c, lcomb c (veyes n) = v.
    Proof.
      intros. exists v. split. apply lcomb_veyes. intros. rewrite lcomb_veyes in H. auto.
    Qed.
    
    (* Example ex1_vspan : vspan vecs. *)
    (* Proof. *)
    (*   unfold vspan. intros. exists (mkvec3 (u.1) (u.2) (u.3)). *)
    (*   apply v3eq_iff. cbv. lra. *)
    (* Qed. *)
    
    (* Example ex2_vbasis : vbasis vecs. *)
    (* Proof. *)
    (*   unfold vbasis. split. apply ex1_vlindep. apply ex1_vspan. *)
    (* Qed. *)

  End veyes.
End props.


(*
Section examples.
  Import VectorR.
  Notation vlcomb := (@vlcomb _ _ vadd vzero vcmul).
  Notation vldep := (@vldep _ Azero _ vadd vzero vcmul).
  Notation vlindep := (@vlindep _ Azero _ vadd vzero vcmul).
  Notation vspan := (@vspan _ _ vadd vzero vcmul).
  Notation vbasis := (@vbasis _ Azero _ vadd vzero vcmul).

  (* Example for "linearly dependent" *)
  Section ex1.
    (* The vectors (2, 2, 5), (3, 3, 12) and (5, 5, −1) are linearly dependent
       elements of the real vector space R3, since
       7(2, 2, 5) − 3(3, 3, 12) − (5, 5, −1) = (0, 0, 0).
       Thus if v1 = (2, 2, 5), v2 = (3, 3, 12) and v3 = (5, 5, −1), then the equation
       c1v1 + c2v2 + c3v3 = 0 is satisfied with c1 = 7, c2 = −3 and c3 = −1.) *)
    Let vecs := Vector.mkvec3 (Azero:=vzero)
                  (mkvec3 2 2 5)
                  (mkvec3 3 3 12)
                  (mkvec3 5 5 (-1)%R).
    Let coefs := mkvec3 7 (-3) (-1).
    
    Example ex1_eq1 : vlcomb coefs vecs = vzero.
    Proof. apply v3eq_iff. cbv. lra. Qed.

    Example ex1_ldep : vldep vecs.
    Proof.
      unfold vldep. exists coefs. split.
      - intro. apply v3eq_iff in H. cbv in H. ra.
      - apply ex1_eq1.
    Qed.
  End ex1.

End examples.
 *)

