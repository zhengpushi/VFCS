(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : atan2
  author    : ZhengPu Shi
  date      : 2021.05
  
  remark    :
  1. 背景：
  计算 θ 用 arctan(y/x)，但是有一些问题：
  (1). 如果 x = 0，除法是未定义的
  (2). arctan 的范围仅是 [-π/2, π/2]，原因是除法y/x丢失了一些有用信息。
  x和y都可以是正或负，从而有4种可能，对应于4个不同象限。但y/x得到了单个值。
  由于这些问题，使得我们需要一些“if”判断来处理每个象限。
  好消息是，有 atan2 函数，它可以正确计算所有 x 和 y 的角度，除了原点这种情况。
 *)


Require Import RExt RealFunction.

Open Scope R_scope.


(* ######################################################################### *)
(** * atan2 *)

(** atan2.
  Note that the parameters are y,x, not x,y. Because: tanθ=sinθ/cosθ=y/x

  atan2 y x =
    atan (y/x),       x > 0
    atan (y/x) + pi,  x < 0, y >= 0
    atan (y/x) - pi,  x < 0, y < 0
    +pi/2,            x = 0, y > 0
    -pi/2,            x = 0, y < 0
    undefined,        x = 0, y = 0
 *)
Definition atan2 (y x : R) : R :=
  if x >? 0
  then atan (y/x)               (* x > 0 *)
  else
    if x <? 0
    then
      if y >=? 0
      then atan (y/x) + PI      (* x < 0, y >= 0 *)
      else atan (y/x) - PI      (* x < 0, y < 0 *)
    else
      if y >? 0
      then PI / 2               (* x = 0, y > 0 *)
      else
        if y <? 0
        then - PI / 2           (* x = 0, y < 0 *)
        else 0                  (* x = 0, y = 0 *) (* mostly, it is undefined *)
.


(** Automaticaly destruct inequalities on R, such as Rlt_le_dec. *)
Ltac destruct_rineq :=
  repeat
    match goal with
    | |- context [Rlt_le_dec _ _] => destruct Rlt_le_dec
    | |- context [Rle_lt_dec _ _] => destruct Rle_lt_dec
    end; try lra.

Lemma atan2_spec1 : forall y x, x > 0 -> atan2 y x = atan (y/x).
Proof. intros. cbv. destruct_rineq. Qed.

Lemma atan2_spec2 : forall y x, x < 0 -> y < 0 -> atan2 y x = (atan (y/x) - PI)%R.
Proof. intros. cbv. destruct_rineq. Qed.

Lemma atan2_spec3 : forall y x, x < 0 -> y >= 0 -> atan2 y x = (atan (y/x) + PI)%R.
Proof. intros. cbv. destruct_rineq. Qed.

Lemma atan2_spec4 : forall y x, x = 0 -> y > 0 -> atan2 y x = PI/2.
Proof. intros. cbv. destruct_rineq. Qed.

Lemma atan2_spec5 : forall y x, x = 0 -> y < 0 -> atan2 y x = - PI/2.
Proof. intros. cbv. destruct_rineq. Qed.

Lemma atan2_spec6 : forall y x, x = 0 -> y = 0 -> atan2 y x = 0.
Proof. intros. cbv. destruct_rineq. Qed.

(** An equation about atan2 will be used in the later proof *)
Lemma atan2_sin_cos_eq1 : forall a k : R,
    - PI < a < PI -> k > 0 ->
    atan2 (sin a * k) (cos a * k) = a.
Proof.
  intros.
  apply Rsplit_neg_pi_to_pi in H.
  repeat match goal with | H: _ \/ _ |- _ => destruct H as [? | H] end; 
    subst; autorewrite with R.
  - rewrite atan2_spec5; ra.
  - rewrite atan2_spec1; ra.
    replace (0 / k) with 0; ra. apply atan_0.
  - rewrite atan2_spec4; ra.
  - assert (sin a < 0). { apply sin_lt_0_var; lra. }
    assert (cos a < 0).
    { rewrite <- RealFunction.cos_2PI_add. apply cos_lt_0; ra. }
    rewrite atan2_spec2; ra.
    rewrite atan_ak_bk; ra. cbv; rewrite Rtan_rw.
    rewrite <- Rtrigo_facts.tan_pi_plus; ra. rewrite atan_tan; ra.
  - assert (sin a < 0). { apply sin_lt_0_var; lra. }
    assert (0 < cos a). { apply cos_gt_0; ra. }
    rewrite atan2_spec1; ra.
    rewrite atan_ak_bk; ra. cbv; rewrite Rtan_rw. rewrite atan_tan; ra.
  - assert (0 < sin a). { apply sin_gt_0; lra. }
    assert (0 < cos a). { apply cos_gt_0; ra. }
    rewrite atan2_spec1; ra.
    rewrite atan_ak_bk; ra. cbv; rewrite Rtan_rw. rewrite atan_tan; ra.
  - assert (0 < sin a). { apply sin_gt_0; lra. }
    assert (cos a < 0). { apply cos_lt_0; ra. }
    rewrite atan2_spec3; ra.
    rewrite atan_ak_bk; ra. cbv; rewrite Rtan_rw.
    rewrite <- RealFunction.tan_sub_PI. rewrite atan_tan; ra.
Qed.

(** Don't unfold it, avoding too many details *)
Global Opaque atan2.
