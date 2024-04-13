(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : 位姿的接口
  author    : ZhengPu Shi
  date      : Nov, 2023
  
  reference :
  1. Peter Corke, Robotics Vision and Control
     Ch2 Representing Position and Orientation 位置和朝向表示
 *)

Module Type PoseInterface.
(* 坐标系 *)
Parameter frame : Type.
(* 相对位姿 ${}^A\xi_B$ 表示 B 相对于 A 的位姿 *)
Parameter pose : frame -> frame -> Type.
(* 点（在某个坐标系下描述点） *)
Parameter point : frame -> Type.

(* 位姿对点的坐标做转换 *)
Parameter pointTrans : forall (A B:frame) (pt:point A), point B.

(* 位姿的复合 *)
Parameter poseOp : forall {A B C:frame} (pAB:pose A B) (pBC:pose B C), pose A C.

(* 位姿的零元 *)
Parameter pose0 : forall {A B:frame}, pose A B.

(* 位姿的逆元 *)
Parameter poseN : forall {A B:frame}, pose A B -> pose B A.

Infix "⊕" := poseOp (at level 50).
Notation "⊖ p" := (poseN p) (at level 40).
Notation "0" := pose0.
Infix "⊖" := (fun p q => p ⊕ (⊖ q)) (at level 50).

(* 一些规则 *)
Section rules.
  (* pose是唯一的 *)
  Axiom poseUniq : forall (A B:frame) (p1 p2:pose A B), p1 = p2.
  
  (* 逆元等于交换上下标 *)
  Axiom poseN_eq : forall (A B:frame) (p:pose A B) (q:pose B A), ⊖ p = q.

  (* 左单位元 *)
  Axiom pose0l : forall (A B:frame) (p:pose A B), p ⊕ 0 = p.

  (* 右单位元 *)
  Axiom pose0r : forall (A B:frame) (p:pose A B), 0 ⊕ p = p.

  (* 左逆元 *)
  Axiom poseNl : forall (A B:frame) (p:pose A B), (⊖ p) ⊕ p = 0.

  (* 右逆元 *)
  Axiom poseNr : forall (A B:frame) (p:pose A B), p ⊕ (⊖ p) = 0.

End rules.

End PoseInterface.

(* Example *)
Declare Module AP : PoseInterface.

(* O,F,B,C,R 的例子 *)
Section example.
  Import AP.

  (* 给定一些坐标系 *)
  Variable O : frame.         (* 世界坐标系 *)
  Variable F : frame.         (* fixed camera *)
  Variable B : frame.         (* object *)
  Variable C : frame.         (* camera on robot *)
  Variable R : frame.         (* robot *)
  
  (* 给定几个位姿 *)
  Variable pOF : pose O F.      (* 从 O 到 F 的位姿 *)
  Variable pOB : pose O B.
  Variable pOR : pose O R.
  Variable pFB : pose F B.
  Variable pCB : pose C B.
  Variable pRC : pose R C.

  (* 证明 pFB = pFOB *)
  Goal pFB = ⊖pOF ⊕ pOB.
  Proof. apply poseUniq. Qed.   (* pose 唯一性 *)
  
  (* 请以多种方式构造出 pFR *)
  Definition pFOR : pose F R := ⊖ pOF ⊕ pOR.
  Definition pFBCR : pose F R := pFB ⊖ pCB ⊖ pRC.

End example.
