(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : 2D中的位姿
  author    : ZhengPu Shi
  date      : Nov, 2023
  
  reference :
  1. Peter Corke, Robotics Vision and Control
     Ch2 Representing Position and Orientation 位置和朝向表示
 *)

Require Import PoseInterface.

Require Import Lra.
Require Import VectorR3.

Module Orientation2D : PoseInterface.

  Definition frame := nat.
  (* 位姿与坐标系有关。另外，需要限制在 SE(2)内，这里未处理 *)
  Definition pose := fun A B : frame => mat 3 3.
  Definition point := fun A : frame => cvec 3.

  Definition pointTrans {A B : frame} (T : pose A B) (p : point A) : point B :=
    T * p.

  Definition poseOp {A B C : frame} (T1 : pose A B) (T2 : pose B C) : pose A C :=
    let R1 : mat 2 2 := l2m [[T1.11;T1.12];[T1.21;T1.22]] in
    let R2 : mat 2 2 := l2m [[T2.11;T2.12];[T2.21;T2.22]] in
    let t1 : cvec 2 := l2cv [T1.13; T1.23] in
    let t2 : cvec 2 := l2cv [T2.13; T2.23] in
    let R1R2 := R1 * R2 in
    let t1R1t2 := t1 + R1 * t2 in
    mappr (mappc R1R2 t1R1t2) (l2rv [0;0;1]).
  
  Definition pose0 {A B : frame} : pose A B := mat1.

  Definition poseN {A B : frame} (T : pose A B) : pose B A :=
    let R : mat 2 2 := l2m [[T.11;T.12];[T.21;T.22]] in
    let t : cvec 2 := l2cv [T.13; T.23] in
    let RT := R\T in
    let nRTt := - (R\T * t) in
    mappr (mappc RT nRTt) (l2rv [0;0;1]).

  Infix "⊕" := poseOp (at level 50).
  Notation "⊖ p" := (poseN p) (at level 40).
  Notation "0" := pose0.
  Infix "⊖" := (fun p q => p ⊕ (⊖ q)) (at level 50).


  (* pose是唯一的，暂时难以说明 *)
  Axiom poseUniq : forall (A B:frame) (p1 p2:pose A B), p1 = p2.
  
  (* 逆元等于交换上下标 *)
  Lemma poseN_eq : forall (A B:frame) (T1:pose A B) (T2:pose B A), ⊖ T1 = T2.
  Proof.
    intros.
    (* unfold poseN. *)
    apply poseUniq.
  Admitted.

  (* 左单位元 *)
  Lemma pose0l : forall (A B:frame) (p:pose A B), p ⊕ 0 = p.
  Proof.
    
    intros. unfold poseOp, pose0. simpl. unfold pose in p. cbv.

  (* 右单位元 *)
  Axiom pose0r : forall (A B:frame) (p:pose A B), 0 ⊕ p = p.

  (* 左逆元 *)
  Axiom poseNl : forall (A B:frame) (p:pose A B), (⊖ p) ⊕ p = 0.

  (* 右逆元 *)
  Axiom poseNr : forall (A B:frame) (p:pose A B), p ⊕ (⊖ p) = 0.
  
End Orientation2D.

(* Require Import Quaternion. *)
Require Import VectorC.
Require Import VectorR.

(* short name for matrix/vector theory on C *)
Module C.
  Include MatrixTheoryC.
  Include VectorTheoryC.
End C.



Module Type AbstractPose.
(* 坐标系，编号用于区分不同的坐标系 *)
Parameter frame : nat -> Type.
(* 相对位姿 ${}^A\xi_B$ 表示 B 相对于 A 的位姿 *)
Parameter pose : forall {n1 n2}, frame n1 -> frame n2 -> Type.
(* 点（在某个坐标系下给出坐标向量） *)
Parameter point : forall {n}, frame n -> Type.

(* 位姿对点的坐标做转换 *)
Parameter pose4point : forall {na nb} (A:frame na) (B:frame nb) (pt:point A), point B.

(* 位姿的复合 *)
Parameter poseOp : forall {na nb nc} {A:frame na} {B:frame nb} {C:frame nc}
                     (pAB:pose A B) (pBC:pose B C), pose A C.

(* 位姿的零元 *)
Parameter pose0 : forall {na nb} {A:frame na} {B:frame nb}, pose A B.

(* 位姿的逆元 *)
Parameter poseN : forall {na nb} {A:frame na} {B:frame nb}, pose A B -> pose B A.

Infix "⊕" := poseOp (at level 50).
Notation "⊖ p" := (poseN p) (at level 40).
Notation "0" := pose0.
Infix "⊖" := (fun p q => p ⊕ (⊖ q)) (at level 50).

(* 一些规则 *)
Section rules.
  (* pose是唯一的 *)
  Axiom poseUniq : forall {na nb} (A:frame na) (B:frame nb) (p1 p2:pose A B), p1 = p2.
  
  (* 逆元等于交换上下标 *)
  Axiom poseN_eq : forall {na nb} (A:frame na) (B:frame nb) (p:pose A B) (q:pose B A),
      ⊖ p = q.

  (* 左单位元 *)
  Axiom pose0l : forall {na nb} (A:frame na) (B:frame nb) (p:pose A B), p ⊕ 0 = p.

  (* 右单位元 *)
  Axiom pose0r : forall {na nb} (A:frame na) (B:frame nb) (p:pose A B), 0 ⊕ p = p.

  (* 左逆元 *)
  Axiom poseNl : forall {na nb} (A:frame na) (B:frame nb) (p:pose A B), (⊖ p) ⊕ p = 0.

  (* 右逆元 *)
  Axiom poseNr : forall {na nb} (A:frame na) (B:frame nb) (p:pose A B), p ⊕ (⊖ p) = 0.

End rules.

End AbstractPose.

(* Example *)
Declare Module AP : AbstractPose.

(* O,F,B,C,R 的例子 *)
Section example.
  Import AP.

  (* 给定一些坐标系 *)
  Variable O : frame 0.         (* 世界坐标系 *)
  Variable F : frame 1.         (* fixed camera *)
  Variable B : frame 2.         (* object *)
  Variable C : frame 3.         (* camera on robot *)
  Variable R : frame 4.         (* robot *)
  
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
