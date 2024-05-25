(*
  Copyright 2024 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : base for differential equation
  author    : ZhengPu Shi
  date      : 2024.05

  ref       :
  * Wang Yi Peng's work
  * https://en.wikipedia.org/wiki/Linear_differential_equation#Second-order_case
  * 高等数学学习手册，徐小湛
  * https://www.math.ncue.edu.tw/~kwlee/ODEBoyce/DEChapter3.pdf
 *)


From Coquelicot Require Export Rbar Continuity Derive RInt AutoDerive.

(* fix Bellet behavior, caused by Mathcomp.ssreflect.ssreflect.v *)
#[export] Set Bullet Behavior "Strict Subproofs".

From Coquelicot Require Export Hierarchy ElemFct.
From FinMatrix Require Export RFunExt Complex MyExtrOCamlR.

Open Scope Rfun_scope.
Open Scope C_scope.
Open Scope R_scope.


(** Noations *)

(* 1st-order derivative *)
Notation "f '" :=
  (Derive f) (at level 10, left associativity, format "f '") : Rfun_scope.

(* Now, 2nd-order or 3st-order derivative could be: f '', f ''' *)

(** Tactics *)

(** Convert function equality to value equality *)
Ltac feq :=
  let x := fresh "x" in
  extensionality x;
  rewrite ?faddR_ok;
  rewrite ?faddR_ok;
  rewrite ?fcmulR_ok;
  try unfold fzeroR;
  try unfold fcnstR.

