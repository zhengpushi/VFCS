(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Convert between {euler angle, matrix, quaternion}
  author    : ZhengPu Shi
  date      : 2022.06

  remark    :

  reference :
  1. (QQ) Introduction to Multicopter Design and Control, Springer, Quan Quan, page 96
  2. (Dunn) 3D Math Primer for Graphics and Game Development, Second Edition
     Fletcher Dunn, Ian Parberry.
  3. (Krasjet) Quaternion and 3D rotation（四元数与三维旋转）
 *)

Require Export VectorR Quaternion.

Open Scope R.
Open Scope quat_scope.
Open Scope mat_scope.
Open Scope cvec_scope.

(** * Euler Angle -> Matrix *)
Section euler2mat.

  (* 需要考虑的因素有：
     1. 旋转过程是从对象空间到直立空间，还是直立空间到对象空间？有两个互为转置的旋转矩阵
     2. 是主动变换还是被动变换？主动是坐标系不动，物体栋；被动是相反的。
     3. *)

End euler2mat.
