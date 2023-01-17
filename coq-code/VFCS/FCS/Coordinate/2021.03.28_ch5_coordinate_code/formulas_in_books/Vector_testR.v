(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  file:       Vector_testR.v
  author:     ZhengPu Shi
  purpose:    Test code of vector and matrix

*)

From FlyCtrl Require Import Vector.
Import Module_VectorR.
Open Scope R.


Example v00 : vector 0 := tt.
Example v00' : vector 1 := [1].
Example v01 : vector 3 := [1,2,3].
Example v11 : vector 3 := [4,5,6].
Example v01' : vector 3 := (pair 1 (pair 2 (pair 3 tt))).
Example v01'' := [1,2,3].
Print v01.
Print v01'.
Print v01''.
(*
v01 = [1, 2, 3]
     : vector 3
v01' = [1, 2, 3]
     : vector 3
v01'' = [1, 2, 3]
     : nat * (nat * (nat * unit))
*)

Example m00 : matrix 0 2 := tt.
Example m00' : matrix 2 0 := [tt,tt].
Example m01 : matrix 1 3 := [[1,2,3]].
Example m02 : matrix 3 1 := [[1],[2],[3]].
Example m03 : matrix 2 3 := [[1,2,3],[4,5,6]].
Example m13 : matrix 2 3 := [[7,8,9],[10,11,12]].
Example m04 : matrix 3 2 := [[1,4],[2,5],[3,6]].
Example m05 : matrix 3 3 := [[1,2,3],[4,5,6],[7,8,9]].


Compute v_nth v01 0. (* = 1 : nat *)
Compute v_nth v01 4. (* = 99 : nat *)

Compute v_make 5 3.    (* = [3, 3, 3, 3, 3] : vector 5 *)

Compute v_make' 3 (fun i => (IZR (Z.of_nat i))).

Compute v_map1 v01 (fun x => x + 1).

Compute v_map2 v01 v01 (fun x y => x + y).

Compute v_fold_l v01 add 0.

Compute v_fold_r v01 add 0.

Compute v_dot v01 v01.

Compute v_app v01 v11.

Compute v_cmul 2 v01.


Compute m_nth m03 0 0.
Compute m_nth m03 1 2.

Compute m_make 0 0 9.   (* = tt : matrix 0 0 *)
Compute m_make 3 0 9.   (* = [tt, tt, tt] : matrix 3 0 *)
Compute m_make 3 2 9.   (* = [[99, 99], [99, 99], [99, 99]] : matrix 3 2 *)

(* Compute m_make' 3 2 (fun i j => (i,j)). *)
Compute m_make' 3 2 (fun i j => IZR (Z_of_nat i) + IZR (Z_of_nat j)).

Compute m_unary m03 (fun x => x + 1).

Compute m_binary m03 m03 (fun x y => x + y).

Compute m_get_row m03 0.
Compute m_get_row m03 2.

Compute m_get_col m03 0.
Compute m_get_col m03 1.
Compute m_get_col m03 3.

Compute m_trans m03.
Compute m_trans m04.
Compute m03 '.
Compute m03 ''.

Compute v_mul_m_aux v01 m03.

Compute m_mul_aux m04 m04.

Compute m_mul m03 m04.

Compute m_mul m04 m03.

Compute rv_to_m v01.
Compute cv_to_m v01.

Compute v_mul_m v01 m04.
Compute m_mul_v m03 v01.

Compute m_app_r m03 m13.

Compute m_app_c m03 m13.

Compute m_cmul 3 m03.

Compute m_3x3_to_tuples m05.

Compute m_3x3_det m05.
Compute m_3x3_det [[1,2,1],[2,1,1],[0,1,3]].

Example ex_ZM_01 : matrix 2 3 := [[3,1,2],[0,-1,4]].
Example ex_ZM_02 : matrix 3 1 := [[2],[-1],[4]].
Example ex_ZM_03 : matrix 2 1 := [[13],[17]].
Lemma ex_ZM_10 : m_mul ex_ZM_01 ex_ZM_02 = ex_ZM_03.
  unfold m_mul.
  unfold Vector.m_mul.
  unfold Vector.m_mul_aux.
  unfold Vector.v_mul_m_aux.
  unfold Vector.v_dot.
  simpl Vector.v_map2.
  simpl Vector.v_fold_l.
  unfold ex_ZM_03.
  simpl_equal_of_tuples;
  unfold add,mul,Zero,T; ring.
  Qed.






