(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  file:       Array_testR.v
  author:     ZhengPu Shi
  purpose:    Test code of array and matrix

*)

From FlyCtrl Require Import Array.
Import Module_ArrayR.
Open Scope R.

Example v00 : array 0 := tt.
Example v00' : array 1 := [1].
Example v01 : array 3 := [1,2,3].
Example v11 : array 3 := [4,5,6].
Example v01' : array 3 := (pair 1 (pair 2 (pair 3 tt))).
Example v01'' := [1,2,3].
Print v01.
Print v01'.
Print v01''.
(*
v01 = [1, 2, 3]
     : array 3
v01' = [1, 2, 3]
     : array 3
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


Compute a_nth v01 0. (* = 1 : nat *)
Compute a_nth v01 4. (* = 99 : nat *)

Compute a_make 5 3.    (* = [3, 3, 3, 3, 3] : array 5 *)

Compute a_make' 3 (fun i => (IZR (Z.of_nat i))).  (* = [1, 2, 3] : array 3 *)

Compute a_map1 v01 (fun x => x + 1).

Compute a_map2 v01 v01 (fun x y => x + y).

Compute a_fold_l v01 add 0.

Compute a_fold_r v01 add 0.

Compute a_dot v01 v01.

Compute a_app v01 v11.

Compute a_cmul 2 v01.


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

Compute cv_dotmul_m v01 m03.

Compute m_dotmul_m m04 m04.

Compute m_mul m03 m04.

Compute m_mul m04 m03.

Compute rv_to_m v01.
Compute cv_to_m v01.

Compute a_mul_m v01 m04.
Compute m_mul_a m03 v01.

Compute m_cons_byRow m03 m13.

Compute m_cons_byCol m03 m13.

Compute m_cmul 3 m03.

Compute m_3x3_to_tuples m05.

Compute m_3x3_det m05.
Compute m_3x3_det [[1,2,1],[2,1,1],[0,1,3]].

Example ex_ZM_01 : matrix 2 3 := [[3,1,2],[0,-1,4]].
Example ex_ZM_02 : matrix 3 1 := [[2],[-1],[4]].
Example ex_ZM_03 : matrix 2 1 := [[13],[17]].

Lemma ex_ZM_10 : m_mul ex_ZM_01 ex_ZM_02 = ex_ZM_03.
Proof. 
  compute. unfold T,Zero,add,mul in *. simpl_equal_of_tuples; ring. 
Qed.
