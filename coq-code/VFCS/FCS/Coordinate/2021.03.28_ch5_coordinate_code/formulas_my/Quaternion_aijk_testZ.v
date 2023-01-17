(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  file:       Quaternion_aijk_testZ.v
  by:         ZhengPu Shi
  date:       2021.01.05
  
  purpose:
  1. Test code for Quaternion_ajik_Z
  
*)


From FlyCtrl Require Import Quaternion_aijk.


(* --------------------------------------------------------------- *)
(* Example code, Quaternion based on Integer *)

Import Module_Quaternion_aijk_Z.

(* 
  1. same notations for different types has different priority.
  2. last opened scope will be prior than first opened scope.
  3. Although same expression may belong to multi different types, but a 
     conversion from lower-type to higher-type need a explicit temporary 
     interpretation scope.
  4. By the way, Coq has ability to choose suitable type, by type inference.
*)
Check 3 : Z.
Check 3 : realpart.
Check 3 : qexp.

Check (3 + 2).
Check (3 + 2)%Z : Z.
Check (3 + 2)%rptype : realpart.
Check (3 + 2)%qtype : qexp.

Fail Check (3 + 2): realpart.

Compute rpeval (3).
Compute rpeval (3 + 2).
Compute rpeval (3 + 2).

(* We can use eval function to simplify any realpart expression at once. *)
Compute rpeval ((2 + 4) * (2 + 3)).
Compute rpeval ((2 + 4) * (2 + 3 * (1 + 2))).

(* Handle negation *)
Compute rpeval (- 1).
Compute rpeval (- (1 - 3)).

(* Construct quaternion expressions *)
Check 2 : qexp.
Check i.
Check 2 + i.
Check i * 3.
Check 1 + 2 * i.
Check 1 + (2 * i).
Check (1 + 2) * i.
Check 1 + 2 * i + 3 * j + 4 * k * k.



(* one of our goals is to simplify this formula *)
Example qexp_ex_10 : qexp := 
  (1 + 2 * i - 3 * j - 4 * k) * (5 - 6 * i + 7 * j + 8 * k).

(*
Compute qexp_opt_realpart ((1 + 2)%rptype * i).
Compute qexp_opt_realpart (i * (1 * 2)%rptype).
Compute qexp_opt_realpart ((1 + 2)%rptype * i + i * (3 * 4)%rptype).
Compute qexp_opt_realpart ((3 + 4 * (1 + 2 * (1 + 2)))%rptype * k).
Compute qexp_opt_realpart (1 + 2).
*)

Compute qexp_depth (i).
Compute qexp_depth (i + j).
Compute qexp_depth ((i + j) * (i + j)).

Compute qexp_opt_bracket1 ((1 + 2) * (3 + 4)).
Compute qexp_opt_bracket1 ((1 + 2 + 3) * (4 + 5 + 6)).
Compute qexp_opt_bracket1 ((1 + 2 + 3 + 4) * (4 + 5 + 6 + 7)).
Compute qexp_opt_bracket1 ((1 + (2 + 3)) * (11 + (12 + 13))).
Compute qexp_opt_bracket1 ((1 + 2 * (3 + 4)) * 11).
Compute qexp_opt_bracket1 ((1 + 2 * (3 + 4)) * (11 + 12 * (13 + 14))).
Compute qexp_opt_bracket1 (1 + (2 * (3 * (1 + (2 + 4))) + 4)).
Compute qexp_opt_bracket2 (1 + (2 * (1 + (2 + 3)) + 4)).
Compute qexp_opt_bracket2 ((1 + (2 + 3)) + (3 * (4* 5 ))).

Compute qexp_opt_bracket ((1 + 2) * (3 + 4)).
Compute qexp_opt_bracket ((1 + 2 + 3) * (4 + 5 + 6)).
Compute qexp_opt_bracket ((1 + 2 + 3 + 4) * (4 + 5 + 6 + 7)).
Compute qexp_opt_bracket ((1 + (2 + 3)) * (11 + (12 + 13))).
Compute qexp_opt_bracket ((1 + 2 * (3 + 4)) * 11).
Compute qexp_opt_bracket ((1 + 2 * (3 + 4)) * (11 + 12 * (13 + 14))).
Compute qexp_opt_bracket (1 + (2 * (3 * (1 + (2 + 4))) + 4)).
Compute qexp_opt_bracket (1 + (2 * (1 + (2 + 3)) + 4)).
Compute qexp_opt_bracket ((1 + (2 + 3)) + (3 * (4 * 5 ))).
Compute qexp_opt_bracket qexp_ex_10.


Compute qexp_elim_negi (i - j - 2 - k).
Compute qexp_elim_negr (i - j - 2 - k).
Compute qexp_elim_negi (qexp_elim_negr (i - j - 2 - k)).
Compute qexp_elim_negr (qexp_elim_negi (i - j - 2 - k)).
Compute qexp_elim_negr (qexp_elim_negi (qexp_opt_bracket qexp_ex_10)).


Compute qexp_split_ri_mul (2 * i).
Compute qexp_split_ri_mul (i * 2).
Compute qexp_split_ri_mul (2 * i * j).
Compute qexp_split_ri_mul (1 * i * 2).
Compute qexp_split_ri_mul (1 * i * 2 * j).
Compute qexp_split_ri_mul (1 * i * 2 * j * 3).
Compute qexp_split_ri_mul (qexp_elim_negr (qexp_elim_negi (qexp_opt_bracket 
  qexp_ex_10))).


Compute qexp_simp_mul (2 * 3 * i * j * k).
Compute qexp_simp_mul (qexp_split_ri_mul (qexp_elim_negr (qexp_elim_negi 
 (qexp_opt_bracket qexp_ex_10)))).


(* This is a more better result *)
Example qexp_ex_12 : qexp :=
5 + 6 * i + 10 * i + -12 + 7 * j +
       14 * k + 15 * j + -18 * k + -21 + 
       8 * k + -16 * j + 24 * i + 
       20 * k + 24 * j + -28 * i + -32.

(* This is a more better result, but this is a wrong formula *)
Example qexp_ex_13 := 46 * j + -60 + 24 * k + -4 * i.


Compute qexp_wf_to_tuple4 (5 + 2 * i + 3 * k + 4 * j).
Compute qexp_wf_to_tuple4 (5).
Compute qexp_wf_to_tuple4 (3 * j).
Compute qexp_wf_to_tuple4 (2 * i + 5).
Compute qexp_wf_to_tuple4 (2 * i + 5 + -3 * k).

Compute qexp_wf_to_tuple4 (5 + i + k + j).
Compute qexp_wf_to_tuple4 (5).
Compute qexp_wf_to_tuple4 (j).
Compute qexp_wf_to_tuple4 (i + 5).
Compute qexp_wf_to_tuple4 (i + 5 + k).


Compute qexp_from_tuple4 (1,2,3,4).


Compute qexp_rearrange (2 * i + 5 + 3 * k + 4 * j).


Compute qexp_AxB_to_tuple4 (i * j + (i * k)) (3 - 2 * i).

(* Final result *)
Example qexp_ex_21 := 1 + 2 * i + 3 * j + 4 * k.
Example qexp_ex_22 := 5 + 6 * i + 7 * j + 8 * k.
Example qexp_ex_23 := 9 + 10 * i + 11 * j + 12 * k.
Compute qexp_AxB_to_tuple4 qexp_ex_21 qexp_ex_22.


(* --------------------------------------------------------------- *)
(* Some proof of QuaternionZ *)

(* Formula of Quaternion Multiplication
p * q = (
  Re p * Re q - Im1 p * Im1 q - Im2 p * Im2 q - Im3 p * Im3 q,
  Re p * Im1 q + Im1 p * Re q + Im2 p * Im3 q - Im3 p * Im2 q,
  Re p * Im2 q - Im1 p * Im3 q + Im2 p * Re q + Im3 p * Im1 q,
  Re p * Im3 q + Im1 p * Im2 q - Im2 p * Im1 q + Im3 p * Re q)

or:
http://www.euclideanspace.com/maths/algebra/realNormedAlgebra/quaternions/arithmetic/other.htm
  (a + i b + j c + k d)*(e + i f + j g + k h) = 
     a*e - b*f - c*g - d*h
+ i (b*e + a*f + c*h - d*g)
+ j (a*g - b*h + c*e + d*f)
+ k (a*h + b*g - c*f + d*e)

*)
Lemma qexp_AxB_formula1_Z(a0 a1 a2 a3 b0 b1 b2 b3 : Z) :
  qexp_AxB_to_tuple4 
    (a0 + a1 * i + a2 * j + a3 * k) 
    (b0 + b1 * i + b2 * j + b3 * k) 
  = (
    (a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3),
    (a0 * b1 + a1 * b0 + a2 * b3 - a3 * b2),
    (a0 * b2 - a1 * b3 + a2 * b0 + a3 * b1),
    (a0 * b3 + a1 * b2 - a2 * b1 + a3 * b0))%element.
Proof.
  (*
  simpl_qexp_AxB; simpl_equal_of_tuples; ring.
  *)
  apply qexp_AxB_formula1.
  
Qed.
