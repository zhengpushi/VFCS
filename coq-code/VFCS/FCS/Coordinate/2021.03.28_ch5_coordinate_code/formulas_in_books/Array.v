(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  file:       Array.v
  author:     ZhengPu Shi
  date:       2021.01.01
  purpose:    
  1. a method for general array.
  2. a method for matrix by array of array.
  3. rv(row vector) and cv(column vector), we also use array to denote it.
     they are indeed same with general array, just treat them differently.
  4. Some common concrete concept, like 
    cv2 (2-dim column vector);
    cv3 (3-dim column vector);
    m_3x3 (3x3 matrix);

  reference:
  1. Coquelicot / Hierarchy / Matrices
  2. Prof. Chen 's coq script.
  
*)


(*
Require Import Nat.   (* Nat.eqb : nat -> nat -> bool *)
Require Import Bool.  (* Bool.eqb : bool -> bool -> bool *)
*)

From FlyCtrl Require Export Basic.

(* --------------------------------------------------------------- *)
(* Freedom definitions, i.e, without constrainted in a module *)


(* ======================================== *)
(* Definitions of array type and matrix type *)

(* notation of array with any length *)
Notation "[ x1 , .. , xn ]" := (pair x1 .. (pair xn tt) .. ).

(* definition of array *)
Fixpoint array {T : Set} (n : nat) : Set :=
  match n with
  | O => unit
  | S n => prod T (@array T n)
  end.

(* definition of matrix *)
Definition matrix {T : Set} (r c : nat) : Set := @array (@array T c) r.

Module TypeConversionExample.

  Section tp_trans.
    Variables n1 n2 n3 : nat.
    Definition tp1 := @array nat (n1 + 1).
    Definition tp2 := @array nat (S n1).

    Definition tp1_tran_tp2 : tp1 -> tp2.
    Proof.
      unfold tp1, tp2. destruct n1.
      - simpl. auto.
      - replace ((S n) + 1)%nat with (S (S n))%nat.
        auto. simpl. rewrite (Nat.add_1_r). auto.
      Qed.
  End tp_trans.

  Definition ttp1 (n : nat) : Type := nat -> tp1 n.
  Lemma arr1_eq_arr2 (n : nat) (arrT1 : tp1 n) (arrT2 : tp2 n) : 
    tp1_tran_tp2 n arrT1 = arrT2.
  Proof.
    Abort.

End TypeConversionExample.


(* ======================================== *)
(* Operations of arrays *)

(* get i-th element of a array *)
Fixpoint a_nth {T : Set} {n : nat} (err : T) : (array n) -> nat -> T 
  := match n with
  | O => fun (_ : array O) (_ : nat) => err
  | S n' => fun (arr : array (S n')) (i : nat) => match i with
     | O => (fst arr)
     | S i' => a_nth err (snd arr) i'
     end
  end.

(* get top n element of a array *)
Fixpoint a_topk {T : Set} {n : nat} (k : nat) (err : T) 
  : (@array T n) -> (@array T k) := 
  match n,k with
  | O, O => fun (arr : array O) => tt
  | O, S k' => fun (arr : array O) => (err, a_topk k' err arr)
  | S n', O => fun (arr : array (S n')) => tt
  | S n', S k' => fun (arr : array (S n')) => (fst arr, a_topk k' err (snd arr))
  end.
  
Fixpoint a_topk' {T : Set} {n : nat} (k : nat) (err : T) 
  : (@array T n) -> (@array T k) := 
  match n with
  | O => fun (arr : array O) => match k with
    | O => tt
    | S k' => (err, a_topk' k' err arr)
    end
  | S n' => fun (arr : array (S n')) => match k with
    | O => tt
    | S k' => (fst arr, a_topk' k' err (snd arr))
    end
  end.

(* construct a array with same element *)
Fixpoint a_make {T : Set} (n : nat) (x0 : T) : @array T n := match n with
  | O => tt
  | S n' => pair x0 (a_make n' x0)
  end.

(* construct a array in the form of : [u(0),u(1),...,u(n-1)] *)
Fixpoint a_make' {T : Set} (n : nat) (u : nat -> T) : array n := match n with
    | O => tt
    | S n => (u O, a_make' n (fun n => u (S n)))
  end.

(* mapping one array to another *)
Fixpoint a_map1 {T : Set} {n : nat} (f : T -> T) 
  : (@array T n) -> (@array T n) :=
  match n with
  | O => fun (arr : array 0) => arr (* 或者 tt 也可以 *)
  | S n' => fun (arr : array (S n')) => 
    pair (f (fst arr)) (a_map1 f (snd arr))
  end.

(* mapping two arrays to another array *)
Fixpoint a_map2 {T : Set} {n : nat} (f : T -> T -> T) 
  : (@array T n) -> (@array T n) -> (@array T n) :=
  match n with
  | O => fun (arr1 : array 0) (arr2 : array 0) => tt
  | S n' => fun (arr1 : array (S n')) (arr2 : array (S n')) => 
    pair (f (fst arr1) (fst arr2)) (a_map2 f (snd arr1) (snd arr2))
  end.

(* fold a array to an element from left to right *)
Fixpoint a_fold_l {T : Set} {n : nat} (f : T -> T -> T) (init_val:T)
  : (@array T n) -> T :=
  match n with
  | O => fun (arr : array 0) => init_val
  | S n' => fun (arr : array (S n')) => 
    f (fst arr) (a_fold_l f init_val (snd arr))
  end.

(* fold a array to en element from right to left *)
Fixpoint a_fold_r {T : Set} {n : nat} (f : T -> T -> T) (init_val:T)
  : (@array T n) -> T :=
  match n with
  | O => fun (arr : array 0) => init_val
  | S n' => fun (arr : array (S n')) => 
    f (a_fold_r f init_val (snd arr)) (fst arr)
  end.

(* the dot product of two arrays *)
Definition a_dot {T : Set} {n : nat} 
  (fmul fadd : T -> T -> T)
  (arr1 arr2 : @array T n) (zero : T) :=
  a_fold_l fadd zero (a_map2 fmul arr1 arr2).

(* append one array with another *)
Fixpoint a_app {T : Set} {n1 n2 : nat} : 
  (@array T n1) -> (@array T n2) -> (@array T (n1 + n2)) :=
  match n1 with
  | O => fun (_ : array 0) a2 => a2
  | S n1' => fun (arr1 : array (S n1')) a2 => 
    pair (fst arr1) (a_app (snd arr1) a2)
  end.

(* constant left multiplied to a array *)
Definition a_cmul {T : Set} {n : nat} (fmul : T -> T -> T)
  (a : T) (arr : array n) : array n :=
  a_map1 (fun x => fmul a x) arr.

(* constant right multiplied to a array *)
Definition a_mulc {T : Set} {n : nat} (fmul : T -> T -> T)
  (arr : array n) (a : T) : array n :=
  a_map1 (fun x => fmul x a) arr.


(* ======================================== *)
(* Operations of matrices *)

(* get (ir,rc) element of a matrix *)
Definition m_nth {T : Set} {r c : nat} (err : T) (A : matrix r c) 
  (ir ic : nat) : T := a_nth err (a_nth (a_make c err) A ir ) ic.

(* construct a matrix with same element *)
Fixpoint m_make {T : Set} (r c : nat) (x0 : T) : matrix r c :=
  match r with
  | O => a_make 0 x0
  | S r' => pair (a_make c x0) (m_make r' c x0)
  end.

(* construct a matrix m*n in the form of : 
 [[u(0,0),...,u(0,n-1)], ..., [u(m-1,0),...,u(m-1,n-1)]]. *)
Definition m_make' {T : Set} (m n : nat) (U : nat -> nat -> T) : matrix m n :=
  a_make' m (fun i => (a_make' n (U i))).

(* mapping one matrix to matrix *)
Fixpoint m_unary {T : Set} {r c : nat} (f : T -> T) 
  : (@matrix T r c) -> (@matrix T r c) :=
  match r with
  | O => fun (m : matrix 0 _) => tt
  | S r' => fun (m : matrix (S r') c) => 
    pair (a_map1 f (fst m)) (m_unary f (snd m))
  end.

(* mapping two matrices to another matrix *)
Fixpoint m_binary {T : Set} {r c : nat} (f : T -> T -> T) 
  : (@matrix T r c) -> (@matrix T r c) -> (@matrix T r c) 
  := match r with
  | O => fun (m1 m2 : matrix 0 _) => tt
  | S r' => fun (m1 m2 : matrix (S r') c) => 
    pair (a_map2 f (fst m1) (fst m2)) (m_binary f (snd m1) (snd m2))
  end.

(* get one row of a matrix as a array *)
Definition m_get_row {T : Set} {r c : nat} (zero : T)
  : (matrix r c) -> nat -> (array c) :=
  fun (m : matrix r c) (ir : nat) => 
    a_nth (a_make c zero) m ir.

(* get one column of a matrix as a array *)
Fixpoint m_get_col {T : Set} {r c : nat} (ic : nat) (zero : T)
  : (matrix r c) -> (array r) :=
  match r with
  | O => fun (m : matrix 0 _) => tt
  | S r' => fun (m : matrix (S r') c) => 
    pair (a_nth zero (fst m) ic) (m_get_col ic zero (snd m))
  end.

(*
(* an auxilary function for operation of matrix transpose *)
Fixpoint m_trans_aux {T : Set} {r c : nat} (err : T) (m : matrix r c)
  (ic : nat) : (matrix ic r) :=
  match ic with
  | O => tt
  | S ic' => pair (m_get_col (s - ic) err m) (m_trans_aux err m ic')
  end.
Compute m_trans_aux 99 m03 1.
Compute m_trans_aux 99 m03 2.
Compute m_trans_aux 99 m03 3.
Compute m_trans_aux 99 m03 4. (* Note, this is an error result *)

(* operation of matrix transpose *)
Definition m_trans {T : Set} {r c : nat} (err : T) (m : matrix r c) 
  : (matrix s r) := 
  m_trans_aux err m s.
*)

(* operation of matrix transpose *)
Definition m_trans {T : Set} {r c : nat} (zero : T) (m : matrix r c) 
  : (matrix c r) := 
  let fix aux (ic : nat) : (matrix ic r) :=
  match ic with
  | O => tt
  | S ic' => pair (m_get_col (c - ic) zero m) (aux ic')
  end in
  aux c.

(* transpose twice return original matrix *)
(*Lemma m_trans_trans_same_aux {T : Set} {r c : nat} (m : @matrix T r c) 
  (def : T) (r c : nat) : m_trans (m_trans m def) def = m.
unfold m_trans.
generalize dependent r.
generalize dependent c.
induction c.
- simpl. unfold m_trans_aux. induction r.
  + intros. destruct m. easy.
  + intros. simpl. apply IHr.
unfold m_trans_aux .
simpl.
*)

(* inner product with column-vector and matrix.
 cv(c) *' m(r,c) = rv(r) *)
Fixpoint cv_dotmul_m {T : Set} {r c : nat} (fmul fadd : T -> T -> T) 
  (arr : @array T c) (zero : T) : (@matrix T r c) -> (@array T r) :=
  match r with 
  | O => fun (m : matrix 0 _) => tt
  | S r' => fun (m : matrix (S r') c) => 
  pair 
    (a_dot fmul fadd arr (fst m) zero) 
    (cv_dotmul_m fmul fadd arr zero (snd m))
  end.

(* inner product with two matrix.
 m1(r,c) *' m2(t,c) = m(r,t) *)
Fixpoint m_dotmul_m {T : Set} {r c t : nat} (fmul fadd : T -> T -> T) (zero : T)
  : (@matrix T r c) -> (@matrix T t c) -> (@matrix T r t) :=
  match r with
  | O => fun (m1 : matrix 0 _) (m2 : matrix _ _) => tt
  | S r' => fun (m1 : matrix (S r') _) (m2 : matrix _ _) => 
    pair (cv_dotmul_m fmul fadd (fst m1) zero m2)
      (m_dotmul_m fmul fadd zero (snd m1) m2)
  end.

(* matrix multiplication  *)
Definition m_mul {T : Set} {r c t : nat} (fmul fadd : T -> T -> T) 
  (m1 : @matrix T r c) (m2 : @matrix T c t) (zero : T)
  : (@matrix T r t) :=
  let m2t := m_trans zero m2 in
  m_dotmul_m fmul fadd zero m1 m2t.

(* convert a row-vector to a matrix *)
Definition rv_to_m {T : Set} {n : nat} (arr : @array T n) 
  : @matrix T 1 n := a_make 1 arr.

(* convert a column-vector to a matrix *)
Definition cv_to_m {T : Set} {n : nat} (err : T) (arr : @array T n) 
  : @matrix T n 1 := m_make' n 1 (fun i j => a_nth err arr i).

(* array muliply matrix. 
 a(r) * m2(r,c) = m1(1,r) * m2(r,c) = m(1,c) *)
Definition a_mul_m {T : Set} {r c : nat} (fmul fadd : T -> T -> T) 
  (arr : @array T r) (m : @matrix T r c) (zero : T) : (@matrix T 1 c) :=
  m_mul fmul fadd (rv_to_m arr) m zero.

(* matrix muliply array.
 m1(r,c) * a(c) = m1(r,c) * m2(c,1) = m(r,1) *)
Definition m_mul_a {T : Set} {r c : nat} (fmul fadd : T -> T -> T) 
  (m : @matrix T r c) (arr : @array T c) (zero : T) : (@matrix T r 1) :=
  m_mul fmul fadd m (cv_to_m zero arr) zero.

(* convert a matrix with only one row to a array *)
Definition m_1xc_to_a {T : Set} {c : nat} (m : @matrix T 1 c) : @array T c :=
  fst m.

(* convert a matrix with only one column to a array *)
Fixpoint m_rx1_to_a {T : Set} {r : nat} : @matrix T r 1 -> @array T r :=
  match r with
  | O => fun (m : matrix 0 _) => tt
  | S r' => fun (m : matrix (S r') 1) => 
    pair (fst (fst m)) (m_rx1_to_a (snd m))
  end.
  
(* Note that, here we should add some invariant or lemmas about the conversion 
  between one-row/one-column matrix to array/row-vector/column-vector. Because 
  there are so many similiar concept *)
  
(* append two matrices by row, 
 m1(r1,c) @ m2(r2,c) = m(r1+r2,c) *)
Definition m_cons_byRow {T : Set} {r1 r2 c : nat} 
  (m1 : @matrix T r1 c) (m2 : @matrix T r2 c) : @matrix T (r1 + r2) c :=
  a_app m1 m2.

(* append two matrices by column, 
 m1(r,c1) @ m2(r,c2) = m(r,c1+c2) *)
Fixpoint m_cons_byCol {T : Set} {r c1 c2 : nat} :
  (@matrix T r c1) -> (@matrix T r c2) -> @matrix T r (c1 + c2) :=
  match r with
  | O => fun (m1 : matrix 0 _) (m2 : matrix 0 _) => tt
  | S r' => fun (m1 : matrix (S r') c1) (m2 : matrix (S r') c2) => 
    let arr1 := fst m1 in
    let arr2 := fst m2 in
    let m1' := snd m1 in
    let m2' := snd m2 in
    pair (a_app arr1 arr2) (m_cons_byCol m1' m2')
  end.

(* constant left multiplied to a matrix *)
Definition m_cmul {T : Set} {r c : nat} (fmul : T -> T -> T)
  (a : T) (m : matrix r c) : matrix r c :=
  m_unary (fun x => fmul a x) m.

(* constant right multiplied to a matrix *)
Definition m_mulc {T : Set} {r c : nat} (fmul : T -> T -> T)
  (m : matrix r c) (a : T) : matrix r c :=
  m_unary (fun x => fmul x a) m.


(* ======================================== *)
(* Operations of common data-types *)

(* conversion between array 2 and tuples. *)
Definition a2_from_tuples {T : Set} (t : T * T) : @array T 2 :=
  let '(a,b) := t in [a,b].
Definition a2_to_tuples {T : Set} (arr : @array T 2) : T * T :=
  let '(a,(b,tt)) := arr in (a,b).

(* conversion between array 3 and tuples. *)
Definition a3_from_tuples {T : Set} (t : T * T * T) : @array T 3 :=
  let '(a,b,c) := t in [a,b,c].
Definition a3_to_tuples {T : Set} (arr : @array T 3) : T * T * T :=
  let '(a,(b,(c,tt))) := arr in (a,b,c).

(* conversion between array 4 and tuples. *)
Definition a4_from_tuples {T : Set} (t : T * T * T * T) : @array T 4 :=
  let '(a,b,c,d) := t in [a,b,c,d].
Definition a4_to_tuples {T : Set} (arr : @array T 4) : T * T * T * T :=
  let '(a,(b,(c,(d,tt)))) := arr in (a,b,c,d).

(* convert matrix 1x1 to value *)
Definition m_1x1_to_scalar {T : Set} (m : @matrix T 1 1) : T :=
  let (a1, a2) := m in
  let (a11, _) := a1 in
  a11.

(* convert matrix 3x1 to tuples *)
Definition m_3x1_to_tuples {T : Set} (m : @matrix T 3 1) : (T * T * T) :=
  let (a1, t2) := m in
  let (a2, t3) := t2 in
  let (a3, t4) := t3 in
  let (a11, t12) := a1 in
  let (a21, t22) := a2 in
  let (a31, t32) := a3 in
    (a11,a21,a31).

(* convert matrix 3x3 to tuples ((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) *)
Definition m_3x3_to_tuples {T : Set} (m : @matrix T 3 3) 
  : (T * T * T) * (T * T * T) * (T * T * T) :=
  let (a1, t2) := m in 
  let (a2, t3) := t2 in
  let (a3, t4) := t3 in
    let (a11, t12) := a1 in
    let (a12, t13) := t12 in
    let (a13, t14) := t13 in
    let (a21, t22) := a2 in
    let (a22, t23) := t22 in
    let (a23, t24) := t23 in
    let (a31, t32) := a3 in
    let (a32, t33) := t32 in
    let (a33, t34) := t33 in
      ( 
        (a11,a12,a13),
        (a21,a22,a23),
        (a31,a32,a33)
      ).

(* determinant of a 3x3 square matrix *)
Definition m_3x3_det {T : Set} (fmul fadd : T -> T -> T) (fneg : T -> T) 
  (m : @matrix T 3 3) : T :=
  let '((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) := m_3x3_to_tuples m in
  let b1 := fmul (fmul a11 a22) a33 in
  let b2 := fmul (fmul a12 a23) a31 in
  let b3 := fmul (fmul a13 a21) a32 in
  let c1 := fmul (fmul a11 a23) a32 in
  let c2 := fmul (fmul a12 a21) a33 in
  let c3 := fmul (fmul a13 a22) a31 in
  let b := fadd (fadd b1 b2) b3 in
  let c := fadd (fadd c1 c2) c3 in
    fadd b (fneg c).

(* get the skew symmetric matrix of a 3-dim column vector *)
Definition cv3_skew_symmetric_matrix {T : Set} (zero : T) 
  (fneg : T -> T) (arr : @array T 3) : @matrix T 3 3 :=
  let '(ax,(ay,(az,tt))) := arr in [
    [zero, fneg az, ay],
    [az, zero, fneg ax],
    [fneg ay, ax, zero]].

(* cross product of two 3-dim column vector *)
Definition cv3_cross {T : Set} (fmul fadd : T -> T -> T) (fneg : T -> T) 
  (arr1 arr2 : @array T 3) (zero : T) :=
  m_mul fmul fadd 
    (cv3_skew_symmetric_matrix zero fneg arr1) 
    (cv_to_m zero arr2)
    zero.


(* get top n rows of a matrix as a smaller matrix 
given, m:matrix r c, n : nat
  if r <=? n 
  then: matrix 0 c
  else: matrix n c
*)

(*
Fixpoint m_get_rows_topn {T : Set} {r c : nat} (err : T) (n : nat) 
  : (@matrix T r c) -> (@matrix T (if r <=? n then 0 else n) c) :=
  match r,n with
  | 0, O => fun (m : matrix 0 c) => 
    let m1 : @matrix T 0 c := tt in m1
  | S r', O =>  fun (m : matrix (S r') c) => 
    let m1 : @matrix T 0 c := tt in m1
  | 0, S n' =>  fun (m : matrix 0 c) => 
    let m1 : @matrix T 0 c := tt in m1
  | S r', S n' =>  fun (m : matrix (S r') c) => 
    pair (fst m) (m_get_rows_topn err n' (snd m))
  end.

(* get some rows [r1~r2] of a matrix as a smaller matrix *)
Definition m_get_rows {T : Set} {r c : nat} (err : T) (m: @matrix T r c)
  (r1 r2 : nat) :=
  let fix top_n_rows (r' : nat) (r1' r2' : nat) 
    : (@matrix T r' c) -> (@matrix T (S (r2' - r1')) c) :=
    match r' with
    | O => 
  
  let r1_r2 := if (r <=? r2) || (r2 <? r1) (* require: r1 <= r2, and r2 < n *)
    then 0 else S (r2 - r1) in
  
  r'.

Compute m_get_rows 99 m04 1 2.
*)


(* --------------------------------------------------------------- *)
(* Module of array and matrix *)

Module Module_Array (E : EType).
  Export E.
  
  (* Notice that, there are two reasons to give these definitions:
  1. binding E.T to these freedom definitions
  2. we can adjust the order of the parameters as needed, and we can give 
    some default parameters here
  *)
  Definition array := @array T.
  Definition matrix := @matrix T.

  Definition a_nth {n} := @a_nth T n 0.
  Definition a_make := @a_make T.
  Definition a_make' := @a_make' T.
  Definition a_map1 {n} arr f  := @a_map1 T n f arr.
  Definition a_map2 {n} arr1 arr2 f := @a_map2 T n f arr1 arr2.
  Definition a_neg {n} arr1 := @a_map1 n arr1 neg.
  Definition a_add {n} arr1 arr2 := @a_map2 n arr1 arr2 add.
  Definition a_fold_l {n} arr f x0 := @a_fold_l T n f x0 arr.
  Definition a_fold_r {n} arr f x0 := @a_fold_r T n f x0 arr.
  Definition a_dot {n} arr1 arr2 := @a_dot T n mul add arr1 arr2 0.
  Definition a_app {n1 n2} := @a_app T n1 n2.
  Definition a_cmul {n} := @a_cmul T n mul.
  Definition a_mulc {n} := @a_mulc T n mul.
  
  Definition m_nth {r c} := @m_nth T r c 0.
  Definition m_make := @m_make T.
  Definition m_make' := @m_make' T.
  Definition m_unary {r c} m f := @m_unary T r c f m.
  Definition m_binary {r c} m1 m2 f := @m_binary T r c f m1 m2.
  Definition m_neg {r c} m := @m_unary r c m neg.
  Definition m_add {r c} m1 m2 := @m_binary r c m1 m2 add.
  Definition m_sub {r c} m1 m2 := @m_binary r c m1 m2 sub.
  Definition m_get_row {r c} (m : matrix r c) (ir : nat) 
    := @m_get_row T r c 0 m ir.
  Definition m_get_col {r c} (m : matrix r c) (ic : nat) 
    := @m_get_col T r c ic 0 m.
  Definition m_trans {r c} := @m_trans T r c 0.
  Definition cv_dotmul_m {r c} arr m := @cv_dotmul_m T r c mul add arr 0 m.
  Definition m_dotmul_m {r c t} := @m_dotmul_m T r c t mul add 0.
  Definition m_mul {r c t} m1 m2 := @m_mul T r c t mul add m1 m2 0.
  Definition rv_to_m {n} := @rv_to_m T n.
  Definition cv_to_m {n} := @cv_to_m T n 0.
  Definition a_mul_m {r c} arr m := @a_mul_m T r c mul add arr m 0.
  Definition m_mul_a {r c} m arr := @m_mul_a T r c mul add m arr 0.
  Definition m_1xc_to_a {c} := @m_1xc_to_a T c.
  Definition m_rx1_to_a {r} := @m_rx1_to_a T r.
  Definition m_cons_byRow {r1 r2 c} := @m_cons_byRow T r1 r2 c.
  Definition m_cons_byCol {r c1 c2} := @m_cons_byCol T r c1 c2.
  Definition m_cmul {r c} := @m_cmul T r c mul.
  Definition m_mulc {r c} := @m_mulc T r c mul.
  
  Definition a2_from_tuples := @a2_from_tuples T.
  Definition a2_to_tuples := @a2_to_tuples T.
  Definition a3_from_tuples := @a3_from_tuples T.
  Definition a3_to_tuples := @a3_to_tuples T.
  Definition a4_from_tuples := @a4_from_tuples T.
  Definition a4_to_tuples := @a4_to_tuples T.
  Definition m_1x1_to_scalar := @m_1x1_to_scalar T.
  Definition m_3x1_to_tuples := @m_3x1_to_tuples T.
  Definition m_3x3_to_tuples := @m_3x3_to_tuples T.
  Definition m_3x3_det := @m_3x3_det T mul add neg.
  
  Definition cv3_skew_symmetric_matrix := @cv3_skew_symmetric_matrix T 0 neg.
  Definition cv3_cross m1 m2 := @cv3_cross T mul add neg m1 m2 0.
  
  
  Definition m_3x3_unit : matrix 3 3 := [[1,0,0],[0,1,0],[0,0,1]].
  Definition I3 : matrix 3 3 := [[1,0,0],[0,1,0],[0,0,1]].
  Definition I4 : matrix 4 4 := [[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]].
  
  Notation "a '" := (m_trans a) (at level 28, left associativity).

  (* example of how to extract programs 
  From Coq Require Extraction.

  Extract Inductive unit => "unit" [ "()" ].
  Extract Inductive bool => "bool" [ "true" "false" ].
  Extract Inductive sumbool => "bool" [ "true" "false" ].
  Extract Inductive list => "list" [ "[]" "(::)" ].
  Extract Inductive prod => "(*)" [ "(,)" ].
  Extract Inductive nat => int [ "0" "succ" ] 
    "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

  (* a key probolem, array cannot be expressed in Ocaml *)
  Extraction array.
  (* Extraction "iterated_array.ml" m_mul.*)
  *)
  
End Module_Array.


(* --------------------------------------------------------------- *)
(* Concrete Module *)

(* based on Integer *)
Module Module_ArrayZ.
  Module ArrayZ := Module_Array ETypeZ.
  
  Export ArrayZ.
  (*
  Export Z.
  Export ETypeZ.
  *)
End Module_ArrayZ.

(* based on RealNumber *)
Module Module_ArrayR.
  Module VectorR := Module_Array ETypeR.
  
  Export VectorR.
  (*
  Export Reals.
  Export ETypeR.
  *)
  
  (* propertiy of SO3 matrix *)
  Definition so3 (m : matrix 3 3) : Prop := 
    let so3_mul_unit : Prop := m_mul (m_trans m) m = m_3x3_unit in
    let so3_det : Prop := m_3x3_det m = 1 in
      so3_mul_unit /\ so3_det.

End Module_ArrayR.


(* --------------------------------------------------------------- *)
(* Usage demo *)

(* based on Integer *)
Module DemoUsageForArrayZ.
  Import Module_ArrayZ.
  Open Scope Z.
  
  Example a3 : array 3 := [1,2,3].
  Example m32 : matrix 3 2 := [[1,2],[3,4],[5,6]].
End DemoUsageForArrayZ.

(* based on RealNumber *)
Module DemoUsageForArrayR.
  Export Module_ArrayR.
  Open Scope R.
  
  Example a3 : array 3 := [1,2,3].
  Example m32 : matrix 3 2 := [[1,2],[3,4],[5,6]].
End DemoUsageForArrayR.
