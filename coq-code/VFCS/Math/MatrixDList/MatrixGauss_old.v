(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Gauss elimination of matrix (old version)
  author    : ZhengPu Shi
  date      : 2023.12

  remark    :
 *)

Require Import NatExt.
Require Import CoqExt.Hierarchy.
Require Import MatrixList.Matrix.
Require Import CoqExt.MyExtrOCamlR.
Require QcExt RExt.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.

(* ======================================================================= *)
(** ** Gauss elimination. *)

(** 高斯消元法的一个部分的实现，仅做参考 *)
Module gauss_elimination_old.

  Section gauss.
    Context `{F:Field}.
    Add Field field_inst : make_field_theory.

    Context {Teqdec: @Dec A}.

    Infix "+" := Aadd : A_scope.
    Notation "- a" := (Aopp a) : A_scope.
    Notation Asub := (fun x y => Aadd x (Aopp y)).
    Infix "-" := Asub : A_scope.
    Infix "*" := Amul : A_scope.

    Infix "+" := (@madd A Aadd _ _) : mat_scope.
    Infix "*" := (@mmul A Aadd Azero Amul _ _ _) : mat_scope.
    Notation "/ a" := (Ainv a) : A_scope.
    Infix "c*" := (@mcmul A Amul _ _) : mat_scope.
    Notation "m $ i $ j " := (mnth Azero m i j) : mat_scope.
    Notation mat1 := (@mat1 _ Azero Aone).
    (* Notation l2m := (@l2m A Azero _ _). *)

    (** *** 初等行变换 (brt: Basic Row Transform) *)

    (* 
     0 0 0
     0 0 0
     0 c 0
     *)
    (* A matrix which only one element is non-zero *)
    Definition brt_e {r c} (ri rj : nat) (k : A) : mat r c :=
      f2m (fun i j => if (i =? ri) && (j =? rj) then k else Azero).

    (* Multiply k times of a row *)
    (*
    1 0 0
    0 c 0
    0 0 1
     *)
    Definition brt_cmul {r c} (ri : nat) (k : A) : mat r c :=
      f2m (fun i j => if i =? j then (if i =? ri then k else Aone) else Azero).

    (* 第 y 行的 k 倍加到第 x 行 *)
    (* 
     1 0 0
     0 1 0
     0 c 1
     *)
    (* Definition row_add_to_row {n} (x y : nat) (k : A) : mat n n := *)
    (*   mat1 + (brt_e x y k). *)

    (** Add k times of rj-th row to rj-th row *)
    Definition brt_add {n} (ri rj : nat) (k : A) : mat n n :=
      (* f2m (fun i j => *)
      (*           if (i =? ri) && (j =? rj) *)
      (*           then k *)
      (*           else (if i =? j then Aone else Azero)). *)
      mat1 + (brt_e ri rj k).

    
    (** 交换两行 *)
    (*
    x =1 , y=2

    1 0 0  -1 0 0   0 0 0   0 0 0   0 1 0    0 1 0
    0 1 0 + 0 0 0 + 0-1 0 + 1 0 0 + 0 0 0  = 1 0 0
    0 0 1   0 0 0   0 0 0   0 0 0   0 0 0    0 0 1
     *)
    (* Definition swap {n} (x y : nat) : mat n n := *)
    (*   mat1 + (e x x (-Aone)) + (e y y (-Aone)) + (e x y Aone) + (e y x Aone). *)

    Definition brt_swap {n} (ri rj : nat) : mat n n :=
      (* f2m (fun i j => *)
      (*           if i =? ri *)
      (*           then (if j =? rj then Aone else Azero) *)
      (*           else (if i =? rj *)
      (*                 then (if j =? ri then Aone else Azero) *)
      (*                 else (if i =? j then Aone else Azero))). *)
      mat1
      + (brt_e ri ri (-Aone))
      + (brt_e rj rj (-Aone))
      + (brt_e ri rj Aone)
      + (brt_e rj ri Aone).

    Definition invertible {n} (M : mat n n) :=
      exists M', M * M' = mat1 /\ M' * M = mat1.

    (* 
     1 2 1      
     -1-3 1  =>  return 0
     1 0 6     

     [(n - i)++, y] , i 
     得到第一个非0 *)
    (** 从第i行开始，检查第y列的第一个非零元素的序号 *)
    Fixpoint get_first_none_zero {n} (MA: mat n n) (i: nat) (y: nat) : nat :=
      match i with
      | O => n
      | S i' =>
          if (Aeqb (MA $ (n - i) $ y) Azero) then
            get_first_none_zero MA i' y
          else
            n - i
      end.

    (* 某一行加到另一行 *)
    Fixpoint elem_change_down {n} (MA: mat n n) (x: nat) (cur: nat) : mat n n * mat n n :=
      match cur with
      | O => (mat1, MA)
      | S cur' =>
          (* 将第 n-cur 行的 MA[n-cur,x] 倍加到第 n 行 *)
          let ee := brt_add (n - cur) x (- (MA $ (n - cur) $ x)) in
          (* 递归进行，左侧是构造的初等矩阵的累乘，右侧是变换后的矩阵 *)
          let (E', EA') := elem_change_down (ee * MA) x cur' in
          (E' * ee, EA')
      end.

    Fixpoint row_echelon_form {n} (MA: mat n n) (i: nat) : option (mat n n * mat n n) :=
      match i with
      | O => Some (mat1, MA)
      | S i' =>
          let r := get_first_none_zero MA i (n - i) in
          if (r =? n) then
            None
          else
            let M0 := (brt_swap (n - i) r) * MA in
            (* 把当前0行和第一个非0行互换 *)
            let ee := (brt_cmul (n - i) (/(M0 $ (n - i) $ (n - i)))) in
            (* 保证这一列第一个数字是1 *)
            let (E', EA') := elem_change_down (ee * M0) (n - i) (i - 1) in
            (* 下面元素全部与当前行相减，变成0 *)
            let ret := row_echelon_form EA' i' in
            match ret with
            | None => None
            | Some (E'', EA'') => Some (E'' * E' * ee * brt_swap (n - i) r, EA'')
            end
      end.

    Fixpoint elem_change_up {n} (MA: mat n n) (x: nat) (i: nat) :=
      match i with
      | O => (mat1, MA)
      | S i' =>
          let ee := brt_add i' x (- (MA $ i' $ x)) in
          let (E, MT) := elem_change_up (ee * MA) x i' in
          (E * ee, MT)
      end.

    Fixpoint fst_to_I {n} (MA: mat n n) (i: nat) :=
      match i with
      | O => (mat1, MA)
      | S i' =>
          let (E, MT) := elem_change_up (MA) i' i' in
          let (E', MT') := fst_to_I MT i' in
          (E' * E, MT')
      end.

    Definition minv_gauss {n} (MA: mat n n) := 
      match row_echelon_form MA n with
      | None => None
      | Some (E, MT) => Some (fst (fst_to_I MT n) * E)
      end.

  End gauss.

  Section test.
    Import ZArith.
    Open Scope Z.

    Definition z_brt_swap := (@brt_swap _ Z.add 0 Z.opp 1).
    (* Compute m2l (z_brt_swap 3 0 2). *)
    (* Compute m2l (z_brt_swap 3 1 2). *)
    
    Definition z_elem_change_down {n} (m:mat n n) i j :=
      @elem_change_down _ Z.add 0 Z.opp Z.mul 1 _ m i j. 

    Let m1 := @l2m _ 0 3 3 [[1;2;3];[4;5;6];[7;8;9]].
    
    (* Compute get_first_none_zero (Azero:=0) m1 3 0. *)
    
    (* Compute let (m1,m2) := z_elem_change_down m1 0 0 in m2l m2. *)
    (* Compute let (m1,m2) := z_elem_change_down m1 0 1 in m2l m2. *)
    (* Compute let (m1,m2) := z_elem_change_down m1 0 2 in m2l m2. *)
    (* Compute let (m1,m2) := z_elem_change_down m1 0 3 in m2l m2. *)
  End test.

End gauss_elimination_old.

