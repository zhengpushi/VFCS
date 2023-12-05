(*
Copyright 2022 ZhengPu Shi
This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix Determinant
  author    : ZhengPu Shi
  date      : 2022.06
  
  remark    :
  1. compute permutation of a list, such as 
     perm [a;b;c] => [[a;b;c]; [a;c;b]; [b;a;c]; [b;c;a]; [c;a;b]; [c;b;a]]
     perm [1;2;3] => [[1;2;3]; [1;3;2]; [2;1;3]; [2;3;1]; [3;1;2]; [3;2;1]]
 *)

Require Import NatExt.
Require Import MatrixList.Matrix.


Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv.

(** ** Parity of a list 奇偶性 *)
Section parity.

  Inductive Parity :=
  | POdd | PEven.

  (* Conversion between nat and parity *)
  Definition nat2Parity (n : nat) : Parity := if odd n then POdd else PEven.

End parity.

(** ** reverse-order-number (RON) of a list 逆序数 *)
Section ronum.

  Context {A : Type}.
  Context {Altb : A -> A -> bool}.
  Infix "<?" := Altb.

  (* The RON of one element respect to a list *)
  Definition ronum1 (a : A) (l : list A) : nat :=
    fold_left (fun (n : nat) (b : A) => n + (if b <? a then 1 else 0)) l 0.

  (* The RON of a list *)
  Fixpoint ronum (l : list A) : nat :=
    match l with
    | [] => 0
    | x :: l' => ronum1 x l' + ronum l'
    end.

  (** If the parity of permutation is odd return true, otherwise return false. *)
  Definition odd_perm (l : list A) : Parity := nat2Parity (ronum l).
  
  (** Is two list have different parity? *)
  Definition perm_parity_diff (l1 l2 : list A) : Prop :=
    let p1 := odd_perm l1 in
    let p2 := odd_perm l2 in
    p1 <> p2.

End ronum.

(* Compute ronum (Altb:=Nat.ltb) [2;4;3;1]. (* 4 *) *)
(* Compute ronum (Altb:=Nat.ltb) [2;1;3;4]. (* 1 *) *)


(** ** Permutation of a list *)
Section perm.
  Context {A : Type} {Azero : A} {Altb:A->A->bool}.

  (** Get k-th element and remaining elements from a list *)
  Fixpoint pick (l : list A) (k : nat) : A * list A :=
    match k with
    | 0 => (hd Azero l, tl l)
    | S k' =>
        match l with
        | [] => (Azero, [])
        | x :: l' =>
            let (a,l0) := pick l' k' in
            (a, [x] ++ l0)
        end
    end.

  Section test.
    Variable a b c : A.
    Let l := [a;b;c].
    (* Compute pick l 0.     (* = (a, [b; c]) *) *)
    (* Compute pick l 1.     (* = (b, [a; c]) *) *)
    (* Compute pick l 2.     (* = (c, [a; b]) *) *)
    (* Compute pick l 3.     (* = (Azero, [a; b; c]) *) *)
  End test.

  (** Get permutation of a list from its top n elements *)
  Fixpoint perm_aux (n : nat) (l : list A) : list (list A) :=
    match n with
    | 0 => [[]]
    | S n' =>
        let d1 := map (fun i => pick l i) (seq 0 n) in
        let d2 :=
          map (fun k : A * list A =>
                 let (x, lx) := k in
                 let d3 := perm_aux n' lx in
                 map (fun l1 => [x] ++ l1) d3) d1 in
        concat d2
    end.

  Section test.
    Variable a b c : A.
    Let l := [a;b;c].
    (* Compute perm_aux 0 l.   (* = [[]] *) *)
    (* Compute perm_aux 1 l.   (* = [[a]] *) *)
    (* Compute perm_aux 2 l.   (* = [[a; b]; [b; a]] *) *)
    (* Compute perm_aux 3 l.   (* = [[a; b; c]; [a; c; b]; [b; a; c];  *)
    (*                                 [b; c; a]; [c; a; b]; [c; b; a]] *) *)
  End test.

  (** Get permutation of a list *)
  Definition perm (l : list A) : list (list A) := perm_aux (length l) l.

  Lemma length_perm_cons : forall l a,
      length (perm (a :: l)) = length (a :: l) * length (perm l).
  Proof.
    intros. unfold perm. induction l.
    - simpl. auto.
    - simpl in *.
  Admitted.

  Section test.
    Variable a b c : A.
    (* Compute perm [a;b;c]. *)
    (* = [[a; b; c]; [a; c; b]; [b; a; c]; [b; c; a]; [c; a; b]; [c; b; a]] *)
  End test.

  (** Length of permutation *)
  Definition Pn (l : list A) := length (perm l).

  (** Pn of cons. 
      Example: Pn [a;b;c;d] = 4 * Pn [a;b;c] *)
  Lemma Pn_cons : forall (a : A) (l : list A), Pn (a :: l) = (length (a :: l)) * (Pn l).
  Proof.
    intros a l. revert a. induction l; auto. intros. simpl.
    unfold Pn in *. simpl.
    rewrite length_perm_cons. rewrite IHl.
    simpl. lia.
  Qed.

  (** Length of permutation equal to the factorial of the length *)
  Lemma Pn_eq : forall l, Pn l = fact (length l).
  Proof.
    induction l; simpl; auto.
    rewrite Pn_cons. rewrite IHl. simpl. auto.
  Qed.

End perm.

(* Compute perm [1;2;3]. *)

(* (** ** transposition, exchange, swap 对换 *) *)
(* Section exchange. *)

(*   (* Context {A : Type}. *) *)
(*   Definition cvexchg {n} (v : @cvec T n) (i0 i1 : nat) : @cvec T n := *)
(*     f2cv (fun i => *)
(*             if i =? i0 *)
(*             then v$i1 *)
(*             else (if i =? i1 then v$i0 else v$i)). *)

(*   (** 对换相邻位置改变排列的奇偶性 *) *)
(*   Theorem cvexchg_swap2close_parity : forall {n} (v : @cvec T n) i0 i1, *)
(*       i0 < n -> i1 < n -> (i0 = S i1 \/ i1 = S i0) -> *)
(*       perm_parity_diff v (cvexchg v i0 i1). *)
(*   Proof. *)
(*     (* 教科书上的证明很巧妙，难以形式化的描述出来 *) *)
(*     intros. unfold cvexchg, perm_parity_diff. *)
(*     unfold PermutationExt.perm_parity_diff, PermutationExt.odd_perm. *)
(*     cvec2fun. unfold cv2l. simpl. *)
(*     (* key part *) *)
(*     destruct H1; subst. *)
(*     - rename i1 into j. *)
(*       revert v j H H0. induction n; try easy. *)
(*       intros. simpl. *)
(*       rewrite <- ?seq_shift. rewrite ?map_map. *)
(*       destruct j. *)
(*       + simpl. *)
(*         rewrite Nat.odd_add. *)
(*   Abort. *)
  
(*   (** 对换改变排列的奇偶性 *) *)
(*   Theorem cvexchg_swap2_parity : forall {n} (v : @cvec T n), *)
(*       (forall i0 i1, i0 < n -> i1 < n -> i0 <> i1 -> *)
(*                 perm_parity_diff v (cvexchg v i0 i1)). *)
(*   Proof. *)
(*     (* 教科书上的证明很巧妙，难以形式化的描述出来 *) *)
(*   Admitted. *)
  
(* End exchange. *)


(** ** Determinant *)
Section det.

  Context `{HARing : ARing}.
  
  (** Determinant of a square matrix *)
  Definition det {n} (m : @smat A n) : A :=
    let colIds := perm (Azero:=0) (seq 0 n) in
    let item (l:list nat) : A :=
      fold_left Amul
        (map (fun i => mnth Azero m i (nth i l 0)) (seq 0 n)) Aone in
    let sign (l:list nat) : Parity := nat2Parity (ronum l (Altb:=Nat.ltb)) in
    let items : list A :=
      map (fun l =>
             match sign l with
             | POdd => Aopp (item l)
             | PEven => item l
             end) colIds in
    fold_left Aadd items Azero.

End det.

(* Compute det (mk_mat_0_c 0). (* 0x0 矩阵的行列式是什么？ *) *)
(* Compute det (mk_mat_1_1 1). *)
(* Compute det (mk_mat_2_2 1 2 3 4). *)
(* Compute det (mk_mat_3_3 1 2 3 4 5 6 7 8 9). *)

Require Import ZArith Rbase.

Section export.
  Open Scope Z_scope.
  Definition detZ {n} (m : @smat Z n) : Z := @det _ Z.add 0 Z.opp Z.mul 1 n m.
  
  Open Scope R_scope.
  Definition detR {n} (m : @smat R n) : R := @det _ Rplus 0 Ropp Rmult 1 n m.
End export.

(** 《高等代数》邱维声 第三版 习题2.2 *)
Section exercise.

  (** Numeric matrix *)
  Open Scope Z_scope.
  
  Let ex_1_5 : mat 5 5 :=
        l2m 0 _ _ [[0;0;0;1;0];[0;0;2;0;0];[0;3;8;0;0];[4;9;0;7;0];[6;0;0;0;5]].
  Goal detZ ex_1_5 = 120. cbv. auto. Qed.

  Let ex_2_1 : mat 3 3 := l2m 0 _ _ [[1;4;2];[3;5;1];[2;1;6]].
  Goal detZ ex_2_1 = -49. auto. Qed.

  (** Symbolic matrix *)
  Open Scope R.

  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : R.
  Let ex_2_3 : mat 3 3 := l2m 0 _ _ [[a11;a12;a13];[0;a22;a23];[0;0;a33]].
  Goal detR ex_2_3 = a11 * a22 * a33. cbv. ring. Qed.
  
End exercise.


(** ** Propertities of determinant *)
Section det_props.

  Context `{R : Ring}.
  Notation det := (@det A Aadd Azero Aopp Amul Aone).

  Lemma det_trans : forall {n} (m : @smat A n), det (m\T) = det m.
  Admitted.

End det_props.
