(*
  Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Extension for permutation, especially for computable permutation.
  author    : ZhengPu Shi
  date      : 2022.06
  
  remark    :
  1. compute permutation of a list, such as 
     perm [a;b;c] => [[a;b;c]; [a;c;b]; [b;a;c]; [b;c;a]; [c;a;b]; [c;b;a]]
     perm [1;2;3] => [[1;2;3]; [1;3;2]; [2;1;3]; [2;3;1]; [3;1;2]; [3;2;1]]
 *)

Require Import NatExt.
Require Import ListExt.
Require Import Vector.


(* ######################################################################### *)
(** * reverse-order-number of a list *)
Section ronum.

  Context {A : Type}.
  Context {Altb : A -> A -> bool}.
  Infix "<?" := Altb.

  Definition ronum1 (a : A) (l : list A) : nat :=
    fold_left (fun (n : nat) (b : A) => n + (if b <? a then 1 else 0)) l 0.
  
  Fixpoint ronum (l : list A) : nat :=
    match l with
    | [] => 0
    | x :: l' => ronum1 x l' + ronum l'
    end.

  (** ** parity of a list *)
  Section parity.

    (** Give speciall name for parity *)
    Definition Parity := bool.
    Definition PEven := true.
    Definition POdd := false.

    (** If the parity of permutation is odd return true, otherwise return false. *)
    Definition odd_perm (l : list A) : Parity := odd (ronum l).
    
    (** Is two list have different parity? *)
    Definition perm_parity_diff (l1 l2 : list A) : Prop :=
      let p1 := odd_perm l1 in
      let p2 := odd_perm l2 in
      p1 = (negb p2).
    
  End parity.

End ronum.

(* Compute ronum (Altb:=Nat.ltb) [2;4;3;1]. *)
(* Compute ronum (Altb:=Nat.ltb) [2;1;3;4]. *)


(* ######################################################################### *)
(** * Permutation of a list *)
Module Perm_with_list.

  (** ** Permutation of a list of n elements *)
  Section perm.
    Context {A : Type} {A0 : A}.

    (** Get k-th element and remaining elements from a list *)
    Fixpoint pick (l : list A) (k : nat) : A * list A :=
      match k with
      | 0 => (hd A0 l, tl l)
      | S k' =>
          match l with
          | [] => (A0, [])
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
      (* Compute pick l 3.     (* = (A0, [a; b; c]) *) *)
    End test.

    (** Get permutation of a list with a special level number *)
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
      (* Compute perm_aux 0 l.     (* = [[]] *) *)
      (* Compute perm_aux 1 l.     (* = [[a]] *) *)
      (* Compute perm_aux 2 l.     (* = [[a; b]; [b; a]] *) *)
    (* Compute perm_aux 3 l.     (* = [[a; b; c]; [a; c; b]; [b; a; c]; [b; c; a];  *)
     (*                              [c; a; b]; [c; b; a]] *) *)
    End test.

    (** Get permutation of a list *)
    Definition perm (l : list A) : list (list A) := perm_aux (length l) l.

    Lemma length_perm_cons : forall l a,
        length (perm (a :: l)) = length (a :: l) * length (perm l).
    Proof.
      induction l; intros; simpl; auto.
      unfold perm in *.
      (* Abort. *)
      (* simpl. *)
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

    (** The inverse number of a permutation *)
    (* Definition inv_no             (*  *) *)

  End perm.

  (* Compute perm [1;2]. *)
  (* Compute perm [1;2;3]. *)
  (* Compute perm [1;2;3;4]. *)
End Perm_with_list.


(* ######################################################################### *)
(** * Permutation of a vector *)
Module Export Perm_with_vector.

  (* Context {A : Type} {A0 : A}. *)
  Open Scope cvec_scope.
  
  (** ** Permutation of a list of n elements *)
  Section perm.

    Context {A : Type} (A0 : A).
    Infix "==" := (meq (Aeq:=eq)) : mat_scope.
    (* Infix "!" := (cvnth A0) : cvec_scope. *)
    
    (** Get k-th element and remaining elements from a vector *)
    Definition pick {n : nat} (v : @cvec A (S n)) (k : nat) : A * (cvec n) :=
      (v$k, cvremove v k).

    (** 显示pick的结果 *)
    Definition show_pick {n} (x : A * (@cvec A n)) :=
      (fst x, cv2l (snd x)).

    Section test.
      Variable a0 a b c : A.
      Let v := l2cv a0 3 [a;b;c].
      (* Compute show_pick (pick v 0).     (* = (a, [b; c]) *) *)
      (* Compute show_pick (pick v 1).     (* = (b, [a; c]) *) *)
      (* Compute show_pick (pick v 2).     (* = (c, [a; b]) *) *)
      (* Compute show_pick (pick v 3).     (* = (A0, [a; b; c]) *) *)
    End test.

    (** Get permutation of a vector *)
    Fixpoint perm {n : nat} : @cvec A n -> list (@cvec A n) :=
      match n with
      | 0 => fun _ => [cvec0 (A0:=A0)]
      | S n' => fun (v : cvec (S n')) =>
          let d1 := map (fun i => pick v i) (seq 0 n) in
          let d2 :=
            map (fun x : A * @cvec A n' =>
                   map (fun v0 => cvcons (fst x) v0) (perm (snd x))) d1 in
          concat d2
      end.

    (** show it is a proper morphism *)
    Global Instance perm_mor : forall n,
        Proper (meq (Aeq:=eq) ==> (eqlistA (meq (Aeq:=eq)))) (perm (n:=n)).
    Proof.
      simp_proper. induction n; intros; simpl; auto. constructor; easy.
      (* assert (map (fun i => pick x i) (seq 1 n) == map (fun i => pick y i) (seq 1 n))%list. *)
      (* rewrite H. *)
      (* eapply map_ext. *)
    Admitted.

    Lemma length_perm_cons : forall {n} (v:cvec n) a,
        length (perm (cvcons a v)) = (S n) * length (perm v).
    Proof.
      induction n; intros; auto.
      (* unfold perm in *. *)
      (* Abort. *)
      (* simpl. *)
      Admitted.


    Section test.
      Variable a0 a b c : A.
      (* Compute cvl2dl (perm (l2cv a0 0 [])). *)
      (* Compute cvl2dl (perm (l2cv a0 1 [a])). *)
      (* Compute cvl2dl (perm (l2cv a0 2 [a;b])). *)
      (* Compute cvl2dl (perm (l2cv a0 3 [a;b;c])). *)
      (* = [[a; b; c]; [a; b; c]; [b; a; c]; [b; a; c]; [c; a; b]; [c; a; b]] *)
    End test.

    (** Length of permutation *)
    Definition Pn {n} (v : @cvec A n) := length (perm v).

    (** Length of permutation equal to the factorial of the length *)
    Lemma Pn_eq : forall n (v : @cvec A n), Pn v = fact n.
    Proof.
      induction n; intros; simpl; auto.
      unfold Pn in *.
      pose proof (cvcons_remove v).
      rewrite <- H.
      rewrite length_perm_cons. rewrite IHn. lia.
    Qed.

    (** The inverse number of a permutation *)
    (* Definition inv_no             (*  *) *)

  End perm.

  (** ** parity of a vector *)
  Section parity.
    Context {A : Type}.
    Context {Altb : A -> A -> bool}.

    Definition odd_perm {n} (v : @cvec A n) : Parity :=
      odd_perm (Altb:=Altb) (cv2l v).
    Definition perm_parity_diff {n} (v1 v2 : @cvec A n) : Prop :=
      perm_parity_diff (Altb:=Altb) (cv2l v1) (cv2l v2).

    (* Definition odd_perm (l : list A) : bool := odd (ronum (Altb:=Altb) l). *)
    (* Definition even_perm (l : list A) : bool := even (ronum (Altb:=Altb) l). *)

    (** ** transposition, exchange, swap 对换 *)
    Section exchange.

      (* Context {A : Type}. *)
      Definition cvexchg {n} (v : @cvec A n) (i0 i1 : nat) : @cvec A n :=
        mk_cvec (fun i =>
                   if i =? i0
                   then v$i1
                   else (if i =? i1 then v$i0 else v$i)).

      (** 对换相邻位置改变排列的奇偶性 *)
      Theorem cvexchg_swap2close_parity : forall {n} (v : @cvec A n) i0 i1,
          i0 < n -> i1 < n -> (i0 = S i1 \/ i1 = S i0) ->
          perm_parity_diff v (cvexchg v i0 i1).
      Proof.
        (* 教科书上的证明很巧妙，难以形式化的描述出来 *)
        intros. unfold cvexchg, perm_parity_diff.
        unfold PermutationExt.perm_parity_diff, PermutationExt.odd_perm.
        cvec_to_fun. unfold cv2l. simpl.
        (* key part *)
        destruct H1; subst.
        - rename i1 into j.
          revert v j H H0. induction n; try easy.
          intros. simpl.
          rewrite <- ?seq_shift. rewrite ?map_map.
          destruct j.
          + simpl.
            rewrite Nat.odd_add.
      Abort.
      
      (** 对换改变排列的奇偶性 *)
      Theorem cvexchg_swap2_parity : forall {n} (v : @cvec A n),
          (forall i0 i1, i0 < n -> i1 < n -> i0 <> i1 -> perm_parity_diff v (cvexchg v i0 i1)).
      Proof.
        (* 教科书上的证明很巧妙，难以形式化的描述出来 *)
      Admitted.
      
    End exchange.

  End parity.

End Perm_with_vector.


(* ######################################################################### *)
(** * Determinant *)
Section det_try.

  (** 取出矩阵中的元素，第一个下标是顺序，第二个下标是全排列 *)

  (** 待计算的矩阵 *)
  Variable A : Type.
  Variable a0 a1 : A.
  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : A.
  Let m1 : mat 3 3 :=
    mk_mat_3_3 (A0:=a0) a11 a12 a13 a21 a22 a23 a31 a32 a33.
  (* Compute m2l m1. *)

  (** 计算行列式的一个步骤：取矩阵元素，第一个下标固定，第二个下标是全排列 *)
  (** 尝试构造下标 *)
  Let v1 : cvec 3 := mk_cvec (fun i => i).
  (* Compute cv2l v1. *)
  Let idx2 := perm 0 v1.
  (* Compute map cv2l idx2. *)

  (** 取出几个元素，相乘 *)
  Variable Amul : A -> A -> A.
  Infix "*" := Amul.
  Let F := fun {n} (vidx:cvec n) => cvfold vidx (fun a i => Amul a (m1$i$(vidx$i))) a1.
  (* Compute F v1. *)

  (** 造出了行列式的每个项 *)
  (* Compute map F idx2. *)

  (** 构造出了单个表达式，但是还没有符号 *)
  Variable Aadd : A -> A -> A.
  Infix "+" := Aadd.
  (* Compute fold_left Aadd (map F idx2) a0. *)
  
End det_try.

Section det.

  Context `{R : Ring}.
  Notation "- a" := (Aopp a) : A_scope.
  Infix "*" := Amul : A_scope.

  (** Get sign of column-index's reverse-order-no.
      i.e. if odd-permutation then -1 else 1 *)
  Let sign4idx {n} (ids : @cvec nat n) : A :=
        if odd_perm (Altb:=Nat.ltb) ids then -A1 else A1.
  
  (** Determinant of a square matrix *)
  Definition det {n} (m : smat A n) : A :=
    let col_ids : list (cvec n) := perm 0 (mk_cvec (fun i => i)) in
    let F :=
      fun (col_id : cvec n) =>
        (sign4idx col_id) *
          cvfold col_id (fun a i => a * (m $ i $ (col_id$i))) A1 in
    fold_left Aadd (map F col_ids) A0.

  (** Determinant of a square matrix (by row index) *)
  Definition det' {n} (m : smat A n) : A :=
    let row_ids : list (cvec n) := perm 0 (mk_cvec (fun i => i)) in
    let F :=
      fun (row_id : cvec n) =>
        (sign4idx row_id) *
          cvfold row_id (fun a j => a * (m $ (row_id$j) $ j)) A1 in
    fold_left Aadd (map F row_ids) A0.

End det.

Require Import ZArith Rbase.

Section export.
  Open Scope Z_scope.
  Definition detZ {n} (m : smat Z n) : Z := @det _ Z.add 0 Z.opp Z.mul 1 n m.
  Definition detZ' {n} (m : smat Z n) : Z := @det' _ Z.add 0 Z.opp Z.mul 1 n m.
  
  Open Scope R_scope.
  Definition detR {n} (m : smat R n) : R := @det _ Rplus 0 Ropp Rmult 1 n m.
End export.

(** 《高等代数》邱维声 第三版 习题2.2 *)
Section exercise.

  (** Numeric matrix *)
  Open Scope Z_scope.
  
  Let ex_1_5 : mat 5 5 :=
        l2m 0 [[0;0;0;1;0];[0;0;2;0;0];[0;3;8;0;0];[4;9;0;7;0];[6;0;0;0;5]].
  Goal detZ ex_1_5 = 120. auto. Qed.

  Let ex_2_1 : mat 3 3 := l2m 0 [[1;4;2];[3;5;1];[2;1;6]].
  Goal detZ ex_2_1 = -49. auto. Qed.

  (** Symbolic matrix *)
  Open Scope R.

  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : R.
  Let ex_2_3 : mat 3 3 := l2m 0 [[a11;a12;a13];[0;a22;a23];[0;0;a33]].
  Goal detR ex_2_3 = a11 * a22 * a33. cbv. ring. Qed.
  
End exercise.


(** ** Propertities of determinant *)
Section det_props.

  Context `{R : Ring}.
  Infix "==" := Aeq : A_scope.
  Notation det := (@det A Aadd A0 Aopp Amul A1).

  Lemma det_trans : forall {n} (m : smat A n), det (m\T) == det m.
  Admitted.


End det_props.
