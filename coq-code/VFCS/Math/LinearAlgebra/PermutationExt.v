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
    Definition POdd := true.
    Definition PEven := false.

    (** Calulate parity of a list *)
    Definition perm_parity (l : list A) : Parity := odd (ronum l).
    
    (** Is two list have different parity? *)
    Definition perm_parity_diff (l1 l2 : list A) : Prop :=
      let p1 := perm_parity l1 in
      let p2 := perm_parity l2 in
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
      intros. simpl. unfold Pn.
      unfold perm. simpl. rewrite app_length. rewrite map_length. f_equal.
      rewrite List.map_map.
      rewrite concat_length.
      rewrite List.map_map.
    Admitted.

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
Module Perm_with_vector.

  Context {A : Type} {A0 : A}.
  Context {Altb : A -> A -> bool}.
  Open Scope cvec_scope.
  Infix "!" := (cvnth A0) : cvec_scope.
  
  (** ** Permutation of a list of n elements *)
  Section perm.
    
    (** Get k-th element and remaining elements from a vector *)
    Definition pick {n : nat} (v : @cvec A (S n)) (k : nat) : A * (cvec n) :=
      (v ! k, cvremove v k).

    Section test.
      Variable a0 a b c : A.
      Let l := l2cv a0 3 [a;b;c].
      (* Compute pick l 0.     (* = (a, [b; c]) *) *)
      (* Compute pick l 1.     (* = (b, [a; c]) *) *)
      (* Compute pick l 2.     (* = (c, [a; b]) *) *)
      (* Compute pick l 3.     (* = (A0, [a; b; c]) *) *)
      (* Compute cv2l (cvremove l 4). *)
    End test.

    (** Get permutation of a vector *)
    Fixpoint perm {n : nat} : @cvec A n -> list (@cvec A n) :=
      match n with
      | 0 => fun _ => [cvec0 (A0:=A0)]
      | S n' => fun (v : cvec (S n')) =>
          let d1 := map (fun i => pick v i) (seq 0 n) in
          let d2 :=
            map (fun k : A * @cvec A n' =>
                   let (x, v') := k in
                   let d3 := perm v' in
                   map (fun v0 => cvcons x v') d3) d1 in
          concat d2
      end.

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

    (** Pn of cons. 
      Example: Pn [a;b;c;d] = 4 * Pn [a;b;c] *)
    (* Lemma Pn_cons : forall {n} (a : A) (v : @vec A n), Pn (a :: v) = (length (a :: l)) * (Pn l). *)
    (* Proof. *)
    (*   intros. simpl. unfold Pn. *)
    (*   unfold perm. simpl. rewrite app_length. rewrite map_length. f_equal. *)
    (*   rewrite List.map_map. *)
    (*   rewrite concat_length. *)
    (*   rewrite List.map_map. *)
    (* Admitted. *)

    (** Length of permutation equal to the factorial of the length *)
    Lemma Pn_eq : forall n (v : @cvec A n), Pn v = fact n.
    Proof.
    (*   induction l; simpl; auto. *)
    (*   rewrite Pn_cons. rewrite IHl. simpl. auto. *)
      (* Qed. *)
      Abort.

    (** The inverse number of a permutation *)
    (* Definition inv_no             (*  *) *)

  End perm.

  (** ** parity of a vector *)
  Definition perm_parity {n} (v : @cvec A n) : Parity :=
    perm_parity (Altb:=Altb) (cv2l v).
  Definition perm_parity_diff {n} (v1 v2 : @cvec A n) : Prop :=
    perm_parity_diff (Altb:=Altb) (cv2l v1) (cv2l v2).
  
  (** ** transposition, exchange, swap 对换 *)
  Section exchange.
    
    Definition cvexchg {n} (v : @cvec A n) (i0 i1 : nat) : @cvec A n :=
      mk_cvec (fun i =>
                if i =? i0
                then v!i1
                else (if i =? i1 then v!i0 else v!i)).

    (** 对换相邻位置改变排列的奇偶性 *)
    Theorem cvexchg_swap2close_parity : forall {n} (v : @cvec A n) i0 i1,
        i0 < n -> i1 < n -> (i0 = S i1 \/ i1 = S i0) ->
        perm_parity_diff v (cvexchg v i0 i1).
    Proof.
      (* 教科书上的证明很巧妙，难以形式化的描述出来 *)
      intros. unfold cvexchg, perm_parity_diff.
      unfold PermutationExt.perm_parity_diff, PermutationExt.perm_parity.
      unfold cvnth,mnth. solve_mnth; try lia.
      clear l0 l l1.
      unfold cvec in *. mat_to_fun. simpl. unfold cv2l. simpl.
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

  (** ** odd/even permutation *)
  Section odd_even.
    Context {A : Type}.
    Context {Altb : A -> A -> bool}.

    Definition odd_perm (l : list A) : bool := odd (ronum (Altb:=Altb) l).
    Definition even_perm (l : list A) : bool := even (ronum (Altb:=Altb) l).
  End odd_even.

  (** ** transposition, exchange, swap *)
  Section exchange.
    

  End exchange.
End Perm_with_vector.


(* ######################################################################### *)
(** * Determinant *)

