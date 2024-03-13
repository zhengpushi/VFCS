Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import PeanoNat.
Require Import Arith.
Require Import Omega.


(** ** Matrix Module *)
Require Export List.
Require Export Matrix.Mat_def.
Require Export Matrix.Mat_trans.
Require Export Matrix.Mat_map.
Require Export Matrix.Mat_add.
Require Export Matrix.Mat_sub.
Require Export Matrix.Mat_mult.
Require Export Matrix.Mat_IO.
Require Export Matrix.Mat_mult_lemma.
Require Export Matrix.Mat_trans_lemma.
Require Export Matrix.Matrix_Module.

Require Export Setoid.
Require Export Relation_Definitions.
Set Implicit Arguments.



(* ################################################################# *)
(** * Definition of Module Type *)

Module Type MType.

Parameter A :Set.
Parameter Zero One : A.
Parameter opp : A -> A.
Parameter inv : A -> A.
Parameter add sub mul div: A->A->A.

Infix " + " := add.
Infix " - " := sub.
Infix " * " := mul.

Parameter add_comm : forall x y , x + y = y + x.
Parameter add_assoc : forall x y z , x + y + z = x + (y + z).
Parameter add_assoc2 : forall x y z w, (x+y)+(z+w) = (x+z)+(y+w).
Parameter add_zero_l : forall x , Zero + x  = x.
Parameter add_zero_r : forall x , x + Zero = x.

Parameter sub_assoc : forall x y z, x - y - z = x - (y + z).
Parameter sub_assoc2: forall x y z w, (x+y)-(z+w) = (x-z)+(y-w).
Parameter sub_opp : forall x y , x - y = opp (y - x ).
Parameter sub_zero_l:forall x ,Zero - x = opp x.
Parameter sub_zero_r:forall x , x - Zero = x.
Parameter sub_self : forall x , x-x =Zero.
Parameter sub_self2 : forall x , Zero-x+x =Zero.
Parameter sub_self3 : forall x , Zero+x-x =Zero.

Parameter add_sub_assoc : forall x y z, x+(y-z) = x + y - z.

(*Parameter mul_one_l : forall x , One * x = x. *)
Parameter mul_add_distr_l : forall x y z, (x+y)*z = x*z + y*z.
Parameter mul_add_distr_r : forall x y z, x*(y+z) = x*y + x*z.
Parameter mul_sub_distr_l : forall x y z, (x-y)*z = x*z - y*z.
Parameter mul_sub_distr_r : forall x y z, x*(y-z) = x*y - x*z.
Parameter mul_assoc : forall x y z, x * y * z = x * (y * z).
Parameter mul_zero_l : forall x , Zero * x = Zero.
Parameter mul_zero_r : forall x , x * Zero = Zero.
Parameter mul_one_l : forall x , One * x = x.
Parameter mul_one_r : forall x , x * One = x.
Parameter mul_comm : forall x y, x*y = y*x.

Parameter inv_self : forall x, inv x * x = One.

Parameter eqdec : A -> A -> bool.

End MType.




Module Matrix (M : MType).

Infix "*e" := M.mul (at level 40, left associativity) : ME_scope.
Infix "+e" := M.add (at level 50, left associativity) : ME_scope.
Infix "-e" := M.sub (at level 50, left associativity) : ME_scope.
Infix "/e" := M.div (at level 50, left associativity) : ME_scope.

Open Scope ME_scope.
Delimit Scope ME_scope with ME.

Notation e0 := M.Zero.
Notation e1 := M.One.


Fixpoint reduce {A} (n: nat) (f: A -> nat -> A) (zero: A) : A :=
  match n with
  | O => zero
  | S n' => f (reduce n' f zero) n'
  end.
(* reduce 5 f 0 *)
(* f (reduce 4 f 0) 4 *)
(* f (f (reduce 3 f 0) 3) 4 *)
(* f (f (f (reduce 2 f 0) 2) 3) 4 *)
(* f (f (f (f (reduce 1 f 0) 1) 2) 3) 4 *)
(* f (f (f (f (f (reduce 0 f 0) 1) 2) 3) 4 *)
(* f (f (f (f (f 0 1) 2) 3) 4 *)
Compute reduce 5 Nat.add 0.

Definition pointwise_relation_n {A} (n: nat) (R: relation A) : relation (nat -> A) :=
  fun (f g : nat -> A) => forall (a: nat), a < n -> R (f a) (g a).

Lemma pointwise_relation_n_decr {A}:
  forall (n : nat) (m1 m2 : nat -> A) (R : relation A),
    pointwise_relation_n (S n) R m1 m2 -> pointwise_relation_n n R m1 m2.
Proof.
  unfold pointwise_relation_n. intuition.
Qed.



Add Parametric Morphism (A : Type) (n : nat) : (@reduce A n)
  with signature (pointwise_relation A (pointwise_relation nat eq) ==>
                  eq ==>
                  eq)
  as reduce_morphism.
(* 两种关系 x,y x = y -> forall n:A , reduce n x n = reduce n y n *)
Proof.
  intros r1 r2 pt_r zero.
  induction n; intros. simpl. auto.
  - simpl.
    unfold pointwise_relation in *. (* forall (a : A) (a0 : nat), eq (r1 a a0) (r2 a a0) *)
    rewrite pt_r.
    f_equal.
    rewrite IHn.
    auto.
Qed.






Add Parametric Morphism (A : Type) (n : nat) : (@reduce A n)
  with signature (pointwise_relation A (pointwise_relation_n n eq) ==>
                  eq ==>
                  eq)
  as reduce_n_morphism.
(* 两种关系 
forall (x y : A -> nat -> A),
 x = y -> 
 forall y0 : A, reduce n x y0 = reduce n y y0 *)
Proof.
  intros r1 r2 ptr zero.
  induction n; intros; simpl.
  - auto.
  -
(*   try rewrite ptr. *)
  unfold pointwise_relation in *.
  unfold pointwise_relation_n in *.
  rewrite ptr.
  rewrite IHn.
  auto.
  intuition.
  auto.
Qed.

(* sum f(k-1) f(k-2) f(k-3) f(k-4) ... f(0) *)
Notation sum k f := (reduce k (fun acc x => acc +e f x) e0).

Section MatrixElemOps.


(* 
per_scan_relation nat eq x y -> sum k x = sum k y
 *)
Add Parametric Morphism k : (fun f => sum k f)
    with signature (pointwise_relation nat (@eq M.A) ==> @eq M.A)
      as sum_morphism. 
(* forall x y : nat -> M.A, per_scan_relation nat eq x y -> sum k x = sum k y *)
Proof.
  intros. apply reduce_morphism.
  unfold pointwise_relation.
  intuition.
  unfold pointwise_relation in *.
  rewrite H.
  auto.
  auto.
Qed.


(* 
per_scan_n k eq x y -> sum k x = sum k y
 *)
Add Parametric Morphism k : (fun f => sum k f)
    with signature (pointwise_relation_n k (@eq M.A) ==> @eq M.A)
      as sum_n_morphism.
(* forall x y : nat -> M.A, per_scan_n k eq x y -> sum k x = sum k y *)
Proof.
  intros. apply reduce_n_morphism.
  unfold pointwise_relation.
  unfold pointwise_relation_n.
  intuition.
  unfold pointwise_relation_n in *.
  rewrite H.
  auto.
  auto.
  auto.
Qed.


(* sum (f1(x) + f2(x)) = sum f1(x) + sum f2(x) *)
Lemma sum_distribute :
  forall (n : nat) (f1 f2 : nat -> M.A),
    sum n (fun x => f1 x +e f2 x) = sum n f1 +e sum n f2.
Proof.
  induction n; simpl; intros.
  - rewrite M.add_zero_l; auto.
  - rewrite IHn.

    rewrite <- M.add_assoc.
    rewrite <- M.add_assoc.
    f_equal.
    rewrite M.add_assoc.
    rewrite M.add_comm.
    rewrite M.add_assoc.
    rewrite M.add_comm.
    f_equal.
    rewrite M.add_comm.
    f_equal.
Qed.

(* a * sum f(x) = sum a*f1(x) + a*f2(x) *)
Lemma sum_multiply_l :
  forall (a : M.A) (n : nat) (f : nat -> M.A),
    a *e sum n f = sum n (fun x => a *e f x).
Proof.
  induction n; simpl; intros.
  - rewrite M.mul_zero_r; auto.
  - rewrite <- IHn.
    rewrite M.mul_add_distr_r; auto.
Qed.

(* sum f(x) * a = sum f1(x) *a + f2(x) *a *)
Lemma sum_multiply_r :
  forall (a : M.A) (n : nat) (f : nat -> M.A),
    sum n f *e a = sum n (fun x => f x *e a).
Proof.
  induction n; simpl; intros.
  try rewrite <- IHn.

  - rewrite M.mul_zero_l. auto.
  - rewrite <- IHn.
    rewrite M.mul_add_distr_l; auto.
Qed. 

(* sum n f = 0 *)
Lemma sum_e0 :
  forall n, (sum n (fun k => e0)) = e0.
Proof.
  induction n.
  - simpl. auto.
  - simpl. rewrite M.add_zero_r. auto.
Qed.

(* f = g => sum n f = sum n g *)
Lemma sum_eq :
  forall n (f g : nat -> M.A),
   (forall i, i < n -> f i = g i) -> sum n f = sum n g.
Proof.
  intros.
  induction n; simpl; intros.
  - auto.
  - rewrite <- IHn.
    + rewrite H. auto. auto.
    + auto.
Qed.

(* sum n f 0 *)
  Lemma sum_e0' :
    forall n (f : nat -> M.A),
     (forall i, i < n -> f i = e0) -> (sum n (fun k => f k)) = e0.
  Proof.
    induction n; simpl; intros.
    - auto.
    - rewrite H. rewrite M.add_zero_r; auto. auto.
   Qed.


(* 除了f(x)其他 f(i)都为0, sum n f = f(x) *)
  Lemma sum_single :
    forall (n : nat) (f : nat -> M.A) (x : nat) (y : M.A),
       x < n -> 
        (forall i, i < n -> i <> x -> f(i) = e0) -> 
          y = f x -> 
            (sum n (fun k => f k)) = y.
  Proof.
    intros.
(* 
 *)
    induction n.
    - omega.
    - destruct (x =? n) eqn : H2.   (* 是不是第x个 *)
      + apply Nat.eqb_eq in H2.
        subst.
        unfold sum.

        rewrite sum_e0'.
        * rewrite M.add_zero_l; auto.
        * intros. rewrite H0. auto. auto. omega.  (*求解Z和nat类型的线性方程组和不等式是非常强大的*)
      + apply beq_nat_false in H2.
        assert (x < n). omega.
        apply IHn in H3.
        simpl.

        rewrite H0 with (i := n); auto.   (* 取 i= n *)
        rewrite M.add_zero_r; auto.
        intros.
        apply H0; auto. 
  Qed. 


Lemma sum_swap :
  forall (m n : nat) (f : nat -> nat -> M.A),
    sum n (fun k => sum m (fun k' => f k' k)) = sum m (fun k => sum n (fun k' => f k k')).
Proof.
  induction m. simpl; intros.
  - rewrite (sum_e0 n). auto.
  - intros.
    simpl.
    rewrite !sum_distribute.
    rewrite IHm.
    auto.
Qed.

End MatrixElemOps.




Definition A := M.A.

Definition Mat_height :=@height A.

Definition Mat_width := @width A.

Definition MMat := @Mat A .

Definition MmkMat := mkMat A.

Definition M_eq := @M_eq A .
Arguments M_eq {m} {n}.

Definition Mtrans := @trans A M.Zero.
Arguments Mtrans {m} {n}.

Definition Melement_op:= @matrix_each A.

Definition Madd := @matrix_each A M.add.
Arguments Madd {m} {n}.

Definition Msub := @matrix_each A M.sub.
Arguments Msub {m} {n}. 

Definition Mopp := @matrix_map A M.opp.
Arguments Mopp {m} {n}.

Definition Mtimes := @matrix_mul A M.Zero M.add M.mul.
Arguments Mtimes {m} {n} {p}.

Definition Mmulc_l:= @const_mul_l A M.mul.
Arguments Mmulc_l {m} {n}.

Definition Mmulc_r:= @const_mul_r A M.mul.
Arguments Mmulc_r {m} {n}.

Definition MMO := @MO A M.Zero.

Definition MMI := @MI A M.Zero M.One.


(* get i-th element of a vector *)
Fixpoint l_nth (n : nat) (default : A) (l :list A):= 
  match n , l with
    | O,a::t => a
    | S n' ,a::t => l_nth n' default t
    | O,nil  => default
    | S n' , nil => default
  end.

(* get i-th element of a 2-vector *)
Fixpoint dl_nth (n : nat)  (dl :list (list A)):= 
  match n , dl with
    | O,a::t => a
    | S n' ,a::t => dl_nth n' t
    | O,nil  => nil
    | S n' , nil => nil
  end.

Definition Mget {m n :nat} (ma: Mat A  m n) (i j :nat) :=
l_nth j M.Zero (dl_nth i (mat A m n ma)).


Definition Meq {m n} (m1: Mat A m n) (m2 : Mat A m n) :=
  forall i j,
    i < m ->
    j < n ->
      Mget m1 i j = Mget m2 i j.



(* 
第i行，第n-j列
j从n开始
 *)
Fixpoint generate_row  (f: nat -> nat -> A) (j n i: nat) :=
  match j with
  | 0 => nil
  | S j' =>
       f i (n - j):: generate_row f j' n i
  end.

(* 
判断条件应该去掉，否则难以证明
 *)
(* 
第i行，第n-j列
j从n开始
i从m开始
 *)
Fixpoint generate_matrix (f: nat -> nat -> A) (m n i: nat) :=
  match i with
  | 0 => nil
  | S i' =>
    generate_row f n n (m-i):: generate_matrix f m n i'
  end.

(* 
必须以i为分界点，不然证明不出来
 *)
Lemma dlist_o_height_help : forall (f: nat -> nat -> A) (m n i: nat),
  i<=m ->
  length (generate_matrix f m n i) = i.
Proof.
  intros.
  induction i.
  - auto.
  - simpl. f_equal. apply IHi. auto. omega.
Qed.



(** *** dlist_o_length *)
(* dlist_o_height m n产生的list高度是m *)
(** The height of the two-dimensional list generated by dlist_o is m. *)
Lemma dlist_o_height : forall (f: nat -> nat -> A) (m n: nat),
   length (generate_matrix f m n m) = m.
Proof.
  intros.
  apply dlist_o_height_help with (i:=m).
  auto.
Qed.

Lemma generate_row_length_help : forall (f: nat -> nat -> A) (m n i j: nat),
j<=n ->
length (generate_row f j n (m - S i)) = j.
Proof.
  intros.
  induction j.
  simpl. auto.
  simpl. f_equal.
  induction n. inversion H.
  apply IHj.
  omega.
Qed.

Lemma generate_row_length : forall (f: nat -> nat -> A) (m n i: nat),
  length (generate_row f n n (m - S i)) = n.
Proof.
  intros.
  induction n.
  induction m.
  induction i.
  simpl. auto.
  simpl. auto.
  simpl. auto.
  simpl. f_equal. apply generate_row_length_help with (j:=n).
  omega.
Qed.



Lemma dlist_o_width_help : forall (f: nat -> nat -> A) (m n i: nat),
  i<=m ->
  width (generate_matrix f m n i) n.
Proof.
  intros.
  induction i.
  simpl. auto. simpl. split. apply generate_row_length.
  apply IHi. omega.
Qed.


(** *** dlist_o_width *)
(* dlist_o_width m n产生的list高度是m *)
(** The width of the two-dimensional list generated by dlist_o is n. *)
Lemma dlist_o_width : forall (f: nat -> nat -> A) (m n: nat),
   width (generate_matrix f m n m) n.
Proof.
  intros.
  apply dlist_o_width_help with (i:=m).
  auto.
Qed.



(** Generate a matrix with height m and width n. *)
Definition Mfill (m n: nat) (f: nat -> nat -> A) :=
  let dl := generate_matrix f m n m in
    mkMat A m n dl (dlist_o_height f m n) (dlist_o_width f m n).


Axiom Mtimes_help : forall(m n p: nat) (m1: MMat m n) (m2: MMat n p),
      forall i j,
        i < m -> j < p ->
        Mget (Mtimes m1 m2) i j = 
          reduce n (fun (acc : M.A) (x : nat) => acc +e (Mget m1 i x) *e (Mget m2 x j)) e0.


Axiom Mtrans_help : 
  forall (m n: nat) (m1: MMat m n),
    forall i j,
      i < m -> j < n ->
        Mget (Mtrans m1 ) j i = Mget m1 i j.


Axiom Melement_op_help : forall (m n: nat) (m1: Mat A m n) (m2: Mat A m n) (op: A -> A -> A),
      forall i j,
        i < m -> j < n ->
        Mget (Melement_op op m1 m2) i j = op (Mget m1 i j) (Mget m2 i j).


Axiom Mfill_help : forall (m n: nat) (f: nat -> nat -> A),
      forall i j,
        i < m -> j < n ->
        Mget (@Mfill m n f) i j = f i j.





(* 逐个点相加、减 *)
Infix "M*" := Mtimes (at level 40, left associativity) : matrix_scope.
Infix "M+" := (Melement_op M.add) (at level 50, left associativity) : matrix_scope.
Infix "M-" := (Melement_op M.sub) (at level 50, left associativity) : matrix_scope.


(* 
原本eq
 *)
Infix "===" := M_eq (at level 70) : matrix_scope.
(* 
新eq
 *)
Infix "M=" := Meq (at level 70) : matrix_scope.
Notation "m &[ i , j ]" := (Mget m i j) (at level 20, format "m &[ i ,  j ]") : matrix_scope.


Delimit Scope matrix_scope with M.
Open Scope matrix_scope.

Section SpecialMatrices.
  Variable n: nat.

Ltac elim_bool:=
  repeat match goal with
         | [ |- context [Nat.eqb ?x ?y]] 
             => let eq := fresh "eq" in destruct (x =? y) eqn: eq
         | [H: ?x =? ?y = false |- _] 
             => apply Nat.eqb_neq in H
         | [H: ?x =? ?y = true |- _] 
             => apply Nat.eqb_eq in H
         end.



Definition I := @Mfill n n (fun i j => (if beq_nat i j then M.One else M.Zero)).

(* 
0 0 0
0 0 0
0 c 0
 *)
(* 初等矩阵 *)
Definition single_val (x y: nat) (c: A) := @Mfill n n (fun i j => (if ((beq_nat i x) && (beq_nat j y))%bool then c else M.Zero)).

(*
1 0 0
0 c 0
0 0 1
*)
Definition matrix_row_mul (x: nat) (c: A) := @Mfill n n (fun i j => (if beq_nat i j then (if beq_nat i x then c else M.One) else M.Zero)).

(* 
1 0 0
0 1 0
0 c 1
 *)
Definition matrix_row_add_to_row (x y: nat) (c: A) := I M+ (single_val x y c). 

(*
x =1 , y=2
*)
(*
1 0 0  -1 0 0   0 0 0   0 0 0   0 1 0    0 1 0
0 1 0 + 0 0 0 + 0-1 0 + 1 0 0 + 0 0 0  = 1 0 0
0 0 1   0 0 0   0 0 0   0 0 0   0 0 0    0 0 1
 *)
Definition matrix_swap (x y: nat) := I M+ (single_val x x (M.opp M.One)) M+ (single_val y y (M.opp M.One)) M+ (single_val x y M.One) M+ (single_val y x M.One).


Lemma I_is_left_identity:
  forall MA: Mat A n n, I M* MA M= MA.
Proof.
    unfold I.
    intros.
      unfold Meq.
      intros.
      rewrite Mtimes_help; auto.
      rewrite sum_single with (x := i) (y := MA&[i,j]); auto.
      + intros.
        rewrite Mfill_help; auto.
        assert (i <> i0). omega.

(*         apply <- Nat.eqb_neq in H2.
        rewrite H2. *)

        apply <- Nat.eqb_neq in H3.
        rewrite H3.
        rewrite M.mul_zero_l.
        auto.
      + rewrite Mfill_help; auto.
        rewrite <- beq_nat_refl.  (* true = (n =? n) *)
        rewrite M.mul_one_l.
        auto.
Qed.


Lemma I_is_right_identity:
  forall MA: Mat A n n, MA M* I M= MA.
Proof.
    unfold I.
    intros.
    unfold Meq.
    intros.
    rewrite Mtimes_help.
    rewrite sum_single with (x := j) (y := MA&[i, j]); auto.  (* x=j的时候，即n=j，表示对角线，和的值为0+0+1*MA&[i, j] *)
      + intros.
      rewrite Mfill_help.
      apply <- Nat.eqb_neq in H2.
      rewrite H2.
      rewrite M.mul_zero_r; auto.
      auto.
      auto.
(*       auto. *)

      + assert (I&[j, j] = e1).                               (* x=j的时候，即n=j，表示对角线 *)
      {
        unfold I.
        rewrite Mfill_help; try assumption.
        rewrite <- beq_nat_refl.
        reflexivity. 
      }
      rewrite Mfill_help; try assumption.
      rewrite <- beq_nat_refl.
      rewrite M.mul_one_r.
      auto.
      + auto.
      + auto.
Qed.

Lemma I_trans_I:
   Mtrans I M= I.
Proof.
    unfold I.
    intros.
    unfold Meq.
    intros.
    rewrite Mtrans_help; auto.
(*     assert (I&[j, j] = e1).
    {
        unfold I.
        rewrite Mfill_help; try assumption.
        rewrite <- beq_nat_refl.
        reflexivity. 
    }                             (* x=j的时候，即n=j，表示对角线 *) *)
    rewrite !Mfill_help; auto.
    destruct (j =? i) eqn: eq. destruct (i =? j) eqn: eq1. auto.
    apply Nat.eqb_eq in eq.
    apply Nat.eqb_neq in eq1. omega.
    destruct (i =? j) eqn: eq1. auto.
    apply Nat.eqb_neq in eq.
    apply Nat.eqb_eq in eq1. omega.
    auto.
Qed.


(* 同一性 *)
Lemma I_is_identity:
    forall MA: Mat A n n, MA M* I M= MA /\ I M* MA M= MA.
Proof.
    split.
    apply I_is_right_identity.
    apply I_is_left_identity.
Qed.

(* 
构建二维表与各元素联系
 *)

(*
0 0 0   1 1 1   0 0 0
0 0 0 * 1 1 1 = 0 0 0
0 0 c   1 1 1   c c c
*)
(* x,y处值为c *)
Lemma single_val_map:
  forall (x y : nat) (c : A) (i j : nat), forall MA: Mat A n n, 
      i < n -> j < n -> x < n -> y < n ->
      Mget ((single_val x y c) M* MA) i j = if (i =? x) then c *e Mget MA y j else e0. 
Proof.
  intros.
  destruct (i =? x) eqn:eq.
  
  
  - 
    unfold single_val.
    rewrite Mtimes_help; auto.
    apply sum_single with (x := y); auto.
    + intros.
      rewrite Mfill_help; auto.
      destruct (i0 =? y) eqn:eq1.
      apply Nat.eqb_eq in eq1.
      omega.
      destruct (i =? x) eqn:eq0.
      auto; simpl.
      apply Nat.eqb_eq in eq0.

      rewrite M.mul_zero_l; auto.
      
     auto; simpl.

      rewrite M.mul_zero_l; auto.

    + rewrite Mfill_help; auto.
      destruct (y =? y) eqn:eq1.
      destruct (i =? x) eqn:eq0.
      auto; simpl.
      auto; simpl.
      apply Nat.eqb_neq in eq0.
      inversion eq.
      destruct (i =? x) eqn:eq0.
      auto; simpl.
      apply Nat.eqb_neq in eq1.
      auto.
      contradiction.
      apply Nat.eqb_neq in eq0.
      apply Nat.eqb_neq in eq1.
      inversion eq.

  -
    unfold single_val.
    rewrite Mtimes_help; auto.
    apply sum_e0'.
    intros.
    rewrite Mfill_help; auto.
    destruct (i0 =? y) eqn:eq1; destruct (i =? x) eqn:eq0; auto; simpl; subst; try tauto.
    apply Nat.eqb_eq in eq0.
    apply Nat.eqb_eq in eq1.
    inversion eq.

    rewrite M.mul_zero_l; auto.
    rewrite M.mul_zero_l; auto.
    rewrite M.mul_zero_l; auto.
Qed.

(*
1 0 0   1 1 1   1 1 1
0 c 0 * 1 1 1 = c c c
0 0 1   1 1 1   1 1 1
*)
Lemma row_mul_map:
  forall (x : nat) (c : A) (i j : nat), forall MA: Mat A n n, 
      i < n -> j < n -> x < n ->
      Mget ((matrix_row_mul x c) M* MA) i j = if (i =? x) then c *e Mget MA i j else Mget MA i j. 
Proof.
  intros.
  destruct (i =? x) eqn:eq.
  - 
    unfold matrix_row_mul.
    rewrite Mtimes_help; auto.
    apply sum_single with (x := i); auto.
    + intros.
      rewrite Mfill_help; auto.
      destruct (i =? i0) eqn:eq0; destruct (i =? x) eqn:eq1; auto; simpl; subst.
      apply Nat.eqb_eq in eq0.
      apply Nat.eqb_eq in eq1.
      omega.
      apply Nat.eqb_eq in eq0.
      apply Nat.eqb_neq in eq1.
      omega.
      rewrite M.mul_zero_l; auto.
      rewrite M.mul_zero_l; auto.
    + rewrite Mfill_help; auto.
      destruct (i =? i) eqn:eq0; destruct (i =? x) eqn:eq1; auto; simpl; subst; try tauto.
      inversion eq.
      apply Nat.eqb_eq in eq1.
      apply Nat.eqb_neq in eq0.
      omega.
      inversion eq.
  - unfold matrix_row_mul.
    rewrite Mtimes_help; auto; simpl.
    apply sum_single with (x := i); auto.
    + intros. rewrite Mfill_help; auto.
      destruct (i =? i0) eqn:eq0; destruct (i =? x) eqn:eq1; auto; simpl; subst; try tauto.
      inversion eq.
      apply Nat.eqb_eq in eq0.
      omega.
      rewrite M.mul_zero_l; auto.
      rewrite M.mul_zero_l; auto.
    + rewrite Mfill_help; auto.
      destruct (i =? i) eqn:eq0; destruct (i =? x) eqn:eq1; auto; simpl; subst; try tauto.
      inversion eq.
      rewrite M.mul_one_l; auto.
      apply Nat.eqb_neq in eq0.
      omega.
      apply Nat.eqb_neq in eq0.
      contradiction.
Qed.

(* ??? *)
Lemma matrix_mul_distr_l:
  forall {x y p} (m1: Mat A x y) (m2: Mat A x y) (m3: Mat A y p),
    (m1 M+ m2) M* m3 M= m1 M* m3 M+ m2 M* m3.
Proof.
  red.
  intros.
  rewrite Mtimes_help; try assumption. rewrite Melement_op_help; try assumption.
  rewrite Mtimes_help; try assumption. rewrite Mtimes_help; try assumption.
  replace (reduce y (fun (acc : M.A) (x0 : nat) => acc +e (m1 M+ m2)&[i, x0] *e m3&[x0, j]) e0)
    with  (reduce y (fun (acc : M.A) (x0 : nat) => acc +e (m1&[i, x0] *e m3&[x0, j] +e m2&[i, x0] *e m3&[x0, j])) e0).
  - apply sum_distribute.
  - apply sum_n_morphism. hnf. intros.
    rewrite Melement_op_help; try assumption.
    rewrite M.mul_add_distr_l; auto.
Qed.


(* 
1 0 0   1 1 1   1   1   1
0 1 0 * 1 1 1 = 1   1   1
0 c 1   1 1 1  c+1 c+1 c+1
 *)
Lemma row_add_to_row_map:
  forall (x y : nat) (c : A) (i j : nat), forall MA: Mat A n n, 
      i < n -> j < n -> x < n -> y < n ->
        Mget ((matrix_row_add_to_row x y c) M* MA) i j = 
          (if i =? x then Mget MA i j +e c *e Mget MA y j else Mget MA i j). 
Proof.
  intros.
  destruct (i =? x) eqn:eq; intros; unfold matrix_row_add_to_row.
  - 
    apply Nat.eqb_eq in eq.
    rewrite matrix_mul_distr_l; auto.
    rewrite Melement_op_help; auto.
    assert ((single_val x y c M* MA)&[i, j] = c *e MA&[y, j]).
    {
      rewrite single_val_map; auto. destruct (i =? x) eqn:eq0. auto.
      apply Nat.eqb_neq in eq0. omega. 
    }
    rewrite H3.
    assert (I M* MA M= MA) by apply I_is_identity.
    rewrite H4; auto.
  - 
    rewrite matrix_mul_distr_l; auto.
    rewrite Melement_op_help; auto.
    assert ((single_val x y c M* MA)&[i, j] = e0).
    {
      rewrite single_val_map; auto. destruct (i =? x) eqn:eq0. auto.
      inversion eq. auto.
    }
    rewrite H3.
    assert (I M* MA M= MA) by apply I_is_identity.
    rewrite H4; auto.
    rewrite M.add_zero_r; auto.
Qed.


(* 
0 1 0   1 1 1   2 2 2
1 0 0 * 2 2 2 = 1 1 1
0 0 1   3 3 3   3 3 3
 *)
Lemma swap_map:
  forall (x y i j : nat), forall MA: Mat A n n, 
      i < n -> j < n -> x < n -> y < n ->
      Mget ((matrix_swap x y) M* MA) i j = (if i =? x then Mget MA y j else if i =? y then Mget MA x j else Mget MA i j). 
Proof.
  intros.
  destruct (i =? x) eqn:eq.
  unfold matrix_swap.
(*   rewrite matrix_mul_distr_l; try auto; rewrite Melement_op_help; try assumption.
  rewrite matrix_mul_distr_l; try auto; rewrite Melement_op_help; try assumption.
  rewrite matrix_mul_distr_l; try auto; rewrite Melement_op_help; try assumption.
  rewrite matrix_mul_distr_l; try auto; rewrite Melement_op_help; try assumption. *)
  repeat (rewrite matrix_mul_distr_l; try rewrite Melement_op_help; try assumption).
  
  rewrite single_val_map; try omega.
  destruct (i =? x) eqn:eq0.
  rewrite I_is_left_identity; try omega.
  apply Nat.eqb_eq in eq0.
  subst.
  rewrite single_val_map; try omega.
  destruct (x =? y) eqn:eq1.
  apply Nat.eqb_eq in eq1.
  subst.
  rewrite single_val_map; try omega. 
  destruct (y =? y) eqn:eq0.
  apply Nat.eqb_eq in eq0.
  subst.
  
  repeat (rewrite single_val_map; repeat (try elim_bool; auto; try omega); try omega);
          try rewrite I_is_left_identity; 
          repeat subst; repeat (try elim_bool; auto; try omega).


  - 
  rewrite <- M.sub_zero_l.
  rewrite M.mul_sub_distr_l.
  rewrite M.mul_zero_l.
  rewrite M.mul_one_l.
  rewrite M.add_sub_assoc.

(*
MA&[i, j] +e e0 -e MA&[x, j] +e (e0 -e e1) *e MA&[y, j] +e MA&[y, j] +e MA&[x, j] = MA&[y, j]
*)
  rewrite M.add_sub_assoc.
  rewrite M.add_zero_r.
  rewrite M.add_zero_r.
  rewrite M.sub_self.
  rewrite M.add_comm.
  rewrite M.sub_zero_l.
  
  rewrite <-M.add_assoc.
  rewrite M.add_comm.
  
  rewrite <-M.sub_zero_l.
  rewrite <-M.add_assoc.
  rewrite M.add_sub_assoc.
  rewrite M.add_zero_r.
  rewrite <-M.add_sub_assoc.
  rewrite M.sub_self.
  rewrite M.add_zero_r; auto.
(*   - assumption.
  - assumption. *)
  -
  apply Nat.eqb_neq in eq0.
  contradiction.
  -
  rewrite single_val_map; try omega.
  destruct (x =? x) eqn:eq0.
  apply Nat.eqb_eq in eq0.
  apply Nat.eqb_neq in eq1.

  rewrite single_val_map; try omega.
  destruct (x =? y) eqn:eq2.
  apply Nat.eqb_eq in eq2.
  subst.
  contradiction.
  

  rewrite <- M.sub_zero_l.
  rewrite M.mul_sub_distr_l.
  rewrite M.mul_zero_l.
  rewrite M.mul_one_l.
  rewrite M.add_sub_assoc.

  rewrite M.add_zero_r.
  rewrite M.add_zero_r.

  rewrite M.add_zero_r; auto.
  rewrite M.sub_self.
  rewrite M.mul_one_l.
  rewrite M.add_zero_l; auto.
  apply Nat.eqb_neq in eq0.
  contradiction.
  
(*   - assumption.
  - assumption. *)

  -
  inversion eq.
  -
  unfold matrix_swap.
  repeat (rewrite matrix_mul_distr_l; repeat(destruct (i =? y) eqn:eq0); 
          try rewrite matrix_mul_distr_l; 
          try rewrite Melement_op_help;
          try assumption);
  repeat (rewrite single_val_map; repeat (try elim_bool; auto; try omega); try omega);
          try rewrite I_is_left_identity; 
          repeat subst; repeat (try elim_bool; auto; try omega).

  inversion eq.
  

(*   repeat (rewrite single_val_map; elim_context);
  try rewrite I_is_left_identity;
  repeat subst;
  repeat (rewrite M.mul_one_l); try assumption. *)
  repeat (rewrite M.add_zero_r); auto.
  rewrite M.mul_one_l; auto.
  rewrite <-M.sub_zero_l.
  rewrite M.mul_sub_distr_l.
  rewrite M.mul_zero_l.
  rewrite M.mul_one_l.
  rewrite M.add_sub_assoc.
  rewrite M.add_comm.
  rewrite M.add_sub_assoc.
  rewrite M.add_zero_r.
  rewrite <-M.add_sub_assoc.
  rewrite M.sub_self.
  rewrite M.add_zero_r.
  auto.


  inversion eq.
  rewrite !M.add_zero_r; auto.
Qed.


End SpecialMatrices.



  
Lemma Mt_refl {m n}: reflexive (Mat A m n) (Meq).
Proof.
  unfold reflexive. unfold "M=". 
  intros.
  reflexivity.
Qed.
  
Lemma Mt_sym {m n}: symmetric (Mat A m n) (Meq).
Proof.
  unfold symmetric. unfold "M=".
  intros.
  rewrite H; auto.
Qed.
  
Lemma Mt_trans {m n}:  transitive (Mat A m n) (Meq).
Proof.
  unfold transitive. unfold "M=".
  intros.
  rewrite H; auto.
Qed.

Global Add Parametric Relation {m n}: (Mat A m n) (Meq)
    reflexivity proved by Mt_refl
    symmetry proved by Mt_sym
    transitivity proved by Mt_trans                      
      as Meq_id.



Global Add Parametric Morphism m n p: (Mtimes) with
    signature (Meq (m:=m)(n:=n)) ==> (Meq (m:=n)(n:=p)) ==> (Meq (m:=m)(n:=p)) 
       as Mtimes_mor.
Proof.
  intros.
  unfold "M=".
  intros.
  rewrite Mtimes_help; auto.
  rewrite Mtimes_help; auto.
  apply sum_n_morphism.
  red. intros.
  rewrite H; try assumption.
  rewrite H0; try assumption.
  reflexivity.
Qed.

(*    Global Add Parametric Morphism m n: (Mopp) with
        signature (Meq (m:=m)(n:=n)) ==> (Meq (m:=m)(n:=n))  as Mopp_mor. 
  Proof.
    intros.
    unfold "M=".
    intros.
Admitted. *)

Global Add Parametric Morphism m n: (Mtrans) with
    signature (Meq (m:=m)(n:=n)) ==> (Meq )  as Mtrans_mor. 
Proof.
  intros.
  unfold "M=".
  intros.
  rewrite Mtrans_help; auto.
  rewrite Mtrans_help; auto.
Qed.




Section MatrixInversion.
  Variable n:nat.

  Set Implicit Arguments.

  Definition MI := @I n.
  Definition ME := @single_val n. 
  Definition row_mul_n := @matrix_row_mul n .
  Definition row_add_to_row_n := @matrix_row_add_to_row n .
  Definition swap_n := @matrix_swap n .

  Definition invertible (MA : Mat A n n) :=
    exists MB, MA M* MB M= MI /\ MB M* MA M= MI.

  (* 
  满秩矩阵
   *)
  Axiom l_inv_r_inv :
    forall (MA E: Mat A n n),
      E M* MA M= MI -> MA M* E M= MI.

  Lemma I_is_invertible:
    invertible MI.
  Proof.
    exists MI.
    split; apply I_is_identity.
  Qed.

(** ** teq_mul *)
(** Transpose properties of matrix multiplication : T(AB) = T(B)*T(A) *)
Theorem matrix_trans_mul:
    forall {m n p} (m1: Mat A m n) (m2: Mat A n p),
      Mtrans (m1 M* m2) M= (Mtrans m2) M* (Mtrans m1).
Proof.
    red. intros.
    setoid_rewrite Mtimes_help; try assumption.
    rewrite Mtrans_help ; try assumption.
    setoid_rewrite Mtimes_help; try assumption.
    - apply sum_n_morphism. hnf. intros.
      rewrite !Mtrans_help ; try assumption.
      rewrite M.mul_comm; auto.
Qed.

Theorem matrix_mul_assoc:
    forall {x y p q} (m1: Mat A x y) (m2: Mat A y p) (m3: Mat A p q),
      (m1 M* m2) M* m3 M= m1 M* (m2 M* m3).
Proof.
    red. intros.
    setoid_rewrite Mtimes_help; try assumption.
    replace (sum p (fun k : nat => (m1 M* m2)&[i, k] *e m3&[k, j])) with
            (sum p (fun k : nat => sum y (fun l : nat => m1&[i, l] *e m2&[l, k]) *e m3&[k, j])).
    symmetry. (* etransitivity.
(*     apply sum_n_morphism. red.
(*     intros. *)
(*     rewrite Mtimes_help. *) *)
    reflexivity. *)
(*     auto.
    auto. *)

(*       by (symmetry; etransitivity; (* setoid_rewrite Mtimes_help should do this *)
      [ apply sum_n_morphism; red; intros;
        rewrite Mtimes_help | ]; intuition reflexivity). *)

    replace (sum y (fun k : nat => m1&[i, k] *e (m2 M* m3)&[k, j])) with
            (sum y (fun k : nat => m1&[i, k] *e sum p (fun l : nat => m2&[k, l] *e m3&[l, j]))).
    symmetry; etransitivity.

    intuition reflexivity.
    
(*       by (symmetry; etransitivity; (* setoid_rewrite Mtimes_help should do this *)
      [ apply sum_n_morphism; red; intros;
        rewrite Mtimes_help | ]; intuition reflexivity). *)
    repeat setoid_rewrite sum_multiply_l.
    repeat setoid_rewrite sum_multiply_r.
    rewrite sum_swap.
    apply sum_morphism_Proper. red. intros.
    apply sum_morphism_Proper. red. intros.
    rewrite M.mul_assoc; auto.

    symmetry.
    apply sum_n_morphism; red; intros;
        rewrite Mtimes_help.
    intuition reflexivity; auto.
    auto.
    auto.

    symmetry.
    apply sum_n_morphism; red; intros;
        rewrite Mtimes_help.
    intuition reflexivity; auto.
    auto.
    auto.
(*     repeat setoid_rewrite sum_multiply_l.
    repeat setoid_rewrite sum_multiply_r.
    rewrite sum_swap.
    apply sum_morphism_Proper. red. intros.
    apply sum_morphism_Proper. red. intros. auto.

    apply sum_n_morphism; red; intros;
        rewrite Mtimes_help.
    intuition reflexivity.
    auto.
    auto. *)
Qed.


(* 
如果A、B是两个同阶可逆矩阵，则AB也可逆
 *)
Lemma AB_inversion:
    forall (MA MB MC MD: Mat A n n ), 
                                invertible MA -> invertible MB ->
                                MA M* MC M= MI -> MB M* MD M= MI -> 
                                invertible (MA M* MB).
Proof.
    intros.
    unfold invertible in H, H0.
    inversion H.
    inversion H0.
    
    unfold invertible.
    exists (x0 M* x).
    split.
    rewrite <- matrix_mul_assoc.
    rewrite matrix_mul_assoc.
    rewrite matrix_mul_assoc.
    rewrite <- matrix_mul_assoc with (m1:= MB) (m2:= x0) (m3:= x).
    inversion H4.
    rewrite H5.
    rewrite I_is_left_identity.
    inversion H3.
    assumption.

    
    rewrite <- matrix_mul_assoc.
    rewrite matrix_mul_assoc.
    rewrite matrix_mul_assoc.
    rewrite <- matrix_mul_assoc with (m1:= x) (m2:= MA) (m3:= MB).
    inversion H3.
    rewrite H6.
    rewrite I_is_left_identity.
    inversion H4.
    assumption.
Qed.
    

  (* 可逆交换 *)
Lemma AB_BA:
    forall MA MB, invertible MA -> MA M* MB M= MI -> MB M* MA M= MI. 
Proof.
    intros.
    unfold invertible in H.
    inversion H.
    inversion H1.
    rename x into B'.
    assert (B' M* (MA M* MB) M= B' M* MI).
    {
      setoid_rewrite H0.
      reflexivity.

(*    rewrite <-H2 in H0.
      rewrite Mtimes_mor.
      split. easy.

      setoid_rewrite H0. auto. *)
  
    }
    rewrite <- matrix_mul_assoc in H4.
    rewrite H3 in H4.
    rewrite I_is_left_identity in H4.
    rewrite I_is_right_identity in H4.
    rewrite H4.
    assumption.
Qed.

Lemma A_only_inversion:
    forall (MA MB MC: Mat A n n ), 
              invertible MA -> 
              MA M* MB M= MI -> 
              MA M* MC M= MI -> 
              MC M= MB.
Proof.
    intros.
    inversion H.
    inversion H2.
    assert (MI M* MB M= MB).
    {
      apply I_is_left_identity.
    }
    apply AB_BA in H1; auto.
    rewrite <-H1 in H5.
    rewrite matrix_mul_assoc in H5.
    rewrite H0 in H5.
    rewrite I_is_right_identity in H5.
    assumption.
Qed.

(* 
 1 2 1      1 0 0   1 2 1
-1-3 1  =>  1 1 0   0-1 2
-1-3 1      1 0 1 , 0-1 2

 1 2 1      1 0 0   1 2 1
-1-3 1  =>  1 1 0   0-1 2
 1 0 6     -1 0 1 , 0-2 5
 *)

(* 
前提必须是MA[i,i] = 1
x表示列数,从0开始,cur从n-1开始,MA存储最终化简的结果，输出对偶形式 *)
Fixpoint elem_change_down  (MA: Mat A n n ) (x: nat) (cur: nat) : Mat A n n * Mat A n n :=
    match cur with
    | O => (MI, MA)
    | S cur' =>
      let ee := row_add_to_row_n (n - cur) x (M.opp (Mget MA (n - cur) x)) in
      let (E, MT) := elem_change_down (ee M* MA) x cur' in
      (E M* ee, MT)
    end.

(* 
 1 2 1      
-1-3 1  =>  return 0
 1 0 6     
[(n - i)++, y] , i 
得到第一个非0 *)
Fixpoint get_first_none_zero (MA: Mat A n n) (i: nat) (y: nat) :=
    match i with
    | O => n
    | S i' =>
      if (M.eqdec (Mget MA (n - i) y) M.Zero) then
        get_first_none_zero MA i' y
      else
        n - i
    end.




(*

第一步,swap 
 0 1 0      -1-3 1    0 1 0
-1-3 1  =>   0 1 0    1 0 0
 1 0 6       1 0 6 ,  0 0 1
第二步,收个数字化简成1
-1-3 1       1 3-1   -1 0 0
 0 1 0  =>   0 1 0    0 1 0
 1 0 6       1 0 6 ,  0 0 1
第三步,化简成阶梯式
1 3-1        1 3-1    1 0 0
0 1 0   =>   0 1 0    0 1 0
1 0 6        0-3 7 , -1 0 1

所以这一阶段的最终结果是
 1 0 0   -1 0 0   0 1 0   0 1 0
 0 1 0  * 0 1 0 * 1 0 0 =-1 0 0
-1 0 1    0 0 1   0 0 1   1 0 1

1 3-1
0 1 0
0-3 7

随后，i--,进入下一个递归
第一步,swap 
1 3-1       1 3-1    1 0 0
0 1 0  =>   0 1 0    0 1 0
0-3 7       0-3 7 ,  0 0 1
第二步,收个数字化简成1
1 3-1       1 3-1    1 0 0
0 1 0  =>   0 1 0    0 1 0
0-3 7       0-3 7 ,  0 0 1
第三步,化简成阶梯式
1 3-1       1 3-1    1 0 0
0 1 0  =>   0 1 0    0 1 0
0-3 7       0 0 7 ,  0 3 1

所以这一阶段的最终结果是
1 0 0    1 0 0   1 0 0   1 0 0
0 1 0  * 0 1 0 * 0 1 0 = 0 1 0
0 3 1    0 0 1   0 0 1   0 3 1

1 3-1
0 1 0
0 0 7

随后，i--,进入下一个递归
第一步,swap 
1 3-1       1 3-1    1 0 0
0 1 0  =>   0 1 0    0 1 0
0 0 7       0 0 7 ,  0 0 1
第二步,收个数字化简成1
1 3-1       1 3-1    1 0 0
0 1 0  =>   0 1 0    0 1 0
0 0 7       0 0 1 ,  0 0 1/7
第三步,化简成阶梯式
1 3-1       1 3-1    1 0 0
0 1 0  =>   0 1 0    0 1 0
0 0 1       0 0 1 ,  0 0 1

所以这一阶段的最终结果是
1 0 0    1 0 0   1 0 0   1 0 0 
0 1 0  * 0 1 0 * 0 1 0 = 0 1 0
0 0 1    0 0 1/7 0 0 1   0 0 1/7

1 3-1
0 1 0
0 0 1

随后，i--,进入下一个递归
i = 0

return (MI, MA),即
1      1 3-1
  1    0 1 0
    1, 0 0 1

EA''存储最终结果
1 3-1
0 1 0
0 0 1
E'' 存储变换矩阵
1 0 0    1 0 0   1 0 0   0 1 0    0-1 0
0 1 0  * 0 1 0 * 0 1 0 *-1 0 0  = 1 0 0
0 0 1    0 0 1/7 0 3 1   1 0 1  3/7 1/7 1/7

i从n开始
*)

(* 
偏函数
通常可以将它描述为一个从a到“option B”的总函数，
约定当函数结果不存在时，值“None”是结果，
当函数应该定义为值y时，值是“Some y”
 *)
Fixpoint row_echelon_form (MA: Mat A n n) (i: nat) :=
    match i with
    | O => Some (MI, MA)
    | S i' =>
      let r := get_first_none_zero MA i (n - i) in
      if (r =? n) then
        None
      else
        let A0 := (swap_n (n - i) r) M* MA in                                (* 把当前0行和第一个非0行互换 *)
        let ee := (row_mul_n (n - i) (M.inv (Mget A0 (n - i) (n - i)))) in   (* 保证这一列第一个数字是1 *)
        let (E, MT) := elem_change_down (ee M* A0) (n - i) (i - 1) in          (* 下面元素全部与当前行相减，变成0 *)
        let ret := row_echelon_form MT i' in
        match ret with
        | None => None
        | Some (E', MT') => Some (E' M* E M* ee M* swap_n (n - i) r, MT')
        end
    end.


(*

第一步
1 3-1
0 1 0
0 0 1, 2, 2

第三行的-0倍加到第二行

     1 0 0 
ee = 0 1-0 
     0 0 1 

1 0 0   1 3-1
0 1-0 * 0 1 0
0 0 1   0 0 1, 2, 1


1 0 1
0 1 0
0 0 1, 


1 0 1   1 3-1
0 1 0 * 0 1 0
0 0 1   0 0 1, 2, 0

i = 0
return

1 0 0  1 3 0
0 1 0  0 1 0 
0 0 1, 0 0 1

i,x都从n-1开始
elem_change_up MA 2 2
elem_change_up MA 2 1
elem_change_up MA 2 0

作用是第x列，对角线以上元素全变成0
*)
Fixpoint elem_change_up (MA: Mat A n n) (x: nat) (i: nat) :=
    match i with
    | O => (MI, MA)
    | S i' =>
      let ee := row_add_to_row_n i' x (M.opp (Mget MA i' x)) in
      let (E, MT) := elem_change_up (ee M* MA) x i' in
      (E M* ee, MT)
    end.

(* 
1 3-1
0 1 0, 3
0 0 1

第一步，第三列向上化简
1 3-1     1 0 0   1 3-1
0 1 0 =>  0 1-0   0 1 0
0 0 1     0 0 1 , 0 0 1
第二步
1 3-1     1 0 1   1 3 0
0 1 0 =>  0 1 0   0 1 0
0 0 1     0 0 1 , 0 0 1

这阶段结果是
1 0 0   1 0 1   1 0 0   1 0 1
0 1 0 * 0 1 0 * 0 1-0 = 0 1 0
0 0 1   0 0 1   0 0 1   0 0 1

1 3 0
0 1 0
0 0 1

随后，i--,进入下一个递归

第一步，第二列向上化简
1 3 0     1-3 0   1 0 0
0 1 0 =>  0 1 0   0 1 0
0 0 1     0 0 1 , 0 0 1

这阶段结果是
1 0 0   1-3 0   1-3 0 
0 1 0 * 0 1 0 = 0 1 0
0 0 1   0 0 1   0 0 1

1 0 0
0 1 0
0 0 1
随后，i--,进入下一个递归

第一步，第一列向上化简
1 0 0     1 0 0   1 0 0
0 1 0 =>  0 1 0   0 1 0
0 0 1     0 0 1 , 0 0 1

随后，i--,进入下一个递归
i = 0

return (MI, MA),即
1      1 0 0
  1    0 1 0
    1, 0 0 1

 *)
Fixpoint fst_to_I (MA: Mat A n n) (i: nat) :=
    match i with
    | O => (MI, MA)
    | S i' =>
        let (E, MT) := elem_change_up (MA) i' i' in
        let (E', MT') := fst_to_I MT i' in
        (E' M* E, MT')
    end.

Definition Inversion (MA: Mat A n n) := 
    match row_echelon_form MA n with
    | None => None
    | Some (E, MT) => Some (fst (fst_to_I MT n) M* E)
    end.


Hint Rewrite @Mfill_help @Melement_op_help @single_val_map  @row_mul_map @row_add_to_row_map @swap_map: MMM.




Ltac elim_bool:=
  repeat match goal with
         | [ |- context [Nat.eqb ?x ?y]] 
             => let eq := fresh "eq" in destruct (x =? y) eqn: eq
         | [H: ?x =? ?y = false |- _] 
             => apply Nat.eqb_neq in H
         | [H: ?x =? ?y = true |- _] 
             => apply Nat.eqb_eq in H
         end.



(* 
 1 2 1      1 0 0   1 2 1
-1-3 1  =>  1 1 0   0-1 2
-1-3 1      1 0 1 , 0-1 2

 1 2 1      1 0 0   1 2 1
-1-3 1  =>  1 1 0   0-1 2
 1 0 6     -1 0 1 , 0-2 5
 *)
(* 
前提必须是MA[i,i] = 1
x表示列数,cur从n-1开始,MA存储最终化简的结果，输出对偶形式 *)

(*
验证
 1 0 0    1 2 1      1 2 1
 1 1 0 * -1-3 1  =>  0-1 2
-1 0 1    1 0 6      0-2 5
*)
Lemma elem_change_down_mult_eq :
    forall (MA : Mat A n n) (x cur : nat),
      x < n -> cur < n - x ->
      (fst (elem_change_down MA x cur) M* MA) M= snd (elem_change_down MA x cur).
Proof.
    intros.
    generalize dependent MA.
    induction cur.  (* 验证每行是否都成立*)
    - intros. simpl. apply I_is_identity.
    - assert (cur < n - x).
      {
        omega.
      }
      intros.
      eapply IHcur in H1.
      simpl.
      destruct (elem_change_down (row_add_to_row_n (n - S cur) x (M.opp (MA&[n - S cur, x])) M* MA) x cur) eqn: eq.
      simpl.
      rewrite eq in H1.
      simpl in H1.
      rewrite <- matrix_mul_assoc in H1.
      assumption.
Qed.

(*
!!!
第x列
第n-cur行
对角线元素都是1，阶梯矩阵的条件

阶梯矩阵继续化简过程中
前n-cur行的所有元素，是不会变化的

 1 2 1      1 2 1     1 2 1 保持不变
-1-3 1  ->  0-1 2 ,   x x x
 1 0 6      1 0 6     x x x

 1 2 1      1 2 1     1 2 1
 0-1 2  ->  0-1 2 ,   0-1 2 保持不变
 1 0 6      0-2 5     x x x

*)
Lemma elem_change_down_former_row_keep :
    forall (MA : Mat A n n) (x cur : nat),
      x < n -> cur < n - x -> Mget MA x x = e1 ->
      forall i j, i < n - cur -> j < n -> Mget (snd (elem_change_down MA x cur)) i j = Mget MA i j.
Proof.
    intros.
    generalize dependent MA.
    generalize dependent i.
    generalize dependent j.
    induction cur.
    - intros.
      simpl.
      auto.
    - intros.
      simpl.
      destruct (elem_change_down (row_add_to_row_n (n - S cur) x (M.opp (MA&[n - S cur, x])) M* MA) x cur) eqn: eq.
      simpl.
      assert (snd (elem_change_down (row_add_to_row_n (n - S cur) x (M.opp (MA&[n - S cur, x])) M* MA) x cur)&[i, j] = (row_add_to_row_n (n - S cur) x (M.opp (MA&[n - S cur, x])) M* MA)&[i, j]).
      {
        apply IHcur; auto; try omega.
        rewrite row_add_to_row_map; auto; try omega.
        destruct (x =? n - S cur) eqn: eq0; auto.
        apply Nat.eqb_eq in eq0; auto.

        rewrite <- eq0.
        rewrite H1.
        omega.
      }
      rewrite eq in H4.
      simpl in H4.
      rewrite H4.
      rewrite row_add_to_row_map; auto; try omega.
      destruct (i =? n - S cur) eqn: eq0; auto.
      apply Nat.eqb_eq in eq0; auto.
      rewrite <-eq0.
      omega.
Qed.

(* 
第x列
第n-cur行
对角线元素都是1，阶梯矩阵的条件

阶梯矩阵继续化简过程中
后n-cur行的所有元素，0

 1 2 1      1 2 1     1 2 1 保持不变
-1-3 1  ->  0-1 2 ,   x x x
 1 0 6      0 0 0     x x x

 1 2 1      1 2 1     1 2 1
 0-1 2  ->  0-1 2 ,   0-1 2 保持不变
 1 0 6      0 0 0     x x x

*)
Lemma elem_change_down_latter_row_keep :
    forall (MA : Mat A n n) (x cur : nat),
      x < n -> cur < n - x -> Mget MA x x = e1 ->
      forall y, y >= n - cur -> y < n -> Mget (snd (elem_change_down MA x cur)) y x = e0.
Proof.
    intros.
    generalize dependent MA.
    generalize dependent y.
    induction cur. 
    - intros.
      simpl.
      omega.  (*不成立 *)
    - intros.
      destruct (beq_nat y (n - S cur)) eqn: eq.

      + simpl.
        destruct (elem_change_down (row_add_to_row_n (n - S cur) x (M.opp (MA&[n - S cur, x])) M* MA) x cur) eqn: eq2. 
        simpl.
        assert (m0&[y, x] = (row_add_to_row_n (n - S cur) x (M.opp (MA&[n - S cur, x])) M* MA)&[y, x]).
        {
          assert (m0 = snd (elem_change_down (row_add_to_row_n (n - S cur) x (M.opp (MA&[n - S cur, x])) M* MA) x cur)) by (rewrite eq2; auto).
          rewrite H4.
          apply elem_change_down_former_row_keep; auto; try omega.
          rewrite row_add_to_row_map; auto; try omega.
          elim_bool. rewrite <-eq0. omega.
          auto.
          apply Nat.eqb_eq in eq; omega.
        }
        rewrite H4.
        rewrite row_add_to_row_map; auto; try omega.
        elim_bool; auto; try omega.
        rewrite <- eq0.
        rewrite H1.
        rewrite M.mul_one_r.
        rewrite <- M.sub_zero_l.
        rewrite M.add_sub_assoc.
        rewrite M.add_comm.
        rewrite M.sub_self3. auto.
        inversion eq.
      + simpl.
        destruct (elem_change_down (row_add_to_row_n (n - S cur) x (M.opp (MA&[n - S cur, x])) M* MA) x cur) eqn: eq2.
        simpl.
        assert (m0 = snd (elem_change_down (row_add_to_row_n (n - S cur) x (M.opp (MA&[n - S cur, x])) M* MA) x cur)) by (rewrite eq2; auto).
        rewrite H4.
        apply IHcur; auto; try omega.
        apply Nat.eqb_neq in eq; omega.
        rewrite row_add_to_row_map; auto; try omega.
        destruct (beq_nat x (n - S cur)) eqn: eq0.
        apply Nat.eqb_neq in eq; try omega.
        apply Nat.eqb_eq in eq0; try omega.
        auto.
Qed.

(*
左下角0
i>j保证在对角线以下
j<x保证在x列之前
*)
  Definition lower_left_zeros (MA: Mat A n n) (x: nat) :=
    forall i j,
      i < n -> j < n -> j < x -> i > j -> Mget MA i j = e0.

(*
第x列,x=1,
第n-cur行, cur=1,0, 第1,2行
i>j, j<x, MA[i,j] = e0

1 3-1     1 3-1   1 x x
0 1 0 ->  0 1 0 , 0 x x 这部分是相等的
0-3 7     0 0 7   0 x x

 *)

Lemma elem_change_down_keep_lower_left_zeros:
    forall (MA : Mat A n n) (x cur : nat),
      x < n -> cur < n - x -> Mget MA x x = e1 -> lower_left_zeros MA x -> 
      lower_left_zeros (snd (elem_change_down MA x cur)) x.
Proof.
    intros.
    generalize dependent MA.
    induction cur.
    - intros.
      simpl.
      assumption.
    - intros.
      simpl.
      destruct (elem_change_down (row_add_to_row_n (n - S cur) x (M.opp (MA&[n - S cur, x])) M* MA)  x cur) eqn: eq.
      simpl.
      unfold lower_left_zeros in *.
      intros.
      destruct (i <? (n - S cur)) eqn: eq2.
      + 
        replace (m0) with (snd (elem_change_down (row_add_to_row_n (n - S cur) x (M.opp (MA&[n - S cur, x])) M* MA) x cur)) by (rewrite eq; auto).
        assert (e0 = (row_add_to_row_n (n - S cur) x (M.opp (MA&[n - S cur, x])) M* MA)&[i, j]).
        {
          rewrite row_add_to_row_map; auto; try omega. apply Nat.ltb_lt in eq2.
          destruct (i =? (n - S cur)) eqn: eq0.
          apply Nat.eqb_eq in eq0; omega.
          apply Nat.eqb_neq in eq0.
          rewrite H2; auto.
        }
        rewrite H7. 
        apply elem_change_down_former_row_keep; auto; try omega.
        rewrite row_add_to_row_map; auto; try omega.
        apply Nat.ltb_lt in eq2.
        elim_bool; auto; try omega.
        apply Nat.ltb_lt in eq2.
        omega.

      + destruct (i =? (n - S cur)) eqn: eq3; elim_bool; auto; try omega.
        * subst.
          replace (m0) with (snd (elem_change_down (row_add_to_row_n (n - S cur) x (M.opp (MA&[n - S cur, x])) M* MA) x cur)) by (rewrite eq; auto).
          assert (e0 = (row_add_to_row_n (n - S cur) x (M.opp (MA&[n - S cur, x])) M* MA)&[n - S cur, j]).
          {
            rewrite row_add_to_row_map; auto; try omega.
            elim_bool; auto; try omega.
            rewrite H2; auto.
            replace (MA&[x, j]) with e0 by (rewrite H2; auto).
            rewrite M.mul_zero_r.
            rewrite M.add_zero_r; auto.
            
          }
          rewrite H7.
          apply elem_change_down_former_row_keep; auto; try omega.
          rewrite row_add_to_row_map; auto; try omega.
          elim_bool; auto; try omega.
        * replace (m0) with (snd (elem_change_down (row_add_to_row_n (n - S cur) x (M.opp (MA&[n - S cur, x])) M* MA) x cur)) by (rewrite eq; auto).
          apply IHcur; auto; try omega.
          --- rewrite row_add_to_row_map; auto; try omega.
              elim_bool; auto; try omega.
          --- intros.
              rewrite row_add_to_row_map; auto; try omega.
              elim_bool; auto; try omega.
              rewrite H2; auto.
              replace (MA&[x, j0]) with e0 by (rewrite H2; auto).
              rewrite M.mul_zero_r.
            rewrite M.add_zero_r; auto.
Qed.

(*
条件1:
x=2,第2列之前列数，对角线下全是0
1
0 1
0 0 1
0 0 x x
0 0 x x x
条件2:
x=2,第2列对角线下元素，变成0
1
0 1
0 0 1
0 0 0 x
0 0 0 x x
结论:
x+1=3,第3列之前列数，对角线下全是0

如果lower_left_zeros MA x成立
如果第x列下面也全部是0，
那么lower_left_zeros MA x+1成立
*)

Lemma lower_left_zeros_extend:
    forall (MA : Mat A n n) (x : nat),
      x < n -> Mget MA x x = e1 -> lower_left_zeros MA x -> 
      lower_left_zeros (snd (elem_change_down MA x (n - x - 1))) (x + 1).
Proof.
    intros.
    unfold lower_left_zeros.
    intros.
    destruct (j =? x) eqn: eq. elim_bool.
    - rewrite eq. apply elem_change_down_latter_row_keep; auto; omega. 
    - elim_bool. apply elem_change_down_keep_lower_left_zeros; auto; omega.
Qed.

(*
(* 
 1 2 1      
-1-3 1  =>  return 0
 1 0 6     
[(n - i)++, y] , i 
得到第一个非0 *)

i从n开始
get_first_none_zero MA i (n - i)

MA[i, n-i]
 *)
Lemma get_first_none_zero_at_least:
    forall (MA : Mat A n n) (i j : nat), get_first_none_zero MA i j >= n - i.
Proof.
    intros.
    induction i.
    - simpl. omega.
    - simpl.
      destruct (M.eqdec (MA&[n - S i, j]) e0); omega. 
Qed.

Lemma get_first_none_zero_at_most:
    forall (MA : Mat A n n) (i j : nat), get_first_none_zero MA i j <= n.
Proof.
    intros.
    induction i.
    - simpl. omega.
    - simpl.
      destruct (M.eqdec (MA&[n - S i, j]) e0); omega. 
Qed.

(*   Lemma  get_first_none_zero_help:
    forall (A0 : Mat A n n) (i j : nat), 
      get_first_none_zero A0 i j < n -> A0&[get_first_none_zero A0 i j, j] <> e0.
  Proof.
    intros.
    induction i.
    - simpl. simpl in H. omega.
    - simpl; mytauto.
      simpl in H.
      mytauto.
  Qed. *)


(*   Lemma row_echelon_form_mult_eq:
    forall (MA : Mat A n n) (i : nat) (E EA : Mat A n n),
      i <= n -> fst (row_echelon_form MA i) M* MA M= snd (row_echelon_form MA i). *)

Lemma row_echelon_form_mult_eq:
    forall (MA : Mat A n n) (i : nat) (E EA : Mat A n n),
      i <= n -> row_echelon_form MA i = Some (E, EA) -> 
      E M* MA M= EA.
Proof.
    intros.
    generalize dependent MA.
    generalize dependent E.
    generalize dependent EA.
    induction i; intros.
    - simpl in H0. inversion H0. subst.
      apply I_is_left_identity.
    - unfold row_echelon_form in H0.
      fold row_echelon_form  in H0.

     destruct 
          (elem_change_down (row_mul_n (n - S i)
              (M.inv ((swap_n (n - S i) (get_first_none_zero MA (S i) (n - S i)) M* MA)&[n - S i, n - S i])) M*
                (swap_n (n - S i) (get_first_none_zero MA (S i) (n - S i)) M* MA)) (n - S i) 
                  (S i - 1)) eqn: Heqp. 
     destruct (get_first_none_zero MA (S i) (n - S i) =? n) eqn: Heqb.
     inversion H0.

     destruct (row_echelon_form m0 i) eqn: Heqo.
     destruct (p) eqn: ?.


      subst.
      remember (swap_n (n - S i) (get_first_none_zero MA (S i) (n - S i)) M* MA) as A1.
      remember (row_mul_n (n - S i) (M.inv (A1&[n - S i, n - S i])) M* A1) as A2. 
      inversion H0.
      replace ((if M.eqdec (MA&[n - S i, n - S i]) e0
                  then get_first_none_zero MA i (n - S i)
                  else n - S i)) 
          with (get_first_none_zero MA (S i) (n - S i)) by (auto).
        rewrite matrix_mul_assoc.
        rewrite <- HeqA1.
        assert (m M* A2 M= m0).
        {
          replace m with (fst (elem_change_down A2 (n - S i) (S i - 1))) by (rewrite Heqp; auto).
          replace m0 with (snd (elem_change_down A2 (n - S i) (S i - 1))) by (rewrite Heqp; auto).
          
          apply elem_change_down_mult_eq; omega.
        }
      destruct (row_echelon_form m0 i) eqn: eq3.
      * destruct p.
        apply IHi in eq3; try omega. 
        
        rewrite matrix_mul_assoc.
        rewrite matrix_mul_assoc.
        rewrite <- HeqA2. 
        rewrite H1.
        rewrite <- H3.
        inversion Heqo.
        rewrite <- H5.
        rewrite <- H6.
        assumption.
      * inversion Heqo.
      * inversion H0.
Qed.

(* ******************************************************************************************** *)

(* 
(row_mul_n x c) M* MA = c * MA

(*
1 0 0
0 c 0 * MA
0 0 1
*)
 *)
(*   Lemma row_mul_map_n:
    forall (x : nat) (c : A) (i j : nat), forall MA: Mat A n n, 
        i < n -> j < n -> x < n ->
        Mget ((row_mul_n x c) M* MA) i j = if (i =? x) then c *e Mget MA i j else Mget MA i j. 
  Proof.
    intros; elim_bool; intros; unfold row_mul_n; unfold row_mul; rewrite Mtimes_help; auto; simpl.
    - apply sum_single with (x := i); auto.
      + intros. rewrite Mfill_help; auto.
        elim_bool; auto; simpl; subst; try tauto; try omega. rewrite M.mul_zero_l; auto.
      + rewrite Mfill_help; auto.
        elim_bool; auto; simpl; subst; try tauto.
    - apply sum_single with (x := i); auto.
      + intros. rewrite Mfill_help; auto.
        elim_bool; auto; simpl; subst; try tauto. rewrite M.mul_zero_l; auto.
      + rewrite Mfill_help; auto.
        elim_bool; auto; simpl; subst; try tauto. rewrite M.mul_one_l; auto.
  Qed. *)


(* Lemma row_echelon_form_help_keep :
    forall (X : Mat A n n) (i : nat) (E EA : Mat A n n),
      i <= n -> row_echelon_form X i = Some (E, EA) -> 
      forall x y, x < n - i -> y < n -> Mget EA x y = Mget X x y. 
  Proof.
    intros X i.
    generalize dependent X.
    induction i; intros.
    - simpl in H0.
      inversion H0; subst.
      reflexivity.
    - simpl in H0; mytauto.
      +
        remember (swap_n (n - S i) (get_first_none_zero X i (n - S i)) M* X) as A0.
        remember (row_mul_n (n - S i) (M.inv (A0&[n - S i, n - S i])) M* A0) as A1; try rewrite <- HeqA0 in *; try rewrite <- HeqA1 in *. 
        inversion H0.
        rewrite <- H5.
        rewrite IHi with (X := m0) (EA := m2) (E := m1); auto; try omega.
        replace (m0) with (snd (elem_change_down A1 (n - S i) (i - 0))) by (rewrite Heqp; auto).
        rewrite elem_change_down_former_row_keep; auto; try omega.
        *
          apply transitivity with (y0 := A0&[x, y]).
          --- rewrite HeqA1.
              rewrite row_mul_map; mytauto;
              assert (get_first_none_zero X i (n - S i) <= n) by apply  get_first_none_zero_at_most;
              omega. 
          --- rewrite HeqA0.
              rewrite swap_map; mytauto.
              assert (get_first_none_zero X i (n - S i) >= n - i) by apply get_first_none_zero_at_least.
              omega.
              assert (get_first_none_zero X i (n - S i) <= n) by apply get_first_none_zero_at_most.
              omega.
        * rewrite HeqA1.
          rewrite row_mul_map; mytauto.
          rewrite M.inv_self; auto.
          assert (get_first_none_zero X i (n - S i) <= n) by apply  get_first_none_zero_at_most;
              omega. 
       + remember (swap_n (n - S i) (n - S i) M* X) as A0; remember (row_mul_n (n - S i) (M.inv (A0&[n - S i, n - S i])) M* A0) as A1; try rewrite <- HeqA0 in *; try rewrite <- HeqA1. 
        inversion H0. 
        rewrite <- H5. 
        rewrite IHi with (X := m0) (EA := m2) (E := m1); auto; try omega.
        replace (m0) with (snd (elem_change_down A1 (n - S i) (i - 0))) by (rewrite Heqp; auto).
        rewrite elem_change_down_former_row_keep; auto; try omega.
        *
          apply transitivity with (y0 := A0&[x, y]).
          --- rewrite HeqA1.
              rewrite row_mul_map; mytauto.
          --- rewrite HeqA0.
              rewrite swap_map; mytauto.
        * rewrite HeqA1.
          rewrite row_mul_map; mytauto.
          rewrite M.inv_self; auto.
  Qed. *)
(* 
1 x x
x 1 x
x x 1

L行以上的对角线全是1
 *)
Definition diagonal_ones (MA: Mat A n n) (L: nat) :=
    forall i,
      i < n -> i < L -> Mget MA i i = e1.

(* 
行阶梯矩阵

X = EA, E是单位矩阵

n行以上对角线全是1
 *)
Lemma row_echelon_form_to_diag_ones :
    forall (X : Mat A n n) (i : nat) (E EA : Mat A n n),
      i <= n -> diagonal_ones X (n - i) -> row_echelon_form X i = Some (E, EA) -> 
      diagonal_ones EA n.
Proof.
    intros.
    generalize dependent X.
    generalize dependent E.
    generalize dependent EA.
    induction i; intros.
    - simpl in H1.
      inversion H1.
      subst.
      replace n with (n - 0) by omega.
      assumption.
    - unfold diagonal_ones.
      intros.
      unfold row_echelon_form in H1.
      fold row_echelon_form in *.

      destruct 
          (elem_change_down 
            (row_mul_n (n - S i)
              (M.inv ((swap_n (n - S i) (get_first_none_zero X (S i) (n - S i)) M* X)&[n - S i, n - S i])) 
               M*
              (swap_n (n - S i) (get_first_none_zero X (S i) (n - S i)) M* X)) 
          (n - S i)
          (S i - 1)) eqn: Heqp.
     destruct (get_first_none_zero X (S i) (n - S i) =? n) eqn: Heqb.
     inversion H1.

     destruct (row_echelon_form m0 i) eqn: Heqo.
     destruct (p) eqn: ?.

     remember (swap_n (n - S i) (get_first_none_zero X (S i) (n - S i)) M* X) as A0.
     remember (row_mul_n (n - S i) (M.inv (A0&[n - S i, n - S i])) M* A0) as A1.
     try rewrite <- HeqA0 in *; try rewrite <- HeqA1 in *.


      (* 
      要应用IHi，先构造一个diagonal_ones X (n - i)
       *)
      assert (diagonal_ones m0 (n - i)).
      {
        unfold diagonal_ones. intros.
        replace (m0) with (snd (elem_change_down A1 (n - S i) (S i - 1))) by (rewrite Heqp; auto). 
        rewrite elem_change_down_former_row_keep; auto; try omega.
        + rewrite HeqA1.
          rewrite row_mul_map; elim_bool; auto; try omega.
          * rewrite <-eq. rewrite M.inv_self; auto.

          * rewrite HeqA0.
            assert (get_first_none_zero X (S i) (n - S i) <= n) by apply get_first_none_zero_at_most.
            assert (get_first_none_zero X (S i) (n - S i) >= n - S i) by apply get_first_none_zero_at_least.
      
            rewrite swap_map; destruct (i1 =? n - S i) eqn: eq0;
            destruct (i1 =? get_first_none_zero X (S i) (n - S i)) eqn: eq1; progress elim_bool;
            progress subst; try omega.

            apply H0. omega. omega.
        + rewrite HeqA1. rewrite row_mul_map; try omega. elim_bool. rewrite M.inv_self; auto.
          omega.
      }
      apply IHi with (E:=m1) (EA:=m2) in H4 ; auto.
      inversion H1. 
      rewrite <- H7.
      apply H4; auto.
      omega.
      inversion H1.
Qed.



(* 
行阶梯矩阵

n-i列之前，左下角全是0，
X = EA, E是单位矩阵
n行以上左下角全是0
 *)
Lemma row_echelon_form_to_lower_left_zeros:
    forall (X : Mat A n n) (i : nat) (E EA : Mat A n n),
      i <= n -> lower_left_zeros X (n - i) -> row_echelon_form X i = Some (E, EA) -> 
      lower_left_zeros EA n.
Proof.
    intros X i.
    generalize dependent X.
    induction i; intros.
    - replace n with (n - 0) by omega.
      simpl in H1.
      inversion H1.
      rewrite <- H4. 
      assumption.
    - unfold row_echelon_form in H1. 
      fold row_echelon_form in *.
      destruct 
          (elem_change_down 
            (row_mul_n (n - S i)
              (M.inv ((swap_n (n - S i) (get_first_none_zero X (S i) (n - S i)) M* X)&[n - S i, n - S i])) 
               M*
              (swap_n (n - S i) (get_first_none_zero X (S i) (n - S i)) M* X)) 
          (n - S i)
          (S i - 1)) eqn: Heqp.
     destruct (get_first_none_zero X (S i) (n - S i) =? n) eqn: Heqb.
     inversion H1.

     destruct (row_echelon_form m0 i) eqn: Heqo.
     destruct (p) eqn: ?.
      remember (swap_n (n - S i) (get_first_none_zero X (S i) (n - S i)) M* X) as A0.
      remember (row_mul_n (n - S i) (M.inv (A0&[n - S i, n - S i])) M* A0) as A1; try rewrite <- HeqA0 in *; try rewrite <- HeqA1 in *.
(* 
      需要利用IHi，先构建lower_left_zeros X (n - i)
     *)
      assert (lower_left_zeros m0 (n - i)).
      {
        unfold lower_left_zeros.
        intros. 
        assert (get_first_none_zero X (S i) (n - S i) <= n) by apply get_first_none_zero_at_most.
        assert (get_first_none_zero X (S i) (n - S i) >= n - S i) by apply get_first_none_zero_at_least.
      
        replace (m0) with (snd (elem_change_down A1 (n - S i) (S i - 1))) by (rewrite Heqp; auto).
        replace (S i - 1) with (n - (n - S i) - 1) by omega. 
        apply lower_left_zeros_extend with (x := n - S i); try omega;
        progress subst; progress autorewrite with MMM; destruct (n - S i =? n - S i) eqn: eq;
        elim_bool; try omega; auto.

        + rewrite M.inv_self; auto.
        + unfold lower_left_zeros; intros.
          rewrite row_mul_map; auto; try omega.
          
          elim_bool.
          progress autorewrite with MMM; auto; try omega.
          elim_bool; try omega.
          subst.
          
          * replace ( X&[get_first_none_zero X (S i) (n - S i), j0]) with e0 by (rewrite <- H0; auto; omega).
            rewrite M.mul_zero_r; auto.
          * autorewrite with MMM; auto; try omega.
            elim_bool.
            omega. 
            rewrite <- H0; auto; omega.
            auto.
      }
      apply IHi with (X := m0) (E := m1); auto; try omega.
      inversion H1. 
      rewrite <- H5.
      assumption.
      inversion H1.
Qed.

Definition upper_triangle (MA: Mat A n n) := 
    lower_left_zeros MA n.


(* 归一化上三角形，即阶梯矩阵 *)
Definition normalized_upper_triangle (MA: Mat A n n) := 
    diagonal_ones MA n /\ lower_left_zeros MA n.


Theorem row_echelon_form_correct:
    forall A E EA : Mat A n n,
      row_echelon_form A n = Some (E, EA) -> 
      E M* A M= EA /\ normalized_upper_triangle EA.
Proof.
    intros.
    split.
    - eapply row_echelon_form_mult_eq; eauto.
    - unfold normalized_upper_triangle.
      split.
      + unfold diagonal_ones. eapply row_echelon_form_to_diag_ones. auto.
        unfold diagonal_ones. intros. omega. eauto.
      + eapply row_echelon_form_to_lower_left_zeros. auto.
        unfold lower_left_zeros. intros. omega. eauto.
Qed.


(* 
****************************************************************************************************
 *)

(* 
第x列， 第i行
1 3-1     1 0 1   1 3 0
0 1 0 =>  0 1 0   0 1 0
0 0 1     0 0 1 , 0 0 1

 1 0 1   1 3 0    1 3-1
 0 1 0 * 0 1 0 =  0 1 0
 0 0 1   0 0 1    0 0 1


fst (fun MA) * MA = snd (fun MA)
 *)

Lemma elem_change_up_mult_eq :
    forall (MA : Mat A n n) (x i : nat),
      x < n -> i <= x ->
      (fst (elem_change_up MA x i) M* MA) M= snd (elem_change_up MA x i).
Proof.
    intros.
    generalize dependent MA. 
    induction i.
    - intros. simpl. apply I_is_identity.
    - assert (i <= x) by omega. intros.
      eapply IHi in H1.
      simpl.
      destruct (elem_change_up (row_add_to_row_n i x (M.opp (MA&[i, x])) M* MA) x i) eqn: eq.
      simpl.
      rewrite eq in H1.
      simpl in H1.
      rewrite <- matrix_mul_assoc in H1.
      assumption.
Qed.
(* 
upper_right_zeros MA 4

倒数(4-1)列都是0

x x 0 0 0
x x 0 0 0
x x x 0 0
x x x x 0
x x x x x

L必须大于等于1
n-L <= j < n,
0   <= i < j,对角线以上
 *)
Definition upper_right_zeros (MA: Mat A n n) (L: nat) :=
    forall i j,
      i < n -> j < n -> j >= n - L -> i < j -> Mget MA i j = e0.


Definition lower_triangle (MA: Mat A n n) := 
    upper_right_zeros MA n.
(* 
!!!
上三角矩阵
i'行， x列
i' < x

上三角元素，经过行相加变化，还是上三角

 *)
Lemma row_add_to_row_keep_upper_triangle:
    forall (MA : Mat A n n) (x i' : nat),
      x < n -> i' < x -> normalized_upper_triangle MA -> 
      normalized_upper_triangle ((row_add_to_row_n i' x (M.opp (Mget MA i' x))) M* MA).
Proof.
    intros.
    unfold normalized_upper_triangle.
    inversion H1.
    unfold diagonal_ones in H2. 
    unfold lower_left_zeros in H3. 
    split.
    + unfold diagonal_ones; intros.
      rewrite row_add_to_row_map; auto; try omega.
      elim_bool; auto; try omega.
      replace (MA&[x, i]) with e0 by (rewrite H3; auto; omega).
      replace (MA&[i, i]) with e1 by (rewrite H2; auto; omega).
      rewrite M.mul_zero_r.
      rewrite M.add_zero_r; auto.
    + unfold lower_left_zeros; intros. 
      rewrite row_add_to_row_map; auto; try omega.
      elim_bool; auto; try omega.
      replace (MA&[i, j]) with e0 by (rewrite H3; auto; omega).
      replace (MA&[x, j]) with e0 by (rewrite H3; auto; omega).
      rewrite M.mul_zero_r.
      rewrite M.add_zero_r; auto.
Qed.


(* 
!!!
上三角矩阵，elem_change_up之后，还是上三角
 *)
Lemma elem_change_up_keep_upper_triangle :
    forall (MA : Mat A n n) (x i : nat),
      x < n -> i <= x -> normalized_upper_triangle MA
           -> normalized_upper_triangle (snd (elem_change_up MA x i)). 
Proof.
    intros.
    generalize dependent MA.
    generalize dependent x.
    induction i; intros.
    - simpl. assumption.
    - simpl.
      destruct (elem_change_up (row_add_to_row_n i x (M.opp (MA&[i, x])) M* MA) x i) eqn: eq.
      replace (snd (m M* row_add_to_row_n i x (M.opp (MA&[i, x])), m0)) with (snd (elem_change_up (row_add_to_row_n i x (M.opp (MA&[i, x])) M* MA) x i)) by (rewrite eq; auto).
      apply IHi; auto; try omega.
      apply row_add_to_row_keep_upper_triangle; auto.
Qed.

(* 
上三角矩阵
elem_change_up MA x i作用是第x列，0~i-1行元素变0，
经过elem_change_up MA x i之后的第i~n-1列，元素不变

利用行相加变换，i行不变
(row_add_to_row_n i x (M.opp (MA&[i, x])) M* MA)&[i', j] == MA&[i', j]

i‘>=i
MA[i', j]元素与原先一样， i=3时
1-3 1     1-3 0
0 1 0     0 1 0
0 0 1   , 0 0 1
第2行所有元素保持不变

i <= i' <n
     j  <n
 *)
Lemma elem_change_up_lower_rows_keep :
    forall (MA : Mat A n n) (x i : nat),
      x < n -> i <= x -> normalized_upper_triangle MA ->
      forall i' j, i' < n -> i' >= i -> j < n -> Mget (snd (elem_change_up MA x i)) i' j = Mget MA i' j.
Proof.
    intros.
    generalize dependent MA.
    generalize dependent i.
    generalize dependent j.
    generalize dependent i'.
    generalize dependent x. 
    induction i.
    - intros.
      simpl.
      reflexivity.
    - intros.
      simpl.
      destruct (elem_change_up (row_add_to_row_n i x (M.opp (MA&[i, x])) M* MA) x i) eqn: eq.
      simpl.
      assert (snd (elem_change_up (row_add_to_row_n i x (M.opp (MA&[i, x])) M* MA) x i)&[i', j] = (row_add_to_row_n i x (M.opp (MA&[i, x])) M* MA)&[i', j]).
      {
        apply IHi; auto; try omega.
        apply row_add_to_row_keep_upper_triangle; auto; try omega.
      }
      rewrite eq in H5. simpl in H5.
      simpl.
      rewrite H5.
      rewrite row_add_to_row_map; auto; try omega.
      elim_bool; auto.
      omega.
Qed.

(* 
上三角矩阵
elem_change_up MA x i作用是第x列，0~i-1行元素变0，
上面元素还是0
 x < n
i0 < i

利用行相加变换，i行不变
(row_add_to_row_n i x (M.opp (MA&[i, x])) M* MA)&[i', j] == MA&[i', j]
 *)

Lemma elem_change_up_upper_rows_to_0 :
    forall (MA : Mat A n n) (x i : nat),
      x < n -> i <= x -> normalized_upper_triangle MA ->
      (forall i0, i0 < i -> (snd (elem_change_up MA x i))&[i0, x] = e0).
Proof.
    intros.
    generalize dependent MA.
    generalize dependent x.
    generalize dependent i.
    generalize dependent i0. 
    induction i; intros.
    - simpl. omega.
    - simpl.
      inversion H1.
      unfold diagonal_ones in H3.
      unfold lower_left_zeros in H4. 
      destruct (elem_change_up (row_add_to_row_n i x (M.opp (MA&[i, x])) M* MA) x i) eqn: eq.
      simpl.
      replace (m0) with (snd (elem_change_up (row_add_to_row_n i x (M.opp (MA&[i, x])) M* MA) x i)) by (rewrite eq; auto).
      destruct (i0 =? i) eqn: eq2; elim_bool; auto.      
      (*       
      i0 == i
       *)
      (* ???  *)

      + (* rewrite IHi; auto; try omega. inversion eq2.  *)
        rewrite elem_change_up_lower_rows_keep; auto; try omega.
        * rewrite row_add_to_row_map; auto; try omega.
          elim_bool; auto; try omega.
          replace (MA&[x, x]) with e1 by (rewrite H3; auto; omega).
          rewrite eq0.
          rewrite M.mul_one_r.
          rewrite <-M.sub_zero_l.
          rewrite M.add_sub_assoc.
          rewrite M.add_comm.
          rewrite M.sub_self3; auto.
        * apply row_add_to_row_keep_upper_triangle; auto; omega.
      (*       
      i0 <> i
       *)
      + rewrite IHi; auto; try omega.
        apply row_add_to_row_keep_upper_triangle; auto.
Qed.

(*
i <= x <n
L < n - x

upper_right_zeros MA L
得到
upper_right_zeros (snd (elem_change_up MA x i)) L

x x 0 0 0
x x 0 0 0
x x x 0 0
x x x x 0
x x x x x
    ^
第x列在这，

x x 0 0 0
x x 0 0 0
x x x 0 0
x x x x 0
x x x x x
      ^ ^

L < n - x,L控制后两列

x x 0 0 0
x x 0 0 0
x x x 0 0
x x x x 0
x x x x x
^ ^

i <= x,i控制前两列
 *)
Lemma elem_change_up_keep_upper_right_zeros:
    forall (MA : Mat A n n) (x i L : nat) ,
      x < n -> i <= x -> L < n - x -> normalized_upper_triangle MA -> upper_right_zeros MA L ->  
      upper_right_zeros (snd (elem_change_up MA x i)) L.
Proof.
    intros.
    generalize dependent MA.
    generalize dependent x.
    generalize dependent L.
    induction i; intros; try assumption.
    simpl.
    destruct (elem_change_up (row_add_to_row_n i x (M.opp (MA&[i, x])) M* MA) x i) eqn: eq.
    (* 
    用的是同一个m0
     *)
    simpl.
    replace (m0) with (snd (elem_change_up (row_add_to_row_n i x (M.opp (MA&[i, x])) M* MA) x i)) by (rewrite eq; auto).
    apply IHi; auto; try omega.
    - apply row_add_to_row_keep_upper_triangle; auto; omega.
    - unfold upper_right_zeros.
      (* 
      i0 < n ->
      j < n -> 
      j >= n - L -> 
      i0 < j
       *)
      intros.
      rewrite row_add_to_row_map; auto; try omega.
      elim_bool; auto; try omega.
      rewrite eq0.
      (* 
      i == j

      L < n - x
      n - L <= j < n
      i < j   上三角
      i <= x < n
      x < j   上三角
       *)
      replace (MA&[i, j]) with e0 by (rewrite H3; auto; omega).
      replace (MA&[x, j]) with e0 by (rewrite H3; auto; omega).
      rewrite M.mul_zero_r.
      rewrite M.add_zero_r; auto.
Qed.

(* 
upper_right_zeros MA (n - x - 1)

x x x 0 0
x x x 0 0
x x x 0 0
x x x x 0
x x x x x

elem_change_up MA x x

x x 0 x x
x x 0 x x
x x x x x
x x x x x
x x x x x
    ^
得到
upper_right_zeros MA (n - x)

x x 0 0 0
x x 0 0 0
x x x 0 0
x x x x 0
x x x x x


x+1 <= j < n,
0   <= i < j,对角线以上
 *)
Lemma upper_right_zeros_entend:
    forall (MA : Mat A n n) (x : nat),
      x < n -> normalized_upper_triangle MA -> upper_right_zeros MA (n - x - 1) ->  
      upper_right_zeros (snd (elem_change_up MA x x)) (n - x).
Proof.
    intros.
    unfold upper_right_zeros.
    intros.
    destruct (j =? x) eqn: eq; elim_bool; auto.
    (* 
    j == x
     *)
    - rewrite eq. apply elem_change_up_upper_rows_to_0; auto; omega.
    (* 
    j > x
     *)
    - rewrite elem_change_up_keep_upper_right_zeros with (L := n - x - 1); auto; omega.
Qed.

(* 
fst (fun MA) * MA = snd (fun MA)
 *)
Lemma fst_to_I_mult_eq:
    forall (MA : Mat A n n) (i : nat),
      i <= n ->
      fst (fst_to_I MA i) M* MA M= snd (fst_to_I MA i).
Proof.
    intros.
    generalize dependent MA.
    induction i.
    - intros; simpl.
      apply I_is_identity.
    - intros.
      simpl.
      destruct (elem_change_up MA i i) eqn: eq1.
      destruct (fst_to_I m0 i) eqn: eq2.
      simpl.
      rewrite matrix_mul_assoc.
      replace (m) with (fst (elem_change_up MA i i)) by (rewrite eq1; auto). 
      rewrite elem_change_up_mult_eq; auto; try omega.
      replace (m1) with (fst (fst_to_I m0 i)) by (rewrite eq2; auto).
      replace (m2) with (snd (fst_to_I m0 i)) by (rewrite eq2; auto).
      replace (m0) with (snd (elem_change_up MA i i)) by (rewrite eq1; auto).
      apply IHi; auto; try omega. 
Qed.

(* 
上三角 MA
fst_to_I MA n之后，
还是上三角
 *)
Lemma fst_to_I_keep_upper_triangle:
    forall (MA : Mat A n n) (i : nat),
      i <= n -> normalized_upper_triangle MA -> 
      normalized_upper_triangle (snd (fst_to_I MA i)).
Proof.
    intros.
    generalize dependent MA.
    induction i.
    - intros. simpl. assumption.
    - intros; simpl.
      destruct (elem_change_up MA i i) eqn: eq1.
      destruct (fst_to_I m0 i) eqn: eq2.
      simpl.
      replace (m2) with (snd (fst_to_I m0 i)) by (rewrite eq2; auto).
      apply IHi; auto; try omega.
      replace (m0) with (snd (elem_change_up MA i i)) by (rewrite eq1; auto).
      apply elem_change_up_keep_upper_triangle; auto; try omega.
Qed.

(* 
上三角 MA
n-i右上是0
那么snd (fst_to_I MA i)之后，
  n右上是0
 *)
Lemma fst_to_I_to_upper_right_zeros:
    forall (MA : Mat A n n) (i : nat),
      i <= n -> normalized_upper_triangle MA -> upper_right_zeros MA (n - i) -> 
      upper_right_zeros (snd (fst_to_I MA i)) n.
Proof.
    intros.
    generalize dependent MA.
    induction i.
    - intros; simpl. replace (n) with (n - 0) by omega. assumption.
    - intros; simpl.
      destruct (elem_change_up MA i i) eqn: eq1.
      destruct (fst_to_I m0 i) eqn: eq2.
      simpl.
      replace (m2) with (snd (fst_to_I m0 i)) by (rewrite eq2; auto).
      apply IHi; auto; try omega.
      + replace (m0) with (snd (elem_change_up MA i i)) by (rewrite eq1; auto).
        apply elem_change_up_keep_upper_triangle; auto; try omega.
      + replace (m0) with (snd (elem_change_up MA i i)) by (rewrite eq1; auto).
        apply upper_right_zeros_entend; auto; try omega.
        replace (n - i - 1) with (n - S i) by omega.
        assumption.
Qed.

(* 
fst * MA = snd 相乘相等
snd = MI
 *)
Theorem fst_to_I_correct:
    forall (MA : Mat A n n),
      normalized_upper_triangle MA ->
      fst (fst_to_I MA n) M* MA M= snd (fst_to_I MA n) /\ snd (fst_to_I MA n) M= MI.
Proof.
    intros.
    split.
    - apply fst_to_I_mult_eq. auto.
      (* 
      主要是第二部分
       *)
    - unfold "M=".
      intros.
      (* 分成上下三角考虑 *)
      destruct (j <=? i) eqn: eq; elim_bool; auto; try omega.
      
      + destruct (j =? i) eqn: eq2; elim_bool; auto; try omega.
      (*
      i==j
       *)
        * subst.
          unfold MI. unfold I. 
          rewrite Mfill_help; elim_bool; auto; try omega.
          apply fst_to_I_keep_upper_triangle. auto. auto. auto. auto.
      (*
      i<>j
       *)
        * unfold MI. unfold I. 
          rewrite Mfill_help; elim_bool; auto; try omega. apply Nat.leb_le in eq. subst.
          apply fst_to_I_keep_upper_triangle; auto; omega.
      (*
      j>i
       *)
      + unfold MI. unfold I. 
        rewrite Mfill_help; elim_bool; auto; apply Nat.leb_gt in eq; try omega.
        apply fst_to_I_to_upper_right_zeros; auto; try omega.
        unfold upper_right_zeros. intros.
        omega.
Qed.


Theorem Inversion_correct:
    forall (MA E : Mat A n n),
      Inversion MA = Some E -> E M* MA M= MI.
Proof.
    intros.
    unfold Inversion in H.
    destruct (row_echelon_form MA n) eqn: eq; try inversion H.
    clear H1.
    destruct p.
    inversion H. clear H.
    assert (m M* MA M= m0 /\ normalized_upper_triangle m0) by (apply row_echelon_form_correct; assumption).
    inversion H. clear H.
    rewrite matrix_mul_assoc.
    rewrite H0.
    assert ((snd (fst_to_I m0 n)) M= MI) by (apply fst_to_I_correct; auto).
    rewrite <- H.
    apply fst_to_I_mult_eq. auto.
Qed.


Theorem Inversion_is_invertible:
    forall (MA E : Mat A n n),
      Inversion MA = Some E -> invertible MA.
Proof.
    intros.
    apply Inversion_correct in H.
    unfold invertible.
    exists E.
    split.
    - apply l_inv_r_inv in H. assumption.
    - assumption.
Qed.

Theorem Inversion_inv_is_invertible:
    forall (MA E : Mat A n n),
      Inversion MA = Some E -> invertible E.
Proof.
    intros.
    apply Inversion_correct in H.
    unfold invertible.
    exists MA.
    split.
    - assumption.
    - apply l_inv_r_inv in H. assumption.
Qed.

Theorem ABC_equal_r:
    forall (MA MB MC: Mat A n n),
      MA M= MB ->
      MA M* MC M= MB M* MC.
Proof.
      intros.
      rewrite <-H.
      apply Meq_id.
Qed.

Theorem ABC_equal_l:
    forall (MA MB MC: Mat A n n),
      MA M= MB ->
      MC M* MA M= MC M* MB.
Proof.
      intros.
      rewrite <-H.
      apply Meq_id.
Qed.

Theorem ABC_equal:
    forall (MA MB MC: Mat A n n),
      MA M= MB ->
      MC M* MA M= MC M* MB /\ MA M* MC M= MB M* MC.
Proof.
      intros.
      split.
      apply ABC_equal_l; auto.
      apply ABC_equal_r; auto.
Qed.


Theorem matrix_cancellation:
    forall (MA MB MC A_inv B_inv C_inv: Mat A n n),
      Inversion MA = Some A_inv ->
      Inversion MB = Some B_inv ->
      Inversion MC = Some C_inv ->
      MA M* MC M= MB M* MC ->
      MA M= MB.
Proof.
    intros.
    apply Inversion_correct in H.
    apply Inversion_correct in H0.
    inversion H1.
    apply Inversion_correct in H1.
    apply AB_BA in H1.
    apply ABC_equal_r with (MA:=(MA M* MC)) (MB:=(MB M* MC)) (MC:= C_inv) in H2.
    rewrite matrix_mul_assoc with (m1:=MA) (m2:=MC) (m3:=C_inv) in H2.
    rewrite matrix_mul_assoc with (m1:=MB) (m2:=MC) (m3:=C_inv) in H2.
    rewrite H1 in H2.
    rewrite !I_is_right_identity in H2. auto.
    apply Inversion_inv_is_invertible in H4.
    auto.
Qed.

    

  
Theorem AB_inv_help:
    forall (MA MB A_inv B_inv AB_inv: Mat A n n),
      Inversion MA = Some A_inv ->
      Inversion MB = Some B_inv ->
      B_inv M* A_inv M* MA M* MB M= MI.
Proof.
    intros.
    apply Inversion_correct in H.
    apply Inversion_correct in H0.
    rewrite matrix_mul_assoc with (m1:=B_inv) (m2:=A_inv) (m3:=MA).
    rewrite H.
    rewrite I_is_right_identity.
    assumption.
Qed.




Theorem Inversion_trans_trans:
    forall (MA A_inv : Mat A n n),
      Inversion MA = Some A_inv ->
      Mtrans( Mtrans (A_inv ))=== A_inv.
Proof.
    intros.
    apply Inversion_correct in H.
    unfold Mtrans,trans,Meq,M_eq.
    induction A_inv.
    simpl.
    apply trans_same;auto.
Qed.

Theorem Inversion_add:
    forall (MA MB A_inv B_inv : Mat A n n),
      Inversion MA = Some A_inv ->
      Inversion MB = Some B_inv ->
      
      A_inv M+ B_inv === B_inv M+ A_inv.
Proof.
    intros.
    apply matrix_comm.
    intros.
    rewrite M.add_comm; auto.
Qed.

Theorem Inversion_add_assoc:
    forall (MA MB MC A_inv B_inv C_inv: Mat A n n),
      Inversion MA = Some A_inv ->
      Inversion MB = Some B_inv ->
      Inversion MC = Some C_inv ->
      A_inv M+ B_inv M+ C_inv  === A_inv M+ (B_inv M+ C_inv).
Proof.
    intros.
    apply matrix_assoc.
    intros.
    rewrite M.add_assoc; auto.
Qed.

Theorem Inversion_self_correct:
    forall (MA A_inv : Mat A n n),
      Inversion MA = Some A_inv ->
      A_inv M* MA M= MI.
Proof.
    intros.
    apply Inversion_correct in H.
    assumption.
Qed.

Theorem Inversion_self_correct2:
    forall (MA A_inv : Mat A n n),
      Inversion MA = Some A_inv ->
      MA M* A_inv M= MI.
Proof.
    intros.
    inversion H.
    inversion H.
    apply Inversion_inv_is_invertible in H1.
    apply Inversion_correct in H.
    apply AB_BA; auto.
Qed.




(* 
AT(A-1)T =(A-1A)T=ET=E.
 *)

Theorem Inversion_trans_mult_inv_correct:
  forall (MA A_inv A_inv_inv: Mat A n n),
      Inversion MA = Some A_inv ->
      Mtrans MA M* Mtrans A_inv M= MI.
 Proof.
    intros.
    rewrite <-matrix_trans_mul.
    assert (A_inv M* MA M= MI).
    {
      apply Inversion_correct in H.
      assumption.
    }
    unfold MI.
    rewrite <-I_trans_I.
    apply Mtrans_mor.
    auto.
Qed.

Theorem Inversion_inv_inv_correct:
    forall (MA A_inv A_inv_inv: Mat A n n),
      Inversion MA = Some A_inv ->
      Inversion A_inv = Some A_inv_inv ->
      MA M= A_inv_inv.
Proof.
    intros.
    apply Inversion_correct in H0.
(*     apply AB_BA in H1; auto.
 *) 
    rewrite <-I_is_right_identity with (MA:=A_inv_inv).
    rewrite <-Inversion_self_correct with (MA:=MA) (A_inv:=A_inv); auto.
    rewrite <-matrix_mul_assoc.
    rewrite H0.
    rewrite I_is_left_identity.
    apply Meq_id.
Qed.

Lemma row_mul_invertible:
    forall i x,
      i < n -> x <> M.Zero -> invertible (row_mul_n i x).
Proof.
    intros.
    unfold invertible.
    exists (row_mul_n i (M.inv x)).
    split.
    - unfold Meq.
      intros.
      rewrite row_mul_map; auto; try omega.
      destruct (i0 =? i) eqn: eq; elim_bool.
      + unfold row_mul_n. unfold Matrix.matrix_row_mul. rewrite Mfill_help; elim_bool; try omega.
        * unfold MI; unfold Matrix.I; elim_bool; try omega. autorewrite with MMM; try omega. elim_bool; try omega. rewrite M.mul_comm; apply M.inv_self.
        * unfold MI; unfold Matrix.I; elim_bool; try omega. autorewrite with MMM; try omega. elim_bool; try omega.  rewrite M.mul_zero_r; auto.
      + unfold row_mul_n; unfold Matrix.matrix_row_mul; elim_bool; try omega.
        * unfold MI; unfold Matrix.I; elim_bool; try omega. autorewrite with MMM; try omega. elim_bool; try omega; auto.
    - unfold Meq; intros.
      rewrite row_mul_map; elim_bool; try omega. subst.
      + unfold row_mul_n; unfold Matrix.matrix_row_mul; unfold MI; unfold Matrix.I; elim_bool; try omega. autorewrite with MMM; try omega. elim_bool; try omega; auto.
        apply M.inv_self. rewrite M.mul_zero_r; auto.
      + unfold row_mul_n; unfold Matrix.matrix_row_mul; unfold MI; unfold Matrix.I; elim_bool; try omega. autorewrite with MMM; try omega. elim_bool; try omega; auto.
Qed.


(*
c 0 0   1 1 1   c c c
0 c 0 * 1 1 1 = c c c
0 0 c   1 1 1   c c c
*)
Lemma row_mul_map_c:
  forall (c : A) (i j : nat), forall MA: Mat A n n, 
      i < n -> j < n ->
      Mget ((@Mfill n n (fun i j => (if beq_nat i j then c else M.Zero))) M* MA) i j =  c *e Mget MA i j.
Proof.
      intros.
      elim_bool.
      rewrite Mtimes_help; auto.
      apply sum_single with (x := i); auto.
      + intros.
        rewrite Mfill_help; auto.
        elim_bool; auto; simpl; subst. omega. 
        rewrite M.mul_zero_l; auto.
      + rewrite Mfill_help; auto.
        elim_bool; auto; simpl; subst; try tauto.
Qed.


(* 如果A可逆，数k≠0，则kA也可逆，且(kA)–1=A–1
 *)

Theorem row_mul_c_invertible:
    forall i c,
      i < n -> c <> M.Zero -> invertible (@Mfill n n (fun i j => (if beq_nat i j then c else M.Zero))).
Proof.
    intros.
    unfold invertible.
    exists (@Mfill n n (fun i j => (if beq_nat i j then (M.inv c) else M.Zero))).
    split.
    - unfold Meq.
      intros.
      rewrite row_mul_map_c; auto; try omega.
      rewrite Mfill_help; elim_bool; try omega.
        * unfold MI; unfold Matrix.I; elim_bool; try omega. autorewrite with MMM; try omega. elim_bool; try omega; auto.
          rewrite M.mul_comm; apply M.inv_self.
        * unfold MI; unfold Matrix.I; elim_bool; try omega. autorewrite with MMM; try omega. elim_bool; try omega; auto.
          rewrite M.mul_zero_r; auto.
    - unfold Meq.
      intros.
      rewrite row_mul_map_c; auto; try omega.
      rewrite Mfill_help; elim_bool; try omega.
        * unfold MI; unfold Matrix.I; elim_bool; try omega. autorewrite with MMM; try omega. elim_bool; try omega; auto.
          apply M.inv_self.
        * unfold MI; unfold Matrix.I; elim_bool; try omega. autorewrite with MMM; try omega. elim_bool; try omega; auto.
          rewrite M.mul_zero_r; auto.
Qed.


End MatrixInversion.

End Matrix.

