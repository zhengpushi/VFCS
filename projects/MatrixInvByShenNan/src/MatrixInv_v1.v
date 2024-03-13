(*
   Remark   :
   1. 使用 FieldMatrixTheoryDR，也就是基于记录的矩阵实现方式。

   Changelog:
   1. v1 
      (1) 使用 DecidableFieldMatrixTheoryDR 代替 EqDecidableFieldMatrixTheoryDR。
          目的是，使用 setoid 代替 eq，以便支持 Q 类型。
      (2) 简化代码，统一命名，以便理解。
 *)
From CoqMatrix Require Import DepRec.Matrix.
From CoqMatrix Require Import MatrixTheoryDR.

Set Implicit Arguments.

(** * unsorted *)
Section unsorted.

  Fixpoint reduce {A} (n: nat) (f: A -> nat -> A) (zero: A) : A :=
    match n with
    | O => zero
    | S n' => f (reduce n' f zero) n'
    end.
  Section test.
    Variable A : Type.
    Variable f : A -> nat -> A.
    Variable a : A.
    (* Compute reduce 3 f a. *)
  (*
        reduce 3 f a
      = f (reduce 2 f a) 2
      = f (f (reduce 1 f a) 1) 2
      = f (f (f (reduce 0 f a) 0) 1) 2
      = f (f (f a 0) 1) 2
   *)
  End test.

  (* Coq.Classes.Morphisms.pointwise_relation 逐点关系

     pointwise_relation =
     fun (A B : Type) (R : relation B) (f g : A -> B) => forall a : A, R (f a) (g a)
     : forall A B : Type, relation B -> relation (A -> B) *)

  (*  若序列 x,y : A -> nat -> A 相等，则 reduce 保持相等关系。即，
    forall (n : nat) (x y : A -> nat -> A),
      pointwise_relation A (pointwise_relation nat eq) x y ->
      forall x0 y0 : A, x0 = y0 -> reduce n x x0 = reduce n y y0 *)
  Add Parametric Morphism (A : Type) (n : nat) : (@reduce A n)
      with signature (
        pointwise_relation A (pointwise_relation nat eq) ==> eq ==> eq)
        as reduce_morphism.
  Proof.
    intros r1 r2 pt_r zero. induction n; intros; auto.
    simpl. unfold pointwise_relation in *. rewrite pt_r. f_equal. auto.
  Qed.
  
  (* 两个序列的前 n 项逐点满足 R 关系 *)
  Definition pointwise_relation_n {A} (n: nat) (R: relation A) : relation (nat -> A) :=
    fun (f g : nat -> A) => forall (a: nat), a < n -> R (f a) (g a).

  (* 若前 S n 项逐点满足 R 关系，则前 n 项也逐点满足 R 关系 *)
  Lemma pointwise_relation_n_decr {A}:
    forall (n : nat) (m1 m2 : nat -> A) (R : relation A),
      pointwise_relation_n (S n) R m1 m2 -> pointwise_relation_n n R m1 m2.
  Proof. unfold pointwise_relation_n. intuition. Qed.

  (* 若序列 x,y : A -> nat -> A 的前n项相等，且初值相等，则 reduce 保持相等关系。即，
     forall (n : nat) (x y : A -> nat -> A),
       pointwise_relation A (pointwise_relation_n n eq) x y -> 
       forall x0 y0 : A, x0 = y0 -> reduce n x x0 = reduce n y y0 *)
  Add Parametric Morphism (A : Type) (n : nat) : (@reduce A n)
      with signature (
        pointwise_relation A (pointwise_relation_n n eq) ==> eq ==> eq)
        as reduce_n_morphism.
  Proof.
    intros r1 r2 ptr zero. induction n; intros; simpl; auto.
    unfold pointwise_relation, pointwise_relation_n in *.
    rewrite ptr; auto. rewrite IHn; auto.
  Qed.
  
End unsorted.

(** * Inverse Matrix  *)
Module MatrixInv (B : BaseType) (E : EqDecidableFieldElementType B).
  Include (DecidableFieldMatrixTheoryDR E).

  (* ******************************************************************* *)
  (** ** Theory for matrix element *)
  
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.

  (* 由于 Field 声明默认使用 Aeq，而此处使用特殊的 eq，所以要补充 eq 版本的 Field 声明，
     以便使用 ring, field 等策略 *)
  Lemma Field_thy: field_theory 0 1 Aadd Amul Asub Aopp Adiv Ainv eq.
  Proof.
    constructor; intros; try easy.
    apply Ring_thy. apply Aone_neq_Azero. rewrite field_mulInvL; auto.
  Qed.
  Add Field Field_thy_inst : Field_thy.
  
  (* /x * x = 1。原本 field_mulInvL 要求 x 非零，这里忽略了该条件。
     注意，该条件也许会导致某个隐藏的缺陷，需要仔细检查使用了该公理之处。*)
  Axiom inv_self : forall x, (/ x * x)%A = Aone.

  
  (* ******************************************************************* *)
  (** ** Theory for sequence over A *)

  (* 0 + f 0 + f 1 + ... + f (k-1) *)
  Notation sum k f := (reduce k (fun acc x => acc + f x)%A 0).

  Section test.
    Variable f : nat -> A.
    (* Compute sum 3 f. *)
    (* = (0 + f 0 + f 1 + f 2)%A *)
  End test.

  (* 若序列 x, y : nat -> A 相等，则 sum 保持相等，即：
     pointwise_relation nat eq x y -> sum k x = sum k y *)
  Add Parametric Morphism k : (fun f => sum k f)
      with signature (pointwise_relation nat (@eq A) ==> @eq A) as sum_morphism. 
  Proof.
    intros. apply reduce_morphism; auto.
    unfold pointwise_relation in *. intros. rewrite H. auto.
  Qed.

  (* 若序列 x, y : nat -> A 前n项相等，则 sum 保持相等，即：
     pointwise_relation_n k eq x y -> sum k x = sum k y *)
  Add Parametric Morphism k : (fun f => sum k f)
      with signature (pointwise_relation_n k (@eq A) ==> @eq A) as sum_n_morphism.
  Proof.
    intros. apply reduce_n_morphism; auto.
    unfold pointwise_relation, pointwise_relation_n in *; auto.
    intros. rewrite H; auto.
  Qed.

  (* sum (f1(x) + f2(x)) = sum f1(x) + sum f2(x) *)
  Lemma sum_add : forall (n : nat) (f1 f2 : nat -> A),
      (sum n (fun x => f1 x + f2 x) = sum n f1 + sum n f2)%A.
  Proof. induction n; simpl; intros. ring. rewrite IHn. ring. Qed.

  (* a * sum f(x) = sum a*f1(x) + a*f2(x) *)
  Lemma sum_cmul_l : forall (a : A) (n : nat) (f : nat -> A),
      (a * sum n f)%A = sum n (fun x => a * f x).
  Proof. induction n; simpl; intros. ring. rewrite <- IHn. ring. Qed.

  (* sum f(x) * a = sum f1(x) *a + f2(x) *a *)
  Lemma sum_cmul_r : forall (a : A) (n : nat) (f : nat -> A),
      (sum n f * a)%A = sum n (fun x => f x * a).
  Proof. induction n; simpl; intros. ring. rewrite <- IHn. ring. Qed.

  (* sum n f = 0 （要求 f 是“常函数 0”） *)
  Lemma sum_e0 : forall n, (sum n (fun k => 0)) = 0.
  Proof. induction n; simpl; auto. rewrite IHn. ring. Qed.

  (* sum n f  = 0 (只要 f 的形为是“常函数0”） *)
  Lemma sum_e0' : forall n (f : nat -> A),
      (forall i, i < n -> f i = 0) -> (sum n (fun k => f k)) = 0.
  Proof. induction n; simpl; intros; auto. rewrite H, IHn; auto. ring. Qed.

  (* f = g => sum n f = sum n g *)
  Lemma sum_eq : forall n (f g : nat -> A),
      (forall i, i < n -> f i = g i) -> sum n f = sum n g.
  Proof. intros. induction n; simpl; intros; auto. rewrite <- IHn, H; auto. Qed.

  (* 除了f(x)其他 f(i)都为0, sum n f = f(x) *)
  Lemma sum_single :
    forall (n : nat) (f : nat -> A) (x : nat) (y : A),
      x < n -> 
      (forall i, i < n -> i <> x -> f(i) = 0) -> 
      y = f x -> 
      (sum n (fun k => f k)) = y.
  Proof.
    intros. induction n; simpl. lia.
    bdestruct (x =? n).
    - subst. rewrite sum_e0'. ring. intros. apply H0; lia.
    - assert (x < n). lia.
      apply IHn in H3. rewrite H3. rewrite H0; auto. ring. auto.
  Qed.

  (* ∑n∑m f(i,j) = ∑m∑n f(i,j) *)
  Lemma sum_swap :
    forall (m n : nat) (f : nat -> nat -> A),
      sum n (fun j => sum m (fun i => f i j)) =
        sum m (fun i => sum n (fun j => f i j)).
  Proof.
    induction m. simpl; intros.
    - rewrite (sum_e0 n). auto.
    - intros. simpl. rewrite !sum_add. rewrite IHm. auto.
  Qed.

  
  (* ******************************************************************* *)
  (** ** Theory for matrix *)

  (* (m1\T)[i,j] = m1[j,i] *)
  Axiom Mtrans_help : 
    forall (m n: nat) (m1: mat m n),
    forall i j,
      i < m -> j < n ->
      mnth (m1\T) j i = mnth m1 i j.

  (* (m1 + m2)[i,j] = op m1[i,j] m2[i,j] *)
  Axiom Madd_help : forall (m n: nat) (m1: mat m n) (m2: mat m n) (op: A -> A -> A),
    forall i j,
      i < m -> j < n ->
      mnth (m1 + m2) i j = Aadd (mnth m1 i j) (mnth m2 i j).

  (* (m1 * m2)[i,j] = ∑(k,0,n) m1[i,k] * m2[k,j] *)
  Axiom Mtimes_help : forall(m n p: nat) (m1: mat m n) (m2: mat n p),
    forall i j,
      i < m -> j < p ->
      mnth (m1 * m2) i j = 
        reduce n (fun (acc : A) (x : nat) => (acc + (mnth m1 i x) * (mnth m2 x j))%A) 0.

  (** Generate a matrix from a function *)
  Notation f2m m n f := (@f2m A m n f).

  (* (f2m f)[i,j] = f i j *)
  Axiom f2m_help : forall (m n: nat) (f: nat -> nat -> A),
    forall i j,
      i < m -> j < n ->
      mnth (f2m m n f) i j = f i j.

  (* mat1\T = mat1 *)
  Axiom mtrans_mat1 : forall {n}, (mat1 n)\T = mat1 n.
  
  (* 取出第(i,j)个元素。*)
  Notation "m &[ i , j ]" :=
    (mnth m i j) (at level 20, format "m &[ i ,  j ]") : mat_scope.

  (* 原本 meq 是列表相等，新的 mnth 是逐点相等 *)
  Definition Meq {m n} (m1: mat m n) (m2 : mat m n) :=
    forall i j, i < m -> j < n -> mnth m1 i j = mnth m2 i j.
  Infix "===" := Meq (at level 70) : mat_scope.

  Lemma Meq_refl {m n}: reflexive (mat m n) (Meq).
  Proof. hnf; intros; hnf in *; intros; auto. Qed.

  Lemma Meq_sym {m n}: symmetric (mat m n) (Meq).
  Proof. hnf; intros; hnf in *; intros; auto. rewrite H; auto. Qed.

  Lemma Meq_trans {m n}: transitive (mat m n) (Meq).
  Proof. hnf; intros; hnf in *; intros; auto. rewrite H; auto. Qed.

  (* Meq 是等价关系 *)
  Global Add Parametric Relation {m n}: (mat m n) (Meq)
         reflexivity proved by Meq_refl
         symmetry proved by Meq_sym
         transitivity proved by Meq_trans                      
         as Meq_id.

  (* meq m1 m2 -> Meq m1 m2 *)
  Lemma meq2Meq : forall {m n} (m1 m2 : mat m n), m1 == m2 -> m1 === m2.
  Proof. intros. rewrite meq_iff_mnth in H. auto. Qed.

  (* Meq m1 m2 -> meq m1 m2 *)
  Lemma Meq2meq : forall {m n} (m1 m2 : mat m n), m1 === m2 -> m1 == m2.
  Proof. intros. apply meq_iff_mnth; intros. hnf in *. auto. Qed.


  (* mmul保持Meq *)
  Global Add Parametric Morphism m n p: (mmul) with
         signature (Meq (m:=m)(n:=n)) ==>
                     (Meq (m:=n)(n:=p)) ==>
                     (Meq (m:=m)(n:=p)) 
           as Mtimes_mor.
  Proof.
    intros. hnf in *; intros. rewrite !Mtimes_help; auto.
    apply sum_n_morphism. hnf; intros. rewrite H, H0; auto.
  Qed.

  (* mtrans保持Meq *)
  Global Add Parametric Morphism m n: (mtrans) with
         signature (Meq (m:=m)(n:=n)) ==> (Meq) as Mtrans_mor. 
  Proof. intros. hnf in *; intros. rewrite !Mtrans_help; auto. Qed.
  
  (* (m1 + m2) * m3 = m1 * m3 + m2 * m3 *)
  Lemma Mmul_madd_distr_l:
    forall {x y p} (m1: mat x y) (m2: mat x y) (m3: mat y p),
      (m1 + m2) * m3 === m1 * m3 + m2 * m3.
  Proof.
    red. intros. rewrite Mtimes_help; auto.
    replace (reduce y (
                 fun (acc : A) (x0 : nat) =>
                   acc + (m1 + m2)%mat&[i, x0] * m3&[x0, j])%A 0)
      with (reduce y (
                fun (acc : A) (x0 : nat) =>
                  acc + (m1&[i, x0] * m3&[x0, j] + m2&[i, x0] * m3&[x0, j]))%A 0).
    - rewrite !Madd_help; auto. rewrite !Mtimes_help; auto.
      apply sum_add.
    - apply sum_n_morphism. hnf. intros.
      rewrite Madd_help; auto. field.
  Qed.

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

    (* ************************************************** *)
    (** *** 单位矩阵 *)
    Definition I := @f2m n n (fun i j => (if Nat.eqb i j then 1 else 0)).

    (* I 等于 mat1 *)
    Axiom I_eq_mat1 : I === mat1 n.
    
    (* I * A = A *)
    Lemma mmul_I_l: forall MA: smat n, I * MA === MA.
    Proof.
      intros. unfold I. unfold Meq; intros. rewrite Mtimes_help; auto.
      rewrite sum_single with (x := i) (y := MA&[i,j]); auto.
      + intros. rewrite f2m_help; auto.
        assert (i <> i0). auto.
        apply <- Nat.eqb_neq in H3. rewrite H3. ring.
      + rewrite f2m_help; auto. rewrite Nat.eqb_refl. ring.
    Qed.

    (* A * I = A *)
    Lemma mmul_I_r: forall MA: smat n, MA * I === MA.
    Proof.
      intros. unfold I. unfold Meq; intros. rewrite Mtimes_help; auto.
      rewrite sum_single with (x := j) (y := MA&[i,j]); auto.
      + intros. rewrite f2m_help; auto.
        apply <- Nat.eqb_neq in H2. rewrite H2. ring.
      + rewrite f2m_help; auto. rewrite Nat.eqb_refl. ring.
    Qed.

    (* I \T = I *)
    Lemma mtrans_I: I\T === I.
    Proof.
      intros. unfold I. unfold Meq; intros. rewrite Mtrans_help; auto.
      rewrite !f2m_help; auto.
      bdestruct (j =? i); bdestruct (i =? j); subst;  easy.
    Qed.
    
    (* ************************************************** *)
    (** *** 仅指定一个元素的矩阵，其余为零 *)
    
    (* 
0 0 0
0 0 0
0 c 0
     *)
    (* 在 (x,y) 的元素是 c，其余是0 *)
    Definition MsingleVal (x y: nat) (c: A) :=
      @f2m n n (fun i j => (if ((Nat.eqb i x) && (Nat.eqb j y))%bool then c else 0)).

    (*
0 0 0   x x x    0  0  0
0 0 0 * x x x =  0  0  0
0 0 c   x x x   cx cx cx
     *)
    (* x,y处值为c *)
    Lemma mnth_MsingleVal:
      forall (x y : nat) (c : A) (i j : nat), forall MA: smat n, 
        i < n -> j < n -> x < n -> y < n ->
        mnth ((MsingleVal x y c) * MA) i j =
          if (i =? x) then (c * mnth MA y j)%A else 0. 
    Proof.
      intros. unfold MsingleVal. rewrite Mtimes_help; auto.
      bdestruct (i =? x).
      - apply sum_single with (x := y); auto.
        + intros. rewrite f2m_help; auto.
          bdestruct (i =? x); bdestruct (i0 =? y); simpl; subst; try easy; ring.
        + rewrite f2m_help; auto.
          bdestruct (i =? x); bdestruct (y =? y); simpl; subst; try easy; ring.
      - apply sum_e0'.
        intros. rewrite f2m_help; auto.
        bdestruct (i =? x); bdestruct (i0 =? y); simpl; subst; try easy; ring.
    Qed.

    (* ************************************************** *)
    (** *** 某行乘以k倍 *)
    (*
1 0 0
0 c 0
0 0 1
     *)

    (* 第 (x,x) 元素是 c，其余是单位阵 *)
    Definition MrowK (x: nat) (c: A) :=
      @f2m n n (fun i j => (if Nat.eqb i j then
                              (if Nat.eqb i x then c else 1) else 0)).
    
    (*
1 0 0   x x x   x x x
0 c 0 * x x x = c c c
0 0 1   x x x   x x x
     *)
    Lemma mnth_MrowK:
      forall (x : nat) (c : A) (i j : nat), forall MA: smat n, 
        i < n -> j < n -> x < n ->
        mnth ((MrowK x c) * MA) i j =
          if (i =? x) then (c * mnth MA i j)%A else mnth MA i j. 
    Proof.
      intros. unfold MrowK. rewrite Mtimes_help; auto.
      bdestruct (i =? x).
      - apply sum_single with (x := i); auto.
        + intros. rewrite f2m_help; auto.
          bdestruct (i =? i0); bdestruct (i =? x); simpl; subst; try easy; ring.
        + rewrite f2m_help; auto.
          bdestruct (i =? i); bdestruct (i =? x); simpl; subst; try easy; ring.
      - apply sum_single with (x := i); auto.
        + intros. rewrite f2m_help; auto.
          bdestruct (i =? i0); bdestruct (i =? x); simpl; subst; try easy; ring.
        + rewrite f2m_help; auto.
          bdestruct (i =? i); bdestruct (i =? x); simpl; subst; try easy; ring.
    Qed.

    (* ************************************************** *)
    (** *** 某行乘以k倍加到另一行 *)
    (* 
1 0 0
0 1 0
0 c 1
     *)

    (* 第 x 行的 c 倍加到第 y 行。单位阵 + 第 (x,y) 元素是 c 的矩阵 *)
    Definition MrowAdd (x y: nat) (c: A) := I + (MsingleVal x y c). 

    (* 
1 0 0   x x x   x    x    x
0 1 0 * x x x = x    x    x
0 c 1   x x x  x+cx x+cx x+cx
     *)
    Lemma mnth_MrowAdd:
      forall (x y : nat) (c : A) (i j : nat), forall MA: smat n, 
        i < n -> j < n -> x < n -> y < n ->
        mnth ((MrowAdd x y c) * MA) i j = 
          (if i =? x then (mnth MA i j + c * mnth MA y j)%A else mnth MA i j). 
    Proof.
      intros. unfold MrowAdd.
      rewrite Mmul_madd_distr_l; auto. rewrite !Madd_help; auto.
      bdestruct (i =? x); subst.
      - f_equal.
        + assert (I * MA === MA) by apply mmul_I_l. rewrite H3; auto.
        + rewrite mnth_MsingleVal; auto. bdestruct (x =? x); auto. easy.
      - replace ((MsingleVal x y c * MA)&[i, j]) with 0.
        + assert (I * MA === MA) by apply mmul_I_l. rewrite H4; auto. ring.
        + rewrite mnth_MsingleVal; auto. bdestruct (i =? x); auto. easy.
    Qed.

    (* ************************************************** *)
    (** *** 两行互换 *)
    (*
1 0 0  -1 0 0   0 0 0   0 0 0   0 1 0    0 1 0
0 1 0 + 0 0 0 + 0-1 0 + 1 0 0 + 0 0 0  = 1 0 0
0 0 1   0 0 0   0 0 0   0 0 0   0 0 0    0 0 1
     *)

    (* 第 x, y 两行互换 *)
    Definition MrowSwap (x y: nat) :=
      I
      + (MsingleVal x x (-(1))%A)
      + (MsingleVal y y (-(1))%A)
      + (MsingleVal x y 1)
      + (MsingleVal y x 1).
    
    (* 
0 1 0   1 1 1   2 2 2
1 0 0 * 2 2 2 = 1 1 1
0 0 1   3 3 3   3 3 3
     *)
    Lemma swap_map:
      forall (x y i j : nat), forall MA: smat n, 
        i < n -> j < n -> x < n -> y < n ->
        mnth ((MrowSwap x y) * MA) i j =
          (if i =? x then mnth MA y j else
             if i =? y then mnth MA x j else mnth MA i j). 
    Proof.
      Proof.
        intros.
        unfold MrowSwap.
        repeat (try rewrite Mmul_madd_distr_l; auto;
                try rewrite Madd_help; auto;
                try rewrite mnth_MsingleVal; auto).
        rewrite mmul_I_l; auto.
        bdestruct (i =? x); bdestruct (i =? y); subst; try ring.
      Qed.
      
  End SpecialMatrices.

  (* ******************************************************************* *)
  (** ** Theory for inverse matrix *)
  Section MatrixInversion.
    Variable n:nat.

    Notation I := (@I n).
    Notation MrowK := (@MrowK n).
    Notation MrowAdd := (@MrowAdd n).
    Notation MrowSwap := (@MrowSwap n).

    (* MA是可逆的 *)
    Definition invertible (MA : smat n) : Prop :=
      exists MB, MA * MB === I /\ MB * MA === I.

    (* M * N = I -> N * M = I *)
    (* 满秩矩阵 *)
    Axiom l_inv_r_inv : forall (M N: smat n), M * N === I -> N * M === I.

    (* I是可逆的 *)
    Lemma I_is_invertible: invertible I.
    Proof. exists I. split; apply mmul_I_l. Qed.

    (* (A*B)\T = B\T * A\T *)
    (** Transpose properties of matrix multiplication : T(AB) = T(B)*T(A) *)
    Theorem matrix_trans_mul:
      forall {m n p} (m1: mat m n) (m2: mat n p),
        mtrans (m1 * m2) === (mtrans m2) * (mtrans m1).
    Proof.
      red. intros.
      rewrite Mtimes_help; auto.
      rewrite Mtrans_help; auto.
      rewrite Mtimes_help; auto.
      apply sum_n_morphism. hnf. intros.
      rewrite !Mtrans_help; auto. ring.
    Qed.

    (* (m1 * m2) * m3 = m1 * (m2 * m3) *)
    Theorem matrix_mul_assoc:
      forall {x y p q} (m1: mat x y) (m2: mat y p) (m3: mat p q),
        (m1 * m2) * m3 === m1 * (m2 * m3).
    Proof. intros. apply meq2Meq. apply mmul_assoc. Qed.


    (* 如果A、B是两个同阶可逆矩阵，则AB可逆 *)
    Lemma AB_inversion:
      forall (MA MB MC MD: smat n ), 
        invertible MA -> invertible MB ->
        invertible (MA * MB).
    Proof.
      intros. hnf in *. destruct H as [MA' [HA1 HA2]], H0 as [MB' [HB1 HB2]].
      exists (MB' * MA'). split.
      - rewrite matrix_mul_assoc.
        rewrite <- (matrix_mul_assoc MB MB').
        rewrite HB1. rewrite mmul_I_l. rewrite HA1. reflexivity.
      - rewrite matrix_mul_assoc.
        rewrite <- (matrix_mul_assoc MA' MA).
        rewrite HA2. rewrite mmul_I_l. rewrite HB2. reflexivity.
    Qed.

    (* 可逆交换：A可逆，则 AB = I -> BA = I *)
    Lemma AB_BA:
      forall MA MB, invertible MA -> MA * MB === I -> MB * MA === I. 
    Proof.
      intros. destruct H as [MA' [HA1 HA2]].
      assert (MA' * (MA * MB) * MA === I).
      - rewrite H0. rewrite matrix_mul_assoc.
        rewrite mmul_I_l. rewrite HA2. reflexivity.
      - rewrite <- matrix_mul_assoc in H. rewrite HA2 in H.
        rewrite mmul_I_l in H. auto.
    Qed.

    (* 逆矩阵唯一：A可逆，AB=I, AC=I，则 B=C *)
    Lemma A_only_inversion:
      forall (MA MB MC: smat n ), 
        invertible MA -> 
        MA * MB === I -> 
        MA * MC === I -> 
        MC == MB.
    Proof.
      intros.
      assert (I * MB === MB). apply mmul_I_l.
      apply AB_BA in H1; auto.
      rewrite <-H1 in H2. rewrite matrix_mul_assoc in H2.
      rewrite H0 in H2. rewrite mmul_I_r in H2.
      apply Meq2meq in H2; auto.
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
    Fixpoint elem_change_down  (MA: smat n ) (x: nat) (cur: nat) : smat n * smat n :=
      match cur with
      | O => (I, MA)
      | S cur' =>
          let ee := MrowAdd (n - cur) x (- (mnth MA (n - cur) x))%A in
          let (E, MT) := elem_change_down (ee * MA) x cur' in
          (E * ee, MT)
      end.

    (* 
 1 2 1      
-1-3 1  =>  return 0
 1 0 6     
[(n - i)++, y] , i 
得到第一个非0 *)
    Fixpoint get_first_none_zero (MA: smat n) (i: nat) (y: nat) :=
      match i with
      | O => n
      | S i' =>
          if (decidable (mnth MA (n - i) y) 0) then
            get_first_none_zero MA i' y
          else
            (n - i)%nat
      end.

    (*

第一步,swap 
 0 1 0      -1-3 1    0 1 0
-1-3 1  =>   0 1 0    1 0 0
 1 0 6       1 0 6 ,  0 0 1
第二步,首个数字化简成1
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
    Fixpoint row_echelon_form (MA: smat n) (i: nat) :=
      match i with
      | O => Some (I, MA)
      | S i' =>
          let r := get_first_none_zero MA i (n - i) in
          if (r =? n) then None
          else
            let A0 := (MrowSwap (n - i) r) * MA in
            (* 把当前0行和第一个非0行互换 *)
            let ee := (MrowK (n - i) (/ (mnth A0 (n - i) (n - i)))) in
            (* 保证这一列第一个数字是1 *)
            let (E, MT) := elem_change_down (ee * A0) (n - i) (i - 1) in
            (* 下面元素全部与当前行相减，变成0 *)
            let ret := row_echelon_form MT i' in
            match ret with
            | None => None
            | Some (E', MT') => Some (E' * E * ee * MrowSwap (n - i) r, MT')
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
    Fixpoint elem_change_up (MA: smat n) (x: nat) (i: nat) :=
      match i with
      | O => (I, MA)
      | S i' =>
          let ee := MrowAdd i' x (- (mnth MA i' x))%A in
          let (E, MT) := elem_change_up (ee * MA) x i' in
          (E * ee, MT)
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
    Fixpoint fst_to_I (MA: smat n) (i: nat) :=
      match i with
      | O => (I, MA)
      | S i' =>
          let (E, MT) := elem_change_up (MA) i' i' in
          let (E', MT') := fst_to_I MT i' in
          (E' * E, MT')
      end.

    Definition Inversion (MA: smat n) := 
      match row_echelon_form MA n with
      | None => None
      | Some (E, MT) => Some (fst (fst_to_I MT n) * E)
      end.

    Hint Rewrite
      @f2m_help @mnth_MsingleVal
      @mnth_MrowK @mnth_MrowAdd @swap_map: MMM.

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
      forall (MA : smat n) (x cur : nat),
        x < n -> cur < n - x ->
        (fst (elem_change_down MA x cur) * MA) === snd (elem_change_down MA x cur).
    Proof.
      intros.
      generalize dependent MA.
      induction cur.  (* 验证每行是否都成立*)
      - intros. simpl. apply mmul_I_l.
      - assert (cur < n - x). lia.
        intros. simpl.
        destruct (elem_change_down
                    (MrowAdd (n - S cur) x
                       (- (MA&[n - S cur, x]))%A * MA) x cur) eqn: eq.
        simpl in *.
        specialize (IHcur H1 
                      (MrowAdd (n - S cur) x
                         (- MA&[n - S cur, x])%A * MA)).
        rewrite eq in IHcur.
        simpl in *. rewrite matrix_mul_assoc. auto.
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
      forall (MA : smat n) (x cur : nat),
        x < n -> cur < n - x -> mnth MA x x = 1 ->
        forall i j, i < n - cur -> j < n ->
                    mnth (snd (elem_change_down MA x cur)) i j = mnth MA i j.
    Proof.
      intros.
      generalize dependent MA.
      generalize dependent i.
      generalize dependent j.
      induction cur.
      - intros. simpl. auto.
      - intros. simpl.
        destruct (elem_change_down
                    (MrowAdd (n - S cur) x
                       (- (MA&[n - S cur, x]))%A * MA) x cur) eqn: eq.
        simpl.
        assert ((snd (elem_change_down
                        (MrowAdd (n - S cur) x
                           (- (MA&[n - S cur, x]))%A * MA) x cur)&[i, j]) =
                  ((MrowAdd (n - S cur) x
                      (- (MA&[n - S cur, x]))%A * MA)&[i, j])).
        {
          apply IHcur; auto; try lia.
          rewrite mnth_MrowAdd; auto; try lia.
          bdestruct (x =? n - S cur); auto.
          rewrite H1. rewrite <- H4. rewrite H1. lia.
        }
        rewrite eq in H4.
        simpl in H4.
        rewrite H4.
        rewrite mnth_MrowAdd; auto; try lia.
        destruct (i =? n - S cur) eqn: eq0; auto.
        apply Nat.eqb_eq in eq0; auto.
        rewrite <-eq0.
        lia.
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
      forall (MA : smat n) (x cur : nat),
        x < n -> cur < n - x -> mnth MA x x = 1 ->
        forall y, y >= n - cur -> y < n ->
                  mnth (snd (elem_change_down MA x cur)) y x = 0.
    Proof.
      intros.
      generalize dependent MA.
      generalize dependent y.
      induction cur. 
      - intros. simpl. lia.
      - intros.
        destruct (Nat.eqb y (n - S cur)) eqn: eq.
        + simpl.
          destruct (elem_change_down
                      (MrowAdd (n - S cur) x
                         (- (MA&[n - S cur, x]))%A * MA) x cur) eqn: eq2. 
          simpl.
          assert (s0&[y, x] =
                       (MrowAdd (n - S cur) x
                          (- (MA&[n - S cur, x]))%A * MA)&[y, x]).
          {
            assert (s0 = snd (elem_change_down
                                (MrowAdd (n - S cur) x
                                   (- (MA&[n - S cur, x]))%A * MA) x cur))
              by (rewrite eq2; auto).
            rewrite H4.
            apply elem_change_down_former_row_keep; auto; try lia.
            rewrite mnth_MrowAdd; auto; try lia.
            elim_bool. rewrite <-eq0. lia.
            auto.
            apply Nat.eqb_eq in eq; lia.
          }
          rewrite H4.
          rewrite mnth_MrowAdd; auto; try lia.
          elim_bool; auto; try lia.
          rewrite <- eq0. rewrite H1. ring.
        + simpl.
          destruct (elem_change_down
                      (MrowAdd (n - S cur) x
                         (- (MA&[n - S cur, x]))%A * MA) x cur) eqn: eq2.
          simpl.
          assert (s0 = snd (elem_change_down
                              (MrowAdd (n - S cur) x
                                 (- (MA&[n - S cur, x]))%A * MA) x cur))
            by (rewrite eq2; auto).
          rewrite H4.
          apply IHcur; auto; try lia.
          apply Nat.eqb_neq in eq; lia.
          rewrite mnth_MrowAdd; auto; try lia.
          destruct (Nat.eqb x (n - S cur)) eqn: eq0.
          apply Nat.eqb_neq in eq; try lia.
          apply Nat.eqb_eq in eq0; try lia.
          auto.
    Qed.

    (*
左下角0
i>j保证在对角线以下
j<x保证在x列之前
     *)
    Definition lower_left_zeros (MA: smat n) (x: nat) :=
      forall i j,
        i < n -> j < n -> j < x -> i > j -> mnth MA i j = 0.

    (*
第x列,x=1,
第n-cur行, cur=1,0, 第1,2行
i>j, j<x, MA[i,j] = e0

1 3-1     1 3-1   1 x x
0 1 0 ->  0 1 0 , 0 x x 这部分是相等的
0-3 7     0 0 7   0 x x

     *)

    Lemma elem_change_down_keep_lower_left_zeros:
      forall (MA : smat n) (x cur : nat),
        x < n -> cur < n - x -> mnth MA x x = 1 -> lower_left_zeros MA x -> 
        lower_left_zeros (snd (elem_change_down MA x cur)) x.
    Proof.
      intros.
      generalize dependent MA.
      induction cur.
      - intros. simpl. auto.
      - intros.
        simpl.
        destruct (elem_change_down
                    (MrowAdd (n - S cur) x
                       (- (MA&[n - S cur, x]))%A * MA) x cur) eqn: eq.
        simpl.
        unfold lower_left_zeros in *.
        intros.
        destruct (i <? (n - S cur)) eqn: eq2.
        + 
          replace s0 with (snd (elem_change_down
                                  (MrowAdd (n - S cur) x
                                     (- (MA&[n - S cur, x]))%A * MA) x cur))
            by (rewrite eq; auto).
          assert (0 = (MrowAdd (n - S cur) x
                         (- (MA&[n - S cur, x]))%A * MA)&[i, j]).
          {
            rewrite mnth_MrowAdd; auto; try lia. apply Nat.ltb_lt in eq2.
            destruct (i =? (n - S cur)) eqn: eq0.
            apply Nat.eqb_eq in eq0; lia.
            apply Nat.eqb_neq in eq0.
            rewrite H2; auto.
          }
          rewrite H7.
          apply elem_change_down_former_row_keep; auto; try lia.
          rewrite mnth_MrowAdd; auto; try lia.
          apply Nat.ltb_lt in eq2.
          elim_bool; auto; try lia.
          apply Nat.ltb_lt in eq2.
          lia.

        + destruct (i =? (n - S cur)) eqn: eq3; elim_bool; auto; try lia.
          * subst.
            replace (s0) with (snd (elem_change_down
                                      (MrowAdd (n - S cur) x
                                         (- (MA&[n - S cur, x]))%A * MA) x cur))
              by (rewrite eq; auto).
            assert (0 = (MrowAdd (n - S cur) x
                           (- (MA&[n - S cur, x]))%A * MA)&[n - S cur, j]).
            {
              rewrite mnth_MrowAdd; auto; try lia.
              elim_bool; auto; try lia.
              rewrite H2; auto.
              replace (MA&[x, j]) with 0 by (rewrite H2; auto). ring.
            }
            rewrite H7.
            apply elem_change_down_former_row_keep; auto; try lia.
            rewrite mnth_MrowAdd; auto; try lia.
            elim_bool; auto; try lia.
          * replace (s0) with (snd (elem_change_down
                                      (MrowAdd (n - S cur) x
                                         (- (MA&[n - S cur, x]))%A * MA) x cur))
              by (rewrite eq; auto).
            apply IHcur; auto; try lia.
            --- rewrite mnth_MrowAdd; auto; try lia.
                elim_bool; auto; try lia.
            --- intros.
                rewrite mnth_MrowAdd; auto; try lia.
                elim_bool; auto; try lia.
                rewrite H2; auto.
                replace (MA&[x, j0]) with 0 by (rewrite H2; auto). ring.
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
      forall (MA : smat n) (x : nat),
        x < n -> mnth MA x x = 1 -> lower_left_zeros MA x -> 
        lower_left_zeros (snd (elem_change_down MA x (n - x - 1))) (x + 1).
    Proof.
      intros.
      unfold lower_left_zeros.
      intros.
      destruct (j =? x) eqn: eq. elim_bool.
      - rewrite eq. apply elem_change_down_latter_row_keep; auto; lia. 
      - elim_bool. apply elem_change_down_keep_lower_left_zeros; auto; lia.
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

    (* get_first_none_zero 的最小值是 n - i *)
    Lemma get_first_none_zero_at_least:
      forall (MA : smat n) (i j : nat), get_first_none_zero MA i j >= n - i.
    Proof.
      intros.
      induction i.
      - simpl. lia.
      - simpl.
        destruct (decidable (MA&[n - S i, j]) 0); lia. 
    Qed.

    (* get_first_none_zero 的最大值是 n *)
    Lemma get_first_none_zero_at_most:
      forall (MA : smat n) (i j : nat), get_first_none_zero MA i j <= n.
    Proof.
      intros.
      induction i.
      - simpl. lia.
      - simpl. destruct (decidable (MA&[n - S i, j]) 0); lia. 
    Qed.

    (*   Lemma  get_first_none_zero_help:
    forall (A0 : smat n) (i j : nat), 
      get_first_none_zero A0 i j < n -> A0&[get_first_none_zero A0 i j, j] <> e0.
  Proof.
    intros.
    induction i.
    - simpl. simpl in H. lia.
    - simpl; mytauto.
      simpl in H.
      mytauto.
  Qed. *)

    Lemma row_echelon_form_mult_eq:
      forall (MA : smat n) (i : nat) (E EA : smat n),
        i <= n -> row_echelon_form MA i = Some (E, EA) -> 
        E * MA === EA.
    Proof.
      intros.
      generalize dependent MA.
      generalize dependent E.
      generalize dependent EA.
      induction i; intros.
      - simpl in H0. inversion H0. subst. apply mmul_I_l.
      - unfold row_echelon_form in H0.
        fold row_echelon_form  in H0.

        destruct 
          (elem_change_down
             (MrowK (n - S i)
                (/((MrowSwap (n - S i) (get_first_none_zero MA (S i) (n - S i)) * MA)&[n - S i, n - S i])) *
                (MrowSwap (n - S i) (get_first_none_zero MA (S i) (n - S i)) * MA)) (n - S i) 
             (S i - 1)) eqn: Heqp. 
        destruct (get_first_none_zero MA (S i) (n - S i) =? n) eqn: Heqb.
        inversion H0.

        destruct (row_echelon_form s0 i) eqn: Heqo.
        destruct (p) eqn: ?.

        subst.
        remember (MrowSwap (n - S i) (get_first_none_zero MA (S i) (n - S i)) * MA) as A1.
        remember (MrowK (n - S i) (/ (A1&[n - S i, n - S i])) * A1) as A2. 
        inversion H0.
        replace ((if decidable (MA&[n - S i, n - S i]) 0
                  then get_first_none_zero MA i (n - S i)
                  else (n - S i)%nat)) 
          with (get_first_none_zero MA (S i) (n - S i)) by (auto).
        rewrite matrix_mul_assoc.
        rewrite <- HeqA1.
        assert (s * A2 === s0).
        {
          replace s with (fst (elem_change_down A2 (n - S i) (S i - 1))) by (rewrite Heqp; auto).
          replace s0 with (snd (elem_change_down A2 (n - S i) (S i - 1))) by (rewrite Heqp; auto).
          apply elem_change_down_mult_eq; lia.
        }
        destruct (row_echelon_form s0 i) eqn: eq3.
        * destruct p.
          apply IHi in eq3; try lia. 
          
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

    (* 
1 x x
x 1 x
x x 1

L行以上的对角线全是1
     *)
    Definition diagonal_ones (MA: smat n) (L: nat) :=
      forall i,
        i < n -> i < L -> mnth MA i i = 1.

    (* 
行阶梯矩阵

X = EA, E是单位矩阵

n行以上对角线全是1
     *)
    Lemma row_echelon_form_to_diag_ones :
      forall (X : smat n) (i : nat) (E EA : smat n),
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
        replace n with (n - 0)%nat by lia.
        assumption.
      - unfold diagonal_ones.
        intros.
        unfold row_echelon_form in H1.
        fold row_echelon_form in *.

        destruct 
          (elem_change_down 
             (MrowK (n - S i)
                (/ ((MrowSwap (n - S i)
                       (get_first_none_zero X (S i) (n - S i)) * X)&[n - S i, n - S i])) 
              *
                (MrowSwap (n - S i) (get_first_none_zero X (S i) (n - S i)) * X)) 
             (n - S i)
             (S i - 1)) eqn: Heqp.
        destruct (get_first_none_zero X (S i) (n - S i) =? n) eqn: Heqb.
        inversion H1.

        destruct (row_echelon_form s0 i) eqn: Heqo.
        destruct (p) eqn: ?.

        remember (MrowSwap (n - S i) (get_first_none_zero X (S i) (n - S i)) * X) as A0.
        remember (MrowK (n - S i) (/ (A0&[n - S i, n - S i])) * A0) as A1.
        try rewrite <- HeqA0 in *; try rewrite <- HeqA1 in *.


        (* 
      要应用IHi，先构造一个diagonal_ones X (n - i)
         *)
        assert (diagonal_ones s0 (n - i)).
        {
          unfold diagonal_ones. intros.
          replace (s0) with (snd (elem_change_down A1 (n - S i) (S i - 1)))
            by (rewrite Heqp; auto). 
          rewrite elem_change_down_former_row_keep; auto; try lia.
          + rewrite HeqA1.
            rewrite mnth_MrowK; elim_bool; auto; try lia.
            * rewrite <-eq.
              (* rewrite field_mulInvL; auto. *)
              rewrite inv_self; auto.
            * rewrite HeqA0.
              assert (get_first_none_zero X (S i) (n - S i) <= n)
                by apply get_first_none_zero_at_most.
              assert (get_first_none_zero X (S i) (n - S i) >= n - S i)
                by apply get_first_none_zero_at_least.
              
              rewrite swap_map; destruct (i1 =? n - S i) eqn: eq0;
                destruct (i1 =? get_first_none_zero X (S i) (n - S i)) eqn: eq1;
                progress elim_bool;
                progress subst; try lia.

              apply H0. lia. lia.
          + rewrite HeqA1. rewrite mnth_MrowK; try lia. elim_bool.
            rewrite inv_self; auto.
            lia.
        }
        apply IHi with (E:=m) (EA:=s1) in H4 ; auto.
        inversion H1. 
        rewrite <- H7.
        apply H4; auto.
        lia.
        inversion H1.
    Qed.

    (* 
行阶梯矩阵

n-i列之前，左下角全是0，
X = EA, E是单位矩阵
n行以上左下角全是0
     *)
    Lemma row_echelon_form_to_lower_left_zeros:
      forall (X : smat n) (i : nat) (E EA : smat n),
        i <= n -> lower_left_zeros X (n - i) ->
        row_echelon_form X i = Some (E, EA) -> 
        lower_left_zeros EA n.
    Proof.
      intros X i.
      generalize dependent X.
      induction i; intros.
      - replace n with (n - 0)%nat by lia.
        simpl in H1.
        inversion H1.
        rewrite <- H4. 
        assumption.
      - unfold row_echelon_form in H1. 
        fold row_echelon_form in *.
        destruct 
          (elem_change_down 
             (MrowK (n - S i)
                (/ ((MrowSwap (n - S i) (get_first_none_zero X (S i) (n - S i))%A * X)&[n - S i, n - S i])) 
              *
                (MrowSwap (n - S i) (get_first_none_zero X (S i) (n - S i)) * X)) 
             (n - S i)
             (S i - 1)) eqn: Heqp.
        destruct (get_first_none_zero X (S i) (n - S i) =? n) eqn: Heqb.
        inversion H1.

        destruct (row_echelon_form s0 i) eqn: Heqo.
        destruct (p) eqn: ?.
        remember (MrowSwap (n - S i) (get_first_none_zero X (S i) (n - S i)) * X) as A0.
        remember (MrowK (n - S i) (/ (A0&[n - S i, n - S i])) * A0) as A1; try rewrite <- HeqA0 in *; try rewrite <- HeqA1 in *.
        (* 
      需要利用IHi，先构建lower_left_zeros X (n - i)
         *)
        assert (lower_left_zeros s0 (n - i)).
        {
          unfold lower_left_zeros.
          intros. 
          assert (get_first_none_zero X (S i) (n - S i) <= n)
            by apply get_first_none_zero_at_most.
          assert (get_first_none_zero X (S i) (n - S i) >= n - S i)
            by apply get_first_none_zero_at_least.
          
          replace (s0) with (snd (elem_change_down A1 (n - S i) (S i - 1)))
            by (rewrite Heqp; auto).
          replace (S i - 1)%nat with (n - (n - S i) - 1)%nat by lia. 
          apply lower_left_zeros_extend with (x := (n - S i)%nat); try lia;
            progress subst; progress autorewrite with MMM;
            destruct (n - S i =? n - S i) eqn: eq;
            elim_bool; try lia; auto.

          + rewrite inv_self; auto.
          + unfold lower_left_zeros; intros.
            rewrite mnth_MrowK; auto; try lia.
            
            elim_bool.
            progress autorewrite with MMM; auto; try lia.
            elim_bool; try lia.
            subst.
            
            * replace ( X&[get_first_none_zero X (S i) (n - S i), j0]) with 0
                by (rewrite <- H0; auto; lia). ring.
            * autorewrite with MMM; auto; try lia.
              elim_bool.
              lia. 
              rewrite <- H0; auto; lia.
              auto.
        }
        apply IHi with (X := s0) (E := m); auto; try lia.
        inversion H1. 
        rewrite <- H5.
        assumption.
        inversion H1.
    Qed.

    Definition upper_triangle (MA: smat n) := 
      lower_left_zeros MA n.


    (* 归一化上三角形，即阶梯矩阵 *)
    Definition normalized_upper_triangle (MA: smat n) := 
      diagonal_ones MA n /\ lower_left_zeros MA n.

    Theorem row_echelon_form_correct:
      forall A E EA : smat n,
        row_echelon_form A n = Some (E, EA) -> 
        E * A === EA /\ normalized_upper_triangle EA.
    Proof.
      intros.
      split.
      - eapply row_echelon_form_mult_eq; eauto.
      - unfold normalized_upper_triangle.
        split.
        + unfold diagonal_ones. eapply row_echelon_form_to_diag_ones. auto.
          unfold diagonal_ones. intros. lia. eauto.
        + eapply row_echelon_form_to_lower_left_zeros. auto.
          unfold lower_left_zeros. intros. lia. eauto.
    Qed.


    (* ************************************************************************ *)

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
      forall (MA : smat n) (x i : nat),
        x < n -> i <= x ->
        (fst (elem_change_up MA x i) * MA) === snd (elem_change_up MA x i).
    Proof.
      intros.
      generalize dependent MA. 
      induction i.
      - intros. simpl. apply mmul_I_l.
      - assert (i <= x) by lia. intros.
        eapply IHi in H1.
        simpl.
        destruct (elem_change_up (MrowAdd i x (- (MA&[i, x]))%A * MA) x i) eqn: eq.
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
    Definition upper_right_zeros (MA: smat n) (L: nat) :=
      forall i j,
        i < n -> j < n -> j >= n - L -> i < j -> mnth MA i j = 0.


    Definition lower_triangle (MA: smat n) := 
      upper_right_zeros MA n.
    (* 
!!!
上三角矩阵
i'行， x列
i' < x

上三角元素，经过行相加变化，还是上三角

     *)
    Lemma row_add_to_row_keep_upper_triangle:
      forall (MA : smat n) (x i' : nat),
        x < n -> i' < x -> normalized_upper_triangle MA -> 
        normalized_upper_triangle ((MrowAdd i' x
                                      (- (mnth MA i' x)))%A * MA).
    Proof.
      intros.
      unfold normalized_upper_triangle.
      inversion H1.
      unfold diagonal_ones in H2. 
      unfold lower_left_zeros in H3. 
      split.
      + unfold diagonal_ones; intros.
        rewrite mnth_MrowAdd; auto; try lia.
        elim_bool; auto; try lia.
        replace (MA&[x, i]) with 0 by (rewrite H3; auto; lia).
        replace (MA&[i, i]) with 1 by (rewrite H2; auto; lia). ring.
      + unfold lower_left_zeros; intros. 
        rewrite mnth_MrowAdd; auto; try lia.
        elim_bool; auto; try lia.
        replace (MA&[i, j]) with 0 by (rewrite H3; auto; lia).
        replace (MA&[x, j]) with 0 by (rewrite H3; auto; lia). ring.
    Qed.


    (* 
!!!
上三角矩阵，elem_change_up之后，还是上三角
     *)
    Lemma elem_change_up_keep_upper_triangle :
      forall (MA : smat n) (x i : nat),
        x < n -> i <= x -> normalized_upper_triangle MA
        -> normalized_upper_triangle (snd (elem_change_up MA x i)). 
    Proof.
      intros.
      generalize dependent MA.
      generalize dependent x.
      induction i; intros.
      - simpl. assumption.
      - simpl.
        destruct (elem_change_up (MrowAdd i x (- (MA&[i, x]))%A * MA) x i) eqn: eq.
        replace (@snd (@Matrix.mat A n n) (smat n) (m * MrowAdd i x (- (MA&[i, x]))%A, s))
          with (snd (elem_change_up (MrowAdd i x (- (MA&[i, x]))%A * MA) x i))
          by (rewrite eq; auto).
        apply IHi; auto; try lia.
        apply row_add_to_row_keep_upper_triangle; auto.
    Qed.

    (* 
上三角矩阵
elem_change_up MA x i作用是第x列，0~i-1行元素变0，
经过elem_change_up MA x i之后的第i~n-1列，元素不变

利用行相加变换，i行不变
(MrowAdd i x (M.opp (MA&[i, x])) M* MA)&[i', j] == MA&[i', j]

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
      forall (MA : smat n) (x i : nat),
        x < n -> i <= x -> normalized_upper_triangle MA ->
        forall i' j, i' < n -> i' >= i -> j < n -> mnth (snd (elem_change_up MA x i)) i' j = mnth MA i' j.
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
        destruct (elem_change_up (MrowAdd i x
                                    (- (MA&[i, x]))%A * MA) x i) eqn: eq.
        simpl.
        assert (snd (elem_change_up (MrowAdd i x
                                       (- (MA&[i, x]))%A * MA) x i)&[i', j] = (MrowAdd i x (- (MA&[i, x]))%A * MA)&[i', j]).
        {
          apply IHi; auto; try lia.
          apply row_add_to_row_keep_upper_triangle; auto; try lia.
        }
        rewrite eq in H5. simpl in H5.
        simpl.
        rewrite H5.
        rewrite mnth_MrowAdd; auto; try lia.
        elim_bool; auto.
        lia.
    Qed.

    (* 
上三角矩阵
elem_change_up MA x i作用是第x列，0~i-1行元素变0，
上面元素还是0
 x < n
i0 < i

利用行相加变换，i行不变
(MrowAdd i x (M.opp (MA&[i, x])) M* MA)&[i', j] == MA&[i', j]
     *)

    Lemma elem_change_up_upper_rows_to_0 :
      forall (MA : smat n) (x i : nat),
        x < n -> i <= x -> normalized_upper_triangle MA ->
        (forall i0, i0 < i -> (snd (elem_change_up MA x i))&[i0, x] = 0).
    Proof.
      intros.
      generalize dependent MA.
      generalize dependent x.
      generalize dependent i.
      generalize dependent i0. 
      induction i; intros.
      - simpl. lia.
      - simpl.
        inversion H1.
        unfold diagonal_ones in H3.
        unfold lower_left_zeros in H4. 
        destruct (elem_change_up (MrowAdd i x (- (MA&[i, x]))%A * MA) x i) eqn: eq.
        simpl.
        replace (s) with (snd (elem_change_up (MrowAdd i x
                                                 (- (MA&[i, x]))%A * MA) x i))
          by (rewrite eq; auto).
        destruct (i0 =? i) eqn: eq2; elim_bool; auto.      
        (*       
      i0 == i
         *)
        (* ???  *)

        + (* rewrite IHi; auto; try lia. inversion eq2.  *)
          rewrite elem_change_up_lower_rows_keep; auto; try lia.
          * rewrite mnth_MrowAdd; auto; try lia.
            elim_bool; auto; try lia.
            replace (MA&[x, x]) with 1 by (rewrite H3; auto; lia).
            rewrite eq0. ring.
          * apply row_add_to_row_keep_upper_triangle; auto; lia.
        (*       
      i0 <> i
         *)
        + rewrite IHi; auto; try lia.
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
      forall (MA : smat n) (x i L : nat) ,
        x < n -> i <= x -> L < n - x ->
        normalized_upper_triangle MA -> upper_right_zeros MA L ->  
        upper_right_zeros (snd (elem_change_up MA x i)) L.
    Proof.
      intros.
      generalize dependent MA.
      generalize dependent x.
      generalize dependent L.
      induction i; intros; try assumption.
      simpl.
      destruct (elem_change_up (MrowAdd i x
                                  (- (MA&[i, x]))%A * MA) x i) eqn: eq.
      (* 
    用的是同一个m0
       *)
      simpl.
      replace (s) with (snd (elem_change_up (MrowAdd i x
                                               (- (MA&[i, x]))%A * MA) x i))
        by (rewrite eq; auto).
      apply IHi; auto; try lia.
      - apply row_add_to_row_keep_upper_triangle; auto; lia.
      - unfold upper_right_zeros.
        (* 
      i0 < n ->
      j < n -> 
      j >= n - L -> 
      i0 < j
         *)
        intros.
        rewrite mnth_MrowAdd; auto; try lia.
        elim_bool; auto; try lia.
        rewrite eq0.
        (* 
      i == j

      L < n - x
      n - L <= j < n
      i < j   上三角
      i <= x < n
      x < j   上三角
         *)
        replace (MA&[i, j]) with 0 by (rewrite H3; auto; lia).
        replace (MA&[x, j]) with 0 by (rewrite H3; auto; lia). ring.
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
      forall (MA : smat n) (x : nat),
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
      - rewrite eq. apply elem_change_up_upper_rows_to_0; auto; lia.
      (* 
    j > x
       *)
      - rewrite elem_change_up_keep_upper_right_zeros
          with (L := (n - x - 1)%nat); auto; lia.
    Qed.

    (* 
fst (fun MA) * MA = snd (fun MA)
     *)
    Lemma fst_to_I_mult_eq:
      forall (MA : smat n) (i : nat),
        i <= n ->
        fst (fst_to_I MA i) * MA === snd (fst_to_I MA i).
    Proof.
      intros.
      generalize dependent MA.
      induction i.
      - intros; simpl.
        apply mmul_I_l.
      - intros.
        simpl.
        destruct (elem_change_up MA i i) eqn: eq1.
        destruct (fst_to_I s i) eqn: eq2.
        simpl.
        rewrite matrix_mul_assoc.
        replace (m) with (fst (elem_change_up MA i i)) by (rewrite eq1; auto). 
        rewrite elem_change_up_mult_eq; auto; try lia.
        replace (m0) with (fst (fst_to_I s i)) by (rewrite eq2; auto).
        replace (s0) with (snd (fst_to_I s i)) by (rewrite eq2; auto).
        rewrite eq1. simpl.
        apply IHi. lia.
    Qed.

    (* 
上三角 MA
fst_to_I MA n之后，
还是上三角
     *)
    Lemma fst_to_I_keep_upper_triangle:
      forall (MA : smat n) (i : nat),
        i <= n -> normalized_upper_triangle MA -> 
        normalized_upper_triangle (snd (fst_to_I MA i)).
    Proof.
      intros.
      generalize dependent MA.
      induction i.
      - intros. simpl. assumption.
      - intros; simpl.
        destruct (elem_change_up MA i i) eqn: eq1.
        destruct (fst_to_I s i) eqn: eq2.
        simpl.
        replace (s0) with (snd (fst_to_I s i)) by (rewrite eq2; auto).
        apply IHi; auto; try lia.
        replace (s) with (snd (elem_change_up MA i i)) by (rewrite eq1; auto).
        apply elem_change_up_keep_upper_triangle; auto; try lia.
    Qed.

    (* 
上三角 MA
n-i右上是0
那么snd (fst_to_I MA i)之后，
  n右上是0
     *)
    Lemma fst_to_I_to_upper_right_zeros:
      forall (MA : smat n) (i : nat),
        i <= n -> normalized_upper_triangle MA -> upper_right_zeros MA (n - i) -> 
        upper_right_zeros (snd (fst_to_I MA i)) n.
    Proof.
      intros.
      generalize dependent MA.
      induction i.
      - intros; simpl. replace (n) with (n - 0)%nat by lia. assumption.
      - intros; simpl.
        destruct (elem_change_up MA i i) eqn: eq1.
        destruct (fst_to_I s i) eqn: eq2.
        simpl.
        replace (s0) with (snd (fst_to_I s i)) by (rewrite eq2; auto).
        apply IHi; auto; try lia.
        + replace (s) with (snd (elem_change_up MA i i)) by (rewrite eq1; auto).
          apply elem_change_up_keep_upper_triangle; auto; try lia.
        + replace (s) with (snd (elem_change_up MA i i)) by (rewrite eq1; auto).
          apply upper_right_zeros_entend; auto; try lia.
          replace (n - i - 1)%nat with (n - S i)%nat by lia.
          assumption.
    Qed.

    (* 
fst * MA = snd 相乘相等
snd = MI
     *)
    Theorem fst_to_I_correct:
      forall (MA : smat n),
        normalized_upper_triangle MA ->
        fst (fst_to_I MA n) * MA === snd (fst_to_I MA n) /\ snd (fst_to_I MA n) === I.
    Proof.
      intros.
      split.
      - apply fst_to_I_mult_eq. auto.
      (* 
      主要是第二部分
       *)
      - hnf; intros.
        (* 分成上下三角考虑 *)
        destruct (j <=? i) eqn: eq; elim_bool; auto; try lia.
        
        + destruct (j =? i) eqn: eq2; elim_bool; auto; try lia.
          (*
      i==j
           *)
          * subst.
            unfold I. unfold I. 
            rewrite f2m_help; elim_bool; auto; try lia.
            apply fst_to_I_keep_upper_triangle. auto. auto. auto. auto.
          (*
      i<>j
           *)
          * unfold I. unfold I. 
            rewrite f2m_help; elim_bool; auto; try lia. apply Nat.leb_le in eq. subst.
            apply fst_to_I_keep_upper_triangle; auto; lia.
        (*
      j>i
         *)
        + unfold I. unfold I. 
          rewrite f2m_help; elim_bool; auto; apply Nat.leb_gt in eq; try lia.
          apply fst_to_I_to_upper_right_zeros; auto; try lia.
          unfold upper_right_zeros. intros.
          lia.
    Qed.


    Theorem Inversion_correct:
      forall (MA E : smat n),
        Inversion MA = Some E -> E * MA === I.
    Proof.
      intros.
      unfold Inversion in H.
      destruct (row_echelon_form MA n) eqn: eq; try inversion H.
      clear H1.
      destruct p.
      inversion H. clear H.
      assert (m * MA === s /\ normalized_upper_triangle s)
        by (apply row_echelon_form_correct; assumption).
      inversion H. clear H.
      rewrite matrix_mul_assoc.
      rewrite H0.
      assert ((snd (fst_to_I s n)) === I) by (apply fst_to_I_correct; auto).
      rewrite <- H.
      apply fst_to_I_mult_eq. auto.
    Qed.


    Theorem Inversion_is_invertible:
      forall (MA E : smat n),
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
      forall (MA E : smat n),
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

    (* A = B -> A * C = B * C *)
    Theorem ABC_equal_r:
      forall (MA MB MC: smat n),
        MA == MB ->
        MA * MC == MB * MC.
    Proof.
      intros. apply Meq2meq. apply meq2Meq in H.
      rewrite <-H. apply Meq_id.
    Qed.

    (* A = B -> C * A = C * B *)
    Theorem ABC_equal_l:
      forall (MA MB MC: smat n),
        MA == MB ->
        MC * MA == MC * MB.
    Proof.
      intros. apply Meq2meq. apply meq2Meq in H. rewrite H. reflexivity.
    Qed.

    (* A = B -> C * A = C * B /\ A * C = B * C *)
    Theorem ABC_equal:
      forall (MA MB MC: smat n),
        MA == MB ->
        MC * MA == MC * MB /\ MA * MC == MB * MC.
    Proof.
      intros.
      split.
      apply ABC_equal_l; auto.
      apply ABC_equal_r; auto.
    Qed.

    (* C可逆，CA = CB -> A = B *)
    Theorem matrix_cancellation_l:
      forall (MA MB MC A_inv B_inv C_inv: smat n),
        invertible MC ->
        MC * MA == MC * MB ->
        MA == MB.
    Proof.
      intros. apply meq2Meq in H0. apply Meq2meq.
      destruct H as [C' [HC1 HC2]].
      assert (C' * MC * MA === C' * MC * MB).
      - rewrite !matrix_mul_assoc.  rewrite H0. reflexivity.
      - rewrite HC2 in H. rewrite !mmul_I_l in H. auto.
    Qed.

    (* C可逆，AC = BC -> A = B *)
    Theorem matrix_cancellation_r:
      forall (MA MB MC A_inv B_inv C_inv: smat n),
        invertible MC ->
        MA * MC == MB * MC ->
        MA == MB.
    Proof.
      intros. apply meq2Meq in H0. apply Meq2meq.
      destruct H as [C' [HC1 HC2]].
      assert (MA * MC * C' === MB * MC * C').
      - rewrite H0. reflexivity.
      - rewrite !matrix_mul_assoc in H. rewrite HC1 in H.
        rewrite !mmul_I_r in H. auto.
    Qed.

    (* B' * A' * A * B = I *)
    Theorem AB_inv_help:
      forall (MA MB A_inv B_inv AB_inv: smat n),
        Inversion MA = Some A_inv ->
        Inversion MB = Some B_inv ->
        B_inv * A_inv * MA * MB == I.
    Proof.
      intros.
      apply Inversion_correct in H.
      apply Inversion_correct in H0.
      apply Meq2meq.
      rewrite matrix_mul_assoc with (m1:=B_inv) (m2:=A_inv) (m3:=MA).
      rewrite H.
      rewrite mmul_I_r.
      assumption.
    Qed.

    (* (A')\T\T = A' *)
    Theorem Inversion_trans_trans:
      forall (MA A_inv : smat n),
        Inversion MA = Some A_inv ->
        mtrans( mtrans (A_inv )) == A_inv.
    Proof.
      intros. rewrite mtrans_trans. reflexivity.
    Qed.

    (* A' + B' = B' + A' *)
    Theorem Inversion_add:
      forall (MA MB A_inv B_inv : smat n),
        Inversion MA = Some A_inv ->
        Inversion MB = Some B_inv ->
        A_inv + B_inv == B_inv + A_inv.
    Proof. intros. apply madd_comm. Qed.

    (* (A' + B') + C' = A' + (B' + C') *)
    Theorem Inversion_add_assoc:
      forall (MA MB MC A_inv B_inv C_inv: smat n),
        Inversion MA = Some A_inv ->
        Inversion MB = Some B_inv ->
        Inversion MC = Some C_inv ->
        A_inv + B_inv + C_inv == A_inv + (B_inv + C_inv).
    Proof. intros. apply madd_assoc. Qed.

    (* A' * A = I *)
    Theorem Inversion_self_correct:
      forall (MA A_inv : smat n),
        Inversion MA = Some A_inv ->
        A_inv * MA == I.
    Proof.
      intros.
      apply Inversion_correct in H.
      apply Meq2meq; auto.
    Qed.

    (* A * A' = I *)
    Theorem Inversion_self_correct2:
      forall (MA A_inv : smat n),
        Inversion MA = Some A_inv ->
        MA * A_inv == I.
    Proof.
      intros.
      pose proof (Inversion_inv_is_invertible MA H).
      apply Inversion_correct in H.
      apply AB_BA in H; auto.
      apply Meq2meq; auto.
    Qed.

    (* A\T * A'\T = (A'A)\T = I *)
    Theorem Inversion_trans_mult_inv_correct:
      forall (MA A_inv A_inv_inv: smat n),
        Inversion MA = Some A_inv ->
        mtrans MA * mtrans A_inv == I.
    Proof.
      intros. apply Meq2meq.
      rewrite <-matrix_trans_mul. apply Inversion_correct in H.
      rewrite H. rewrite I_eq_mat1. rewrite mtrans_mat1. reflexivity.
    Qed.

    (* A = (A')' *)
    Theorem Inversion_inv_inv_correct:
      forall (MA A_inv A_inv_inv: smat n),
        Inversion MA = Some A_inv ->
        Inversion A_inv = Some A_inv_inv ->
        MA == A_inv_inv.
    Proof.
      intros.
      apply Inversion_correct in H,H0.
      assert (A_inv_inv * A_inv * MA === MA).
      - rewrite H0. apply mmul_I_l.
      - rewrite matrix_mul_assoc in H1. rewrite H in H1.
        rewrite mmul_I_r in H1. symmetry.
        apply Meq2meq; auto.
    Qed.

    (* “第 i 行乘以 x 倍” 的矩阵是可逆的  *)
    Lemma row_mul_invertible:
      forall i x,
        i < n -> x <> 0 -> invertible (MrowK i x).
    Proof.
      intros.
      unfold invertible.
      exists (MrowK i (/ x)).
      split.
      - hnf; intros.
        rewrite mnth_MrowK; auto; try lia.
        bdestruct (i0 =? i); subst.
        + unfold MrowK. unfold MrowK.
          rewrite f2m_help; elim_bool; try lia.
          * subst. unfold I; elim_bool; try lia.
            autorewrite with MMM; try lia.
            elim_bool; try lia. rewrite commutative. apply inv_self.
          * unfold I; elim_bool; try lia.
            autorewrite with MMM; try lia. elim_bool; try lia. ring.
        + unfold MrowK; unfold MrowK; elim_bool; try lia.
          unfold I; elim_bool; try lia.
          autorewrite with MMM; try lia. elim_bool; try lia; auto.
      - hnf; intros.
        rewrite mnth_MrowK; elim_bool; try lia; subst.
        + unfold MrowK; unfold MrowK; unfold I; elim_bool; try lia.
          autorewrite with MMM; try lia. elim_bool; try lia; auto.
          apply inv_self. ring.
        + unfold MrowK; unfold MrowK; unfold I; elim_bool; try lia.
          autorewrite with MMM; try lia. elim_bool; try lia; auto.
    Qed.

    (*
c 0 0   1 1 1   c c c
0 c 0 * 1 1 1 = c c c
0 0 c   1 1 1   c c c
     *)
    Lemma mnth_MrowK_c:
      forall (c : A) (i j : nat), forall MA: smat n, 
        i < n -> j < n ->
        mnth ((@f2m n n
                 (fun i j => (if Nat.eqb i j then c else 0))) * MA) i j
        = (c * mnth MA i j)%A.
    Proof.
      intros.
      rewrite Mtimes_help; auto.
      apply sum_single with (x := i); auto.
      + intros.
        rewrite f2m_help; auto.
        elim_bool; auto; simpl; subst. lia. ring.
      + rewrite f2m_help; auto.
        elim_bool; auto; simpl; subst; try tauto.
    Qed.

    (* 如果A可逆，数k≠0，则kA也可逆，且(kA)\–1 = A\–1 *)

    (* 以下矩阵是可逆的
c 0 0
0 c 0
0 0 c
     *)
    Theorem row_mul_c_invertible:
      forall i c,
        i < n -> c <> 0 ->
        invertible (@f2m n n (fun i j => (if Nat.eqb i j then c else 0))).
    Proof.
      intros.
      unfold invertible.
      exists (@f2m n n (fun i j => (if Nat.eqb i j then (/ c) else 0))).
      split.
      - hnf; intros.
        rewrite mnth_MrowK_c; auto; try lia.
        rewrite f2m_help; elim_bool; try lia.
        * unfold I; elim_bool; try lia. autorewrite with MMM; try lia.
          elim_bool; try lia; auto.
          rewrite commutative. apply inv_self.
        * unfold I; elim_bool; try lia. autorewrite with MMM; try lia.
          elim_bool; try lia; auto. ring.
      - hnf; intros.
        rewrite mnth_MrowK_c; auto; try lia.
        rewrite f2m_help; elim_bool; try lia.
        * unfold I; elim_bool; try lia. autorewrite with MMM; try lia.
          elim_bool; try lia; auto. apply inv_self.
        * unfold I; elim_bool; try lia. autorewrite with MMM; try lia.
          elim_bool; try lia; auto. ring.
    Qed.
  End MatrixInversion.

End MatrixInv.


