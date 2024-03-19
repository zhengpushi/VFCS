(* 
   purpose  : 使用 SafeNatFun 模型，进一步简化代码，以便理解
 *)
From CoqMatrix Require Import SafeNatFun.Matrix.
From CoqMatrix Require Import MatrixTheorySF.
Require Import Extraction.

Set Implicit Arguments.

(** * unsorted *)

(* ab = (a, b) -> a = fst ab *)
Lemma pair_eq_imply_fst : forall {A B} ab (a : A) (b : B), ab = (a, b) -> a = fst ab.
Proof. intros. subst. auto. Qed.

(* ab = (a, b) -> b = snd ab *)
Lemma pair_eq_imply_snd : forall {A B} ab (a : A) (b : B), ab = (a, b) -> b = snd ab.
Proof. intros. subst. auto. Qed.

(* Some (a1, b1) = Some (a2, b2) -> a1 = a2 /\ b1 = b2 *)
Lemma Some_pair_eq : forall {A B} (a1 a2 : A) (b1 b2 : B),
    Some (a1, b1) = Some (a2, b2) -> a1 = a2 /\ b1 = b2.
Proof. intros. inversion H. auto. Qed.

(* 自动化简在上下文和目标中的 "x =? y" 表达式 *)
Ltac elim_bool:=
  repeat
    (intros;
     match goal with
     | [ H : context [ ?x =? ?y ] |- _] => bdestruct (x =? y)
     | [ |- context [?x =? ?y]] =>         bdestruct (x =? y)
     end;
     (* simpl; *)
     auto; try reflexivity; try easy; try lia; try ring
    ).


(* ########################################################################## *)
(** * Inverse Matrix  *)
Module MatrixInv (B : BaseType) (E : EqDecidableFieldElementType B).
  Include (DecidableFieldMatrixTheorySF E).

  (* ******************************************************************* *)
  (** ** Theory for matrix element *)
  
  Notation "0" := Azero : A_scope.
  Notation "1" := Aone : A_scope.

  (* 由于 Field 声明默认使用 Aeq，而此处使用特殊的 eq，
     所以要补充 eq 版本的 Field 声明，以便使用 ring, field 等策略 *)
  Lemma Field_thy_eq: field_theory 0 1 Aadd Amul Asub Aopp Adiv Ainv eq.
  Proof.
    constructor; intros; try easy.
    apply Ring_thy. apply Aone_neq_Azero. rewrite field_mulInvL; auto.
  Qed.
  Add Field Field_thy_inst : Field_thy_eq.
  
  (* /x * x = 1。原本 field_mulInvL 要求 x 非零，这里忽略了该条件。
     注意，该条件也许会导致某个隐藏的缺陷，需要仔细检查使用了该公理之处。*)
  Axiom inv_self : forall x, (/ x * x)%A = Aone.

  
  (* ******************************************************************* *)
  (** ** Theory for sequence over A *)

  (* 0 + f 0 + f 1 + ... + f (k-1) *)
  Notation sum n f := (@seqsum _ Aadd Azero f n).

  (* sum (f1(x) + f2(x)) = sum f1(x) + sum f2(x) *)
  Lemma sum_add : forall (n : nat) (f1 f2 : nat -> A),
      sum n (fun x => f1 x + f2 x)%A = (sum n f1 + sum n f2)%A.
  Proof. induction n; simpl; intros. ring. rewrite IHn. ring. Qed.

  (* ∑n∑m f(i,j) = ∑m∑n f(i,j) *)
  Lemma sum_swap :
    forall (m n : nat) (f : nat -> nat -> A),
      sum n (fun j => sum m (fun i => f i j)) =
        sum m (fun i => sum n (fun j => f i j)).
  Proof.
    induction m. simpl; intros.
    - apply seqsum_seq0. auto.
    - intros. simpl. rewrite !sum_add. rewrite IHm. auto.
  Qed.


  (* ******************************************************************* *)
  (** *** Identity matrix *)
  Arguments mat1 {n}.
  Notation I := mat1.
  

  (* ******************************************************************* *)
  (** ** Get element of matrix *)

  (** Get element of matrix : M $ i $ j *)

  (* (M\T)[i,j] = M[j,i] *)
  Lemma mnth_mtrans :  forall {m n} (M: mat m n) i j,
      i < m -> j < n -> (M\T) $ j $ i = M $ i $ j.
  Proof. intros. auto. Qed.

  (* mtrans 保持 meq *)
  Global Add Parametric Morphism m n : (@mtrans m n) with
         signature meq ==> meq as mtrans_mor.
  Proof. intros. hnf in *; intros. rewrite !mnth_mtrans; auto. Qed.

  (* (M + N)[i,j] = M[i,j] + N[i,j] *)
  Lemma mnth_madd : forall {m n} (M N : mat m n) i j,
      i < m -> j < n -> (M + N) $ i $ j = (M $ i $ j + N $ i $ j)%A.
  Proof. intros. auto. Qed.

  (* madd 保持 meq *)
  Global Add Parametric Morphism m n : (@madd m n) with
         signature meq ==> meq ==> meq as madd_mor.
  Proof.
    intros. hnf in *; intros. rewrite !mnth_madd; auto. rewrite H,H0; auto. easy.
  Qed.
  
  (* (m1 * m2)[i,j] = ∑(k,0,n) m1[i,k] * m2[k,j] *)
  Lemma mnth_mmul : forall {m n p} (m1: mat m n) (m2: mat n p) i j,
      i < m -> j < p -> (m1 * m2) $ i $ j = sum n (fun k => (m1 $ i $ k * m2 $ k $ j)%A).
  Proof. intros. auto. Qed.

  (* mmul 保持 meq *)
  Global Add Parametric Morphism m n p: (@mmul m n p) with
         signature meq ==> meq ==> meq as mmul_mor.
  Proof.
    intros. hnf in *; intros. rewrite !mnth_mmul; auto.
    apply seqsum_eq; intros k Hk. rewrite H, H0; auto. easy.
  Qed.

  (* (A * B)\T = B\T * A\T *)
  Lemma mtrans_mmul: forall {m n p} (m1: mat m n) (m2: mat n p),
      mtrans (m1 * m2) == (mtrans m2) * (mtrans m1).
  Proof.
    intros. hnf; intros. unfold Aeq. rewrite mnth_mtrans; auto.
    rewrite !mnth_mmul; auto. apply seqsum_eq; intros k Hk.
    rewrite !mnth_mtrans; auto.
    replace (@eq B.A) with (@eq A); auto. ring.
  Qed.

  
  (* ******************************************************************* *)
  (** ** f2m *)

  (** Generate a matrix from a function *)
  Definition f2m {m n} (f : nat -> nat -> A) : mat m n := mk_mat f.

  (* (f2m f)[i,j] = f i j *)
  Lemma mnth_f2m : forall {m n} (f: nat -> nat -> A) i j,
      i < m -> j < n -> (@f2m m n f) $ i $ j = f i j.
  Proof. intros. auto. Qed.


  (* ******************************************************************* *)
  (** ** 矩阵形状的谓词 *)
  
  (* 左下角是0: 矩阵前 x 列的左下角全为 0。当 x=n 时，则整个矩阵左下角全为0 *)
  Definition lowerLeftZeros {n} (MA: smat n) (x: nat) := forall i j,
      i < n -> j < n -> j < x -> i > j -> MA $ i $ j = 0.
  
  (* 对角线都是1：矩阵前 x 行/列的对角线都是 1。当 x=n 时，则整个矩阵的对角线都是1 *)
  Definition diagonalOnes {n} (MA: smat n) (x: nat) := forall i,
      i < n -> i < x -> MA $ i $ i = 1.
  
  (* 归一化上三角形：对角线全1，左下角全0 *)
  Definition normedUpperTri {n} (MA: smat n) := 
    diagonalOnes MA n /\ lowerLeftZeros MA n.
  
  (* 第 n- L 列开始的右上角全是 0 *)
  Definition upperRightZeros {n} (MA: smat n) (L: nat) := forall i j,
      i < n -> j < n -> j >= n - L -> i < j -> MA $ i $ j = 0.
  
  
  (* ******************************************************************* *)
  (** ** 基本矩阵：仅一个位置是指定值，其余都是 0 *)
  
  (* “(x,y) 是 c”的基本矩阵 *)
  Definition mcell {n} (x y: nat) (c: A) :=
    @f2m n n (fun i j => (if ((i =? x) && (j =? y))%bool then c else 0)).

  (* “基本矩阵左乘”取元素 *)
  Lemma mnth_mcell_mul: forall {n} (x y : nat) (c : A) (i j : nat) (MA: smat n), 
      i < n -> j < n -> x < n -> y < n ->
      ((mcell x y c) * MA) $ i $ j =
        if i =? x then (c * MA $ y $ j)%A else 0.
  Proof.
    intros. unfold mcell. rewrite mnth_mmul; auto; elim_bool; simpl; elim_bool.
    - subst. apply seqsum_unique with (i:=y); auto; elim_bool; simpl; ring.
    - apply seqsum_seq0; intros. elim_bool; simpl; ring.
  Qed.


  (* ******************************************************************* *)
  (** ** 倍乘：某行乘以k倍 *)

  (* 第 (x,x) 元素是 c，其余是单位阵 *)
  Definition mrowScale {n} (x: nat) (c: A) : smat n :=
    f2m (fun i j => (if i =? j then (if i =? x then c else 1) else 0)).
  
  Lemma mnth_mrowScale_mul: forall {n} (x : nat) (c : A) (i j : nat) (MA: smat n),
      i < n -> j < n -> x < n ->
      ((mrowScale x c) * MA) $ i $ j =
        if i =? x then (c * MA $ i $ j)%A else MA $ i $ j.
  Proof.
    intros. unfold mrowScale. rewrite mnth_mmul; auto; elim_bool; simpl; elim_bool.
    - subst. apply seqsum_unique with (i:=x); auto; elim_bool.
    - apply seqsum_unique with (i:=i); auto; elim_bool.
  Qed.


  (* ******************************************************************* *)
  (** ** 倍加：某行乘以k倍加到另一行 *)

  (* 第 y 行的 c 倍加到第 x 行。单位阵 + 第 (x,y) 元素是 c 的矩阵 *)
  Definition mrowAdd {n} (x y: nat) (c: A) : smat n := I + (mcell x y c).
  
  Lemma mnth_mrowAdd_mul: forall {n} (x y : nat) (c : A) (i j : nat) (MA: smat n),
      i < n -> j < n -> x < n -> y < n ->
      ((mrowAdd x y c) * MA) $ i $ j =
        if i =? x then (MA $ i $ j + c * MA $ y $ j)%A else MA $ i $ j.
  Proof.
    intros. unfold mrowAdd. rewrite mmul_add_distr_r; auto.
    rewrite mnth_madd; auto. rewrite mmul_1_l; auto.
    rewrite mnth_mcell_mul; auto. elim_bool.
  Qed.

  (* 归一化上三角矩阵，任意下面的行的倍数加到上面，仍然是归一化上三角矩阵 *)
  Lemma mrowAdd_keep_normedUpperTri:
    forall {n} (MA : smat n) (x i' : nat),
      x < n -> i' < x -> normedUpperTri MA -> 
      normedUpperTri ((mrowAdd i' x (- (MA $ i' $ x)))%A * MA).
  Proof.
    intros. unfold normedUpperTri. inv H1. split; hnf in *; intros.
    - rewrite mnth_mrowAdd_mul; auto; try lia. elim_bool. rewrite <- H5.
      rewrite H2; try lia. rewrite (H3 _ i); auto; try lia. ring.
    - rewrite mnth_mrowAdd_mul; auto; try lia. elim_bool. rewrite <- H7.
      rewrite !(H3 _ j); try lia. ring.
  Qed.
  

  (* ******************************************************************* *)
  (** ** 两行互换 *)

  (* 第 x, y 两行互换的矩阵。
     例如，(0,2) 两行互换如下：
     0 0 1 0
     0 1 0 0
     1 0 0 0
     0 0 0 1
     特点：第 (x,y) 和 (y,x) 元素是 1，其余不在x,y这些行列上的是单位阵。*)
  Definition mrowSwap {n} (x y: nat) : smat n  :=
    f2m (fun i j =>
           if i=?x
           then (if j=?y then 1 else 0)
           else (if i=?y
                 then (if j=?x then 1 else 0)
                 else if i=?j then 1 else 0)).

  Lemma mnth_mrowSwap_mul: forall {n} (x y i j : nat) (MA: smat n),
      i < n -> j < n -> x < n -> y < n ->
      ((mrowSwap x y) * MA) $ i $ j =
        if i =? x then MA $ y $ j
        else
          (if i =? y then MA $ x $ j else MA $ i $ j).
  Proof.
    intros. unfold mrowSwap. rewrite mnth_mmul; auto; elim_bool; simpl; elim_bool.
    - subst. apply seqsum_unique with (i:=y); auto; elim_bool.
    - subst. apply seqsum_unique with (i:=x); auto; elim_bool.
    - apply seqsum_unique with (i:=i); auto; elim_bool.
  Qed.
  

  (* ******************************************************************* *)
  (** ** Invertible matrix *)

  (* MA是可逆的 *)
  Definition invertible {n} (MA : smat n) : Prop :=
    exists MB, MA * MB == I /\ MB * MA == I.

  (* 可逆交换：A可逆，则 AB = I -> BA = I *)
  Lemma AB_BA: forall {n} (MA MB : smat n),
      invertible MA -> MA * MB == I -> MB * MA == I.
  Proof.
    intros. destruct H as [MA' [HA1 HA2]].
    assert (MA' * (MA * MB) * MA == I).
    - rewrite H0. rewrite mmul_assoc.  rewrite mmul_1_l. rewrite HA2. reflexivity.
    - rewrite <- mmul_assoc in H. rewrite HA2 in H. rewrite mmul_1_l in H. auto.
  Qed.
  
  (* M * N = I -> N * M = I *)
  (* 满秩矩阵。该性质是成立的，因为两个矩阵乘积的行列式为1，则各自的行列式都不可能是0，
     因此都可逆，所以有：M'=N, N'=M，所以由 MN=I 得到 M'(MN)N'=M'IN'，所以I=NIM=NM。
     但因为可能没有行列式理论，所以该定理暂不能在目前的上下文得证 *)
  Axiom l_inv_r_inv : forall {n} (M N: smat n), M * N == I -> N * M == I.

  (* I是可逆的 *)
  Lemma I_is_invertible: forall {n}, invertible (@I n).
  Proof. intros. exists I. split; apply mmul_1_l. Qed.

  (* 如果A、B是两个同阶可逆矩阵，则AB可逆 *)
  Lemma mmul_invertible: forall {n} (MA MB MC MD: smat n), 
      invertible MA -> invertible MB -> invertible (MA * MB).
  Proof.
    intros. hnf in *. destruct H as [MA' [HA1 HA2]], H0 as [MB' [HB1 HB2]].
    exists (MB' * MA'). split.
    - rewrite mmul_assoc. rewrite <- (mmul_assoc MB MB').
      rewrite HB1. rewrite mmul_1_l. rewrite HA1. reflexivity.
    - rewrite mmul_assoc. rewrite <- (mmul_assoc MA' MA).
      rewrite HA2. rewrite mmul_1_l. rewrite HB2. reflexivity.
  Qed.

  (* 逆矩阵唯一，或者看作是乘法消去律 *)
  Lemma mmul_cancel_l: forall {n} (MA MB MC: smat n),
      invertible MA -> MA * MB == I -> MA * MC == I -> MC == MB.
  Proof.
    intros. assert (I * MB == MB). apply mmul_1_l.
    apply AB_BA in H1; auto.
    rewrite <-H1 in H2. rewrite mmul_assoc in H2.
    rewrite H0 in H2. rewrite mmul_1_r in H2. auto.
  Qed.
  
  (* 倍乘矩阵是可逆的  *)
  Lemma row_mul_invertible: forall {n} i x,
      i < n -> x <> 0 -> @invertible n (mrowScale i x).
  Proof.
    intros. hnf. exists (mrowScale i (/ x)). split.
    - hnf; intros.
      rewrite mnth_mrowScale_mul; auto; try lia. simpl. elim_bool; subst.
      rewrite commutative. apply inv_self.
      unfold Aeq. replace (@eq B.A) with (@eq A); auto. ring.
    - hnf; intros.
      rewrite mnth_mrowScale_mul; auto; try lia. simpl. elim_bool; subst.
      apply inv_self.
      unfold Aeq. replace (@eq B.A) with (@eq A); auto. ring.
  Qed.


  (* ******************************************************************* *)
  (** ** 某列的第一个非零元的行号 *)
  
  (* 第y列的从n-i开始向下的第一个非零元的行号，找不到时返回 n *)
  Fixpoint firstNonzero {n} (MA: smat n) (i: nat) (y: nat) :=
    match i with
    | O => n
    | S i' =>
        (* 递归时 i 从大到小，而 n-i 是从小到达 *)
        if (decidable (MA $ (n - i) $ y) 0)
        then firstNonzero MA i' y
        else (n - i)%nat
    end.

  (* 非零元行号最小值是 n - i *)
  Lemma firstNonzero_min: forall {n} (MA : smat n) (i j : nat), firstNonzero MA i j >= n - i.
  Proof.
    intros. induction i; simpl; try lia.
    destruct (decidable (MA $ (n - S i) $ j) 0); lia. 
  Qed.

  (* 非零元行号最大值是 n *)
  Lemma firstNonzero_max: forall {n} (MA : smat n) (i j : nat), firstNonzero MA i j <= n.
  Proof.
    intros. induction i; simpl; try lia.
    destruct (decidable (MA $ (n - S i) $ j) 0); lia. 
  Qed.


  (* ******************************************************************* *)
  (** ** 向下消元 *)
  
  (* 对矩阵MA的(i,j)元开始向下消元，返回（变换阵，变换结果）*)
  Fixpoint elimDown {n} (MA: smat n ) (i: nat) (j: nat) : smat n * smat n :=
    match i with
    | O => (I, MA)
    | S i' =>
        (* 递归时 i 从大到小，而 n-i 是从小到大 *)
        (* 将第 j 行的 -Ma[n-i,j] 倍加到第 n-i 行 *)
        let E1 := mrowAdd (n - i) j (- (MA $ (n - i) $ j))%A in
        let (E2, MT) := elimDown (E1 * MA) i' j in
        (E2 * E1, MT)
    end.
  
  (* 对MA向下消元得到 (E,MA')，则 E * MA = MA' *)
  Lemma elimDown_mult_eq : forall {n} (MA : smat n) (x cur : nat),
      x < n -> cur < n - x ->
      (fst (elimDown MA cur x) * MA) == snd (elimDown MA cur x).
  Proof.
    intros. generalize dependent MA. induction cur.
    - intros. simpl. apply mmul_1_l.
    - assert (cur < n - x). lia.
      intros. simpl. destruct elimDown eqn:eq. simpl in *.
      specialize (IHcur H1 (mrowAdd (n - S cur) x (- MA $ (n - S cur) $ x)%A * MA)).
      rewrite eq in IHcur; simpl in *.
      rewrite mmul_assoc. auto.
  Qed.

  (* 若MA[x,x]=1，则从(cur,x)向下消元后，前n-cur行的所有元素保持不变 *)
  Lemma elimDown_former_row_keep : forall {n} (MA : smat n) (x cur : nat) i j,
      x < n -> cur < n - x -> MA $ x $ x = 1 -> i < n - cur -> j < n ->
      (snd (elimDown MA cur x)) $ i $ j = MA $ i $ j.
  Proof.
    intros n MA x cur. revert MA x.
    induction cur; auto. intros. simpl.
    destruct (elimDown) eqn:eq; simpl.
    rewrite (pair_eq_imply_snd eq).
    rewrite IHcur; auto; try lia.
    - rewrite mnth_mrowAdd_mul; auto; try lia. elim_bool.
    - rewrite mnth_mrowAdd_mul; auto; try lia. elim_bool.
  Qed.

  (* 若MA[x,x]=1，则从(cur,x)向下消元后，第x列的后n-cur行的所有元素都是0 *)
  Lemma elimDown_latter_row_0 : forall {n} (MA : smat n) (x cur : nat) y,
      x < n -> cur < n - x -> MA $ x $ x = 1 -> y >= n - cur -> y < n ->
      (snd (elimDown MA cur x)) $ y $ x = 0.
  Proof.
    intros n MA x cur. revert MA x.
    induction cur; intros; simpl; try lia.
    bdestruct (Nat.eqb y (n - S cur)).
    - destruct elimDown eqn:eq. simpl. rewrite (pair_eq_imply_snd eq).
      rewrite elimDown_former_row_keep; auto; try lia.
      + rewrite mnth_mrowAdd_mul; auto; try lia.
        elim_bool. subst. rewrite H1. ring.
      + rewrite mnth_mrowAdd_mul; auto; try lia. elim_bool.
    - destruct elimDown eqn: eq. simpl. rewrite (pair_eq_imply_snd eq).
      apply IHcur; auto; try lia. rewrite mnth_mrowAdd_mul; auto; try lia.
      elim_bool.
  Qed.

  (* 向下消元后的前x列左下方都是0 *)
  Lemma elimDown_keep_lowerLeftZeros: forall {n} (MA : smat n) (x cur : nat),
      x < n -> cur < n - x -> MA $ x $ x = 1 -> lowerLeftZeros MA x -> 
      lowerLeftZeros (snd (elimDown MA cur x)) x.
  Proof.
    intros n MA x cur. revert MA x. induction cur; intros; simpl; auto.
    destruct elimDown eqn: eq. simpl. rewrite (pair_eq_imply_snd eq).
    unfold lowerLeftZeros in *; intros.
    specialize (IHcur (mrowAdd (n - S cur) x (- MA $ (n - S cur) $ x)%A * MA) x H).
    bdestruct (cur <? n - x).
    - apply IHcur; auto.
      + rewrite mnth_mrowAdd_mul; auto; try lia. elim_bool.
      + intros. rewrite mnth_mrowAdd_mul; auto; try lia. elim_bool.
        rewrite !(H2 _ j0); auto. ring.
    - rewrite elimDown_former_row_keep; try lia.
  Qed.

  (* 向下消元后的前x列左下方都是0 (？？） *)
  Lemma elimDown_lowerLeftZeros: forall {n} (MA : smat n) (x : nat),
      x < n -> MA $ x $ x = 1 -> lowerLeftZeros MA x -> 
      lowerLeftZeros (snd (elimDown MA (n - x - 1) x)) (x + 1).
  Proof.
    intros. unfold lowerLeftZeros. intros. bdestruct (j =? x).
    - subst. apply elimDown_latter_row_0; auto; lia. 
    - apply elimDown_keep_lowerLeftZeros; auto; lia.
  Qed.


  (* ******************************************************************* *)
  (** ** 化为行阶梯形 *)
  
  (* 化为行阶梯形 *)
  Fixpoint rowEchelon {n} (MA: smat n) (i: nat) : option (smat n * smat n) :=
    match i with
    | O => Some (I, MA)
    | S i' =>
        (* 从(n-i,n-i)开始向下找出第1个非零元的行号。若找不到返回n；初值是0列0行 *)
        let r := firstNonzero MA i (n - i) in
        (* 若返回 n，则说明该列没有非零元，则该矩阵不可逆  *)
        if (r =? n) then None
        else
          (* 交换 n-i 和 r 行 *)
          let E0 := mrowSwap (n - i) r in
          let A1 := E0 * MA in
          (* A1 的 (n-i, n-i) 化成1 *)
          let E1 := (mrowScale (n - i) (/ (A1 $ (n - i) $ (n - i)))) in
          let A2 := E1 * A1 in
          (* A2 从 (i-1, n-i) 开始向下消元 *)
          let (E2, MT) := elimDown A2 (i - 1) (n - i) in
          (* 递归 *)
          match rowEchelon MT i' with
          | None => None
          | Some (E3, MT') => Some (E3 * E2 * E1 * E0, MT')
          end
    end.

  (* 阶梯形矩阵 f(MA) = Some (E,EA) -> E * MA = EA *)
  Lemma rowEchelon_mult_eq: forall {n} (MA : smat n) (i : nat) (E EA : smat n),
      i <= n -> rowEchelon MA i = Some (E, EA) -> E * MA == EA.
  Proof.
    intros n MA i. revert MA. induction i; intros.
    - simpl in H0. inversion H0. subst. apply mmul_1_l.
    - unfold rowEchelon in H0; fold (@rowEchelon n) in H0.
      (* 非零元行号 =? n *)
      elim_bool.
      (* elimDown的结果 *)
      destruct elimDown as [E2 MT] eqn:Heqp.
      (* 命名 mrowSwap 矩阵，命名 mrowScale 矩阵 *)
      remember (mrowSwap (n - S i) (firstNonzero MA (S i) (n - S i)) * MA) as A1.
      remember (mrowScale (n - S i) (/ (A1 $ (n - S i) $ (n - S i))) * A1) as A2.
      (* 分解H0，以便利用归纳假设 *)
      destruct rowEchelon as [[E3 MT']|] eqn: H2; try easy.
      apply IHi in H2; try lia.
      apply Some_pair_eq in H0. destruct H0 as [H01 H02].
      rewrite <- H01, <- H02, <- H2.
      rewrite !mmul_assoc. rewrite <- HeqA1. rewrite <- HeqA2.
      (* 使用 elimDown不变式 *)
      rewrite (pair_eq_imply_fst Heqp). rewrite elimDown_mult_eq; try lia.
      rewrite Heqp. simpl. reflexivity.
  Qed.

  (* 化行阶梯矩阵 f(X) = Some(E,EA), 则 EA 是对角线1 *)
  Lemma rowEchelon_to_diag_ones : forall {n} (X : smat n) (i : nat) (E EA : smat n),
      i <= n -> diagonalOnes X (n - i) ->
      rowEchelon X i = Some (E, EA) -> diagonalOnes EA n.
  Proof.
    intros n X i. revert X. induction i; intros.
    - simpl in H1. inversion H1. subst.
      replace n with (n - 0)%nat by lia. auto.
    - unfold diagonalOnes. intros.
      unfold rowEchelon in H1; fold (@rowEchelon n) in *.
      destruct (elimDown) eqn: Heqp.
      elim_bool.
      destruct (rowEchelon s0 i) eqn: Heqo; try easy.
      destruct (p) eqn: ?.
      remember (mrowSwap (n - S i) (firstNonzero X (S i) (n - S i)) * X) as A0.
      remember (mrowScale (n - S i) (/ (A0 $ (n - S i) $ (n - S i))) * A0) as A1.
      inversion H1. apply IHi in Heqo; auto; try lia.
      + rewrite <- H7. auto.
      + unfold diagonalOnes. intros.
        rewrite (pair_eq_imply_snd Heqp).
        rewrite elimDown_former_row_keep; auto; try lia.
        * rewrite HeqA1.
          rewrite mnth_mrowScale_mul; auto; try lia. elim_bool.
          ** rewrite H9.
             (* rewrite field_mulInvL; auto. *)
             rewrite inv_self; auto.
          ** rewrite HeqA0.
             assert (firstNonzero X (S i) (n - S i) <= n)
               by apply firstNonzero_max.
             assert (firstNonzero X (S i) (n - S i) >= n - S i)
               by apply firstNonzero_min.
             rewrite mnth_mrowSwap_mul; auto; try lia.
             simpl in *. elim_bool.
             rewrite H0; auto; try lia.
        * rewrite HeqA1. rewrite mnth_mrowScale_mul; try lia. elim_bool.
          rewrite inv_self; auto.
  Qed.

  (* 行阶梯矩阵变换，使得其左下角全是0 *)
  Lemma rowEchelon_to_lowerLeftZeros: forall {n} (X : smat n) (i : nat) (E EA : smat n),
      i <= n -> lowerLeftZeros X (n - i) ->
      rowEchelon X i = Some (E, EA) -> lowerLeftZeros EA n.
  Proof.
    intros n X i. revert X. induction i; intros.
    - simpl in H1. inversion H1; subst. replace n with (n - 0)%nat; auto; lia.
    - unfold rowEchelon in H1; fold (@rowEchelon n) in H1. elim_bool.
      destruct elimDown as [E2 MT] eqn: H3.
      destruct rowEchelon as [[E3 MT']|] eqn: H4; try easy.
      destruct (Some_pair_eq H1) as [H11 H12]; clear H1.
      rewrite <- H12. apply IHi in H4; auto; try lia.
      hnf; intros.
      assert (firstNonzero X (S i) (n - S i) <= n) by apply firstNonzero_max.
      assert (firstNonzero X (S i) (n - S i) >= n - S i) by apply firstNonzero_min.
      rewrite (pair_eq_imply_snd H3).
      replace (S i - 1)%nat with (n - (n - S i) - 1)%nat by lia. 
      apply elimDown_lowerLeftZeros with (x := (n - S i)%nat); auto; try lia.
      + rewrite mnth_mrowScale_mul; auto; try lia.
        elim_bool. rewrite inv_self; auto.
      + unfold lowerLeftZeros in *; intros.
        rewrite mnth_mrowScale_mul; auto; try lia. elim_bool.
        * rewrite !mnth_mrowSwap_mul; auto; try lia.
          elim_bool. rewrite (H0 _ j0); try lia. ring.
        * rewrite !mnth_mrowSwap_mul; auto; try lia. elim_bool. apply H0; try lia.
  Qed.

  Theorem rowEchelon_correct: forall {n} (A E EA : smat n),
      rowEchelon A n = Some (E, EA) -> E * A == EA /\ normedUpperTri EA.
  Proof.
    intros. split.
    - apply rowEchelon_mult_eq in H; eauto.
    - unfold normedUpperTri. split.
      + apply rowEchelon_to_diag_ones in H; auto. hnf; intros; lia.
      + apply rowEchelon_to_lowerLeftZeros in H; auto. hnf; intros; lia.
  Qed.


  (* ******************************************************************* *)
  (** ** 向上消元 *)
  
  (* 第(i,x)向上消元 *)
  Fixpoint elimUp {n} (MA: smat n) (x: nat) (i: nat) :=
    match i with
    | O => (I, MA)
    | S i' =>
        (* 第 x 行的 - (MA[i',x]) 倍加到第 i' 行 *)
        let ee := mrowAdd i' x (- (MA $ i' $ x))%A in
        let (E, MT) := elimUp (ee * MA) x i' in
        (E * ee, MT)
    end.

  (* fst (f MA) * MA = snd (f MA) *)
  Lemma elimUp_mult_eq : forall {n} (MA E MT : smat n) (x i : nat),
      x < n -> i <= x -> elimUp MA x i = (E, MT) -> E * MA == MT.
  Proof.
    intros. revert MA E MT H1. induction i; intros.
    - simpl in H1. inversion H1. apply mmul_1_l.
    - simpl in H1. destruct (elimUp) as [E' MT'] eqn: H2.
      inversion H1. apply IHi in H2; try lia.
      rewrite mmul_assoc. rewrite <- H5. auto.
  Qed.

  (* ************************************************************************ *)
  (* 向上消元后是上三角矩阵 *)
  Lemma elimUp_keep_normedUpperTri : forall {n} (MA : smat n) (x i : nat),
      x < n -> i <= x -> normedUpperTri MA ->
      normedUpperTri (snd (elimUp MA x i)). 
  Proof.
    intros n MA x i. revert MA x. induction i; intros; auto. simpl.
    destruct elimUp as [E MT] eqn: H2.
    simpl. rewrite (pair_eq_imply_snd H2).
    apply IHi; auto; try lia.
    apply mrowAdd_keep_normedUpperTri; auto.
  Qed.

  (* 上消元的元素保持性 *)
  Lemma elimUp_lower_rows_keep : forall {n} (MA : smat n) (x i : nat) i' j,
      x < n -> i <= x -> normedUpperTri MA -> i' < n -> i' >= i -> j < n ->
      (snd (elimUp MA x i)) $ i' $ j = MA $ i' $ j.
  Proof.
    intros n MA x i. revert MA x. induction i; intros; auto. simpl.
    destruct (elimUp) as [E MT] eqn: H5. simpl.
    rewrite (pair_eq_imply_snd H5).
    rewrite IHi; auto; try lia.
    - rewrite mnth_mrowAdd_mul; auto; try lia. elim_bool.
    - apply mrowAdd_keep_normedUpperTri; auto; try lia.
  Qed.

  (* 上消元后该列上方元素为 0 *)
  Lemma elimUp_upper_rows_to_0 : forall {n} (MA : smat n) (x i : nat) i',
      x < n -> i <= x -> normedUpperTri MA -> i' < i ->
      (snd (elimUp MA x i)) $ i' $ x = 0.
  Proof.
    intros n MA x i. revert MA x. induction i; intros; auto; try lia. simpl.
    destruct elimUp as [E T] eqn: H3. simpl. rewrite (pair_eq_imply_snd H3).
    bdestruct (i =? i').
    - rewrite H4 in *. rewrite elimUp_lower_rows_keep; try lia.
      + rewrite mnth_mrowAdd_mul; auto; try lia. elim_bool.
        hnf in H1. destruct H1 as [H1 H1']. rewrite H1; auto. ring.
      + apply mrowAdd_keep_normedUpperTri; auto; try lia.
    - apply IHi; auto; try lia. apply mrowAdd_keep_normedUpperTri; auto; try lia.
  Qed.

  (* 上消元后，右上角全是 0 *)
  Lemma elimUp_keep_upperRightZeros: forall {n} (MA : smat n) (x i L : nat),
      x < n -> i <= x -> L < n - x -> normedUpperTri MA -> upperRightZeros MA L ->  
      upperRightZeros (snd (elimUp MA x i)) L.
  Proof.
    intros n MA x i. revert MA x. induction i; intros; auto. simpl.
    destruct elimUp as [E MT] eqn: H4. simpl. rewrite (pair_eq_imply_snd H4).
    apply IHi; auto; try lia.
    - apply mrowAdd_keep_normedUpperTri; auto; lia.
    - hnf; intros. rewrite mnth_mrowAdd_mul; auto; try lia. elim_bool.
      subst. rewrite !(H3 _ j); auto; try lia. ring.
  Qed.

  (* 上消元后，右上角元素都是 0 *)
  Lemma elimUp_keep_upperRightZeros_entend: forall {n} (MA : smat n) (x : nat),
      x < n -> normedUpperTri MA -> upperRightZeros MA (n - x - 1) ->  
      upperRightZeros (snd (elimUp MA x x)) (n - x).
  Proof.
    intros. hnf; intros.
    bdestruct (j =? x).
    - subst. apply elimUp_upper_rows_to_0; auto; lia.
    - rewrite elimUp_keep_upperRightZeros
        with (L := (n - x - 1)%nat); auto; lia.
  Qed.
  

  (* ******************************************************************* *)
  (** ** 最简行阶梯形矩阵 *)

  (* 化为最简行阶梯形矩阵 *)
  Fixpoint minRowEchelon {n} (MA: smat n) (i: nat) :=
    match i with
    | O => (I, MA)
    | S i' =>
        let (E, MT) := elimUp (MA) i' i' in
        let (E', MT') := minRowEchelon MT i' in
        (E' * E, MT')
    end.

  (* minRowEchelon不变式 *)
  Lemma minRowEchelon_mult_eq: forall {n} (MA : smat n) (i : nat),
      i <= n -> fst (minRowEchelon MA i) * MA == snd (minRowEchelon MA i).
  Proof.
    intros n MA i. revert MA. induction i; intros; simpl. apply mmul_1_l.
    destruct elimUp as [E MT] eqn: H1.
    destruct minRowEchelon as [E' MT'] eqn: H2. simpl.
    apply elimUp_mult_eq in H1; auto.
    rewrite mmul_assoc. rewrite H1.
    rewrite (pair_eq_imply_fst H2). rewrite (pair_eq_imply_snd H2).
    apply IHi. lia.
  Qed.

  (* minRowEchelon 保持上三角 *)
  Lemma minRowEchelon_keep_upper_triangle: forall {n} (MA : smat n) (i : nat),
      i <= n -> normedUpperTri MA -> normedUpperTri (snd (minRowEchelon MA i)).
  Proof.
    intros n MA i. revert MA. induction i; intros; simpl; auto.
    destruct elimUp as [E MT] eqn: HE1.
    destruct minRowEchelon as [E' MT'] eqn: HE2. simpl.
    rewrite (pair_eq_imply_snd HE2). apply IHi; auto; try lia.
    rewrite (pair_eq_imply_snd HE1).
    apply elimUp_keep_normedUpperTri; auto.
  Qed.

  (* minRowEchelon 后的右上角是0 *)
  Lemma minRowEchelon_to_upperRightZeros: forall {n} (MA : smat n) (i : nat),
      i <= n -> normedUpperTri MA -> upperRightZeros MA (n - i) -> 
      upperRightZeros (snd (minRowEchelon MA i)) n.
  Proof.
    intros n MA i. revert MA. induction i; intros; simpl.
    - replace n with (n - 0)%nat by lia; auto.
    - destruct elimUp as [E MT] eqn: HE1.
      destruct minRowEchelon as [E' MT'] eqn: HE2. simpl.
      rewrite (pair_eq_imply_snd HE2). apply IHi; auto; try lia.
      + rewrite (pair_eq_imply_snd HE1).
        apply elimUp_keep_normedUpperTri; auto.
      + rewrite (pair_eq_imply_snd HE1).
        apply elimUp_keep_upperRightZeros_entend; auto.
        replace (n - i - 1)%nat with (n - S i)%nat by lia; auto.
  Qed.

  (* minRowEchelon 的结果是单位阵 *)
  Lemma minRowEchelon_eq_I : forall {n} (MA : smat n),
      normedUpperTri MA -> snd (minRowEchelon MA n) == I.
  Proof.
    intros; hnf; intros. unfold I, Matrix.mat1; simpl. elim_bool; subst.
    - apply minRowEchelon_keep_upper_triangle; auto.
    - bdestruct (j <? i). (* 分成上下三角考虑 *)
      + (* 左下角 j < i *)
        apply minRowEchelon_keep_upper_triangle; auto.
      + (* 右上角 j > i *)
        apply minRowEchelon_to_upperRightZeros; auto; try lia.
        hnf; intros. lia.
  Qed.


  (* ******************************************************************* *)
  (** ** 计算逆矩阵 *)

  (* 计算逆矩阵 *)
  Definition minvert {n} (MA: smat n) :=
    (* 先化行阶梯形，再化行最简阶梯形 *)
    match rowEchelon MA n with
    | None => None
    | Some (E, MT) => Some (fst (minRowEchelon MT n) * E)
    end.

  Theorem minvert_correct: forall {n} (MA E : smat n),
      minvert MA = Some E -> E * MA == I.
  Proof.
    intros. unfold minvert in H.
    destruct rowEchelon as [[E1 T1]|] eqn: HE1; try easy.
    destruct minRowEchelon as [E2 T2] eqn: HE2; simpl in *. inversion H.
    (* E1 * MA = T1 *)
    apply rowEchelon_correct in HE1. destruct HE1 as [HE1 HE1'].
    apply minRowEchelon_eq_I in HE1'.   (* snd (minRowEchelon T1) = I *)
    rewrite mmul_assoc; rewrite HE1.
    rewrite (pair_eq_imply_fst HE2).    (* fst (minRowEchelon T1) * T1 = I *)
    rewrite minRowEchelon_mult_eq.      (* snd (minRowEchelon T1) = I *)
    auto. auto.
  Qed.

  (* minvert若有值，则原矩阵是可逆的 *)
  Theorem minvert_is_invertible: forall {n} (MA E : smat n),
      minvert MA = Some E -> invertible MA.
  Proof.
    intros. apply minvert_correct in H. hnf.
    exists E. split; auto. apply l_inv_r_inv; auto.
  Qed.

  (* minvert若有值，则结果矩阵是可逆的 *)
  Theorem minvert_inv_is_invertible: forall {n} (MA E : smat n),
      minvert MA = Some E -> invertible E.
  Proof.
    intros. apply minvert_correct in H. hnf.
    exists MA. split; auto. apply l_inv_r_inv; auto.
  Qed.

  (* 左消去律 *)
  Theorem matrix_cancel_l: forall {n} (M N P : smat n),
      invertible P -> M * P == N * P -> M == N.
  Proof.
    intros.
    destruct H as [P' [HP1 HP2]].
    assert (M * P * P' == N * P * P'). rewrite H0; reflexivity.
    rewrite !mmul_assoc in H. rewrite HP1 in H. rewrite !mmul_1_r in H. auto.
  Qed.

  (* 右消去律 *)
  Theorem matrix_cancel_r: forall {n} (M N P : smat n),
      invertible P -> P * M == P * N -> M == N.
  Proof.
    intros.
    destruct H as [P' [HP1 HP2]].
    assert (P' * P * M == P' * P * N). rewrite !mmul_assoc. rewrite H0; reflexivity.
    rewrite HP2 in H. rewrite !mmul_1_l in H. auto.
  Qed.

  (* N' * M' * M * N = I *)
  Corollary minvert_eq1: forall {n} (M N M' N': smat n),
      minvert M = Some M' -> minvert N = Some N' -> N' * M' * M * N == I.
  Proof.
    intros. apply minvert_correct in H. apply minvert_correct in H0.
    rewrite (mmul_assoc N'). rewrite H. rewrite mmul_1_r. auto.
  Qed.

  (* M = (M')' *)
  Theorem minvert_minvert: forall {n} (M M' M'' : smat n),
      minvert M = Some M' ->
      minvert M' = Some M'' ->
      M == M''.
  Proof.
    intros.
    apply minvert_correct in H,H0.
    assert (M'' * M' * M == M). rewrite H0. apply mmul_1_l.
    rewrite mmul_assoc in H1. rewrite H in H1. rewrite mmul_1_r in H1. easy.
  Qed.


  (* ******************************************************************* *)
  (** ** 其他性质 *)

  (* 取出“对角矩阵(c,c,...,c) 左乘以某个矩阵”的元素 *)
  Lemma mnth_mdiagonal_mul: forall {n} (c : A) (i j : nat), forall MA: smat n, 
      i < n -> j < n ->
      ((@f2m n n (fun i j => (if Nat.eqb i j then c else 0))) * MA) $ i $ j
      = (c * MA $ i $ j)%A.
  Proof.
    intros. rewrite mnth_mmul; auto.
    apply seqsum_unique with (i := i); auto; intros; simpl; elim_bool.
  Qed.

  (* 对角矩阵(c,c,...,c) 是可逆的 *)
  Lemma mdiagonal_invertible: forall {n} i c,
      i < n -> c <> 0 ->
      invertible (@f2m n n (fun i j => (if Nat.eqb i j then c else 0))).
  Proof.
    intros. hnf. exists (f2m (fun i j => (if Nat.eqb i j then (/ c) else 0))). split.
    - hnf; intros. rewrite mnth_mdiagonal_mul; auto. simpl.
      elim_bool. rewrite commutative. apply inv_self.
      unfold Aeq. replace (@eq B.A) with (@eq E.A); auto. ring.
    - hnf; intros. rewrite mnth_mdiagonal_mul; auto. simpl.
      elim_bool. apply inv_self.
      unfold Aeq. replace (@eq B.A) with (@eq E.A); auto. ring.
  Qed.
  
End MatrixInv.
