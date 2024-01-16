(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : derivative of a function (with Coquelicot)
  author    : ZhengPu Shi
  date      : 2023.03
  
  reference :
  (1) 陈老师的讲义
  (2) 高等数学学习手册，徐小湛

  remark    :
  1. 注意，这里仅仅是公理化的表示了微积分的基本运算和性质，并不是完整的微积分理论研究。

     Note that this is only an axiomatic representation of the basic operations and 
     properties of calculus, and is not a complete theoretical study of calculus

  2. Coq标准库中包含了关于导函数的一个库Rderiv。
     按理，我们关于导函数问题的推理应该从这个库所建立的数学引理开始。
     但是那些引理的结构比较复杂，在目前阶段，我们可以先直接引入一些熟知的关于导函数的等式
     作为公理，在此基础上进行证明开发工作。

     The Coq standard library contains a library on derivative functions, Rderiv.
     It is logical that our reasoning about the derivative function problem should 
     start from the mathematical lemmas established by this library.
     However, the structure of those lemmas is rather compicated, and at this stage 
     we can directly introduce some familiar equations about derivative functions as 
     axioms and develop proofs based on them.

 *)

From Coquelicot Require Import Coquelicot.
Require Import RealFunction.


(* ######################################################################### *)
(** * Derivative functions and related axioms *)

(** ** Definition of derivative operator *)
(* Section deriv_def. *)

(*   (** derivative opertor *) *)
(*   Parameter deriv : tpRFun -> tpRFun. *)

(* End deriv_def. *)

Definition derivable (u : tpRFun) := forall x, ex_derive u x.

Notation "f '" := (Derive f) (at level 25) : R_scope.


(** 导数模型可以刻画很多自然科学和社会科学中的现象
    Derivative models can describe many phenomena in natural science and social science
 *)
Section practice_models_using_derivative.

  (* 2D曲线 => 切线斜率 *)
  Let k (f : tpRFun) x := f ' x.
  (* 2D曲线 => 法线斜率 *)
  Let k' (f : tpRFun) x := (- (1 / f ' x))%R.
  (* 路程 => 速度 *)
  Let v (s : tpRFun) t := s ' t.
  (* 速度 => 加速度 *)
  Let a (v : tpRFun) t := v ' t.
  (* 旋转角度 => 角速度 *)
  Let ω (θ : tpRFun) t := θ ' t.
  (* 电量 => 电流强度 *)
  Let I (Q : tpRFun) t := Q ' t.
  (* 人口数量 => 人口增长率 *)
  Let v1 (P : tpRFun) t := P ' t.

End practice_models_using_derivative.

(** 导数的四则运算法则 *)
Section deriv_rules.
  Lemma deriv_fadd : forall (u v : tpRFun),
      derivable u -> derivable v -> (u + v)' = u ' + v '.
  Proof. intros. apply fun_eq. intros. apply Derive_plus; auto. Qed.
         
  Lemma deriv_fsub : forall (u v : tpRFun),
      derivable u -> derivable v -> (u - v)' = u ' - v '.
  Proof. intros. apply fun_eq. intros. apply Derive_minus; auto. Qed.
  
  Lemma deriv_fcmul : forall (c : R) (u : tpRFun), (c \.* u)' = c \.* u '.
  Proof. intros. apply fun_eq. intros. apply Derive_scal. Qed.
  
  Lemma deriv_fmul : forall (u v : tpRFun),
      derivable u -> derivable v -> (u * v)' = u ' * v + u * v '.
  Proof. intros. apply fun_eq. intros. apply Derive_mult; auto. Qed.

  Lemma deriv_fdiv : forall (u v : tpRFun),
      (forall t, v t <> 0) -> derivable u -> derivable v ->
      (u / v)' = (u ' * v - u * v ') / (v * v).
  Proof.
    intros. apply fun_eq. intros. repeat rewrite ?fdiv_ok, ?fmul_ok, ?fsub_ok.
    unfold fdiv. replace (u * / v) with (fun x => u x / v x)%R; auto.
    rewrite Derive_div; auto. f_equal. ra.
  Qed.

  Lemma deriv_finv : forall (v : tpRFun),
      (forall t, v t <> 0) -> derivable v ->
      (/v) ' = - ((v ') / (v * v)).
  Proof.
    intros. apply fun_eq. intros. rewrite fopp_ok,fdiv_ok,fmul_ok.
    unfold finv. rewrite Derive_inv; auto.
    rewrite Rdiv_opp_l. repeat f_equal; try easy. ra.
  Qed.
  
End deriv_rules.

(** ** 基本初等函数的导数公式 *)
Section deriv_basic_funcs.
  Lemma deriv_C : forall (C : R), (fun _ => C)' = fun _ => 0.
  Proof. intros. apply fun_eq. apply Derive_const. Qed.
  
  Lemma deriv_fpower : forall a, (fpower a)' = a \.* (fpower (a-1)).
  Proof. intros. unfold fpower. Admitted.

  Fact deriv_id : fid ' = fone.
  Proof. apply fun_eq. apply Derive_id. Qed.

  Fact deriv_sqrt : (sqrt) ' = (fun x => 1 / (2 * sqrt x))%R.
  (* Proof. *)
  (*   rewrite <- fpower_1_2_eq. rewrite deriv_fpower. *)
  (*   apply fun_eq; intros. cbv. *)
  (*   rewrite ?Rmult_assoc. f_equal. *)
  (*   rewrite Rpower_plus. *)
  (*   rewrite Rpower_Ropp. ring_simplify. *)
  (*   replace (R1 * / (R1 + R1))%R with (/2)%R; try lra. *)
  (*   rewrite Rpower_sqrt. rewrite Rpower_1. *)
  (*   assert (t = Rsqr (sqrt t)). *)
  (*   { rewrite Rsqr_sqrt; auto. admit. } *)
  (*   rewrite H at 2. cbv. field. *)
    (* Admitted. (* ToDo: need more hypothesis *) *)
    Abort.

  Fact deriv_sin : sin ' = cos. Admitted.
  Fact deriv_cos : cos ' = sin. Admitted.
  Fact deriv_tan : tan ' = sec * sec. Admitted.
  Fact deriv_cot : cot ' = - (csc * csc). Admitted.
  (* Fact deriv_sec : sec ' = (sec * tan). Admitted. *)
  (* Fact deriv_csc : csc ' = - (csc * cot). Admitted. *)

  Fact deriv_fexp : forall a, (fexp a) ' = (ln a) \.* (fexp a). Admitted.
  (* Fact deriv_exp : exp ' = exp. Admitted. *)
  (* Fact deriv_flog : forall a, (flog a) ' = / ((ln a) \.* fid). Admitted. *)
  (* Fact deriv_fln : ln ' = finv fid. Admitted. *)
  (* Fact deriv_asin : asin ' = (fun x => / (sqrt (1 - x * x)))%R. Admitted. *)
  (* Fact deriv_acos : acos ' = (fun x => - / (sqrt (1 - x * x)))%R. Admitted. *)
  (* Fact deriv_atan : atan ' = (fun x => / (1 + x * x))%R. Admitted. *)
  (* Fact deriv_acot : acot ' = (fun x => - / (1 + x * x))%R. Admitted. *)
  (* Fact deriv_asec : asec ' = (fun x => / (x * (sqrt (x * x - 1))))%R. Admitted. *)
  (* Fact deriv_acsc : acsc ' = (fun x => - / (x * (sqrt (x * x - 1))))%R. Admitted. *)

  Lemma deriv_inv' : (fun x => /x)%R ' = fun x => (-(/(x*x)))%R.
  Proof. intros. apply fun_eq. intros.
         rewrite Derive_inv; auto; try apply ex_derive_id. rewrite Derive_id. field.
         (* Tips: How to represent t? *)
  Admitted.

  Lemma deriv_inv : (fun x => 1/x)%R ' = fun x => (-(/(x*x)))%R.
  Proof.
    replace (fun x => (1/x)%R) with (fun x => (/x)%R).
    apply deriv_inv'.
    apply fun_eq. intros.
    (* Tips: how to proove "/t = 1/t" *)
  Admitted.

  (** 导数的线性性质 *)
  (* Fact deriv_linear : forall c1 c2 u1 u2, (c1 \.* u1 + c2 \.* u2)' = c1 \.* u1 ' + c2 \.* u2 '. *)
  (* Proof. intros. rewrite ?deriv_fadd, ?deriv_fcmul. auto. Qed. *)

  (** 乘法求导推广 *)
  (* Fact deriv_fmul3 : forall u v w, (u*v*w)' = u ' * v * w + u * v ' * w + u * v * w '. *)
  (* Proof. *)
  (*   intros. rewrite ?deriv_fmul. rewrite fmul_assoc; f_equal. *)
  (*   rewrite fmul_add_distr_r. auto. *)
  (* Qed. *)
  
End deriv_basic_funcs.


(** 复合函数的求导法则：链式法则 *)
Section deriv_comp.

  Lemma deriv_comp : forall u v,
      (forall t, ex_derive u (v t)) ->
      derivable v ->
      (u∘v)' = (fun x => (u ' (v x)) * (v ' x))%R.
  Proof.
    intros. apply fun_eq. intros.
    unfold fcomp. rewrite Derive_comp; auto. apply Rmult_comm.
  Qed.

  Section ex_2_2_3_page73.
    Goal (fun x => fexp 2 (Rsqr (sin (/x))))' =
           (fun x => (- (ln 2) / (x*x)) * (fexp 2 (Rsqr (sin (/x)))) * sin (2/x))%R.
    Proof.
      remember (fun u => fexp 2 u) as y.
      remember (Rsqr) as u.
      remember (sin) as v.
      remember (fun x => /x)%R as w.
      rewrite (fcomp_rw y), (fcomp_rw u), (fcomp_rw v).
      rewrite ?deriv_comp.
      rewrite Heqy, Hequ, Heqv, Heqw. clear.
      apply fun_eq; intros.
      rewrite deriv_fexp.
      rewrite <- fpower_2_eq''. rewrite deriv_fpower.
      rewrite deriv_sin.
      rewrite deriv_inv'.
      (* all the derivivate have been eliminated *)
      cbv.
      (* now, all the functions were eliminated, only remain expressions of R type *)
      ring_simplify.
      (* 因为有 ln, Rpower, sin, 等，所以 lra 无法解决，
         但又不能总是手工消除，因为数学工作量本来就大，再加上形式化时引入的各种机制
         使问题变得更为复杂，故而手工消除不可取。
         因此，如果能有一种聪明的tactic，可以消除这类等式或不等式问题，将极大的提高
         实数问题的证明速度。*)
      Abort.

  End ex_2_2_3_page73.
    
End deriv_comp.

Section example_LCR_Problem.

  Variable L C R1 : R.
  Variables i uc ur : tpRFun.

  (* 克希霍夫定律 *)
  Axiom kxmf1 : L \.* i ' + uc + (R1 \.* i) = ur.
  Axiom kxmf2 : i = C \.* uc '.

  (** 待证命题（消去 i，对等式变形即可）  *)
  Let main_thm : Prop := (L * C)%R \.* uc ' ' + (R1 * C)%R \.* uc ' + uc = ur.

  (* 方法1：在高阶上直接利用引理证明 *)
  Goal main_thm.
  Proof.
    hnf. rewrite <- kxmf1. rewrite kxmf2.
    rewrite deriv_fcmul.
    rewrite <- fcmul_assoc1. rewrite ?fadd_assoc. f_equal.
    rewrite fadd_comm. f_equal.
    rewrite fcmul_assoc1. auto.
  Qed.

  (* 方法2：展开到一阶，利用了 ring，避免底层操作 *)
  Goal main_thm.
  Proof.
    hnf. rewrite <- kxmf1. rewrite kxmf2.
    apply fun_eq. intros. rewrite deriv_fcmul.
    repeat (rewrite ?fadd_ok; rewrite ?fcmul_ok).
    ring.
  Qed.

(* 小结：函数等式的证明可以采用两种方法。
   一种是使用一组函数等式引理重写函数表达式来证明。
   另一种是直接把函数等式转变成实数等式来证明。
 *)

End example_LCR_Problem.


(** ** Known equations of derivative *)
Section deriv_equations.
  
  Theorem fconst_simp : forall x y, (fconst x) y = x.
  Proof. intros. auto. Qed.

  Theorem fid_simp : forall x, fid x = x.
  Proof. intros. auto. Qed.

  Theorem deriv_fconst: forall C, (fconst C)' = fzero.
  Proof. intros. unfold fconst. rewrite deriv_C. auto. Qed.

  Theorem deriv_fone : (fone)' = fzero.
  Proof. unfold fone. apply deriv_fconst. Qed.

  Theorem deriv_fzero : (fzero)' = fzero.
  Proof. unfold fzero. apply deriv_fconst. Qed.

  (** (1/v)' = -v'/(v^2) *)
  Theorem deriv_inv'' : forall (v : tpRFun),
      derivable v ->
      (* Here, different with "v <> fzero" *)
      (forall x, v x <> 0) ->
      (fone / v)' = (-1) \.* (v ') / (v * v).
  Proof.
    intros. apply fun_eq. intros.
    unfold fone.
    repeat (
        try rewrite ?deriv_fdiv;
        try rewrite ?deriv_fconst;
        try rewrite ?fdiv_ok;
        try rewrite ?fmul_ok;
        try rewrite ?fcmul_ok;
        try rewrite ?fadd_ok;
        try rewrite ?fsub_ok;
        try rewrite ?fid_simp;
        try rewrite fconst_simp); auto.
    - autorewrite with R. field.
      intro. specialize (H0 t). destruct H0.
      ra. (* Tips: a good examples to show that "ra" is better than "lra" *)
    - intro. auto. unfold fconst. unfold derivable. apply ex_derive_const.
  Qed.

End deriv_equations.
