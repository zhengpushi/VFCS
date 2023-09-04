(*
 Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose     : C code generation (version 2)
  author      : ZhengPu Shi
  date        : 2022.09.16

  remark      :
  1. 考虑simulink中的模块和组装，如何在Coq中实现。
  2. 按照数电中的思想，根据模块的输出是否只与输入有关，将模块分为两种类型
    组合的：输出只与输入有关。
    时序的：输出与当前输入和之前的状态有关。
  3. 主要面向嵌入式系统的典型场景（以飞控为例）：
    a. 业务流程：
      初始化软硬件（会启动中断）。
      主程序进入循环：从全局变量取出数据，然后再修改某些变量。
        比如修改内存变量，根据传感器数据进行姿态解算。
        比如修改外设变量，控制电机等。
      定时执行子任务（由节拍或时钟中断触发）：采集传感器数据、控制外设等。
        比如修改外设变量，控制电机。（可以在主程序，也可在子程序）
    b. 中断会引起共享变量的问题
      比如两个中断处理程序和一个主程序，这三者都可能修改某个全局变量。
      简化的情形是：每个全局变量的修改仅由一个isr(interrupt service routine)负责，
        其读取可以是多方的。
  4. 主要设计思想
    a. 关注数学、工程的正确性，以及生成C代码。衡量指标是：能验证、能合成。
    b. 类似于Simulink的模块与组装，但强调验证。
    c. 暂不考虑共享变量引起的问题，首先保证各个子程序（对应一个模块）都是正确的。
    d. 支持组合与时序两种方式的模块，使用一个节拍信号来控制。
      节拍信号表示定时调用。
      每执行一次，模块内部状态会变化一次。
      还可以提供复位端口以便回到初始值。
*)

(* Coq实现的一些设想
  1. 模块有内部和外部两方面的特征：
    外部特征是输入输出端口，每个端口是不同数据类型，可包括数组、矩阵等；
    内部特征是：输出逻辑、当前状态
  2. 所以重点解决的问题有：
    a. 如何支持多样的数据类型
    b. 将输出逻辑建模为函数式还是命令式？
      函数式方便验证，命令式方便代码生成。
      函数式方便进行高层优化。
    c. 每个模块内部的当前状态，可建模为一个映射。
  3. 具体问题
    a. 异构数据类型问题
    b. 数组和矩阵的表示问题（可考虑用映射，有别于NatFun）
      注意到：OCaml会将尾递归优化为循环函数，效率高。
    c. IMP模型
    d. DPIA中处理矩阵的做法，能否用于处理C中的其他内容（表达式、控制结构、函数）？
      DPIA重点关注了for循环
    e. SF其他篇的技术。
    f. 关于IMP模型的验证，可能需要HOARE逻辑
    g. 因为命令式模型不便于优化，但IMP语言的这种建模，难道就没有优化的空间吗？
      难度到底有多大？
      既然函数式程序的map、fold、list编程技术有很好的优化可能，
      那么命令式程序能否再反过来对应到这些结构呢？
*)

(* 关于数组的一些想法：
既然C、OCaml等语言都自带了数组数据类型，那么Coq中能否也设法做一种内置的数组数据类型呢
要求：
  构造式的，能证明
思路：
1. 可以仿照 Map 的实现，方便验证和计算。
2. 可以公理化的实现，然后映射到 Map 上，key 可以使用 nat。

老师 2022.09.20 讲OCaml时，(数组，列表，seq，hash）这几样东西用在一起，
可以借鉴，Hash就像是 TotalMap。
OCaml提供的 Hashtbl.of_seq 函数，原理可能是增加了一个分量，该分量是地址，
  总之，内部就是建立了一种比较，连续的比较就能排序。
  思路比较简单：数组按下标访问，而list是链表模型，需要借助hash、数组等加快访问。
*)

(** 关于记录：
OCaml中用 a.x <- y 为记录的字段更新内容。这说明记录和普通数据的管理方式有些区别。
所以设计时需要考虑
*)

Require Import List. Import ListNotations.
Require Import Nat.
Require Import StrExt.
Require Import RExt.
Open Scope string_scope.

(* 语法 *)

(** 首先是实数表达式的AST *)

Inductive op1 :=
(* | op1_ropp *)
(* | op1_rinv *)
| op1_fun : string -> op1
.

Definition op1_fun_db : list (string * (R->R)) :=
  [("sin", sin); ("cos", cos); ("sqrt", sqrt)].
Definition op1_fun_def : string * (R->R) := ("def1", fun x => R0).

Inductive op2 :=
| op2_rplus
| op2_rminus
| op2_rmult
| op2_rdiv
| op2_fun : string -> op2.

Definition op2_fun_db : list (string * (R->R->R)) :=
  [("plus", Rplus); ("minus", Rminus)].
Definition op2_fun_def : string * (R->R->R) := ("def2", fun x y => R0).

Fixpoint alst_lookup {A} (l:list (string * A)) (key:string) : option A :=
  match l with
  | (k,v) :: tl => if String.eqb k key then Some v else alst_lookup tl key
  | [] => None
  end.

Inductive aexp :=
| rvar : string -> aexp
| rconst : R -> aexp
| rpow : aexp -> nat -> aexp
| runary : op1 -> aexp -> aexp
| rbinary : op2 -> aexp -> aexp -> aexp.

(* 语义 *)
Fixpoint aeval (a : aexp) (ctx : string -> R) : R :=
  match a with
  | rvar x => ctx x
  | rconst r => r
  | rpow a1 n => pow (aeval a1 ctx) n
  | runary op1 a1 =>
      match op1 with
      (* | op1_ropp => - (aeval a1 ctx) *)
      (* | op1_rinv => / (aeval a1 ctx) *)
      | op1_fun x =>
          match alst_lookup op1_fun_db x with
          | Some op => op (aeval a1 ctx)
          | None => (snd op1_fun_def) (aeval a1 ctx)
          end
      end
  | rbinary op2 a1 a2 =>
      match op2 with
      | op2_rplus => (aeval a1 ctx) + (aeval a2 ctx)
      | op2_rminus => (aeval a1 ctx) - (aeval a2 ctx)
      | op2_rmult => (aeval a1 ctx) * (aeval a2 ctx)
      | op2_rdiv => (aeval a1 ctx) / (aeval a2 ctx)
      | op2_fun x => 
          match alst_lookup op2_fun_db x with
          | Some op => op (aeval a1 ctx) (aeval a2 ctx)
          | None => (snd op2_fun_def) (aeval a1 ctx) (aeval a2 ctx)
          end
      end
  end.

(* C表达式 *)
Section cgen.
  
  Variable R2str : R -> string.

  Fixpoint a2str (a : aexp) : string :=
    match a with
    | rvar x => " " ++ x ++ " "
    | rconst r => " " ++ R2str r ++ " "
    | rpow a1 n => "(" ++ a2str a1 ++ ")^" ++ (nat2str n)
    | runary op1 a1 =>
        match op1 with
        (* | op1_ropp => "- (" ++ (a2str a1) ++ ")" *)
        (* | op1_rinv => "/ (" ++ (a2str a1) ++ ")" *)
        | op1_fun x =>
            let x' : string :=
              match alst_lookup op1_fun_db x with
              | Some _ => x | None => (fst op2_fun_def)
              end in
            x' ++ "(" ++ (a2str a1) ++ ")"
        end
    | rbinary op2 a1 a2 =>
        match op2 with
        | op2_rplus => (a2str a1) ++ "+" ++ (a2str a2)
        | op2_rminus => (a2str a1) ++ "- (" ++ (a2str a2) ++ ")"
        | op2_rmult => (a2str a1) ++ "* (" ++ (a2str a2) ++ ")"
        | op2_rdiv => (a2str a1) ++ "/ (" ++ (a2str a2) ++ ")"
        | op2_fun x => 
            let x' : string :=
              match alst_lookup op2_fun_db x with
              | Some _ => x | None => (fst op2_fun_def)
              end in
            x' ++ "(" ++ (a2str a1) ++ ", " ++ (a2str a1) ++ ")"
        end
    end.
End cgen.

(** 语法助记符 *)
Declare Custom Entry aexp.

Notation "<{ e }>" := e (e custom aexp at level 99).
Notation "( x )" := x (in custom aexp, x at level 99).
Notation "x" := x (in custom aexp at level 0, x constr at level 0).
(* Notation "- x" := (runary op1_ropp x) (in custom aexp at level 1, left associativity). *)
(* Notation "/ x" := (runary op1_rinv x) (in custom aexp at level 1, left associativity). *)
Notation "'\F' op x" := (runary (op1_fun op) x) (in custom aexp at level 5, right associativity).
Notation "x + y" := (rbinary op2_rplus x y) (in custom aexp at level 10, left associativity).
Notation "x - y" := (rbinary op2_rminus x y) (in custom aexp at level 10, left associativity).
Notation "x * y" := (rbinary op2_rmult x y) (in custom aexp at level 4, left associativity).
Notation "x / y" := (rbinary op2_rdiv x y) (in custom aexp at level 4, left associativity).
Notation "op x y" := (rbinary op2_fun op x y) (in custom aexp at level 1, left associativity).
Notation "{ x }" := x (in custom aexp at level 1, x constr).
Coercion rvar : string >-> aexp.
Coercion rconst : R >-> aexp.

(** 一些方便的操作  *)
Definition OP1 (op:string) : aexp->aexp := runary (op1_fun op).
Definition OP2 (op:string) : aexp->aexp->aexp := rbinary (op2_fun op).

Compute OP1 "sin".

(* Definition x : string := "x". *)
(* Definition y : string := "y". *)
(* Definition z : string := "z". *)

(* Hint Unfold x : core. *)
(* Hint Unfold y : core. *)
(* Hint Unfold z : core. *)


(* 示例1 *)
Section test.
  (* 给出表达式的AST  *)
  Let ex1 : aexp := <{"x" + R0 + "y"*"z"*R1 }>.
  Print ex1.

  (* 验证数学性质 *)
  Let ex1_spec : forall ctx,
      let x := ctx "x" in
      let y := ctx "y" in
      let z := ctx "z" in
      aeval ex1 ctx = (x + y * z)%R.
  Proof. intros. cbv. ring. Qed.

  (* 实数到字符串的转换 *)
  Let R2str (r:R) : string :=
        if (r =? R0)%R then "R0"
        else if (r =? R1)%R then "R1"
             else "Rx".
  Let R2str' (r:R) : string := "Rx".
  
  (* 代码生成 *)
  Open Scope string_scope.
  Compute a2str R2str ex1.      (* 是否可以用Ltac或Coq插件将R常量表达式转换为字符串？ *)
  Compute a2str R2str' ex1.
End test.

(* 示例2 *)
Section test.

  (* 飞控QQ (4.25)
     N = 60 * sqrt (T / (rho * D_p^4 * C_T))
     M = rho * D_p^t * C_M * (N/60)^2
   *)

  Let T := "T".
  Let rho := "rho".
  Let D_p := "D_p".
  Let C_T := "C_T".
  Let C_M := "C_M".

  (* 公式1: N *)
  Section formula1. 

    (* 定义表达式的AST *)
    Let N : aexp :=
          let f1 := <{ T / (rho * {rpow D_p 4} * C_T) }> in
          <{60 * {OP1 "sqrt" f1}}>.
    Compute aeval N.

    (* 校验数学性质（防止AST出错，得到其数学表达式） *)
    Let N_spec : forall ctx,
        let vT := ctx T in
        let vrho := ctx rho in
        let vD_p := ctx D_p in
        let vC_T := ctx C_T in
        let vC_M := ctx C_M in
        aeval N ctx = 60 * sqrt (vT / (vrho * vD_p ^ 4 * vC_T)).
    Proof. intros. cbv. ring. Qed.

    (* 生成C代码 *)
    Compute a2str (fun _ => "000") N.
  End formula1.
End test.

Require Import Extraction.
Definition ex1 : aexp := R0.
Definition ex2 : aexp := <{R0 + R0}>.
Extraction aeval.
Recursive Extraction ex1 aeval a2str.

(** 自定义语法，但是语义映射到 Map *)

(** 含有数组的表达式

 *)
Inductive 

