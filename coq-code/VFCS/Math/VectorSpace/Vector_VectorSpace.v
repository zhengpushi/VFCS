(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : vector forms vector-space
  author    : ZhengPu Shi
  date      : 2024.01

  remark    :
 *)


Require Export Vector.
Require Export VectorSpace.
Require VectorR.

Generalizable Variable A Aadd Azero Aopp Amul Aone Ainv Ale Alt Altb Aleb a2r.

Open Scope A_scope.
Open Scope vec_scope.
Open Scope VectorSpace_scope.

(** ** Vector forms a vector-space *)
Section vectorSpace.
  
  (* Let's have an field *)
  Context `{HField : Field A Aadd Azero Aopp Amul Aone Ainv}.
  Add Field field_inst : (make_field_theory HField).
  
  Infix "+" := Aadd : A_scope.
  Infix "*" := Amul : A_scope.
  Notation "- a" := (Aopp a) : A_scope.
  Notation Asub := (fun a b => a + (- b))%A.
  Infix "-" := Asub : A_scope.

  Notation vzero := (vzero Azero).
  Notation vadd := (@vadd _ Aadd).
  Notation vopp := (@vopp _ Aopp).
  Notation vsub := (@vsub _ Aadd Aopp).
  Notation vcmul := (@vcmul _ Amul).
  Infix "+" := vadd : vec_scope.
  Notation "- v" := (vopp v) : vec_scope.
  Infix "-" := vsub : vec_scope.
  Infix "\.*" := vcmul : vec_scope.
  
  #[export] Instance vec_VectorSpace {n : nat} :
    VectorSpace (V:=vec n) vadd vzero vopp vcmul.
  Proof.
    constructor; try apply vadd_AGroup; intros.
    apply vcmul_1_l. rewrite vcmul_assoc; auto.
    apply vcmul_add. apply vcmul_vadd.
  Qed.
    
End vectorSpace.


Section examples.
  Import VectorR.
  Notation vlcomb := (@vlcomb _ _ vadd vzero vcmul).
  Notation vldep := (@vldep _ Azero _ vadd vzero vcmul).
  Notation vlindep := (@vlindep _ Azero _ vadd vzero vcmul).
  Notation vspan := (@vspan _ _ vadd vzero vcmul).
  Notation vbasis := (@vbasis _ Azero _ vadd vzero vcmul).

  (* Example for "linearly dependent" *)
  Section ex1.
    (* The vectors (2, 2, 5), (3, 3, 12) and (5, 5, −1) are linearly dependent
       elements of the real vector space R3, since
       7(2, 2, 5) − 3(3, 3, 12) − (5, 5, −1) = (0, 0, 0).
       Thus if v1 = (2, 2, 5), v2 = (3, 3, 12) and v3 = (5, 5, −1), then the equation
       c1v1 + c2v2 + c3v3 = 0 is satisfied with c1 = 7, c2 = −3 and c3 = −1.) *)
    Let vecs := Vector.mkvec3 (Azero:=vzero)
                  (mkvec3 2 2 5)
                  (mkvec3 3 3 12)
                  (mkvec3 5 5 (-1)%R).
    Let coefs := mkvec3 7 (-3) (-1).
    
    Example ex1_eq1 : vlcomb coefs vecs = vzero.
    Proof. apply v3eq_iff. cbv. lra. Qed.

    Example ex1_ldep : vldep vecs.
    Proof.
      unfold vldep. exists coefs. split.
      - intro. apply v3eq_iff in H. cbv in H. ra.
      - apply ex1_eq1.
    Qed.
  End ex1.

  (* Example for "basis" *)
  Section ex2.
    (* The vectors (1, 0, 0), (0, 1, 0) and (0, 0, 1) constitute a basis of the 
       vector space R3 of all ordered triples of real numbers. *)
    Let vecs := Vector.mkvec3 (Azero:=vzero)
                  (mkvec3 1 0 0)
                  (mkvec3 0 1 0)
                  (mkvec3 0 0 1).
    Example ex1_vlindep : vlindep vecs.
    Proof.
      unfold vlindep, vldep. intro. destruct H as [v [H H0]]. destruct H.
      apply v3eq_iff in H0. cbv in H0. apply v3eq_iff. cbv. lra.
    Qed.
      
    Example ex1_vspan : vspan vecs.
    Proof.
      unfold vspan. intros. exists (mkvec3 (u.1) (u.2) (u.3)).
      apply v3eq_iff. cbv. lra.
    Qed.
      
    Example ex2_vbasis : vbasis vecs.
    Proof.
      unfold vbasis. split. apply ex1_vlindep. apply ex1_vspan.
    Qed.

  End ex2.

  Section ex3.
    (* (x1, x2, . . . , xn) = x1e1 + x2e2 + · · · + xnen *)
    Variable n : nat.
    Let ei (i : fin n) : vec n := fun j => if finEqdec i j then Aone else Azero.
    Let e : @Vector.vec (vec n) n := fun i => ei i.

    Example ex3_eq : forall (v : vec n), v = vlcomb v e.
    Proof.
      intros. apply veq_iff_vnth. intros.
      unfold vlcomb. unfold vec,vadd,vzero. rewrite vnth_vsum.
      rewrite vsum_unique with (a:=v i) (i:=i); auto.
      - rewrite vnth_vmap2. rewrite vnth_vcmul. unfold e, ei.
        destruct (finEqdec i i); subst. monoid. easy.
      - intros. rewrite vnth_vmap2. rewrite vnth_vcmul. unfold e, ei.
        destruct (finEqdec j i); subst. easy. apply ring_mul_0_r.
    Qed.
        
  End ex3.
  
End examples.
  

