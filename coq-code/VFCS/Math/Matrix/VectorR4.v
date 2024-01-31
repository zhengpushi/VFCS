(*
  Copyright 2022 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : 4-dimensional vector on R.
  author    : ZhengPu Shi
  date      : 2023.01

  reference :
  remark    :
 *)

Require Import VectorR.
Open Scope vec_scope.

(* ======================================================================= *)
(** * 4D vector theory *)

(** Equality *)
Section v4eq.

  (** Convert equality of vector to equality of its components *)
  Lemma v4eq_iff : forall (v1 v2 : vec 4),
      v1 = v2 <-> (v1.1 = v2.1 /\ v1.2 = v2.2 /\ v1.3 = v2.3 /\ v1.4 = v2.4).
  Proof.
    intros. split; intros; subst; auto.
    unfold nat2finS in H; simpl in H. destruct H as [H1 [H2 [H3 H4]]].
    apply veq_iff_vnth_nat; intros. unfold nat2fin.
    destruct i; simpl; auto. apply (vnth_sameIdx_imply H1).
    destruct i; simpl; auto. apply (vnth_sameIdx_imply H2).
    destruct i; simpl; auto. apply (vnth_sameIdx_imply H3).
    destruct i; simpl; auto. apply (vnth_sameIdx_imply H4).
    lia.
  Qed.

  (** Convert inequality of vector to inequality of its components *)
  Lemma v4neq_iff : forall (v1 v2 : vec 4),
      v1 <> v2 <-> (v1.1 <> v2.1 \/ v1.2 <> v2.2 \/ v1.3 <> v2.3 \/ v1.4 <> v2.4).
  Proof. intros. unfold not. rewrite v4eq_iff. lra. Qed.

End v4eq.


(** Standard unit vector in space of 4-dimensions *)
Section basis_vector.
  Definition v4i : vec 4 := mkvec4 1 0 0 0.
  Definition v4j : vec 4 := mkvec4 0 1 0 0.
  Definition v4k : vec 4 := mkvec4 0 0 1 0.
  Definition v4l : vec 4 := mkvec4 0 0 0 1.
End basis_vector.
