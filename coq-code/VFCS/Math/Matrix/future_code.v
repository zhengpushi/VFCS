
Require Import NatExt.


(* ==================================== *)
(** ** Kronecker delta function *)
Section kronecker.
  
  Definition kronecker_fun {A} {Azero Aone : A} (i j : nat) :=
    if (i =? j)%nat then Aone else Azero.

End kronecker.
