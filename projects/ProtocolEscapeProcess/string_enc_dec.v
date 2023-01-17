(*
  purpose   : encode a string based on ASCII to escape given chars, then decode 
              the result back. And prove these two function are inverse of each
              other.
  author    : ZhengPu Shi
  date      : Oct 23, 2022

  remark    :
  1. Escape processing
    
    black list:     { b1, b2, ..., bn }
          All the chars in it will be encaped.

    fresh list:     { c1, c2, ..., cn}
          All the chars in it will be different with "black list",
          the content have no special meaning.
    
    encape char: x
    
    encode,
        b1 -> x c1
        ...
        bn -> x cn
        x -> x x
    decode,
        x c1 -> Some b1
        ...
        x cn -> Some bn
        x x  -> Some x
        x _  -> None
        a    -> Some a
 *)

Require Import List. Import ListNotations.
Require Import Ascii String.

Open Scope string.

(** * Use config *)
Definition blacklist_raw : list ascii := (["A";"B";"C"])%char.
Definition freshlist_raw : list ascii := (["X";"Y";"Z"])%char.
Definition EscapeChar : ascii := "0"%char.

(** That means:
enc:
    "A" => "0X"
    "B" => "0Y"
    "C" => "0Z"
    "0" => "00"
dec:
    reverse operation of enc.
 *)


(** * Function  *)

Definition blacklist : list ascii := EscapeChar :: blacklist_raw.
Definition freshlist : list ascii := EscapeChar :: freshlist_raw.

(** Check that if a char need to be escape, return the result and 
    corresponding new char. *)
Definition need_enc (a:ascii) : bool * ascii :=
  (fix f (bl fl:list ascii) : bool * ascii :=
     match bl, fl with
     | [], [] => (false, a)
     | x :: bl', y :: fl' =>
         if Ascii.eqb a x
         then (true, y)
         else f bl' fl'
     | _, _ => (false, a)
     end)
    blacklist freshlist.

Compute need_enc "A".

(** Check that if a char need to be reverse escape, return the result and 
    corresponding old char. *)
Definition need_dec (a:ascii) : bool * ascii :=
  (fix f (bl fl:list ascii) : bool * ascii :=
     match bl, fl with
     | [], [] => (false, a)
     | x :: bl', y :: fl' =>
         if Ascii.eqb a x
         then (true, y)
         else f bl' fl'
     | _, _ => (false, a)
     end)
    freshlist blacklist.

Compute need_dec "Z".

(** Encode a string *)
Fixpoint enc (str : string) : string :=
  match str with
  | "" => ""
  | String c str' =>
      let (b,c') := need_enc c in
      if b
      then String EscapeChar (String c' (enc str'))
      else String c' (enc str')
  end.

Compute enc "0".
Compute enc "ABCDE". (* "0X0Y0ZDE" *)

(** ToDo: prove that "enc" will not produce a string contain chars in
    blacklist *)


(** Decode a string *)
Fixpoint dec (str : string) : option string :=
  match str with
  (* empty string *)
  | "" => Some ""
  (* only one char *)
  | String c1 "" =>
      (* if it need to be dec, data error *)
      let (b,c1') := need_dec c1 in
      if b
      then None
      else Some (String c1 "")
  (* at least two chars *)
  | String c1 str' =>
      (* check the first char *)
      match Ascii.eqb c1 EscapeChar with
      (* if the first char is not escape char, go on *)
      | false =>
          match dec str' with
          | Some str'' => Some (String c1 str'')
          | _ => None
          end
      (* if the first char is a escape char, decode it. *)
      | true =>
          match str' with
          | "" => None (* can't come here *)
          | String c2 str'' =>
              (* the second char must be in the freshlist *)
              let (b,c') := need_dec c2 in
              match b with
              | false => None
              | true =>
                  match dec str'' with
                  | Some str''' => Some (String c' str''')
                  | _ => None
                  end
              end
          end
      end
  end
.

Compute enc "ABCDE". (* "0X0Y0ZDE" *)
Compute dec ("0X0Y0ZDE").

Compute (enc "0", dec (enc "0")).
Compute (enc "A", dec (enc "A")).

(** * Prove the correctness *)

(** Properties of need_enc *)
Fact need_enc_output_no_EscapeChar : forall a b c,
    need_enc a = (b,c) -> c <> EscapeChar.
Admitted.

Fact need_enc_true_iff : forall a c,
    need_enc a = (true,c) <-> In c blacklist.
Admitted.

Fact need_dec_0 : need_dec "0" = (true, "0")%char. Admitted.
Fact need_dec_X : need_dec "X" = (true, "A")%char. Admitted.
Fact need_dec_Y : need_dec "Y" = (true, "B")%char. Admitted.
Fact need_dec_Z : need_dec "Z" = (true, "C")%char. Admitted.

Theorem enc_dec : forall str : string, dec (enc str) = Some str.
Proof.
  intros str. induction str eqn:E1; auto.
  - simpl.
    destruct (need_enc a) eqn:E2.
    + destruct b eqn:E3.
      * subst. simpl.
        ?
        apply need_enc_true_iff in E1. cbv in E1.
        (* a0="A" \/ a0="B" \/ a0="C" \/ False *)
        destruct E1.
        { subst. rewrite need_dec_0. rewrite IHstr. repeat f_equal.
          ?
        destruct (a0 =? EscapeChar)%char eqn:E3.
        { rewrite IHstr.
          exfalso.
          (* E1 and E3 is contradiction *)
          apply Ascii.eqb_eq in E3. subst.
          apply need_enc_output_no_EscapeChar in E1. auto. }
        { 
          
          assert (forall a b c, need_enc a = (b,c) -> c <> EscapeChar).
          {
            intros.
            unfold need_enc in H.
    
  
