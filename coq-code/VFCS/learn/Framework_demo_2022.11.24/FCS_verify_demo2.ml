
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)let rec add n m =
   match n with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

module Nat =
 struct
  (** val add : nat -> nat -> nat **)

  let rec add n m =
    match n with
    | O -> m
    | S p -> S (add p m)

  (** val mul : nat -> nat -> nat **)

  let rec mul n m =
    match n with
    | O -> O
    | S p -> add m (mul p m)

  (** val pow : nat -> nat -> nat **)

  let rec pow n = function
  | O -> S O
  | S m0 -> mul n (pow n m0)
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p -> (match y with
               | XI q0 -> XO (add_carry p q0)
               | XO q0 -> XI (add p q0)
               | XH -> XO (succ p))
    | XO p -> (match y with
               | XI q0 -> XI (add p q0)
               | XO q0 -> XO (add p q0)
               | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p -> (match y with
               | XI q0 -> XI (add_carry p q0)
               | XO q0 -> XO (add_carry p q0)
               | XH -> XI (succ p))
    | XO p -> (match y with
               | XI q0 -> XO (add_carry p q0)
               | XO q0 -> XI (add p q0)
               | XH -> XO (succ p))
    | XH -> (match y with
             | XI q0 -> XI (succ q0)
             | XO q0 -> XO (succ q0)
             | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double_mask (sub_mask p q0)
       | XO q0 -> succ_double_mask (sub_mask p q0)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p q0)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val pow : positive -> positive -> positive **)

  let pow x =
    iter (mul x) XH

  (** val size_nat : positive -> nat **)

  let rec size_nat = function
  | XI p0 -> S (size_nat p0)
  | XO p0 -> S (size_nat p0)
  | XH -> S O

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p -> (match y with
               | XI q0 -> compare_cont r p q0
               | XO q0 -> compare_cont Gt p q0
               | XH -> Gt)
    | XO p -> (match y with
               | XI q0 -> compare_cont Lt p q0
               | XO q0 -> compare_cont r p q0
               | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val ggcdn : nat -> positive -> positive -> (positive, (positive, positive) prod) prod **)

  let rec ggcdn n a b =
    match n with
    | O -> Pair (XH, (Pair (a, b)))
    | S n0 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> Pair (a, (Pair (XH, XH)))
             | Lt ->
               let Pair (g, p) = ggcdn n0 (sub b' a') a in let Pair (ba, aa) = p in Pair (g, (Pair (aa, (add aa (XO ba)))))
             | Gt ->
               let Pair (g, p) = ggcdn n0 (sub a' b') b in let Pair (ab, bb) = p in Pair (g, (Pair ((add bb (XO ab)), bb))))
          | XO b0 -> let Pair (g, p) = ggcdn n0 a b0 in let Pair (aa, bb) = p in Pair (g, (Pair (aa, (XO bb))))
          | XH -> Pair (XH, (Pair (a, XH))))
       | XO a0 ->
         (match b with
          | XI _ -> let Pair (g, p) = ggcdn n0 a0 b in let Pair (aa, bb) = p in Pair (g, (Pair ((XO aa), bb)))
          | XO b0 -> let Pair (g, p) = ggcdn n0 a0 b0 in Pair ((XO g), p)
          | XH -> Pair (XH, (Pair (a, XH))))
       | XH -> Pair (XH, (Pair (XH, b))))

  (** val ggcd : positive -> positive -> (positive, (positive, positive) prod) prod **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_nat : nat -> positive **)

  let rec of_nat = function
  | O -> XH
  | S x -> (match x with
            | O -> XH
            | S _ -> succ (of_nat x))

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p -> (match y with
               | XI q0 -> double (pos_sub p q0)
               | XO q0 -> succ_double (pos_sub p q0)
               | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH -> (match y with
             | XI q0 -> Zneg (XO q0)
             | XO q0 -> Zneg (Coq_Pos.pred_double q0)
             | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' -> (match y with
                  | Z0 -> x
                  | Zpos y' -> Zpos (Coq_Pos.add x' y')
                  | Zneg y' -> pos_sub x' y')
    | Zneg x' -> (match y with
                  | Z0 -> x
                  | Zpos y' -> pos_sub y' x'
                  | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' -> (match y with
                  | Z0 -> Z0
                  | Zpos y' -> Zpos (Coq_Pos.mul x' y')
                  | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' -> (match y with
                  | Z0 -> Z0
                  | Zpos y' -> Zneg (Coq_Pos.mul x' y')
                  | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' -> (match y with
                  | Zneg y' -> compOpp (Coq_Pos.compare x' y')
                  | _ -> Lt)

  (** val sgn : z -> z **)

  let sgn = function
  | Z0 -> Z0
  | Zpos _ -> Zpos XH
  | Zneg _ -> Zneg XH

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False

  (** val max : z -> z -> z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val min : z -> z -> z **)

  let min n m =
    match compare n m with
    | Gt -> m
    | _ -> n

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val to_nat : z -> nat **)

  let to_nat = function
  | Zpos p -> Coq_Pos.to_nat p
  | _ -> O

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n0 -> Zpos (Coq_Pos.of_succ_nat n0)

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH

  (** val pos_div_eucl : positive -> z -> (z, z) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q0, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q0), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q0) (Zpos XH)), (sub r' b)))
    | XO a' ->
      let Pair (q0, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q0), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q0) (Zpos XH)), (sub r' b)))
    | XH -> (match leb (Zpos (XO XH)) b with
             | True -> Pair (Z0, (Zpos XH))
             | False -> Pair ((Zpos XH), Z0))

  (** val div_eucl : z -> z -> (z, z) prod **)

  let div_eucl a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let Pair (q0, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> Pair ((opp q0), Z0)
          | _ -> Pair ((opp (add q0 (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos _ ->
         let Pair (q0, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> Pair ((opp q0), Z0)
          | _ -> Pair ((opp (add q0 (Zpos XH))), (sub b r)))
       | Zneg b' -> let Pair (q0, r) = pos_div_eucl a' (Zpos b') in Pair (q0, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let Pair (q0, _) = div_eucl a b in q0

  (** val ggcd : z -> z -> (z, (z, z) prod) prod **)

  let ggcd a b =
    match a with
    | Z0 -> Pair ((abs b), (Pair (Z0, (sgn b))))
    | Zpos a0 ->
      (match b with
       | Z0 -> Pair ((abs a), (Pair ((sgn a), Z0)))
       | Zpos b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in let Pair (aa, bb) = p in Pair ((Zpos g), (Pair ((Zpos aa), (Zpos bb))))
       | Zneg b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in let Pair (aa, bb) = p in Pair ((Zpos g), (Pair ((Zpos aa), (Zneg bb)))))
    | Zneg a0 ->
      (match b with
       | Z0 -> Pair ((abs a), (Pair ((sgn a), Z0)))
       | Zpos b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in let Pair (aa, bb) = p in Pair ((Zpos g), (Pair ((Zneg aa), (Zpos bb))))
       | Zneg b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in let Pair (aa, bb) = p in Pair ((Zpos g), (Pair ((Zneg aa), (Zneg bb)))))
 end

type q = { qnum : z; qden : positive }

type cReal = { seq : (z -> q); scale : z }

type dReal = (q -> bool)

module type RbaseSymbolsSig =
 sig
  type coq_R

  val coq_Rabst : cReal -> coq_R

  val coq_Rrepr : coq_R -> cReal

  val coq_R0 : coq_R

  val coq_R1 : coq_R

  val coq_Rplus : coq_R -> coq_R -> coq_R

  val coq_Rmult : coq_R -> coq_R -> coq_R

  val coq_Ropp : coq_R -> coq_R
 end

module RbaseSymbolsImpl =
 struct
  type coq_R = float

  (** val coq_Rabst : cReal -> dReal **)

  let coq_Rabst = __

  (** val coq_Rrepr : dReal -> cReal **)

  let coq_Rrepr = __

  (** val coq_Rquot1 : __ **)

  let coq_Rquot1 =
    __

  (** val coq_Rquot2 : __ **)

  let coq_Rquot2 =
    __

  (** val coq_R0 : coq_R **)

  let coq_R0 = 0.0

  (** val coq_R1 : coq_R **)

  let coq_R1 = 1.0

  (** val coq_Rplus : coq_R -> coq_R -> coq_R **)

  let coq_Rplus = (+.)

  (** val coq_Rmult : coq_R -> coq_R -> coq_R **)

  let coq_Rmult = ( *. )

  (** val coq_Ropp : coq_R -> coq_R **)

  let coq_Ropp = fun a -> (0.0 -. a)

  type coq_Rlt = __

  (** val coq_R0_def : __ **)

  let coq_R0_def =
    __

  (** val coq_R1_def : __ **)

  let coq_R1_def =
    __

  (** val coq_Rplus_def : __ **)

  let coq_Rplus_def =
    __

  (** val coq_Rmult_def : __ **)

  let coq_Rmult_def =
    __

  (** val coq_Ropp_def : __ **)

  let coq_Ropp_def =
    __

  (** val coq_Rlt_def : __ **)

  let coq_Rlt_def =
    __
 end

(** val rminus : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let rminus = (-.)

(** val iPR_2 : positive -> RbaseSymbolsImpl.coq_R **)

let rec iPR_2 = function
| XI p0 ->
  RbaseSymbolsImpl.coq_Rmult (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1)
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 (iPR_2 p0))
| XO p0 -> RbaseSymbolsImpl.coq_Rmult (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1) (iPR_2 p0)
| XH -> RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1

(** val iPR : positive -> RbaseSymbolsImpl.coq_R **)

let iPR = function
| XI p0 -> RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 (iPR_2 p0)
| XO p0 -> iPR_2 p0
| XH -> RbaseSymbolsImpl.coq_R1

(** val iZR : z -> RbaseSymbolsImpl.coq_R **)

let iZR = function
| Z0 -> RbaseSymbolsImpl.coq_R0
| Zpos n -> iPR n
| Zneg n -> RbaseSymbolsImpl.coq_Ropp (iPR n)

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl =
 struct
  (** val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

  let coq_Rinv = fun a -> (1.0 /. a)

  (** val coq_Rinv_def : __ **)

  let coq_Rinv_def =
    __
 end

(** val rdiv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let rdiv r1 r2 =
  RbaseSymbolsImpl.coq_Rmult r1 (RinvImpl.coq_Rinv r2)

(** val q2R : q -> RbaseSymbolsImpl.coq_R **)

let q2R x =
  RbaseSymbolsImpl.coq_Rmult (iZR x.qnum) (RinvImpl.coq_Rinv (iZR (Zpos x.qden)))

(** val rpower : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let rpower = Float.pow

type 'a rConvertable = 'a -> RbaseSymbolsImpl.coq_R
  (* singleton inductive, whose constructor was Build_RConvertable *)

module PropulsionSystem =
 struct
  (** val coq_Pa0 : RbaseSymbolsImpl.coq_R **)

  let coq_Pa0 = 101325.0

  (** val rho0 : RbaseSymbolsImpl.coq_R **)

  let rho0 = 1.293

  (** val n_r : RbaseSymbolsImpl.coq_R **)

  let n_r = 4.0

  (** val coq_T0 : RbaseSymbolsImpl.coq_R **)

  let coq_T0 = 273.15

  module Env =
   struct
    type coq_Rho = RbaseSymbolsImpl.coq_R
      (* singleton inductive, whose constructor was mkRho *)

    (** val coq_Rho_rect : (RbaseSymbolsImpl.coq_R -> 'a1) -> coq_Rho -> 'a1 **)

    let coq_Rho_rect f =
      f

    (** val coq_Rho_rec : (RbaseSymbolsImpl.coq_R -> 'a1) -> coq_Rho -> 'a1 **)

    let coq_Rho_rec f =
      f

    (** val coq_Rho2R : coq_Rho -> RbaseSymbolsImpl.coq_R **)

    let coq_Rho2R x =
      x

    type coq_Temp = RbaseSymbolsImpl.coq_R
      (* singleton inductive, whose constructor was mkTemp *)

    (** val coq_Temp_rect : (RbaseSymbolsImpl.coq_R -> 'a1) -> coq_Temp -> 'a1 **)

    let coq_Temp_rect f =
      f

    (** val coq_Temp_rec : (RbaseSymbolsImpl.coq_R -> 'a1) -> coq_Temp -> 'a1 **)

    let coq_Temp_rec f =
      f

    (** val coq_Temp_Rconvertable : coq_Temp rConvertable **)

    let coq_Temp_Rconvertable x =
      x

    (** val coq_Temp2R : coq_Temp -> RbaseSymbolsImpl.coq_R **)

    let coq_Temp2R x =
      x

    type coq_Pa = RbaseSymbolsImpl.coq_R
      (* singleton inductive, whose constructor was mkPa *)

    (** val coq_Pa_rect : (RbaseSymbolsImpl.coq_R -> 'a1) -> coq_Pa -> 'a1 **)

    let coq_Pa_rect f =
      f

    (** val coq_Pa_rec : (RbaseSymbolsImpl.coq_R -> 'a1) -> coq_Pa -> 'a1 **)

    let coq_Pa_rec f =
      f

    (** val coq_Pa2R : coq_Pa -> RbaseSymbolsImpl.coq_R **)

    let coq_Pa2R x =
      x

    type coq_Height = RbaseSymbolsImpl.coq_R
      (* singleton inductive, whose constructor was mkHeight *)

    (** val coq_Height_rect : (RbaseSymbolsImpl.coq_R -> 'a1) -> coq_Height -> 'a1 **)

    let coq_Height_rect f =
      f

    (** val coq_Height_rec : (RbaseSymbolsImpl.coq_R -> 'a1) -> coq_Height -> 'a1 **)

    let coq_Height_rec f =
      f

    (** val coq_Height2R : coq_Height -> RbaseSymbolsImpl.coq_R **)

    let coq_Height2R x =
      x

    (** val coq_Pa_Temp_Height_spec_rect : coq_Pa -> coq_Temp -> coq_Height -> (__ -> 'a1) -> 'a1 **)

    let coq_Pa_Temp_Height_spec_rect _ _ _ f =
      f __

    (** val coq_Pa_Temp_Height_spec_rec : coq_Pa -> coq_Temp -> coq_Height -> (__ -> 'a1) -> 'a1 **)

    let coq_Pa_Temp_Height_spec_rec _ _ _ f =
      f __

    (** val get_Pa_by_Temp_Height : coq_Temp -> coq_Height -> coq_Pa **)

    let get_Pa_by_Temp_Height t h =
      RbaseSymbolsImpl.coq_Rmult coq_Pa0
        (rpower
          (rminus (iZR (Zpos XH))
            (RbaseSymbolsImpl.coq_Rmult
              (q2R { qnum = (Zpos (XI (XO (XO (XO (XO (XO XH))))))); qden = (XO (XO (XO (XO (XI (XO (XO (XO (XI (XI (XI (XO
                (XO XH))))))))))))) }) (rdiv (coq_Height2R h) (RbaseSymbolsImpl.coq_Rplus (coq_Temp2R t) coq_T0))))
          (q2R { qnum = (Zpos (XI (XO (XO (XO (XI (XO (XI (XO (XI (XO (XI (XI (XO (XO (XI XH)))))))))))))))); qden = (XO (XO
            (XO (XO (XI (XO (XO (XO (XI (XI (XI (XO (XO XH))))))))))))) }))

    (** val get_Height_by_Pa_Temp : coq_Pa -> coq_Temp -> coq_Height **)

    let get_Height_by_Pa_Temp pa0 t =
      rdiv
        (RbaseSymbolsImpl.coq_Rmult (RbaseSymbolsImpl.coq_Rplus (coq_Temp2R t) coq_T0)
          (rminus (iZR (Zpos XH))
            (rpower (rdiv (coq_Pa2R pa0) coq_Pa0)
              (rdiv (iZR (Zpos XH))
                (q2R { qnum = (Zpos (XI (XO (XO (XO (XI (XO (XI (XO (XI (XO (XI (XI (XO (XO (XI XH)))))))))))))))); qden =
                  (XO (XO (XO (XO (XI (XO (XO (XO (XI (XI (XI (XO (XO XH))))))))))))) })))))
        (q2R { qnum = (Zpos (XI (XO (XO (XO (XO (XO XH))))))); qden = (XO (XO (XO (XO (XI (XO (XO (XO (XI (XI (XI (XO (XO
          XH))))))))))))) })
   end
 end

(** val pa : PropulsionSystem.Env.coq_Pa **)

let pa =
  iZR Z0

(** val temp : PropulsionSystem.Env.coq_Temp **)

let temp =
  iZR (Zpos XH)

(** val height : PropulsionSystem.Env.coq_Height **)

let height =
  PropulsionSystem.Env.get_Height_by_Pa_Temp pa temp
