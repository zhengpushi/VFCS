
type __ = Obj.t

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

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

val add : nat -> nat -> nat

module Nat :
 sig
  val add : nat -> nat -> nat

  val mul : nat -> nat -> nat

  val pow : nat -> nat -> nat
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val pow : positive -> positive -> positive

  val size_nat : positive -> nat

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val ggcdn : nat -> positive -> positive -> (positive, (positive, positive) prod) prod

  val ggcd : positive -> positive -> (positive, (positive, positive) prod) prod

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_nat : nat -> positive

  val of_succ_nat : nat -> positive
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val sgn : z -> z

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val max : z -> z -> z

  val min : z -> z -> z

  val abs : z -> z

  val to_nat : z -> nat

  val of_nat : nat -> z

  val to_pos : z -> positive

  val pos_div_eucl : positive -> z -> (z, z) prod

  val div_eucl : z -> z -> (z, z) prod

  val div : z -> z -> z

  val ggcd : z -> z -> (z, (z, z) prod) prod
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

module RbaseSymbolsImpl :
 RbaseSymbolsSig

val rminus : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val iPR_2 : positive -> RbaseSymbolsImpl.coq_R

val iPR : positive -> RbaseSymbolsImpl.coq_R

val iZR : z -> RbaseSymbolsImpl.coq_R

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl :
 RinvSig

val rdiv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val q2R : q -> RbaseSymbolsImpl.coq_R

val rpower : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

type 'a rConvertable = 'a -> RbaseSymbolsImpl.coq_R
  (* singleton inductive, whose constructor was Build_RConvertable *)

module PropulsionSystem :
 sig
  val coq_Pa0 : RbaseSymbolsImpl.coq_R

  val rho0 : RbaseSymbolsImpl.coq_R

  val n_r : RbaseSymbolsImpl.coq_R

  val coq_T0 : RbaseSymbolsImpl.coq_R

  module Env :
   sig
    type coq_Rho = RbaseSymbolsImpl.coq_R
      (* singleton inductive, whose constructor was mkRho *)

    val coq_Rho_rect : (RbaseSymbolsImpl.coq_R -> 'a1) -> coq_Rho -> 'a1

    val coq_Rho_rec : (RbaseSymbolsImpl.coq_R -> 'a1) -> coq_Rho -> 'a1

    val coq_Rho2R : coq_Rho -> RbaseSymbolsImpl.coq_R

    type coq_Temp = RbaseSymbolsImpl.coq_R
      (* singleton inductive, whose constructor was mkTemp *)

    val coq_Temp_rect : (RbaseSymbolsImpl.coq_R -> 'a1) -> coq_Temp -> 'a1

    val coq_Temp_rec : (RbaseSymbolsImpl.coq_R -> 'a1) -> coq_Temp -> 'a1

    val coq_Temp_Rconvertable : coq_Temp rConvertable

    val coq_Temp2R : coq_Temp -> RbaseSymbolsImpl.coq_R

    type coq_Pa = RbaseSymbolsImpl.coq_R
      (* singleton inductive, whose constructor was mkPa *)

    val coq_Pa_rect : (RbaseSymbolsImpl.coq_R -> 'a1) -> coq_Pa -> 'a1

    val coq_Pa_rec : (RbaseSymbolsImpl.coq_R -> 'a1) -> coq_Pa -> 'a1

    val coq_Pa2R : coq_Pa -> RbaseSymbolsImpl.coq_R

    type coq_Height = RbaseSymbolsImpl.coq_R
      (* singleton inductive, whose constructor was mkHeight *)

    val coq_Height_rect : (RbaseSymbolsImpl.coq_R -> 'a1) -> coq_Height -> 'a1

    val coq_Height_rec : (RbaseSymbolsImpl.coq_R -> 'a1) -> coq_Height -> 'a1

    val coq_Height2R : coq_Height -> RbaseSymbolsImpl.coq_R

    val coq_Pa_Temp_Height_spec_rect : coq_Pa -> coq_Temp -> coq_Height -> (__ -> 'a1) -> 'a1

    val coq_Pa_Temp_Height_spec_rec : coq_Pa -> coq_Temp -> coq_Height -> (__ -> 'a1) -> 'a1

    val get_Pa_by_Temp_Height : coq_Temp -> coq_Height -> coq_Pa

    val get_Height_by_Pa_Temp : coq_Pa -> coq_Temp -> coq_Height
   end
 end

val pa : PropulsionSystem.Env.coq_Pa

val temp : PropulsionSystem.Env.coq_Temp

val height : PropulsionSystem.Env.coq_Height
