
type __ = Obj.t

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val add : int -> int -> int

val sub : int -> int -> int

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val pow : int -> int -> int
 end

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

  val size_nat : positive -> int

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val ggcdn : int -> positive -> positive -> positive * (positive * positive)

  val ggcd : positive -> positive -> positive * (positive * positive)

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> int

  val of_nat : int -> positive

  val of_succ_nat : int -> positive
 end

val nth : int -> 'a1 list -> 'a1 -> 'a1

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val seq : int -> int -> int list

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

  val max : z -> z -> z

  val min : z -> z -> z

  val abs : z -> z

  val to_nat : z -> int

  val of_nat : int -> z

  val to_pos : z -> positive

  val ggcd : z -> z -> z * (z * z)
 end

type q = { qnum : z; qden : positive }

type cReal = { seq0 : (z -> q); scale : z }

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

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl :
 RinvSig

val req_dec_T : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

type 'a dec = 'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_Dec *)

val dec0 : 'a1 dec -> 'a1 -> 'a1 -> bool

val aeqdec : 'a1 dec -> 'a1 -> 'a1 -> bool

val nat_eq_Dec : int dec

val nat_lt_Dec : int dec

val r_eq_Dec : RbaseSymbolsImpl.coq_R dec

type fin = int
  (* singleton inductive, whose constructor was Fin *)

val fin_eq_dec : int -> fin -> fin -> bool

val fin0 : int -> fin

val fin2nat : int -> fin -> int

val nat2finS : int -> int -> fin

val nat2fin : int -> int -> fin

val ff2f : 'a1 -> int -> (fin -> 'a1) -> int -> 'a1

val finseq : int -> fin list

val l2ff : 'a1 -> int -> 'a1 list -> fin -> 'a1

val ff2l : int -> (fin -> 'a1) -> 'a1 list

val seqsum : ('a1 -> 'a1 -> 'a1) -> 'a1 -> (int -> 'a1) -> int -> 'a1

val fseqsum : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> (fin -> 'a1) -> 'a1

type 'a vec = fin -> 'a

val vrepeat : int -> 'a1 -> 'a1 vec

val vzero : 'a1 -> int -> 'a1 vec

val l2v : 'a1 -> int -> 'a1 list -> 'a1 vec

val v2l : int -> 'a1 vec -> 'a1 list

val vmap2 : ('a1 -> 'a2 -> 'a3) -> int -> 'a1 vec -> 'a2 vec -> 'a3 vec

val vsum : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> 'a1 vec -> 'a1

val vdot :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec -> 'a1

val m2l : int -> int -> 'a1 vec vec -> 'a1 list list

val l2m : 'a1 -> int -> int -> 'a1 list list -> 'a1 vec vec

val mat1 : 'a1 -> 'a1 -> int -> 'a1 vec vec

val mmul :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> int -> int -> 'a1 vec vec ->
  'a1 vec vec -> 'a1 vec vec

val mrowScale : ('a1 -> 'a1 -> 'a1) -> int -> fin -> 'a1 -> 'a1 vec vec -> 'a1 vec vec

val mrowAdd :
  ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> fin -> fin -> 'a1 -> 'a1 vec vec ->
  'a1 vec vec

val mrowSwap : int -> fin -> fin -> 'a1 vec vec -> 'a1 vec vec

val seqFirst : int -> int -> (int -> bool) -> int option

type 'a rowOp =
| ROnop
| ROswap of fin * fin
| ROscale of fin * 'a
| ROadd of fin * fin * 'a

val rowOps2mat :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> 'a1 rowOp list -> 'a1
  vec vec

val firstNonzero : 'a1 -> 'a1 dec -> int -> 'a1 vec vec -> fin -> fin -> fin option

val elimDown :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 dec -> int -> 'a1
  vec vec -> int -> fin -> 'a1 rowOp list * 'a1 vec vec

val rowEchelon :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> 'a1
  dec -> int -> 'a1 vec vec -> int -> ('a1 rowOp list * 'a1 vec vec) option

val elimUp :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 dec -> int -> 'a1
  vec vec -> int -> fin -> 'a1 rowOp list * 'a1 vec vec

val minRowEchelon :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 dec -> int -> 'a1
  vec vec -> int -> 'a1 rowOp list * 'a1 vec vec

val minvGE :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1)
  -> 'a1 dec -> int -> 'a1 vec vec -> 'a1 vec vec

val mmul_R :
  int -> int -> int -> RbaseSymbolsImpl.coq_R vec vec -> RbaseSymbolsImpl.coq_R vec vec ->
  RbaseSymbolsImpl.coq_R vec vec

val minvGE_R : int -> RbaseSymbolsImpl.coq_R vec vec -> RbaseSymbolsImpl.coq_R vec vec
