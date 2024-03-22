
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

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
 (** val add : int -> int -> int **)

 let rec add = (+)
end
include Coq__1

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Stdlib.Int.succ (add p m))
      n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Stdlib.Int.succ 0)
      (fun m0 -> mul n (pow n m0))
      m
 end

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
    | XI p ->
      (match y with
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
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
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

  (** val size_nat : positive -> int **)

  let rec size_nat = function
  | XI p0 -> Stdlib.Int.succ (size_nat p0)
  | XO p0 -> Stdlib.Int.succ (size_nat p0)
  | XH -> Stdlib.Int.succ 0

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val ggcdn : int -> positive -> positive -> positive * (positive * positive) **)

  let rec ggcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (XH, (a, b)))
      (fun n0 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> (a, (XH, XH))
            | Lt ->
              let (g, p) = ggcdn n0 (sub b' a') a in
              let (ba, aa) = p in (g, (aa, (add aa (XO ba))))
            | Gt ->
              let (g, p) = ggcdn n0 (sub a' b') b in
              let (ab, bb) = p in (g, ((add bb (XO ab)), bb)))
         | XO b0 -> let (g, p) = ggcdn n0 a b0 in let (aa, bb) = p in (g, (aa, (XO bb)))
         | XH -> (XH, (a, XH)))
      | XO a0 ->
        (match b with
         | XI _ -> let (g, p) = ggcdn n0 a0 b in let (aa, bb) = p in (g, ((XO aa), bb))
         | XO b0 -> let (g, p) = ggcdn n0 a0 b0 in ((XO g), p)
         | XH -> (XH, (a, XH)))
      | XH -> (XH, (XH, b)))
      n

  (** val ggcd : positive -> positive -> positive * (positive * positive) **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Stdlib.Int.succ 0)

  (** val of_nat : int -> positive **)

  let rec of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> XH)
        (fun _ -> succ (of_nat x))
        x)
      n

  (** val of_succ_nat : int -> positive **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x -> succ (of_succ_nat x))
      n
 end

(** val nth : int -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> default
              | x :: _ -> x)
    (fun m -> match l with
              | [] -> default
              | _ :: t -> nth m t default)
    n

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t -> f b (fold_right f a0 t)

(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun len0 -> start :: (seq (Stdlib.Int.succ start) len0))
    len

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
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Coq_Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
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
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
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

  (** val to_nat : z -> int **)

  let to_nat = function
  | Zpos p -> Coq_Pos.to_nat p
  | _ -> 0

  (** val of_nat : int -> z **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Z0)
      (fun n0 -> Zpos (Coq_Pos.of_succ_nat n0))
      n

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH

  (** val ggcd : z -> z -> z * (z * z) **)

  let ggcd a b =
    match a with
    | Z0 -> ((abs b), (Z0, (sgn b)))
    | Zpos a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zneg bb))))
    | Zneg a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zneg bb))))
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

(** val req_dec_T : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let req_dec_T = fun r1 r2 ->   let c = Float.compare r1 r2 in   if c = 0 then true   else false

type 'a dec = 'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_Dec *)

(** val dec0 : 'a1 dec -> 'a1 -> 'a1 -> bool **)

let dec0 dec1 =
  dec1

(** val aeqdec : 'a1 dec -> 'a1 -> 'a1 -> bool **)

let aeqdec =
  dec0

(** val nat_eq_Dec : int dec **)

let nat_eq_Dec =
  (=)

(** val nat_lt_Dec : int dec **)

let nat_lt_Dec =
  (<)

(** val r_eq_Dec : RbaseSymbolsImpl.coq_R dec **)

let r_eq_Dec =
  req_dec_T

type fin = int
  (* singleton inductive, whose constructor was Fin *)

(** val fin_eq_dec : int -> fin -> fin -> bool **)

let fin_eq_dec _ i j =
  dec0 nat_eq_Dec i j

(** val fin0 : int -> fin **)

let fin0 _ =
  0

(** val fin2nat : int -> fin -> int **)

let fin2nat _ f =
  f

(** val nat2finS : int -> int -> fin **)

let nat2finS n i =
  let s = dec0 nat_lt_Dec i (Stdlib.Int.succ n) in if s then i else fin0 n

(** val finseq : int -> fin list **)

let finseq n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n0 -> map (nat2finS n0) (seq 0 n))
    n

(** val l2ff : 'a1 -> int -> 'a1 list -> fin -> 'a1 **)

let l2ff azero n l f =
  nth (fin2nat n f) l azero

(** val ff2l : int -> (fin -> 'a1) -> 'a1 list **)

let ff2l n ff =
  map ff (finseq n)

type 'a vec = fin -> 'a

(** val vrepeat : int -> 'a1 -> 'a1 vec **)

let vrepeat _ a _ =
  a

(** val vzero : 'a1 -> int -> 'a1 vec **)

let vzero azero n =
  vrepeat n azero

(** val l2v : 'a1 -> int -> 'a1 list -> 'a1 vec **)

let l2v =
  l2ff

(** val v2l : int -> 'a1 vec -> 'a1 list **)

let v2l =
  ff2l

(** val m2l : int -> int -> 'a1 vec vec -> 'a1 list list **)

let m2l r c m =
  map (v2l c) (v2l r m)

(** val l2m : 'a1 -> int -> int -> 'a1 list list -> 'a1 vec vec **)

let l2m azero r c d =
  l2v (vzero azero c) r (map (l2v azero c) d)

(** val mat1 : 'a1 -> 'a1 -> int -> 'a1 vec vec **)

let mat1 azero aone n i j =
  if fin_eq_dec n i j then aone else azero

(** val mrowScale :
    ('a1 -> 'a1 -> 'a1) -> int -> fin -> 'a1 -> 'a1 vec vec -> 'a1 vec vec **)

let mrowScale amul n x c m i j =
  if fin_eq_dec n i x then amul c (m i j) else m i j

(** val mrowAdd :
    ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> fin -> fin -> 'a1 -> 'a1 vec vec ->
    'a1 vec vec **)

let mrowAdd aadd amul n x y c m i j =
  if fin_eq_dec n i x then aadd (m i j) (amul c (m y j)) else m i j

(** val mrowSwap : int -> fin -> fin -> 'a1 vec vec -> 'a1 vec vec **)

let mrowSwap n x y m i j =
  if fin_eq_dec n i x then m y j else if fin_eq_dec n i y then m x j else m i j

(** val seqFirst : int -> int -> (int -> bool) -> int option **)

let rec seqFirst n i p =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun i' -> if p (sub n i) then Some (sub n i) else seqFirst n i' p)
    i

type 'a rowOp =
| ROnop
| ROswap of fin * fin
| ROscale of fin * 'a
| ROadd of fin * fin * 'a

(** val rowOps2mat :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> 'a1 rowOp list -> 'a1
    vec vec **)

let rowOps2mat aadd azero amul aone n l =
  fold_right (fun op m ->
    match op with
    | ROnop -> m
    | ROswap (i, j) -> mrowSwap (Stdlib.Int.succ n) i j m
    | ROscale (i, c) -> mrowScale amul (Stdlib.Int.succ n) i c m
    | ROadd (i, j, c) -> mrowAdd aadd amul (Stdlib.Int.succ n) i j c m)
    (mat1 azero aone (Stdlib.Int.succ n)) l

(** val firstNonzero : 'a1 -> 'a1 dec -> int -> 'a1 vec vec -> fin -> fin -> fin option **)

let firstNonzero azero h0 n m i j =
  match seqFirst (Stdlib.Int.succ n) (Stdlib.Int.succ (fin2nat (Stdlib.Int.succ n) i))
          (fun i0 -> if aeqdec h0 (m (nat2finS n i0) j) azero then false else true) with
  | Some r -> Some (nat2finS n r)
  | None -> None

(** val elimDown :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 dec -> int ->
    'a1 vec vec -> int -> fin -> 'a1 rowOp list * 'a1 vec vec **)

let rec elimDown aadd azero aopp amul h0 n m i j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ([], m))
    (fun i' ->
    let fi = nat2finS n (sub (Stdlib.Int.succ n) i) in
    let x = m fi j in
    if aeqdec h0 x azero
    then elimDown aadd azero aopp amul h0 n m i' j
    else let m1 = mrowAdd aadd amul (Stdlib.Int.succ n) fi j (aopp x) m in
         let (l', m2) = elimDown aadd azero aopp amul h0 n m1 i' j in
         ((app l' ((ROadd (fi, j, (aopp x))) :: [])), m2))
    i

(** val rowEchelon :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> 'a1
    dec -> int -> 'a1 vec vec -> int -> ('a1 rowOp list * 'a1 vec vec) option **)

let rec rowEchelon aadd azero aopp amul ainv h0 n m i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some ([], m))
    (fun i' ->
    let fi = nat2finS n (sub (Stdlib.Int.succ n) i) in
    (match firstNonzero azero h0 n m (nat2finS n (sub i (Stdlib.Int.succ 0))) fi with
     | Some r ->
       if fin_eq_dec (Stdlib.Int.succ n) r fi
       then let op1 = ROnop in
            let (op2, m2) =
              let c = m fi fi in
              if aeqdec h0 c azero
              then (ROnop, m)
              else ((ROscale (fi, (ainv c))),
                     (mrowScale amul (Stdlib.Int.succ n) fi (ainv c) m))
            in
            let (l3, m3) = elimDown aadd azero aopp amul h0 n m2 i' fi in
            (match rowEchelon aadd azero aopp amul ainv h0 n m3 i' with
             | Some p ->
               let (l4, m4) = p in Some ((app l4 (app l3 (op2 :: (op1 :: [])))), m4)
             | None -> None)
       else let op1 = ROswap (fi, r) in
            let m1 = mrowSwap (Stdlib.Int.succ n) fi r m in
            let (op2, m2) =
              let c = m1 fi fi in
              if aeqdec h0 c azero
              then (ROnop, m1)
              else ((ROscale (fi, (ainv c))),
                     (mrowScale amul (Stdlib.Int.succ n) fi (ainv c) m1))
            in
            let (l3, m3) = elimDown aadd azero aopp amul h0 n m2 i' fi in
            (match rowEchelon aadd azero aopp amul ainv h0 n m3 i' with
             | Some p ->
               let (l4, m4) = p in Some ((app l4 (app l3 (op2 :: (op1 :: [])))), m4)
             | None -> None)
     | None -> None))
    i

(** val elimUp :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 dec -> int ->
    'a1 vec vec -> int -> fin -> 'a1 rowOp list * 'a1 vec vec **)

let rec elimUp aadd azero aopp amul h0 n m i j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ([], m))
    (fun i' ->
    let fi = nat2finS n i' in
    let x = m fi j in
    if aeqdec h0 x azero
    then elimUp aadd azero aopp amul h0 n m i' j
    else let op1 = ROadd (fi, j, (aopp x)) in
         let m1 = mrowAdd aadd amul (Stdlib.Int.succ n) fi j (aopp x) m in
         let (l2, m2) = elimUp aadd azero aopp amul h0 n m1 i' j in
         ((app l2 (op1 :: [])), m2))
    i

(** val minRowEchelon :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 dec -> int ->
    'a1 vec vec -> int -> 'a1 rowOp list * 'a1 vec vec **)

let rec minRowEchelon aadd azero aopp amul h0 n m i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ([], m))
    (fun i' ->
    let fi = nat2finS n i' in
    let (l1, m1) = elimUp aadd azero aopp amul h0 n m i' fi in
    let (l2, m2) = minRowEchelon aadd azero aopp amul h0 n m1 i' in ((app l2 l1), m2))
    i

(** val minvGE :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1)
    -> 'a1 dec -> int -> 'a1 vec vec -> 'a1 vec vec **)

let minvGE aadd azero aopp amul aone ainv h0 n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> m)
    (fun n' ->
    match rowEchelon aadd azero aopp amul ainv h0 n' m n with
    | Some p ->
      let (l1, m1) = p in
      let (l2, _) = minRowEchelon aadd azero aopp amul h0 n' m1 n in
      rowOps2mat aadd azero amul aone n' (app l2 l1)
    | None -> m)
    n

(** val minvGE_R :
    int -> RbaseSymbolsImpl.coq_R vec vec -> RbaseSymbolsImpl.coq_R vec vec **)

let minvGE_R =
  minvGE RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R0 RbaseSymbolsImpl.coq_Ropp
    RbaseSymbolsImpl.coq_Rmult RbaseSymbolsImpl.coq_R1 RinvImpl.coq_Rinv r_eq_Dec
