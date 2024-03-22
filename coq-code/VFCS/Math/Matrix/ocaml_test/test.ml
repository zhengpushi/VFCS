(*
  Copyright 2024 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Test matrix ocaml program which extracted from Coq
  author    : ZhengPu Shi
  date      : Mar 22, 2024

 *)

(** These indicatos only using in REPL, and need to be removed when compiling *)
#use "topfind";;
#require "unix";;
#use "matrix.ml";;

open Printf
open Unix

(* calculate the computation time of executing a function. *)
let calc_exe_time_core (f : 'a -> unit) (n:'a) : float =
  let start_time = Sys.time () in
  let _ = f n in
  let end_time = Sys.time () in
  let elapsed = end_time -. start_time in
  elapsed

(* calculate the computation time of executing a function, and print time elapsed. *)
let calc_exe_time (f : 'a -> unit) (n:'a) =
  let elapsed = calc_exe_time_core f n in
  printf "Execution of f () takes %6.2f seconds\n" elapsed
  
(** Get the current time in seconds with an integer type *)
let current_time_get () = Float.to_int (Unix.time ())

(** Update random generator, using fixed seed or use current time as seed. *)
let random_update =
  (* when using fixed seed, the random output every time are same from first start *)
  (* let seed = 1 in *)
  (* when using current time as seed, there are better randomness *)
  let seed = current_time_get () in
  Random.init seed

(** Trim a float number to given length precision.
    E.g. f 123.45678 2 ==> 123.45 *)
let float_trim (x : float) (n : int) : float =
  let coef = 10.0 ** (float_of_int n) in
  let i = int_of_float (x *. coef) in
  let x' = (float_of_int i) /. coef in
  x'

(** Generate a float number with default precision *)
let gen_float () : float =
  float_trim (Random.float 1.0) 4

(** aa : float array array *)
type aa = float array array;;

(** Generate an `aa` with r*c shape *)
let gen_aa (r:int) (c:int) : aa =
  random_update;
  Array.init r (fun _ -> Array.init c (fun _ -> gen_float()));;

(** Get shape of an `aa` *)
let shape4aa (x:aa) : int * int =
  (Array.length x, Array.length (Array.get x 0));;

(** Convert `float` to string *)
let float2str (f:float) : string =
  Printf.sprintf "%8.3f" f

(** Convert `float array` to string *)
let arr2str (a:float array) : string =
  Array.fold_left (fun s f -> s^(float2str f)) "" a

(** Convert an `aa` to string *)
let aa2str (x:aa) : string =
  Array.fold_left (fun s a -> s^(arr2str a)^"\n") "" x
  
(** Print an `aa` *)
let prt_aa (x:aa) : unit =
  print_endline (aa2str x);;

(** matrix type *)
type matrix = int * int * (int -> int -> float);;

(** Convert `float array array` to matrix *)
let aa2mat (x:aa) : matrix =
  let (r,c) = shape4aa x in
  let f : int->int->float =
    fun i j -> if (i >= r) || (j >= c) then 0. else Array.get (Array.get x i) j in
  (r,c,f);;

(** Generate a `matrix` with r*c shape *)
let gen_mat (r:int) (c:int) : matrix =
  aa2mat (gen_aa r c);;

(** Convert `int->float` to string *)
let f2str (n:int) (f:int->float) : string =
  let rec loop (i:int) (acc:string) : string =
    if i < n
    then loop (i+1) (acc ^ float2str (f i))
    else acc in
  loop 0 "";;

(** Convert `int->int->float` to string *)
let ff2str (r:int) (c:int) (ff:int->int->float) : string =
  let rec loop (i:int) (acc:string) : string =
    if i < r
    then loop (i+1) (acc ^ f2str c (ff i) ^ "\n")
    else acc in
  loop 0 "";;
  
(** Print a `matrix` *)
let prt_mat (prefix:string) (m:matrix) : unit =
  let (r,c,ff) = m in
  let s = Printf.sprintf "%s matrix (%dx%d):\n%s" prefix r c (ff2str r c ff) in
  print_endline s;;

(** Experinemt for matrix inversion *)
let minv (m:matrix) : matrix =
  let (r,c,f) = m in
  (r,c, minvGE_R r f);;

(** command option processing *)

(* global variables for command options. *)
let cmdopt_matrix_size : int ref = ref 10
let cmdopt_show_matrix : bool ref = ref true

let set_matrix_size (i:int)   = cmdopt_matrix_size := i
let set_show_matrix (b:bool)  = cmdopt_show_matrix := b

let read_options () : string =
  let speclist =
    [
      ("-size", Arg.Int set_matrix_size, "Set matrix dimension");
      ("-print", Arg.Bool set_show_matrix, "Show matrix content");
    ]
  in
  let usage_msg = "Usage: ./matrix [option] where options are:" in
  let _ = Arg.parse speclist (fun s -> ()) usage_msg in
  ""

let show_hello_msg () =
  let hello_msg = "Program for test matrix." in
  print_endline hello_msg

let main () =
  let _ = read_options () in
  let n = !cmdopt_matrix_size in
  let is_print = !cmdopt_show_matrix in
  let m = gen_mat n n in
  let m' = minv m in
  show_hello_msg ();
  if is_print then
    (
      prt_mat "ORIGINAL" m;
      prt_mat "INVERSE" m'
    );;
  
main ();;
       
