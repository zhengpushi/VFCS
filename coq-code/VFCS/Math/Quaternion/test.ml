(* #load "quat.cmo" *)
    
open Printf
open Quat
   
   
let welcome_msg () : unit =
  print_endline "quaternion program extracted from Coq, v0.1\n";;

let test1 ()  =
  let p = quat_of_ssss 3. 1. (-2.) 1. in
  let q = quat_of_ssss 2. (-1.) 2. 3. in
  let pq = qmul p q in
  printf "pq is (%.2f, %.2f, %.2f, %.2f)\n" (re pq) (im1 pq) (im2 pq) (im3 pq);;

let test2 () =
  let ((a,b),c) = ex1 in
  printf "ex1 is (%.2f, %.2f, %.2f)\n" a b c;;

let test () : unit =
  test1();
  test2();;
  
let main () =
  welcome_msg();
  test();;

let _ = main ();;
    
