(* Copyright 2022 ZhengPu Shi
 * This file is part of VFCS. It is distributed under the MIT
 * "expat license". You should have recieved a LICENSE file with it. *)


#use "FCS_verify_demo2.ml";;

open PropulsionSystem;;
open Env;;

(** 海拔高度与大气压对照表 *)
let table : (float * float) list = [
    (    0.0, 101.3);
    ( 1000.0,  90.2);
    ( 2000.0,  80.2);
    ( 3000.0,  71.0);
    ( 4000.0,  62.7);
    ( 5000.0,  55.2);
    ( 6000.0,  48.5);
    ( 7000.0,  42.4);
    ( 8000.0,  37.0);
    ( 9000.0,  32.2);
    (10000.0,  27.8)
  ];;

(** 因为不知道温度，先任给温度为0.0，测试由给定高度计算出的大气压强及偏差 *)
let test_Pa =
  let f2s (f:float) : string = Printf.sprintf "%6.2f" f in
  (* 输出 (期望值，实际值，差异百分比) *)
  List.map (fun t ->
      let (h0,p0) = t in
      let v_expected = p0 *. 1000.0 in
      let v_actual = get_Pa_by_Temp_Height 0.0 h0 in
      let v_diff_percent = Float.abs (v_actual -. v_expected) /. v_expected in
      (f2s v_expected) ^ ", " ^ (f2s v_actual) ^ ", " ^ (f2s v_diff_percent))
    table;;

(** 因为不知道温度，先任给温度为0.0，测试由给定大气压强计算出的高度及偏差 *)
let test_Height =
  let f2s (f:float) : string = Printf.sprintf "%6.2f" f in
  (* 输出 (期望值，实际值，差异百分比) *)
  List.map (fun t ->
      let (h0,p0) = t in
      let v_expected = h0 in
      let v_actual = get_Height_by_Pa_Temp (p0 *. 1000.0) 0.0 in
      let v_diff_percent = Float.abs (v_actual -. v_expected) /. v_expected in
      (f2s v_expected) ^ ", " ^ (f2s v_actual) ^ ", " ^ (f2s v_diff_percent))
    table;;

(** 从结果看，这些数据比较接近，也间接说明了我们的模型符合这些数据。*)
