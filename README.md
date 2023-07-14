# Remark for ISSRE2023

***This branch is the source code for a paper in ISSRE2023.***

```text
paper title:
Coq Formalization of Orientation Representation: Matrix, Euler Angle, Axis-Angle and Quaternion.

main files:
1. Section III. Mathmatical Preliminary
coq-code/VFCS/Math/Matrix/Matrix.v
coq-code/VFCS/Math/Matrix/MatrixR.v
coq-code/VFCS/Math/Matrix/VectorR.v
coq-code/VFCS/Math/Matrix/VectorR3.v
coq-code/VFCS/Math/Quaternion/Quaternion_base.v

2. Section IV. Orientation Representation
coq-code/VFCS/Math/Quaternion/Quaternion_rot.v
coq-code/VFCS/FCS/AttitudeRepr/eulerangle.v
coq-code/VFCS/Math/Matrix/MatrixR.v
coq-code/VFCS/Math/Matrix/VectorR3.v

```

# VFCS

***This is an on-going project***
* created at: July 13, 2022*


## 1. Introduction
* What is VFCS?
  * Verified Flight Control System (VFCS) is an academic project for study the FCS software by theorem prover Coq.
  * We adopt the idea of construct-correct to analysis, modeling and design the FCS.
  * Coq proof assistant is a higher-order logic theorem prover based on Calculus of Inductive Constructions.
  * We mainly study the Multicopter at the first stage.
* Why start the project ?
  * FCS is a safety critical software system, and it's reliability is hard to promise by traditional Disign-Build-Test aproch.
  * The FCS is a comprehensive engineering system, and many special knowledge, experience data and mathematical theory need to be formal described , organized and verified. Meanwhile, these knowledge and theory are existed in many similiar system. 
  * So, it is a fundamental research topic with huge potential benefits
* Who are we?
  * We are a team focusing on formal engineering mathematics study, and located in Nanjing University of  Aeronautics and Astronautics, in China.
  * Authors list
	ZhengPu Shi (zhengpushi@nuaa.edu.cn) 

## 2. Dependent or related projects
* Dependent projects:
  * [CoqExt](https://github.com/zhengpushi/CoqExt): Extension of Coq Standard Libray. [Homepage]
  * [CoqMatrix](https://github.com/zhengpushi/CoqMatrix): Formal matrix theory with multiple implementations in Coq.
* Related projects:
