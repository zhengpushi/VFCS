#  Copyright 2022 ZhengPu Shi
#  This file is part of VFCS. It is distributed under the MIT
#  "expat license". You should have recieved a LICENSE file with it.
#

COQC = coqc
COQCFLAGS = -Q ./ FlyCtrl.CoordinateSystem

all : Basic.vo Real_proof.vo \
	Array.vo Array_testZ.vo Array_testR.vo Vector.vo\
	Quaternion_aijk.vo Quaternion_aijk_testZ.vo Quaternion_aijk_testR.vo \
	Quaternion_tttt.vo \
	Coordinate.vo

# GIVE THE Dependent relation Manually
Basic.vo : Basic.v
	$(COQC) $(COQCFLAGS) $<
Real_proof.vo : Real_proof.v
	$(COQC) $(COQCFLAGS) $<
Quaternion_aijk.vo : Quaternion_aijk.v Basic.vo Real_proof.vo
	$(COQC) $(COQCFLAGS) $<
Quaternion_aijk_lemmas.vo : Quaternion_aijk_lemmas.v Quaternion_aijk.vo
	$(COQC) $(COQCFLAGS) $<
Quaternion_aijk_testZ.vo : Quaternion_aijk_testZ.v Quaternion_aijk.vo
	$(COQC) $(COQCFLAGS) $<
Quaternion_aijk_testR.vo : Quaternion_aijk_testR.v Quaternion_aijk.vo
	$(COQC) $(COQCFLAGS) $<
Array.vo : Array.v Basic.vo
	$(COQC) $(COQCFLAGS) $<
Array_testZ.vo : Array_testZ.v Array.vo
	$(COQC) $(COQCFLAGS) $<
Array_testR.vo : Array_testR.v Array.vo
	$(COQC) $(COQCFLAGS) $<
Vector.vo : Vector.v Array.vo
	$(COQC) $(COQCFLAGS) $<
Quaternion_tttt.vo : Quaternion_tttt.v Basic.vo Array.vo Quaternion_aijk.vo 
	$(COQC) $(COQCFLAGS) $<
Coordinate.vo : Coordinate.v Basic.vo Array.vo Real_proof.vo Quaternion_tttt.vo 
	$(COQC) $(COQCFLAGS) $<

.PHONY : clean

clean :
	rm -f *.vo *.glob *.vos *.vok .*.aux *.mli *.ml
