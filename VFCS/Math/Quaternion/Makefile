# Copyright 2023 ZhengPu Shi
# This file is part of CoqMatrix. It is distributed under the MIT
# "expat license". You should have recieved a LICENSE file with it.


test : test.ml quat.ml
	-@rm quat.mli
	@ocamlc -o $@ quat.ml test.ml

# test.opt : test.ml quat.ml
# 	@ocamlcfind opt -o $@ quat.ml test.ml -linkpkg -package unix

clean :
	rm -f *.cmi *.cmo *.o test

.PHONY : clean
