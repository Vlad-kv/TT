dir_1 = ..\peano_and_parser
dir_2 = ..\robinsons_algorithm
.PHONY: build_and_run $(dir_1)\camlprog.exe $(dir_2)\camlprog.exe
build_and_run: camlprog.exe
	camlprog.exe
$(dir_1)\camlprog.exe:
	$(MAKE) -C $(dir_1) camlprog.exe
$(dir_2)\camlprog.exe:
	$(MAKE) -C $(dir_2) camlprog.exe
camlprog.exe: hw2_inference.mli hw2_inference.ml test_4.ml $(dir_1)\camlprog.exe $(dir_2)\camlprog.exe
	ocamlc -c -I $(dir_1) -I $(dir_2) hw2_inference.mli
	ocamlc -c -I $(dir_1) -I $(dir_2) hw2_inference.ml
	ocamlc -I $(dir_1) -I $(dir_2) hw2_unify.cmo hw1.cmo hw2_inference.cmo test_4.ml
clean:
	del *.cmi *.cmo *.exe
	$(MAKE) -C $(dir_1) clean
	$(MAKE) -C $(dir_2) clean
