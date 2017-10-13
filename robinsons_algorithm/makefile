.PHONY: build_and_run
build_and_run: camlprog.exe
	camlprog.exe
camlprog.exe: hw2_unify.mli hw2_unify.ml test_3.ml
	ocamlc -c hw2_unify.mli
	ocamlc -c hw2_unify.ml
	ocamlc hw2_unify.cmo test_3.ml
clean:
	del *.cmi *.cmo *.exe
