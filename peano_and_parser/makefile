.PHONY: build
build_and_run: camlprog.exe
	camlprog.exe
camlprog.exe: hw1.mli hw1.ml test_1.ml
	ocamlc -c hw1.mli
	ocamlc -c hw1.ml
	ocamlc hw1.cmo test_1.ml
clean:
	del *.cmi *.cmo *.exe
