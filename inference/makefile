.PHONY: build_and_run ..\peano_and_parser\camlprog.exe
build_and_run: camlprog.exe
	camlprog.exe
..\peano_and_parser\camlprog.exe:
	$(MAKE) -C ..\peano_and_parser\ camlprog.exe
camlprog.exe: hw2_inference.mli hw2_inference.ml test_4.ml ..\peano_and_parser\camlprog.exe
	ocamlc -c -I ..\peano_and_parser hw2_inference.mli
	ocamlc -c -I ..\peano_and_parser hw2_inference.ml
	ocamlc -I ..\peano_and_parser hw1.cmo hw2_inference.cmo test_4.ml
clean:
	del *.cmi *.cmo *.exe
	cd ..\peano_and_parser && $(MAKE) clean
