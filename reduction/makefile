.PHONY: build_and_run ..\peano_and_parser\camlprog.exe
build_and_run: camlprog.exe
	camlprog.exe
..\peano_and_parser\camlprog.exe:
	$(MAKE) -C ..\peano_and_parser\ camlprog.exe
camlprog.exe: hw2.mli hw2.ml test_2.ml ..\peano_and_parser\camlprog.exe
	ocamlc -c -I ..\peano_and_parser hw2.mli
	ocamlc -c -I ..\peano_and_parser hw2.ml
	ocamlc -I ..\peano_and_parser hw1.cmo hw2.cmo test_2.ml
clean:
	del *.cmi *.cmo *.exe
	cd ..\peano_and_parser && $(MAKE) clean
