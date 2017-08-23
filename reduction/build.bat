call clean
cd ..\peano_and_parser
call build
cd ..\reduction

ocamlc -c -I ..\peano_and_parser hw2.mli
ocamlc -c -I ..\peano_and_parser hw2.ml
ocamlc -I ..\peano_and_parser hw1.cmo hw2.cmo test_2.ml
