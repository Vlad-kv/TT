dir_1 =peano_and_parser
dir_2 =reduction
dir_3 =robinsons_algorithm
dir_4 =inference
to_delete =*.cmi *.cmo *.exe
.PHONY: build_and_run

build_and_run: $(dir_1)\camlprog.exe
	$(dir_1)\camlprog.exe

$(dir_1)\camlprog.exe: $(dir_1)\hw1.mli  $(dir_1)\hw1.ml  $(dir_1)\test_1.ml
	ocamlc  -I $(dir_1)  -o $(dir_1)\hw1.cmi  -c $(dir_1)\hw1.mli
	ocamlc  -I $(dir_1)  -o $(dir_1)\hw1.cmo  -c $(dir_1)\hw1.ml
	ocamlc  -I $(dir_1)  -o $(dir_1)\camlprog.exe  hw1.cmo $(dir_1)\test_1.ml

$(dir_2)\camlprog.exe: $(dir_2)\hw2.mli  $(dir_2)\hw2.ml  $(dir_2)\test_2.ml  $(dir_1)\camlprog.exe
	ocamlc  -I $(dir_1) -I $(dir_2)  -o $(dir_2)\hw2.cmi  -c $(dir_2)\hw2.mli
	ocamlc  -I $(dir_1) -I $(dir_2)  -o $(dir_2)\hw2.cmo  -c $(dir_2)\hw2.ml
	ocamlc  -I $(dir_1) -I $(dir_2)  -o $(dir_2)\camlprog.exe  hw1.cmo hw2.cmo $(dir_2)\test_2.ml

$(dir_3)\camlprog.exe: $(dir_3)\hw2_unify.mli  $(dir_3)\hw2_unify.ml  $(dir_3)\test_3.ml
	ocamlc  -I $(dir_3)  -o $(dir_3)\hw2_unify.cmi  -c $(dir_3)\hw2_unify.mli
	ocamlc  -I $(dir_3)  -o $(dir_3)\hw2_unify.cmo  -c $(dir_3)\hw2_unify.ml
	ocamlc  -I $(dir_3)  -o $(dir_3)\camlprog.exe  hw2_unify.cmo $(dir_3)\test_3.ml

$(dir_4)\camlprog.exe: $(dir_4)\hw2_inference.mli  $(dir_4)\hw2_inference.ml  $(dir_4)\test_4.ml  $(dir_1)\camlprog.exe  $(dir_2)\camlprog.exe  $(dir_3)\camlprog.exe
	ocamlc  -I $(dir_1) -I $(dir_2) -I $(dir_3) -I $(dir_4)  -o $(dir_4)\hw2_inference.cmi  -c $(dir_4)\hw2_inference.mli
	ocamlc  -I $(dir_1) -I $(dir_2) -I $(dir_3) -I $(dir_4)  -o $(dir_4)\hw2_inference.cmo  -c $(dir_4)\hw2_inference.ml
	ocamlc  -I $(dir_1) -I $(dir_2) -I $(dir_3) -I $(dir_4)  -o $(dir_4)\camlprog.exe  hw2_unify.cmo hw1.cmo hw2.cmo hw2_inference.cmo $(dir_4)\test_4.ml

clean:
	cd $(dir_1)  && del $(to_delete)
	cd $(dir_2)  && del $(to_delete)
	cd $(dir_3)  && del $(to_delete)
	cd $(dir_4)  && del $(to_delete)
