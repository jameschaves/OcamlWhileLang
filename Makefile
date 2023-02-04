default: build
	utop

build:
	ocamlbuild -use-ocamlfind main.byte

dt:
	ocamlbuild -use-ocamlfind data_flow.byte

lv:
	ocamlbuild -use-ocamlfind data_flow.byte
	ocamlbuild -use-ocamlfind lv_analysis.byte

tests:
	ocamlbuild -use-ocamlfind test.byte && ./test.byte

clean:
	ocamlbuild -clean