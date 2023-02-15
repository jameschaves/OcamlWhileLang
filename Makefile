default: build
	utop

build:
	ocamlbuild -use-ocamlfind main.byte

dt:
	ocamlbuild -use-ocamlfind data_flow.byte

lv:
	ocamlbuild -use-ocamlfind lv_analysis.byte

vb:
	ocamlbuild -use-ocamlfind vb_analysis.byte

ae:
	ocamlbuild -use-ocamlfind ae_analysis.byte

rd:
	ocamlbuild -use-ocamlfind rd_analysis.byte

cfg:
	ocamlbuild -use-ocamlfind cfg.byte

tests:
	ocamlbuild -use-ocamlfind test.byte && ./test.byte

clean:
	ocamlbuild -clean