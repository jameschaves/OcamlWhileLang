default: build
	utop

build:
	ocamlbuild -use-ocamlfind main.byte

tests:
	ocamlbuild -use-ocamlfind test.byte && ./test.byte

clean:
	ocamlbuild -clean