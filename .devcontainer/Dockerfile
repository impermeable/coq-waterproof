FROM coqorg/coq:8.20-ocaml-4.14-flambda

RUN opam update; \
    opam install coq-lsp.0.2.2+8.20 -y; \
    opam install ocaml-lsp-server -y
