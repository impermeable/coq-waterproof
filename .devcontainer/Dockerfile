FROM coqorg/coq:8.17.1-ocaml-4.14.2-flambda

RUN opam update; \
    opam install coq-lsp.0.2.0+8.17 -y; \
    opam install ocaml-lsp-server -y
