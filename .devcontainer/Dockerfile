FROM coqorg/coq:8.18.0-ocaml-4.14.2-flambda

RUN opam update; \
    opam install coq-lsp.0.2.0+8.18 -y; \
    opam install ocaml-lsp-server -y
