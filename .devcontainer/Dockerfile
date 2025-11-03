FROM rocq/rocq-prover:dev-ocaml-4.14.2-flambda

RUN opam update; \
    opam install coq-lsp.0.2.3+dev -y; \
    opam install ocaml-lsp-server -y
