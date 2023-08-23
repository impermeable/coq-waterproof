#FROM coqorg/coq:8.17-ocaml-4.14-flambda
FROM ubuntu:latest

ARG source=main

# COPY . /home/coq/coq-waterproof/
# RUN opam install -y coq-lsp; \
#    cd /coq/coq-waterproof;
RUN echo $source; \
    git clone --depth=1 https://github.com/impermeable/coq-waterproof#{$source}; \
#    git config --global --add safe.directory /home/coq/coq-waterproof; \
#    opam install .;