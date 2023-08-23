FROM ubuntu:latest
#FROM coqorg/coq:8.17-ocaml-4.14-flambda

# ARG SOURCE=main
# ARG BRANCH=main
# COPY . /home/coq/coq-waterproof/
# RUN opam install -y coq-lsp; \
#    cd /coq/coq-waterproof;

RUN echo hello
#    echo $BRANCH; \
#    echo $SOURCE; 
#    git clone --depth=1 --single-branch --branch=$BRANCH https://github.com/impermeable/coq-waterproof.git; \
#    cd coq-waterproof; \
#    git checkout $SOURCE; \
#    opam install .;
#