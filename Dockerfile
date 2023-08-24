FROM coqorg/coq:8.17-ocaml-4.14-flambda

ARG SOURCE=main
ARG BRANCH=main

# RUN opam install -y coq-lsp; \
#    cd /coq/coq-waterproof;

RUN sudo apt update; \
    sudo apt install wget; \
    opam install coq-lsp -y; \
    echo Cloning from branch: $BRANCH; \
    echo Cloning checkshum $SOURCE; \
    git clone --depth=1 --single-branch --branch=$BRANCH https://github.com/impermeable/coq-waterproof.git; \
    cd coq-waterproof; \
    git checkout $SOURCE; \
    opam install .; \
    echo Check the tail of .bashrc of root; \
    coq-lsp --version; \
    sudo tail /root/.bashrc; \
    echo -e "export PATH=$PATH:/home/coq/.opam/4.14.1+flambda/bin" | sudo tee -a /root/.bashrc; \
    echo Check the tail of .bashrc of root; \
    sudo tail /root/.bashrc;