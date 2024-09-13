COQ_PROJ := _CoqProjectForMake
COQ_MAKEFILE := Makefile.coq
COQ_MAKE := +${MAKE} -f $(COQ_MAKEFILE)
LTAC2_PLUGIN_DIR := $(shell ocamlfind query coq-core.plugins.ltac2)

all install: $(COQ_MAKEFILE) Makefile
	$(COQ_MAKE) $@

clean:
	-$(COQ_MAKE) clean
	find . -type f -name ".*.aux" -delete
	rm -rf docs/ocaml docs/coq

doc:
	dune build @doc
	mv _build/default/_doc/_html/ docs/ocaml
	mv _build/default/theories/Waterproof.html docs/coq

uninstall:
	$(COQ_MAKE) uninstall

configure: configure.ac

%.vo: %.v
	$(COQ_MAKE) $@

ltac2_prerequisite: $(LTAC2_PLUGIN_DIR)
	@if ! [ -n "$(LTAC2_PLUGIN_DIR)" ]; then \
		echo "Error: Ltac2 plugin not found. Please install Ltac2."; \
		exit 1; \
	fi

$(COQ_MAKEFILE): $(COQ_PROJ) $(LTAC2_PLUGIN_DIR) ltac2_prerequisite
	$(COQBIN)coq_makefile -I $(LTAC2_PLUGIN_DIR) -f $(COQ_PROJ) -o $@

help:
	@echo	"You can run:"
	@echo 	"	* 'make' to build coq-waterproof"
	@echo 	"	* 'make install' to install coq-waterproof"
	@echo 	"	* 'make uninstall' to uninstall coq-waterproof"
	@echo 	"	* 'make doc' to generate documentation of the library"
	@echo 	"	* 'make clean' to remove generated files"

.PHONY: all install uninstall doc clean
