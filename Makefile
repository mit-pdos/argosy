SRC_DIRS := 'src' $(shell test -d 'vendor' && echo 'vendor') 'logging-client'
ALL_VFILES := $(shell find $(SRC_DIRS) -name "*.v")
TEST_VFILES := $(shell find 'src' -name "*Tests.v")
PROJ_VFILES := $(shell find 'src' -name "*.v")
VFILES := $(filter-out $(TEST_VFILES),$(PROJ_VFILES))

COQARGS := -w +deprecated-since-8.8,+deprecated-since-8.17,+deprecated-since-8.20,+deprecated-since-9.0,-deprecated-transitive-library-file-since-9.0

all: coq extract
coq: $(VFILES:.v=.vo)
test: $(TEST_VFILES:.v=.vo) $(VFILES:.v=.vo)

_RocqProject: libname $(wildcard vendor/*)
	@echo "-R src $$(cat libname)" > $@
	@for libdir in $(wildcard vendor/*); do \
	libname=$$(cat $$libdir/libname); \
	if [ $$? -ne 0 ]; then \
	  echo "Do you need to run git submodule update --init --recursive?" 1>&2; \
		exit 1; \
	fi; \
	echo "-R $$libdir/src $$(cat $$libdir/libname)" >> $@; \
	done
	@echo "_RocqProject:"
	@cat $@

.coqdeps.d: $(ALL_VFILES) _RocqProject
	@echo "COQDEP $@"
	@rocq dep -f _RocqProject $(ALL_VFILES) > $@

ifneq ($(MAKECMDGOALS), clean)
-include .coqdeps.d
endif

%.vo: %.v _RocqProject
	@echo "COQC $<"
	@rocq compile $(COQARGS) $(shell cat '_RocqProject') $< -o $@

extract: logging-client/extract/ComposedRefinement.hs

logging-client/extract/ComposedRefinement.hs: logging-client/Extract.vo
	./scripts/add-preprocess.sh logging-client/extract/*.hs

Makefile.coq: _RocqProject $(VFILES)
	@rocq makefile -R src $$(cat libname) $(VFILES) -o Makefile.coq

install: coq Makefile.coq
	$(MAKE) -f Makefile.coq install

uninstall: Makefile.coq
	$(MAKE) -f Makefile.coq uninstall

clean:
	@echo "CLEAN vo glob aux"
	@rm -f $(ALL_VFILES:.v=.vo) $(ALL_VFILES:.v=.glob)
	@find $(SRC_DIRS) -name ".*.aux" -exec rm {} \;
	@echo "CLEAN extraction"
	@rm -rf logging-client/extract/*.hs
	rm -f _RocqProject .coqdeps.d Makefile.coq Makefile.coq.conf .filestoinstall

.PHONY: all coq test clean extract install uninstall
.DELETE_ON_ERROR:
