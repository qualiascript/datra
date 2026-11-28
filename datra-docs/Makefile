PYTHON ?= python3
TECTONIC := $(PYTHON) tools/tectonic.py
REPO_ROOT := ..
# The appendix is an explicit editorial selection, independent of lake build.
# Imports in these files remain imports; they do not expand the source appendix.
PREPRINT_SOURCES := $(REPO_ROOT)/datra-lean/Semantics.lean
LEAN_EXTRACTION := $(REPO_ROOT)/scripts/lean_sources.py $(REPO_ROOT)/lakefile.toml

.PHONY: blueprint setup-tex preprint preprint_full primer

blueprint: preprint.tex

preprint.tex: $(PREPRINT_SOURCES) $(LEAN_EXTRACTION) extract_blueprint Makefile
	./extract_blueprint --exact-sources $(PREPRINT_SOURCES) > preprint.tex

setup-tex:
	$(TECTONIC) --install-only

preprint: $(REPO_ROOT)/preprint.pdf

$(REPO_ROOT)/preprint.pdf: preprint.tex tools/tectonic.py
	$(TECTONIC) --keep-logs --synctex preprint.tex
	cp preprint.pdf $@

primer: $(REPO_ROOT)/primer.pdf

$(REPO_ROOT)/primer.pdf: primer.tex tools/tectonic.py
	$(TECTONIC) --keep-logs --synctex primer.tex
	cp primer.pdf $@

datra_code.lean: $(PREPRINT_SOURCES) $(LEAN_EXTRACTION) extract_blueprint Makefile
	./extract_blueprint --lean --exact-sources $(PREPRINT_SOURCES) > datra_code.lean

preprint_full.tex: preprint.tex datra_code.lean tools/full_preprint.py
	$(PYTHON) tools/full_preprint.py preprint.tex preprint_full.tex

preprint_full: $(REPO_ROOT)/preprint_full.pdf

$(REPO_ROOT)/preprint_full.pdf: preprint_full.tex datra_code.lean tools/tectonic.py
	$(TECTONIC) --keep-logs --synctex preprint_full.tex
	cp preprint_full.pdf $@
