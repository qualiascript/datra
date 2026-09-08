PYTHON ?= python3
TECTONIC := $(PYTHON) tools/tectonic.py
REPO_ROOT := ..

.PHONY: blueprint setup-tex preprint preprint_full primer

blueprint: preprint.tex

preprint.tex: $(REPO_ROOT)/datra.lean extract_blueprint
	./extract_blueprint $(REPO_ROOT)/datra.lean > preprint.tex

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

datra_code.lean: $(REPO_ROOT)/datra.lean extract_blueprint
	./extract_blueprint --lean $(REPO_ROOT)/datra.lean > datra_code.lean

preprint_full.tex: preprint.tex datra_code.lean tools/full_preprint.py
	$(PYTHON) tools/full_preprint.py preprint.tex preprint_full.tex

preprint_full: $(REPO_ROOT)/preprint_full.pdf

$(REPO_ROOT)/preprint_full.pdf: preprint_full.tex datra_code.lean tools/tectonic.py
	$(TECTONIC) --keep-logs --synctex preprint_full.tex
	cp preprint_full.pdf $@
