PYTHON ?= python3
TECTONIC := $(PYTHON) tools/tectonic.py

.PHONY: blueprint setup-tex preprint preprint_full

blueprint: preprint.tex

preprint.tex: datra.lean extract_blueprint
	./extract_blueprint datra.lean > preprint.tex

setup-tex:
	$(TECTONIC) --install-only

preprint: preprint.pdf

preprint.pdf: preprint.tex tools/tectonic.py
	$(TECTONIC) --keep-logs --synctex preprint.tex

datra_code.lean: datra.lean extract_blueprint
	./extract_blueprint --lean datra.lean > datra_code.lean

preprint_full.tex: preprint.tex datra_code.lean tools/full_preprint.py
	$(PYTHON) tools/full_preprint.py preprint.tex preprint_full.tex

preprint_full: preprint_full.pdf

preprint_full.pdf: preprint_full.tex datra_code.lean tools/tectonic.py
	$(TECTONIC) --keep-logs --synctex preprint_full.tex
