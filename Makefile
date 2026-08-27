PYTHON ?= python3
TECTONIC := $(PYTHON) tools/tectonic.py

.PHONY: blueprint setup-tex preprint

blueprint: preprint.tex

preprint.tex: datra.lean extract_blueprint
	./extract_blueprint datra.lean > preprint.tex

setup-tex:
	$(TECTONIC) --install-only

preprint: preprint.pdf

preprint.pdf: preprint.tex tools/tectonic.py
	$(TECTONIC) --keep-logs --synctex preprint.tex
