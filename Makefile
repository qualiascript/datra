.PHONY: verify-formal verify-alignment verify-fixtures verify-proof-guards preprint-full

ifneq ($(wildcard .elan/bin/lake),)
LAKE ?= $(CURDIR)/.elan/bin/lake
export ELAN_HOME := $(CURDIR)/.elan
else
LAKE ?= lake
endif
CABAL_PROJECT ?= cabal.project
export CABAL_PROJECT
ifneq ($(wildcard .tools/z3-4.15.4/bin/z3),)
export PATH := $(CURDIR)/.tools/z3-4.15.4/bin:$(PATH)
endif

verify-alignment:
	python3 scripts/check_alignment.py

verify-formal:
	python3 scripts/check_alignment.py --require-complete
	$(LAKE) build
	$(MAKE) -C datra-haskell verify-liquid
	$(MAKE) verify-proof-guards
	$(MAKE) -C datra-haskell check
	$(MAKE) verify-fixtures

verify-fixtures:
	python3 scripts/check_fixtures.py

verify-proof-guards:
	python3 scripts/check_proof_guards.py

preprint-full:
	$(MAKE) -C datra-docs preprint_full
