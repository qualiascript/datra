.PHONY: check coverage verify-liquid docker-images docker-development docker-prod

CABAL_PROJECT ?= cabal.project
CABAL := cabal --project-file=$(CABAL_PROJECT)
ifneq ($(wildcard ../.tools/z3-4.15.4/bin/z3),)
export PATH := $(abspath ../.tools/z3-4.15.4/bin):$(PATH)
endif

.DEFAULT_GOAL := docker-prod

check:
	cabal check
	$(CABAL) build all --enable-tests -f-liquid -j1
	$(CABAL) test all -f-liquid -j1 --test-show-details=direct

coverage:
	$(CABAL) test all --enable-coverage -f-liquid -j1 --test-show-details=direct

verify-liquid:
	python3 ../scripts/check_solver.py
	$(CABAL) build lib:datra-haskell -fliquid -j1

docker-images: docker-development docker-prod

docker-development:
	docker build --target development --tag datra-haskell:development .

docker-prod:
	docker build --target prod --tag datra-haskell:prod .
