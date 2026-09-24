.PHONY: check coverage docker-images docker-development docker-prod

CABAL_PROJECT ?= cabal.project
CABAL := cabal --project-file=$(CABAL_PROJECT)

.DEFAULT_GOAL := docker-prod

check:
	cabal check
	$(CABAL) build all --enable-tests
	$(CABAL) test all --test-show-details=direct

coverage:
	$(CABAL) test all --enable-coverage --test-show-details=direct

docker-images: docker-development docker-prod

docker-development:
	docker build --target development --tag datra-haskell:development .

docker-prod:
	docker build --target prod --tag datra-haskell:prod .
