.PHONY: docker-images docker-development docker-prod

.DEFAULT_GOAL := docker-prod

docker-images: docker-development docker-prod

docker-development:
	docker build --target development --tag datra-haskell:development .

docker-prod:
	docker build --target prod --tag datra-haskell:prod .
