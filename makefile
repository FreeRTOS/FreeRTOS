.PHONY: docker-image docker-interactive clean

docker-image: Dockerfile
	UID=$(shell id -u) GID=$(shell id -g) USER=$(USER) \
		DOCKER_BUILDKIT=1 BUILDKIT_PROGRESS=plain \
		docker build --build-arg UID --build-arg GID --build-arg USER \
		-f $< -t freertos_devenv:latest .

docker-interactive:
	docker run -v $(PWD):/home/$(USER)/FreeRTOS -it -w /home/$(USER)/FreeRTOS freertos_devenv:latest

clean:
	@echo nothing to clean.
