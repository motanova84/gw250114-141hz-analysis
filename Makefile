.PHONY: all install venv setup data analyze clean docker

all: setup data analyze

venv:
	python3 -m venv venv

setup: venv
	./venv/bin/pip install --upgrade pip
	./venv/bin/pip install -r requirements.txt

install: setup

data:
	./venv/bin/python scripts/descargar_datos.py

analyze:
	./venv/bin/python scripts/analizar_ringdown.py
	./venv/bin/python scripts/analizar_l1.py
	./venv/bin/python scripts/analisis_noesico.py

docker:
	docker build -t gw141hz .
	docker run --rm -v $(PWD):/app gw141hz

clean:
	rm -rf venv __pycache__ .pytest_cache results/ data/ *.egg-info
