.PHONY: all download analyze clean venv setup test-data

all: setup test-data analyze

venv:
	python3 -m venv venv

setup: venv
	./venv/bin/pip install -r requirements.txt

download:
	./venv/bin/python scripts/descargar_datos.py

test-data:
	./venv/bin/python scripts/generar_datos_prueba.py

analyze:
	./venv/bin/python scripts/analizar_ringdown.py

clean:
	rm -rf data/raw/*.hdf5
	rm -rf results/figures/*.png

clean-all: clean
	rm -rf venv
