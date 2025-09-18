.PHONY: all download analyze clean venv

all: download analyze

venv:
	python3 -m venv venv
	source venv/bin/activate && pip install -r requirements.txt

download:
	python scripts/descargar_datos.py

analyze:
	python scripts/analizar_ringdown.py

clean:
	rm -rf data/raw/*.hdf5
	rm -rf results/figures/*.png

clean-all: clean
	rm -rf venv
