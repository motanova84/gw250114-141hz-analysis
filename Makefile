.PHONY: install data analyze clean docker

install:
	python3 -m venv venv
	source venv/bin/activate && pip install --upgrade pip
	source venv/bin/activate && pip install -r requirements.txt

data:
	source venv/bin/activate && python scripts/descargar_datos.py

analyze:
	source venv/bin/activate && python scripts/analizar_ringdown.py
	source venv/bin/activate && python scripts/analizar_l1.py
	source venv/bin/activate && python scripts/analisis_noesico.py

docker:
	docker build -t gw141hz .
	docker run --rm -v $(PWD):/app gw141hz

clean:
	rm -rf venv __pycache__ .pytest_cache results/ data/ *.egg-info
