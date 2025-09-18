.PHONY: install data analyze update-readme clean docker

install:
	python3 -m venv venv
	./venv/bin/pip install --upgrade pip
	./venv/bin/pip install -r requirements.txt

data:
	./venv/bin/python scripts/descargar_datos.py

analyze:
	mkdir -p results/figures
	./venv/bin/python scripts/analizar_ringdown.py
	./venv/bin/python scripts/analizar_l1.py
	./venv/bin/python scripts/analisis_noesico.py
	./venv/bin/python scripts/analisis_avanzado.py
	$(MAKE) update-readme

update-readme:
	./venv/bin/python scripts/update_readme.py

docker:
	docker build -t gw141hz .
	docker run --rm -v $(PWD):/app gw141hz

clean:
	rm -rf venv __pycache__ .pytest_cache results/ data/ *.egg-info
