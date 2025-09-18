.PHONY: install data analyze clean docker

install:
	python3 -m venv venv
	bash -c "source venv/bin/activate && pip install --upgrade pip"
	bash -c "source venv/bin/activate && pip install -r requirements.txt"

data:
	bash -c "source venv/bin/activate && python scripts/descargar_datos.py"

analyze:
	bash -c "source venv/bin/activate && python scripts/analizar_ringdown.py" || true
	bash -c "source venv/bin/activate && python scripts/analizar_l1.py" || true
	bash -c "source venv/bin/activate && python scripts/analisis_noesico.py" || true
	bash -c "source venv/bin/activate && python scripts/generar_validacion.py" || true

docker:
	docker build -t gw141hz .
	docker run --rm -v $(PWD):/app gw141hz

clean:
	rm -rf venv __pycache__ .pytest_cache results/ data/ *.egg-info
