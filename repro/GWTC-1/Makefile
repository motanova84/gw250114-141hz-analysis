PY=python3
OUT=../../artifacts

.PHONY: env run clean

env:
	python3 -m venv .venv && . .venv/bin/activate && pip install -r env.lock

run:
	. .venv/bin/activate && $(PY) -m qcal analyze --catalog GWTC-1 --band 141.7 --detector H1 --outdir $(OUT)

clean:
	rm -rf .venv
