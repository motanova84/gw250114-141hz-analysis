.PHONY: all venv setup install data download test-data analyze validate pipeline clean docker help

# Default target - complete workflow
all: setup validate

# Show available targets
help:
	@echo "🌌 GW250114 - 141.7001 Hz Analysis - Available targets:"
	@echo ""
	@echo "  all         - Complete workflow: setup + validate"
	@echo "  setup       - Create virtual environment and install dependencies"
	@echo "  install     - Alias for setup (compatibility)"
	@echo "  venv        - Create virtual environment only"
	@echo "  data        - Download real GWOSC data"
	@echo "  download    - Alias for data (compatibility)"
	@echo "  test-data   - Generate test data (falls back to real data)"
	@echo "  analyze     - Run complete analysis pipeline"
	@echo "  validate    - Run scientific validation pipeline (NEW)"
	@echo "  pipeline    - Alias for validate (compatibility)"
	@echo "  validate-connectivity - Test GWOSC connectivity only (NEW)"  
	@echo "  validate-gw150914     - Validate GW150914 control (NEW)"
	@echo "  validate-gw250114     - Test GW250114 framework (NEW)"
	@echo "  docker      - Build and run Docker container"
	@echo "  clean       - Remove generated files and virtual environment"
	@echo "  help        - Show this help message"

# Create virtual environment
venv:
	python3 -m venv venv

# Setup environment with dependencies (alias for install)
setup: venv
	./venv/bin/pip install --upgrade pip
	./venv/bin/pip install -r requirements.txt

# Install dependencies (same as setup for compatibility)
install: setup

# Download real data from GWOSC
data:
	./venv/bin/python scripts/descargar_datos.py

# Alias for data (for compatibility with old branch)
download: data

# Generate test data (optional - script not implemented yet)
test-data:
	@echo "⚠️  Test data generation script not implemented yet"
	@echo "   Using real GWOSC data instead via 'make data'"
	$(MAKE) data

# Run complete analysis (legacy scripts)
analyze:
	./venv/bin/python scripts/analizar_ringdown.py
	./venv/bin/python scripts/analizar_l1.py
	./venv/bin/python scripts/analisis_noesico.py

# Run scientific validation pipeline (NEW - from problem statement)
validate:
	@echo "🚀 Ejecutando Pipeline de Validación Científica"
	@echo "   Implementa los requisitos del problema statement"
	./venv/bin/python scripts/pipeline_validacion.py

# Alias for validate
pipeline: validate

# Individual validation steps  
validate-connectivity:
	./venv/bin/python scripts/validar_conectividad.py

validate-gw150914:
	./venv/bin/python scripts/validar_gw150914.py

validate-gw250114:
	./venv/bin/python scripts/analizar_gw250114.py

# Docker support
docker:
	docker build -t gw141hz .
	docker run --rm -v $(PWD):/app gw141hz

# Clean up generated files
clean:
	rm -rf venv __pycache__ .pytest_cache results/ data/ *.egg-info
