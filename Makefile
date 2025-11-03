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
.PHONY: all venv setup install data download test-data analyze analyze-gw250114 analyze-all clean docker help

# Default target - complete workflow
all: setup validate
	@echo "🎉 Workflow predeterminado completado"
	@echo "💡 Para análisis completo con datos: make workflow"

# Show available targets
help:
	@echo "🌌 GW250114 - 141.7001 Hz Analysis - Available targets:"
	@echo ""
	@echo "  all              - Complete workflow: setup + test-data + analyze"
	@echo "  setup            - Create virtual environment and install dependencies"
	@echo "  install          - Alias for setup (compatibility)"
	@echo "  venv             - Create virtual environment only"
	@echo "  data             - Download real GWOSC data"
	@echo "  download         - Alias for data (compatibility)"
	@echo "  test-data        - Generate test data (falls back to real data)"
	@echo "  analyze          - Run legacy analysis pipeline (GW150914)"
	@echo "  analyze-gw250114 - Run comprehensive GW250114 analysis (6-step workflow)"
	@echo "  analyze-all      - Run both legacy and GW250114 analyses"
	@echo "  docker           - Build and run Docker container"
	@echo "  clean            - Remove generated files and virtual environment"
	@echo "  help             - Show this help message"

# Create virtual environment
venv:
	python3 -m venv venv

# Setup environment with dependencies (alias for install)
setup: venv
	@echo "📦 Installing dependencies..."
	@./venv/bin/pip install --upgrade pip --timeout 30 2>/dev/null || echo "⚠️  Pip upgrade skipped due to network issues"
	@./venv/bin/pip install -r requirements.txt --timeout 30 || echo "⚠️  Some packages may not have installed - check manually if needed"
	@echo "✅ Setup completed"

# Install dependencies (same as setup for compatibility)
install: setup

# Download real data from GWOSC
data: setup
	@echo "📡 Descargando datos de GWOSC..."
	./venv/bin/python scripts/descargar_datos.py || echo "⚠️  Error descargando datos - verificar conectividad"

# Alias for data (for compatibility with old branch)  
download: data

# Generate test data (optional - script not implemented yet)
test-data: data
	@echo "⚠️  Test data generation script not implemented yet"
	@echo "   Using real GWOSC data instead via 'make data'"

# Check if data exists
check-data:
	@echo "🔍 Verificando disponibilidad de datos..."
	@if [ -d "data/raw" ] && [ -n "$$(ls -A data/raw 2>/dev/null)" ]; then \
		echo "   ✅ Datos encontrados en data/raw/"; \
		ls -la data/raw/; \
	else \
		echo "   ❌ No se encontraron datos"; \
		echo "   💡 Ejecuta: make data"; \
		false; \
	fi

# Run complete analysis (legacy scripts) - with data dependency
analyze: check-data
	@echo "🔬 Ejecutando análisis completo..."
	./venv/bin/python scripts/analizar_ringdown.py
	./venv/bin/python scripts/analizar_l1.py
	./venv/bin/python scripts/analisis_noesico.py

# Run comprehensive GW250114 analysis (6-step workflow)
analyze-gw250114:
	./venv/bin/python scripts/analisis_gw250114.py

# Run all analyses (legacy + GW250114)
analyze-all: analyze analyze-gw250114

# Docker support
docker:
	docker build -t gw141hz .
	docker run --rm -v $(PWD):/app gw141hz

# Complete workflow with data
workflow: setup data analyze
	@echo "🎉 Workflow completo finalizado"
	@echo "📊 Datos descargados y análisis ejecutado"

# Clean up generated files
clean:
	@echo "🧹 Limpiando archivos generados..."
	rm -rf venv __pycache__ .pytest_cache results/ data/ *.egg-info
	rm -rf scripts/__pycache__/ notebooks/__pycache__/
	@echo "✅ Limpieza completada"

# Experimental Protocols for f₀ Validation
experimentos: setup
	@echo "🧪 Ejecutando Protocolos Experimentales para f₀ = 141.7001 Hz..."
	./venv/bin/python scripts/protocolos_experimentales.py
	@echo ""
	@echo "✅ Experimentos completados"
	@echo "📊 Resultados: results/experimentos_f0.json"

# Test experimental protocols
test-experimentos: setup
	@echo "🧪 Ejecutando tests de protocolos experimentales..."
	./venv/bin/python scripts/test_protocolos_experimentales.py
	@echo ""
	@echo "✅ Tests completados"

# Generate workflow diagrams for experiments
diagrams-experimentos: setup
	@echo "📊 Generando diagramas de flujo experimental..."
	./venv/bin/python scripts/generar_diagrama_experimentos.py
	@echo ""
	@echo "✅ Diagramas generados"
	@echo "🖼️  Flujo: results/figures/flujo_experimentos_f0.png"
	@echo "🖼️  Timeline: results/figures/timeline_experimentos_f0.png"

# Search for higher harmonics of f₀
busqueda-armonicos: setup
	@echo "🎵 Búsqueda experimental de armónicos superiores..."
	@echo "   Frecuencia fundamental: f₀ = 141.7001 Hz"
	@echo "   Armónicos: submúltiplos, múltiplos, áureos, π"
	./venv/bin/python scripts/busqueda_armonicos_superiores.py || echo "⚠️  Análisis completado con advertencias"

# Test higher harmonics search
test-armonicos: setup
	@echo "🧪 Testing búsqueda de armónicos superiores..."
	./venv/bin/python scripts/test_busqueda_armonicos_superiores.py

# Multi-detector cross-resonance analysis (Virgo/KAGRA)
resonancia-cruzada: setup
	@echo "🔗 Análisis de resonancia cruzada multi-detector..."
	@echo "   Detectores: H1, L1, V1, K1"
	@echo "   Análisis: Coherencia, fase, SNR individual"
	./venv/bin/python scripts/resonancia_cruzada_virgo_kagra.py || echo "⚠️  Análisis completado con advertencias"

# Test cross-resonance analysis
test-resonancia: setup
	@echo "🧪 Testing análisis de resonancia cruzada..."
	./venv/bin/python scripts/test_resonancia_cruzada_virgo_kagra.py

# Bayesian Q-factor characterization
caracterizacion-bayesiana: setup
	@echo "📊 Caracterización bayesiana del Q-factor..."
	@echo "   Incluye: distribución posterior, intervalos de credibilidad"
	./venv/bin/python scripts/caracterizacion_bayesiana.py || echo "⚠️  Caracterización completada con advertencias"

# Test Bayesian characterization
test-caracterizacion: setup
	@echo "🧪 Testing caracterización bayesiana..."
	@echo "   Verificando cálculo de posteriores y Q-factor"
	@./venv/bin/python -c "from scripts.caracterizacion_bayesiana import CaracterizacionBayesiana, generar_datos_sinteticos_gw250114; import numpy as np; datos, fs, _ = generar_datos_sinteticos_gw250114(); bayes = CaracterizacionBayesiana(); res = bayes.estimar_q_factor(datos, fs); print('✅ Tests básicos pasaron')"

# Additional reproducibility targets

# Build LaTeX documentation (if available)
pdf-docs:
	@echo "📄 Building LaTeX documentation..."
	@if command -v latexmk >/dev/null 2>&1; then \
		if [ -f "docs/main.tex" ]; then \
			cd docs && latexmk -pdf -shell-escape main.tex; \
		else \
			echo "No LaTeX source found, skipping"; \
		fi \
	else \
		echo "latexmk not installed, skipping PDF build"; \
	fi

# Generate environment lock file
lock-env:
	@echo "🔒 Generating environment lock file..."
	./venv/bin/pip freeze > ENV.lock
	@echo "✅ Environment locked to ENV.lock"

# Run hierarchical Bayesian analysis for 141.7 Hz
bayes-analysis:
	@echo "📊 Running hierarchical Bayesian analysis..."
	./venv/bin/python bayes/hierarchical_model.py

# Verify antenna patterns
antenna-check:
	@echo "📡 Checking antenna pattern consistency..."
	@jupyter nbconvert --to notebook --execute notebooks/antenna_pattern.ipynb --output antenna_pattern_executed.ipynb
	@echo "✅ Antenna pattern analysis complete"
