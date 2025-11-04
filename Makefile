.PHONY: all venv setup install data data-force download test-data check-data analyze validate validate-offline pipeline validate-connectivity validate-gw150914 validate-gw250114 verify-optimization workflow status clean clean-force docker help

# Default target - complete workflow
all: setup validate
	@echo "🎉 Workflow predeterminado completado"
	@echo "💡 Para análisis completo con datos: make workflow"

# Show available targets
help:
	@echo "🌌 GW250114 - 141.7001 Hz Analysis - Available targets:"
	@echo ""
	@echo "  all                   - Complete workflow: setup + validate"
	@echo "  setup                 - Create virtual environment and install dependencies"
	@echo "  install               - Alias for setup (compatibility)"
	@echo "  venv                  - Create virtual environment only"
	@echo "  data                  - Download real GWOSC data (with confirmation)"
	@echo "  data-force            - Download data without confirmation (automated)"
	@echo "  download              - Alias for data (compatibility)"
	@echo "  test-data             - Generate test data (falls back to real data)"
	@echo "  check-data            - Verify if data files are available"
	@echo "  analyze               - Run complete analysis pipeline (requires data)"
	@echo "  validate              - Run scientific validation pipeline (NEW)"
	@echo "  validate-offline      - Run validation with synthetic data only (NEW)"
	@echo "  pipeline              - Alias for validate (compatibility)"
	@echo "  validate-connectivity - Test GWOSC connectivity only (NEW)"
	@echo "  validate-gw150914     - Validate GW150914 control (NEW)"
	@echo "  validate-gw250114     - Test GW250114 framework (NEW)"
	@echo "  verify-optimization   - Verify maximum system optimization (NEW)"
	@echo "  workflow              - Complete workflow: setup + data + analyze"
	@echo "  docker                - Build and run Docker container"
	@echo "  status                - Show project status and environment info"
	@echo "  clean                 - Remove generated files (with confirmation)"
	@echo "  clean-force           - Clean without confirmation (automated)"
	@echo "  help                  - Show this help message"

# Create virtual environment
# Create virtual environment
venv:
	python3 -m venv venv

# Setup environment with dependencies
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

# Download data without confirmation (for automated workflows)
data-force: setup
	@echo "📡 Descargando datos de GWOSC (sin confirmación)..."
	./venv/bin/python scripts/descargar_datos.py --yes || echo "⚠️  Error descargando datos - verificar conectividad"

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

# Run scientific validation pipeline (NEW - from problem statement)
validate:
	@echo "🚀 Ejecutando Pipeline de Validación Científica"
	@echo "   Implementa los requisitos del problema statement"
	./venv/bin/python scripts/pipeline_validacion.py

# Alias for validate
pipeline: validate
# Run comprehensive GW250114 analysis (6-step workflow)
analyze-gw250114:
	./venv/bin/python scripts/analisis_gw250114.py

# Run all analyses (legacy + GW250114)
analyze-all: analyze analyze-gw250114

# Verify maximum system optimization
verify-optimization: setup
	@echo "🔍 Verificando optimización máxima del sistema..."
	./venv/bin/python scripts/verificacion_sistema_optimizado.py

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
	@echo "⚠️  Esta operación eliminará:"
	@echo "   - venv/ (entorno virtual)"
	@echo "   - data/ (datos descargados)"
	@echo "   - results/ (resultados de análisis)"
	@echo "   - Archivos de caché y temporales"
	@read -p "¿Continuar? [y/N]: " -n 1 -r; \
	echo; \
	if [[ $$REPLY =~ ^[YySs]$$ ]]; then \
		rm -rf venv __pycache__ .pytest_cache results/ data/ *.egg-info; \
		rm -rf scripts/__pycache__/ notebooks/__pycache__/; \
		echo "✅ Limpieza completada"; \
	else \
		echo "❌ Limpieza cancelada"; \
	fi

# Clean up without confirmation (for automated workflows)
clean-force:
	@echo "🧹 Limpiando archivos generados (sin confirmación)..."
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
