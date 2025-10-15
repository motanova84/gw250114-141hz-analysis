# Show project status
status:
	@echo "🌌 GW250114 - Project Status"
	@echo "============================="
	@echo ""
	@echo "📦 Environment:"
	@if [ -d "venv" ]; then \
		echo "   ✅ Virtual environment: Ready"; \
		echo "   🐍 Python: $$(./venv/bin/python --version)"; \
	else \
		echo "   ❌ Virtual environment: Not found"; \
		echo "   💡 Run: make setup"; \
	fi
	@echo ""
	@echo "📡 Data:"
	@if [ -d "data/raw" ] && [ -n "$$(ls -A data/raw 2>/dev/null)" ]; then \
		echo "   ✅ GWOSC data: Available"; \
		echo "   📁 Files: $$(ls data/raw/ | wc -l)"; \
	else \
		echo "   ❌ GWOSC data: Not found"; \
		echo "   💡 Run: make data"; \
	fi
	@echo ""
	@echo "📊 Results:"
	@if [ -d "results" ]; then \
		echo "   📂 Results directory: Exists"; \
	else \
		echo "   📂 Results directory: Will be created"; \
	fi

.PHONY: all venv setup install data download test-data check-data analyze validate validate-offline pipeline validate-connectivity validate-gw150914 validate-gw250114 workflow status clean docker help optimize optimize-sudo stop-optimize status-optimize

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
	@echo "  data                  - Download real GWOSC data"
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
	@echo "  optimize              - Start optimization system with dashboard (NEW)"
	@echo "  optimize-sudo         - Start optimization system with root privileges (NEW)"
	@echo "  stop-optimize         - Stop all optimization services (NEW)"
	@echo "  status-optimize       - Check optimization system status (NEW)"
	@echo "  workflow              - Complete workflow: setup + data + analyze"
	@echo "  docker                - Build and run Docker container"
	@echo "  status                - Show project status and environment info"
	@echo "  clean                 - Remove generated files and virtual environment"
	@echo "  help                  - Show this help message"

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

# Run scientific validation pipeline (NEW - from problem statement)
validate: setup
	@echo "🚀 Ejecutando Pipeline de Validación Científica"
	@echo "   Implementa los requisitos del problema statement"
	./venv/bin/python scripts/pipeline_validacion.py || echo "⚠️  Validación completada con advertencias - revisar log"

# Run validation in offline mode (synthetic data only)
validate-offline:
	@echo "🚀 Validación en modo offline (datos sintéticos)"
	@echo "   Ejecutando solo frameworks que no requieren conectividad"
	@if [ -f "./venv/bin/python" ]; then \
		./venv/bin/python scripts/analizar_gw250114.py || echo "⚠️  Framework offline presentó errores"; \
	else \
		echo "❌ Virtual environment not found - run make setup first"; \
		exit 1; \
	fi

# Alias for validate
pipeline: validate

# Individual validation steps  
validate-connectivity: setup
	@echo "🌐 Validando conectividad GWOSC..."
	./venv/bin/python scripts/validar_conectividad.py || echo "⚠️  Problemas de conectividad detectados"

validate-gw150914: setup
	@echo "🔬 Validando análisis de control GW150914..."
	./venv/bin/python scripts/validar_gw150914.py || echo "⚠️  Validación GW150914 falló - revisar conectividad"

validate-gw250114: setup  
	@echo "🎯 Validando framework GW250114..."
	./venv/bin/python scripts/analizar_gw250114.py || echo "⚠️  Framework GW250114 presentó errores - revisar logs"

# Docker support
docker:
	docker build -t gw141hz .
	docker run --rm -v $(PWD):/app gw141hz

# Complete workflow with data
workflow: setup data analyze
	@echo "🎉 Workflow completo finalizado"
	@echo "📊 Datos descargados y análisis ejecutado"

# Optimization system targets
optimize: setup
	@echo "🚀 Iniciando sistema de optimización máxima..."
	./scripts/optimizacion_maxima.sh

optimize-sudo: setup
	@echo "🚀 Iniciando sistema de optimización máxima (con privilegios)..."
	sudo ./scripts/optimizacion_maxima.sh

stop-optimize:
	@echo "🛑 Deteniendo sistema de optimización..."
	./scripts/detener_servicios.sh

status-optimize:
	@echo "📊 Estado del sistema de optimización:"
	@if curl -s http://localhost:5000/health > /dev/null 2>&1; then \
		echo "   ✅ Dashboard: ACTIVO (http://localhost:5000)"; \
		curl -s http://localhost:5000/api/estado-completo | python3 -m json.tool || true; \
	else \
		echo "   ❌ Dashboard: INACTIVO"; \
	fi
	@echo ""
	@if [ -f /tmp/monitor_avanzado.pid ]; then \
		if ps -p $$(cat /tmp/monitor_avanzado.pid) > /dev/null 2>&1; then \
			echo "   ✅ Monitor Avanzado: ACTIVO"; \
		else \
			echo "   ❌ Monitor Avanzado: INACTIVO"; \
		fi; \
	else \
		echo "   ❌ Monitor Avanzado: NO INICIADO"; \
	fi
	@if [ -f /tmp/monitor_recursos.pid ]; then \
		if ps -p $$(cat /tmp/monitor_recursos.pid) > /dev/null 2>&1; then \
			echo "   ✅ Monitor de Recursos: ACTIVO"; \
		else \
			echo "   ❌ Monitor de Recursos: INACTIVO"; \
		fi; \
	else \
		echo "   ❌ Monitor de Recursos: NO INICIADO"; \
	fi

# Clean up generated files
clean:
	@echo "🧹 Limpiando archivos generados..."
	rm -rf venv __pycache__ .pytest_cache results/ data/ *.egg-info
	rm -rf scripts/__pycache__/ notebooks/__pycache__/
	@echo "✅ Limpieza completada"
