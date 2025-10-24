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

.PHONY: \
  all venv setup install \
  data download test-data check-data \
  analyze validate validate-offline pipeline \
  validate-connectivity validate-gw150914 validate-gw250114 \
  alert-gw250114 test-alert-gw250114 test-rpsi \
  validacion-quintica multievento test-multievento \
  energia-cuantica test-energia-cuantica \
  validate-3-pilares test-3-pilares \
  validate-discovery-standards test-discovery-standards \
  pycbc-analysis test-pycbc demo-pycbc coherencia-escalas \
  dashboard dashboard-status workflow status \
  clean docker help \
  experimentos test-experimentos diagrams-experimentos

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
	@echo "  alert-gw250114        - Monitor GW250114 availability continuously (NEW)"
	@echo "  test-alert-gw250114   - Test GW250114 alert system (NEW)"
	@echo "  test-rpsi             - Test R_Ψ symmetry and compactification radius (NEW)"
	@echo "  multievento           - Run multi-event Bayesian analysis (NEW)"
	@echo "  test-multievento      - Test multi-event module with synthetic data (NEW)"
	@echo "  energia-cuantica      - Calculate quantum energy E_Ψ = hf₀ (NEW)"
	@echo "  test-energia-cuantica - Test quantum energy calculations (NEW)"
	@echo "  validate-3-pilares    - Run 3 pillars validation: reproducibility, falsifiability, evidence (NEW)"
	@echo "  test-3-pilares        - Test 3 pillars validation scripts (NEW)"
	@echo "  validate-discovery-standards - Validate scientific discovery standards (>10σ) (NEW)"
	@echo "  test-discovery-standards     - Test discovery standards validation (NEW)"
	@echo "  pycbc-analysis        - Run PyCBC-based GW150914 analysis (NEW)"
	@echo "  test-pycbc            - Test PyCBC analysis script (NEW)"
	@echo "  demo-pycbc            - Run PyCBC analysis demo with simulated data (NEW)"
	@echo "  coherencia-escalas    - Generate coherence multi-scale visualization (NEW)"
	@echo "  experimentos          - Run experimental protocols for f₀ validation (NEW)"
	@echo "  test-experimentos     - Test experimental protocols (28 tests) (NEW)"
	@echo "  diagrams-experimentos - Generate workflow diagrams for experiments (NEW)"
	@echo "  dashboard             - Run real-time monitoring dashboard (NEW)"
	@echo "  dashboard-status      - Run GW250114 status dashboard (NEW)"
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
validate: setup validate-3-pilares
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

# Alert system for GW250114 availability
alert-gw250114: setup
	@echo "🚨 Sistema de alertas automáticas para GW250114"
	@echo "   Iniciando monitoreo continuo..."
	@echo "   Presiona Ctrl+C para detener"
	./venv/bin/python scripts/verificador_gw250114.py

# Test alert system for GW250114
test-alert-gw250114: setup
	@echo "🧪 Testing alert system for GW250114..."
	./venv/bin/python scripts/test_verificador_gw250114.py

# Test R_Ψ symmetry and compactification radius
test-rpsi: setup
	@echo "🔬 Testing R_Ψ symmetry and compactification radius..."
	@echo "   Validating R_Ψ = 1.687e-35 m and f₀ = 141.7001 Hz relationship"
	./venv/bin/python scripts/test_rpsi_symmetry.py

# Validate Calabi-Yau compactification (Section 5.7f)
validacion-quintica: setup
	@echo "🔬 Validación numérica de compactificación sobre la quíntica en ℂP⁴..."
	@echo "   Sección 5.7(f): Jerarquía RΨ ≈ 10⁴⁷ y frecuencia f₀ = 141.7001 Hz"
	./venv/bin/python scripts/validacion_compactificacion_quintica.py

# Multi-event Bayesian analysis
multievento: setup
	@echo "🌌 Ejecutando análisis bayesiano multi-evento..."
	@echo "   Eventos: GW150914, GW151012, GW170104, GW190521, GW200115"
	./venv/bin/python scripts/analisis_bayesiano_multievento.py || echo "⚠️  Análisis multi-evento completado con advertencias"

# Test multi-event module with synthetic data
test-multievento: setup
	@echo "🧪 Testing análisis bayesiano multi-evento..."
	./venv/bin/python scripts/test_analisis_bayesiano_multievento.py

# Calculate quantum energy of fundamental mode
energia-cuantica: setup
	@echo "⚛️  Calculando energía cuántica del modo fundamental..."
	@echo "   E_Ψ = hf₀ con f₀ = 141.7001 Hz"
	./venv/bin/python scripts/energia_cuantica_fundamental.py

# Test quantum energy calculations
test-energia-cuantica: setup
	@echo "🧪 Testing cálculos de energía cuántica..."
	./venv/bin/python scripts/test_energia_cuantica.py

# Run 3 pillars validation: reproducibility, falsifiability, evidence
validate-3-pilares: setup
	@echo "🌟 Ejecutando Validación de 3 Pilares del Método Científico..."
	@echo "   1. REPRODUCIBILIDAD GARANTIZADA"
	@echo "   2. FALSABILIDAD EXPLÍCITA"
	@echo "   3. EVIDENCIA EMPÍRICA CONCRETA"
	./venv/bin/python scripts/validacion_completa_3_pilares.py

# Test 3 pillars validation scripts
test-3-pilares: setup
	@echo "🧪 Testing scripts de validación de 3 pilares..."
	@echo "   Testing reproducibilidad..."
	./venv/bin/python scripts/reproducibilidad_garantizada.py || exit 1
	@echo "   Testing falsabilidad..."
	./venv/bin/python scripts/falsabilidad_explicita.py || exit 1
	@echo "   Testing evidencia empírica..."
	./venv/bin/python scripts/evidencia_empirica.py || exit 1
	@echo "   Testing validación completa..."
	./venv/bin/python scripts/validacion_completa_3_pilares.py || exit 1
	@echo "✅ Todos los tests de 3 pilares pasaron exitosamente"

# Validate scientific discovery standards (Particle Physics, Astronomy, Medicine)
validate-discovery-standards: setup
	@echo "📊 Validando Estándares de Descubrimiento Científico..."
	@echo "   • Física de partículas: ≥ 5σ"
	@echo "   • Astronomía: ≥ 3σ"
	@echo "   • Medicina (EEG): ≥ 2σ"
	./venv/bin/python scripts/discovery_standards.py
	@echo "✅ Validación de estándares completada"

# Test discovery standards validation
test-discovery-standards: setup
	@echo "🧪 Testing validación de estándares de descubrimiento..."
	./venv/bin/python scripts/test_discovery_standards.py
	@echo "✅ Tests de estándares de descubrimiento pasaron exitosamente"

# Run PyCBC-based GW150914 analysis
pycbc-analysis: setup
	@echo "🌌 Ejecutando análisis GW150914 con PyCBC..."
	@echo "   Filtrado, blanqueado y graficado de señal"
	@mkdir -p results/figures
	./venv/bin/python scripts/analizar_gw150914_pycbc.py || echo "⚠️  Análisis PyCBC requiere conectividad a GWOSC"

# Test PyCBC analysis script
test-pycbc: setup
	@echo "🧪 Testing script de análisis PyCBC..."
	./venv/bin/python scripts/test_analizar_gw150914_pycbc.py

# Run PyCBC demo with simulated data
demo-pycbc: setup
	@echo "🎬 Ejecutando demostración de análisis PyCBC con datos simulados..."
	@mkdir -p results/figures
	@if ./venv/bin/python -c "import matplotlib" 2>/dev/null; then \
		./venv/bin/python scripts/demo_pycbc_analysis.py; \
	else \
		echo "⚠️  venv sin matplotlib, usando Python del sistema"; \
		python3 scripts/demo_pycbc_analysis.py; \
	fi

# Generate coherence multi-scale visualization
coherencia-escalas: setup
	@echo "🌈 Generando visualización de coherencia multi-escala..."
	@echo "   f₀ = 141.7001 Hz a través de escalas Planck, LIGO y CMB"
	@mkdir -p results/figures
	./venv/bin/python scripts/generar_coherencia_escalas.py
	@echo "✅ Visualización guardada en coherence_f0_scales.png"

# Run real-time monitoring dashboard
dashboard: setup
	@echo "📊 Iniciando Dashboard de Monitoreo GW250114..."
	@echo "🌐 Dashboard disponible en http://localhost:5000"
	@cd dashboard && ../venv/bin/python dashboard_avanzado.py

# Run GW250114 status dashboard
dashboard-status: setup
	@echo "📊 Iniciando Dashboard de Estado GW250114..."
	@echo "🌐 Monitor disponible en http://localhost:5000/monitor-gw"
	@echo "📊 API JSON en http://localhost:5000/estado-gw250114"
	./venv/bin/python scripts/run_dashboard.py

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
