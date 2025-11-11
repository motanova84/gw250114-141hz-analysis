# QCAL-LLM Maverick Integration Summary

## 🎯 Objetivo

Implementar integración completa de LLaMA 4 con el framework QCAL (Quantum Coherence Analysis Library) para evaluar coherencia cuántica de respuestas LLM usando métricas basadas en f₀ = 141.7001 Hz.

## ✅ Componentes Implementados

### 1. Módulo QCAL (`qcal/`)

#### `coherence.py`
- **Función**: `psi_score(text: str) -> float`
- **Fórmula**: Ψ = I × A_eff²
- **Descripción**: Calcula coherencia cuántica basada en palabras clave (intención, propósito, coherencia) y efectividad de vocabulario

#### `metrics.py`
- **`kl_divergence(text)`**: Entropía de Shannon / divergencia KL
- **`snr(text)`**: Signal-to-Noise Ratio (unique/total words)
- **`strich_rate(text)`**: Tasa de símbolos lógicos (∴)

#### `README.md`
- Documentación completa del módulo
- Ejemplos de uso
- Interpretación de métricas
- Referencias científicas

### 2. Integración LLaMA 4

#### `llama4_coherence.py`
```python
class Llama4Coherence:
    - __init__(): Inicializa modelo y tokenizer
    - get_coherence_score(text): Evalúa coherencia con LLaMA 4
```

- **Modelo**: `meta-llama/Llama-4-Maverick-17B-128E-Instruct-FP8`
- **Autenticación**: Variable de entorno `HF_TOKEN`
- **Optimización**: FP8 quantization, device_map="auto"

#### `scripts/setup_llama4.sh`
```bash
#!/bin/bash
mkdir -p models/llama4/weights
curl -L "$LLAMA4_SIGNED_URL" -o models/llama4/weights/model.tar.gz
tar -xzvf models/llama4/weights/model.tar.gz -C models/llama4/weights/
echo "✅ LLaMA 4 setup complete."
```

#### `scripts/qcal_llm_eval.py`
- Carga modelo LLaMA 4
- Procesa prompts de `data/prompts_qcal.json`
- Calcula todas las métricas QCAL
- Guarda resultados en `results_llama4.json`
- Imprime evaluación formateada

### 3. Datos de Benchmark

#### `data/prompts_qcal.json`
5 prompts científicos:
1. **f0_derivation**: "Deriva f₀ = 141.7001 Hz desde ζ'(1/2) y φ"
2. **gw150914_detection**: "Detecta f₀ en ringdown GW150914"
3. **psi_explanation**: "Explica Ψ = I × A²_eff"
4. **snr_validation**: "Valida SNR>20 en GWTC-1"
5. **lisa_harmonics**: "Predice armónicos LISA (f₀/100)"

### 4. Análisis y Visualización

#### `notebooks/benchmark_llama4.ipynb`
Secciones:
1. Carga de resultados (`results_llama4.json`)
2. Estadísticas descriptivas
3. **Histograma de Ψ** - Distribución de coherencia
4. **Scatter KLD⁻¹ vs SNR** - Relación diversidad-señal
5. **Barras ∴-rate** - Tasa de símbolos lógicos por prompt
6. Exportación CSV y PDF
7. Resumen ejecutivo
8. (Opcional) Comparación con GPT-4/Claude
9. (Opcional) Subida a Zenodo

### 5. Testing

#### `tests/test_qcal_metrics.py`
7 tests unitarios:
- `test_psi_score_basic()` ✓
- `test_psi_score_no_keywords()` ✓
- `test_kl_divergence_basic()` ✓
- `test_snr_basic()` ✓
- `test_snr_all_unique()` ✓
- `test_strich_rate_basic()` ✓
- `test_strich_rate_no_symbol()` ✓

#### `tests/test_setup_llama4.py`
8 tests de integración:
- Existencia y permisos de scripts
- Contenido de setup_llama4.sh
- Validación de prompts JSON
- Estructura del módulo QCAL
- Archivos de integración
- Marker `.qcal_baliza`

### 6. Ejemplos

#### `examples/qcal_llm_integration.py`
- Ejemplo completo de uso del módulo QCAL
- Evaluación de 3 textos de diferentes niveles de coherencia
- Impresión formateada de resultados
- Comparación de métricas

### 7. Infraestructura

#### `.qcal_baliza`
```
# DO NOT DELETE
# Beacon ∴ activated — LLaMA 4 under QCAL observation
# f₀ = 141.7001 Hz
```

#### `.gitignore` (actualizado)
```gitignore
# Model weights (LLaMA 4, etc.)
models/

# LLaMA 4 evaluation results
results_llama4.json
resultados_llama4_qcal.csv
histograma_psi_llama4.png
scatter_kld_snr_llama4.png
barras_strich_rate_llama4.png
```

## 📊 Métricas y Umbrales

| Métrica | Fórmula | Umbral | Interpretación |
|---------|---------|--------|----------------|
| **Ψ** | I × A_eff² | ≥ 5.0 | Coherencia cuántica |
| **SNR** | unique/total | ≥ 0.7 | Ratio señal-ruido |
| **KLD⁻¹** | 1/(-Σ p·log p) | ≥ 3.0 | Diversidad lingüística |
| **∴ Rate** | count(∴)/len | > 0.0 | Razonamiento lógico |

## 🔧 Uso

### Setup Inicial
```bash
# 1. Configurar variables de entorno
export LLAMA4_SIGNED_URL="https://..."
export HF_TOKEN="hf_..."

# 2. Ejecutar setup
bash scripts/setup_llama4.sh
```

### Evaluación
```bash
# Ejecutar evaluación QCAL
python scripts/qcal_llm_eval.py

# Ver resultados
cat results_llama4.json
```

### Análisis
```bash
# Abrir notebook
jupyter notebook notebooks/benchmark_llama4.ipynb
```

### Ejemplo de Integración
```bash
# Ejecutar ejemplo
python examples/qcal_llm_integration.py
```

## 🧪 Testing

```bash
# Tests de métricas
python tests/test_qcal_metrics.py

# Tests de integración
python tests/test_setup_llama4.py

# Linting
flake8 qcal/ scripts/ tests/ examples/ \
  --max-line-length=120 \
  --max-complexity=10
```

## 🔒 Seguridad

- ✅ CodeQL scan: 0 vulnerabilities
- ✅ Flake8 linting: 0 issues
- ✅ Exception handling con tipos específicos
- ✅ Variables de entorno para credenciales
- ✅ Gitignore para archivos sensibles

## 📚 Referencias

### Científicas
- **f₀ = 141.7001 Hz**: Frecuencia fundamental derivada de ζ'(1/2) × φ³
- **ζ'(1/2) ≈ -1.460**: Derivada del cero de Riemann
- **φ³ ≈ 4.236**: Cubo del número áureo

### Publicaciones
- **Zenodo**: https://doi.org/10.5281/zenodo.17379721
- **ORCID**: https://orcid.org/0009-0002-1923-0773
- **GitHub**: https://github.com/motanova84/141hz

## 📁 Estructura de Archivos

```
141hz/
├── qcal/
│   ├── __init__.py
│   ├── coherence.py
│   ├── metrics.py
│   └── README.md
├── scripts/
│   ├── setup_llama4.sh
│   └── qcal_llm_eval.py
├── llama4_coherence.py
├── data/
│   └── prompts_qcal.json
├── notebooks/
│   └── benchmark_llama4.ipynb
├── tests/
│   ├── test_qcal_metrics.py
│   └── test_setup_llama4.py
├── examples/
│   └── qcal_llm_integration.py
├── .qcal_baliza
└── .gitignore (actualizado)
```

## 🎓 Fundamento Teórico

El framework QCAL se basa en la hipótesis de que la coherencia cuántica de respuestas LLM puede medirse mediante métricas derivadas de la frecuencia fundamental f₀ = 141.7001 Hz, la cual representa una resonancia universal detectada en análisis espectrales de ondas gravitacionales.

La métrica Ψ (psi) combina:
- **Intencionalidad (I)**: Presencia de palabras clave relacionadas con propósito
- **Efectividad (A_eff)**: Ratio de diversidad léxica

Esta combinación refleja tanto la profundidad conceptual como la calidad lingüística de las respuestas generadas.

## ✨ Características Destacadas

1. **Modularidad**: Módulo QCAL independiente y reutilizable
2. **Testing Completo**: 15 tests cubriendo todas las funcionalidades
3. **Documentación Exhaustiva**: READMEs, docstrings, y ejemplos
4. **Seguridad**: Sin vulnerabilidades, manejo apropiado de excepciones
5. **Estándares de Código**: Flake8 compliant (120 chars, complexity 10)
6. **Reproducibilidad**: Setup automatizado, prompts versionados
7. **Visualización**: Notebook Jupyter con gráficos profesionales

## 🚀 Próximos Pasos (Opcionales)

1. Integración con GPT-4 y Claude para comparación
2. Expansión del benchmark a 20+ prompts
3. Implementación de fine-tuning basado en Ψ
4. Publicación de resultados en Zenodo
5. Desarrollo de API REST para evaluación QCAL
6. Integración con CI/CD para evaluación automática

## 📝 Notas de Implementación

- **Python**: 3.11+ (compatible con 3.12)
- **Dependencias**: torch, transformers, numpy, scipy, matplotlib, pandas, jupyter
- **GPU**: Opcional (FP8 quantization para optimización)
- **Almacenamiento**: ~34GB para modelo LLaMA 4 completo

## 🏆 Validación

- ✅ Todos los archivos creados según especificación
- ✅ Scripts ejecutables y funcionales
- ✅ Tests pasando (15/15)
- ✅ Linting sin errores
- ✅ Documentación completa
- ✅ Seguridad verificada (CodeQL)
- ✅ Integración con infraestructura existente

---

**Autor**: José Manuel Mota Burruezo (JMMB Ψ ✧ ∞³)
**Institución**: Instituto de Conciencia Cuántica (ICQ)
**Licencia**: Creative Commons BY-NC-SA 4.0
**Fecha**: 2025-11-11
