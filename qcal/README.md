# QCAL — Quantum Coherence Analysis Library

QCAL es un módulo de Python para evaluar la coherencia cuántica de textos generados por modelos de lenguaje, utilizando métricas derivadas de la frecuencia fundamental **f₀ = 141.7001 Hz**.

## 📦 Componentes

### `coherence.py`
Implementa el **psi_score (Ψ)**, la métrica principal de coherencia cuántica:

```python
from qcal.coherence import psi_score

text = "Este texto tiene intención y coherencia"
psi = psi_score(text)
print(f"Ψ = {psi:.3f}")
```

**Fórmula:**
```
Ψ = I × A_eff²
```

Donde:
- **I**: Conteo de palabras clave (intención, propósito, coherencia)
- **A_eff**: Efectividad de vocabulario (unique words / total words)

### `metrics.py`
Proporciona métricas complementarias para análisis de texto:

#### 1. **kl_divergence(text)**
Calcula la divergencia Kullback-Leibler (entropía de Shannon) de la distribución de palabras.

```python
from qcal.metrics import kl_divergence

text = "hello world hello world"
kld = kl_divergence(text)
print(f"KLD = {kld:.3f}")
```

#### 2. **snr(text)**
Signal-to-Noise Ratio: relación entre palabras únicas y totales.

```python
from qcal.metrics import snr

text = "hello world test data"
snr_val = snr(text)
print(f"SNR = {snr_val:.3f}")
```

#### 3. **strich_rate(text)**
Tasa de símbolos lógicos (∴) en el texto.

```python
from qcal.metrics import strich_rate

text = "some text ∴ more text ∴"
rate = strich_rate(text)
print(f"∴ Rate = {rate:.4f}")
```

## 🚀 Uso con LLaMA 4

### 1. Configurar LLaMA 4
```bash
# Configurar variable de entorno con URL firmada
export LLAMA4_SIGNED_URL="https://..."

# Ejecutar script de setup
bash scripts/setup_llama4.sh
```

### 2. Evaluar con QCAL
```bash
# Configurar token de HuggingFace
export HF_TOKEN="hf_..."

# Ejecutar evaluación
python scripts/qcal_llm_eval.py
```

**Salida:**
```
🔹 Prompt: f0_derivation
Ψ = 8.234 | SNR = 0.87 | KLD⁻¹ = 5.23 | ∴ = 0.012
Output: f₀ = -ζ'(1/2) × φ³ scale = 141.7001 Hz...

...
```

### 3. Analizar Resultados
```bash
# Abrir notebook de benchmarking
jupyter notebook notebooks/benchmark_llama4.ipynb
```

## 📊 Interpretación de Métricas

| Métrica | Umbral | Interpretación |
|---------|--------|----------------|
| **Ψ** | ≥ 5.0 | Coherencia cuántica aceptable |
| **SNR** | ≥ 0.7 | Buen ratio señal-ruido |
| **KLD⁻¹** | ≥ 3.0 | Diversidad lingüística suficiente |
| **∴ Rate** | > 0.0 | Presencia de razonamiento lógico |

## 🧪 Tests

```bash
# Tests de métricas
python tests/test_qcal_metrics.py

# Tests de integración
python tests/test_setup_llama4.py
```

## 📁 Archivos

```
qcal/
├── __init__.py           # Módulo principal
├── coherence.py          # Métrica Ψ
├── metrics.py            # KLD, SNR, ∴-rate
└── README.md             # Esta documentación

scripts/
├── setup_llama4.sh       # Setup de LLaMA 4
└── qcal_llm_eval.py      # Evaluación con QCAL

data/
└── prompts_qcal.json     # 5 prompts de benchmark

notebooks/
└── benchmark_llama4.ipynb # Análisis y visualización

tests/
├── test_qcal_metrics.py  # Tests de métricas
└── test_setup_llama4.py  # Tests de integración
```

## 🔬 Fundamento Científico

Las métricas QCAL están basadas en la frecuencia fundamental **f₀ = 141.7001 Hz**, derivada de:

```
f₀ = -ζ'(1/2) × φ³ scale
```

Donde:
- **ζ'(1/2)**: Derivada del cero de Riemann en s=1/2 ≈ -1.460
- **φ³**: Cubo del número áureo ≈ 4.236

Esta frecuencia ha sido detectada en análisis espectrales de ondas gravitacionales (GW150914) y representa una resonancia fundamental del universo cuántico.

## 📚 Referencias

- **Zenodo**: https://doi.org/10.5281/zenodo.17379721
- **ORCID**: https://orcid.org/0009-0002-1923-0773
- **GitHub**: https://github.com/motanova84/141hz

## 📄 Licencia

Creative Commons BY-NC-SA 4.0

© 2025 · José Manuel Mota Burruezo (JMMB Ψ ✧)
Instituto de Conciencia Cuántica (ICQ)
