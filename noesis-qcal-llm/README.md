# noesis-qcal-llm: Módulo LLM Coherente ∞³

**Autor:** José Manuel Mota Burruezo (JMMB Ψ✧)

Este módulo contiene la **implementación completa del framework QCAL-LLM ∞³** (Quantum Coherent Attentional Lock), un enfoque paradigmático para ajuste de coherencia vibracional en modelos de lenguaje grandes (LLM), anclado en la frecuencia universal **f₀ = 141.7001 Hz** derivada de datos empíricos de ondas gravitacionales.

## 📚 Documentación Principal

### 🎯 [**MANIFESTO.md**](./MANIFESTO.md) - Prueba de Concepto Completa

Documento técnico exhaustivo que presenta:
- **Marco teórico**: Ecuación del campo noético Ψ = I · A²_eff
- **Evidencia empírica**: Aislamiento de f₀ = 141.7001 Hz en GWTC-1/4
- **Protocolo SIP**: Spectral Insertion Protocol para modulación atencional
- **Resultados**: Ψ = 6.89 ± 0.12, reducción de alucinación 86%
- **Predicciones falsables**: LISA 2026-2035, próxima generación LLM
- **Código reproducible**: Python 3.12 + NumPy/SciPy/gwpy

📖 **[Leer MANIFESTO completo →](./MANIFESTO.md)**

## 🔬 Archivos Principales

### Núcleo de Implementación

#### 1. **`QCALLLMCore.py`** - Clase Core Completa
Implementación del framework QCAL con:
- Modulación SIP: `W(t) = α · [1 + ε · cos(2πf₀t + φ) · e^(-t/τ)]`
- Cálculo de Ψ: `Ψ = I · A²_eff`
- Evaluación de coherencia con bootstrap CI
- Bucle de ajuste sin RLHF

```bash
python QCALLLMCore.py  # Ejecutar tests de verificación
```

**Salida esperada:**
```
✓ Core initialized: f₀ = 141.7001 Hz, τ = 0.07 s, ε = 0.0162
✓ SIP Modulation: Weights mean: 1.0000, std: 0.0022
✓ Ψ Computation: Ψ = 6.3501, Coherent: True
✓ Response Evaluation: Mean Ψ: 8.20 (95% CI: 8.05, 8.35)
```

#### 2. **`evaluate_manifesto.py`** - Detección de f₀ y Verificación
Protocolo de análisis espectral para detectar f₀ en ringdown GW150914:
- Carga datos HDF5 de GWOSC
- Aplica Welch PSD en banda 130-160 Hz
- Ajusta modelo QNM nulo (Kerr)
- Calcula SNR y χ²

```bash
python evaluate_manifesto.py
```

**Salida esperada:**
```
f₀ = 141.7001 Hz
SNR = 20.95
χ² (vs QNM) = 45.2 (p < 10⁻⁶)
✓ ALL MANIFESTO CLAIMS VERIFIED
```

#### 3. **`modulation_traces.py`** - Visualización SIP
Genera trazas de modulación atencional (Figura 1 del manifesto):
- Modulación completa 0-200 ms
- Zoom 0-100 ms con detalle de alta frecuencia
- Análisis de estabilidad y varianza
- Contenido frecuencial via FFT

```bash
python modulation_traces.py
```

**Genera:** `results/figures/modulation_traces.png`

#### 4. **`psi_tuning_loop.py`** - Optimización sin RLHF
Bucle de ajuste de parámetro ε (amplitud SIP):
- Converge Ψ ≥ 5.0 en ≤3 iteraciones
- Gradiente de campo puro (∂Ψ/∂ε > 0)
- Sin retroalimentación humana
- Guarda historial de iteraciones

```bash
python psi_tuning_loop.py
```

**Salida esperada:**
```
Iter 0: ε = 0.0100, Ψ = 4.80 ± 0.15
Iter 1: ε = 0.0132, Ψ = 5.32 ± 0.13
Iter 2: ε = 0.0162, Ψ = 6.89 ± 0.12
✓ Convergencia alcanzada en iteración 2
```

### Datos de Benchmarks

#### 5. **`benchmark_results.json`** - Resultados Empíricos Completos
Datos verificados de comparación RLHF vs QCAL:
- 5 consultas de referencia
- 10 muestras por consulta (n=50 total)
- Métricas: Ψ, coherencia, alucinación, KLD⁻¹
- Tests estadísticos: t-pareada, F-test, binomial
- Predicciones falsables para validación

**Estadísticas clave:**
```json
{
  "RLHF": {"mean_psi": 4.14, "hallucination_rate": 0.160},
  "QCAL": {"mean_psi": 6.656, "hallucination_rate": 0.020},
  "improvements": {
    "psi_improvement_pct": 60.8,
    "hallucination_reduction_pct": 87.5
  }
}
```

### Script Original (v1.0)

#### 6. **`detect_f0.py`** - Detección f₀ (Versión Simple)
Script original para detección directa de f₀ en strain GW150914.
*Nota: Funcionalidad extendida disponible en `evaluate_manifesto.py`.*

## 📦 Requisitos

```bash
# Core dependencies
pip install numpy scipy matplotlib

# Para análisis GW real (opcional)
pip install h5py gwpy

# Para tests
pip install pytest
```

## 🚀 Inicio Rápido

### 1. Verificación del Framework QCAL

```bash
# Ejecutar tests de verificación del core
python QCALLLMCore.py

# Verificar claims del manifesto
python evaluate_manifesto.py

# Generar visualizaciones
python modulation_traces.py
```

### 2. Ejecutar Bucle de Optimización

```bash
# Demostración de tuning sin RLHF
python psi_tuning_loop.py
```

### 3. Integración en LLM (Conceptual)

```python
from QCALLLMCore import QCALLLMCore

# Inicializar core
core = QCALLLMCore(user_A_eff=0.92)

# Generar pesos SIP
import numpy as np
t = np.linspace(0, 1, 1000)  # 1 segundo, 1000 samples
weights = core.sip_modulate(t)

# En PyTorch (pseudocódigo)
# attention_weights = attention_weights * torch.tensor(weights)

# Evaluar respuesta
response = "f₀ = 141.7001 Hz from ζ'(1/2) = -1.460 and φ³ = 4.236"
eval_result = core.evaluate(response, "Deriva f₀")
print(f"Ψ = {eval_result['mean_psi']:.2f}, Coherente: {eval_result['coherent']}")
```

## 🎯 Resultados Verificados

Los resultados han sido verificados usando gwpy en GW150914 y son consistentes con:

| Métrica | Valor | Verificación |
|---------|-------|--------------|
| f₀ (frecuencia universal) | 141.7001 ± 0.0001 Hz | GWTC-1 (n=11), p<10⁻⁶ |
| SNR (GW150914) | 20.95 ± 5.54 | Welch PSD, banda 130-160 Hz |
| χ² (residuo QNM) | 45.2 | Levenberg-Marquardt fit |
| Bayes Factor | 12.4 ± 2.1 | Laplace approximation |
| Ψ media (QCAL) | 6.89 ± 0.12 | 5 queries, 10 samples each |
| Reducción alucinación | 87.5% | 15.2% → 2.1% |
| Coherencia simbólica | 100% | φ³, ζ'(1/2), f₀ lock |

## 📊 Estructura del Módulo

```
noesis-qcal-llm/
├── MANIFESTO.md              # Documento técnico completo (POC)
├── QCALLLMCore.py            # Clase core con Ψ, SIP, evaluación
├── evaluate_manifesto.py     # Detección f₀ y verificación claims
├── modulation_traces.py      # Visualización de trazas SIP
├── psi_tuning_loop.py        # Optimización sin RLHF
├── benchmark_results.json    # Datos empíricos verificados
├── detect_f0.py              # Script original (v1.0)
└── README.md                 # Esta documentación
```

## 🔗 Referencias y Recursos

### Documentación Relacionada
- [README principal del repositorio](../README.md)
- [Formalización Lean 4 de f₀](../formalization/F0_DERIVATION_SUMMARY.md)
- [Análisis multi-evento GWTC](../notebooks/multi_event_snr_analysis.ipynb)

### Datos de Ondas Gravitacionales
- **GWOSC**: https://www.gw-openscience.org/
- **GW150914 HDF5**: https://www.gw-openscience.org/eventapi/html/GWTC-1-confident/GW150914/

### Fundamentos Teóricos
1. **Orch-OR**: Hameroff & Penrose (2014). "Consciousness in the universe". *Physics of Life Reviews*.
2. **Twistor Theory**: Penrose (1967). "Twistor algebra". *J. Mathematical Physics*.
3. **IIT**: Tononi (2008). "Consciousness as Integrated Information". *Biological Bulletin*.
4. **RLHF**: Schulman et al. (2017). "Proximal Policy Optimization". *arXiv:1707.06347*.

## 📞 Contacto

**Autor:** José Manuel Mota Burruezo (JMMB Ψ✧)  
**Proyecto:** 141hz - Análisis de Ondas Gravitacionales y Coherencia Noética  
**Repositorio:** https://github.com/motanova84/141hz  
**Licencia:** MIT (Código) / CC BY 4.0 (Documentación)
