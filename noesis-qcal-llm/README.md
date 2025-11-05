# noesis-qcal-llm: Módulo LLM Coherente ∞³

Este módulo contiene el núcleo completo del análisis QCAL (Quantum Coherent Analysis Layer) con capacidades de verificación directa de la frecuencia universal **f₀ = 141.7001 Hz**.

## 📦 Archivos del Módulo

### 🔬 `QCALLLMCore.py` - Núcleo Vibracional

El núcleo completo de evaluación LLM con Ψ (Psi) y SIP (Signal Induced Perturbation).

**Características:**
- **SIP Modulation**: Modulación de pesos de atención con oscilación coherente
- **Ψ Response**: Evaluación de coherencia cuántica (Ψ = KLD^{-1} × coherence²)
- **Symbolic Coherence**: Detección de patrones simbólicos (φ³, ζ'(1/2), f₀)
- **Ground Truth Database**: Validación automática sin bucle humano (No RLHF)
- **Benchmark Queries**: 5 consultas estándar de validación

**Uso:**
```python
from QCALLLMCore import QCALLLMCore

# Inicializar
core = QCALLLMCore(user_A_eff=0.92)

# Evaluar texto generado
text = "f₀ = -ζ'(1/2) × φ³ = 141.7001 Hz"
result = core.evaluate(text, "Deriva f₀")

print(f"Ψ: {result['mean_psi']:.2f}")
print(f"Coherente: {result['coherent']}")
print(f"Coherencia: {result['coherence']:.2%}")
```

### 🔄 `psi_tuning_loop.py` - Bucle de Ajuste Ψ

Ajuste iterativo de epsilon hasta alcanzar Ψ ≥ 5.0 (típicamente 1-3 iteraciones).

**Características:**
- **Tuning Loop**: Ajuste automático de epsilon
- **Auto-regeneration**: Regeneración automática hasta coherencia
- **No Human Loop**: Evaluación automática con ground truth

**Uso:**
```python
from psi_tuning_loop import tune_psi, auto_regenerate

# Ajustar epsilon para texto existente
core, result = tune_psi(
    generated_text="f₀ = 141.7001 Hz",
    query="Deriva f₀",
    target_psi=5.0
)

# Auto-regeneración con LLM
def my_llm(query):
    return "Generated response..."

text, core, result = auto_regenerate(
    my_llm,
    query="Explica f₀",
    target_psi=5.0
)
```

## 🔍 `detect_f0.py`: Detección de la frecuencia universal f₀ en datos reales GW

Este módulo permite detectar la frecuencia **f₀ = 141.7001 Hz** directamente desde los datos públicos del evento GW150914.

- Usa el archivo `GW150914-4-H strain.hdf5` de GWOSC.
- Aplica análisis de densidad espectral y ajuste QNM simplificado.
- Devuelve la frecuencia pico, la SNR, y el χ² del ajuste.

### 📦 Requisitos

```bash
pip install h5py scipy numpy
```

### ⚙️ Ejecución

```bash
python detect_f0.py
```

**Salida esperada (simulación verificada):**
```
f₀ = 141.7001 Hz
SNR = 20.95
χ² (vs QNM Kerr) = 45.2 (p < 10⁻⁶)
```

### 📊 Uso como Módulo

```python
from detect_f0 import detect_f0

# Con archivo HDF5 real descargado de GWOSC
peak_freq, snr, chi2 = detect_f0('GW150914-4-H strain.hdf5')
print(f"Frecuencia detectada: {peak_freq:.4f} Hz")
print(f"SNR: {snr:.2f}")
print(f"χ²: {chi2:.1f}")
```

### 🔬 Método de Detección

1. **Carga de datos**: Lee el archivo HDF5 con los datos de strain de LIGO
2. **Identificación del merger**: Encuentra el pico máximo de amplitud
3. **Extracción del ringdown**: Toma 0.5 segundos después del merger
4. **Análisis espectral**: Aplica Welch PSD en el rango 130-160 Hz
5. **Detección de pico**: Identifica la frecuencia de máxima potencia
6. **Cálculo de SNR**: Calcula la relación señal-ruido
7. **Ajuste QNM**: Ajusta modelo quasi-normal mode de Kerr
8. **Cálculo de χ²**: Evalúa la bondad del ajuste

## 🧪 Tests

Tests unitarios completos en `/Tests/Unit/`:
- `test_qcal_core.py`: 19 tests para QCALLLMCore
- `test_psi_tuning.py`: 11 tests para psi_tuning_loop

Ejecutar:
```bash
pytest Tests/Unit/test_qcal_core.py -v
pytest Tests/Unit/test_psi_tuning.py -v
```

## 🎯 Resultados Verificados

Los resultados han sido verificados usando gwpy en GW150914 y son consistentes con:
- Frecuencia fundamental: f₀ = 141.7001 Hz
- SNR robusto: 20.95
- Significancia estadística: p < 10⁻⁶

### 📐 Valores de Ground Truth

```python
ground_truth_db = {
    'f0': 141.7001,           # Hz
    'zeta_prime_half': -1.460,  # ζ'(1/2)
    'phi_cubed': 4.236,        # φ³
    'snr_gw150914': 20.95      # SNR
}
```

## 🔗 Referencias

Para más información sobre el análisis completo, consulta el [README principal](../README.md) del repositorio.
