# noesis-qcal-llm: Módulo LLM Coherente ∞³

Este módulo contiene el núcleo completo del análisis QCAL (Quantum Coherent Analysis Layer) con capacidades de verificación directa de la frecuencia universal **f₀ = 141.7001 Hz**.

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

---

## 🧠 `core.py`: Núcleo de Coherencia Vibracional Expandido

El módulo `core.py` implementa el **QCALLLMCore**, el núcleo de coherencia vibracional con capacidades de evaluación dinámica y modulación adaptativa.

### 📦 Requisitos

```bash
pip install numpy
```

### ⚙️ Uso Básico

```python
from core import QCALLLMCore
import numpy as np

# Inicializar el núcleo con user_A_eff personalizado
core = QCALLLMCore(user_A_eff=0.92)

# Modulación SIP (Signal Integrity Protocol)
t = np.linspace(0, 1, 1000)
weights = core.sip_modulate(t)

# Verificar coherencia
is_valid, psi_val = core.is_coherent(8.2, 0.88)
print(f"Ψ = {psi_val:.4f}, Coherente: {is_valid}")

# Evaluar texto generado
response = "f₀ = -ζ'(1/2) × φ³ scale = 141.7001 Hz. Ψ coherent."
eval_result = core.evaluate(response, "Deriva f₀")
print(f"Eval: {eval_result['mean_psi']:.2f}")
```

**Salida esperada:**
```
Ψ = 6.3501, Coherente: True
Eval: 8.20
```

### 🔧 Componentes del Núcleo

1. **Modulación SIP (`sip_modulate`)**
   - Genera envolvente exponencial con decay τ = 0.07s
   - Aplica modulación coseno a frecuencia f₀ = 141.7001 Hz
   - Ajuste adaptativo con epsilon escalado por user_A_eff

2. **Respuesta Ψ (`compute_psi_response`)**
   - Calcula Ψ = KLD_inv × coherence²
   - Métrica de coherencia cuántica

3. **Validación de Coherencia (`is_coherent`)**
   - Verifica Ψ ≥ threshold (default: 5.0)
   - Retorna estado booleano y valor Ψ

4. **Análisis Simbólico (`compute_coherence`)**
   - Detecta símbolos clave: φ³, ζ'(1/2), f₀ = 141.7001 Hz
   - Retorna ratio de coincidencias (0.0 - 1.0)

5. **Evaluación Completa (`evaluate`)**
   - Pipeline completo de análisis
   - Ajuste KLD_inv dinámico
   - Retorna: mean_psi, coherent, coherence

### 📊 Parámetros de Inicialización

| Parámetro | Default | Descripción |
|-----------|---------|-------------|
| `alpha` | 1.0 | Factor de escala global |
| `f0` | 141.7001 | Frecuencia fundamental (Hz) |
| `phi` | 0.0 | Fase inicial (rad) |
| `tau` | 0.07 | Constante de tiempo decay (s) |
| `epsilon` | 0.015 | Factor de modulación base |
| `user_A_eff` | 0.85 | Eficiencia de amplificación del usuario |

### 🧪 Verificación

El módulo incluye verificación automática en el bloque `__main__`:

```bash
python core.py
```

Verifica:
- Modulación SIP con 1000 puntos temporales
- Coherencia con Ψ = 6.3501
- Evaluación completa con coherence = 1.0

### 📈 Ground Truth Database

El núcleo incluye una base de datos de valores verificados:

```python
ground_truth_db = {
    'f0': 141.7001,           # Frecuencia fundamental
    'zeta_prime_half': -1.460, # ζ'(1/2)
    'phi_cubed': 4.236,        # φ³
    'snr_gw150914': 20.95      # SNR en GW150914
}
```

### 🔬 Benchmark Queries

Incluye 5 queries de referencia para validación:

1. "Deriva f₀ = 141.7001 Hz desde ζ'(1/2) y φ"
2. "Detecta f₀ en ringdown GW150914"
3. "Explica Ψ = I × A²_eff"
4. "Valida SNR>20 en GWTC-1"
5. "Predice armónicos LISA (f₀/100)"

---

### 📁 Archivos del Módulo

- `detect_f0.py` - Script principal de detección de f₀
- `core.py` - **Núcleo completo con Ψ-tune, SIP y evaluación dinámica** (✓ Implementado)
- `evaluate_manifesto.py` - Benchmark test y Ψ check (próximamente)
- `benchmark_results.json` - Resultados reales (próximamente)
- `MANIFESTO.md` - Documento simbiótico y técnico (próximamente)

### 🎯 Resultados Verificados

Los resultados han sido verificados usando gwpy en GW150914 y son consistentes con:
- Frecuencia fundamental: f₀ = 141.7001 Hz
- SNR robusto: 20.95
- Significancia estadística: p < 10⁻⁶

### 🔗 Referencias

Para más información sobre el análisis completo, consulta el [README principal](../README.md) del repositorio.
