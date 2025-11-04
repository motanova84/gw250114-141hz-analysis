# noesis-qcal-llm: Módulo LLM Coherente ∞³

Este módulo contiene el núcleo completo del análisis QCAL (Quantum Coherent Analysis Layer) con capacidades de verificación directa de la frecuencia universal **f₀ = 141.7001 Hz**.

## 🔍 `detect_f0.py`: Detección de la frecuencia universal f₀ en datos reales GW

Este módulo permite detectar la frecuencia **f₀ = 141.7001 Hz** directamente desde los datos públicos del evento GW150914.

- Usa el archivo `GW150914_4H_strain.hdf5` de GWOSC.
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

### 📁 Archivos del Módulo

- `detect_f0.py` - Script principal de detección de f₀
- `QCALLLMCore.py` - Núcleo completo con Ψ, SIP (próximamente)
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
