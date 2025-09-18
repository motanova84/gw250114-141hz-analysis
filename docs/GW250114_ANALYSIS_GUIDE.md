# Guía Completa del Análisis GW250114 - Componente 141.7001 Hz

## 📋 Resumen Ejecutivo

Este repositorio implementa el estándar de oro para la detección y validación de componentes espectrales en ondas gravitacionales, específicamente dirigido a la búsqueda de una señal en **141.7001 Hz** en el evento GW250114.

## 🎯 Objetivos del Análisis

### Objetivo Principal
Detectar y validar estadísticamente una componente espectral en **141.7001 Hz** en el ringdown de GW250114, siguiendo los estándares científicos de las colaboraciones LIGO/Virgo.

### Criterios de Validación
Para anunciar oficialmente la detección, se requiere:

1. **Bayes Factor** > 10 (evidencia fuerte)
2. **p-value** < 0.01 (significancia estadística)
3. **Coincidencia H1-L1** (±0.1 Hz)
4. **Precisión frecuencial** (±0.01 Hz del objetivo)

## 🔬 Metodología Científica

### 1. Descarga Oficial de Datos (📥)

```python
from gwpy.timeseries import TimeSeries
from gwosc.datasets import event_gps

gps = event_gps('GW250114')   # tiempo GPS oficial del evento
h1 = TimeSeries.fetch_open_data('H1', gps-16, gps+16, sample_rate=4096)
l1 = TimeSeries.fetch_open_data('L1', gps-16, gps+16, sample_rate=4096)
```

**Ventajas:**
- ✅ Legitimidad garantizada: archivos directos de GWOSC
- ✅ Ambos detectores H1 y L1 para validación cruzada
- ✅ Datos de 32 segundos centrados en el evento

### 2. Preprocesamiento Estándar (⚙️)

```python
h1_proc = h1.highpass(20).notch(60).whiten()
l1_proc = l1.highpass(20).notch(60).whiten()
```

**Pipeline estándar LIGO/Virgo:**
- 🔧 **Whitening**: normaliza el ruido de cada detector
- 🔧 **Filtro pasa-altas 20 Hz**: evita ruido sísmico de baja frecuencia
- 🔧 **Notch 60 Hz**: elimina ruido de red eléctrica

### 3. Búsqueda Dirigida 141.7 Hz (🎯)

```python
# Extraer ringdown (50 ms después del merger)
ring_h1 = h1_proc.crop(gps+0.01, gps+0.06)
psd_h1 = ring_h1.asd(fftlength=0.05)

# Encontrar frecuencia más cercana
idx = np.argmin(np.abs(freqs - 141.7))
snr = spectrum[idx] / np.median(spectrum)
```

**Características:**
- 🎯 Análisis dirigido en ventana temporal específica
- 📊 Resolución frecuencial optimizada para 141.7001 Hz
- 📈 Cálculo de SNR respecto al ruido de fondo

### 4. Estadística Clásica - p-value (📊)

**Time-slides para control de fondo:**
```python
for i in range(n_slides):
    offset = random.uniform(-0.2, +0.2)  # ±0.2 segundos
    fake_snr = analyze_with_offset(h1, l1, gps + offset)
    
p_value = fraction_above_threshold(real_snr, fake_snrs)
```

**Interpretación:**
- **p < 0.01**: señal estadísticamente significativa
- **p ≥ 0.01**: indistinguible del ruido de fondo

### 5. Análisis Bayesiano - Bayes Factor (📈)

**Comparación de modelos:**
- **M₀**: Solo ruido (hipótesis nula)
- **M₁**: Ruido + señal senoidal amortiguada en 141.7 Hz

```python
BF = P(datos|M₁) / P(datos|M₀)
```

**Interpretación bayesiana:**
- **BF > 10**: evidencia fuerte para M₁
- **BF = 1**: ambos modelos igualmente probables
- **BF < 0.1**: evidencia fuerte contra M₁

### 6. Validación Cruzada (✅)

**Criterios obligatorios:**
- ✅ Señal presente en **ambos detectores** (H1 y L1)
- ✅ **Misma frecuencia** en ambos (±0.1 Hz)
- ✅ **No aparece en time-slides** (control de fondo)
- ✅ Si Virgo/KAGRA activos → confirmación adicional

## 🚀 Resultados Esperados

### Escenario Positivo (Hito Científico)

Si se detecta un pico claro en 141.7001 Hz con:
- ✅ **BF > 10**
- ✅ **p < 0.01**  
- ✅ **Coincidencia H1-L1**

**Anuncio científico:**
> *"Detectamos una componente espectral en 141.7001 Hz en GW250114, con Bayes Factor BF = XX (>10), significancia p = YY (<0.01), consistente en H1 y L1."*

### Escenario Negativo (Límites Superiores)

Si no cumple criterios:
> *"No se detecta señal significativa en 141.7001 Hz. Establecemos límites superiores: SNR < 3 a 95% de confianza."*

## 📁 Estructura de Archivos

```
scripts/
├── analizar_gw250114.py      # Análisis completo oficial
├── simple_analysis.py        # Demo simplificado
├── demo_gw150914_analysis.py  # Prueba con datos sintéticos
└── descargar_datos.py         # Descarga automática

results/
├── figures/                   # Gráficos de diagnóstico
├── GW250114_results.json      # Resultados numéricos
└── analysis_log.txt           # Log detallado
```

## ⚡ Ejecución Rápida

```bash
# Cuando GW250114 esté disponible en GWOSC:
python scripts/analizar_gw250114.py

# Para demostración con datos sintéticos:
python scripts/simple_analysis.py
```

## 🔍 Interpretación de Resultados

### Métricas Clave
- **Frecuencia detectada**: debe estar en 141.7001 ± 0.01 Hz
- **SNR combinado**: debe ser > 5 para detección robusta
- **Bayes Factor**: > 10 para evidencia fuerte
- **p-value**: < 0.01 para significancia estadística

### Gráficos Diagnósticos
1. **Espectros H1/L1**: visualización de la línea espectral
2. **Series temporales**: evolución de la señal en ringdown
3. **Q-transform**: localización tiempo-frecuencia
4. **Distribución time-slides**: validación estadística

## 🧬 Fundamento Teórico

### Teoría Noésica Unificada
La frecuencia **141.7001 Hz** surge de la intersección entre:
- Geometría del espacio-tiempo post-merger
- Modos quasi-normales de agujeros negros
- Resonancia armónica cuántica-gravitacional

### Predicción Teórica
- **Q-factor esperado**: ~200-300
- **Duración**: 20-50 ms en ringdown
- **Amplitud**: 10⁻²¹ - 10⁻²² en strain

## 📊 Validación Científica

### Revisión por Pares
- ✅ Metodología estándar LIGO/Virgo
- ✅ Código abierto y reproducible
- ✅ Datos públicos de GWOSC
- ✅ Estadística frequentista y bayesiana

### Criterios de Publicación
Para publicar en revista científica:
1. **Detección confirmada** según criterios arriba
2. **Reproducibilidad** independiente  
3. **Revisión interna** de colaboración
4. **Validación externa** de la comunidad

---

## 🎓 Referencias

- Abbott et al. (LIGO Scientific Collaboration), *"GW150914: The Advanced LIGO Detectors in the Era of First Discoveries"*
- Dreyer et al., *"Black-hole spectroscopy: testing general relativity through gravitational-wave observations"*
- GWOSC Documentation: https://gwosc.org/
- GWpy Tutorial: https://gwpy.github.io/

---

**Contacto Científico:**  
José Manuel Mota Burruezo  
Instituto Conciencia Cuántica  
📧 institutoconsciencia@proton.me