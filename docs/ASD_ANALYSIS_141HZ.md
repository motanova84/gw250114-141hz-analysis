# Análisis de ASD en 141.7 Hz para GW150914

## 📋 Descripción

Este documento describe el análisis de la Densidad Espectral de Amplitud (ASD - Amplitude Spectral Density) en la frecuencia objetivo de **141.7 Hz** para el evento GW150914 y días de control.

## 🎯 Objetivo

Implementar los 5 pasos del análisis de ruido especificados:

1. 📥 **Descargar segmentos de 32–64 s** para H1 y L1 alrededor de GW150914
2. 🧪 **Calcular el ASD** con `gwpy.timeseries.TimeSeries.asd()` o FFT
3. 📉 **Extraer el valor exacto** del ASD en 141.7 Hz
4. ⚖️ **Comparar amplitud de ruido** en L1 vs H1
5. 🔁 **Repetir en días sin eventos**, mismo tiempo UTC

## 🚀 Uso

### Análisis Básico

```bash
# Análisis estándar con 64 segundos y controles por defecto (1, 7, 30 días antes)
python scripts/analizar_asd_141hz.py
```

### Opciones Avanzadas

```bash
# Segmento de 32 segundos
python scripts/analizar_asd_141hz.py --duration 32

# Controles personalizados (1, 3 y 7 días antes)
python scripts/analizar_asd_141hz.py --control-days 1 3 7

# Sin generar gráficas
python scripts/analizar_asd_141hz.py --no-plot

# Con información detallada
python scripts/analizar_asd_141hz.py --verbose

# Directorio de salida personalizado
python scripts/analizar_asd_141hz.py --output-dir /ruta/personalizada
```

### Combinación de Opciones

```bash
# Análisis completo con todas las opciones
python scripts/analizar_asd_141hz.py \
  --duration 48 \
  --control-days 1 7 14 30 \
  --output-dir results/asd_custom \
  --verbose
```

## 📊 Salida

El script genera los siguientes archivos en el directorio de salida (default: `results/asd_analysis`):

### Archivos de Resultados

- **`asd_results.txt`**: Resultados numéricos detallados
  - Valores de ASD en 141.7 Hz para H1 y L1
  - Ratios de comparación L1/H1
  - Metadatos de cada análisis

### Gráficas Generadas

1. **`asd_comparison_full.png`**: ASDs completos (10-500 Hz)
   - Panel superior: H1 (Hanford)
   - Panel inferior: L1 (Livingston)
   - Línea vertical roja marca 141.7 Hz

2. **`asd_comparison_zoom.png`**: Zoom alrededor de 141.7 Hz (131.7-151.7 Hz)
   - H1 (línea continua)
   - L1 (línea discontinua)
   - Comparación directa en la región de interés

3. **`noise_ratio_comparison.png`**: Ratios L1/H1 para todos los análisis
   - Evento vs controles
   - Línea horizontal roja indica ruido igual (ratio = 1.0)

## 🔬 Metodología

### 1. Descarga de Datos

- **Fuente**: GWOSC (Gravitational Wave Open Science Center)
- **Detectores**: H1 (Hanford) y L1 (Livingston)
- **Sample rate**: 4096 Hz
- **Duración**: Configurable (32-64 s recomendado)
- **Centrado**: En el tiempo del merger de GW150914 (GPS 1126259462.423)

### 2. Cálculo de ASD

El ASD se calcula usando el método de Welch implementado en gwpy:

```python
asd = data.asd(fftlength=4, overlap=2)
```

- **fftlength**: 4 segundos (resolución de frecuencia ~0.25 Hz)
- **overlap**: 2 segundos (50% de solapamiento)
- **Resultado**: FrequencySeries con ASD en Hz^(-1/2)

### 3. Extracción en 141.7 Hz

Se encuentra la frecuencia más cercana a 141.7 Hz en el espectro discreto:

```python
idx = np.argmin(np.abs(freqs - 141.7))
asd_value = asd.value[idx]
```

### 4. Comparación L1 vs H1

Se calcula el ratio de ruido:

```
ratio = ASD_L1 / ASD_H1
diff_percent = (ratio - 1.0) × 100%
```

**Interpretación:**
- `ratio ≈ 1.0`: Niveles de ruido similares
- `ratio > 1.0`: L1 tiene más ruido que H1
- `ratio < 1.0`: H1 tiene más ruido que L1

### 5. Análisis de Control

Se repite el análisis en días anteriores al evento (sin señal gravitacional):
- Mismo tiempo UTC (hora del día)
- Diferentes días (default: -1d, -7d, -30d)
- Permite establecer línea base de ruido instrumental

## 📈 Interpretación de Resultados

### Niveles Típicos de ASD

En 141.7 Hz, los valores típicos de ASD son:

- **H1**: ~1-5 × 10^(-23) Hz^(-1/2)
- **L1**: ~1-5 × 10^(-23) Hz^(-1/2)

### Criterios de Evaluación

1. **Consistencia temporal**: Los valores de ASD deben ser similares entre el evento y los controles (variación < 30%)

2. **Consistencia inter-detector**: Los ratios L1/H1 deben ser consistentes (no cambios drásticos entre evento y controles)

3. **Líneas espectrales**: 141.7 Hz debe estar libre de líneas instrumentales conocidas (60 Hz, 120 Hz, etc.)

## 🧪 Testing

El script incluye una suite completa de tests:

```bash
# Ejecutar tests con pytest
pytest scripts/test_analizar_asd_141hz.py -v

# O ejecutar tests manualmente
python scripts/test_analizar_asd_141hz.py
```

### Tests Incluidos

- **Funciones básicas**: download_segment, calculate_asd, extract_asd_at_frequency
- **Análisis de pares**: analyze_detector_pair con diferentes escenarios
- **Generación de gráficas**: plot_asd_comparison
- **Guardado de resultados**: save_results_to_file
- **Integración completa**: Workflow completo end-to-end

## 📚 Referencias

- **GWOSC**: https://www.gw-openscience.org/
- **GWpy Documentation**: https://gwpy.github.io/
- **GW150914 Event**: https://www.ligo.org/detections/GW150914.php
- **Welch's Method**: Welch, P. (1967). "The use of fast Fourier transform for the estimation of power spectra"

## 🔧 Requisitos

- Python >= 3.9
- gwpy >= 3.0.0
- numpy >= 1.21.0
- matplotlib >= 3.5.0
- scipy >= 1.7.0

## 💡 Notas Importantes

1. **Conectividad**: El script requiere acceso a internet para descargar datos de GWOSC

2. **Tiempo de ejecución**: Depende de:
   - Duración del segmento (32-64s)
   - Número de controles
   - Velocidad de conexión
   - Típicamente: 2-5 minutos

3. **Espacio en disco**: Las gráficas ocupan ~1-2 MB por análisis

4. **Reproducibilidad**: Los resultados son determinísticos dado el mismo tiempo GPS y parámetros

## 🐛 Troubleshooting

### Error: "No se pudieron descargar los datos"

- Verificar conectividad a internet
- GWOSC puede estar temporalmente no disponible
- Intentar con otro rango de tiempo

### Error: "ASD calculation failed"

- Verificar que la duración sea >= 4 segundos
- Datos pueden estar corruptos para ese tiempo específico

### Advertencia: "Niveles de ruido muy diferentes"

- Esperado si uno de los detectores estaba en peor estado
- Revisar logs de operación de LIGO para esa fecha

## 📝 Ejemplo de Salida

```
🌌 ANÁLISIS DE ASD EN 141.7 Hz - GW150914
======================================================================
Frecuencia objetivo: 141.7 Hz
Duración del segmento: 64 s
======================================================================

📥 PASO 1-2: Descargando y analizando GW150914 (evento)
----------------------------------------------------------------------
   Descargando H1: GPS 1126259430.423 - 1126259494.423 (64s)
   ✅ H1: 262144 muestras @ 4096.0 Hz
   Descargando L1: GPS 1126259430.423 - 1126259494.423 (64s)
   ✅ L1: 262144 muestras @ 4096.0 Hz

🧪 Calculando ASD para ambos detectores...
📡 H1 (Hanford):
   ✅ ASD calculado: 8193 puntos de frecuencia
   Frecuencia más cercana: 141.750000 Hz (Δ = 0.050000 Hz)
   ✅ ASD en 141.750000 Hz: 2.456789e-23 Hz^(-1/2)

📡 L1 (Livingston):
   ✅ ASD calculado: 8193 puntos de frecuencia
   Frecuencia más cercana: 141.750000 Hz (Δ = 0.050000 Hz)
   ✅ ASD en 141.750000 Hz: 2.789012e-23 Hz^(-1/2)

⚖️  Comparación de ruido en 141.7 Hz:
   H1 ASD: 2.456789e-23 Hz^(-1/2)
   L1 ASD: 2.789012e-23 Hz^(-1/2)
   Ratio L1/H1: 1.1352
   Diferencia: +13.52%
   ⚠️  L1 tiene 13.5% MÁS ruido que H1

...

✅ ANÁLISIS COMPLETADO
======================================================================
📁 Resultados guardados en: results/asd_analysis
```

## 🤝 Contribuciones

Este análisis es parte del proyecto de investigación de la frecuencia 141.7 Hz en eventos de ondas gravitacionales. Para contribuir:

1. Fork del repositorio
2. Crear branch para tu feature
3. Hacer commits con cambios
4. Abrir Pull Request

## 📄 Licencia

MIT License - Ver LICENSE en el repositorio principal.
