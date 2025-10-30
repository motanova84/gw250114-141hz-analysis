# Prerregistro (versión 1.0)

## Objetivo

Protocolo de análisis ciego para detectar y validar la presencia de una componente espectral en 141.7001 Hz en eventos de ondas gravitacionales del catálogo GWTC.

## Parámetros Predefinidos

### Ventana Temporal
- **Ventana**: [t0-0.25 s, t0+0.25 s] alrededor de coalescencia publicada
- **Justificación**: Captura la fase de ringdown sin extenderse a regiones de ruido dominante

### Método de Análisis SNR
- **PSD**: Welch con Nfft=2^14 (16384 puntos), 50% overlap
- **Ventana**: Hann
- **Banda de análisis**: 20–1024 Hz
- **Whitening**: Por detector (normalización independiente H1, L1, V1)

### Frecuencia Objetivo
- **f0**: 141.7001 Hz (±0.3 Hz) — *predefinida por predicción teórica*
- **Banda de interés**: [141.4001, 142.0001] Hz

### Estadística Final
- **SNR coherente**: Productoria/mezcla Fisher entre detectores
- **Bayes Factor**: Modelo jerárquico con parámetro π_global (fracción de eventos con tono coherente)

## Controles de Validación

### Corrección por Múltiples Eventos
- **Método**: Modelo jerárquico bayesiano
- **Parámetro**: π_global (probabilidad de que un evento arbitrario contenga la señal)
- **Prior**: Beta(1,1) (uniforme en [0,1])

### Exclusiones de Líneas Instrumentales
- **Fuente**: `controls/lines_exclusion.csv`
- **Criterio**: Frecuencias con líneas instrumentales conocidas (armónicos de red eléctrica, resonancias mecánicas) son excluidas del análisis

### Off-Source Validation
- **Número de ventanas**: 10^4 por evento
- **Distribución**: Uniforme en tiempos fuera de ±10 s alrededor de coalescencia
- **Objetivo**: Estimar distribución nula de SNR bajo ausencia de señal

### Time-Slides
- **Número de desfasajes**: 200 por par de detectores
- **Rango**: ±50 ms, excluyendo desfase cero
- **Objetivo**: Destruir coherencia física entre detectores manteniendo ruido instrumental

### Leave-One-Out Validation
- **Por evento**: Análisis excluyendo un evento a la vez
- **Por detector**: Análisis usando solo un detector a la vez
- **Objetivo**: Verificar robustez de la señal ante exclusión de datos individuales

## Cierre del Plan

**Hash del plan**: Este documento será hasheado y depositado en Zenodo antes de cualquier corrida masiva de análisis.

**Timestamp de prerregistro**: 2025-10-30

**Versión**: 1.0

---

## Criterios de Éxito Predefinidos

1. **Detección primaria**: SNR coherente > 5.0 en al menos 8/11 eventos de GWTC-1
2. **Coherencia multi-detector**: Correlación de fase entre H1 y L1 > 0.7
3. **Off-source null**: p-value < 0.01 comparando on-source vs off-source
4. **Time-slide null**: BF_coherent / BF_timeslides > 10
5. **Leave-one-out estabilidad**: Desviación estándar de SNR_global < 20% al excluir eventos individuales

## Falsación

El resultado se considerará **falsado** si:
- SNR medio cae por debajo de 3.0 sigma
- Off-source produce igual o mayor número de "detecciones"
- Time-slides no reducen significancia (BF ratio < 3)
- Patrón de antena no es consistente con fuente astronómica
- Líneas instrumentales conocidas explican la señal

---

**Investigador Principal**: José Manuel Mota Burruezo (JMMB Ψ✧)  
**Fecha de prerregistro**: 30 de Octubre de 2025  
**Licencia**: MIT  
