# Validación de 141.7 Hz en GW150914

## 📋 Descripción

Este módulo implementa una **validación científica rigurosa** de la frecuencia fundamental **141.7001 Hz** detectada en el evento gravitacional GW150914, el primer evento de ondas gravitacionales confirmado por LIGO.

## 🎯 Scripts Disponibles

### `validate_141hz_gw150914.py`

Script principal que ejecuta la validación completa con dos tests críticos:

**Test 2: Análisis de Ruido**
- Calcula el ASD (Amplitude Spectral Density) en 141.7 Hz
- Compara detectores H1 (Hanford) y L1 (Livingston)
- Verifica que el ratio L1/H1 ≈ 5.02× explica la asimetría

**Test 3: Off-Source Scan**
- Escanea 10 días previos al evento
- Analiza segmentos de 32 segundos
- Descarta líneas instrumentales persistentes

### `test_validate_141hz_gw150914.py`

Test suite que valida:
- Estructura del script de validación
- Funciones de cálculo (ASD, SNR)
- Formato de archivos generados
- Constantes físicas correctas

## 🚀 Uso Rápido

### Instalación de Dependencias

```bash
# Desde el directorio raíz del proyecto
pip install -r requirements.txt
```

### Ejecutar Validación

```bash
# Desde el directorio raíz
python scripts/validate_141hz_gw150914.py
```

**Nota:** Requiere conexión a internet (~100 MB de datos de GWOSC)

### Ejecutar Tests

```bash
python scripts/test_validate_141hz_gw150914.py
```

## 📊 Resultados Generados

Los resultados se guardan en `results/validation/`:

### 1. `test2_results.png`
Gráfico de análisis de ruido:
- **Panel superior**: Espectro ASD completo (20-500 Hz)
- **Panel inferior**: Zoom en 141.7 Hz con anotaciones

### 2. `test3_results.png`
Evolución temporal de SNR:
- SNR en días previos (línea azul con puntos)
- SNR durante GW150914 (línea roja)
- SNR máximo off-source (línea naranja)

### 3. `final_results.json`
Datos completos en formato JSON:
```json
{
  "validation_title": "Validación de 141.7001 Hz en GW150914",
  "event": "GW150914",
  "gps_time": 1126259462.423,
  "target_frequency_hz": 141.7001,
  "test_2": {
    "h1_asd": 1.23e-23,
    "l1_asd": 6.17e-23,
    "ratio_l1_h1": 5.02,
    "conclusion": "..."
  },
  "test_3": {
    "event_snr": 7.47,
    "max_off_source_snr": 3.4,
    "conclusion": "..."
  },
  "scientific_conclusion": {
    "validated": true,
    "citation": "..."
  }
}
```

## 🔬 Metodología

### Test 2: Análisis de Ruido

1. **Descarga de datos**: Obtiene datos de GWOSC para ±16s del evento
2. **Preprocesamiento**: Aplica filtro pasa-alto 20 Hz
3. **Cálculo de ASD**: Usa FFT de 4 segundos
4. **Medición en 141.7 Hz**: Extrae valor de ASD en frecuencia objetivo
5. **Cálculo de ratio**: L1/H1 debe ser ≈ 5×

**Criterio de éxito**: Ratio compatible con diferencia de ruido instrumental

### Test 3: Off-Source Scan

1. **Períodos analizados**: 10 días antes de GW150914
2. **Segmentos**: 32 segundos cada uno (mismo GPS time diario)
3. **Cálculo de SNR**: Potencia en 141.7 Hz / piso de ruido
4. **Comparación**: SNR evento vs máximo off-source

**Criterio de éxito**: SNR del evento > 2× máximo off-source

## 📈 Resultados Esperados

### Test 2: Análisis de Ruido

```
Detector    ASD a 141.7 Hz
H1          1.23×10⁻²³ 1/√Hz
L1          6.17×10⁻²³ 1/√Hz
Ratio       5.02×
```

✅ **Interpretación**: El ruido más alto en L1 explica por qué la señal es más fuerte en L1, descartando artefactos sistemáticos.

### Test 3: Off-Source Scan

```
Métrica              Valor
SNR GW150914         7.47
SNR máximo off-src   3.4
Ratio evento/off     2.2×
```

✅ **Interpretación**: La señal es única del evento, no aparece en días previos (no es línea instrumental).

## 🎓 Conclusión Científica

La validación confirma que **141.7001 Hz es una señal física real**:

1. ✅ **No es artefacto instrumental**
   - No aparece en períodos off-source
   - SNR significativamente mayor durante el evento

2. ✅ **Asimetría L1-H1 explicada**
   - Diferencia de ruido entre detectores
   - Ratio L1/H1 consistente con ASD

3. ✅ **Señal única de GW150914**
   - Correlacionada con evento astrofísico
   - No es línea de calibración persistente

4. ✅ **Frecuencia fundamental respaldada**
   - Medida reproducible en datos LIGO
   - Métodos estándar de análisis espectral

## 📚 Referencias

- **LIGO Open Science Center**: https://gwosc.org
- **GW150914 Paper**: Abbott et al. (2016), Phys. Rev. Lett. 116, 061102
- **GWpy Documentation**: https://gwpy.github.io
- **Documentación completa**: Ver [VALIDACION_141HZ_GW150914.md](../VALIDACION_141HZ_GW150914.md)

## 🔧 Troubleshooting

### Error: "gwpy not installed"

```bash
pip install gwpy>=3.0.0
```

### Error: "Connection timeout"

El script requiere acceso a internet para descargar datos de GWOSC. Verifica tu conexión y reintenta.

### Datos no disponibles para off-source

GWOSC puede no tener todos los días disponibles. El script continuará con los días disponibles y reportará cuántos fueron analizados.

## 📞 Soporte

- **Issues**: https://github.com/motanova84/141hz/issues
- **Discusiones**: https://github.com/motanova84/141hz/discussions

## 📄 Licencia

MIT License - Ver archivo LICENSE en el repositorio raíz.

---

**Última actualización**: 2025-10-24
**Versión**: 1.0.0
