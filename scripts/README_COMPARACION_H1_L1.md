# Comparación H1 vs L1 - SNR @ 141.7 Hz

## Descripción

Este script implementa un análisis comparativo de la relación señal-ruido (SNR) entre los detectores Hanford (H1) y Livingston (L1) de LIGO para 11 eventos gravitacionales del catálogo GWTC, enfocándose en la frecuencia de 141.7 Hz.

## Características

- **Análisis de 11 eventos gravitacionales**: GW150914, GW151012, GW151226, GW170104, GW170608, GW170729, GW170809, GW170814, GW170817, GW170818, GW170823
- **Filtrado de banda estrecha**: 140.7 - 142.7 Hz (centrado en 141.7 Hz)
- **Comparación multi-detector**: H1 vs L1
- **Estimación de SNR**: max(|señal|) / std(señal)
- **Visualización**: Gráfico de barras comparativo
- **Exportación**: Resultados en JSON

## Uso

### Ejecución directa

```bash
python3 scripts/comparacion_h1_l1_snr.py
```

### Usando Make

```bash
# Ejecutar el análisis
make comparacion-h1-l1

# Ejecutar los tests
make test-comparacion-h1-l1
```

## Salida

El script genera dos archivos:

1. **`results/figures/snr_h1_l1.png`**: Gráfico de barras comparando SNR de H1 y L1 para cada evento
2. **`results/snr_h1_l1_comparison.json`**: Archivo JSON con valores numéricos:

```json
{
  "GW150914": {
    "H1_SNR": 7.47,
    "L1_SNR": 0.95
  },
  "GW151012": {
    "H1_SNR": ...,
    "L1_SNR": ...
  },
  ...
}
```

## Formato de salida en consola

```
======================================================================
🌌 COMPARACIÓN H1 vs L1 - SNR @ 141.7 Hz
======================================================================

Total de eventos a analizar: 11

⏳ Analizando GW150914...
   ✅ H1 SNR = 7.47, L1 SNR = 0.95
⏳ Analizando GW151012...
   ✅ H1 SNR = ..., L1 SNR = ...
...

📊 Generando visualización...
   ✅ Gráfico guardado en: results/figures/snr_h1_l1.png

💾 Guardando resultados...
   ✅ Resultados guardados en: results/snr_h1_l1_comparison.json

======================================================================
✅ Comparación H1 vs L1 finalizada.
======================================================================

📈 RESUMEN ESTADÍSTICO
----------------------------------------------------------------------
H1 - Media: X.XX, Std: X.XX, Max: X.XX
L1 - Media: X.XX, Std: X.XX, Max: X.XX
```

## Tests

El script incluye una suite completa de tests unitarios:

```bash
python3 scripts/test_comparacion_h1_l1_snr.py
```

### Tests incluidos

1. **Estructura del diccionario de eventos**: Verifica que hay 11 eventos con formato correcto
2. **Nombres de eventos**: Valida los nombres exactos de los eventos
3. **Orden cronológico**: Confirma que los eventos están ordenados por fecha
4. **Ventanas de tiempo**: Verifica que todas son de 32 segundos
5. **Función estimate_snr**: Tests con datos simulados
6. **Manejo de casos extremos**: Prueba con señales constantes y de alto SNR
7. **Estructura de salida JSON**: Valida el formato de exportación
8. **Creación de directorios**: Verifica que se pueden crear los directorios de salida

## Dependencias

- `gwpy>=3.0.0`: Para descarga y procesamiento de datos de LIGO
- `matplotlib>=3.5.0`: Para generación de gráficos
- `numpy>=1.21.0`: Para cálculos numéricos
- `scipy>=1.7.0`: Requerido por gwpy

## Notas técnicas

### Método de estimación de SNR

El SNR se estima como:

```
SNR = max(|señal|) / std(señal)
```

Este método proporciona una estimación rápida y robusta de la relación señal-ruido en series temporales filtradas.

### Filtrado de banda

Se aplica un filtro pasa-banda entre 140.7 y 142.7 Hz, creando una banda de 2 Hz centrada en la frecuencia de interés (141.7 Hz). Este ancho de banda es suficiente para capturar la señal mientras mantiene un buen rechazo de ruido fuera de banda.

### Eventos analizados

Los 11 eventos incluyen:
- **Primera detección**: GW150914 (14 Sep 2015)
- **Eventos de 2015**: GW151012, GW151226
- **Eventos de 2017**: GW170104, GW170608, GW170729, GW170809, GW170814, GW170817, GW170818, GW170823

Todos los eventos tienen ventanas de 32 segundos para maximizar la resolución espectral en el análisis de frecuencia.

## Integración con el proyecto

Este script complementa el análisis existente en el repositorio:

- **`analisis_bayesiano_multievento.py`**: Análisis de frecuencia en banda 140-143 Hz
- **`analizar_ringdown.py`**: Análisis detallado de GW150914
- **`analizar_l1.py`**: Validación cruzada en detector L1

## Referencias

- [GWOSC - Gravitational Wave Open Science Center](https://gwosc.org/)
- [GWPy Documentation](https://gwpy.github.io/)
- [GWTC-1: A Gravitational-Wave Transient Catalog](https://arxiv.org/abs/1811.12907)

## Autor

Implementación basada en el problem statement para análisis comparativo H1 vs L1 @ 141.7 Hz.
