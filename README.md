# Análisis de Componente en 141.7 Hz - GW150914

Este proyecto realiza el análisis espectral de datos de ondas gravitacionales para detectar componentes específicas en 141.7 Hz en el ringdown de GW150914.

## Características

- Descarga automatizada de datos de GWOSC (Gravitational Wave Open Science Center)
- Análisis espectral avanzado con FFT
- Detección de picos espectrales cerca de 141.7 Hz
- Generación automática de gráficos de diagnóstico
- Cálculo de relación señal-ruido (SNR)

## Estructura del Proyecto

```
├── scripts/
│   ├── descargar_datos.py       # Descarga datos reales de GWOSC
│   ├── generar_datos_prueba.py  # Genera datos simulados para testing
│   └── analizar_ringdown.py     # Análisis espectral principal
├── data/raw/                    # Datos descargados (no incluidos en git)
├── results/figures/             # Gráficos generados (no incluidos en git)
├── requirements.txt             # Dependencias Python
└── Makefile                    # Automatización del workflow
```

## Uso Rápido

### Opción 1: Con datos reales (requiere internet)
```bash
make setup      # Instalar dependencias
make download   # Descargar datos de GWOSC
make analyze    # Realizar análisis
```

### Opción 2: Con datos simulados (para testing)
```bash
make all        # Ejecuta setup + test-data + analyze
```

### Opción 3: Paso a paso
```bash
# 1. Crear entorno virtual e instalar dependencias
make setup

# 2a. Descargar datos reales (requiere conexión a internet)
make download

# 2b. O generar datos simulados para prueba
make test-data

# 3. Ejecutar análisis
make analyze
```

## Comandos Disponibles

- `make setup` - Configurar entorno virtual e instalar dependencias
- `make download` - Descargar datos reales de GW150914 desde GWOSC
- `make test-data` - Generar datos simulados con señal en 141.7 Hz
- `make analyze` - Ejecutar análisis espectral y generar gráficos
- `make all` - Ejecutar workflow completo con datos simulados
- `make clean` - Limpiar archivos de datos y resultados
- `make clean-all` - Limpiar todo incluyendo entorno virtual

## Resultados

El análisis genera:

1. **Detección de frecuencia**: Identifica el pico espectral más cercano a 141.7 Hz
2. **Cálculo de SNR**: Relación señal-ruido aproximada del pico detectado
3. **Gráficos de diagnóstico**:
   - Serie temporal de la señal
   - Espectro de potencia completo (100-200 Hz)
   - Zoom del espectro (130-160 Hz) alrededor de 141.7 Hz
   - Histograma de distribución de potencia

Los gráficos se guardan en `results/figures/` como archivos PNG de alta resolución.

## Dependencias

- Python 3.8+
- gwpy >= 3.0.0 (para manejo de datos gravitacionales)
- numpy >= 1.21.0 (cálculos numéricos)
- scipy >= 1.7.0 (transformadas de Fourier)
- matplotlib >= 3.5.0 (visualización)
- h5py >= 3.7.0 (formato de datos HDF5)
- astropy >= 5.0 (astronomía y tiempo GPS)

## Notas Técnicas

- Los datos se almacenan en formato HDF5 compatible con gwpy
- El análisis se enfoca en el rango de frecuencias 100-200 Hz
- La señal de prueba incluye ruido gaussiano realista
- El análisis busca componentes en el ringdown post-merger

## Troubleshooting

Si hay problemas de conexión para descargar datos reales, usa `make test-data` para generar datos simulados que incluyen una señal artificial en 141.7 Hz.

## Limpieza

```bash
make clean      # Solo datos y resultados
make clean-all  # Incluye entorno virtual
```
