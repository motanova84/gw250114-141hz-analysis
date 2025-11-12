# CLI — Interfaz de Línea de Comandos

QCAL proporciona una interfaz de línea de comandos robusta para análisis de coherencia en datos de ondas gravitacionales.

## Instalación

```bash
# Clonar el repositorio
git clone https://github.com/motanova84/141hz.git
cd 141hz

# Crear entorno virtual
python -m venv venv
source venv/bin/activate  # En Windows: venv\Scripts\activate

# Instalar dependencias
pip install -r requirements.txt
```

## Comando principal: `qcal analyze`

### Uso básico

```bash
qcal analyze --event GW150914 --detector H1 --freq 141.7
```

### Parámetros

| Parámetro | Tipo | Descripción | Requerido | Default |
|-----------|------|-------------|-----------|---------|
| `--event` | str | ID del evento (e.g., GW150914) | Sí | - |
| `--detector` | str | Detector (H1, L1, V1) | Sí | - |
| `--freq` | float | Frecuencia objetivo (Hz) | No | 141.7 |
| `--output` | str | Directorio de salida | No | `results/` |
| `--format` | str | Formato: `json`, `csv`, `png` | No | `json,png` |

### Ejemplos

#### Análisis estándar de GW150914

```bash
qcal analyze --event GW150914 --detector H1
```

#### Análisis multi-detector

```bash
qcal analyze --event GW150914 --detector H1 --output results/h1/
qcal analyze --event GW150914 --detector L1 --output results/l1/
```

#### Exportar solo CSV

```bash
qcal analyze --event GW150914 --detector H1 --format csv
```

## Scripts auxiliares

### Validación completa

```bash
python run_all_validations.py
```

Ejecuta todas las validaciones del proyecto:
- Validación de radio cuántico
- Validación de energía cuántica
- Validación de simetría discreta
- Tests unitarios

### Análisis multi-evento

```bash
python multi_event_analysis.py
```

Analiza múltiples eventos de GWTC-1 en paralelo.

## Salida

Los resultados se guardan en el directorio especificado con `--output`:

```
results/
├── GW150914_H1_141.7Hz.json    # Resultados numéricos
├── GW150914_H1_spectrum.png    # Espectro de potencia
└── GW150914_H1_timeseries.png  # Serie temporal
```

Ver [Formatos de salida](FORMATOS_SALIDA.md) para detalles completos.

## Troubleshooting

### Error: "No module named 'qcal'"

Asegúrate de haber instalado las dependencias:

```bash
pip install -r requirements.txt
```

### Error de descarga de datos GWOSC

Verifica tu conexión a internet y que el evento existe en GWOSC:

```bash
# Listar eventos disponibles
python -c "import gwosc; print(gwosc.datasets.find_datasets())"
```

### Rendimiento lento

Para análisis largos, considera usar:

```bash
# Ejecutar en background
nohup qcal analyze --event GW150914 --detector H1 > analysis.log 2>&1 &
```

## Ver también

- [Reproducibilidad](reproducibilidad.md): Gestión de entornos
- [Validación](validation.md): Tests y CI/CD
- [Tutorial completo](TUTORIAL_COMPLETO.md): Guía paso a paso
