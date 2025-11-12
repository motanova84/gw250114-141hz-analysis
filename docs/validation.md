# Validación

QCAL implementa un framework de validación riguroso que garantiza la calidad y corrección de los análisis.

## Metodología de validación

### Niveles de validación

1. **Tests unitarios**: Funciones individuales
2. **Tests de integración**: Pipelines completos
3. **Validación científica**: Controles off-source, time-slides
4. **Validación estadística**: Significancia, p-valores
5. **Revisión por pares**: Pre-registro y replicación

## Tests unitarios

### Estructura de tests

```
tests/
├── test_qcal_module.py       # Tests del módulo principal
├── test_multi_event_analysis.py
├── test_pozo_infinito_cuantico.py
└── ...
```

### Ejecutar tests

```bash
# Todos los tests
pytest

# Tests específicos
pytest tests/test_qcal_module.py

# Con cobertura
pytest --cov=qcal tests/
```

## Validaciones científicas

### 1. Validación de radio cuántico

Verifica la consistencia de las predicciones teóricas:

```bash
python run_all_validations.py --validation radio_cuantico
```

**Criterios de éxito**:
- Desviación < 1% del valor teórico
- p-valor > 0.05 (no rechazo)

### 2. Validación de energía cuántica

Valida cálculos de energía en el pozo cuántico:

```bash
python run_all_validations.py --validation energia_cuantica
```

### 3. Validación de simetría discreta

Verifica simetría gauge en el campo Ψ:

```bash
python run_all_validations.py --validation simetria_discreta
```

## Controles experimentales

### Off-source analysis

Análisis de ventanas temporales sin señal esperada:

```python
# 10,000 ventanas off-source por evento
from controls import offsource_analysis

null_distribution = offsource_analysis(
    event='GW150914',
    detector='H1',
    n_windows=10000
)
```

**Objetivo**: Caracterizar distribución nula bajo H₀.

### Time-slides

Desplazamiento temporal entre detectores:

```python
from controls import time_slides

significance = time_slides(
    events=['GW150914', 'GW151226'],
    detectors=['H1', 'L1'],
    n_slides=100
)
```

**Objetivo**: Estimar tasa de coincidencias accidentales.

### Leave-one-out cross-validation

```python
from bayes import leave_one_out

loo_results = leave_one_out(event_list)
```

**Objetivo**: Verificar robustez del análisis Bayesiano.

## Análisis Bayesiano multi-evento

### Modelo jerárquico

```python
from bayes.hierarchical_model import bayes_factor

# Lista de SNRs de múltiples eventos
snr_list = [12.5, 8.3, 15.1, 6.7, ...]

# Calcular Bayes Factor
bf, diagnostics = bayes_factor(snr_list)
print(f"Bayes Factor: {bf:.2f}")
print(f"log₁₀(BF): {np.log10(bf):.2f}")
```

**Interpretación** (escala de Kass-Raftery):
- log₁₀(BF) < 0.5: No evidencia
- 0.5 < log₁₀(BF) < 1: Evidencia débil
- 1 < log₁₀(BF) < 2: Evidencia fuerte
- log₁₀(BF) > 2: Evidencia decisiva

### Parámetros globales

- **π**: Fracción de eventos con señal (prior: Beta(1,1))
- **μ, σ**: Media y desviación de SNR (priors normales)

Ver [hierarchical_model.py](../bayes/hierarchical_model.py) para detalles.

## CI/CD

### Workflows automáticos

#### `.github/workflows/ci.yml`
Tests básicos en cada commit:
```yaml
- Lint (flake8)
- Tests unitarios (pytest)
- Cobertura de código
```

#### `.github/workflows/analyze.yml`
Análisis completo cada 4 horas:
```yaml
- Descarga de datos GWOSC
- Análisis espectral
- Generación de artefactos
```

#### `.github/workflows/scientific-validation.yml`
Validaciones científicas programadas:
```yaml
- Radio cuántico
- Energía cuántica
- Simetría discreta
```

### Badges de estado

![CI](https://github.com/motanova84/141hz/workflows/CI/badge.svg)
![Tests](https://github.com/motanova84/141hz/workflows/Tests/badge.svg)

Ver [.github/workflows/](../.github/workflows/) para todos los workflows.

## Pre-registro

### Blind pre-registration

El proyecto sigue un protocolo de pre-registro ciego:

1. **Análisis pre-registrado** en [PREREGISTRATION.md](../PREREGISTRATION.md)
2. **Parámetros fijos** en [analysis_plan.json](../analysis_plan.json)
3. **Criterios de éxito** definidos a priori
4. **Falsificación posible**: Condiciones de rechazo claras

### Criterios de éxito

**Hipótesis nula (H₀)**: No hay señal coherente a 141.7 Hz

**Criterio de rechazo de H₀**:
- SNR > 5σ en ≥3 eventos
- Consistencia multi-detector (H1/L1)
- Bayes Factor > 100
- Controles off-source: p < 0.01

## Exclusión de líneas instrumentales

Frecuencias conocidas se excluyen del análisis:

```csv
# controls/lines_exclusion.csv
frequency,source,detector
60.0,power_grid,H1
120.0,power_grid_2nd_harmonic,H1
500.0,calibration_line,H1
```

Ver [lines_exclusion.csv](../controls/lines_exclusion.csv) completo.

## Antenna pattern consistency

Verifica consistencia con el patrón de antena de LIGO:

```python
from notebooks import antenna_pattern

# Calcula F+ y Fx para una dirección del cielo
f_plus, f_cross = antenna_pattern(ra, dec, psi, detector='H1')

# Compara con amplitudes observadas
ratio_predicted = f_plus / f_cross
ratio_observed = A_plus / A_cross

assert np.isclose(ratio_predicted, ratio_observed, rtol=0.1)
```

Ver [antenna_pattern.ipynb](../notebooks/antenna_pattern.ipynb).

## Estadística de validación

### p-valores y significancia

```python
from scipy import stats

# Test de Kolmogorov-Smirnov
ks_stat, p_value = stats.kstest(observed, null_distribution)

# Test χ²
chi2, p_value = stats.chisquare(observed, expected)
```

### Corrección por múltiples pruebas

Aplicamos corrección de Bonferroni:

```python
alpha_corrected = 0.05 / n_tests
```

## Replicabilidad

### Datos públicos

Todos los análisis usan datos públicos de GWOSC:
- [https://www.gw-openscience.org/](https://www.gw-openscience.org/)

### Código abierto

Todo el código es open source (MIT License):
- [https://github.com/motanova84/141hz](https://github.com/motanova84/141hz)

### Documentación completa

Cada script incluye docstrings y ejemplos de uso.

## Reportes de validación

Los resultados de validación se publican como GitHub Issues:
- [Validation Reports](https://github.com/motanova84/141hz/labels/validation)

## Ver también

- [CLI](cli.md): Cómo ejecutar análisis
- [Reproducibilidad](reproducibilidad.md): Gestión de entornos
- [PREREGISTRATION.md](../PREREGISTRATION.md): Protocolo de pre-registro
- [DISCOVERY_STANDARDS.md](../DISCOVERY_STANDARDS.md): Estándares de descubrimiento
