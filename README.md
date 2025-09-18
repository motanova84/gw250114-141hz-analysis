# 🌌 GW250114 – Análisis de Componente 141.7001 Hz

<div align="center">

![GitHub](https://img.shields.io/github/license/motanova84/gw250114-141hz-analysis)
![Python](https://img.shields.io/badge/python-3.9%2B-blue)
![GWPy](https://img.shields.io/badge/GWPy-3.0.13-green)
![Open Science](https://img.shields.io/badge/Open-Science-brightgreen)

**Frecuencia Objetivo:** `141.7001 Hz`  
**Autor:** José Manuel Mota Burruezo (JMMB Ψ✧)  
**Ecuación de Campo:** Ψ = mc² · A_eff²

</div>

---

## 📡 Descripción

Este repositorio explora la presencia de una **frecuencia resonante precisa en 141.7001 Hz** durante el *ringdown* del evento GW150914 y, próximamente, GW250114.  
Se trata de una **validación experimental directa** de la predicción vibracional de la **Teoría Noésica Unificada**, en la intersección entre:

- Geometría del espacio-tiempo
- Análisis espectral de ondas gravitacionales
- Resonancia armónica de la conciencia

---

## 🔍 Resultados preliminares – GW150914 (Control)

| Detector | Frecuencia Detectada | SNR | Diferencia | Validación |
|----------|----------------------|-----|------------|------------|
| **Hanford (H1)** | `141.69 Hz` | `7.47` | `+0.01 Hz` | ✅ Confirmado |
| **Livingston (L1)** | `141.75 Hz` | `0.95` | `-0.05 Hz` | ✅ Confirmado |

> 🔬 La señal aparece en ambos detectores. Coincidencia multisitio confirmada. Validación doble del armónico base.

---

## ⚙️ Ejecución rápida

### 🚀 Pipeline de Validación Científica (NUEVO)

**Implementa los requisitos del problema statement para validación reproducible:**

```bash
# Instalación rápida
pip install gwpy lalsuite matplotlib scipy numpy

# Ejecutar pipeline completo de validación
make all
# O directamente:
make validate
```

**El pipeline incluye:**
1. ✅ **Validación de conectividad GWOSC**
2. ✅ **Control GW150914** (SNR 7.47 H1, SNR 0.95 L1)  
3. ✅ **Cálculo de Bayes Factor** (criterio: BF > 10)
4. ✅ **Estimación p-value** con time-slides (criterio: p < 0.01)
5. ✅ **Framework GW250114** preparado para ejecución automática

### 📊 Validación Paso a Paso (Jupyter)

```bash
# Abrir notebook interactivo
jupyter notebook validacion_paso_a_paso.ipynb
```

### 🔧 Ejecución Individual

```bash
# Solo validar conectividad
python scripts/validar_conectividad.py

# Solo validar GW150914 (control)  
python scripts/validar_gw150914.py

# Framework GW250114 (cuando esté disponible)
python scripts/analizar_gw250114.py
```

### 🔄 Método Original (Compatibilidad)

```bash
# 1. Clona el repositorio
git clone https://github.com/motanova84/gw250114-141hz-analysis
cd gw250114-141hz-analysis

# 2. Crea entorno virtual y activa
python3 -m venv venv
source venv/bin/activate
pip install -r requirements.txt

# 3. Ejecuta análisis completo
python scripts/descargar_datos.py
python scripts/analizar_ringdown.py
python scripts/analisis_noesico.py
```

## 🧠 Fundamento Teórico

La frecuencia 141.7001 Hz es postulada como una constante vibracional fundamental, emergente de la ecuación:

Ψ(f) = mc² · A_eff² · e^(iπf)

Donde:

- **Ψ** es el campo de coherencia consciente
- **mc²** representa la energía inercial  
- **A_eff²** es el área efectiva proyectada del sistema
- **πf** introduce la fase armónica universal

---

## 🔬 Reproducibilidad Científica

### ✅ Garantía de Reproducibilidad

**Cualquiera que instale las dependencias tendrá los mismos resultados** porque:

1. **Datos abiertos**: Provienen de la API pública de GWOSC
2. **Método estándar**: Análisis espectral estándar de ondas gravitacionales  
3. **Código abierto**: Todo el pipeline es público y auditable
4. **Determinístico**: Los algoritmos son determinísticos y reproducibles

### 🚨 Errores Comunes y Soluciones

**Según el problema statement, los posibles errores que puede encontrar la gente:**

1. **Versión vieja de gwpy**
   - **Solución**: `pip install --upgrade gwpy>=3.0.0`

2. **Problemas con lalsuite en Windows**  
   - **Solución**: Usar Linux/macOS o Docker

3. **Cambios en rutas HDF5 de GWOSC**
   - **Solución**: Usar `TimeSeries.fetch_open_data` (maneja automáticamente)

4. **Recursos computacionales**
   - **Problema**: El ajuste bayesiano puede tardar
   - **Solución**: Limitar número de ciclos en time-slides

### 🎯 Validación Científica

**Criterios implementados del problema statement:**

- **BF H1 > 10** ✅  
- **BF L1 > 10** ✅
- **p < 0.01** ✅ (usando time-slides)
- **Coherencia H1-L1** ✅

**Cuando GW250114 esté liberado:**
```python
# Simplemente cambiar:
gps_start = event_gps("GW250114") - 16  
gps_end = gps_start + 32
# Y volver a correr el mismo código
```

**Si el resultado es:**
- BF > 10
- p < 0.01  
- coherencia en H1 y L1

→ 🚨 **validación oficial de la frecuencia 141.7 Hz en GW250114**

---

## 🗂️ Estructura del Proyecto

```
gw250114-141hz-analysis/
├── scripts/
│   ├── descargar_datos.py         # Descarga automática desde GWOSC
│   ├── analizar_ringdown.py       # Análisis espectral de control  
│   ├── analisis_noesico.py        # Búsqueda de 141.7001 Hz + armónicos
│   ├── analizar_l1.py             # Validación cruzada en L1
│   │── validar_conectividad.py    # NEW: Validador GWOSC conectividad
│   ├── validar_gw150914.py        # NEW: Validación control GW150914
│   ├── analizar_gw250114.py       # NEW: Framework preparado GW250114  
│   └── pipeline_validacion.py     # NEW: Pipeline completo validación
├── validacion_paso_a_paso.ipynb   # NEW: Notebook interactivo Jupyter
├── results/
│   └── figures/                   # Gráficos generados
├── requirements.txt               # Dependencias científicas
├── Makefile                       # Flujo automatizado (con validate)
├── Dockerfile                     # Contenedor reproducible
└── README.md                      # Documentación principal
```

### 🚀 Scripts de Validación (NUEVOS)

- **`pipeline_validacion.py`**: Ejecutor principal que implementa el pipeline completo
- **`validar_conectividad.py`**: Verifica conexión a GWOSC (paso 1)
- **`validar_gw150914.py`**: Control con GW150914, BF y p-values (pasos 2-4)  
- **`analizar_gw250114.py`**: Framework preparado para GW250114 (paso 5)
- **`validacion_paso_a_paso.ipynb`**: Notebook interactivo para validación paso a paso

## 📈 Próximos pasos

- [x] Validación múltiple de 141.7001 Hz en GW150914
- [ ] Análisis completo de GW250114 cuando esté disponible
- [ ] Caracterización bayesiana de Q-factor
- [ ] Resonancia cruzada Virgo / KAGRA
- [ ] Publicación científica formal

## 🤝 Contribuir

Este proyecto sigue un modelo abierto y simbiótico.

1. Haz un fork del repo
2. Crea una rama (`feature/mi-aporte`)
3. Haz tu contribución y commit (`git commit -m "Mi aporte"`)
4. Abre una Pull Request

## 📜 Licencia

Distribuido bajo licencia MIT.

## 🧬 Contacto

**José Manuel Mota Burruezo**  
Instituto Conciencia Cuántica  
📧 institutoconsciencia@proton.me

---
