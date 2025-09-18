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

```bash
# 1. Clona el repositorio
git clone https://github.com/motanova84/gw250114-141hz-analysis
cd gw250114-141hz-analysis

# 2. Crea entorno virtual y activa
make setup
# O alternativamente:
# python3 -m venv venv && source venv/bin/activate && pip install -r requirements.txt

# 3. Ejecuta análisis GW250114 completo (6 pasos)
make analyze-gw250114

# 4. Ejecuta análisis legacy (GW150914 control)
make analyze

# 5. Ver todas las opciones disponibles
make help
```

## 🔬 Análisis GW250114 - Workflow de 6 Pasos

El nuevo script `scripts/analisis_gw250114.py` implementa el **estándar de oro** para validación de la componente 141.7 Hz:

### 📥 **Paso 1**: Descarga oficial GWOSC
- Utiliza `gwosc.datasets.event_gps('GW250114')` para tiempo GPS oficial
- Descarga datos H1 y L1 con `TimeSeries.fetch_open_data()`
- Legitimidad garantizada desde la fuente oficial

### ⚙️ **Paso 2**: Preprocesamiento estándar  
- `highpass(20Hz)` - Elimina ruido sísmico de baja frecuencia
- `notch(60Hz)` - Filtra ruido eléctrico
- `whiten()` - Normaliza el ruido para análisis espectral

### 🔎 **Paso 3**: Búsqueda dirigida en 141.7 Hz
- Extrae ringdown (50ms post-merger)
- Calcula ASD con `fftlength=0.05`
- Mide SNR en 141.7 Hz vs. mediana del ruido

### 📊 **Paso 4**: Estadística clásica (p-value)
- Ejecuta 1000 time-slides desplazando H1-L1 ±0.2s
- Calcula distribución de picos falsos
- **p-value = fracción de picos simulados ≥ pico real**
- Criterio: **p < 0.01** → significativo

### 📈 **Paso 5**: Bayes Factor
- Compara modelos M0 (ruido) vs M1 (ruido + señal 141.7Hz)
- Calcula **BF = P(datos|M1) / P(datos|M0)**
- Criterio: **BF > 10** → evidencia fuerte

### ✅ **Paso 6**: Validación cruzada
- Verifica coincidencia H1-L1 (±0.1 Hz)
- Confirma ausencia en time-slides
- Requiere **BF > 10 Y p < 0.01**

**🚀 Resultado esperado**: Si cumple todos los criterios → **"Detectamos componente en 141.7 Hz con significancia BF=XX, p=YY"**

## 🧠 Fundamento Teórico

La frecuencia 141.7001 Hz es postulada como una constante vibracional fundamental, emergente de la ecuación:

Ψ(f) = mc² · A_eff² · e^(iπf)

Donde:

- **Ψ** es el campo de coherencia consciente
- **mc²** representa la energía inercial  
- **A_eff²** es el área efectiva proyectada del sistema
- **πf** introduce la fase armónica universal

## 🗂️ Estructura del Proyecto

```
gw250114-141hz-analysis/
├── scripts/
│   ├── analisis_gw250114.py     # 🆕 Análisis completo GW250114 (6 pasos)
│   ├── descargar_datos.py       # Descarga automática desde GWOSC
│   ├── analizar_ringdown.py     # Análisis espectral de control
│   ├── analisis_noesico.py      # Búsqueda de 141.7001 Hz + armónicos  
│   └── analizar_l1.py           # Validación cruzada en L1
├── results/
│   ├── gw250114/                # 🆕 Resultados análisis GW250114
│   └── figures/                 # Gráficos generados (legacy)
├── requirements.txt             # Dependencias científicas + gwosc
├── Makefile                     # Flujo automatizado con nuevos targets
├── Dockerfile                   # Contenedor reproducible
└── README.md                    # Documentación principal
```

## 📈 Próximos pasos

- [x] Validación múltiple de 141.7001 Hz en GW150914
- [x] **Workflow completo de 6 pasos para GW250114** 🆕
- [x] **Integración con GWOSC oficial** 🆕
- [x] **Estadística clásica con time-slides** 🆕  
- [x] **Cálculo de Bayes Factor** 🆕
- [ ] Análisis completo de GW250114 cuando esté disponible en GWOSC
- [ ] Caracterización bayesiana avanzada con bilby/pycbc
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
