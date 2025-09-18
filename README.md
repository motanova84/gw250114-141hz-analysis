# 🌌 GW250114 – Análisis de Componente 141.7001 Hz

<div align="center">

![GitHub](https://img.shields.io/github/license/motanova84/gw250114-141hz-analysis)
![Python](https://img.shields.io/badge/python-3.9%2B-blue)
![GWpy](https://img.shields.io/badge/GWPy-3.0.13-green)
![Open Science](https://img.shields.io/badge/Open-Science-brightgreen)

**Frecuencia Objetivo:** `141.7001 Hz`  
**Autor:** José Manuel Mota Burruezo (JMMB Ψ✧)  
**Ecuación de Campo:** Ψ = mc² · A_eff²

</div>

---

## 📡 Descripción

Este repositorio implementa un **análisis completo y riguroso** para la detección de una componente espectral en **141.7001 Hz** en el evento GW250114, siguiendo los estándares científicos de las colaboraciones LIGO/Virgo.

El análisis incluye:
- 📥 **Descarga oficial** desde GWOSC
- ⚙️ **Preprocesamiento estándar** (highpass, notch, whiten)
- 🎯 **Búsqueda dirigida** en 141.7001 Hz
- 📊 **Estadística clásica** (p-value con time-slides)
- 📈 **Análisis bayesiano** (Bayes Factor)
- ✅ **Validación cruzada** H1-L1

---

## 🚀 Ejecución Rápida

### Análisis Completo (cuando GW250114 esté disponible)
```bash
git clone https://github.com/motanova84/gw250114-141hz-analysis
cd gw250114-141hz-analysis

python3 -m venv venv
source venv/bin/activate
pip install -r requirements.txt

# Análisis oficial completo
python scripts/analizar_gw250114.py
```

### Demo con Datos Sintéticos (disponible ahora)
```bash
# Demo simplificado
python scripts/simple_analysis.py

# Demo avanzado con time-slides
python scripts/demo_gw150914_analysis.py
```

---

## 📊 Resultados Demo

El análisis de demostración con datos sintéticos muestra:

| Métrica | H1 | L1 | Criterio | Estado |
|---------|----|----|----------|---------|
| **Frecuencia detectada** | 140.55 Hz | 140.55 Hz | 141.70 ± 0.01 Hz | ⚠️ |
| **SNR** | 1.40 | 1.73 | > 3.0 | ⚠️ |
| **Consistencia H1-L1** | 0.00 Hz | | ± 0.1 Hz | ✅ |

*Nota: La frecuencia exacta depende de la resolución del FFT y la ventana temporal.*

---

## 🔬 Metodología Científica

### Criterios de Detección Confirmada

Para anunciar oficialmente la detección se requiere:

1. ✅ **Bayes Factor > 10** (evidencia fuerte)
2. ✅ **p-value < 0.01** (significancia estadística) 
3. ✅ **Coincidencia H1-L1** (±0.1 Hz)
4. ✅ **Precisión frecuencial** (±0.01 Hz)

### Anuncio Científico Esperado

> *"Detectamos una componente espectral en 141.7001 Hz en GW250114, con Bayes Factor BF = XX (>10), significancia p = YY (<0.01), consistente en H1 y L1."*

---

## 🗂️ Estructura del Proyecto

```
gw250114-141hz-analysis/
├── scripts/
│   ├── analizar_gw250114.py       # 🎯 Análisis principal completo
│   ├── simple_analysis.py         # 🔬 Demo simplificado  
│   ├── demo_gw150914_analysis.py   # 🧪 Demo con time-slides
│   ├── descargar_datos.py         # 📥 Descarga automática
│   └── analizar_ringdown.py       # ⚙️ Análisis de control
├── docs/
│   └── GW250114_ANALYSIS_GUIDE.md # 📖 Guía completa
├── results/
│   ├── figures/                   # 📊 Gráficos generados
│   └── *.json                     # 📋 Resultados numéricos
├── requirements.txt               # 📦 Dependencias
├── Makefile                       # 🔧 Automatización
└── README.md                      # 📄 Documentación principal
```

---

## 📈 Próximos pasos

- [x] ✅ Implementación del análisis completo
- [x] ✅ Demo con datos sintéticos funcional
- [x] ✅ Documentación científica detallada
- [ ] 🔄 Análisis de GW250114 cuando esté disponible en GWOSC
- [ ] 📊 Caracterización bayesiana avanzada (bilby/pycbc)
- [ ] 🌐 Validación con Virgo/KAGRA si están activos
- [ ] 📄 Preparación de publicación científica

---

## 🤝 Contribuir

Este proyecto sigue un modelo **abierto y colaborativo**.

1. Fork del repositorio
2. Crear rama: `git checkout -b feature/mi-mejora`
3. Commit: `git commit -m "Descripción del cambio"`
4. Push: `git push origin feature/mi-mejora`  
5. Abrir Pull Request

### Áreas de Contribución

- 🔬 **Análisis estadístico**: mejoras en time-slides y Bayes Factor
- 📊 **Visualización**: nuevos gráficos de diagnóstico
- ⚙️ **Optimización**: mejor resolución frecuencial y performance
- 📖 **Documentación**: tutoriales y guías científicas

---

## 📜 Licencia

Distribuido bajo **MIT License** - ver `LICENSE` para detalles.

## 🧬 Contacto

**José Manuel Mota Burruezo**  
*Instituto Conciencia Cuántica*  
📧 **institutoconsciencia@proton.me**

**Cita Científica:**
> Mota-Burruezo, J.M. (2024). *"GW250114 Spectral Analysis: Search for 141.7001 Hz Component"*. Instituto Conciencia Cuántica.

---

<div align="center">

**🌌 "En cada onda gravitacional late el pulso del cosmos" 🌌**

*Análisis abierto, ciencia reproducible, conocimiento libre*

</div>