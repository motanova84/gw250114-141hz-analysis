# Roadmap

Hoja de ruta del proyecto QCAL — Análisis de Coherencia a 141.7 Hz

## v0.2.0 — Q1 2026 (Planificado)

### Análisis Multi-Evento
- [ ] Integración completa de eventos GWTC-2 y GWTC-3
- [ ] Pipeline automatizado para nuevos eventos
- [ ] Dashboard interactivo de resultados

### Mejoras en Validación
- [ ] 10,000 ventanas off-source por evento (automatizado)
- [ ] Time-slides multi-detector (100+ combinaciones)
- [ ] Análisis Bayesiano jerárquico refinado

### Infraestructura
- [ ] API REST para acceso programático
- [ ] Base de datos de resultados (PostgreSQL)
- [ ] Cache de datos GWOSC (reducir descargas)

## v0.3.0 — Q2 2026 (Planificado)

### Detectores adicionales
- [ ] Integración de Virgo (todos los eventos O2+)
- [ ] Integración de KAGRA (eventos O4)
- [ ] Análisis de coherencia 3-4 detectores

### Machine Learning
- [ ] Clasificador de señales vs ruido (CNN)
- [ ] Detección automática de líneas instrumentales
- [ ] Predicción de SNR con redes neuronales

### Visualización
- [ ] Dashboard web interactivo (Dash/Streamlit)
- [ ] Plots 3D de coherencia multi-detector
- [ ] Animaciones de evolución temporal

## v1.0.0 — Q3 2026 (Objetivo)

### Release estable
- [ ] API estable (SemVer)
- [ ] Documentación completa (Sphinx + MkDocs)
- [ ] Tutorial interactivo (Jupyter Book)

### Publicación científica
- [ ] Paper en revista peer-reviewed
- [ ] Preprint en arXiv
- [ ] Datasets en Zenodo con DOI

### Comunidad
- [ ] Guías de contribución detalladas
- [ ] Issues templates
- [ ] Discusiones en GitHub

## Backlog (Ideas futuras)

### Análisis avanzados
- Análisis de armónicos (2×141.7 Hz, 3×141.7 Hz)
- Búsqueda de modulaciones temporales
- Correlación con catálogos astronómicos

### Integraciones
- PyCBC (análisis de ondas gravitacionales)
- LALSuite (LIGO Algorithm Library)
- Bilby (inferencia Bayesiana)

### Formalismos matemáticos
- Lean 4: Formalización completa de teoremas
- Coq: Verificación de algoritmos críticos
- Isabelle/HOL: Pruebas de propiedades estadísticas

### HPC y escalabilidad
- Paralelización con Dask/Ray
- Soporte GPU (CuPy)
- Cluster computing (Slurm)

## Versiones anteriores

### v0.1.1 — 2025-11-11 ✅
- Sitio MkDocs optimizado
- Despliegue automático a gh-pages
- Minificado HTML y sitemap

### v0.1.0 — 2025-11-11 ✅
- CLI inicial `qcal analyze`
- Tests + CI + SBOM + OSV scan
- Documentación con MkDocs Material

## Contribuir al roadmap

¿Tienes ideas para el proyecto? Abre un issue:

- [Feature requests](https://github.com/motanova84/141hz/issues/new?labels=enhancement)
- [Bug reports](https://github.com/motanova84/141hz/issues/new?labels=bug)
- [Discusiones](https://github.com/motanova84/141hz/discussions)

## Prioridades

Las siguientes características tienen alta prioridad:

1. 🔥 **Multi-evento GWTC-2/3**: Ampliar cobertura
2. 🔥 **Validación robusta**: Off-source automatizado
3. 🔥 **API REST**: Acceso programático
4. ⭐ **Dashboard web**: Visualización interactiva
5. ⭐ **Paper científico**: Publicación peer-reviewed

## Financiación

Buscamos financiación para:

- Tiempo de cómputo en clusters HPC
- Revisión y auditoría de código
- Conferencias y presentaciones
- Publicaciones en open access

Ver [dataroom/valuation_onepager.md](dataroom/valuation_onepager.md) para más información.

---

**Última actualización**: 2025-11-12  
**Mantenedor**: José Manuel Mota Burruezo (JMMB Ψ✧)
