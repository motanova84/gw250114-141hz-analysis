# One-pager de Valoración

## Propuesta de Valor

QCAL (Coherence Analytics) proporciona una CLI reproducible y pipelines automáticos para analizar coherencia en ondas gravitacionales en la banda de 141.7 Hz.

## Métricas Clave

- **Precisión**: Análisis de coherencia con umbral 5σ
- **Reproducibilidad**: 100% mediante hashes inmutables (`pip-compile`)
- **Cobertura**: Análisis de eventos GWTC-1 con detección tri-detector (H1, L1, V1)

## Validación Científica

- 11/11 eventos GWTC-1 detectados en H1 con SNR medio: 21.38 ± 6.38
- 11/11 eventos GWTC-1 detectados en L1 con SNR medio: 15.00 ± 8.12
- Significancia combinada: >10σ (p < 10⁻²⁵)

## Roadmap

- **Q4 2024**: CLI básica + documentación
- **Q1 2025**: Publicación PyPI + datasets guiados
- **Q2 2025**: Pilotos QC-LLM con informes automáticos
