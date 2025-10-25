# 🤖 Colaboradores Automatizados del Proyecto

Este documento describe los **8 bots inteligentes** que actúan como colaboradores automatizados en el proyecto GW250114-141Hz, mejorando flujos de trabajo, calidad del código y gestión del proyecto.

## 📋 Resumen de Colaboradores

| Bot | Función Principal | Frecuencia | Archivo |
|-----|-------------------|------------|---------|
| 🔒 Dependabot | Actualizar dependencias | Semanal (Lunes 09:00) | `.github/dependabot.yml` |
| 🏷️ Auto-Labeler | Etiquetar PRs/Issues | En cada PR/Issue | `.github/workflows/auto-label.yml` |
| 📋 Issue Management | Gestionar issues | Diaria (00:00) | `.github/workflows/issue-management.yml` |
| 🧠 Workflow Intelligence | Analizar workflows | Semanal (Lunes 08:00) | `.github/workflows/workflow-intelligence.yml` |
| 📚 Documentation Updater | Actualizar docs | Semanal (Domingo 02:00) | `.github/workflows/auto-update-docs.yml` |
| 👀 PR Review Automation | Gestionar revisiones | Diaria (09:00) | `.github/workflows/pr-review-automation.yml` |
| 🏥 Dependency Health | Verificar salud deps | Semanal (Miércoles 10:00) | `.github/workflows/dependency-health.yml` |
| 🔄 Coherence Viz | Actualizar gráficos | Diaria (00:00) | `.github/workflows/update_coherence_visualization.yml` |

## 🔒 1. Dependabot

### Función
Mantiene las dependencias del proyecto actualizadas automáticamente, creando PRs cuando hay nuevas versiones disponibles.

### Características
- **Agrupación inteligente**: Agrupa actualizaciones relacionadas
  - `scientific-computing`: numpy, scipy, matplotlib, astropy
  - `gravitational-wave`: gwpy, pycbc
  - `testing`: pytest, flake8
- **Frecuencia**: Semanal (Lunes 09:00 UTC)
- **Límite de PRs**: Máximo 5 PRs simultáneos
- **Rebase automático**: Actualiza PRs cuando la rama base cambia

### Configuración
```yaml
# .github/dependabot.yml
version: 2
updates:
  - package-ecosystem: "pip"
    directory: "/"
    schedule:
      interval: "weekly"
      day: "monday"
```

### Beneficios
- ✅ Mantiene dependencias actualizadas
- ✅ Reduce deuda técnica
- ✅ Mejora seguridad (detecta vulnerabilidades)
- ✅ Reduce trabajo manual de actualización

## 🏷️ 2. Auto-Labeler

### Función
Etiqueta automáticamente PRs e Issues basándose en:
- Archivos modificados
- Contenido del título y descripción
- Palabras clave científicas

### Etiquetas Detectadas

#### Por Tipo
- `bug` - Correcciones de errores
- `enhancement` - Nuevas funcionalidades
- `documentation` - Cambios en documentación
- `testing` - Cambios en tests
- `ci/cd` - Cambios en workflows

#### Por Área Científica
- `frequency-analysis` - Análisis de 141.7001 Hz
- `gravitational-waves` - Ondas gravitacionales LIGO
- `validation` - Scripts de validación
- `statistics` - Análisis bayesiano/estadístico

#### Por Prioridad
- `priority: high` - Asuntos urgentes/críticos
- `automated` - Creado por bots

### Características Especiales
- 🎉 **Bienvenida a nuevos contribuidores**: Primer PR recibe mensaje de bienvenida
- 📊 **Análisis de archivos**: Detecta tipo de cambio por archivos modificados
- 🔍 **Análisis semántico**: Lee título y descripción para detectar contexto

### Ejemplo
```yaml
PR Title: "fix: Corrección en análisis bayesiano GW150914"
Etiquetas aplicadas:
  - bug
  - statistics
  - gravitational-waves
```

## 📋 3. Issue Management Bot

### Función
Gestiona el ciclo de vida de issues automáticamente.

### Características

#### Al Abrir Issue
- ✅ Verifica información completa:
  - Pasos para reproducir
  - Comportamiento esperado vs observado
  - Información del entorno
- 📝 Comenta con recursos útiles y información faltante

#### Durante Vida del Issue
- 🔍 Detecta cuando issue está resuelto (keywords: "resolved", "fixed", etc.)
- 🚪 Cierra automáticamente issues resueltos

#### Issues Obsoletos
- ⏰ Marca como `stale` después de 60 días sin actividad
- 🚫 Cierra automáticamente después de 7 días más
- 🔐 Excepciones: Issues con etiquetas `pinned`, `security`, `priority: high`

### Configuración
```yaml
days-before-stale: 60
days-before-close: 7
exempt-issue-labels: 'pinned,security,priority: high'
```

## 🧠 4. Workflow Intelligence

### Función
Analiza el rendimiento de workflows y sugiere optimizaciones.

### Análisis Realizado

#### Métricas de Rendimiento
- Tasa de éxito por workflow
- Duración promedio de ejecución
- Identificación de workflows lentos (>30 min)
- Fallos consecutivos

#### Sugerencias Automáticas
- 💨 **Optimización de velocidad**
  - Cachear más dependencias
  - Paralelizar jobs independientes
  - Optimizar descarga de datos GWOSC

- 🔧 **Mejoras técnicas**
  - Detecta scripts de validación no usados en workflows
  - Verifica cumplimiento de estándares (según `.github/copilot-instructions.md`)
  - Sugiere uso de matrix strategies

#### Alertas Automáticas
- 🚨 Crea issue automático si workflow falla 3+ veces consecutivas
- 📊 Genera reporte semanal de rendimiento

### Ejemplo de Reporte
```markdown
## 📊 Análisis de Rendimiento de Workflows

### CI/CD - Tests and Analysis
- Ejecuciones: 25
- Tasa de éxito: 92.0%
- Duración promedio: 8.3 minutos

## 💡 Recomendaciones
- Considerar cachear datos GWOSC
- Paralelizar validaciones independientes
```

## 📚 5. Documentation Updater

### Función
Mantiene la documentación actualizada automáticamente.

### Archivos Generados

#### 1. Inventario de Scripts (`scripts_inventory.tmp.md`)
- Lista todos los scripts de análisis
- Lista scripts de validación
- Lista scripts de test
- Extrae docstrings automáticamente

#### 2. Inventario de Workflows (`workflows_inventory.tmp.md`)
- Lista todos los workflows activos
- Extrae triggers (push, PR, schedule, manual)
- Documenta frecuencia de cron jobs

### Frecuencia
- **Semanal**: Domingo 02:00 UTC
- **Manual**: Via `workflow_dispatch`
- **Automático**: Al cambiar scripts o workflows

### Comportamiento
- ✅ Commitea directamente a `main` en ejecuciones automáticas
- 🔀 Crea PR en ejecuciones programadas
- 🏷️ Etiqueta como `automated` y `documentation`

## 👀 6. PR Review Automation

### Función
Gestiona el proceso de revisión de PRs inteligentemente.

### Características

#### Al Abrir PR
- 👥 **Asigna revisores automáticamente** basado en archivos modificados
- 📝 **Agrega checklist de revisión**:
  - [ ] Los tests pasan
  - [ ] Sigue estándares del proyecto
  - [ ] Documentación actualizada
  - [ ] No rompe compatibilidad

#### PRs Sin Revisar
- ⏰ Envía recordatorio después de 2 días sin revisión
- 🚫 Evita spam (máximo 1 recordatorio cada 24h)

#### PR Mergeado
- 🎉 **Mensaje de celebración** aleatorio
- 📊 **Estadísticas del PR**:
  - Número de commits
  - Archivos cambiados
  - Líneas añadidas/eliminadas

### Mensajes de Celebración
```
- "🎉 ¡PR mergeado con éxito! Gracias por tu contribución a la ciencia abierta."
- "✨ ¡Excelente trabajo! Este cambio mejora el proyecto."
- "🌟 ¡Merge completado! Tu contribución es valiosa para la comunidad científica."
```

## 🏥 7. Dependency Health Check

### Función
Monitorea la salud de las dependencias del proyecto.

### Verificaciones

#### 1. Vulnerabilidades de Seguridad
- 🔍 Ejecuta `pip-audit` para detectar vulnerabilidades conocidas
- 🚨 Crea issue automático si encuentra vulnerabilidades
- 📋 Genera reporte detallado en JSON

#### 2. Paquetes Desactualizados
- 📦 Lista paquetes con versiones más recientes disponibles
- 📊 Muestra versión actual → versión más reciente

#### 3. Compatibilidad Python
- ✅ Verifica instalación con Python 3.11
- ✅ Verifica instalación con Python 3.12
- 📋 Documenta resultados en reporte

### Frecuencia
- **Semanal**: Miércoles 10:00 UTC
- **Automático**: Al cambiar `requirements.txt`
- **Manual**: Via `workflow_dispatch`

### Artefactos Generados
- `dependency_health_report.md` - Reporte completo
- `pip_audit_report.json` - Reporte de vulnerabilidades
- `outdated_packages.json` - Lista de paquetes desactualizados

### Alertas
```yaml
Vulnerabilidades → Issue con label "security,priority: high"
Paquetes críticos desactualizados → Comentario en PR
```

## 🔄 8. Coherence Visualization Updater

### Función
Mantiene las visualizaciones científicas actualizadas automáticamente.

### Proceso
1. Ejecuta `scripts/generar_coherencia_escalas.py`
2. Verifica si imagen cambió
3. Si cambió: commitea y pushea
4. Si no cambió: no hace nada (evita commits innecesarios)

### Archivos Actualizados
- `coherence_f0_scales.png`
- `results/figures/coherence_f0_scales.png`

### Frecuencia
- **Diaria**: 00:00 UTC
- **Automático**: Al cambiar script de generación
- **Manual**: Via `workflow_dispatch`

### Características Especiales
- 🎯 Solo commitea si hay cambios reales (verifica diff)
- 🏷️ Usa `[skip ci]` en mensaje de commit para evitar loops
- 📊 Genera summary con detalles de escalas analizadas

## 🎯 Mejores Prácticas

### Para Mantenedores

#### 1. Revisar PRs de Dependabot
```bash
# Verificar PR de dependabot
- Revisar changelog de paquete actualizado
- Verificar que tests pasen
- Merge si todo está OK
```

#### 2. Responder a Issues de Bots
```bash
# Issue de vulnerabilidades
- Priorizar inmediatamente
- Actualizar dependencias afectadas
- Verificar que tests pasen
- Cerrar issue manualmente
```

#### 3. Monitorear Workflow Intelligence
```bash
# Revisar reportes semanales
- Identificar workflows lentos
- Implementar sugerencias de optimización
- Verificar tasa de éxito de workflows
```

### Para Contribuidores

#### 1. Confiar en Auto-Labeler
- No es necesario añadir etiquetas manualmente
- El bot las añadirá automáticamente
- Puedes añadir etiquetas adicionales si es necesario

#### 2. Responder a Issue Management Bot
- Proporcionar información solicitada
- Marcar como resuelto claramente en comentarios
- El bot cerrará automáticamente

#### 3. Estar atento a Recordatorios de PR
- Revisar PRs cuando recibas recordatorio
- Comentar si necesitas más tiempo
- El bot dejará de recordar después de comentario

## 🔧 Personalización

### Modificar Frecuencia de Bots

#### Ejemplo: Cambiar frecuencia de Dependabot
```yaml
# .github/dependabot.yml
schedule:
  interval: "daily"  # Cambiar de "weekly" a "daily"
  time: "09:00"      # Hora UTC
```

#### Ejemplo: Cambiar cron de Workflow Intelligence
```yaml
# .github/workflows/workflow-intelligence.yml
schedule:
  - cron: '0 8 * * 1'  # Lunes 08:00 UTC
  # Cambiar a diario: '0 8 * * *'
```

### Añadir Nuevas Etiquetas

#### En labeler.yml
```yaml
# .github/labeler.yml
new-category:
  - changed-files:
    - any-glob-to-any-file: 'path/to/files/**'
```

#### En auto-label.yml
```javascript
// Añadir detección semántica
if (body.includes('keyword')) {
  labels.push('new-category');
}
```

## 📊 Métricas de Éxito

### KPIs Monitoreados
- ⏱️ Tiempo promedio de merge de PRs
- 📉 Número de issues obsoletos
- 🔒 Vulnerabilidades detectadas y resueltas
- 📦 Paquetes mantenidos actualizados
- ✅ Tasa de éxito de workflows
- 📚 Documentación siempre actualizada

### Objetivos
- Reducir tiempo de merge de PRs en 50%
- Mantener 0 vulnerabilidades conocidas
- >95% de tasa de éxito en workflows
- 100% de scripts documentados en inventarios

## 🚀 Futuras Mejoras

### Planificadas
- [ ] Bot de changelog automático
- [ ] Bot de release notes
- [ ] Bot de benchmarking de rendimiento
- [ ] Integración con notificaciones Slack/Discord
- [ ] Bot de análisis de cobertura de tests

### En Consideración
- [ ] Bot de sugerencias de código con AI
- [ ] Bot de detección de duplicados en issues
- [ ] Bot de asignación automática de issues
- [ ] Bot de generación de documentación API

## 📧 Soporte

Si experimentas problemas con algún bot:

1. **Verifica logs del workflow** en Actions tab
2. **Abre issue** con etiqueta `automated` y `bug`
3. **Contacta mantenedores** si es urgente

## 📚 Referencias

- [GitHub Actions Documentation](https://docs.github.com/en/actions)
- [Dependabot Documentation](https://docs.github.com/en/code-security/dependabot)
- [GitHub Script Action](https://github.com/actions/github-script)
- [Copilot Instructions](.github/copilot-instructions.md)

---

**🌌 Estos colaboradores automatizados ayudan a hacer el proyecto más eficiente, seguro y colaborativo.**

*Documentación generada: $(date -u '+%Y-%m-%d')*
