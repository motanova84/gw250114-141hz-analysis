# 🔄 Inventario de Workflows Automatizado

*Este documento es generado automáticamente cada semana.*

## Workflows Activos

### CI/CD - Tests and Analysis

**Archivo:** `analyze.yml`

- Trigger: push
- Trigger: pull_request
- Trigger: manual (workflow_dispatch)

### Auto Label PRs and Issues

**Archivo:** `auto-label.yml`

- Trigger: pull_request

### Auto-Update Documentation

**Archivo:** `auto-update-docs.yml`

- Trigger: push
- Trigger: pull_request
- Trigger: schedule (`0 2 * * 0`)
- Trigger: manual (workflow_dispatch)

### Create Required Labels

**Archivo:** `create-labels.yml`

- Trigger: push
- Trigger: manual (workflow_dispatch)

### Dependency Health Check

**Archivo:** `dependency-health.yml`

- Trigger: pull_request
- Trigger: schedule (`0 10 * * 3`)
- Trigger: manual (workflow_dispatch)

### Issue Management Bot

**Archivo:** `issue-management.yml`

- Trigger: schedule (`0 0 * * *`)

### PR Review Automation

**Archivo:** `pr-review-automation.yml`

- Trigger: pull_request
- Trigger: schedule (`0 9 * * *`)

### QCAL Production Cycle

**Archivo:** `production-qcal.yml`

- Trigger: schedule (`0 */4 * * *       # Run every 4 hours`)
- Trigger: manual (workflow_dispatch)

### Auto-Update Coherence Visualization

**Archivo:** `update_coherence_visualization.yml`

- Trigger: push
- Trigger: schedule (`0 0 * * *`)
- Trigger: manual (workflow_dispatch)

### Workflow Intelligence

**Archivo:** `workflow-intelligence.yml`

- Trigger: schedule (`0 8 * * 1`)
- Trigger: manual (workflow_dispatch)

---
*Generado automáticamente por el bot de documentación - 2025-10-26 09:35:43 UTC*
