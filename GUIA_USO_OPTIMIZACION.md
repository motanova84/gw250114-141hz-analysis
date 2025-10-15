# 📋 Guía de Uso Rápido - Sistema de Optimización Máxima

## Instalación y Setup

```bash
# 1. Clonar el repositorio
git clone https://github.com/motanova84/gw250114-141hz-analysis
cd gw250114-141hz-analysis

# 2. Instalar dependencias
make setup
# o
pip install -r requirements.txt
```

## Uso del Sistema de Optimización

### Opción 1: Usar Makefile (Recomendado)

```bash
# Iniciar el sistema completo
make optimize

# Ver estado del sistema
make status-optimize

# Detener el sistema
make stop-optimize
```

### Opción 2: Usar scripts directamente

```bash
# Iniciar el sistema
./scripts/optimizacion_maxima.sh

# Ver estado (manual)
curl http://localhost:5000/api/estado-completo | python3 -m json.tool

# Detener el sistema
./scripts/detener_servicios.sh
```

### Opción 3: Con privilegios root (para optimizaciones de sistema)

```bash
# Iniciar con sudo para aplicar optimizaciones de kernel
make optimize-sudo
# o
sudo ./scripts/optimizacion_maxima.sh
```

## Acceso al Dashboard

Una vez iniciado el sistema:

1. Abrir navegador en: http://localhost:5000
2. Ver métricas en tiempo real
3. Monitorear estado de los módulos

## APIs Disponibles

```bash
# Estado completo del sistema
curl http://localhost:5000/api/estado-completo

# Solo métricas
curl http://localhost:5000/api/metricas

# Health check
curl http://localhost:5000/health

# Stream en tiempo real (SSE)
curl http://localhost:5000/api/stream
```

## Ejemplos de Respuestas

### Estado Completo
```json
{
  "estado": "operativo",
  "inicio": "2025-10-15T12:00:00",
  "ultima_actualizacion": "2025-10-15T12:30:00",
  "metricas": {
    "snr_promedio": 12.5,
    "eventos_detectados": 0,
    "validaciones_exitosas": 0,
    "tiempo_ejecucion": 0
  },
  "modulos": {
    "monitor": "activo",
    "optimizacion_snr": "activo",
    "validacion_estadistica": "activo",
    "busqueda_gwtc1": "activo"
  }
}
```

## Monitoreo de Logs

```bash
# Ver log del monitor avanzado
tail -f /tmp/monitor_avanzado.log

# Ver log del monitor de recursos
tail -f /tmp/monitor_recursos.log

# Ver log del dashboard
tail -f /tmp/dashboard.log

# Ver logs de Gunicorn (si se usa)
tail -f /tmp/dashboard_access.log
tail -f /tmp/dashboard_error.log
```

## Verificar Procesos Activos

```bash
# Ver todos los procesos del sistema
ps aux | grep -E "monitor_avanzado|monitor_recursos|dashboard"

# Ver PIDs guardados
cat /tmp/monitor_avanzado.pid
cat /tmp/monitor_recursos.pid
cat /tmp/dashboard.pid

# Verificar estado con Makefile
make status-optimize
```

## Solución de Problemas Comunes

### El dashboard no inicia

```bash
# Instalar dependencias faltantes
pip install flask gunicorn

# Verificar que el puerto 5000 está libre
lsof -i :5000

# Si está ocupado, matar el proceso
kill $(lsof -t -i:5000)
```

### Los monitores no responden

```bash
# Detener todos los servicios
make stop-optimize

# Reiniciar el sistema
make optimize
```

### Permisos insuficientes

```bash
# Ejecutar con sudo para optimizaciones de sistema
sudo make optimize-sudo

# O ejecutar sin sudo (funcionará sin optimizaciones de kernel)
make optimize
```

## Integración con Validación

El sistema de optimización se puede combinar con el sistema de validación:

```bash
# 1. Iniciar sistema de optimización
make optimize

# 2. En otra terminal, ejecutar validación
make validate

# 3. Ver resultados en el dashboard
# http://localhost:5000

# 4. Detener todo
make stop-optimize
```

## Desinstalación

```bash
# Detener servicios
make stop-optimize

# Limpiar archivos temporales
rm -f /tmp/monitor_*.{log,pid}
rm -f /tmp/dashboard*.{log,pid}

# Limpiar proyecto (opcional)
make clean
```

## Características Avanzadas

### Configurar Intervalo de Monitoreo

Editar `scripts/monitor_avanzado_gw250114.py`:
```python
self.intervalo = 60  # Cambiar a 30, 120, etc.
```

Editar `scripts/monitor_recursos.sh`:
```bash
INTERVALO=5  # Cambiar a 10, 30, etc.
```

### Personalizar Dashboard

El dashboard está en `dashboard/dashboard_avanzado.py` y puede ser personalizado modificando:
- Métricas mostradas
- Intervalos de actualización
- Estilo visual (CSS en el template HTML)

### Modo Desarrollo

Para desarrollo del dashboard con auto-reload:
```bash
cd dashboard
export FLASK_DEBUG=1
python3 dashboard_avanzado.py
```

## Testing

```bash
# Ejecutar tests del sistema
python3 scripts/test_optimizacion_sistema.py

# Debería mostrar:
# Tests pasados: 6/6
# ✅ TODOS LOS TESTS PASADOS
```

## Recursos Adicionales

- 📖 Documentación completa: [OPTIMIZACION_MAXIMA.md](OPTIMIZACION_MAXIMA.md)
- 🔬 Sistema de validación: [ADVANCED_VALIDATION_SYSTEM.md](ADVANCED_VALIDATION_SYSTEM.md)
- 📚 README principal: [README.md](README.md)

## Soporte

Para problemas o preguntas:
1. Revisar logs en `/tmp/`
2. Ejecutar tests: `python3 scripts/test_optimizacion_sistema.py`
3. Verificar que todas las dependencias están instaladas: `pip install -r requirements.txt`
4. Abrir un issue en GitHub

---

**Última actualización**: 2025-10-15
