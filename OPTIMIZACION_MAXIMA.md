# 🚀 Sistema de Optimización Máxima - GW250114

## Descripción

Sistema completo de optimización y monitoreo para el análisis de GW250114 (componente 141.7 Hz). 
Incluye optimización de sistema, monitoreo avanzado, seguimiento de recursos y dashboard web en tiempo real.

## Componentes

### 1. Script de Optimización Principal
**Archivo**: `scripts/optimizacion_maxima.sh`

Script principal que configura e inicia todos los componentes del sistema:
- Optimización de parámetros del kernel (buffers de red)
- Configuración de prioridad de procesos
- Inicio de monitores en background
- Despliegue del dashboard web

### 2. Monitor Avanzado
**Archivo**: `scripts/monitor_avanzado_gw250114.py`

Monitor inteligente que supervisa el análisis de GW250114:
- Monitoreo continuo del estado del sistema
- Verificación de métricas de análisis (SNR, validación estadística)
- Guardado de estado en JSON para integración con dashboard
- Manejo graceful de señales (SIGTERM, SIGINT)

### 3. Monitor de Recursos
**Archivo**: `scripts/monitor_recursos.sh`

Monitor de recursos del sistema en tiempo real:
- CPU usage con código de colores (verde/amarillo/rojo)
- Uso de memoria RAM
- Uso de disco
- Número de procesos activos
- Log continuo en `/tmp/monitor_recursos_gw250114.log`

### 4. Dashboard Web
**Archivo**: `dashboard/dashboard_avanzado.py`

Aplicación Flask/Gunicorn con interfaz web moderna:
- Vista en tiempo real del estado del sistema
- Métricas principales (SNR, eventos detectados, validaciones)
- Estado de módulos (monitor, optimización SNR, validación estadística)
- API REST completa
- Server-Sent Events para actualizaciones en vivo
- Interfaz responsive con gradientes modernos

### 5. Script de Detención
**Archivo**: `scripts/detener_servicios.sh`

Script para detener todos los servicios del sistema de forma segura:
- Detención graceful de procesos
- Limpieza de archivos temporales
- Eliminación de archivos PID

## Instalación

### Requisitos Previos

```bash
# Python 3.7+
python3 --version

# Bash
bash --version
```

### Instalación de Dependencias

```bash
# Clonar repositorio
git clone https://github.com/motanova84/gw250114-141hz-analysis
cd gw250114-141hz-analysis

# Instalar dependencias Python
pip install -r requirements.txt

# O usar make
make setup
```

## Uso

### Inicio Rápido

```bash
# Ejecutar sistema completo de optimización
./scripts/optimizacion_maxima.sh

# O con sudo para optimizaciones de sistema
sudo ./scripts/optimizacion_maxima.sh
```

### Acceso al Dashboard

Una vez iniciado el sistema, accede al dashboard:

```
http://localhost:5000
```

### Endpoints de la API

#### Estado Completo
```bash
curl http://localhost:5000/api/estado-completo
```

Respuesta:
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

#### Health Check
```bash
curl http://localhost:5000/health
```

#### Stream de Eventos en Tiempo Real
```bash
curl http://localhost:5000/api/stream
```

### Verificación de Estado

```bash
# Verificar procesos activos
ps aux | grep -E "monitor_avanzado|monitor_recursos|dashboard"

# Ver logs en tiempo real
tail -f /tmp/monitor_avanzado.log
tail -f /tmp/monitor_recursos.log
tail -f /tmp/dashboard.log

# Verificar PIDs guardados
cat /tmp/monitor_avanzado.pid
cat /tmp/monitor_recursos.pid
cat /tmp/dashboard.pid
```

### Detener el Sistema

```bash
# Detener todos los servicios
./scripts/detener_servicios.sh

# O manualmente
kill $(cat /tmp/monitor_avanzado.pid /tmp/monitor_recursos.pid /tmp/dashboard.pid 2>/dev/null)
```

## Características Avanzadas

### Optimizaciones de Sistema

El script aplica las siguientes optimizaciones (requiere sudo):

```bash
# Buffers de red maximizados
net.core.rmem_max = 268435456
net.core.wmem_max = 268435456
net.ipv4.tcp_rmem = "4096 87380 268435456"
net.ipv4.tcp_wmem = "4096 65536 268435456"
```

### Prioridad de Procesos

El monitor avanzado se ejecuta con máxima prioridad (requiere sudo):
```bash
nice -n -20 python3 monitor_avanzado_gw250114.py
```

### Configuración del Dashboard

El dashboard se despliega con Gunicorn en modo producción:
- 4 workers para alta disponibilidad
- Binding a 0.0.0.0:5000 (accesible desde red local)
- Logs separados para acceso y errores
- Modo daemon para ejecución en background

## Arquitectura

```
optimizacion_maxima.sh (Orquestador)
    │
    ├── Sistema (sysctl optimizations)
    │
    ├── monitor_avanzado_gw250114.py
    │   ├── Monitoreo de análisis GW250114
    │   ├── Chequeos de SNR
    │   ├── Validación estadística
    │   └── Estado JSON → /tmp/monitor_gw250114_estado.json
    │
    ├── monitor_recursos.sh
    │   ├── CPU monitoring
    │   ├── Memory monitoring
    │   ├── Disk monitoring
    │   └── Log → /tmp/monitor_recursos_gw250114.log
    │
    └── dashboard_avanzado.py (Flask/Gunicorn)
        ├── Web UI (HTML5 + CSS3)
        ├── API REST
        │   ├── /api/estado-completo
        │   ├── /api/estado
        │   ├── /api/metricas
        │   └── /api/stream (SSE)
        └── Health Check (/health)
```

## Archivos Generados

### PIDs
- `/tmp/monitor_avanzado.pid` - PID del monitor avanzado
- `/tmp/monitor_recursos.pid` - PID del monitor de recursos
- `/tmp/dashboard.pid` - PID del dashboard

### Logs
- `/tmp/monitor_avanzado.log` - Log del monitor avanzado
- `/tmp/monitor_recursos.log` - Log del monitor de recursos (detallado)
- `/tmp/monitor_recursos_gw250114.log` - Log alternativo de recursos
- `/tmp/dashboard.log` - Log del dashboard (Flask)
- `/tmp/dashboard_access.log` - Log de accesos HTTP (Gunicorn)
- `/tmp/dashboard_error.log` - Log de errores (Gunicorn)

### Estado
- `/tmp/monitor_gw250114_estado.json` - Estado actual del monitor

## Solución de Problemas

### Dashboard no inicia

```bash
# Verificar que Flask está instalado
pip install flask gunicorn

# Verificar que el puerto 5000 está libre
lsof -i :5000

# Ver errores en el log
cat /tmp/dashboard_error.log
```

### Monitor no responde

```bash
# Verificar que el proceso está corriendo
ps aux | grep monitor_avanzado

# Ver log para errores
tail -50 /tmp/monitor_avanzado.log

# Reiniciar solo el monitor
kill $(cat /tmp/monitor_avanzado.pid)
python3 scripts/monitor_avanzado_gw250114.py &
```

### Problemas de permisos

```bash
# El script puede ejecutarse sin sudo, pero algunas optimizaciones lo requieren
sudo ./scripts/optimizacion_maxima.sh

# O ejecutar sin sudo (sin optimizaciones de sistema)
./scripts/optimizacion_maxima.sh
```

## Integración con Makefile

Puedes agregar targets al Makefile para facilitar el uso:

```makefile
# Iniciar sistema de optimización
optimize:
	@echo "🚀 Iniciando sistema de optimización..."
	./scripts/optimizacion_maxima.sh

# Detener sistema
stop-optimize:
	@echo "🛑 Deteniendo sistema de optimización..."
	./scripts/detener_servicios.sh

# Ver estado
status-optimize:
	@echo "📊 Estado del sistema:"
	@curl -s http://localhost:5000/api/estado-completo | python3 -m json.tool || echo "Dashboard no disponible"
```

## Desarrollo

### Modificar el Dashboard

El dashboard está en `dashboard/dashboard_avanzado.py`. Para desarrollo:

```bash
# Modo desarrollo (con auto-reload)
cd dashboard
python3 -c "from dashboard_avanzado import app; app.run(debug=True)"
```

### Personalizar Monitores

Los monitores pueden configurarse modificando las variables al inicio de cada script:

```python
# En monitor_avanzado_gw250114.py
self.intervalo = 60  # Cambiar intervalo de monitoreo (segundos)
```

```bash
# En monitor_recursos.sh
INTERVALO=5  # Cambiar intervalo de monitoreo (segundos)
```

## Contribuir

Para contribuir mejoras al sistema de optimización:

1. Fork el repositorio
2. Crea una rama para tu feature
3. Realiza tus cambios
4. Envía un Pull Request

## Licencia

Este proyecto es parte del análisis de GW250114 y está disponible bajo la licencia del repositorio principal.

## Referencias

- [LIGO Scientific Collaboration](https://www.ligo.org/)
- [GWOSC - Gravitational Wave Open Science Center](https://www.gw-openscience.org/)
- [Flask Documentation](https://flask.palletsprojects.com/)
- [Gunicorn Documentation](https://gunicorn.org/)

---

**Nota**: Este sistema está diseñado para optimizar el rendimiento del análisis de GW250114. 
Las optimizaciones de kernel requieren privilegios de root pero el sistema puede funcionar sin ellas.
