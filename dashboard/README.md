# 📊 Dashboard Avanzado GW250114

## Descripción

Dashboard web de máxima eficiencia para monitoreo en tiempo real del sistema de análisis GW250114. Proporciona visualización de métricas del sistema, estado de operación y estadísticas de detección.

## 🚀 Características Principales

- **Monitoreo en Tiempo Real**: Stream de datos actualizado cada segundo usando Server-Sent Events (SSE)
- **Métricas del Sistema**:
  - Uso de CPU
  - Uso de Memoria
  - Latencia de Red
  - Eventos Procesados
  - Confianza de Detección
  - Estado del Sistema
- **Interfaz Moderna**: Diseño responsive con gradientes y animaciones
- **Información Detallada**: Datos técnicos del sistema de análisis GW250114
- **Visualización Intuitiva**: Barras de progreso y badges de estado

## 📋 Requisitos

```bash
flask>=2.3.0
numpy>=1.21.0
```

## 🔧 Instalación

1. Asegúrate de tener el entorno virtual activado:
```bash
source venv/bin/activate  # Linux/Mac
# o
venv\Scripts\activate  # Windows
```

2. Instala las dependencias:
```bash
pip install -r requirements.txt
```

## 🎯 Uso

### Iniciar el Dashboard

```bash
cd dashboard
python dashboard_avanzado.py
```

El dashboard estará disponible en: `http://localhost:5000`

### Configuración

Por defecto, el dashboard se ejecuta en:
- **Host**: `0.0.0.0` (accesible desde cualquier interfaz de red)
- **Puerto**: `5000`
- **Modo Debug**: `True` (desactivar en producción)

Para cambiar la configuración, edita las últimas líneas de `dashboard_avanzado.py`:

```python
app.run(debug=False, host='127.0.0.1', port=8080)
```

## 🌐 API Endpoints

### GET `/`
Página principal del dashboard

**Respuesta**: HTML del dashboard interactivo

### GET `/api/stream`
Stream de datos en tiempo real usando Server-Sent Events (SSE)

**Respuesta**: Stream continuo de datos JSON
```json
{
  "timestamp": "2025-10-15T12:00:00.000000",
  "cpu_usage": 15.3,
  "memory_usage": 45.2,
  "network_latency": 12.5,
  "events_processed": 523,
  "detection_confidence": 0.9823,
  "system_status": "OPTIMO"
}
```

### GET `/api/estado-completo`
Información completa del sistema

**Respuesta**: JSON con datos estáticos del sistema
```json
{
  "sistema": "Monitor Avanzado GW250114",
  "version": "2.0.0",
  "estado": "OPERATIVO",
  "ultima_verificacion": "2025-10-15T12:00:00.000000",
  "metricas": {
    "sensibilidad_actual": "141.7001 ± 0.0001 Hz",
    "tiempo_respuesta": "< 2 segundos",
    "confianza_deteccion": "99.9%",
    "eventos_monitoreados": "247",
    "falsos_positivos": "0.1%"
  }
}
```

## 🎨 Interfaz de Usuario

### Métricas Visualizadas

1. **CPU Usage**: Porcentaje de uso del procesador
2. **Memory Usage**: Porcentaje de memoria utilizada
3. **Network Latency**: Latencia de red en milisegundos
4. **Events Processed**: Número de eventos procesados
5. **Detection Confidence**: Nivel de confianza de detección (0-100%)
6. **System Status**: Estado actual del sistema (ÓPTIMO/ADVERTENCIA/CRÍTICO)

### Información del Sistema

- Sistema: Monitor Avanzado GW250114
- Versión: 2.0.0
- Sensibilidad: 141.7001 ± 0.0001 Hz
- Tiempo de Respuesta: < 2 segundos
- Confianza de Detección: 99.9%
- Eventos Monitoreados: 247
- Falsos Positivos: 0.1%

## 🔧 Arquitectura Técnica

### Backend (Flask)

- **Framework**: Flask 2.3+
- **Threading**: Generación de datos en hilo separado para no bloquear el servidor
- **SSE**: Server-Sent Events para streaming en tiempo real
- **JSON API**: Endpoints RESTful para datos estáticos

### Frontend (HTML/CSS/JavaScript)

- **HTML5**: Estructura semántica
- **CSS3**: Gradientes, animaciones y diseño responsive
- **JavaScript Vanilla**: EventSource API para SSE, Fetch API para datos estáticos
- **Sin dependencias**: No requiere jQuery, React u otros frameworks

### Patrón de Diseño

- **Singleton**: Instancia única de `DashboardAvanzado`
- **Observer**: EventSource para actualizaciones en tiempo real
- **MVC**: Separación clara entre backend (modelo), frontend (vista) y lógica de actualización (controlador)

## 🛠️ Personalización

### Modificar Frecuencia de Actualización

En `dashboard_avanzado.py`, línea 33:
```python
time.sleep(1)  # Cambiar a 0.5 para actualizar cada medio segundo
```

### Añadir Nuevas Métricas

1. En `generar_datos_tiempo_real()`, añadir la métrica:
```python
self.metricas_tiempo_real['nueva_metrica'] = valor
```

2. En el HTML, añadir un nuevo card:
```html
<div class="metric-card">
    <div class="metric-title">📈 Nueva Métrica</div>
    <div class="metric-value" id="nueva-metrica">--</div>
</div>
```

3. En el JavaScript, actualizar el valor:
```javascript
document.getElementById('nueva-metrica').textContent = data.nueva_metrica;
```

### Cambiar Colores del Tema

En `dashboard_avanzado.html`, sección `<style>`:
```css
/* Color principal */
--primary-color: #00d4ff;  /* Azul cyan */

/* Gradiente de fondo */
background: linear-gradient(135deg, #0a0e27 0%, #1a1f3a 100%);
```

## 🚨 Solución de Problemas

### Error: "Address already in use"
```bash
# Encontrar el proceso usando el puerto 5000
lsof -i :5000

# Matar el proceso
kill -9 <PID>
```

### Error: "ModuleNotFoundError: No module named 'flask'"
```bash
pip install flask
```

### El stream no se actualiza
- Verificar que el navegador soporte Server-Sent Events
- Revisar la consola del navegador para errores
- Comprobar que el hilo de generación de datos esté activo

## 📈 Próximas Mejoras

- [ ] Integración con datos reales del sistema de análisis
- [ ] Gráficos históricos con Chart.js o D3.js
- [ ] Alertas configurables por umbral
- [ ] Exportación de métricas a CSV/JSON
- [ ] Autenticación y control de acceso
- [ ] WebSocket para comunicación bidireccional
- [ ] Panel de configuración en tiempo real
- [ ] Modo oscuro/claro conmutable

## 📝 Notas

- **Modo Debug**: Desactivar en producción para evitar fugas de información
- **Seguridad**: Implementar autenticación antes de exponer públicamente
- **Rendimiento**: El stream SSE mantiene una conexión abierta por cliente
- **Escalabilidad**: Considerar Redis o similar para múltiples workers

## 🤝 Contribuciones

Para añadir nuevas funcionalidades o reportar bugs:
1. Fork del repositorio
2. Crear rama feature (`git checkout -b feature/nueva-funcionalidad`)
3. Commit de cambios (`git commit -am 'Añadir nueva funcionalidad'`)
4. Push a la rama (`git push origin feature/nueva-funcionalidad`)
5. Crear Pull Request

## 📄 Licencia

Parte del proyecto GW250114 - 141.7001 Hz Analysis

---

**Desarrollado para el análisis de ondas gravitacionales GW250114** 🌌
