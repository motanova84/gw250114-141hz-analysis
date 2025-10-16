# 📚 Documentación del Sistema de Alertas Avanzado

Documentación completa del Sistema de Alertas de Máxima Prioridad para GW250114.

## 📖 Documentos Disponibles

### 1. [SISTEMA_ALERTAS.md](SISTEMA_ALERTAS.md)
**Guía principal del sistema de alertas**

- Descripción general del sistema
- Características y niveles de prioridad
- Instalación y configuración
- Ejemplos de uso básico
- Guía de testing
- Seguridad y mejores prácticas
- Troubleshooting

**Para:** Usuarios que quieren entender y usar el sistema de alertas.

### 2. [INTEGRACION_ALERTAS.md](INTEGRACION_ALERTAS.md)
**Guía de integración con pipeline existente**

- Puntos de integración en el pipeline
- Ejemplos de integración completos
- Configuración por entorno
- Criterios de priorización
- Plantillas de mensajes
- Checklist de integración

**Para:** Desarrolladores que integran alertas en el pipeline de validación.

## 🚀 Inicio Rápido

### Instalación

```bash
# 1. Instalar dependencias
pip install aiohttp twilio pushbullet.py

# 2. Configurar credenciales
cp config/alertas.env.template config/alertas.env
# Editar config/alertas.env con credenciales reales
```

### Uso Básico

```python
import asyncio
from sistema_alertas_avanzado import SistemaAlertasAvanzado

async def main():
    sistema = SistemaAlertasAvanzado()
    
    evento = {'nombre': 'GW250114', 'detector': 'H1-L1'}
    resultados = {
        'frecuencia': 141.7001,
        'snr': 15.2,
        'p_value': 0.0001,
        'diferencia': 0.0000
    }
    
    await sistema.alerta_validacion_psi(evento, resultados)

asyncio.run(main())
```

## 🎯 Niveles de Prioridad

| Prioridad | Canales | Uso |
|-----------|---------|-----|
| **Máxima** | SMS + Push + Webhook + Llamada | Validación experimental confirmada |
| **Alta** | Email + Push + Webhook | Detección fuerte |
| **Media** | Email + Webhook | Detección prometedora |
| **Baja** | Email | Detección preliminar |

## 🧪 Testing

```bash
# Ejecutar suite completa de tests
python scripts/test_sistema_alertas.py

# Ejecutar ejemplo de integración
python scripts/ejemplo_integracion_alertas.py

# Ejecutar ejemplo básico
python scripts/sistema_alertas_avanzado.py
```

## 📁 Archivos Relacionados

### Scripts
- `scripts/sistema_alertas_avanzado.py` - Implementación principal
- `scripts/ejemplo_integracion_alertas.py` - Ejemplos de integración
- `scripts/test_sistema_alertas.py` - Suite de tests

### Configuración
- `config/alertas.env.template` - Template de configuración
- `config/alertas.env` - Configuración real (no en git)

### Documentación
- `docs/SISTEMA_ALERTAS.md` - Guía principal
- `docs/INTEGRACION_ALERTAS.md` - Guía de integración
- `docs/README.md` - Este archivo

## 🔒 Seguridad

**IMPORTANTE:** Nunca commits credenciales al repositorio

- ✅ `config/alertas.env.template` - Template público
- ❌ `config/alertas.env` - Credenciales privadas (en .gitignore)
- ✅ Variables de entorno - Método recomendado para producción

## 📊 Arquitectura

```
Sistema de Alertas
├── Configuración
│   ├── Variables de entorno
│   └── Archivo de configuración
├── Canales
│   ├── SMS (Twilio)
│   ├── Llamadas (Twilio)
│   ├── Push (Pushbullet)
│   ├── Webhooks (HTTP)
│   └── Email (SMTP)
├── Priorización
│   ├── Máxima → Todos los canales
│   ├── Alta → Push + Email + Webhook
│   ├── Media → Email + Webhook
│   └── Baja → Solo Email
└── Logging
    └── results/logs/alertas.log
```

## 🎓 Flujo de Trabajo Típico

1. **Configurar** credenciales (una vez)
2. **Importar** `SistemaAlertasAvanzado`
3. **Definir** evento y resultados
4. **Determinar** prioridad según criterios
5. **Enviar** alerta
6. **Revisar** logs y reportes

## 💡 Casos de Uso

### Caso 1: Validación Experimental Completa
```python
# Todos los criterios cumplidos → Alerta MÁXIMA
await sistema.alerta_validacion_psi(evento, resultados)
```

### Caso 2: Detección Significativa
```python
# SNR alto pero requiere más análisis → Alerta ALTA
await sistema.enviar_alertas_multicanal(mensaje, 'alta', evento, resultados)
```

### Caso 3: Progreso de Análisis
```python
# Actualización de estado → Alerta MEDIA o BAJA
await sistema.enviar_alertas_multicanal(mensaje, 'media')
```

## 🐛 Troubleshooting Común

### Problema: "Module not found: aiohttp"
**Solución:** `pip install aiohttp`

### Problema: "Authentication failed"
**Solución:** Verificar credenciales en `config/alertas.env`

### Problema: Alertas no se envían
**Solución:** 
1. Verificar conectividad de red
2. Revisar logs en `results/logs/alertas.log`
3. Ejecutar en modo debug

## 📞 Soporte

1. Leer esta documentación
2. Revisar ejemplos en `scripts/`
3. Ejecutar tests para validar instalación
4. Revisar logs para debugging

## 🗺️ Roadmap

- [x] Sistema básico multi-canal
- [x] Priorización jerárquica
- [x] Testing completo
- [x] Documentación
- [ ] Dashboard web
- [ ] Integración con Slack/Discord
- [ ] Sistema de reconocimiento de alertas
- [ ] Analytics de alertas

---

**Proyecto:** GW250114 - Análisis de frecuencia 141.7001 Hz  
**Versión:** 1.0.0  
**Última actualización:** 2025-10-15
