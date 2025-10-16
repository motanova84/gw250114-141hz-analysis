# 🔔 Sistema de Alertas Avanzado - GW250114

Sistema multi-canal de alertas de máxima prioridad para validación experimental de la Teoría Ψ.

## 📋 Descripción

El Sistema de Alertas Avanzado proporciona notificaciones en tiempo real mediante múltiples canales según el nivel de prioridad del evento. Diseñado específicamente para alertar sobre la validación experimental de la frecuencia 141.7001 Hz en eventos gravitacionales.

## 🌟 Características

### Niveles de Prioridad

| Prioridad | Canales | Uso |
|-----------|---------|-----|
| **Máxima** | SMS, Pushbullet, Webhook de emergencia, Llamada telefónica | Validación experimental confirmada |
| **Alta** | Email, Pushbullet, Webhook estándar | Detección fuerte, requiere revisión |
| **Media** | Email, Webhook estándar | Detección prometedora |
| **Baja** | Email | Detección preliminar |

### Canales Disponibles

- **📱 SMS**: Mensajes de texto vía Twilio
- **📞 Llamadas**: Llamadas automáticas de voz vía Twilio
- **📲 Push Notifications**: Notificaciones push vía Pushbullet
- **🌐 Webhooks**: POST HTTP a URLs configurables
- **📧 Email**: Correo electrónico vía SMTP

## 🚀 Instalación

### 1. Instalar Dependencias

```bash
pip install -r requirements.txt
```

O instalar manualmente:

```bash
pip install aiohttp twilio pushbullet.py
```

### 2. Configurar Credenciales

Copiar el template de configuración:

```bash
cp config/alertas.env.template config/alertas.env
```

Editar `config/alertas.env` o configurar variables de entorno:

```bash
# Twilio
export TWILIO_ACCOUNT_SID="your_account_sid"
export TWILIO_AUTH_TOKEN="your_auth_token"
export TWILIO_FROM_NUMBER="+1234567890"
export TWILIO_TO_NUMBER="+1234567890"

# Pushbullet
export PUSHBULLET_API_KEY="your_api_key"

# Email
export SMTP_SERVER="smtp.gmail.com"
export SMTP_PORT="587"
export FROM_EMAIL="your_email@gmail.com"
export TO_EMAIL="destination@example.com"
export EMAIL_PASSWORD="your_app_password"

# Webhooks
export WEBHOOK_EMERGENCIA_URL="https://hooks.example.com/emergencia"
export WEBHOOK_ESTANDAR_URL="https://hooks.example.com/alerta"
```

## 💻 Uso

### Uso Básico

```python
import asyncio
from sistema_alertas_avanzado import SistemaAlertasAvanzado

async def main():
    # Inicializar sistema
    sistema = SistemaAlertasAvanzado()
    
    # Definir evento y resultados
    evento = {
        'nombre': 'GW250114',
        'detector': 'H1-L1',
        'tiempo_gps': 1234567890.123
    }
    
    resultados = {
        'frecuencia': 141.7001,
        'snr': 15.2,
        'p_value': 0.0001,
        'bayes_factor': 150.5,
        'diferencia': 0.0000
    }
    
    # Enviar alerta de máxima prioridad
    await sistema.alerta_validacion_psi(evento, resultados)

# Ejecutar
asyncio.run(main())
```

### Alertas Personalizadas

```python
# Alerta de prioridad media
mensaje = "Detección en análisis - SNR: 8.5"
await sistema.enviar_alertas_multicanal(
    mensaje, 
    'media',
    evento,
    resultados
)

# Alerta de prioridad alta
mensaje = "Detección significativa - Revisión requerida"
await sistema.enviar_alertas_multicanal(
    mensaje,
    'alta',
    evento,
    resultados
)
```

## 🧪 Testing

### Ejecutar Tests

```bash
# Ejecutar suite completa de tests
python scripts/test_sistema_alertas.py

# Ejecutar ejemplo de integración
python scripts/ejemplo_integracion_alertas.py

# Ejecutar ejemplo básico
python scripts/sistema_alertas_avanzado.py
```

## 🔒 Seguridad

### Mejores Prácticas

1. **No compartir credenciales** - Mantener `.env` fuera de control de versiones
2. **Usar contraseñas específicas de aplicación** - Para Gmail y otros servicios
3. **Rotar credenciales periódicamente** - Cambiar tokens regularmente
4. **Validar webhooks** - Usar HTTPS y autenticación

## 📊 Reportes

Las alertas se registran automáticamente en `results/logs/alertas.log`

```python
reporte = sistema.generar_reporte_alertas()
print(f"Total de alertas: {reporte['total_alertas']}")
```

## 📚 Documentación Completa

Ver ejemplos completos en:
- `scripts/sistema_alertas_avanzado.py` - Implementación principal
- `scripts/ejemplo_integracion_alertas.py` - Ejemplos de integración
- `scripts/test_sistema_alertas.py` - Suite de tests
- `config/alertas.env.template` - Template de configuración

---

**Versión:** 1.0.0  
**Fecha:** 2025-10-15
