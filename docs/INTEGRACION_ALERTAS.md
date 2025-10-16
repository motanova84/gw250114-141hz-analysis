# 🔗 Guía de Integración del Sistema de Alertas

Este documento describe cómo integrar el Sistema de Alertas Avanzado con el pipeline de validación científica existente.

## 📋 Resumen de Integración

El sistema de alertas se puede integrar en cualquier punto del pipeline de validación donde se obtengan resultados científicos que requieran notificación.

## 🎯 Puntos de Integración

### 1. Pipeline de Validación Principal (`scripts/pipeline_validacion.py`)

Agregar alertas al final de la validación:

```python
# En pipeline_validacion.py
import asyncio
from sistema_alertas_avanzado import SistemaAlertasAvanzado

async def main_with_alerts():
    # Pipeline existente
    resultados = ejecutar_pipeline_validacion()
    
    # Agregar sistema de alertas
    sistema_alertas = SistemaAlertasAvanzado()
    
    if validacion_exitosa(resultados):
        evento = {
            'nombre': 'GW250114',
            'detector': 'H1-L1',
            'tiempo_gps': resultados.get('tiempo_gps')
        }
        
        await sistema_alertas.alerta_validacion_psi(evento, resultados)

if __name__ == "__main__":
    asyncio.run(main_with_alerts())
```

### 2. Sistema de Validación Completo (`scripts/sistema_validacion_completo.py`)

Agregar alertas después de cada módulo:

```python
# En sistema_validacion_completo.py
from sistema_alertas_avanzado import SistemaAlertasAvanzado
import asyncio

class SistemaValidacionCompleto:
    def __init__(self):
        self.alertas = SistemaAlertasAvanzado()
        # ... resto de inicialización
    
    async def ejecutar_con_alertas(self):
        """Ejecutar validación con alertas integradas"""
        
        # Módulo 1: Caracterización Bayesiana
        resultado_bayes = self.ejecutar_caracterizacion_bayesiana()
        if resultado_bayes['estado'] == 'completado':
            mensaje = f"Caracterización Bayesiana completada - Q: {resultado_bayes['q_factor']}"
            await self.alertas.enviar_alertas_multicanal(mensaje, 'baja')
        
        # Módulo 2-4: Continuar con otros módulos...
        
        # Alerta final si todos los módulos tienen éxito
        if self.todos_modulos_exitosos():
            await self.alertas.alerta_validacion_psi(evento, resultados_consolidados)
```

### 3. Validación GW150914 (`scripts/validar_gw150914.py`)

Agregar alertas para control científico:

```python
# En validar_gw150914.py
from sistema_alertas_avanzado import SistemaAlertasAvanzado

async def validar_con_alertas():
    # Análisis existente
    h1_data, l1_data, merger_time = load_gw150914_data()
    resultados = calcular_bayes_factor(...)
    
    # Sistema de alertas
    sistema = SistemaAlertasAvanzado()
    
    if resultados['bayes_factor'] > 10 and resultados['p_value'] < 0.01:
        evento = {
            'nombre': 'GW150914',
            'detector': 'H1-L1',
            'tiempo_gps': merger_time
        }
        
        await sistema.enviar_alertas_multicanal(
            f"GW150914 control: BF={resultados['bayes_factor']:.2f}",
            'alta',
            evento,
            resultados
        )
```

### 4. Búsqueda Sistemática GWTC-1 (`scripts/busqueda_sistematica_gwtc1.py`)

Alertas por cada detección significativa:

```python
# En busqueda_sistematica_gwtc1.py
from sistema_alertas_avanzado import SistemaAlertasAvanzado

class BusquedaSistematicaGWTC1:
    def __init__(self):
        self.alertas = SistemaAlertasAvanzado()
        # ... resto de inicialización
    
    async def buscar_con_alertas(self):
        """Búsqueda sistemática con alertas"""
        
        for evento_nombre in self.eventos_gwtc1:
            resultados = self.analizar_evento(evento_nombre)
            
            # Alerta si se detecta 141.7 Hz con SNR alto
            if self.es_deteccion_significativa(resultados):
                await self.alertas.enviar_alertas_multicanal(
                    f"Detección en {evento_nombre}: {resultados['frecuencia']:.4f} Hz",
                    'alta',
                    {'nombre': evento_nombre},
                    resultados
                )
```

## 🔧 Configuración por Entorno

### Desarrollo / Testing

```python
# Usar alertas silenciosas en desarrollo
import os
os.environ['ALERTA_MODO'] = 'silencioso'

sistema = SistemaAlertasAvanzado()
# Las alertas se registran pero no se envían realmente
```

### Producción

```python
# Cargar credenciales desde archivo .env
from dotenv import load_dotenv
load_dotenv('config/alertas.env')

sistema = SistemaAlertasAvanzado()
# Las alertas se envían a servicios reales
```

## 📊 Ejemplo Completo: Pipeline con Alertas Progresivas

```python
#!/usr/bin/env python3
"""
Pipeline de validación con alertas progresivas
"""
import asyncio
from sistema_alertas_avanzado import SistemaAlertasAvanzado

async def pipeline_completo_con_alertas():
    """Pipeline completo con sistema de alertas integrado"""
    
    sistema = SistemaAlertasAvanzado()
    
    # Fase 1: Descarga de datos
    print("📡 Descargando datos...")
    await sistema.enviar_alertas_multicanal(
        "Iniciando descarga de datos GW250114",
        'baja'
    )
    
    # Fase 2: Preprocesamiento
    print("🔧 Preprocesando datos...")
    # ... procesamiento ...
    
    # Fase 3: Análisis de frecuencias
    print("📊 Analizando frecuencias...")
    resultados_freq = analizar_frecuencias()
    
    if resultados_freq['snr'] > 8:
        await sistema.enviar_alertas_multicanal(
            f"Detección prometedora: SNR={resultados_freq['snr']:.2f}",
            'media',
            evento={'nombre': 'GW250114'},
            resultados=resultados_freq
        )
    
    # Fase 4: Validación estadística
    print("🔬 Validación estadística...")
    resultados_stat = validacion_estadistica()
    
    if resultados_stat['p_value'] < 0.01:
        await sistema.enviar_alertas_multicanal(
            f"Significancia confirmada: p={resultados_stat['p_value']:.4f}",
            'alta',
            evento={'nombre': 'GW250114'},
            resultados=resultados_stat
        )
    
    # Fase 5: Validación final
    print("✅ Validación final...")
    if todos_criterios_cumplidos(resultados_freq, resultados_stat):
        evento = {
            'nombre': 'GW250114',
            'detector': 'H1-L1',
            'tiempo_gps': resultados_freq['tiempo_gps']
        }
        
        resultados_finales = {
            'frecuencia': resultados_freq['frecuencia'],
            'snr': resultados_freq['snr'],
            'p_value': resultados_stat['p_value'],
            'bayes_factor': resultados_stat['bayes_factor'],
            'diferencia': abs(resultados_freq['frecuencia'] - 141.7001)
        }
        
        # ¡ALERTA DE MÁXIMA PRIORIDAD!
        await sistema.alerta_validacion_psi(evento, resultados_finales)
    
    # Generar reporte
    reporte = sistema.generar_reporte_alertas()
    print(f"\n📈 Alertas enviadas: {reporte['total_alertas']}")

if __name__ == "__main__":
    asyncio.run(pipeline_completo_con_alertas())
```

## 🎛️ Configuración de Prioridades

### Criterios Recomendados

```python
def determinar_prioridad(resultados):
    """Determinar prioridad de alerta basado en resultados"""
    
    snr = resultados.get('snr', 0)
    p_value = resultados.get('p_value', 1)
    bayes_factor = resultados.get('bayes_factor', 0)
    freq_diff = abs(resultados.get('frecuencia', 0) - 141.7001)
    
    # Prioridad MÁXIMA: Validación completa
    if (snr > 10 and 
        p_value < 0.01 and 
        bayes_factor > 10 and 
        freq_diff < 0.01):
        return 'maxima'
    
    # Prioridad ALTA: Detección fuerte
    elif snr > 8 and p_value < 0.05:
        return 'alta'
    
    # Prioridad MEDIA: Detección prometedora
    elif snr > 5:
        return 'media'
    
    # Prioridad BAJA: Detección preliminar
    else:
        return 'baja'
```

## 📝 Plantilla de Mensajes Personalizados

```python
def generar_mensaje_alerta(evento, resultados, nivel):
    """Generar mensaje personalizado según nivel"""
    
    if nivel == 'maxima':
        return f"""
🌟🚨 VALIDACIÓN EXPERIMENTAL TEORÍA Ψ 🚨🌟

EVENTO: {evento['nombre']}
FRECUENCIA: {resultados['frecuencia']:.6f} Hz
PREDICCIÓN: 141.7001 Hz
DIFERENCIA: {resultados['diferencia']:.6f} Hz
SNR: {resultados['snr']:.2f}
SIGNIFICANCIA: p < {resultados['p_value']:.2e}

¡VALIDACIÓN EXPERIMENTAL CONFIRMADA!
"""
    
    elif nivel == 'alta':
        return f"""
📊 DETECCIÓN SIGNIFICATIVA - {evento['nombre']}

Frecuencia: {resultados['frecuencia']:.4f} Hz
SNR: {resultados['snr']:.2f}
p-value: {resultados['p_value']:.4f}

Requiere revisión inmediata.
"""
    
    elif nivel == 'media':
        return f"""
📈 Detección prometedora en {evento['nombre']}
SNR: {resultados['snr']:.2f}
Análisis en progreso.
"""
    
    else:  # baja
        return f"""
📋 Detección preliminar en {evento['nombre']}
SNR: {resultados['snr']:.2f}
"""
```

## 🔍 Monitoreo y Debug

### Activar Modo Verbose

```python
# En desarrollo, para ver todos los detalles
import logging
logging.basicConfig(level=logging.DEBUG)

sistema = SistemaAlertasAvanzado()
```

### Revisar Log de Alertas

```bash
# Ver últimas alertas
tail -f results/logs/alertas.log

# Buscar alertas de máxima prioridad
grep "maxima" results/logs/alertas.log
```

## ✅ Checklist de Integración

- [ ] Instalar dependencias: `pip install aiohttp twilio pushbullet.py`
- [ ] Copiar template: `cp config/alertas.env.template config/alertas.env`
- [ ] Configurar credenciales en `config/alertas.env`
- [ ] Importar `SistemaAlertasAvanzado` en scripts relevantes
- [ ] Agregar llamadas a alertas en puntos clave del pipeline
- [ ] Configurar criterios de prioridad según necesidades
- [ ] Probar en modo desarrollo antes de producción
- [ ] Verificar logs en `results/logs/alertas.log`
- [ ] Documentar puntos de integración específicos

## 🆘 Soporte

Para problemas de integración:

1. Revisar este documento
2. Ejecutar tests: `python scripts/test_sistema_alertas.py`
3. Ver ejemplos: `python scripts/ejemplo_integracion_alertas.py`
4. Consultar documentación: `docs/SISTEMA_ALERTAS.md`

---

**Última actualización:** 2025-10-15  
**Versión:** 1.0.0
