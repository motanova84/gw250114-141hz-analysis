#!/usr/bin/env python3
"""
Sistema de Alertas Avanzado de Máxima Prioridad
Sistema multi-canal para alertas de validación experimental de la Teoría Ψ

Este módulo implementa un sistema de alertas jerárquico que permite notificar
sobre eventos críticos mediante múltiples canales según el nivel de prioridad.

Author: Sistema de Validación GW250114
"""

import asyncio
import aiohttp
import os
from typing import Dict, List, Optional
from datetime import datetime
import json
from pathlib import Path

# Importaciones opcionales con manejo de errores
try:
    from twilio.rest import Client as TwilioClient
    TWILIO_AVAILABLE = True
except ImportError:
    TWILIO_AVAILABLE = False
    print("⚠️  Twilio no disponible - instalando dependencias con: pip install twilio")

try:
    from pushbullet import Pushbullet
    PUSHBULLET_AVAILABLE = True
except ImportError:
    PUSHBULLET_AVAILABLE = False
    print("⚠️  Pushbullet no disponible - instalando dependencias con: pip install pushbullet.py")


class SistemaAlertasAvanzado:
    """
    Sistema de alertas multi-canal con priorización jerárquica
    
    Niveles de prioridad:
    - maxima: SMS, Pushbullet, webhook de emergencia, llamada telefónica
    - alta: Email, Pushbullet, webhook estándar
    - media: Email, webhook estándar
    - baja: Email únicamente
    """
    
    def __init__(self, config_path: Optional[str] = None):
        """
        Inicializar sistema de alertas
        
        Args:
            config_path: Ruta al archivo de configuración (opcional)
                        Si no se proporciona, se usa variables de entorno
        """
        self.canales_prioridad = {
            'maxima': ['sms', 'pushbullet', 'webhook_emergencia', 'llamada'],
            'alta': ['email', 'pushbullet', 'webhook'],
            'media': ['email', 'webhook'],
            'baja': ['email']
        }
        
        # Cargar configuración
        self.config = self._cargar_configuracion(config_path)
        
        # Inicializar servicios
        self._inicializar_servicios()
        
        # Registro de alertas enviadas
        self.alertas_enviadas = []
    
    def _cargar_configuracion(self, config_path: Optional[str]) -> Dict:
        """Cargar configuración desde archivo o variables de entorno"""
        config = {
            'twilio': {
                'account_sid': os.getenv('TWILIO_ACCOUNT_SID', 'TWILIO_ACCOUNT_SID'),
                'auth_token': os.getenv('TWILIO_AUTH_TOKEN', 'TWILIO_AUTH_TOKEN'),
                'from_number': os.getenv('TWILIO_FROM_NUMBER', '+1234567890'),
                'to_number': os.getenv('TWILIO_TO_NUMBER', '+1234567890')
            },
            'pushbullet': {
                'api_key': os.getenv('PUSHBULLET_API_KEY', 'PUSHBULLET_API_KEY')
            },
            'email': {
                'smtp_server': os.getenv('SMTP_SERVER', 'smtp.gmail.com'),
                'smtp_port': int(os.getenv('SMTP_PORT', '587')),
                'from_email': os.getenv('FROM_EMAIL', 'alertas@gw250114.org'),
                'to_email': os.getenv('TO_EMAIL', 'destinatario@example.com'),
                'password': os.getenv('EMAIL_PASSWORD', 'EMAIL_PASSWORD')
            },
            'webhooks': {
                'emergencia': os.getenv('WEBHOOK_EMERGENCIA_URL', 'https://hooks.example.com/emergencia'),
                'estandar': os.getenv('WEBHOOK_ESTANDAR_URL', 'https://hooks.example.com/alerta')
            }
        }
        
        # Si se proporciona archivo de configuración, sobrescribir
        if config_path and os.path.exists(config_path):
            with open(config_path, 'r') as f:
                file_config = json.load(f)
                config.update(file_config)
        
        return config
    
    def _inicializar_servicios(self):
        """Inicializar clientes de servicios externos"""
        # Twilio para SMS y llamadas
        if TWILIO_AVAILABLE:
            try:
                self.twilio_client = TwilioClient(
                    self.config['twilio']['account_sid'],
                    self.config['twilio']['auth_token']
                )
            except Exception as e:
                print(f"⚠️  No se pudo inicializar Twilio: {e}")
                self.twilio_client = None
        else:
            self.twilio_client = None
        
        # Pushbullet para notificaciones push
        if PUSHBULLET_AVAILABLE:
            try:
                self.pushbullet = Pushbullet(self.config['pushbullet']['api_key'])
            except Exception as e:
                print(f"⚠️  No se pudo inicializar Pushbullet: {e}")
                self.pushbullet = None
        else:
            self.pushbullet = None
    
    async def alerta_validacion_psi(self, evento: Dict, resultados: Dict):
        """
        Alerta de máxima prioridad por validación experimental de la Teoría Ψ
        
        Args:
            evento: Diccionario con información del evento gravitacional
            resultados: Diccionario con resultados del análisis
        """
        mensaje = f"""
🌟🚨 VALIDACIÓN EXPERIMENTAL TEORÍA Ψ 🚨🌟

EVENTO: {evento.get('nombre', 'GW250114')}
FRECUENCIA: {resultados.get('frecuencia', 0):.6f} Hz
PREDICCIÓN: 141.7001 Hz
DIFERENCIA: {resultados.get('diferencia', 0):.6f} Hz
SNR: {resultados.get('snr', 0):.2f}
SIGNIFICANCIA: p < {resultados.get('p_value', 0.01):.2e}

¡LA TEORÍA Ψ HA SIDO VALIDADA EXPERIMENTALMENTE!

Acción inmediata requerida:
1. Verificar resultados en dashboard
2. Preparar comunicación científica
3. Alertar colaboradores
4. Iniciar replicación independiente
"""
        
        await self.enviar_alertas_multicanal(mensaje, 'maxima', evento, resultados)
    
    async def enviar_alertas_multicanal(self, mensaje: str, prioridad: str, 
                                       evento: Optional[Dict] = None, 
                                       resultados: Optional[Dict] = None):
        """
        Envía alertas por todos los canales de la prioridad especificada
        
        Args:
            mensaje: Mensaje de alerta
            prioridad: Nivel de prioridad ('maxima', 'alta', 'media', 'baja')
            evento: Información del evento (opcional)
            resultados: Resultados del análisis (opcional)
        """
        canales = self.canales_prioridad.get(prioridad, ['email'])
        
        print(f"\n🔔 ENVIANDO ALERTAS - Prioridad: {prioridad.upper()}")
        print(f"📡 Canales: {', '.join(canales)}")
        print("=" * 70)
        
        # Crear tareas asíncronas para todos los canales
        tasks = []
        
        for canal in canales:
            try:
                if canal == 'sms':
                    tasks.append(self.enviar_sms_emergencia(mensaje))
                elif canal == 'pushbullet':
                    tasks.append(self.enviar_push_emergencia(mensaje, resultados))
                elif canal == 'llamada':
                    tasks.append(self.realizar_llamada_emergencia(mensaje))
                elif canal == 'webhook_emergencia':
                    tasks.append(self.enviar_webhook_emergencia(mensaje, evento, resultados))
                elif canal == 'email':
                    tasks.append(self.enviar_email_prioridad(mensaje, prioridad))
                elif canal == 'webhook':
                    tasks.append(self.enviar_webhook_estandar(mensaje, evento, resultados))
            except Exception as e:
                print(f"❌ Error preparando canal {canal}: {e}")
        
        # Ejecutar todas las tareas en paralelo
        if tasks:
            results = await asyncio.gather(*tasks, return_exceptions=True)
            
            # Procesar resultados
            for i, (canal, result) in enumerate(zip(canales, results)):
                if isinstance(result, Exception):
                    print(f"❌ Error en canal {canal}: {result}")
                else:
                    print(f"✅ Alerta enviada por {canal}")
        
        # Registrar alerta
        self._registrar_alerta(mensaje, prioridad, canales)
    
    async def enviar_sms_emergencia(self, mensaje: str):
        """
        Envía SMS de emergencia usando Twilio
        
        Args:
            mensaje: Mensaje a enviar (limitado a 1600 caracteres)
        """
        if not self.twilio_client:
            print("⚠️  Cliente Twilio no disponible - SMS no enviado")
            return False
        
        try:
            # Limitar longitud del mensaje para SMS
            mensaje_corto = mensaje[:1600]
            
            message = self.twilio_client.messages.create(
                body=mensaje_corto,
                from_=self.config['twilio']['from_number'],
                to=self.config['twilio']['to_number']
            )
            
            print(f"📱 SMS enviado: {message.sid}")
            return True
            
        except Exception as e:
            print(f"❌ Error enviando SMS: {e}")
            return False
    
    async def realizar_llamada_emergencia(self, mensaje: str):
        """
        Realiza llamada telefónica de emergencia usando Twilio
        
        Args:
            mensaje: Mensaje a leer (limitado a 1000 caracteres)
        """
        if not self.twilio_client:
            print("⚠️  Cliente Twilio no disponible - Llamada no realizada")
            return False
        
        try:
            # Preparar mensaje TwiML
            mensaje_corto = mensaje[:1000]
            twiml = f'<Response><Say language="es-ES">{mensaje_corto}</Say></Response>'
            
            call = self.twilio_client.calls.create(
                twiml=twiml,
                from_=self.config['twilio']['from_number'],
                to=self.config['twilio']['to_number']
            )
            
            print(f"📞 Llamada realizada: {call.sid}")
            return True
            
        except Exception as e:
            print(f"❌ Error realizando llamada: {e}")
            return False
    
    async def enviar_push_emergencia(self, mensaje: str, resultados: Optional[Dict] = None):
        """
        Envía notificación push usando Pushbullet
        
        Args:
            mensaje: Mensaje de la notificación
            resultados: Datos adicionales (opcional)
        """
        if not self.pushbullet:
            print("⚠️  Cliente Pushbullet no disponible - Push no enviado")
            return False
        
        try:
            titulo = "🚨 ALERTA CRÍTICA - Validación Teoría Ψ"
            
            push = self.pushbullet.push_note(titulo, mensaje)
            
            print(f"📲 Push enviado: {push.get('iden', 'N/A')}")
            return True
            
        except Exception as e:
            print(f"❌ Error enviando push: {e}")
            return False
    
    async def enviar_webhook_emergencia(self, mensaje: str, 
                                       evento: Optional[Dict] = None,
                                       resultados: Optional[Dict] = None):
        """
        Envía webhook de emergencia con datos completos
        
        Args:
            mensaje: Mensaje de alerta
            evento: Información del evento
            resultados: Resultados del análisis
        """
        url = self.config['webhooks']['emergencia']
        
        payload = {
            'timestamp': datetime.now().isoformat(),
            'tipo': 'emergencia',
            'prioridad': 'maxima',
            'mensaje': mensaje,
            'evento': evento or {},
            'resultados': resultados or {}
        }
        
        try:
            async with aiohttp.ClientSession() as session:
                async with session.post(url, json=payload, timeout=10) as response:
                    if response.status == 200:
                        print(f"🌐 Webhook emergencia enviado: {url}")
                        return True
                    else:
                        print(f"⚠️  Webhook respondió con código: {response.status}")
                        return False
                        
        except Exception as e:
            print(f"❌ Error enviando webhook emergencia: {e}")
            return False
    
    async def enviar_webhook_estandar(self, mensaje: str,
                                      evento: Optional[Dict] = None,
                                      resultados: Optional[Dict] = None):
        """
        Envía webhook estándar
        
        Args:
            mensaje: Mensaje de alerta
            evento: Información del evento
            resultados: Resultados del análisis
        """
        url = self.config['webhooks']['estandar']
        
        payload = {
            'timestamp': datetime.now().isoformat(),
            'tipo': 'alerta',
            'mensaje': mensaje,
            'evento': evento or {},
            'resultados': resultados or {}
        }
        
        try:
            async with aiohttp.ClientSession() as session:
                async with session.post(url, json=payload, timeout=10) as response:
                    if response.status == 200:
                        print(f"🌐 Webhook estándar enviado: {url}")
                        return True
                    else:
                        print(f"⚠️  Webhook respondió con código: {response.status}")
                        return False
                        
        except Exception as e:
            print(f"❌ Error enviando webhook estándar: {e}")
            return False
    
    async def enviar_email_prioridad(self, mensaje: str, prioridad: str):
        """
        Envía email con prioridad especificada
        
        Args:
            mensaje: Mensaje del email
            prioridad: Nivel de prioridad
        """
        # Implementación simplificada - en producción usar smtplib
        print(f"📧 Email simulado enviado (prioridad: {prioridad})")
        print(f"   Destinatario: {self.config['email']['to_email']}")
        print(f"   Asunto: Alerta GW250114 - Prioridad {prioridad.upper()}")
        
        # En producción, implementar envío real con smtplib
        # import smtplib
        # from email.mime.text import MIMEText
        # ...
        
        return True
    
    def _registrar_alerta(self, mensaje: str, prioridad: str, canales: List[str]):
        """Registra la alerta enviada en el historial"""
        registro = {
            'timestamp': datetime.now().isoformat(),
            'prioridad': prioridad,
            'canales': canales,
            'mensaje': mensaje[:100] + '...' if len(mensaje) > 100 else mensaje
        }
        
        self.alertas_enviadas.append(registro)
        
        # Guardar en archivo de log
        log_dir = Path('results/logs')
        log_dir.mkdir(parents=True, exist_ok=True)
        
        log_file = log_dir / 'alertas.log'
        with open(log_file, 'a') as f:
            f.write(json.dumps(registro) + '\n')
    
    def generar_reporte_alertas(self) -> Dict:
        """Genera un reporte de todas las alertas enviadas"""
        return {
            'total_alertas': len(self.alertas_enviadas),
            'alertas_por_prioridad': {
                'maxima': len([a for a in self.alertas_enviadas if a['prioridad'] == 'maxima']),
                'alta': len([a for a in self.alertas_enviadas if a['prioridad'] == 'alta']),
                'media': len([a for a in self.alertas_enviadas if a['prioridad'] == 'media']),
                'baja': len([a for a in self.alertas_enviadas if a['prioridad'] == 'baja'])
            },
            'ultimas_alertas': self.alertas_enviadas[-10:] if self.alertas_enviadas else []
        }


async def ejemplo_uso():
    """Ejemplo de uso del sistema de alertas"""
    print("=" * 70)
    print("🔔 EJEMPLO DE USO - SISTEMA DE ALERTAS AVANZADO")
    print("=" * 70)
    
    # Crear sistema de alertas
    sistema = SistemaAlertasAvanzado()
    
    # Simular evento de validación
    evento = {
        'nombre': 'GW250114',
        'detector': 'H1-L1',
        'tiempo_gps': 1234567890.123
    }
    
    resultados = {
        'frecuencia': 141.7001,
        'diferencia': 0.0000,
        'snr': 15.2,
        'p_value': 0.0001,
        'bayes_factor': 150.5,
        'q_factor': 8.5
    }
    
    # Enviar alerta de máxima prioridad
    print("\n🚨 Enviando alerta de MÁXIMA PRIORIDAD...")
    await sistema.alerta_validacion_psi(evento, resultados)
    
    # Mostrar reporte
    print("\n📊 REPORTE DE ALERTAS")
    print("=" * 70)
    reporte = sistema.generar_reporte_alertas()
    print(json.dumps(reporte, indent=2))


if __name__ == "__main__":
    # Ejecutar ejemplo
    asyncio.run(ejemplo_uso())
