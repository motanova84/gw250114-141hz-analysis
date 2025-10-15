#!/usr/bin/env python3
"""
Integración del Sistema de Alertas con el Pipeline de Validación
Demuestra cómo integrar alertas en el flujo de validación existente
"""

import sys
import asyncio
from pathlib import Path

# Agregar directorio de scripts al path
sys.path.insert(0, str(Path(__file__).parent))

from sistema_alertas_avanzado import SistemaAlertasAvanzado


async def validacion_con_alertas():
    """
    Ejemplo de integración del sistema de alertas con validación científica
    """
    print("🌌 VALIDACIÓN GW250114 CON SISTEMA DE ALERTAS")
    print("=" * 70)
    
    # Inicializar sistema de alertas
    sistema_alertas = SistemaAlertasAvanzado()
    
    # Simular resultados de validación científica
    # En producción, estos datos vendrían de los módulos de análisis
    evento = {
        'nombre': 'GW250114',
        'detector': 'H1-L1',
        'tiempo_gps': 1234567890.123,
        'masa_total': 65.0,
        'masa_final': 62.0
    }
    
    print("\n🔬 Ejecutando análisis científico...")
    print("   1. Análisis de frecuencias...")
    print("   2. Cálculo de SNR...")
    print("   3. Estimación de p-value...")
    print("   4. Bayes Factor...")
    
    # Resultados simulados
    resultados = {
        'frecuencia': 141.7001,
        'diferencia': 0.0000,  # Diferencia con predicción teórica
        'snr': 15.2,
        'p_value': 0.0001,
        'bayes_factor': 150.5,
        'q_factor': 8.5,
        'coherencia_h1_l1': 0.87
    }
    
    print("   ✅ Análisis completado\n")
    
    # Verificar criterios de validación
    criterios_cumplidos = {
        'frecuencia_match': abs(resultados['frecuencia'] - 141.7001) < 0.01,
        'snr_alto': resultados['snr'] > 10,
        'significancia': resultados['p_value'] < 0.01,
        'bayes_favorable': resultados['bayes_factor'] > 10,
        'coherencia_alta': resultados['coherencia_h1_l1'] > 0.7
    }
    
    print("📊 CRITERIOS DE VALIDACIÓN")
    print("=" * 70)
    for criterio, cumplido in criterios_cumplidos.items():
        emoji = "✅" if cumplido else "❌"
        print(f"   {emoji} {criterio}: {cumplido}")
    
    # Determinar si se cumplieron todos los criterios
    todos_cumplidos = all(criterios_cumplidos.values())
    
    if todos_cumplidos:
        print("\n🌟 ¡TODOS LOS CRITERIOS CUMPLIDOS!")
        print("🚨 Activando alerta de MÁXIMA PRIORIDAD...\n")
        
        # Enviar alerta de máxima prioridad
        await sistema_alertas.alerta_validacion_psi(evento, resultados)
        
    else:
        print("\n⚠️  No todos los criterios fueron cumplidos")
        print("📝 Enviando alerta de prioridad MEDIA...\n")
        
        mensaje = f"""
📊 ACTUALIZACIÓN ANÁLISIS GW250114

EVENTO: {evento['nombre']}
ESTADO: En análisis
FRECUENCIA DETECTADA: {resultados['frecuencia']:.4f} Hz
SNR: {resultados['snr']:.2f}

Criterios cumplidos: {sum(criterios_cumplidos.values())}/{len(criterios_cumplidos)}

Requiere análisis adicional.
        """
        
        await sistema_alertas.enviar_alertas_multicanal(mensaje, 'media', evento, resultados)
    
    # Generar reporte final
    print("\n" + "=" * 70)
    print("📈 REPORTE DE ALERTAS ENVIADAS")
    print("=" * 70)
    
    reporte = sistema_alertas.generar_reporte_alertas()
    print(f"Total de alertas: {reporte['total_alertas']}")
    print("\nPor prioridad:")
    for prioridad, cantidad in reporte['alertas_por_prioridad'].items():
        if cantidad > 0:
            print(f"   • {prioridad}: {cantidad}")
    
    return todos_cumplidos


async def ejemplo_alertas_progresivas():
    """
    Ejemplo de alertas progresivas según el nivel de confianza
    """
    print("\n\n" + "=" * 70)
    print("🔔 EJEMPLO: ALERTAS PROGRESIVAS")
    print("=" * 70)
    
    sistema = SistemaAlertasAvanzado()
    
    evento_base = {
        'nombre': 'GW250114',
        'detector': 'H1-L1'
    }
    
    # Escenario 1: SNR bajo - Alerta baja
    print("\n📊 Escenario 1: SNR bajo (4.5)")
    resultados_1 = {
        'frecuencia': 141.7001,
        'snr': 4.5,
        'p_value': 0.05,
        'diferencia': 0.0001
    }
    
    mensaje_1 = f"Detección preliminar - SNR: {resultados_1['snr']}"
    await sistema.enviar_alertas_multicanal(mensaje_1, 'baja', evento_base, resultados_1)
    
    # Escenario 2: SNR medio - Alerta media
    print("\n📊 Escenario 2: SNR medio (8.0)")
    resultados_2 = {
        'frecuencia': 141.7001,
        'snr': 8.0,
        'p_value': 0.02,
        'diferencia': 0.0001
    }
    
    mensaje_2 = f"Detección prometedora - SNR: {resultados_2['snr']}"
    await sistema.enviar_alertas_multicanal(mensaje_2, 'media', evento_base, resultados_2)
    
    # Escenario 3: SNR alto - Alerta alta
    print("\n📊 Escenario 3: SNR alto (12.0)")
    resultados_3 = {
        'frecuencia': 141.7001,
        'snr': 12.0,
        'p_value': 0.005,
        'diferencia': 0.0001
    }
    
    mensaje_3 = f"Detección fuerte - SNR: {resultados_3['snr']}"
    await sistema.enviar_alertas_multicanal(mensaje_3, 'alta', evento_base, resultados_3)
    
    # Escenario 4: Validación completa - Alerta máxima
    print("\n📊 Escenario 4: Validación completa")
    resultados_4 = {
        'frecuencia': 141.7001,
        'snr': 15.2,
        'p_value': 0.0001,
        'bayes_factor': 150.5,
        'diferencia': 0.0000
    }
    
    await sistema.alerta_validacion_psi(evento_base, resultados_4)


async def main():
    """Ejecutar ejemplos de integración"""
    try:
        # Ejemplo 1: Validación con alertas
        resultado = await validacion_con_alertas()
        
        # Ejemplo 2: Alertas progresivas
        await ejemplo_alertas_progresivas()
        
        print("\n\n" + "=" * 70)
        print("✅ EJEMPLOS COMPLETADOS")
        print("=" * 70)
        print("\n💡 NOTAS:")
        print("   • Configurar credenciales en .env para alertas reales")
        print("   • Ver config/alertas.env.template para plantilla")
        print("   • Logs de alertas guardados en results/logs/alertas.log")
        
    except KeyboardInterrupt:
        print("\n\n⚠️  Ejecución interrumpida por el usuario")
    except Exception as e:
        print(f"\n❌ Error durante la ejecución: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    asyncio.run(main())
