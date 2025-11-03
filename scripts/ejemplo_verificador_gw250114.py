#!/usr/bin/env python3
"""
Ejemplos de uso del sistema de verificación GW250114
Demuestra diferentes modos de operación del verificador.
"""
import sys
import os

# Añadir directorio scripts al path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from verificador_gw250114 import VerificadorGW250114


def ejemplo_verificacion_simple():
    """
    Ejemplo 1: Verificación simple de disponibilidad
    
    Verifica una sola vez si GW250114 está disponible en GWOSC.
    """
    print("="*70)
    print("EJEMPLO 1: Verificación Simple")
    print("="*70)
    
    verificador = VerificadorGW250114()
    
    disponible, gps_time, mensaje = verificador.verificar_disponibilidad()
    
    if disponible:
        print(f"\n✅ GW250114 está disponible!")
        print(f"   GPS Time: {gps_time}")
        print(f"   Mensaje: {mensaje}")
    else:
        print(f"\n⏳ GW250114 aún no está disponible")
        print(f"   Mensaje: {mensaje}")
    
    return disponible, gps_time


def ejemplo_analisis_completo():
    """
    Ejemplo 2: Análisis completo del evento
    
    Si el evento está disponible, realiza análisis completo.
    """
    print("\n" + "="*70)
    print("EJEMPLO 2: Análisis Completo")
    print("="*70)
    
    verificador = VerificadorGW250114()
    
    disponible, gps_time, mensaje = verificador.verificar_disponibilidad()
    
    if disponible:
        print(f"\n📊 Iniciando análisis completo...")
        resultados = verificador.analizar_evento(gps_time)
        
        if 'error' not in resultados:
            print(f"\n✅ Análisis completado exitosamente")
            
            # Mostrar resultados por detector
            for detector, res in resultados.get('detectores', {}).items():
                print(f"\n   {detector}:")
                print(f"      Frecuencia pico: {res['frecuencia_pico']:.4f} Hz")
                print(f"      SNR @ 141.7 Hz: {res['snr']:.2f}")
                print(f"      Bayes Factor: {res['bayes_factor']:.2e}")
                print(f"      Significancia: {res['significancia']}")
            
            # Evaluación combinada
            if 'evaluacion_combinada' in resultados:
                eval_comb = resultados['evaluacion_combinada']
                print(f"\n   📋 Evaluación Combinada:")
                print(f"      Status: {eval_comb['status']}")
                print(f"      SNR medio: {eval_comb['snr_medio']:.2f}")
                print(f"      Coherencia: {'Sí' if eval_comb['coherencia'] else 'No'}")
        else:
            print(f"\n❌ Error en análisis: {resultados['error']}")
    else:
        print(f"\n⏳ No se puede realizar análisis: {mensaje}")


def ejemplo_monitoreo_limitado():
    """
    Ejemplo 3: Monitoreo con límite de verificaciones
    
    Monitorea periódicamente hasta 3 verificaciones.
    """
    print("\n" + "="*70)
    print("EJEMPLO 3: Monitoreo Limitado (3 verificaciones)")
    print("="*70)
    
    # Verificador con intervalo corto para demostración
    verificador = VerificadorGW250114(check_interval=5)
    
    print("\n🔄 Monitoreando disponibilidad de GW250114...")
    print("   (máximo 3 verificaciones con intervalo de 5 segundos)")
    
    verificador.monitorear(max_checks=3)


def ejemplo_monitoreo_continuo():
    """
    Ejemplo 4: Monitoreo continuo (modo producción)
    
    ADVERTENCIA: Este modo ejecuta indefinidamente.
    Use Ctrl+C para detener.
    """
    print("\n" + "="*70)
    print("EJEMPLO 4: Monitoreo Continuo")
    print("="*70)
    
    print("\n⚠️  MODO PRODUCCIÓN:")
    print("   Este modo ejecutará continuamente hasta detectar el evento.")
    print("   Presione Ctrl+C para detener.")
    
    respuesta = input("\n¿Desea ejecutar en modo continuo? (s/N): ")
    
    if respuesta.lower() == 's':
        # Verificador con intervalo de 1 hora
        verificador = VerificadorGW250114(check_interval=3600)
        
        try:
            verificador.monitorear()
        except KeyboardInterrupt:
            print("\n\n⏹️  Monitoreo detenido por el usuario")
    else:
        print("   Modo continuo cancelado")


def ejemplo_configuracion_personalizada():
    """
    Ejemplo 5: Configuración personalizada
    
    Demuestra cómo configurar el verificador con parámetros personalizados.
    """
    print("\n" + "="*70)
    print("EJEMPLO 5: Configuración Personalizada")
    print("="*70)
    
    # Crear verificador con configuración personalizada
    verificador = VerificadorGW250114(
        check_interval=600  # 10 minutos
    )
    
    print(f"\n📝 Configuración:")
    print(f"   Evento objetivo: {verificador.event_name}")
    print(f"   Frecuencia objetivo: {verificador.target_frequency} Hz")
    print(f"   Intervalo de verificación: {verificador.check_interval} segundos")
    print(f"   Directorio de resultados: {verificador.results_dir}")
    
    # Verificación única con esta configuración
    print(f"\n🔍 Realizando verificación única...")
    disponible, gps_time, mensaje = verificador.verificar_disponibilidad()
    
    print(f"\n   Resultado: {mensaje}")


def mostrar_menu():
    """Mostrar menú de ejemplos"""
    print("\n" + "="*70)
    print("SISTEMA DE VERIFICACIÓN GW250114 - EJEMPLOS DE USO")
    print("="*70)
    print("\nSeleccione un ejemplo:")
    print("  1. Verificación simple de disponibilidad")
    print("  2. Análisis completo del evento")
    print("  3. Monitoreo limitado (3 verificaciones)")
    print("  4. Monitoreo continuo (modo producción)")
    print("  5. Configuración personalizada")
    print("  6. Ejecutar todos los ejemplos (1-3, 5)")
    print("  0. Salir")
    print("="*70)


def main():
    """Función principal"""
    
    while True:
        mostrar_menu()
        
        try:
            opcion = input("\nOpción: ").strip()
            
            if opcion == "0":
                print("\n👋 Saliendo...")
                break
            elif opcion == "1":
                ejemplo_verificacion_simple()
            elif opcion == "2":
                ejemplo_analisis_completo()
            elif opcion == "3":
                ejemplo_monitoreo_limitado()
            elif opcion == "4":
                ejemplo_monitoreo_continuo()
            elif opcion == "5":
                ejemplo_configuracion_personalizada()
            elif opcion == "6":
                # Ejecutar todos los ejemplos seguros
                ejemplo_verificacion_simple()
                ejemplo_analisis_completo()
                ejemplo_monitoreo_limitado()
                ejemplo_configuracion_personalizada()
                print("\n✅ Todos los ejemplos ejecutados")
            else:
                print(f"\n❌ Opción '{opcion}' no válida")
            
            input("\nPresione Enter para continuar...")
            
        except KeyboardInterrupt:
            print("\n\n👋 Saliendo...")
            break
        except Exception as e:
            print(f"\n❌ Error: {e}")
            input("\nPresione Enter para continuar...")


if __name__ == "__main__":
    print("""
╔══════════════════════════════════════════════════════════════════╗
║     SISTEMA DE VERIFICACIÓN EN TIEMPO REAL - GW250114            ║
║     Ejemplos de Uso del Verificador                              ║
╚══════════════════════════════════════════════════════════════════╝
    """)
    
    main()
