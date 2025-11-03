#!/usr/bin/env python3
"""
Ejemplo de Uso del Sistema de Validación Avanzada
Muestra cómo utilizar los módulos individualmente y en conjunto
"""
import sys
import json
from pathlib import Path

# Agregar directorio de scripts al path
sys.path.insert(0, str(Path(__file__).parent))

def ejemplo_caracterizacion_bayesiana():
    """Ejemplo: Caracterización Bayesiana"""
    print("=" * 70)
    print("EJEMPLO 1: CARACTERIZACIÓN BAYESIANA")
    print("=" * 70)
    
    from caracterizacion_bayesiana import CaracterizacionBayesiana, generar_datos_sinteticos_gw250114
    
    # Generar datos sintéticos
    datos, fs, params_reales = generar_datos_sinteticos_gw250114()
    
    # Ejecutar caracterización
    bayes = CaracterizacionBayesiana(frecuencia_objetivo=141.7001)
    resultados = bayes.estimar_q_factor(datos, fs)
    
    print("\n✅ Resultados de Caracterización Bayesiana:")
    print(f"   Q-factor estimado: {resultados['q_factor']:.2f} ± {resultados['q_std']:.2f}")
    print(f"   Q-factor real: {params_reales['q_factor']}")
    print(f"   Frecuencia detectada: {resultados['frecuencia_detectada']:.4f} Hz")
    
    return resultados

def ejemplo_busqueda_gwtc1():
    """Ejemplo: Búsqueda Sistemática GWTC-1"""
    print("\n" + "=" * 70)
    print("EJEMPLO 2: BÚSQUEDA SISTEMÁTICA GWTC-1")
    print("=" * 70)
    
    from busqueda_sistematica_gwtc1 import BusquedaSistematicaGWTC1
    
    # Crear buscador
    buscador = BusquedaSistematicaGWTC1()
    
    # Cargar catálogo
    eventos = buscador.cargar_catalogo_gwtc1()
    print(f"Eventos en catálogo: {eventos}")
    
    # Analizar solo un evento de ejemplo
    print("\nAnalizando GW150914 como ejemplo...")
    buscador.analizar_evento('GW150914')
    
    print("\n✅ Ejemplo de resultado:")
    if buscador.resultados:
        print(f"   Evento: {buscador.resultados[0]['evento']}")
        print(f"   Detector: {buscador.resultados[0]['detector']}")
        print(f"   Frecuencia: {buscador.resultados[0]['frecuencia_detectada']:.2f} Hz")
        print(f"   SNR: {buscador.resultados[0]['snr']:.2f}")
    
    return buscador.resultados

def ejemplo_optimizacion_snr():
    """Ejemplo: Optimización SNR"""
    print("\n" + "=" * 70)
    print("EJEMPLO 3: OPTIMIZACIÓN SNR")
    print("=" * 70)
    
    from optimizacion_snr_avanzada import OptimizacionSNRAvanzada
    import numpy as np
    
    # Generar datos sintéticos
    fs = 4096
    t = np.linspace(0, 2, fs*2)
    señal = 1e-21 * np.exp(-np.pi * 141.7001 * t / 8.5) * np.sin(2 * np.pi * 141.7001 * t)
    datos_h1 = señal + np.random.normal(0, 2e-22, len(t))
    datos_l1 = señal + np.random.normal(0, 2e-22, len(t))
    
    # Crear optimizador
    optimizador = OptimizacionSNRAvanzada()
    
    # Ejecutar optimización
    resultados = optimizador.optimizar_snr_combinado(datos_h1, datos_l1, fs)
    
    print("\n✅ Resultados de Optimización:")
    print(f"   SNR original: {resultados['snr_original']:.2f}")
    print(f"   SNR optimizado: {resultados['snr_optimizado']:.2f}")
    print(f"   Mejora: {resultados['factor_mejora']:.2f}x")
    
    return resultados

def ejemplo_validacion_estadistica():
    """Ejemplo: Validación Estadística"""
    print("\n" + "=" * 70)
    print("EJEMPLO 4: VALIDACIÓN ESTADÍSTICA")
    print("=" * 70)
    
    from validacion_estadistica import ValidacionEstadisticaCompleta
    
    # Crear validador
    validador = ValidacionEstadisticaCompleta()
    
    # Ejecutar validación completa (con datos sintéticos)
    resultados = validador.ejecutar_validacion_completa()
    
    print("\n✅ Resumen de Validación:")
    print(f"   Significancia: {'✅ Cumple' if resultados.get('test_significancia', {}).get('significativo') else '❌ No cumple'}")
    print(f"   Bayes Factor: {'✅ Cumple' if resultados.get('bayes_factor', {}).get('evidencia_fuerte') else '❌ No cumple'}")
    print(f"   Coherencia: {'✅ Cumple' if resultados.get('coherencia', {}).get('coherente') else '❌ No cumple'}")
    
    return resultados

def ejemplo_sistema_completo():
    """Ejemplo: Sistema Completo"""
    print("\n" + "=" * 70)
    print("EJEMPLO 5: SISTEMA COMPLETO")
    print("=" * 70)
    
    from sistema_validacion_completo import SistemaValidacionCompleto
    
    # Crear sistema
    sistema = SistemaValidacionCompleto()
    
    # Ejecutar validación completa
    resultados = sistema.ejecutar_validacion_completa()
    
    print("\n✅ Sistema Completo Ejecutado")
    print(f"   Módulos: {len(resultados)}")
    
    # Mostrar resumen
    for modulo, resultado in resultados.items():
        estado = resultado.get('estado', 'desconocido')
        print(f"   • {modulo}: {estado}")
    
    return resultados

def main():
    """Ejecutar todos los ejemplos"""
    print("🌌 EJEMPLOS DE USO - SISTEMA DE VALIDACIÓN AVANZADA")
    print("=" * 70)
    print("Este script muestra cómo utilizar cada módulo del sistema")
    print("=" * 70)
    
    ejemplos = [
        ("Caracterización Bayesiana", ejemplo_caracterizacion_bayesiana),
        ("Búsqueda GWTC-1", ejemplo_busqueda_gwtc1),
        ("Optimización SNR", ejemplo_optimizacion_snr),
        ("Validación Estadística", ejemplo_validacion_estadistica),
        ("Sistema Completo", ejemplo_sistema_completo)
    ]
    
    resultados_ejemplos = {}
    
    for nombre, funcion in ejemplos:
        try:
            print(f"\n{'='*70}")
            print(f"Ejecutando: {nombre}")
            print(f"{'='*70}")
            resultado = funcion()
            resultados_ejemplos[nombre] = {"estado": "éxito", "resultado": resultado}
        except Exception as e:
            print(f"\n❌ Error en {nombre}: {e}")
            resultados_ejemplos[nombre] = {"estado": "error", "mensaje": str(e)}
    
    # Resumen final
    print("\n" + "=" * 70)
    print("📊 RESUMEN DE EJEMPLOS")
    print("=" * 70)
    
    for nombre, resultado in resultados_ejemplos.items():
        estado = "✅" if resultado["estado"] == "éxito" else "❌"
        print(f"{estado} {nombre}: {resultado['estado']}")
    
    print("\n✅ Todos los ejemplos ejecutados")
    print("\n💡 Tip: Revisa el código de este script para ver cómo usar cada módulo")

if __name__ == "__main__":
    main()
